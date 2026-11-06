From Coq Require Import Bool List ZArith Lia.
From compcert Require Import Integers Values Memory AST Zbits Coqlib.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.
From TrustNoBPF.Semantics Require Import AbstractDomain Concretization Transfer CompCertAssms IRLevelAssms Common ArithmeticHelpers.

Import ListNotations.
Open Scope Z_scope.

(** [entails] is the load's [attr_entails], consulted by [meet::fold]. *)
Section Arithmetic.
Variable entails : value_state -> value_state -> bool.

(** =========== Transfer definitions =========== *)

Definition source_term (source : SourceOperand.t) : term :=
  match source with
  | SourceOperand.Imm immediate => Const (Int.signed immediate)
  | SourceOperand.Value name => Var name
  end.

Definition arithmetic_immediate (size : OpSize.t) (immediate : int) : Z :=
  match size with OpSize.Op32 => Int.unsigned immediate
                  | OpSize.Op64 => Int.signed immediate end.

(** Rust [apply_assignment]; variable propagation is implemented in
    [ArithmeticHelpers.apply_assignment_var_offset]. *)
Definition apply_assignment (state : abstract_state) (dst : var)
    (expr : AssignmentExpr.t) : option abstract_state :=
  match expr with
  | AssignmentExpr.Const value =>
      Some (filter (fun fact => negb (atom_mentions dst fact)) state ++
        [Eq (Var dst) (Const value); AbstractValue (Var dst) Unknown;
         AbstractValue (Var dst) (URangeValue
           (URange (Int64.unsigned (Int64.repr value)) (Int64.unsigned (Int64.repr value))));
         AbstractValue (Var dst) (RangeValue (Range value value))])
  | AssignmentExpr.VarOffset name offset =>
      ArithmeticHelpers.apply_assignment_var_offset entails state dst name offset
  end.

Definition arithmetic_def_op (op : ArithmeticOp.t) : option def_op :=
  match op with
  | ArithmeticOp.Add => Some DefOp.Add | ArithmeticOp.Sub => Some DefOp.Sub
  | ArithmeticOp.And => Some DefOp.And | ArithmeticOp.Or => Some DefOp.Or
  | ArithmeticOp.Xor => Some DefOp.Xor | ArithmeticOp.Lsh => Some DefOp.Lsh
  | ArithmeticOp.Rsh => Some DefOp.Rsh | ArithmeticOp.Arsh => Some DefOp.Arsh
  | ArithmeticOp.Mul => Some DefOp.Mul | ArithmeticOp.Div => Some DefOp.Div
  | ArithmeticOp.Mod => Some DefOp.Mod | _ => None
  end.

Definition append_arithmetic_def (state : abstract_state) (dst : var)
    (op : ArithmeticOp.t) (lhs rhs : term) : abstract_state :=
  match arithmetic_def_op op with
  | Some operation => state ++ [Def dst operation lhs rhs]
  | None => state
  end.

(** The 64-bit [and]/[or]/[xor]/shift/[mul]/[div]/[mod] arm of Rust
    [transfer.rs::transfer_arithmetic]. Constant folding reads the state after
    [Def] insertion. No guarded fact reaches [dst]; Rust leaves that to the
    [CarryRelation] hint. *)
Definition transfer_alu64 (state : abstract_state) (dst lhs : var)
    (source : SourceOperand.t) (op : ArithmeticOp.t) : abstract_state :=
  let post := append_arithmetic_def (apply_havoc state dst)
    dst op (Var lhs) (source_term source) in
  let post := match ArithmeticHelpers.fold_alu_constants post op lhs source with
    | Some value => post ++ [AbstractValue (Var dst) (URangeValue (URange value value))]
    | None => post
    end in
  match source with
  | SourceOperand.Imm immediate =>
      let post := match ArithmeticHelpers.pow2_stride op (Int.signed immediate) with
        | Some stride => post ++ [AbstractValue (Var dst)
            (CongruenceValue (Congruence stride 0))]
        | None => post
        end in
      match op with
      | ArithmeticOp.Rsh => if (1 <=? Int.signed immediate) && (Int.signed immediate <=? 63)
          then post ++ [AbstractValue (Var dst) (URangeValue
            (URange 0 (Z.shiftr Int64.max_unsigned (Int.signed immediate))))]
          else post
      | _ => post
      end
  | _ => post
  end.

(** The [add]/[sub] arms of Rust [transfer.rs::transfer_arithmetic]. *)
Definition transfer_add_sub (state : abstract_state) (size : OpSize.t)
    (dst lhs : var) (source : SourceOperand.t) (op : ArithmeticOp.t) : option abstract_state :=
  match source with
  | SourceOperand.Imm immediate =>
      let offset := match op with ArithmeticOp.Sub => - Int.signed immediate
                    | _ => Int.signed immediate end in
      match size with
      | OpSize.Op64 => apply_assignment state dst (AssignmentExpr.VarOffset lhs offset)
      | OpSize.Op32 =>
          if ArithmeticHelpers.op32_shift_exact state lhs offset
          then apply_assignment state dst (AssignmentExpr.VarOffset lhs offset)
          else Some (apply_havoc_with_size state dst Word ++
            [Def dst (DefOp.AddWrap OpSize.Op32) (Var lhs) (Const offset)])
      end
  | SourceOperand.Value rhs =>
      match size with
      | OpSize.Op32 =>
          match ArithmeticHelpers.op32_binop_bounds state lhs rhs op with
          | Some (lower, upper) => Some (append_arithmetic_def (apply_havoc state dst)
              dst op (Var lhs) (Var rhs) ++
              [AbstractValue (Var dst) (URangeValue (URange lower upper))])
          | None => Some (apply_havoc_with_size state dst Word)
          end
      | OpSize.Op64 =>
          match op with
          | ArithmeticOp.Sub => Some (apply_havoc state dst ++ [Eq (Var dst) (Sub lhs rhs)])
          | _ => let derived := ArithmeticHelpers.derived_ptr_add_reg state lhs rhs in
              Some (apply_havoc state dst ++ match derived with
                | Some ptr => [AbstractValue (Var dst) (Ptr ptr)] | None => [] end)
          end
      end
  end.

(** [verifier/transfer.rs::transfer_arithmetic]. Match arms are regrouped by
    opcode, preserving Rust's guards and fallback behavior. [None] represents
    [UnexpectedLhs]/[MissingLhs].
    Allocation failures are not modeled. *)
Definition transfer_arithmetic (state : abstract_state) (size : OpSize.t)
    (dst : var) (lhs : option var) (source : SourceOperand.t)
    (op : ArithmeticOp.t) : option abstract_state :=
  let fallback := match size with OpSize.Op32 => apply_havoc_with_size state dst Word
                                 | OpSize.Op64 => apply_havoc state dst end in
  match op, lhs with
  | ArithmeticOp.Mov, Some _ => None
  | ArithmeticOp.Mov, None =>
      match source with
      | SourceOperand.Imm immediate => apply_assignment state dst (AssignmentExpr.Const
          (arithmetic_immediate size immediate))
      | SourceOperand.Value name =>
          match size with
          | OpSize.Op64 => apply_assignment state dst (AssignmentExpr.VarOffset name 0)
          | OpSize.Op32 => if ArithmeticHelpers.fits_u32 state name
              then apply_assignment state dst (AssignmentExpr.VarOffset name 0)
              else Some fallback
          end
      end
  | ArithmeticOp.Add, None | ArithmeticOp.Sub, None => None
  | ArithmeticOp.Add, Some name | ArithmeticOp.Sub, Some name =>
      transfer_add_sub state size dst name source op
  | ArithmeticOp.And, Some name =>
      match size with
      | OpSize.Op64 => Some (transfer_alu64 state dst name source op)
      | OpSize.Op32 => let upper := ArithmeticHelpers.and32_upper_bound state name source in
          Some (apply_havoc state dst ++
            [AbstractValue (Var dst) (URangeValue (URange 0 upper));
             AbstractValue (Var dst) (RangeValue (Range 0 upper))])
      end
  | ArithmeticOp.Or, Some name | ArithmeticOp.Xor, Some name
  | ArithmeticOp.Lsh, Some name | ArithmeticOp.Rsh, Some name
  | ArithmeticOp.Arsh, Some name | ArithmeticOp.Mul, Some name
  | ArithmeticOp.Div, Some name | ArithmeticOp.Mod, Some name =>
      match size with OpSize.Op64 => Some (transfer_alu64 state dst name source op)
                      | OpSize.Op32 => Some fallback end
  | _, _ => Some fallback
  end.

(** Rust [transfer_instruction]'s operand initialization check followed by
    [transfer_arithmetic]. *)
Definition transfer_arithmetic_defined (before : abstract_machine_state)
    (dst : ireg) (dst_value : var) (lhs : option ireg)
    (source : ireg + int) (size : OpSize.t) (op : ArithmeticOp.t) :
    option abstract_machine_state :=
  let initialized := fun reg => ensure_defined (facts before) (register_name before reg) in
  if (match lhs with Some reg => initialized reg | None => true end) &&
     (match source with inl reg => initialized reg | inr _ => true end) then
    option_map (fun post => AbstractMachineState post
      (set_register_name (register_name before) dst dst_value))
      (transfer_arithmetic (facts before) size dst_value
        (option_map (register_name before) lhs)
        (match source with inl reg => SourceOperand.Value (register_name before reg)
                         | inr immediate => SourceOperand.Imm immediate end) op)
  else None.

(** Rust [leaks::typed_pointer]: an untyped BTF pointer may hold an integer
    the kernel types as a scalar. *)
Definition typed_pointer (state : abstract_state) (name : var) : bool :=
  match find_pointer_fact state name with
  | Some ptr => negb (Region.probe_readable (ptr_ty ptr) &&
      match Region.btf_type (ptr_ty ptr) with None => true | Some _ => false end)
  | None => false
  end.

(** Rust [leaks::check_pointer_arithmetic]: two pointers combine only by a
    subtraction, whatever the loader's privileges. *)
Definition check_pointer_arithmetic (state : abstract_state) (lhs : option var)
    (source : SourceOperand.t) (op : ArithmeticOp.t) : bool :=
  match lhs, source with
  | Some lhs, SourceOperand.Value rhs =>
      negb (match op with ArithmeticOp.Sub => false | _ => true end &&
            typed_pointer state lhs && typed_pointer state rhs)
  | _, _ => true
  end.

(** Rust [leaks::operands_disclosable]. *)
Definition operands_disclosable (state : abstract_state) (lhs : option var)
    (source : SourceOperand.t) : bool :=
  match lhs with Some lhs => disclosable state lhs | None => true end &&
  match source with SourceOperand.Imm _ => true | SourceOperand.Value name => disclosable state name end.

(** The [Arithmetic] arm of Rust [transfer_instruction]: the result of an
    operation on disclosable operands is disclosable. *)
Definition transfer_arithmetic_local (before : abstract_machine_state)
    (dst : ireg) (dst_value : var) (lhs : option ireg)
    (source : ireg + int) (size : OpSize.t) (op : ArithmeticOp.t) :
    option abstract_machine_state :=
  let lhs_name := option_map (register_name before) lhs in
  let operand := match source with inl reg => SourceOperand.Value (register_name before reg)
                                  | inr immediate => SourceOperand.Imm immediate end in
  if check_pointer_arithmetic (facts before) lhs_name operand op then
    let scalar := operands_disclosable (facts before) lhs_name operand in
    option_map (fun after =>
      if scalar then AbstractMachineState (mark_scalar (facts after) dst_value) (register_name after)
      else after)
      (transfer_arithmetic_defined before dst dst_value lhs source size op)
  else None.

(** =========== Soundness proof =========== *)

Lemma arithmetic_immediate_bounds : forall size immediate,
  Int64.min_signed <= arithmetic_immediate size immediate <= Int64.max_signed.
Proof.
  intros size immediate. destruct size; cbn [arithmetic_immediate].
  - pose proof (Int.unsigned_range immediate).
    change (0 <= Int.unsigned immediate < 4294967296) in H.
    change (-9223372036854775808 <= Int.unsigned immediate <= 9223372036854775807). lia.
  - pose proof (Int.signed_range immediate).
    change (-2147483648 <= Int.signed immediate <= 2147483647) in H.
    change (-9223372036854775808 <= Int.signed immediate <= 9223372036854775807). lia.
Qed.

Lemma shift_mask32_in_range : forall n,
  Int.ltu (Int.and n (Int.repr 31)) Int.iwordsize = true.
Proof.
  intros n. pose proof (Int.and_le (Int.repr 31) n) as LIMIT.
  rewrite Int.and_commut in LIMIT.
  change (Int.unsigned (Int.and n (Int.repr 31)) <= 31) in LIMIT.
  unfold Int.ltu. change ((if Coqlib.zlt (Int.unsigned (Int.and n (Int.repr 31))) 32
    then true else false) = true).
  destruct Coqlib.zlt; [reflexivity |lia].
Qed.

Lemma eval_alu32_scalar : forall op opcode a (source : int64 + int),
  arithmetic_opcode op = Some opcode ->
  exists n, eval_alu32 opcode (Vlong a)
    (match source with inl b => inl (Vlong b) | inr i => inr i end) =
    Vlong (Int64.repr (Int.unsigned n)).
Proof.
  intros op opcode a source OPCODE. destruct op; inversion OPCODE; subst opcode;
    destruct source as [b|i];
    cbn [eval_alu32 Val.loword Val.add Val.sub Val.mul Val.or Val.and Val.xor
      Val.neg Val.shl Val.shru Val.shr eval_shift_mask Val.longofintu
      eval_div_u32 eval_mod_u32 Val.divu Val.modu].
  all: rewrite ?shift_mask32_in_range.
  all: try (eexists; reflexivity).
  all: unfold eval_div_u32, eval_mod_u32; cbn [Val.divu Val.modu].
  all: match goal with |- context [if Int.eq ?n Int.zero then _ else _] =>
    destruct (Int.eq n Int.zero) eqn:ZERO end; cbn [Vzero];
    try (eexists; reflexivity).
  all: apply Int.same_if_eq in ZERO; rewrite ZERO;
    destruct (Val.eq (Vint Int.zero) (Vint Int.zero)); try contradiction;
    eexists; reflexivity.
Qed.

Lemma exec_alu32_scalar : forall op opcode (regs : regset) (dst : ireg) source stack code_id count memory a,
  arithmetic_opcode op = Some opcode -> regs dst = Vlong a -> scalar_source regs source ->
  exists n, exec_alu opcode W32 dst source regs stack code_id count memory =
    Next (nextinstr (Pregmap.set dst (Vlong (Int64.repr (Int.unsigned n))) regs))
      stack code_id count memory.
Proof.
  intros op opcode regs dst [src|imm] stack code_id count memory a OPCODE DST SOURCE.
  - destruct SOURCE as [b SRC]. unfold exec_alu. cbn -[ireg_eqb eval_alu32].
    rewrite DST, SRC. destruct (ireg_eqb dst src).
    + destruct op; inversion OPCODE; subst opcode;
        try (exists Int.zero; reflexivity);
        destruct (eval_alu32_scalar _ _ a (inl b) OPCODE) as [n VALUE];
        exists n; rewrite VALUE; reflexivity.
    + destruct (eval_alu32_scalar op opcode a (inl b) OPCODE) as [n VALUE].
      exists n. rewrite VALUE. reflexivity.
  - unfold exec_alu. cbn -[eval_alu32]. rewrite DST.
    destruct (eval_alu32_scalar op opcode a (inr imm) OPCODE) as [n VALUE].
    exists n. rewrite VALUE. reflexivity.
Qed.

Lemma havoc_bounded_word_holds : forall world memory state dst n bound,
  Forall (atom_holds world memory) state ->
  0 <= Int.unsigned n <= bound ->
  Forall (atom_holds (assign_value world dst (Vlong (Int64.repr (Int.unsigned n)))) memory)
    (apply_havoc state dst ++
      [AbstractValue (Var dst) (URangeValue (URange 0 bound));
       AbstractValue (Var dst) (RangeValue (Range 0 bound))]).
Proof.
  intros world memory state dst n bound FACTS BOUNDS.
  apply Forall_app. split; [apply apply_havoc_holds; [exact FACTS |constructor] |].
  assert (UNSIGNED : 0 <= Int.unsigned n <= Int64.max_unsigned).
  { pose proof (Int.unsigned_range n). change (0 <= Int.unsigned n < 4294967296) in H.
    change (0 <= Int.unsigned n <= 18446744073709551615). lia. }
  assert (SIGNED : Int64.min_signed <= Int.unsigned n <= Int64.max_signed).
  { pose proof (Int.unsigned_range n). change (0 <= Int.unsigned n < 4294967296) in H.
    change (-9223372036854775808 <= Int.unsigned n <= 9223372036854775807). lia. }
  apply Forall_forall. intros fact IN. destruct IN as [<- | [<- | []]].
  all: cbn [atom_holds eval_term assign_value variable_value];
    destruct (Nat.eq_dec dst dst); try contradiction;
    cbn [value_holds u_lower u_upper lower upper];
    rewrite ?Int64.unsigned_repr by exact UNSIGNED;
    rewrite ?Int64.signed_repr by exact SIGNED;
    pose proof (Int.unsigned_range n); change (0 <= Int.unsigned n < 4294967296) in H; lia.
Qed.

Lemma havoc_word_holds : forall world memory state dst n,
  Forall (atom_holds world memory) state ->
  Forall (atom_holds (assign_value world dst (Vlong (Int64.repr (Int.unsigned n)))) memory)
    (apply_havoc_with_size state dst Word).
Proof.
  intros. apply havoc_bounded_word_holds; [assumption |apply Int.unsigned_range_2].
Qed.

(** Complete 32-bit scalar cases whose Rust transfer only havocs and records
    the zero-extended word bounds. No operand-name freshness is needed here. *)
Theorem transfer_alu32_havoc_sound :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst : ireg) dst_value source op opcode a,
    In op [ArithmeticOp.Or; ArithmeticOp.Xor; ArithmeticOp.Lsh; ArithmeticOp.Rsh;
      ArithmeticOp.Arsh; ArithmeticOp.Mul; ArithmeticOp.Div; ArithmeticOp.Mod; ArithmeticOp.Neg] ->
    arithmetic_opcode op = Some opcode ->
    regs dst = Vlong a -> scalar_source regs source ->
    fresh_destination before dst dst_value ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value (Some dst) source OpSize.Op32 op = Some after ->
    exists concrete', instruction_step regions program (Palu opcode W32 dst source)
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst dst_value
    source op opcode a OPS OPCODE DST SOURCE FRESH CONCRETE TRANSFER.
  destruct CONCRETE as [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]].
  assert (POST : forall lhs src,
    transfer_arithmetic (facts before) OpSize.Op32 dst_value (Some lhs) src op =
      Some (apply_havoc_with_size (facts before) dst_value Word)).
  { intros lhs src. destruct op; cbn in OPS;
      try solve [exfalso; intuition discriminate]; reflexivity. }
  unfold transfer_arithmetic_defined in TRANSFER.
  destruct ((match Some dst with Some reg => ensure_defined (facts before) (register_name before reg)
    | None => true end) && (match source with inl reg =>
      ensure_defined (facts before) (register_name before reg) | inr _ => true end)); try discriminate.
  cbn [option_map] in TRANSFER. rewrite POST in TRANSFER. inversion TRANSFER; subst after.
  destruct (exec_alu32_scalar op opcode regs dst source stack code_id count memory a
    OPCODE DST SOURCE) as [n EXEC].
  exists (TLS_State (nextinstr (Pregmap.set dst (Vlong (Int64.repr (Int.unsigned n))) regs))
    stack code_id count memory). split.
  - unfold instruction_step. cbn [exec_instr]. exact EXEC.
  - eapply concretizes_register_update; [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |].
    apply havoc_word_holds. exact FACTS.
Qed.

Lemma bitwise64_unsigned_bounds : forall op a b,
  In op [ArithmeticOp.And; ArithmeticOp.Or; ArithmeticOp.Xor] ->
  let result := match op with ArithmeticOp.And => Z.land (Int64.unsigned a) (Int64.unsigned b)
    | ArithmeticOp.Or => Z.lor (Int64.unsigned a) (Int64.unsigned b)
    | _ => Z.lxor (Int64.unsigned a) (Int64.unsigned b) end in
  0 <= result <= Int64.max_unsigned.
Proof.
  intros op a b OPS result.
  pose proof (Int64.unsigned_range a) as A. pose proof (Int64.unsigned_range b) as B.
  assert (ALOG : Z.log2 (Int64.unsigned a) <= 63).
  { assert (H : Int64.unsigned a <= Int64.max_unsigned) by (unfold Int64.max_unsigned; lia).
    pose proof (Z.log2_le_mono _ _ H) as LOG.
    change (Z.log2 (Int64.unsigned a) <= 63) in LOG. exact LOG. }
  assert (BLOG : Z.log2 (Int64.unsigned b) <= 63).
  { assert (H : Int64.unsigned b <= Int64.max_unsigned) by (unfold Int64.max_unsigned; lia).
    pose proof (Z.log2_le_mono _ _ H) as LOG.
    change (Z.log2 (Int64.unsigned b) <= 63) in LOG. exact LOG. }
  assert (NONNEG : 0 <= result).
  { destruct op; cbn in OPS; try solve [exfalso; intuition discriminate]; unfold result.
    - apply Z.lor_nonneg. lia.
    - apply Z.land_nonneg. left. lia.
    - apply Z.lxor_nonneg. lia. }
  assert (LOG : Z.log2 result <= 63).
  { destruct op; cbn in OPS; try solve [exfalso; intuition discriminate]; unfold result.
    - rewrite Z.log2_lor by lia. apply Z.max_lub; assumption.
    - eapply Z.le_trans; [apply Z.log2_land; lia |].
      eapply Z.le_trans; [apply Z.le_min_l |exact ALOG].
    - eapply Z.le_trans; [apply Z.log2_lxor; lia |]. apply Z.max_lub; assumption. }
  split; [exact NONNEG |]. destruct (Z.eq_dec result 0); [subst result; cbn; lia |].
  assert (BOUND : result < 2 ^ 64) by (apply Z.log2_lt_pow2; lia).
  change (result <= 18446744073709551615). change (result < 18446744073709551616) in BOUND. lia.
Qed.

Lemma shift_mask64_in_range : forall n,
  Int.ltu (Int.and n (Int.repr 63)) Int64.iwordsize' = true.
Proof.
  intros n. pose proof (Int.and_le (Int.repr 63) n) as LIMIT.
  rewrite Int.and_commut in LIMIT.
  change (Int.unsigned (Int.and n (Int.repr 63)) <= 63) in LIMIT.
  unfold Int.ltu. change ((if zlt (Int.unsigned (Int.and n (Int.repr 63))) 64
    then true else false) = true).
  destruct zlt; [reflexivity |lia].
Qed.

Lemma shift_mask64_count : forall n,
  Int.unsigned (Int.and (Int.repr (Int64.signed n)) (Int.repr 63)) =
    Z.land (Int64.unsigned n) 63.
Proof.
  intros n. replace (Int.repr 63) with (Int.sub (Int.repr 64) Int.one) by reflexivity.
  rewrite <- (Int.modu_and (Int.repr (Int64.signed n)) (Int.repr 64) (Int.repr 6) eq_refl).
  change (Int.unsigned (Int.repr (Int.unsigned (Int.repr (Int64.signed n)) mod 64)) =
    Z.land (Int64.unsigned n) 63).
  rewrite Int.unsigned_repr by
    (pose proof (Z.mod_pos_bound (Int.unsigned (Int.repr (Int64.signed n))) 64 ltac:(lia));
     change (0 <= Int.unsigned (Int.repr (Int64.signed n)) mod 64 <= 4294967295); lia).
  replace 63 with (Z.ones 6) by reflexivity. rewrite Z.land_ones by lia.
  change (Int.unsigned (Int.repr (Int64.signed n)) mod 64 = Int64.unsigned n mod 64).
  apply eqmod_mod_eq; [lia |]. eapply eqmod_trans with (Int64.signed n).
  - apply eqmod_sym. eapply eqmod_divides; [apply Int.eqm_unsigned_repr |].
    exists 67108864. reflexivity.
  - eapply eqmod_divides; [apply Int64.eqm_signed_unsigned |].
    exists 288230376151711744. reflexivity.
Qed.

Lemma pinned_source_sound : forall world memory state source value,
  Forall (atom_holds world memory) state ->
  (match source with
   | SourceOperand.Imm imm => Some (ArithmeticHelpers.unsigned64 (Int.signed imm))
   | SourceOperand.Value name => ArithmeticHelpers.pinned state (Var name)
   end) = Some value ->
  exists n, eval_term world (source_term source) = Vlong n /\ Int64.unsigned n = value.
Proof.
  intros world memory state [imm|name] value FACTS PINNED.
  - inversion PINNED; subst value. eexists. split; reflexivity.
  - eapply ArithmeticHelpers.pinned_sound; eauto.
Qed.

Lemma fold_shift_constants_sound : forall world memory state lhs source op opcode value,
  In op [ArithmeticOp.Lsh; ArithmeticOp.Rsh; ArithmeticOp.Arsh] ->
  arithmetic_opcode op = Some opcode -> Forall (atom_holds world memory) state ->
  ArithmeticHelpers.fold_alu_constants state op lhs source = Some value ->
  exists a b, variable_value world lhs = Vlong a /\
    eval_term world (source_term source) = Vlong b /\
    eval_alu64 opcode (Vlong a) (inl (Vlong b)) = Vlong (Int64.repr value) /\
    0 <= value <= Int64.max_unsigned.
Proof.
  intros world memory state lhs source op opcode value OPS OPCODE FACTS FOLD.
  unfold ArithmeticHelpers.fold_alu_constants in FOLD.
  destruct (ArithmeticHelpers.pinned state (Var lhs)) as [left|] eqn:LEFT;
    [|destruct source; try discriminate;
      destruct (ArithmeticHelpers.pinned state (Var name)); discriminate].
  destruct (match source with
    | SourceOperand.Imm imm => Some (ArithmeticHelpers.unsigned64 (Int.signed imm))
    | SourceOperand.Value name => ArithmeticHelpers.pinned state (Var name)
    end) as [right|] eqn:RIGHT; try discriminate.
  destruct (ArithmeticHelpers.pinned_sound world memory state (Var lhs) left FACTS LEFT)
    as [a [A AU]].
  destruct (pinned_source_sound world memory state source right FACTS RIGHT) as [b [B BU]].
  cbn [eval_term] in A. rewrite <- AU, <- BU in FOLD.
  destruct op; cbn in OPS; try solve [exfalso; intuition discriminate];
    inversion OPCODE; subst opcode; inversion FOLD; subst value;
    exists a, b; repeat split; try exact A; try exact B.
  all: try solve [cbn [eval_alu64 eval_val_int eval_shift_mask int_of_int64 Val.and Val.shll Val.shrlu Val.shrl];
    unfold int_of_int64;
    rewrite shift_mask64_in_range; unfold Int64.shl', Int64.shru', Int64.shr';
    rewrite shift_mask64_count; unfold ArithmeticHelpers.unsigned64, ArithmeticHelpers.signed64;
    rewrite ?Int64.repr_unsigned, ?Int64.repr_signed; reflexivity].
  all: try solve [unfold ArithmeticHelpers.unsigned64;
    match goal with |- context [Int64.unsigned ?n] => pose proof (Int64.unsigned_range_2 n); lia end].
  all: try solve [apply Z.shiftr_nonneg; pose proof (Int64.unsigned_range a); lia].
  assert (MASK : 0 <= Z.land (Int64.unsigned b) 63).
  { replace 63 with (Z.ones 6) by reflexivity. rewrite Z.land_ones by lia.
    change (0 <= Int64.unsigned b mod 64).
    exact (proj1 (Z.mod_pos_bound (Int64.unsigned b) 64 ltac:(lia))). }
  rewrite Z.shiftr_div_pow2 by exact MASK.
  eapply Z.le_trans; [apply Z.div_le_upper_bound |exact (proj2 (Int64.unsigned_range_2 a))].
  - apply Z.pow_pos_nonneg; lia.
  - pose proof (Int64.unsigned_range a).
    pose proof (Z.pow_pos_nonneg 2 (Z.land (Int64.unsigned b) 63) ltac:(lia) MASK). nia.
Qed.

Lemma fold_bitwise_mul_constants_sound : forall world memory state lhs source op opcode value,
  In op [ArithmeticOp.And; ArithmeticOp.Or; ArithmeticOp.Xor; ArithmeticOp.Mul] ->
  arithmetic_opcode op = Some opcode ->
  Forall (atom_holds world memory) state ->
  ArithmeticHelpers.fold_alu_constants state op lhs source = Some value ->
  exists a b, variable_value world lhs = Vlong a /\
    eval_term world (source_term source) = Vlong b /\
    eval_alu64 opcode (Vlong a) (inl (Vlong b)) = Vlong (Int64.repr value) /\
    0 <= value <= Int64.max_unsigned.
Proof.
  intros world memory state lhs source op opcode value OPS OPCODE FACTS FOLD.
  unfold ArithmeticHelpers.fold_alu_constants in FOLD.
  destruct (ArithmeticHelpers.pinned state (Var lhs)) as [left|] eqn:LEFT;
    [|destruct source; try discriminate;
      destruct (ArithmeticHelpers.pinned state (Var name)); discriminate].
  destruct (match source with
    | SourceOperand.Imm imm => Some (ArithmeticHelpers.unsigned64 (Int.signed imm))
    | SourceOperand.Value name => ArithmeticHelpers.pinned state (Var name)
    end) as [right|] eqn:RIGHT; try discriminate.
  destruct (ArithmeticHelpers.pinned_sound world memory state (Var lhs) left FACTS LEFT)
    as [a [A AU]].
  destruct (pinned_source_sound world memory state source right FACTS RIGHT) as [b [B BU]].
  cbn [eval_term] in A. rewrite <- AU, <- BU in FOLD.
  destruct op; cbn in OPS; try solve [exfalso; intuition discriminate];
    inversion OPCODE; subst opcode; inversion FOLD; subst value;
    exists a, b; repeat split; try exact A; try exact B;
    cbn [eval_alu64 eval_val_int Val.andl Val.orl Val.xorl Val.mull];
    unfold Int64.and, Int64.or, Int64.xor, Int64.mul, ArithmeticHelpers.unsigned64;
    try solve [rewrite ?Int64.repr_unsigned; reflexivity].
  all: try solve [pose proof (Int64.unsigned_range_2
    (Int64.repr (Int64.unsigned a * Int64.unsigned b))); lia].
  all: pose proof (bitwise64_unsigned_bounds ArithmeticOp.And a b (or_introl eq_refl)) as AND;
    pose proof (bitwise64_unsigned_bounds ArithmeticOp.Or a b
      (or_intror (or_introl eq_refl))) as OR;
    pose proof (bitwise64_unsigned_bounds ArithmeticOp.Xor a b
      (or_intror (or_intror (or_introl eq_refl)))) as XOR;
    cbn -[Int64.max_unsigned] in AND, OR, XOR; lia.
Qed.

Lemma eval_alu64_simple_scalar : forall op opcode a b,
  In op [ArithmeticOp.And; ArithmeticOp.Or; ArithmeticOp.Xor;
    ArithmeticOp.Lsh; ArithmeticOp.Rsh; ArithmeticOp.Arsh; ArithmeticOp.Mul;
    ArithmeticOp.Div; ArithmeticOp.Mod] ->
  arithmetic_opcode op = Some opcode ->
  exists n, eval_alu64 opcode (Vlong a) (inl (Vlong b)) = Vlong n.
Proof.
  intros op opcode a b OPS OPCODE.
  destruct op; cbn in OPS; try solve [exfalso; intuition discriminate];
    inversion OPCODE; subst opcode; cbn [eval_alu64 eval_val_int Val.andl Val.orl Val.xorl Val.mull
      eval_shift_mask Val.and Val.shll Val.shrlu Val.shrl];
    rewrite ?shift_mask64_in_range;
    try (eexists; reflexivity).
  all: unfold eval_div_u64, eval_mod_u64; cbn [Val.divlu Val.modlu].
  all: destruct (Int64.eq b Int64.zero) eqn:ZERO; cbn; try (eexists; reflexivity).
  all: apply Int64.same_if_eq in ZERO; subst b;
    destruct (Val.eq (Vlong Int64.zero) (Vlong Int64.zero)); try contradiction;
    eexists; reflexivity.
Qed.

Lemma fold_alu64_constants_sound : forall world memory state lhs source op opcode value,
  In op [ArithmeticOp.And; ArithmeticOp.Or; ArithmeticOp.Xor;
    ArithmeticOp.Lsh; ArithmeticOp.Rsh; ArithmeticOp.Arsh; ArithmeticOp.Mul;
    ArithmeticOp.Div; ArithmeticOp.Mod] ->
  arithmetic_opcode op = Some opcode -> Forall (atom_holds world memory) state ->
  ArithmeticHelpers.fold_alu_constants state op lhs source = Some value ->
  exists a b, variable_value world lhs = Vlong a /\
    eval_term world (source_term source) = Vlong b /\
    eval_alu64 opcode (Vlong a) (inl (Vlong b)) = Vlong (Int64.repr value) /\
    0 <= value <= Int64.max_unsigned.
Proof.
  intros world memory state lhs source op opcode value OPS OPCODE FACTS FOLD.
  destruct op; cbn in OPS; try solve [exfalso; intuition discriminate].
  all: first
    [solve [eapply fold_bitwise_mul_constants_sound; eauto; cbn; auto]
    |solve [eapply fold_shift_constants_sound; eauto; cbn; auto]
    |unfold ArithmeticHelpers.fold_alu_constants in FOLD;
       destruct (ArithmeticHelpers.pinned state (Var lhs));
       destruct source; try discriminate;
       destruct (ArithmeticHelpers.pinned state (Var name)); discriminate].
Qed.

Lemma assignment_const_holds : forall world memory state dst constant,
  Forall (atom_holds world memory) state ->
  Int64.min_signed <= constant <= Int64.max_signed ->
  Forall (atom_holds (assign_value world dst (Vlong (Int64.repr constant))) memory)
    (filter (fun fact => negb (atom_mentions dst fact)) state ++
      [Eq (Var dst) (Const constant); AbstractValue (Var dst) Unknown;
       AbstractValue (Var dst) (URangeValue
         (URange (Int64.unsigned (Int64.repr constant)) (Int64.unsigned (Int64.repr constant))));
       AbstractValue (Var dst) (RangeValue (Range constant constant))]).
Proof.
  intros world memory state dst constant FACTS BOUNDS. apply Forall_app. split.
  - apply Forall_forall. intros fact IN. apply filter_In in IN as [IN KEPT].
    apply negb_true_iff in KEPT. eapply atom_holds_assign; [exact KEPT |].
    exact ((proj1 (Forall_forall _ _) FACTS) _ IN).
  - apply Forall_forall. intros fact IN.
    destruct IN as [<- | [<- | [<- | [<- | []]]]].
    all: cbn [atom_holds eval_term assign_value variable_value value_holds];
      destruct (Nat.eq_dec dst dst); try contradiction.
    all: repeat split; try constructor; cbn [u_lower u_upper lower upper];
      rewrite ?Int64.signed_repr by exact BOUNDS; lia.
Qed.

Theorem transfer_mov_imm_sound :
  forall (attrs : load_attrs) program regions before after concrete dst dst_value size immediate,
    fresh_destination before dst dst_value ->
    concretizes attrs regions before concrete ->
    transfer_arithmetic_defined before dst dst_value None (inr immediate)
      size ArithmeticOp.Mov = Some after ->
    exists concrete',
      instruction_step regions program
        (Palu MOV (match size with OpSize.Op32 => W32 | OpSize.Op64 => W64 end)
          dst (inr immediate)) concrete concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after concrete dst dst_value size immediate
    FRESH CONCRETE TRANSFER.
  destruct concrete as [regs stack code_id count memory].
  destruct CONCRETE as [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]].
  unfold transfer_arithmetic_defined, transfer_arithmetic, apply_assignment in TRANSFER.
  cbn [option_map] in TRANSFER. inversion TRANSFER; subst after; clear TRANSFER.
  exists (TLS_State (nextinstr (Pregmap.set dst
    (Vlong (Int64.repr (arithmetic_immediate size immediate))) regs))
    stack code_id count memory). split.
  - unfold instruction_step. cbn [exec_instr exec_alu eval_alu32 eval_alu64 eval_val_int].
    destruct size; cbn [arithmetic_immediate int64_of_int Val.longofintu]; reflexivity.
  - eapply concretizes_register_update; [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |].
    apply assignment_const_holds; [exact FACTS |apply arithmetic_immediate_bounds].
Qed.

Lemma eval_add_sub32_exact : forall op a b,
  (op = ArithmeticOp.Add \/ op = ArithmeticOp.Sub) ->
  0 <= Int64.unsigned a <= Int.max_unsigned ->
  0 <= Int64.unsigned b <= Int.max_unsigned ->
  let result := match op with ArithmeticOp.Sub => Int64.unsigned a - Int64.unsigned b
                             | _ => Int64.unsigned a + Int64.unsigned b end in
  0 <= result <= Int.max_unsigned ->
  eval_alu32 (match op with ArithmeticOp.Sub => SUB | _ => ADD end)
    (Vlong a) (inl (Vlong b)) = Vlong (Int64.repr result).
Proof.
  intros op a b [-> | ->] A B result RESULT;
    cbn [eval_alu32 Val.loword Val.add Val.sub Val.longofintu];
    unfold Int.add, Int.sub, Int64.loword;
    rewrite (Int.unsigned_repr (Int64.unsigned a)) by exact A;
    rewrite (Int.unsigned_repr (Int64.unsigned b)) by exact B;
    rewrite Int.unsigned_repr by exact RESULT; reflexivity.
Qed.

(** The exact, nonwrapping register-add/subtract arm. The old operands must
    retain their SSA names: [Def] still refers to them after updating [dst].
    This is stated explicitly, not hidden in concretization. *)
Theorem transfer_add_sub32_reg_sound_if_exact :
  forall (attrs : load_attrs) program regions before after concrete dst dst_value src op lo hi,
    (op = ArithmeticOp.Add \/ op = ArithmeticOp.Sub) ->
    ArithmeticHelpers.op32_binop_bounds (facts before)
      (register_name before dst) (register_name before src) op = Some (lo, hi) ->
    fresh_destination before dst dst_value ->
    dst_value <> register_name before dst ->
    program_register dst ->
    program_register src ->
    concretizes attrs regions before concrete ->
    transfer_arithmetic_defined before dst dst_value (Some dst) (inl src)
      OpSize.Op32 op = Some after ->
    exists concrete',
      instruction_step regions program
        (Palu (match op with ArithmeticOp.Sub => SUB | _ => ADD end) W32 dst (inl src))
        concrete concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after concrete dst dst_value src op lo hi
    OP EXACT FRESH LEFT_NAME DST_REGISTER SRC_REGISTER CONCRETE TRANSFER.
  pose proof (fresh_destination_operand_name _ _ _ FRESH LEFT_NAME src) as RIGHT_NAME.
  destruct concrete as [regs stack code_id count memory].
  destruct CONCRETE as [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]].
  destruct (ArithmeticHelpers.op32_binop_bounds_sound world memory (facts before)
    (register_name before dst) (register_name before src) op lo hi FACTS EXACT)
    as [a [b [AVALUE [BVALUE [_ [ABOUNDS [BBOUNDS [RESULT_BOUNDS [LOW HIGH]]]]]]]]].
  set (result := match op with ArithmeticOp.Sub => Int64.unsigned a - Int64.unsigned b
                             | _ => Int64.unsigned a + Int64.unsigned b end).
  assert (RESULT32 : 0 <= result <= Int.max_unsigned) by (unfold result; lia).
  assert (RESULT64 : 0 <= result <= Int64.max_unsigned).
  { assert (LIMIT : Int.max_unsigned <= Int64.max_unsigned).
    { change (4294967295 <= 18446744073709551615). lia. } lia. }
  assert (EVAL : eval_alu32 (match op with ArithmeticOp.Sub => SUB | _ => ADD end)
    (Vlong a) (inl (Vlong b)) = Vlong (Int64.repr result)).
  { apply eval_add_sub32_exact; assumption. }
  assert (DST : regs dst = Vlong a) by (rewrite <- REGISTERS by assumption; exact AVALUE).
  assert (SRC : regs src = Vlong b) by (rewrite <- REGISTERS by assumption; exact BVALUE).
  assert (VALUE : variable_value (assign_value world dst_value (Vlong (Int64.repr result)))
    dst_value = Vlong (Int64.repr result)) by apply variable_value_assign_same.
  assert (LEFT : variable_value (assign_value world dst_value (Vlong (Int64.repr result)))
    (register_name before dst) = Vlong a).
  { rewrite variable_value_assign_other; [exact AVALUE |apply Nat.eqb_neq; congruence]. }
  assert (RIGHT : variable_value (assign_value world dst_value (Vlong (Int64.repr result)))
    (register_name before src) = Vlong b).
  { rewrite variable_value_assign_other; [exact BVALUE |apply Nat.eqb_neq; congruence]. }
  unfold transfer_arithmetic_defined in TRANSFER.
  destruct (ensure_defined (facts before) (register_name before dst) &&
    ensure_defined (facts before) (register_name before src)); try discriminate.
  destruct OP as [-> | ->]; cbn [transfer_arithmetic transfer_add_sub option_map] in TRANSFER;
    rewrite EXACT in TRANSFER; inversion TRANSFER; subst after; clear TRANSFER.
  all: exists (TLS_State (nextinstr (Pregmap.set dst (Vlong (Int64.repr result)) regs))
    stack code_id count memory); split.
  - unfold instruction_step. cbn [exec_instr]. unfold exec_alu.
    cbn -[ireg_eqb eval_alu32]. rewrite DST, SRC.
    destruct (ireg_eqb dst src); exact (f_equal
      (fun value => Next (nextinstr (Pregmap.set dst value regs)) stack code_id count memory) EVAL).
  - eapply concretizes_register_update; [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |].
    cbn [append_arithmetic_def arithmetic_def_op]. repeat rewrite Forall_app. repeat split.
    + apply apply_havoc_holds; [exact FACTS |constructor].
    + constructor; [|constructor]. cbn [atom_holds eval_term definition_holds].
      rewrite VALUE, LEFT, RIGHT. cbn [definition_holds].
      rewrite Int64.unsigned_repr by exact RESULT64. reflexivity.
    + constructor; [|constructor]. cbn [atom_holds eval_term]. rewrite VALUE.
      cbn [value_holds u_lower u_upper]. rewrite Int64.unsigned_repr by exact RESULT64.
      exact RESULT_BOUNDS.
  - unfold instruction_step. cbn [exec_instr]. unfold exec_alu.
    cbn -[ireg_eqb eval_alu32]. rewrite DST, SRC. destruct (ireg_eqb dst src) eqn:SAME.
    + unfold ireg_eqb in SAME. destruct (ireg_eq dst src); try discriminate.
      subst src. rewrite DST in SRC. inversion SRC; subst b.
      unfold result. rewrite Z.sub_diag. reflexivity.
    + exact (f_equal
        (fun value => Next (nextinstr (Pregmap.set dst value regs)) stack code_id count memory) EVAL).
  - eapply concretizes_register_update; [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |].
    cbn [append_arithmetic_def arithmetic_def_op]. repeat rewrite Forall_app. repeat split.
    + apply apply_havoc_holds; [exact FACTS |constructor].
    + constructor; [|constructor]. cbn [atom_holds eval_term definition_holds].
      rewrite VALUE, LEFT, RIGHT. cbn [definition_holds].
      rewrite Int64.unsigned_repr by exact RESULT64. reflexivity.
    + constructor; [|constructor]. cbn [atom_holds eval_term]. rewrite VALUE.
      cbn [value_holds u_lower u_upper]. rewrite Int64.unsigned_repr by exact RESULT64.
      exact RESULT_BOUNDS.
Qed.

(** Unlike the exact-arm theorem, this covers both successful bounds inference
    and the wrapping fallback. Scalar operands are explicit premises. *)
Theorem transfer_add_sub32_reg_sound :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst src : ireg) dst_value op a b,
    (op = ArithmeticOp.Add \/ op = ArithmeticOp.Sub) ->
    regs dst = Vlong a -> regs src = Vlong b ->
    fresh_destination before dst dst_value ->
    dst_value <> register_name before dst ->
    program_register dst ->
    program_register src ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value (Some dst) (inl src) OpSize.Op32 op = Some after ->
    exists concrete', instruction_step regions program
      (Palu (match op with ArithmeticOp.Sub => SUB | _ => ADD end) W32 dst (inl src))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst src dst_value
    op a b OP DST SRC FRESH LEFT_NAME DST_REGISTER SRC_REGISTER CONCRETE TRANSFER.
  destruct (ArithmeticHelpers.op32_binop_bounds (facts before)
    (register_name before dst) (register_name before src) op) as [[lo hi]|] eqn:BOUNDS.
  - eapply transfer_add_sub32_reg_sound_if_exact; eauto.
  - destruct CONCRETE as [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]].
    assert (OPCODE : arithmetic_opcode op =
      Some (match op with ArithmeticOp.Sub => SUB | _ => ADD end)).
    { destruct OP as [-> | ->]; reflexivity. }
    destruct (exec_alu32_scalar op _ regs dst (inl src) stack code_id count memory a
      OPCODE DST (ex_intro _ b SRC)) as [n EXEC].
    unfold transfer_arithmetic_defined in TRANSFER.
    destruct (ensure_defined (facts before) (register_name before dst) &&
      ensure_defined (facts before) (register_name before src)); try discriminate.
    destruct OP as [-> | ->]; cbn [transfer_arithmetic transfer_add_sub option_map] in TRANSFER;
      rewrite BOUNDS in TRANSFER; inversion TRANSFER; subst after.
    all: exists (TLS_State (nextinstr (Pregmap.set dst (Vlong (Int64.repr (Int.unsigned n))) regs))
      stack code_id count memory); split.
    all: try solve [unfold instruction_step; cbn [exec_instr]; exact EXEC].
    all: eapply concretizes_register_update; [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |];
      apply havoc_word_holds; exact FACTS.
Qed.

Theorem transfer_neg64_sound :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst : ireg) dst_value source a,
    regs dst = Vlong a ->
    fresh_destination before dst dst_value ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value (Some dst) source OpSize.Op64 ArithmeticOp.Neg = Some after ->
    exists concrete', instruction_step regions program (Palu NEG W64 dst source)
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst dst_value
    source a DST FRESH CONCRETE TRANSFER.
  destruct CONCRETE as [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]].
  unfold transfer_arithmetic_defined in TRANSFER.
  destruct (ensure_defined (facts before) (register_name before dst) &&
    (match source with inl reg => ensure_defined (facts before) (register_name before reg)
     | inr _ => true end)); try discriminate.
  cbn [transfer_arithmetic option_map] in TRANSFER. inversion TRANSFER; subst after.
  exists (TLS_State (nextinstr (Pregmap.set dst (Vlong (Int64.neg a)) regs))
    stack code_id count memory). split.
  - unfold instruction_step. cbn [exec_instr]. unfold exec_alu.
    destruct source as [src|imm]; cbn -[ireg_eqb eval_alu64]; rewrite DST.
    + destruct (ireg_eqb dst src); reflexivity.
    + reflexivity.
  - eapply concretizes_register_update; [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |].
    apply apply_havoc_holds; [exact FACTS |constructor].
Qed.

(** The register-subtraction arm is sound whenever CompCert defines the
    difference: scalar-scalar, pointer-minus-scalar, and same-block
    pointer-minus-pointer all give a [runtime_value]. Scalar-minus-pointer and
    cross-region differences are [Vundef] and excluded by the premise. *)
Theorem transfer_sub64_reg_sound_if_defined :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst src : ireg) dst_value,
    runtime_value (Val.subl (regs dst) (regs src)) ->
    fresh_destination before dst dst_value ->
    dst_value <> register_name before dst ->
    program_register dst ->
    program_register src ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value (Some dst) (inl src)
      OpSize.Op64 ArithmeticOp.Sub = Some after ->
    exists concrete', instruction_step regions program (Palu SUB W64 dst (inl src))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst src dst_value
    RUNTIME FRESH LEFT_NAME DST_REGISTER SRC_REGISTER
    [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]] TRANSFER.
  pose proof (fresh_destination_operand_name _ _ _ FRESH LEFT_NAME src) as RIGHT_NAME.
  unfold transfer_arithmetic_defined in TRANSFER.
  destruct (ensure_defined (facts before) (register_name before dst) &&
    ensure_defined (facts before) (register_name before src)) eqn:DEFINED; try discriminate.
  apply andb_true_iff in DEFINED as [LEFT RIGHT].
  pose proof (ensure_defined_sound world memory _ _ FACTS LEFT) as LEFT_VALUE.
  rewrite REGISTERS in LEFT_VALUE by assumption.
  cbn [transfer_arithmetic transfer_add_sub option_map] in TRANSFER.
  inversion TRANSFER; subst after; clear TRANSFER.
  exists (TLS_State (nextinstr (Pregmap.set dst (Val.subl (regs dst) (regs src)) regs))
    stack code_id count memory). split.
  - unfold instruction_step. cbn [exec_instr]. unfold exec_alu.
    cbn -[ireg_eqb]. destruct (ireg_eqb dst src) eqn:SAME; [|reflexivity].
    unfold ireg_eqb in SAME. destruct (ireg_eq dst src); try discriminate.
    subst src. inversion LEFT_VALUE; subst; cbn [Val.subl].
    + rewrite Int64.sub_idem. reflexivity.
    + destruct (eq_block b b); [|contradiction].
      rewrite Ptrofs.sub_idem. reflexivity.
  - eapply concretizes_register_update; [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |].
    apply Forall_app. split; [apply apply_havoc_holds; assumption |].
    constructor; [|constructor]. cbn [atom_holds eval_term]. split.
    + cbn [assign_value variable_value]. destruct (Nat.eq_dec dst_value dst_value);
        [exact RUNTIME |contradiction].
    + rewrite (variable_value_assign_other world dst_value _ (register_name before dst)),
        (variable_value_assign_other world dst_value _ (register_name before src))
        by (apply Nat.eqb_neq; congruence).
      rewrite !REGISTERS by assumption. cbn [assign_value variable_value].
      destruct (Nat.eq_dec dst_value dst_value); congruence.
Qed.

(** The truncating arm of MOV32 does not propagate source descriptions. *)
Theorem transfer_mov32_reg_sound_if_truncated :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst src : ireg) dst_value a,
    ArithmeticHelpers.fits_u32 (facts before) (register_name before src) = false ->
    regs src = Vlong a -> fresh_destination before dst dst_value ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value None (inl src)
      OpSize.Op32 ArithmeticOp.Mov = Some after ->
    exists concrete', instruction_step regions program (Palu MOV W32 dst (inl src))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst src dst_value
    a TRUNCATE SRC FRESH [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]] TRANSFER.
  unfold transfer_arithmetic_defined in TRANSFER.
  destruct (true && ensure_defined (facts before) (register_name before src)); try discriminate.
  cbn [transfer_arithmetic option_map] in TRANSFER. rewrite TRUNCATE in TRANSFER.
  inversion TRANSFER; subst after; clear TRANSFER.
  exists (TLS_State (nextinstr (Pregmap.set dst
    (Vlong (Int64.repr (Int.unsigned (Int.repr (Int64.unsigned a))))) regs))
    stack code_id count memory). split.
  - unfold instruction_step. cbn [exec_instr]. unfold exec_alu.
    cbn -[ireg_eqb]. rewrite SRC. destruct (ireg_eqb dst src); reflexivity.
  - eapply concretizes_register_update; [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |].
    apply havoc_word_holds. exact FACTS.
Qed.

Theorem transfer_mov_reg_scalar_sound :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst src : ireg) dst_value size a,
    regs src = Vlong a -> fresh_destination before dst dst_value ->
    Forall (fun fact => atom_mentions dst_value fact = false) (facts before) ->
    ArithmeticHelpers.eq_constants_fit_i64 (facts before) ->
    program_register src ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value None (inl src) size ArithmeticOp.Mov = Some after ->
    exists concrete', instruction_step regions program
      (Palu MOV (match size with OpSize.Op32 => W32 | OpSize.Op64 => W64 end) dst (inl src))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst src dst_value size a
    SRC FRESH FRESH_FACTS CONSTANTS SRC_REGISTER CONCRETE TRANSFER.
  destruct (match size with OpSize.Op32 =>
    ArithmeticHelpers.fits_u32 (facts before) (register_name before src) | _ => true end) eqn:COPY.
  - destruct CONCRETE as [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]].
    assert (ASSIGNMENT : transfer_arithmetic (facts before) size dst_value None
      (SourceOperand.Value (register_name before src)) ArithmeticOp.Mov =
      ArithmeticHelpers.apply_assignment_var_offset entails (facts before) dst_value (register_name before src) 0).
    { destruct size; cbn [transfer_arithmetic apply_assignment]; try rewrite COPY; reflexivity. }
    unfold transfer_arithmetic_defined in TRANSFER.
    destruct (true && ensure_defined (facts before) (register_name before src)) eqn:DEFINED;
      try discriminate. cbn in DEFINED.
    cbn [option_map] in TRANSFER. rewrite ASSIGNMENT in TRANSFER.
    destruct (ArithmeticHelpers.apply_assignment_var_offset entails (facts before) dst_value
      (register_name before src) 0) as [post|] eqn:ASSIGN; try discriminate.
    inversion TRANSFER; subst after.
    assert (HOLDS : Forall (atom_holds (assign_value world dst_value (Vlong a)) memory) post).
    { pose proof (ArithmeticHelpers.apply_assignment_scalar_offset_holds entails world memory
        (facts before) dst_value (register_name before src) 0 a post FACTS CONSTANTS
        (ensure_defined_fresh_name _ _ _ FRESH_FACTS DEFINED)
        (eq_trans (REGISTERS src ltac:(assumption)) SRC) ASSIGN) as RESULT.
      now rewrite Int64.add_zero in RESULT. }
    exists (TLS_State (nextinstr (Pregmap.set dst (Vlong a) regs)) stack code_id count memory). split.
    + unfold instruction_step. cbn [exec_instr]. unfold exec_alu.
      cbn -[ireg_eqb eval_alu32 eval_alu64]. rewrite SRC. destruct size.
      * unfold ArithmeticHelpers.fits_u32 in COPY.
        destruct (ArithmeticHelpers.u32_bounds (facts before) (register_name before src))
          as [[lo hi]|] eqn:BOUNDS; try discriminate.
        destruct (ArithmeticHelpers.u32_bounds_sound world memory _ _ lo hi FACTS BOUNDS)
          as [a' [VALUE [RANGE [LOW HIGH]]]].
        rewrite REGISTERS, SRC in VALUE by assumption. inversion VALUE; subst a'.
        assert (NARROW : Int64.repr (Int.unsigned (Int.repr (Int64.unsigned a))) = a).
        { rewrite Int.unsigned_repr by lia. apply Int64.repr_unsigned. }
        destruct (ireg_eqb dst src);
          change (Next (nextinstr (Pregmap.set dst
            (Vlong (Int64.repr (Int.unsigned (Int.repr (Int64.unsigned a))))) regs))
            stack code_id count memory =
            Next (nextinstr (Pregmap.set dst (Vlong a) regs)) stack code_id count memory);
          rewrite NARROW; reflexivity.
      * destruct (ireg_eqb dst src); reflexivity.
    + eapply concretizes_register_update; eauto.
  - destruct size; [|discriminate]. eapply transfer_mov32_reg_sound_if_truncated; eauto.
Qed.

Theorem transfer_mov32_reg_sound_if_copied :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst src : ireg) dst_value,
    ArithmeticHelpers.fits_u32 (facts before) (register_name before src) = true ->
    fresh_destination before dst dst_value ->
    Forall (fun fact => atom_mentions dst_value fact = false) (facts before) ->
    ArithmeticHelpers.eq_constants_fit_i64 (facts before) ->
    program_register src ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value None (inl src)
      OpSize.Op32 ArithmeticOp.Mov = Some after ->
    exists concrete', instruction_step regions program (Palu MOV W32 dst (inl src))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst src dst_value
    FITS FRESH FRESH_FACTS CONSTANTS SRC_REGISTER CONCRETE TRANSFER.
  pose proof CONCRETE as [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]].
  unfold ArithmeticHelpers.fits_u32 in FITS.
  destruct (ArithmeticHelpers.u32_bounds (facts before) (register_name before src))
    as [[lo hi]|] eqn:BOUNDS; try discriminate.
  destruct (ArithmeticHelpers.u32_bounds_sound world memory _ _ lo hi FACTS BOUNDS)
    as [a [VALUE RANGE]].
  eapply transfer_mov_reg_scalar_sound with (size := OpSize.Op32); eauto.
  rewrite <- REGISTERS by assumption. exact VALUE.
Qed.


Theorem transfer_mov64_reg_sound :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst src : ireg) dst_value,
    fresh_destination before dst dst_value ->
    Forall (fun fact => atom_mentions dst_value fact = false) (facts before) ->
    ArithmeticHelpers.eq_constants_fit_i64 (facts before) ->
    program_register src ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value None (inl src) OpSize.Op64 ArithmeticOp.Mov = Some after ->
    exists concrete', instruction_step regions program (Palu MOV W64 dst (inl src))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst src dst_value
    FRESH FRESH_FACTS CONSTANTS
    SRC_REGISTER [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]] TRANSFER.
  unfold transfer_arithmetic_defined in TRANSFER.
  destruct (true && ensure_defined (facts before) (register_name before src)) eqn:DEFINED;
    try discriminate. cbn in DEFINED.
  pose proof (ensure_defined_sound world memory _ _ FACTS DEFINED) as RUNTIME.
  cbn [transfer_arithmetic apply_assignment option_map] in TRANSFER.
  destruct (ArithmeticHelpers.apply_assignment_var_offset entails (facts before) dst_value
    (register_name before src) 0) as [post|] eqn:COPY; try discriminate.
  inversion TRANSFER; subst after.
  exists (TLS_State (nextinstr (Pregmap.set dst (regs src) regs)) stack code_id count memory). split.
  - unfold instruction_step. cbn [exec_instr]. unfold exec_alu.
    cbn -[ireg_eqb]. destruct (ireg_eqb dst src); reflexivity.
  - eapply concretizes_register_update;
      [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |].
    rewrite <- (REGISTERS src ltac:(assumption)).
    eapply ArithmeticHelpers.apply_assignment_copy_holds; eauto.
Qed.

Lemma and32_upper_bound_sound : forall world memory state lhs source a rhs,
  variable_value world lhs = Vlong a ->
  (match source with SourceOperand.Imm imm => rhs = imm
   | SourceOperand.Value name => exists b, variable_value world name = Vlong b /\
       rhs = Int.repr (Int64.unsigned b) end) ->
  Forall (atom_holds world memory) state ->
  0 <= Int.unsigned (Int.and (Int.repr (Int64.unsigned a)) rhs) <=
    ArithmeticHelpers.and32_upper_bound state lhs source.
Proof.
  intros world memory state lhs source a rhs LEFT RIGHT FACTS.
  set (operand := fun name => match ArithmeticHelpers.u32_bounds state name with
    | Some (_, hi) => if (0 <=? hi) && (hi <=? Int.max_unsigned) then Some hi else None
    | None => None end).
  assert (OPERAND : forall name n hi, variable_value world name = Vlong n ->
    operand name = Some hi -> Int.unsigned (Int.repr (Int64.unsigned n)) <= hi).
  { intros name n hi VALUE BOUND. unfold operand in BOUND.
    destruct (ArithmeticHelpers.u32_bounds state name) as [[lo high]|] eqn:FOUND;
      try discriminate.
    destruct ((0 <=? high) && (high <=? Int.max_unsigned)); try discriminate.
    inversion BOUND; subst high.
    destruct (ArithmeticHelpers.u32_bounds_sound world memory state name lo hi FACTS FOUND)
      as [n' [VALUE' [BOUNDS [LOW HIGH]]]].
    rewrite VALUE in VALUE'. inversion VALUE'; subst n'.
    rewrite Int.unsigned_repr; lia. }
  pose proof (Int.unsigned_range_2 (Int.and (Int.repr (Int64.unsigned a)) rhs)) as RANGE.
  pose proof (Int.and_le (Int.repr (Int64.unsigned a)) rhs) as LIMIT_LEFT.
  pose proof (Int.and_le rhs (Int.repr (Int64.unsigned a))) as LIMIT_RIGHT.
  rewrite Int.and_commut in LIMIT_RIGHT.
  split; [lia |].
  destruct source as [imm|name].
  - subst rhs. change (Int.unsigned (Int.and (Int.repr (Int64.unsigned a)) imm) <=
      match operand lhs with Some hi => Z.min hi (Int.unsigned imm)
      | None => Int.unsigned imm end).
    destruct (operand lhs) as [hi|] eqn:BOUND; [|exact LIMIT_RIGHT].
    apply Z.min_glb; [|exact LIMIT_RIGHT].
    eapply Z.le_trans; [exact LIMIT_LEFT |eapply OPERAND; eauto].
  - destruct RIGHT as [b [VALUE ->]].
    change (Int.unsigned (Int.and (Int.repr (Int64.unsigned a)) (Int.repr (Int64.unsigned b))) <=
      match operand lhs, operand name with Some hi, Some hi' => Z.min hi hi'
      | Some hi, None | None, Some hi => hi | None, None => Int.max_unsigned end).
    destruct (operand lhs) as [hi|] eqn:BOUND_LEFT;
      destruct (operand name) as [hi'|] eqn:BOUND_RIGHT;
      cbn -[Int.max_unsigned Int.unsigned Int.and Int.repr Int64.unsigned].
    + apply Z.min_glb; eapply Z.le_trans;
        [exact LIMIT_LEFT |eapply OPERAND; eauto |exact LIMIT_RIGHT |eapply OPERAND; eauto].
    + eapply Z.le_trans; [exact LIMIT_LEFT |eapply OPERAND; eauto].
    + eapply Z.le_trans; [exact LIMIT_RIGHT |eapply OPERAND; eauto].
    + exact (proj2 RANGE).
Qed.

Theorem transfer_and32_sound :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst : ireg) dst_value source a,
    regs dst = Vlong a -> scalar_source regs source ->
    fresh_destination before dst dst_value ->
    program_register dst ->
    program_operand source ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value (Some dst) source
      OpSize.Op32 ArithmeticOp.And = Some after ->
    exists concrete', instruction_step regions program (Palu AND W32 dst source)
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst dst_value
    source a DST SOURCE FRESH DST_REGISTER SOURCE_REGISTER [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]] TRANSFER.
  unfold transfer_arithmetic_defined in TRANSFER.
  destruct (ensure_defined (facts before) (register_name before dst) &&
    match source with inl reg => ensure_defined (facts before) (register_name before reg)
    | inr _ => true end); try discriminate.
  cbn [transfer_arithmetic option_map] in TRANSFER.
  set (operand := match source with inl reg => SourceOperand.Value (register_name before reg)
    | inr imm => SourceOperand.Imm imm end) in *.
  inversion TRANSFER; subst after; clear TRANSFER.
  assert (LEFT : variable_value world (register_name before dst) = Vlong a)
    by (rewrite REGISTERS by assumption; exact DST).
  destruct source as [src|imm].
  - destruct SOURCE as [b SRC].
    pose proof (and32_upper_bound_sound world memory (facts before) (register_name before dst)
      (SourceOperand.Value (register_name before src)) a (Int.repr (Int64.unsigned b))
      LEFT (ex_intro _ b (conj (eq_trans (REGISTERS src ltac:(assumption)) SRC) eq_refl)) FACTS) as BOUNDS.
    set (n := Int.and (Int.repr (Int64.unsigned a)) (Int.repr (Int64.unsigned b))) in *.
    exists (TLS_State (nextinstr (Pregmap.set dst (Vlong (Int64.repr (Int.unsigned n))) regs))
      stack code_id count memory). split.
    + unfold instruction_step. cbn [exec_instr]. unfold exec_alu.
      cbn -[ireg_eqb]. rewrite DST, SRC. destruct (ireg_eqb dst src); reflexivity.
    + eapply concretizes_register_update; [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |].
      apply havoc_bounded_word_holds; assumption.
  - pose proof (and32_upper_bound_sound world memory (facts before) (register_name before dst)
      (SourceOperand.Imm imm) a imm LEFT eq_refl FACTS) as BOUNDS.
    set (n := Int.and (Int.repr (Int64.unsigned a)) imm) in *.
    exists (TLS_State (nextinstr (Pregmap.set dst (Vlong (Int64.repr (Int.unsigned n))) regs))
      stack code_id count memory). split.
    + unfold instruction_step. cbn [exec_instr]. unfold exec_alu. cbn. rewrite DST. reflexivity.
    + eapply concretizes_register_update; [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |].
      apply havoc_bounded_word_holds; assumption.
Qed.

Lemma eval_add_sub32_imm_wrap : forall op a immediate,
  (op = ArithmeticOp.Add \/ op = ArithmeticOp.Sub) ->
  eval_alu32 (match op with ArithmeticOp.Sub => SUB | _ => ADD end) (Vlong a) (inr immediate) =
  eval_alu32 ADD (Vlong a) (inl (Vlong (Int64.repr
    (match op with ArithmeticOp.Sub => - Int.signed immediate | _ => Int.signed immediate end)))).
Proof.
  intros op a immediate [-> | ->];
    cbn [eval_alu32 eval_val_int Val.loword Val.add Val.sub Val.longofintu];
    unfold Int64.loword;
    rewrite loword_repr64.
  - rewrite Int.repr_signed. reflexivity.
  - rewrite Int.sub_add_opp, <- Int.neg_repr, Int.repr_signed. reflexivity.
Qed.

Theorem transfer_add_sub32_imm_sound_if_wrapping :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst : ireg) dst_value immediate op a,
    (op = ArithmeticOp.Add \/ op = ArithmeticOp.Sub) ->
    ArithmeticHelpers.op32_shift_exact (facts before) (register_name before dst)
      (match op with ArithmeticOp.Sub => - Int.signed immediate | _ => Int.signed immediate end) = false ->
    regs dst = Vlong a -> fresh_destination before dst dst_value ->
    dst_value <> register_name before dst ->
    program_register dst ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value (Some dst) (inr immediate)
      OpSize.Op32 op = Some after ->
    exists concrete', instruction_step regions program
      (Palu (match op with ArithmeticOp.Sub => SUB | _ => ADD end) W32 dst (inr immediate))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst dst_value
    immediate op a OP WRAPPING DST FRESH NEWNAME DST_REGISTER [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]] TRANSFER.
  set (offset := match op with ArithmeticOp.Sub => - Int.signed immediate | _ => Int.signed immediate end).
  destruct (eval_alu32_scalar op (match op with ArithmeticOp.Sub => SUB | _ => ADD end)
    a (inr immediate) ltac:(destruct OP as [-> | ->]; reflexivity)) as [n EVAL].
  assert (LEFT : variable_value world (register_name before dst) = Vlong a)
    by (rewrite REGISTERS by assumption; exact DST).
  assert (POST : Forall (atom_holds (assign_value world dst_value
      (Vlong (Int64.repr (Int.unsigned n)))) memory)
    (apply_havoc_with_size (facts before) dst_value Word ++
      [Def dst_value (DefOp.AddWrap OpSize.Op32) (Var (register_name before dst)) (Const offset)])).
  { apply Forall_app. split; [apply havoc_word_holds; exact FACTS |].
    constructor; [| constructor].
    cbn [atom_holds eval_term].
    rewrite (variable_value_assign_other world dst_value _ (register_name before dst))
      by (apply Nat.eqb_neq; congruence).
    rewrite LEFT. cbn [assign_value variable_value].
    destruct (Nat.eq_dec dst_value dst_value); [|contradiction].
    change (Vlong (Int64.repr (Int.unsigned n)) = eval_alu32 ADD (Vlong a)
      (inl (Vlong (Int64.repr (match op with ArithmeticOp.Sub => - Int.signed immediate
        | _ => Int.signed immediate end))))).
    rewrite <- (eval_add_sub32_imm_wrap op a immediate OP).
    exact (eq_sym EVAL). }
  unfold transfer_arithmetic_defined in TRANSFER.
  destruct (ensure_defined (facts before) (register_name before dst) && true); try discriminate.
  destruct OP as [-> | ->]; cbn [transfer_arithmetic transfer_add_sub option_map] in TRANSFER;
    rewrite WRAPPING in TRANSFER; inversion TRANSFER; subst after.
  all: exists (TLS_State (nextinstr (Pregmap.set dst (Vlong (Int64.repr (Int.unsigned n))) regs))
    stack code_id count memory); split.
  all: try solve [unfold instruction_step; cbn [exec_instr]; unfold exec_alu;
    cbn -[eval_alu32]; rewrite DST, EVAL; reflexivity].
  all: eapply concretizes_register_update; eauto.
Qed.

Lemma eval_add_sub64_imm_offset : forall op value immediate,
  (op = ArithmeticOp.Add \/ op = ArithmeticOp.Sub) ->
  eval_alu64 (match op with ArithmeticOp.Sub => SUB | _ => ADD end) value (inr immediate) =
    Val.addl value (Vlong (Int64.repr
      (match op with ArithmeticOp.Sub => - Int.signed immediate | _ => Int.signed immediate end))).
Proof.
  intros op value immediate [-> | ->];
    cbn [eval_alu64 eval_val_int]; unfold int64_of_int; [reflexivity |].
  rewrite Val.subl_addl_opp, Int64.neg_repr. reflexivity.
Qed.

Theorem transfer_add_sub_imm_assignment_sound :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst : ireg) dst_value size immediate op a,
    (op = ArithmeticOp.Add \/ op = ArithmeticOp.Sub) ->
    (size = OpSize.Op32 -> ArithmeticHelpers.op32_shift_exact (facts before) (register_name before dst)
      (match op with ArithmeticOp.Sub => - Int.signed immediate | _ => Int.signed immediate end) = true) ->
    regs dst = Vlong a -> fresh_destination before dst dst_value ->
    Forall (fun fact => atom_mentions dst_value fact = false) (facts before) ->
    ArithmeticHelpers.eq_constants_fit_i64 (facts before) ->
    program_register dst ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value (Some dst) (inr immediate) size op = Some after ->
    exists concrete', instruction_step regions program
      (Palu (match op with ArithmeticOp.Sub => SUB | _ => ADD end)
        (match size with OpSize.Op32 => W32 | OpSize.Op64 => W64 end) dst (inr immediate))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst dst_value size
    immediate op a OPS EXACT DST FRESH FRESH_FACTS CONSTANTS
    DST_REGISTER [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]] TRANSFER.
  set (offset := match op with ArithmeticOp.Sub => - Int.signed immediate
    | _ => Int.signed immediate end).
  assert (SOURCE : variable_value world (register_name before dst) = Vlong a) by
    (rewrite REGISTERS by assumption; exact DST).
  assert (ASSIGNMENT : transfer_arithmetic (facts before) size dst_value
    (Some (register_name before dst)) (SourceOperand.Imm immediate) op =
    ArithmeticHelpers.apply_assignment_var_offset entails (facts before) dst_value (register_name before dst) offset).
  { destruct OPS as [-> | ->]; destruct size; cbn [transfer_arithmetic transfer_add_sub apply_assignment];
      try rewrite (EXACT eq_refl); reflexivity. }
  unfold transfer_arithmetic_defined in TRANSFER.
  destruct (ensure_defined (facts before) (register_name before dst) && true) eqn:DEFINED;
    try discriminate.
  rewrite andb_true_r in DEFINED.
  pose proof (ensure_defined_fresh_name _ _ _ FRESH_FACTS DEFINED) as DIFFERENT.
  cbn [option_map] in TRANSFER. rewrite ASSIGNMENT in TRANSFER.
  destruct (ArithmeticHelpers.apply_assignment_var_offset entails (facts before) dst_value
    (register_name before dst) offset) as [post|] eqn:ASSIGN; try discriminate.
  inversion TRANSFER; subst after.
  exists (TLS_State (nextinstr (Pregmap.set dst (Vlong (Int64.add a (Int64.repr offset))) regs))
    stack code_id count memory). split.
  - unfold instruction_step. cbn [exec_instr]. unfold exec_alu.
    cbn -[eval_alu32 eval_alu64]. rewrite DST. destruct size.
    + destruct (ArithmeticHelpers.op32_shift_exact_sound world memory (facts before)
        (register_name before dst) offset FACTS (EXACT eq_refl))
        as [a' [VALUE [RANGE BOUND]]].
      rewrite SOURCE in VALUE. inversion VALUE; subst a'.
      rewrite eval_add_sub32_imm_wrap by exact OPS.
      cbn [eval_alu32 eval_val_int Val.loword Val.add Val.longofintu].
      unfold Int64.loword. rewrite loword_repr64, ArithmeticHelpers.repr_add32.
      fold offset. rewrite Int.unsigned_repr by exact BOUND.
      assert (RESULT : Int64.repr (Int64.unsigned a + offset) = Int64.add a (Int64.repr offset)).
      { rewrite <- (Int64.repr_unsigned a) at 2. symmetry. apply ArithmeticHelpers.repr_add. }
      rewrite RESULT. reflexivity.
    + rewrite eval_add_sub64_imm_offset by exact OPS. reflexivity.
  - eapply concretizes_register_update; [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |].
    eapply ArithmeticHelpers.apply_assignment_scalar_offset_holds; eauto.
Qed.

Theorem transfer_add64_reg_sound_without_pointer_result_if_integer_operand :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst src : ireg) dst_value,
    ArithmeticHelpers.derived_ptr_add_reg (facts before)
      (register_name before dst) (register_name before src) = None ->
    ((exists a, regs dst = Vlong a) \/ (exists b, regs src = Vlong b)) ->
    fresh_destination before dst dst_value ->
    program_register dst ->
    program_register src ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value (Some dst) (inl src)
      OpSize.Op64 ArithmeticOp.Add = Some after ->
    exists concrete', instruction_step regions program (Palu ADD W64 dst (inl src))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst src dst_value
    NO_POINTER INTEGER FRESH DST_REGISTER SRC_REGISTER [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]] TRANSFER.
  unfold transfer_arithmetic_defined in TRANSFER.
  destruct (ensure_defined (facts before) (register_name before dst) &&
    ensure_defined (facts before) (register_name before src)) eqn:DEFINED; try discriminate.
  apply andb_true_iff in DEFINED as [LEFT RIGHT].
  pose proof (ensure_defined_sound world memory _ _ FACTS LEFT) as LEFT_VALUE.
  pose proof (ensure_defined_sound world memory _ _ FACTS RIGHT) as RIGHT_VALUE.
  rewrite REGISTERS in LEFT_VALUE, RIGHT_VALUE by assumption.
  assert (RUNTIME : runtime_value (Val.addl (regs dst) (regs src))).
  { destruct INTEGER as [[a DST]|[b SRC]];
      inversion LEFT_VALUE; inversion RIGHT_VALUE; subst;
      rewrite ?DST, ?SRC in *; try discriminate; cbn [Val.addl]; constructor. }
  cbn [transfer_arithmetic transfer_add_sub option_map] in TRANSFER.
  rewrite NO_POINTER, app_nil_r in TRANSFER. inversion TRANSFER; subst after.
  exists (TLS_State (nextinstr (Pregmap.set dst (Val.addl (regs dst) (regs src)) regs))
    stack code_id count memory). split.
  - unfold instruction_step. cbn [exec_instr]. unfold exec_alu.
    cbn -[ireg_eqb]. destruct (ireg_eqb dst src); reflexivity.
  - eapply concretizes_register_update; [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |].
    apply apply_havoc_holds; assumption.
Qed.

Theorem transfer_add64_reg_sound_if_pointer_inferred :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst src : ireg) dst_value ptr,
    fresh_destination before dst dst_value ->
    ArithmeticHelpers.derived_ptr_add_reg (facts before)
      (register_name before dst) (register_name before src) = Some ptr ->
    program_register dst ->
    program_register src ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value (Some dst) (inl src)
      OpSize.Op64 ArithmeticOp.Add = Some after ->
    exists concrete', instruction_step regions program (Palu ADD W64 dst (inl src))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst src dst_value ptr
    FRESH INFERRED DST_REGISTER SRC_REGISTER [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]] TRANSFER.
  pose proof (ArithmeticHelpers.derived_ptr_add_reg_holds world memory (facts before)
    (register_name before dst) (register_name before src) (regs dst) (regs src) ptr FACTS
    (REGISTERS dst ltac:(assumption)) (REGISTERS src ltac:(assumption)) INFERRED) as POINTER.
  assert (RUNTIME : runtime_value (Val.addl (regs dst) (regs src))).
  { eapply initialized_value_holds with (abstract := Ptr ptr); [discriminate |exact POINTER]. }
  unfold transfer_arithmetic_defined in TRANSFER.
  destruct (ensure_defined (facts before) (register_name before dst) &&
    ensure_defined (facts before) (register_name before src)); try discriminate.
  cbn [transfer_arithmetic transfer_add_sub option_map] in TRANSFER.
  rewrite INFERRED in TRANSFER. inversion TRANSFER; subst after.
  exists (TLS_State (nextinstr (Pregmap.set dst (Val.addl (regs dst) (regs src)) regs))
    stack code_id count memory). split.
  - unfold instruction_step. cbn [exec_instr]. unfold exec_alu.
    cbn -[ireg_eqb]. destruct (ireg_eqb dst src); reflexivity.
  - eapply concretizes_register_update;
      [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |].
    apply Forall_app. split; [apply apply_havoc_holds; assumption |].
    constructor; [|constructor]. cbn [atom_holds eval_term].
    rewrite variable_value_assign_same, value_holds_assign. exact POINTER.
Qed.

Theorem transfer_add64_reg_sound :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst src : ireg) dst_value,
    ((exists a, regs dst = Vlong a) \/ (exists b, regs src = Vlong b)) ->
    fresh_destination before dst dst_value ->
    program_register dst ->
    program_register src ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value (Some dst) (inl src)
      OpSize.Op64 ArithmeticOp.Add = Some after ->
    exists concrete', instruction_step regions program (Palu ADD W64 dst (inl src))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst src dst_value
    INTEGER FRESH DST_REGISTER SRC_REGISTER CONCRETE TRANSFER.
  destruct (ArithmeticHelpers.derived_ptr_add_reg (facts before)
    (register_name before dst) (register_name before src)) as [ptr|] eqn:INFERRED.
  - eapply transfer_add64_reg_sound_if_pointer_inferred; eauto.
  - eapply transfer_add64_reg_sound_without_pointer_result_if_integer_operand; eauto.
Qed.

Lemma eval_shift64_immediate : forall op opcode a immediate,
  In op [ArithmeticOp.Lsh; ArithmeticOp.Rsh; ArithmeticOp.Arsh] ->
  arithmetic_opcode op = Some opcode ->
  let count := Z.land (Int64.unsigned (Int64.repr (Int.signed immediate))) 63 in
  eval_alu64 opcode (Vlong a) (inr immediate) = Vlong (Int64.repr
    (match op with
     | ArithmeticOp.Lsh => Z.shiftl (Int64.unsigned a) count
     | ArithmeticOp.Rsh => Z.shiftr (Int64.unsigned a) count
     | _ => Z.shiftr (Int64.signed a) count
     end)).
Proof.
  intros op opcode a immediate OPS OPCODE count.
  destruct op; cbn in OPS; try solve [exfalso; intuition discriminate];
    inversion OPCODE; subst opcode;
    cbn [eval_alu64 eval_val_int eval_shift_mask int_of_int64 Val.and Val.shll Val.shrlu Val.shrl];
    unfold int_of_int64, int64_of_int;
    rewrite shift_mask64_in_range;
    unfold Int64.shl', Int64.shru', Int64.shr';
    rewrite shift_mask64_count; reflexivity.
Qed.

Lemma shift64_immediate_count : forall immediate,
  0 <= Int.signed immediate <= 63 ->
  Z.land (Int64.unsigned (Int64.repr (Int.signed immediate))) 63 = Int.signed immediate.
Proof.
  intros immediate RANGE. rewrite Int64.unsigned_repr by
    (change (0 <= Int.signed immediate <= 18446744073709551615); lia).
  replace 63 with (Z.ones 6) by reflexivity. rewrite Z.land_ones by lia.
  change (Int.signed immediate mod 64 = Int.signed immediate).
  apply Z.mod_small. lia.
Qed.

(** Immediate masks and multipliers clear the claimed low bits, including when
    the 64-bit result wraps. The claimed power-of-two modulus divides 2^64. *)
Lemma pow2_stride_and_mul_sound : forall op a immediate stride,
  In op [ArithmeticOp.And; ArithmeticOp.Mul] ->
  ArithmeticHelpers.pow2_stride op (Int.signed immediate) = Some stride ->
  let n := match op with
    | ArithmeticOp.And => Int64.and a (Int64.repr (Int.signed immediate))
    | _ => Int64.mul a (Int64.repr (Int.signed immediate)) end in
  0 < stride /\ Int64.signed n mod stride = 0.
Proof.
  intros op a immediate stride OPS STRIDE n.
  set (bits := Z.min (ArithmeticHelpers.trailing_zeros 64
    (ArithmeticHelpers.unsigned64 (Int.signed immediate))) 63).
  assert (SHAPE : (0 <? bits) = true /\ stride = 2 ^ bits).
  { destruct op; cbn in OPS; try solve [exfalso; intuition discriminate];
      unfold ArithmeticHelpers.pow2_stride in STRIDE;
      fold bits in STRIDE; destruct (0 <? bits) eqn:POS; inversion STRIDE; auto. }
  destruct SHAPE as [POS ->]. apply Z.ltb_lt in POS.
  destruct (ArithmeticHelpers.trailing_zeros_divides 64
    (ArithmeticHelpers.unsigned64 (Int.signed immediate))) as [BOUNDS DIVIDES].
  assert (BITS : bits <= ArithmeticHelpers.trailing_zeros 64
    (ArithmeticHelpers.unsigned64 (Int.signed immediate)) /\ bits <= 63).
  { unfold bits. split; [apply Z.le_min_l |apply Z.le_min_r]. }
  assert (SMALL : (2 ^ bits | ArithmeticHelpers.unsigned64 (Int.signed immediate))).
  { eapply Z.divide_trans; [|exact DIVIDES].
    exists (2 ^ (ArithmeticHelpers.trailing_zeros 64
      (ArithmeticHelpers.unsigned64 (Int.signed immediate)) - bits)).
    rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (MODULUS : (2 ^ bits | Int64.modulus)).
  { exists (2 ^ (64 - bits)). change Int64.modulus with (2 ^ 64).
    rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (POWER : 0 < 2 ^ bits) by (apply Z.pow_pos_nonneg; lia).
  split; [exact POWER |].
  destruct op; cbn in OPS; try solve [exfalso; intuition discriminate];
    unfold n, Int64.and, Int64.mul.
  - change (ArithmeticHelpers.signed64
      (Int64.unsigned a * Int64.unsigned (Int64.repr (Int.signed immediate)))
      mod 2 ^ bits = 0).
    rewrite ArithmeticHelpers.signed64_mod_divisor by assumption.
    apply (proj2 (Z.mod_divide
      (Int64.unsigned a * Int64.unsigned (Int64.repr (Int.signed immediate)))
      (2 ^ bits) ltac:(lia))).
    destruct SMALL as [k EQ]. exists (Int64.unsigned a * k).
    unfold ArithmeticHelpers.unsigned64 in EQ. rewrite EQ. ring.
  - change (ArithmeticHelpers.signed64
      (Z.land (Int64.unsigned a) (Int64.unsigned (Int64.repr (Int.signed immediate))))
      mod 2 ^ bits = 0).
    rewrite ArithmeticHelpers.signed64_mod_divisor by assumption.
    rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc.
    rewrite Z.land_ones by lia.
    change (Int64.unsigned (Int64.repr (Int.signed immediate))) with
      (ArithmeticHelpers.unsigned64 (Int.signed immediate)).
    rewrite (proj2 (Z.mod_divide
      (ArithmeticHelpers.unsigned64 (Int.signed immediate)) (2 ^ bits)
      ltac:(lia)) SMALL).
    apply Z.land_0_r.
Qed.

Theorem transfer_add_sub64_imm_sound :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst : ireg) dst_value immediate op,
    (op = ArithmeticOp.Add \/ op = ArithmeticOp.Sub) ->
    fresh_destination before dst dst_value ->
    Forall (fun fact => atom_mentions dst_value fact = false) (facts before) ->
    ArithmeticHelpers.eq_constants_fit_i64 (facts before) ->
    program_register dst ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value (Some dst) (inr immediate)
      OpSize.Op64 op = Some after ->
    exists concrete', instruction_step regions program
      (Palu (match op with ArithmeticOp.Sub => SUB | _ => ADD end) W64 dst (inr immediate))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst dst_value
    immediate op OPS FRESH FRESH_FACTS CONSTANTS
    DST_REGISTER [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]] TRANSFER.
  set (offset := match op with ArithmeticOp.Sub => - Int.signed immediate
    | _ => Int.signed immediate end).
  unfold transfer_arithmetic_defined in TRANSFER.
  destruct (ensure_defined (facts before) (register_name before dst) && true) eqn:DEFINED;
    try discriminate.
  rewrite andb_true_r in DEFINED.
  pose proof (ensure_defined_sound world memory _ _ FACTS DEFINED) as RUNTIME.
  pose proof (ensure_defined_fresh_name _ _ _ FRESH_FACTS DEFINED) as DIFFERENT.
  assert (ASSIGNMENT : transfer_arithmetic (facts before) OpSize.Op64 dst_value
    (Some (register_name before dst)) (SourceOperand.Imm immediate) op =
    ArithmeticHelpers.apply_assignment_var_offset entails (facts before) dst_value
      (register_name before dst) offset).
  { destruct OPS as [-> | ->]; reflexivity. }
  cbn [option_map] in TRANSFER. rewrite ASSIGNMENT in TRANSFER.
  destruct (ArithmeticHelpers.apply_assignment_var_offset entails (facts before) dst_value
    (register_name before dst) offset) as [post|] eqn:ASSIGN; try discriminate.
  inversion TRANSFER; subst after.
  exists (TLS_State (nextinstr (Pregmap.set dst
    (Val.addl (regs dst) (Vlong (Int64.repr offset))) regs)) stack code_id count memory). split.
  - unfold instruction_step. cbn [exec_instr]. unfold exec_alu.
    cbn -[eval_alu64]. rewrite eval_add_sub64_imm_offset by exact OPS. reflexivity.
  - eapply concretizes_register_update;
      [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |].
    rewrite <- (REGISTERS dst ltac:(assumption)).
    eapply ArithmeticHelpers.apply_assignment_offset_holds;
      [exact FACTS |exact RUNTIME |reflexivity | | |exact ASSIGN].
    + rewrite variable_value_assign_other; [reflexivity |now apply Nat.eqb_neq].
    + intros. eapply ArithmeticHelpers.derive_value_holds; eauto.
Qed.

Lemma pow2_stride_lsh_sound : forall a immediate stride,
  ArithmeticHelpers.pow2_stride ArithmeticOp.Lsh (Int.signed immediate) = Some stride ->
  exists n, eval_alu64 LSH (Vlong a) (inr immediate) = Vlong n /\
    0 < stride /\ Int64.signed n mod stride = 0.
Proof.
  intros a immediate stride STRIDE.
  unfold ArithmeticHelpers.pow2_stride in STRIDE.
  destruct ((0 <=? Int.signed immediate) && (Int.signed immediate <? 64)) eqn:WIDTH;
    try discriminate.
  destruct (0 <? Z.min (Int.signed immediate) 63) eqn:POS; try discriminate.
  inversion STRIDE; subst stride.
  apply andb_true_iff in WIDTH as [LOW HIGH]. apply Z.leb_le in LOW. apply Z.ltb_lt in HIGH.
  apply Z.ltb_lt in POS. rewrite Z.min_l in * by lia.
  pose proof (eval_shift64_immediate ArithmeticOp.Lsh LSH a immediate
    ltac:(cbn; auto) eq_refl) as EVAL.
  cbn zeta in EVAL. rewrite shift64_immediate_count in EVAL by lia.
  eexists. split; [exact EVAL |].
  assert (POWER : 0 < 2 ^ Int.signed immediate) by (apply Z.pow_pos_nonneg; lia).
  assert (MODULUS : (2 ^ Int.signed immediate | Int64.modulus)).
  { exists (2 ^ (64 - Int.signed immediate)). change Int64.modulus with (2 ^ 64).
    rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  split; [exact POWER |].
  change (ArithmeticHelpers.signed64 (Z.shiftl (Int64.unsigned a) (Int.signed immediate))
    mod 2 ^ Int.signed immediate = 0).
  rewrite ArithmeticHelpers.signed64_mod_divisor by assumption.
  rewrite Z.shiftl_mul_pow2 by lia. apply Z.mod_mul. lia.
Qed.

Lemma rsh64_immediate_bound : forall a immediate,
  1 <= Int.signed immediate <= 63 ->
  exists n, eval_alu64 RSH (Vlong a) (inr immediate) = Vlong n /\
    0 <= Int64.unsigned n <= Z.shiftr Int64.max_unsigned (Int.signed immediate).
Proof.
  intros a immediate WIDTH.
  pose proof (eval_shift64_immediate ArithmeticOp.Rsh RSH a immediate
    ltac:(cbn; auto) eq_refl) as EVAL.
  cbn zeta in EVAL. rewrite shift64_immediate_count in EVAL by lia.
  eexists. split; [exact EVAL |].
  assert (POWER : 0 < 2 ^ Int.signed immediate) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Int64.unsigned_range_2 a) as RANGE.
  assert (BOUND : 0 <= Z.shiftr (Int64.unsigned a) (Int.signed immediate) <=
    Z.shiftr Int64.max_unsigned (Int.signed immediate)).
  { rewrite !Z.shiftr_div_pow2 by lia. split;
      [apply Z.div_pos; lia |apply Z.div_le_mono; lia]. }
  assert (MAX : Z.shiftr Int64.max_unsigned (Int.signed immediate) <= Int64.max_unsigned).
  { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_le_upper_bound; nia. }
  rewrite Int64.unsigned_repr by lia. exact BOUND.
Qed.

Lemma pow2_stride_alu64_sound : forall op opcode a immediate n stride,
  arithmetic_opcode op = Some opcode ->
  eval_alu64 opcode (Vlong a) (inr immediate) = Vlong n ->
  ArithmeticHelpers.pow2_stride op (Int.signed immediate) = Some stride ->
  0 < stride /\ Int64.signed n mod stride = 0.
Proof.
  intros op opcode a immediate n stride OPCODE EVAL STRIDE.
  assert (KIND : In op [ArithmeticOp.And; ArithmeticOp.Mul] \/ op = ArithmeticOp.Lsh).
  { destruct op; cbn [ArithmeticHelpers.pow2_stride] in STRIDE; try discriminate; cbn; auto. }
  destruct KIND as [BITS | ->].
  - pose proof (pow2_stride_and_mul_sound op a immediate stride BITS STRIDE) as HOLDS.
    destruct op; cbn in BITS; try solve [exfalso; intuition discriminate];
      inversion OPCODE; subst opcode;
      cbn [eval_alu64 eval_val_int Val.andl Val.mull] in EVAL;
      unfold int64_of_int in EVAL; inversion EVAL; subst n; exact HOLDS.
  - inversion OPCODE; subst opcode.
    destruct (pow2_stride_lsh_sound a immediate stride STRIDE) as [n' [VALUE HOLDS]].
    rewrite EVAL in VALUE. inversion VALUE; subst n'. exact HOLDS.
Qed.

Lemma transfer_alu64_holds :
  forall world memory state dst lhs source op opcode a b,
    In op [ArithmeticOp.And; ArithmeticOp.Or; ArithmeticOp.Xor;
      ArithmeticOp.Lsh; ArithmeticOp.Rsh; ArithmeticOp.Arsh; ArithmeticOp.Mul;
      ArithmeticOp.Div; ArithmeticOp.Mod] ->
    arithmetic_opcode op = Some opcode -> dst <> lhs ->
    (match source with SourceOperand.Value rhs => dst <> rhs | _ => True end) ->
    variable_value world lhs = Vlong a ->
    eval_term world (source_term source) = Vlong b ->
    Forall (atom_holds world memory) state ->
    exists n, eval_alu64 opcode (Vlong a) (inl (Vlong b)) = Vlong n /\
      Forall (atom_holds (assign_value world dst (Vlong n)) memory)
        (transfer_alu64 state dst lhs source op).
Proof.
  intros world memory state dst lhs source op opcode a b OPS OPCODE LEFT_NAME RIGHT_NAME
    AVALUE BVALUE FACTS.
  destruct (eval_alu64_simple_scalar op opcode a b OPS OPCODE) as [n EVAL].
  exists n. split; [exact EVAL |].
  set (updated := assign_value world dst (Vlong n)).
  assert (DEST : variable_value updated dst = Vlong n) by apply variable_value_assign_same.
  assert (LEFT : variable_value updated lhs = Vlong a).
  { unfold updated. rewrite variable_value_assign_other; [exact AVALUE |apply Nat.eqb_neq; congruence]. }
  assert (RIGHT : eval_term updated (source_term source) = Vlong b).
  { unfold updated. rewrite term_value_assign; [exact BVALUE |].
    destruct source; cbn [source_term term_mentions]; [reflexivity |apply Nat.eqb_neq; congruence]. }
  set (base := append_arithmetic_def (apply_havoc state dst) dst op (Var lhs)
    (source_term source)).
  assert (BASE : Forall (atom_holds updated memory) base).
  { unfold base. destruct op; cbn in OPS; try solve [exfalso; intuition discriminate];
      cbn [append_arithmetic_def arithmetic_def_op]; apply Forall_app; split.
    all: try solve [apply apply_havoc_holds; [exact FACTS |constructor]].
    all: constructor; [|constructor]; cbn [atom_holds eval_term]; rewrite DEST, LEFT, RIGHT;
      cbn [definition_holds]; inversion OPCODE; subst opcode; exact (eq_sym EVAL). }
  set (folded := match ArithmeticHelpers.fold_alu_constants base op lhs source with
    | Some value => base ++ [AbstractValue (Var dst) (URangeValue (URange value value))]
    | None => base end).
  assert (FOLDED : Forall (atom_holds updated memory) folded).
  { unfold folded.
    destruct (ArithmeticHelpers.fold_alu_constants base op lhs source) as [value|] eqn:FOLD;
      [|exact BASE].
    destruct (fold_alu64_constants_sound updated memory base lhs source op opcode value
      OPS OPCODE BASE FOLD) as [a' [b' [A [B [VALUE RANGE]]]]].
    rewrite LEFT in A. rewrite RIGHT in B. inversion A; subst a'. inversion B; subst b'.
    rewrite EVAL in VALUE. inversion VALUE; subst n.
    apply Forall_app. split; [exact BASE |]. constructor; [|constructor].
    cbn [atom_holds eval_term]. rewrite DEST. cbn [value_holds u_lower u_upper].
    rewrite Int64.unsigned_repr by exact RANGE. lia. }
  unfold transfer_alu64. fold base folded.
  destruct source as [immediate|rhs]; [|exact FOLDED].
  cbn [source_term eval_term] in BVALUE. inversion BVALUE; subst b.
  change (eval_alu64 opcode (Vlong a) (inr immediate) = Vlong n) in EVAL.
  set (strided := match ArithmeticHelpers.pow2_stride op (Int.signed immediate) with
    | Some stride => folded ++ [AbstractValue (Var dst) (CongruenceValue (Congruence stride 0))]
    | None => folded end).
  assert (STRIDED : Forall (atom_holds updated memory) strided).
  { unfold strided.
    destruct (ArithmeticHelpers.pow2_stride op (Int.signed immediate)) as [stride|] eqn:STRIDE;
      [|exact FOLDED].
    destruct (pow2_stride_alu64_sound op opcode a immediate n stride OPCODE EVAL STRIDE)
      as [POS CONG].
    apply Forall_app. split; [exact FOLDED |]. constructor; [|constructor].
    cbn [atom_holds eval_term]. rewrite DEST. cbn [value_holds modulus residue].
    destruct (stride =? 0) eqn:ZERO; [apply Z.eqb_eq in ZERO; lia |].
    split; [exact POS |]. rewrite Z.mod_0_l by lia. exact CONG. }
  fold strided. destruct op; try exact STRIDED.
  destruct ((1 <=? Int.signed immediate) && (Int.signed immediate <=? 63)) eqn:WIDTH;
    [|exact STRIDED].
  apply andb_true_iff in WIDTH as [LOW HIGH]. apply Z.leb_le in LOW, HIGH.
  inversion OPCODE; subst opcode.
  destruct (rsh64_immediate_bound a immediate ltac:(lia)) as [n' [VALUE RANGE]].
  rewrite EVAL in VALUE. inversion VALUE; subst n'.
  apply Forall_app. split; [exact STRIDED |]. constructor; [|constructor].
  cbn [atom_holds eval_term]. rewrite DEST. exact RANGE.
Qed.

Theorem transfer_alu64_reg_sound :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst src : ireg) dst_value op opcode a b,
    In op [ArithmeticOp.And; ArithmeticOp.Or; ArithmeticOp.Xor;
      ArithmeticOp.Lsh; ArithmeticOp.Rsh; ArithmeticOp.Arsh; ArithmeticOp.Mul;
      ArithmeticOp.Div; ArithmeticOp.Mod] ->
    arithmetic_opcode op = Some opcode ->
    regs dst = Vlong a -> regs src = Vlong b ->
    fresh_destination before dst dst_value ->
    dst_value <> register_name before dst ->
    program_register dst ->
    program_register src ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value (Some dst) (inl src) OpSize.Op64 op = Some after ->
    exists concrete', instruction_step regions program (Palu opcode W64 dst (inl src))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst src dst_value
    op opcode a b OPS OPCODE DST SRC FRESH LEFT_NAME DST_REGISTER SRC_REGISTER CONCRETE TRANSFER.
  pose proof (fresh_destination_operand_name _ _ _ FRESH LEFT_NAME src) as RIGHT_NAME.
  destruct CONCRETE as [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]].
  assert (LEFT : variable_value world (register_name before dst) = Vlong a) by
    (rewrite REGISTERS by assumption; exact DST).
  assert (RIGHT : variable_value world (register_name before src) = Vlong b) by
    (rewrite REGISTERS by assumption; exact SRC).
  destruct (transfer_alu64_holds world memory (facts before) dst_value
    (register_name before dst) (SourceOperand.Value (register_name before src)) op opcode a b
    OPS OPCODE LEFT_NAME RIGHT_NAME LEFT RIGHT FACTS) as [n [EVAL HOLDS]].
  assert (POST : forall lhs rhs,
    transfer_arithmetic (facts before) OpSize.Op64 dst_value (Some lhs) (SourceOperand.Value rhs) op =
      Some (transfer_alu64 (facts before) dst_value lhs (SourceOperand.Value rhs) op)).
  { intros lhs rhs. destruct op; cbn in OPS; try solve [exfalso; intuition discriminate]; reflexivity. }
  unfold transfer_arithmetic_defined in TRANSFER.
  destruct (ensure_defined (facts before) (register_name before dst) &&
    ensure_defined (facts before) (register_name before src)); try discriminate.
  cbn [option_map] in TRANSFER. rewrite POST in TRANSFER. inversion TRANSFER; subst after.
  exists (TLS_State (nextinstr (Pregmap.set dst (Vlong n) regs)) stack code_id count memory). split.
  - unfold instruction_step. cbn [exec_instr]. unfold exec_alu.
    cbn -[ireg_eqb eval_alu64]. rewrite DST, SRC. destruct (ireg_eqb dst src) eqn:SAME.
    + destruct op; cbn in OPS; try solve [exfalso; intuition discriminate];
        inversion OPCODE; subst opcode; try (rewrite EVAL; reflexivity).
      unfold ireg_eqb in SAME. destruct (ireg_eq dst src); try discriminate.
      subst src. rewrite DST in SRC. inversion SRC; subst b.
      cbn [eval_alu64 eval_val_int Val.xorl] in EVAL. rewrite Int64.xor_idem in EVAL.
      inversion EVAL. reflexivity.
    + rewrite EVAL. reflexivity.
  - eapply concretizes_register_update; eauto.
Qed.

Theorem transfer_alu64_imm_scalar_sound :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst : ireg) dst_value immediate op opcode a,
    In op [ArithmeticOp.And; ArithmeticOp.Or; ArithmeticOp.Xor;
      ArithmeticOp.Lsh; ArithmeticOp.Rsh; ArithmeticOp.Arsh; ArithmeticOp.Mul;
      ArithmeticOp.Div; ArithmeticOp.Mod] ->
    arithmetic_opcode op = Some opcode -> regs dst = Vlong a ->
    fresh_destination before dst dst_value ->
    Forall (fun fact => atom_mentions dst_value fact = false) (facts before) ->
    program_register dst ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value (Some dst) (inr immediate) OpSize.Op64 op = Some after ->
    exists concrete', instruction_step regions program (Palu opcode W64 dst (inr immediate))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst dst_value immediate
    op opcode a OPS OPCODE DST FRESH FRESH_FACTS
    DST_REGISTER [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]] TRANSFER.
  unfold transfer_arithmetic_defined in TRANSFER.
  destruct (ensure_defined (facts before) (register_name before dst) && true) eqn:DEFINED;
    try discriminate.
  rewrite andb_true_r in DEFINED.
  pose proof (ensure_defined_fresh_name _ _ _ FRESH_FACTS DEFINED) as DIFFERENT.
  assert (LEFT : variable_value world (register_name before dst) = Vlong a) by
    (rewrite REGISTERS by assumption; exact DST).
  destruct (transfer_alu64_holds world memory (facts before) dst_value
    (register_name before dst) (SourceOperand.Imm immediate) op opcode a
    (Int64.repr (Int.signed immediate)) OPS OPCODE DIFFERENT I LEFT eq_refl FACTS)
    as [n [EVAL HOLDS]].
  change (eval_alu64 opcode (Vlong a) (inr immediate) = Vlong n) in EVAL.
  destruct op; cbn in OPS; try solve [exfalso; intuition discriminate];
    cbn [transfer_arithmetic option_map] in TRANSFER; inversion TRANSFER; subst after.
  all: exists (TLS_State (nextinstr (Pregmap.set dst (Vlong n) regs)) stack code_id count memory); split.
  all: try solve [unfold instruction_step; cbn [exec_instr]; unfold exec_alu;
    cbn -[eval_alu64]; rewrite DST, EVAL; reflexivity].
  all: eapply concretizes_register_update; eauto.
Qed.

Theorem transfer_alu64_imm_sound :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst : ireg) dst_value immediate op opcode a,
    In op [ArithmeticOp.And; ArithmeticOp.Or; ArithmeticOp.Xor; ArithmeticOp.Mul;
    ArithmeticOp.Div; ArithmeticOp.Mod; ArithmeticOp.Arsh] ->
    arithmetic_opcode op = Some opcode -> regs dst = Vlong a ->
    fresh_destination before dst dst_value -> dst_value <> register_name before dst ->
    program_register dst ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value (Some dst) (inr immediate) OpSize.Op64 op = Some after ->
    exists concrete', instruction_step regions program (Palu opcode W64 dst (inr immediate))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst dst_value immediate
    op opcode a OPS OPCODE DST FRESH DIFFERENT DST_REGISTER [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]] TRANSFER.
  destruct (transfer_alu64_holds world memory (facts before) dst_value
    (register_name before dst) (SourceOperand.Imm immediate) op opcode a
    (Int64.repr (Int.signed immediate))
    ltac:(destruct op; cbn in OPS |- *; intuition discriminate)
    OPCODE DIFFERENT I (eq_trans (REGISTERS dst ltac:(assumption)) DST) eq_refl FACTS)
    as [n [EVAL HOLDS]].
  change (eval_alu64 opcode (Vlong a) (inr immediate) = Vlong n) in EVAL.
  unfold transfer_arithmetic_defined in TRANSFER.
  destruct (ensure_defined (facts before) (register_name before dst) && true); try discriminate.
  destruct op; cbn in OPS; try solve [exfalso; intuition discriminate];
    cbn [transfer_arithmetic option_map] in TRANSFER; inversion TRANSFER; subst after.
  all: exists (TLS_State (nextinstr (Pregmap.set dst (Vlong n) regs)) stack code_id count memory); split.
  all: try solve [unfold instruction_step; cbn [exec_instr]; unfold exec_alu;
    cbn -[eval_alu64]; rewrite DST, EVAL; reflexivity].
  all: eapply concretizes_register_update; eauto.
Qed.

Lemma zero_ext_bitfield_insert : forall bound position width original field,
  0 <= position -> 0 < width -> position + width <= bound ->
  Int64.zero_ext bound original = original ->
  Int64.zero_ext bound (Int64.bitfield_insert position width original field) =
    Int64.bitfield_insert position width original field.
Proof.
  intros bound position width original field POSITION WIDTH BOUND ORIGINAL.
  apply Int64.same_bits_eq. intros bit BITS.
  rewrite Int64.bits_zero_ext by lia. destruct (zlt bit bound); [reflexivity |].
  rewrite Int64.bits_bitfield_insert by lia.
  destruct (zlt bit (position + width)); [lia |]. rewrite andb_false_r.
  pose proof (f_equal (fun value => Int64.testbit value bit) ORIGINAL) as ZERO.
  cbn beta in ZERO. rewrite Int64.bits_zero_ext in ZERO by lia.
  rewrite zlt_false in ZERO by lia. exact ZERO.
Qed.

Lemma swapn_zero_ext32 : forall width a,
  width <> S64 -> Int64.zero_ext 32 (swapn width a) = swapn width a.
Proof.
  intros width a NARROW. destruct width; [| |contradiction]; unfold swapn, swab16, swab32.
  all: repeat (apply zero_ext_bitfield_insert; try (change Int64.zwordsize with 64; lia)).
  all: unfold Int64.unsigned_bitfield_extract; apply Int64.zero_ext_widen; lia.
Qed.

Lemma eval_end_scalar : forall direction width a,
  exists result, eval_end direction width (Vlong a) = Vlong result /\
    (width <> S64 -> 0 <= Int64.unsigned result <= Int.max_unsigned).
Proof.
  intros direction width a.
  assert (TRUNCATE : width <> S64 ->
    Int64.zero_ext 32 (eval_end_trunction width a) = eval_end_trunction width a).
  { intros NARROW. destruct width; [| |contradiction]; cbn [eval_end_trunction].
    - apply Int64.zero_ext_widen. lia.
    - apply Int64.zero_ext_idem. lia. }
  unfold eval_end. destruct direction; destruct Archi.big_endian; eexists.
  all: split; [reflexivity |].
  all: intros NARROW;
    match goal with |- 0 <= Int64.unsigned ?result <= Int.max_unsigned =>
      pose proof (Int64.zero_ext_range 32 result ltac:(change (0 <= 32 < 64); lia)) as RANGE end;
    first [rewrite (swapn_zero_ext32 width a NARROW) in RANGE
      |rewrite (TRUNCATE NARROW) in RANGE];
    change (two_p 32) with 4294967296 in RANGE;
    change Int.max_unsigned with 4294967295; lia.
Qed.

Theorem transfer_end_scalar_sound :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst : ireg) dst_value size direction width a,
    (size = OpSize.Op32 -> width <> S64) -> regs dst = Vlong a ->
    fresh_destination before dst dst_value ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value (Some dst)
      (inr (Int.repr (match width with S16 => 16 | S32 => 32 | S64 => 64 end)))
      size ArithmeticOp.End = Some after ->
    exists concrete', instruction_step regions program
      (Palu (END direction width) (match size with OpSize.Op32 => W32 | OpSize.Op64 => W64 end) dst
        (inr (Int.repr (match width with S16 => 16 | S32 => 32 | S64 => 64 end))))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst dst_value size
    direction width a NARROW DST FRESH [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]] TRANSFER.
  unfold transfer_arithmetic_defined in TRANSFER.
  destruct (ensure_defined (facts before) (register_name before dst) && true); try discriminate.
  cbn [transfer_arithmetic option_map] in TRANSFER. inversion TRANSFER; subst after.
  destruct size.
  - destruct (eval_end_scalar direction width (Int64.repr (Int.unsigned (Int.repr (Int64.unsigned a)))))
      as [result [EVAL BOUNDS]].
    assert (RESULT32 : 0 <= Int64.unsigned result <= Int.max_unsigned) by (apply BOUNDS; auto).
    assert (EXEC : eval_alu32 (END direction width) (Vlong a)
      (inr (Int.repr (match width with S16 => 16 | S32 => 32 | S64 => 64 end))) = Vlong result).
    { exact EVAL. }
    exists (TLS_State (nextinstr (Pregmap.set dst (Vlong result) regs)) stack code_id count memory). split.
    + unfold instruction_step. cbn [exec_instr]. unfold exec_alu.
      cbn -[eval_alu32]. rewrite DST, EXEC. reflexivity.
    + eapply concretizes_register_update;
        [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |].
      rewrite <- (Int64.repr_unsigned result), <- (Int.unsigned_repr (Int64.unsigned result) RESULT32).
      apply havoc_word_holds. exact FACTS.
  - destruct (eval_end_scalar direction width a) as [result [EVAL BOUNDS]].
    assert (EXEC : eval_alu64 (END direction width) (Vlong a)
      (inr (Int.repr (match width with S16 => 16 | S32 => 32 | S64 => 64 end))) = Vlong result)
      by exact EVAL.
    exists (TLS_State (nextinstr (Pregmap.set dst (Vlong result) regs)) stack code_id count memory). split.
    + unfold instruction_step. cbn [exec_instr]. unfold exec_alu.
      cbn -[eval_alu64]. rewrite DST, EXEC. reflexivity.
    + eapply concretizes_register_update;
        [exact FRESH |exact REGISTERS |exact POLICY |exact LAYOUT |exact ENVIRONMENT |].
      apply apply_havoc_holds; [exact FACTS |constructor].
Qed.

(** ** Pointer-leak rules *)

Lemma eval_alu_integer_not_pointer : forall op w dst source b o,
  (op = MOV \/ exists a, dst = Vlong a) ->
  (match source with inl v => exists c, v = Vlong c | inr _ => True end) ->
  (forall e s, op <> END e s) -> (forall c, op <> MOVSX c) ->
  (match w with W32 => eval_alu32 | W64 => eval_alu64 end) op dst source <> Vptr b o.
Proof.
  intros op w dst source b o DST SOURCE NOT_END NOT_MOVSX.
  destruct op; try (exfalso; eapply NOT_END; reflexivity);
    try (exfalso; eapply NOT_MOVSX; reflexivity);
    (destruct DST as [DST | [a ->]]; [try discriminate DST |]);
    (destruct source as [v | i]; [destruct SOURCE as [c ->] |]);
    destruct w; cbn; unfold eval_div_u32, eval_div_s32, eval_div_u64, eval_div_s64,
      eval_mod_u32, eval_mod_s32, eval_mod_u64, eval_mod_s64, eval_shift_mask, Val.longofintu;
    cbn;
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    | |- context [if ?x then _ else _] => destruct x eqn:?
    | H : context [if ?x then _ else _] |- _ => destruct x eqn:?
    | H : Some _ = Some _ |- _ => injection H as <-
    end; try discriminate; try congruence.
Qed.

(** An ALU step on integer operands writes no pointer. *)
Lemma alu_step_not_pointer :
  forall regions program opcode w dst source regs stack code_id count memory
         regs' stack' code_id' count' memory',
    instruction_step regions program (Palu opcode w dst source)
      (TLS_State regs stack code_id count memory)
      (TLS_State regs' stack' code_id' count' memory') ->
    (opcode = MOV \/ exists a, regs dst = Vlong a) ->
    (match source with inl src => exists c, regs src = Vlong c | inr _ => True end) ->
    (forall e s, opcode <> END e s) -> (forall c, opcode <> MOVSX c) ->
    forall b o, regs' dst <> Vptr b o.
Proof.
  intros regions program opcode w dst source regs stack code_id count memory
    regs' stack' code_id' count' memory' STEP DST SOURCE NOT_END NOT_MOVSX b o.
  unfold instruction_step in STEP. cbn [exec_instr] in STEP. unfold exec_alu in STEP.
  injection STEP as <- _ _ _ _. rewrite nextinstr_set_value.
  destruct source as [src | immediate].
  - destruct (ireg_eqb dst src);
      [destruct opcode; try discriminate;
       try (exfalso; eapply NOT_END; reflexivity); try (exfalso; eapply NOT_MOVSX; reflexivity)|].
    all: apply eval_alu_integer_not_pointer; assumption.
  - apply eval_alu_integer_not_pointer; assumption.
Qed.

Lemma transfer_arithmetic_initializes : forall state size dst lhs source op post,
  transfer_arithmetic state size dst lhs source op = Some post ->
  In (AbstractValue (Var dst) Unknown) post.
Proof.
  assert (HAVOC : forall state dst, In (AbstractValue (Var dst) Unknown) (apply_havoc state dst)).
  { intros. unfold apply_havoc. apply in_app_iff. right. now left. }
  assert (SIZED : forall state dst size,
    In (AbstractValue (Var dst) Unknown) (apply_havoc_with_size state dst size)).
  { intros. unfold apply_havoc_with_size. destruct size; cbv zeta;
      try solve [apply HAVOC]; apply in_app_iff; left; apply HAVOC. }
  assert (DEF : forall fact state dst op lhs rhs,
    In fact state -> In fact (append_arithmetic_def state dst op lhs rhs)).
  { intros. unfold append_arithmetic_def. destruct (arithmetic_def_op op);
      [apply in_app_iff |]; auto. }
  Ltac find_in HAVOC SIZED DEF := match goal with
    | |- In _ (apply_havoc _ _) => apply HAVOC
    | |- In _ (apply_havoc_with_size _ _ _) => apply SIZED
    | |- In _ (append_arithmetic_def _ _ _ _ _) => apply DEF; find_in HAVOC SIZED DEF
    | |- In _ (_ ++ _) => apply in_or_app;
        (left; find_in HAVOC SIZED DEF) || (right; find_in HAVOC SIZED DEF)
    | |- In _ (_ :: _) => (left; reflexivity) || (right; find_in HAVOC SIZED DEF)
    end.
  intros state size dst lhs source op post TRANSFER.
  unfold transfer_arithmetic, transfer_alu64, transfer_add_sub, apply_assignment,
    ArithmeticHelpers.apply_assignment_var_offset in TRANSFER.
  repeat match type of TRANSFER with
  | context [match ?x with _ => _ end] => destruct x
  | context [if ?x then _ else _] => destruct x
  end; try discriminate; injection TRANSFER as <-; find_in HAVOC SIZED DEF.
Qed.

(** The leak wrapper keeps the soundness of the operand-checked transfer:
    [mark_scalar] only describes a result computed from integers. *)
Lemma arithmetic_leaks_sound :
  forall (attrs : load_attrs) regions program before after instruction concrete
         dst dst_value lhs source size op,
    program_register dst ->
    transfer_arithmetic_local before dst dst_value lhs source size op = Some after ->
    (forall core,
      transfer_arithmetic_defined before dst dst_value lhs source size op = Some core ->
      exists regs' stack' code_id' count' memory',
        instruction_step regions program instruction concrete
          (TLS_State regs' stack' code_id' count' memory') /\
        concretizes attrs regions core (TLS_State regs' stack' code_id' count' memory') /\
        (operands_disclosable (facts before) (option_map (register_name before) lhs)
          (match source with inl reg => SourceOperand.Value (register_name before reg)
                           | inr immediate => SourceOperand.Imm immediate end) = true ->
         forall b o, regs' dst <> Vptr b o)) ->
    exists concrete', instruction_step regions program instruction concrete concrete' /\
      concretizes attrs regions after concrete'.
Proof.
  intros attrs regions program before after instruction concrete dst dst_value lhs source size
    op DST TRANSFER CORE_SOUND.
  unfold transfer_arithmetic_local in TRANSFER. cbv zeta in TRANSFER.
  destruct (check_pointer_arithmetic _ _ _ _); [| discriminate].
  destruct (transfer_arithmetic_defined before dst dst_value lhs source size op)
    as [core |] eqn:CORE; [| discriminate].
  cbn [option_map] in TRANSFER. injection TRANSFER as AFTER.
  destruct (CORE_SOUND core eq_refl)
    as [regs' [stack' [code_id' [count' [memory' [STEP [CONCRETE INTEGER]]]]]]].
  exists (TLS_State regs' stack' code_id' count' memory'). split; [exact STEP |].
  destruct (operands_disclosable _ _ _) eqn:SCALAR; subst after; [| exact CONCRETE].
  unfold transfer_arithmetic_defined in CORE.
  destruct (_ && _); [| discriminate].
  destruct (transfer_arithmetic _ _ _ _ _ _) as [post |] eqn:POST; [| discriminate].
  injection CORE as <-. cbn [facts register_name].
  eapply concretizes_mark_scalar; [exact CONCRETE | | exact DST | | exact (INTEGER eq_refl)].
  - unfold set_register_name. destruct (ireg_eq dst dst); [reflexivity | contradiction].
  - eapply has_initialized_value_present; [eapply transfer_arithmetic_initializes; exact POST |].
    discriminate.
Qed.

Lemma operands_disclosable_registers :
  forall attrs regions before regs stack code_id count memory lhs source,
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    (match lhs with Some reg => program_register reg | None => True end) ->
    program_operand source ->
    operands_disclosable (facts before) (option_map (register_name before) lhs)
      (match source with inl reg => SourceOperand.Value (register_name before reg)
                       | inr immediate => SourceOperand.Imm immediate end) = true ->
    (match lhs with Some reg => exists a, regs reg = Vlong a | None => True end) /\
    (match source with inl src => exists c, regs src = Vlong c | inr _ => True end).
Proof.
  intros attrs regions before regs stack code_id count memory lhs source
    [world [REGISTERS [FACTS _]]] LHS SOURCE SCALAR.
  unfold operands_disclosable in SCALAR. apply andb_true_iff in SCALAR as [LEFT RIGHT].
  split.
  - destruct lhs as [reg |]; [| exact I]. cbn [option_map] in LEFT.
    destruct (disclosable_sound _ _ _ _ FACTS LEFT) as [a VALUE].
    rewrite (REGISTERS reg LHS) in VALUE. eauto.
  - destruct source as [src | immediate]; [| exact I].
    destruct (disclosable_sound _ _ _ _ FACTS RIGHT) as [c VALUE].
    rewrite (REGISTERS src SOURCE) in VALUE. eauto.
Qed.

(** =========== General ALU soundness =========== *)

(** General soundness of the ALU transfer: every [transfer_arithmetic] arm
    dispatched onto its per-arm theorem. Beyond the draft premises it takes SSA
    freshness ([dst_value] distinct from [dst]'s old name and absent from the
    pre-state facts), the [eq_constants_fit_i64] representation premise, operand
    register well-formedness, and the CompCert premise [alu_integer_operands].
    [End] is excluded by [arithmetic_opcode]. *)
Theorem transfer_arithmetic_defined_sound :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count
         memory dst dst_value lhs source size op opcode,
    fresh_destination before dst dst_value ->
    dst_value <> register_name before dst ->
    Forall (fun fact => atom_mentions dst_value fact = false) (facts before) ->
    ArithmeticHelpers.eq_constants_fit_i64 (facts before) ->
    program_register dst ->
    program_operand source ->
    alu_integer_operands before regs size dst source op ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_defined before dst dst_value lhs source size op = Some after ->
    arithmetic_opcode op = Some opcode ->
    arithmetic_in_place op lhs dst ->
    exists concrete',
      instruction_step regions program
        (Palu opcode (lower_width size) dst source)
        (TLS_State regs stack code_id count memory) concrete' /\
      concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst dst_value lhs
    source size op opcode FRESH NEWNAME FRESHFACTS FITEQ PROGDST PROGSRC WF CONCRETE TRANSFER
    OPCODE INPLACE.
  unfold alu_integer_operands in WF. unfold lower_width.
  destruct op; cbn [arithmetic_opcode] in OPCODE; try discriminate OPCODE; injection OPCODE as <-.
  (* Add *)
  - destruct INPLACE as [[E _] | ->]; [discriminate E |].
    destruct source as [src | immediate]; cbn [program_operand] in PROGSRC;
      destruct size; cbn beta iota zeta in WF.
    + destruct WF as [[a DA] [b DB]].
      eapply transfer_add_sub32_reg_sound with (op := ArithmeticOp.Add);
        [left; reflexivity | exact DA | exact DB | exact FRESH | exact NEWNAME | exact PROGDST | exact PROGSRC | exact CONCRETE | exact TRANSFER].
    + eapply transfer_add64_reg_sound;
        [exact WF | exact FRESH | exact PROGDST | exact PROGSRC | exact CONCRETE | exact TRANSFER].
    + destruct WF as [[a DA] _].
      destruct (ArithmeticHelpers.op32_shift_exact (facts before) (register_name before dst)
        (Int.signed immediate)) eqn:EXACT.
      * eapply transfer_add_sub_imm_assignment_sound with (op := ArithmeticOp.Add) (size := OpSize.Op32);
          [left; reflexivity | intros _; exact EXACT | exact DA | exact FRESH | exact FRESHFACTS
           | exact FITEQ | exact PROGDST | exact CONCRETE | exact TRANSFER].
      * eapply transfer_add_sub32_imm_sound_if_wrapping with (op := ArithmeticOp.Add);
          [left; reflexivity | exact EXACT | exact DA | exact FRESH | exact NEWNAME | exact PROGDST
           | exact CONCRETE | exact TRANSFER].
    + eapply transfer_add_sub64_imm_sound with (op := ArithmeticOp.Add);
        [left; reflexivity | exact FRESH | exact FRESHFACTS | exact FITEQ
         | exact PROGDST | exact CONCRETE | exact TRANSFER].
  (* Sub *)
  - destruct INPLACE as [[E _] | ->]; [discriminate E |].
    destruct source as [src | immediate]; cbn [program_operand] in PROGSRC;
      destruct size; cbn beta iota zeta in WF.
    + destruct WF as [[a DA] [b DB]].
      eapply transfer_add_sub32_reg_sound with (op := ArithmeticOp.Sub);
        [right; reflexivity | exact DA | exact DB | exact FRESH | exact NEWNAME | exact PROGDST | exact PROGSRC | exact CONCRETE | exact TRANSFER].
    + eapply transfer_sub64_reg_sound_if_defined;
        [exact WF | exact FRESH | exact NEWNAME | exact PROGDST | exact PROGSRC | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] _].
      destruct (ArithmeticHelpers.op32_shift_exact (facts before) (register_name before dst)
        (- Int.signed immediate)) eqn:EXACT.
      * eapply transfer_add_sub_imm_assignment_sound with (op := ArithmeticOp.Sub) (size := OpSize.Op32);
          [right; reflexivity | intros _; exact EXACT | exact DA | exact FRESH | exact FRESHFACTS
           | exact FITEQ | exact PROGDST | exact CONCRETE | exact TRANSFER].
      * eapply transfer_add_sub32_imm_sound_if_wrapping with (op := ArithmeticOp.Sub);
          [right; reflexivity | exact EXACT | exact DA | exact FRESH | exact NEWNAME | exact PROGDST
           | exact CONCRETE | exact TRANSFER].
    + eapply transfer_add_sub64_imm_sound with (op := ArithmeticOp.Sub);
        [right; reflexivity | exact FRESH | exact FRESHFACTS | exact FITEQ
         | exact PROGDST | exact CONCRETE | exact TRANSFER].
  (* Mul *)
  - destruct INPLACE as [[E _] | ->]; [discriminate E |].
    destruct source as [src | immediate]; cbn [program_operand] in PROGSRC;
      destruct size; cbn beta iota zeta in WF.
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Mul);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] [b DB]].
      eapply transfer_alu64_reg_sound with (op := ArithmeticOp.Mul);
        [cbn; tauto | reflexivity | exact DA | exact DB | exact FRESH | exact NEWNAME | exact PROGDST | exact PROGSRC | exact CONCRETE | exact TRANSFER].
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Mul);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] _].
      eapply transfer_alu64_imm_sound with (op := ArithmeticOp.Mul);
        [cbn; tauto | reflexivity | exact DA | exact FRESH | exact NEWNAME | exact PROGDST
         | exact CONCRETE | exact TRANSFER].
  (* Div *)
  - destruct INPLACE as [[E _] | ->]; [discriminate E |].
    destruct source as [src | immediate]; cbn [program_operand] in PROGSRC;
      destruct size; cbn beta iota zeta in WF.
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Div);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] [b DB]].
      eapply transfer_alu64_reg_sound with (op := ArithmeticOp.Div);
        [cbn; tauto | reflexivity | exact DA | exact DB | exact FRESH | exact NEWNAME | exact PROGDST | exact PROGSRC | exact CONCRETE | exact TRANSFER].
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Div);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] _].
      eapply transfer_alu64_imm_sound with (op := ArithmeticOp.Div);
        [cbn; tauto | reflexivity | exact DA | exact FRESH | exact NEWNAME | exact PROGDST
         | exact CONCRETE | exact TRANSFER].
  (* Or *)
  - destruct INPLACE as [[E _] | ->]; [discriminate E |].
    destruct source as [src | immediate]; cbn [program_operand] in PROGSRC;
      destruct size; cbn beta iota zeta in WF.
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Or);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] [b DB]].
      eapply transfer_alu64_reg_sound with (op := ArithmeticOp.Or);
        [cbn; tauto | reflexivity | exact DA | exact DB | exact FRESH | exact NEWNAME | exact PROGDST | exact PROGSRC | exact CONCRETE | exact TRANSFER].
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Or);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] _].
      eapply transfer_alu64_imm_sound with (op := ArithmeticOp.Or);
        [cbn; tauto | reflexivity | exact DA | exact FRESH | exact NEWNAME | exact PROGDST
         | exact CONCRETE | exact TRANSFER].
  (* And *)
  - destruct INPLACE as [[E _] | ->]; [discriminate E |].
    destruct source as [src | immediate]; cbn [program_operand] in PROGSRC;
      destruct size; cbn beta iota zeta in WF.
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_and32_sound;
        [exact DA | exact SCALAR | exact FRESH | exact PROGDST | exact PROGSRC | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] [b DB]].
      eapply transfer_alu64_reg_sound with (op := ArithmeticOp.And);
        [cbn; tauto | reflexivity | exact DA | exact DB | exact FRESH | exact NEWNAME | exact PROGDST | exact PROGSRC | exact CONCRETE | exact TRANSFER].
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_and32_sound;
        [exact DA | exact SCALAR | exact FRESH | exact PROGDST | exact PROGSRC | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] _].
      eapply transfer_alu64_imm_sound with (op := ArithmeticOp.And);
        [cbn; tauto | reflexivity | exact DA | exact FRESH | exact NEWNAME | exact PROGDST
         | exact CONCRETE | exact TRANSFER].
  (* Lsh *)
  - destruct INPLACE as [[E _] | ->]; [discriminate E |].
    destruct source as [src | immediate]; cbn [program_operand] in PROGSRC;
      destruct size; cbn beta iota zeta in WF.
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Lsh);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] [b DB]].
      eapply transfer_alu64_reg_sound with (op := ArithmeticOp.Lsh);
        [cbn; tauto | reflexivity | exact DA | exact DB | exact FRESH | exact NEWNAME | exact PROGDST | exact PROGSRC | exact CONCRETE | exact TRANSFER].
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Lsh);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [a DA].
      eapply transfer_alu64_imm_scalar_sound with (op := ArithmeticOp.Lsh);
        [cbn; tauto | reflexivity | exact DA | exact FRESH | exact FRESHFACTS | exact PROGDST
         | exact CONCRETE | exact TRANSFER].
  (* Rsh *)
  - destruct INPLACE as [[E _] | ->]; [discriminate E |].
    destruct source as [src | immediate]; cbn [program_operand] in PROGSRC;
      destruct size; cbn beta iota zeta in WF.
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Rsh);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] [b DB]].
      eapply transfer_alu64_reg_sound with (op := ArithmeticOp.Rsh);
        [cbn; tauto | reflexivity | exact DA | exact DB | exact FRESH | exact NEWNAME | exact PROGDST | exact PROGSRC | exact CONCRETE | exact TRANSFER].
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Rsh);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [a DA].
      eapply transfer_alu64_imm_scalar_sound with (op := ArithmeticOp.Rsh);
        [cbn; tauto | reflexivity | exact DA | exact FRESH | exact FRESHFACTS | exact PROGDST
         | exact CONCRETE | exact TRANSFER].
  (* Neg *)
  - destruct INPLACE as [[E _] | ->]; [discriminate E |].
    destruct source as [src | immediate]; cbn [program_operand] in PROGSRC;
      destruct size; cbn beta iota zeta in WF.
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Neg);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [a DA].
      eapply transfer_neg64_sound; [exact DA | exact FRESH | exact CONCRETE | exact TRANSFER].
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Neg);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [a DA].
      eapply transfer_neg64_sound; [exact DA | exact FRESH | exact CONCRETE | exact TRANSFER].
  (* Mod *)
  - destruct INPLACE as [[E _] | ->]; [discriminate E |].
    destruct source as [src | immediate]; cbn [program_operand] in PROGSRC;
      destruct size; cbn beta iota zeta in WF.
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Mod);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] [b DB]].
      eapply transfer_alu64_reg_sound with (op := ArithmeticOp.Mod);
        [cbn; tauto | reflexivity | exact DA | exact DB | exact FRESH | exact NEWNAME | exact PROGDST | exact PROGSRC | exact CONCRETE | exact TRANSFER].
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Mod);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] _].
      eapply transfer_alu64_imm_sound with (op := ArithmeticOp.Mod);
        [cbn; tauto | reflexivity | exact DA | exact FRESH | exact NEWNAME | exact PROGDST
         | exact CONCRETE | exact TRANSFER].
  (* Xor *)
  - destruct INPLACE as [[E _] | ->]; [discriminate E |].
    destruct source as [src | immediate]; cbn [program_operand] in PROGSRC;
      destruct size; cbn beta iota zeta in WF.
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Xor);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] [b DB]].
      eapply transfer_alu64_reg_sound with (op := ArithmeticOp.Xor);
        [cbn; tauto | reflexivity | exact DA | exact DB | exact FRESH | exact NEWNAME | exact PROGDST | exact PROGSRC | exact CONCRETE | exact TRANSFER].
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Xor);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] _].
      eapply transfer_alu64_imm_sound with (op := ArithmeticOp.Xor);
        [cbn; tauto | reflexivity | exact DA | exact FRESH | exact NEWNAME | exact PROGDST
         | exact CONCRETE | exact TRANSFER].
  (* Mov *)
  - destruct INPLACE as [[_ ->] | ->].
    2: { unfold transfer_arithmetic_defined in TRANSFER.
         destruct (_ && _) in TRANSFER; cbn [transfer_arithmetic] in TRANSFER; discriminate TRANSFER. }
    destruct source as [src | immediate]; cbn [program_operand] in PROGSRC;
      [destruct size |]; cbn beta iota zeta in WF.
    + destruct (ArithmeticHelpers.fits_u32 (facts before) (register_name before src)) eqn:FITS.
      * eapply transfer_mov32_reg_sound_if_copied;
          [exact FITS | exact FRESH | exact FRESHFACTS | exact FITEQ
           | exact PROGSRC | exact CONCRETE | exact TRANSFER].
      * destruct (WF eq_refl) as [a DA].
        eapply transfer_mov32_reg_sound_if_truncated;
          [exact FITS | exact DA | exact FRESH | exact CONCRETE | exact TRANSFER].
    + eapply transfer_mov64_reg_sound;
        [exact FRESH | exact FRESHFACTS | exact FITEQ | exact PROGSRC
         | exact CONCRETE | exact TRANSFER].
    + eapply transfer_mov_imm_sound; [exact FRESH | exact CONCRETE | exact TRANSFER].
  (* Arsh *)
  - destruct INPLACE as [[E _] | ->]; [discriminate E |].
    destruct source as [src | immediate]; cbn [program_operand] in PROGSRC;
      destruct size; cbn beta iota zeta in WF.
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Arsh);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] [b DB]].
      eapply transfer_alu64_reg_sound with (op := ArithmeticOp.Arsh);
        [cbn; tauto | reflexivity | exact DA | exact DB | exact FRESH | exact NEWNAME | exact PROGDST | exact PROGSRC | exact CONCRETE | exact TRANSFER].
    + destruct WF as [[a DA] SCALAR].
      eapply transfer_alu32_havoc_sound with (op := ArithmeticOp.Arsh);
        [cbn; tauto | reflexivity | exact DA | exact SCALAR | exact FRESH | exact CONCRETE
         | exact TRANSFER].
    + destruct WF as [[a DA] _].
      eapply transfer_alu64_imm_sound with (op := ArithmeticOp.Arsh);
        [cbn; tauto | reflexivity | exact DA | exact FRESH | exact NEWNAME | exact PROGDST
         | exact CONCRETE | exact TRANSFER].
Qed.

(** General soundness of the ALU transfer, including Rust's pointer-leak
    wrapper: the [transfer_arithmetic_defined_sound] premises suffice. *)
Theorem transfer_arithmetic_sound :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count
         memory dst dst_value lhs source size op opcode,
    fresh_destination before dst dst_value ->
    dst_value <> register_name before dst ->
    Forall (fun fact => atom_mentions dst_value fact = false) (facts before) ->
    ArithmeticHelpers.eq_constants_fit_i64 (facts before) ->
    program_register dst ->
    program_operand source ->
    alu_integer_operands before regs size dst source op ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_local before dst dst_value lhs source size op = Some after ->
    arithmetic_opcode op = Some opcode ->
    arithmetic_in_place op lhs dst ->
    exists concrete',
      instruction_step regions program
        (Palu opcode (lower_width size) dst source)
        (TLS_State regs stack code_id count memory) concrete' /\
      concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst dst_value lhs
    source size op opcode FRESH NEWNAME FRESHFACTS FITEQ PROGDST PROGSRC WF CONCRETE TRANSFER
    OPCODE INPLACE.
  eapply arithmetic_leaks_sound; [exact PROGDST | exact TRANSFER |].
  intros core CORE.
  destruct (transfer_arithmetic_defined_sound attrs program regions before core regs stack code_id
    count memory dst dst_value lhs source size op opcode FRESH NEWNAME FRESHFACTS FITEQ PROGDST
    PROGSRC WF CONCRETE CORE OPCODE INPLACE)
    as [[regs' stack' code_id' count' memory'] [STEP POST]].
  exists regs', stack', code_id', count', memory'. split; [exact STEP |]. split; [exact POST |].
  intros SCALAR.
  destruct (operands_disclosable_registers attrs regions before regs stack code_id count memory
    lhs source CONCRETE ltac:(destruct INPLACE as [[_ ->] | ->]; [exact I | exact PROGDST])
    PROGSRC SCALAR) as [LEFT RIGHT].
  eapply alu_step_not_pointer; [exact STEP | | exact RIGHT | |].
  - destruct INPLACE as [[MOV ->] | ->]; [subst op; injection OPCODE as <-; now left | now right].
  - intros e s ->. destruct op; discriminate OPCODE.
  - intros c ->. destruct op; discriminate OPCODE.
Qed.

(** The [End] arm through Rust's pointer-leak wrapper: a byte swap of an
    integer is an integer. *)
Theorem transfer_end_sound :
  forall (attrs : load_attrs) program regions before after (regs : regset) stack code_id count memory
    (dst : ireg) dst_value size direction width a,
    (size = OpSize.Op32 -> width <> S64) -> regs dst = Vlong a ->
    fresh_destination before dst dst_value ->
    program_register dst ->
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    transfer_arithmetic_local before dst dst_value (Some dst)
      (inr (Int.repr (match width with S16 => 16 | S32 => 32 | S64 => 64 end)))
      size ArithmeticOp.End = Some after ->
    exists concrete', instruction_step regions program
      (Palu (END direction width) (match size with OpSize.Op32 => W32 | OpSize.Op64 => W64 end) dst
        (inr (Int.repr (match width with S16 => 16 | S32 => 32 | S64 => 64 end))))
      (TLS_State regs stack code_id count memory) concrete' /\ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after regs stack code_id count memory dst dst_value size
    direction width a NARROW DST FRESH PROGDST CONCRETE TRANSFER.
  eapply arithmetic_leaks_sound; [exact PROGDST | exact TRANSFER |].
  intros core CORE.
  destruct (transfer_end_scalar_sound attrs program regions before core regs stack code_id count
    memory dst dst_value size direction width a NARROW DST FRESH CONCRETE CORE)
    as [[regs' stack' code_id' count' memory'] [STEP POST]].
  exists regs', stack', code_id', count', memory'. split; [exact STEP |]. split; [exact POST |].
  intros _ b o. unfold instruction_step in STEP. cbn [exec_instr] in STEP. unfold exec_alu in STEP.
  destruct size; cbn -[eval_alu32 eval_alu64] in STEP; rewrite DST in STEP;
    injection STEP as <- _ _ _ _; rewrite nextinstr_set_value; discriminate.
Qed.

End Arithmetic.
