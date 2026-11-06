From Coq Require Import Bool List ZArith Lia.
From compcert Require Import Coqlib Integers Values Memory Ctypes.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.
From TrustNoBPF.Semantics Require Import AbstractDomain Concretization Transfer CompCertAssms
  IRLevelAssms Common ArithmeticHelpers.

Import ListNotations.
Open Scope Z_scope.

(** eBPF terminators only: the arm64 lifter's [Terminator::BranchFlags] has no
    counterpart here. *)

(** =========== Transfer definitions =========== *)

(** The comparison an edge carries: Rust's [(Condition, OpSize, bool)]. *)
Definition branch := (condition * OpSize.t * bool)%type.

Definition cmp_op_eq_dec : forall x y : CmpOp.t, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition cmp_is_signed (op : CmpOp.t) : bool :=
  match op with
  | CmpOp.SignedGt | CmpOp.SignedGe | CmpOp.SignedLt | CmpOp.SignedLe => true
  | _ => false
  end.

(** [CmpOp::negated]. *)
Definition cmp_negated (op : CmpOp.t) : option CmpOp.t :=
  match op with
  | CmpOp.Eq => Some CmpOp.Ne
  | CmpOp.Ne => Some CmpOp.Eq
  | CmpOp.UnsignedGt => Some CmpOp.UnsignedLe
  | CmpOp.UnsignedLe => Some CmpOp.UnsignedGt
  | CmpOp.UnsignedGe => Some CmpOp.UnsignedLt
  | CmpOp.UnsignedLt => Some CmpOp.UnsignedGe
  | CmpOp.SignedGt => Some CmpOp.SignedLe
  | CmpOp.SignedLe => Some CmpOp.SignedGt
  | CmpOp.SignedGe => Some CmpOp.SignedLt
  | CmpOp.SignedLt => Some CmpOp.SignedGe
  | CmpOp.BitSet => None
  end.

(** [CmpOp::eval] on [u64] operands. Reducing modulo [2^64] first is the
    identity on Rust-sized inputs. *)
Definition cmp_eval (op : CmpOp.t) (size : OpSize.t) (lhs rhs : Z) : bool :=
  let '(ul, ur, sl, sr) :=
    match size with
    | OpSize.Op32 => (Int.unsigned (Int.repr lhs), Int.unsigned (Int.repr rhs),
                      Int.signed (Int.repr lhs), Int.signed (Int.repr rhs))
    | OpSize.Op64 => (Int64.unsigned (Int64.repr lhs), Int64.unsigned (Int64.repr rhs),
                      Int64.signed (Int64.repr lhs), Int64.signed (Int64.repr rhs))
    end in
  match op with
  | CmpOp.Eq => ul =? ur
  | CmpOp.Ne => negb (ul =? ur)
  | CmpOp.UnsignedGt => ur <? ul
  | CmpOp.UnsignedGe => ur <=? ul
  | CmpOp.UnsignedLt => ul <? ur
  | CmpOp.UnsignedLe => ul <=? ur
  | CmpOp.SignedGt => sr <? sl
  | CmpOp.SignedGe => sr <=? sl
  | CmpOp.SignedLt => sl <? sr
  | CmpOp.SignedLe => sl <=? sr
  | CmpOp.BitSet => negb (Z.land ul ur =? 0)
  end.

(** [CmpOp::jmp_imm_const]. *)
Definition jmp_imm_const (op : CmpOp.t) (size : OpSize.t) (imm : int) : Z :=
  match size with
  | OpSize.Op32 => if cmp_is_signed op then Int.signed imm else Int.unsigned imm
  | OpSize.Op64 => Int.signed imm
  end.

Inductive widening_domain := WidenUnsigned | WidenSigned.

(** [CmpOp::jmp32_widening_domain]. *)
Definition jmp32_widening_domain (op : CmpOp.t) (taken : bool) : option widening_domain :=
  match op, taken with
  | CmpOp.Ne, true | CmpOp.Eq, false | CmpOp.BitSet, _ => None
  | CmpOp.Eq, true | CmpOp.Ne, false
  | CmpOp.UnsignedGt, _ | CmpOp.UnsignedGe, _
  | CmpOp.UnsignedLt, _ | CmpOp.UnsignedLe, _ => Some WidenUnsigned
  | CmpOp.SignedGt, _ | CmpOp.SignedGe, _
  | CmpOp.SignedLt, _ | CmpOp.SignedLe, _ => Some WidenSigned
  end.

(** [check.rs::operand_confined_to]. *)
Definition operand_confined_to (state : abstract_state) (expression : term)
    (domain : widening_domain) : bool :=
  match domain with
  | WidenUnsigned =>
      match ArithmeticHelpers.term_bounds state expression false with
      | Some (_, hi) => hi <=? Int.max_unsigned
      | None => false
      end
  | WidenSigned =>
      match ArithmeticHelpers.term_bounds state expression true with
      | Some (lo, hi) => (Int.min_signed <=? lo) && (hi <=? Int.max_signed)
      | None => false
      end
  end.

(** [check.rs::branch_provably_not_taken]. Its local [pinned] is
    [ArithmeticHelpers.pinned]; an immediate is read as [i64::from(imm) as u64]. *)
Definition branch_provably_not_taken (state : abstract_state) (cond : condition)
    (size : OpSize.t) (taken : bool) : bool :=
  match ArithmeticHelpers.pinned state (Var (cond_dst cond)) with
  | None => false
  | Some lhs =>
      let rhs := match cond_src cond with
        | SourceOperand.Imm imm => Some (ArithmeticHelpers.unsigned64 (Int.signed imm))
        | SourceOperand.Value name => ArithmeticHelpers.pinned state (Var name)
        end in
      match rhs with
      | Some rhs => negb (Bool.eqb (cmp_eval (cond_op cond) size lhs rhs) taken)
      | None => false
      end
  end.

Definition branch_rhs_term (cond : condition) (size : OpSize.t) : term :=
  match cond_src cond with
  | SourceOperand.Imm imm => Const (jmp_imm_const (cond_op cond) size imm)
  | SourceOperand.Value name => Var name
  end.

(** The atom [check.rs::inject_branch_atom] pushes for an injected comparison. *)
Definition comparison_atoms (dst rhs : term) (op : CmpOp.t) (taken imm_zero : bool) : list atom :=
  match op, taken with
  | CmpOp.Eq, true | CmpOp.Ne, false => [Eq dst rhs]
  | CmpOp.Ne, true | CmpOp.Eq, false => if imm_zero then [NeqZero dst] else [Neq dst rhs]
  | CmpOp.UnsignedLt, true => [Lt dst rhs false]
  | CmpOp.UnsignedLt, false => [Le rhs dst false]
  | CmpOp.UnsignedLe, true => [Le dst rhs false]
  | CmpOp.UnsignedLe, false => [Lt rhs dst false]
  | CmpOp.UnsignedGt, true => [Lt rhs dst false]
  | CmpOp.UnsignedGt, false => [Le dst rhs false]
  | CmpOp.UnsignedGe, true => [Le rhs dst false]
  | CmpOp.UnsignedGe, false => [Lt dst rhs false]
  | CmpOp.SignedLt, true => [Lt dst rhs true]
  | CmpOp.SignedLt, false => [Le rhs dst true]
  | CmpOp.SignedLe, true => [Le dst rhs true]
  | CmpOp.SignedLe, false => [Lt rhs dst true]
  | CmpOp.SignedGt, true => [Lt rhs dst true]
  | CmpOp.SignedGt, false => [Le dst rhs true]
  | CmpOp.SignedGe, true => [Le rhs dst true]
  | CmpOp.SignedGe, false => [Lt dst rhs true]
  | CmpOp.BitSet, _ => []
  end.

(** The [jmp32] widening gate of [check.rs::inject_branch_atom]. *)
Definition branch_suppressed (state : abstract_state) (cond : condition)
    (size : OpSize.t) (taken : bool) : bool :=
  match size, jmp32_widening_domain (cond_op cond) taken with
  | OpSize.Op32, Some domain =>
      negb (operand_confined_to state (Var (cond_dst cond)) domain &&
            operand_confined_to state (branch_rhs_term cond size) domain)
  | _, _ => false
  end.

(** [check.rs::inject_branch_atom]: the atoms an edge adds for its outcome. *)
Definition branch_atoms (state : abstract_state) (cond : condition)
    (size : OpSize.t) (taken : bool) : list atom :=
  let imm_zero := match cond_src cond with
    | SourceOperand.Imm imm => Int.eq imm Int.zero
    | SourceOperand.Value _ => false
    end in
  if branch_suppressed state cond size taken then []
  else comparison_atoms (Var (cond_dst cond)) (branch_rhs_term cond size) (cond_op cond) taken imm_zero.

(** [facts.rs::ScalarFact]. *)
Inductive scalar_fact :=
  | EqConst (constant : Z)
  | NeqConst (constant : Z)
  | UnsignedFact (bounds : urange)
  | SignedFact (bounds : range).

(** [facts.rs::scalar_fact]. *)
Definition scalar_fact_of (fact : atom) : option (term * scalar_fact) :=
  match fact with
  | Eq expression (Const constant) | Eq (Const constant) expression =>
      Some (expression, EqConst constant)
  | Neq expression (Const constant) | Neq (Const constant) expression =>
      Some (expression, NeqConst constant)
  | NeqZero expression => Some (expression, NeqConst 0)
  | AbstractValue expression (URangeValue bounds) => Some (expression, UnsignedFact bounds)
  | AbstractValue expression (RangeValue bounds) => Some (expression, SignedFact bounds)
  | _ => None
  end.

(** The running summary of [contradiction.rs::facts_conflict]: the pinned
    constant and the intersections of the unsigned and of the signed ranges. *)
Record fact_summary := FactSummary {
  summary_pinned : option Z;
  summary_unsigned : option urange;
  summary_signed : option range }.

(** One iteration of the loop of [contradiction.rs::facts_conflict]; [None]
    is its early [return true]. *)
Definition summarize_fact (summary : fact_summary) (fact : scalar_fact) : option fact_summary :=
  let '(FactSummary pinned unsigned signed) := summary in
  match fact with
  | EqConst c =>
      match pinned with
      | Some p => if p =? c then Some (FactSummary (Some c) unsigned signed) else None
      | None => Some (FactSummary (Some c) unsigned signed)
      end
  | UnsignedFact r =>
      let r := match unsigned with
        | Some u => URange (Z.max (u_lower u) (u_lower r)) (Z.min (u_upper u) (u_upper r))
        | None => r
        end in
      if u_upper r <? u_lower r then None else Some (FactSummary pinned (Some r) signed)
  | SignedFact r =>
      let r := match signed with
        | Some s => Range (Z.max (lower s) (lower r)) (Z.min (upper s) (upper r))
        | None => r
        end in
      if upper r <? lower r then None else Some (FactSummary pinned unsigned (Some r))
  | NeqConst _ => Some summary
  end.

Fixpoint summarize_facts (summary : fact_summary) (facts : list scalar_fact) : option fact_summary :=
  match facts with
  | [] => Some summary
  | fact :: rest =>
      match summarize_fact summary fact with
      | Some summary => summarize_facts summary rest
      | None => None
      end
  end.

(** [contradiction.rs::facts_conflict]; [c as u64] is [unsigned64 c]. *)
Definition facts_conflict (facts : list scalar_fact) : bool :=
  let u64 := ArithmeticHelpers.unsigned64 in
  match summarize_facts (FactSummary None None None) facts with
  | None => true
  | Some (FactSummary pinned unsigned signed) =>
      match pinned with
      | Some c =>
          match unsigned with
          | Some r => (u64 c <? u_lower r) || (u_upper r <? u64 c)
          | None => false
          end ||
          match signed with
          | Some r => (c <? lower r) || (upper r <? c)
          | None => false
          end
      | None => false
      end ||
      existsb (fun fact =>
        match fact with
        | NeqConst c =>
            match pinned with Some p => p =? c | None => false end ||
            match unsigned with
            | Some r => (u_lower r =? u_upper r) && (u_lower r =? u64 c)
            | None => false
            end ||
            match signed with
            | Some r => (lower r =? upper r) && (lower r =? c)
            | None => false
            end
        | _ => false
        end) facts
  end.

(** The scalar facts of [state] about [expression]: one run of the facts
    [contradiction.rs::is_contradictory] sorts by term. *)
Definition scalar_facts_about (state : abstract_state) (expression : term) : list scalar_fact :=
  flat_map (fun fact =>
    match scalar_fact_of fact with
    | Some (other, scalar) => if term_beq expression other then [scalar] else []
    | None => []
    end) state.

(** The same-term scan of [contradiction.rs::is_contradictory]. Rust sorts the
    scalar facts by term (unstably) and summarizes each run; [facts_conflict]
    does not depend on the order inside a run, so Rocq summarizes the facts
    about each term in state order. *)
Definition scalar_contradiction (state : abstract_state) : bool :=
  existsb (fun fact =>
    match scalar_fact_of fact with
    | Some (expression, _) => facts_conflict (scalar_facts_about state expression)
    | None => false
    end) state.

(** The order-atom scan of [contradiction.rs::is_contradictory]. *)
Definition order_contradiction (state : abstract_state) : bool :=
  existsb (fun fact =>
    let bounds lhs rhs signed :=
      match ArithmeticHelpers.term_bounds state lhs signed,
            ArithmeticHelpers.term_bounds state rhs signed with
      | Some (lo, _), Some (_, hi) => Some (lo, hi)
      | _, _ => None
      end in
    match fact with
    | Lt lhs rhs signed =>
        match bounds lhs rhs signed with Some (lo, hi) => hi <=? lo | None => false end
    | Le lhs rhs signed =>
        match bounds lhs rhs signed with Some (lo, hi) => hi <? lo | None => false end
    | _ => false
    end) state.

(** Rust [contradiction.rs::is_contradictory]. *)
Definition is_contradictory (state : abstract_state) : bool :=
  scalar_contradiction state || order_contradiction state.

(** [check.rs::edge_state_owned] on an edge with no hint sited on it, where
    [apply_edge_hints] is the identity. [None] is a discharged edge.
    TODO(control-flow): hints apply lemmas (e.g. [Unguard], the only way a
    [Guarded] atom is recovered); they are not modeled, so no theorem covers
    an edge carrying one.
    TODO(branch-sync [NULL-RELEASE]): Rust then runs [release_null_results]:
    for every [Owns] token carried at offset 0 by a maybe-null pointer the edge
    pins to 0, [transfer.rs::release_token_facts] drops the token's [Owns]
    atom and the cells of its region and degrades its carriers to [Unknown].
    Rocq keeps all these facts, which still hold; it therefore rejects at
    [transfer_return] ([ensure_nothing_held]) a program that releases a
    reference only on a null edge, which Rust accepts. *)
Definition edge_state_without_hints (state : abstract_state) (edge : option branch) : option abstract_state :=
  let refined :=
    match edge with
    | Some (cond, size, taken) =>
        if branch_provably_not_taken state cond size taken then None
        else Some (state ++ branch_atoms state cond size taken)
    | None => Some state
    end in
  match refined with
  | Some state => if is_contradictory state then None else Some state
  | None => None
  end.

(** Rust [leaks::check_comparison] with [allow_ptr_leaks] false: a null
    check, two packet pointers, or two disclosable operands. *)
Definition check_comparison (state : abstract_state) (cond : condition) : bool :=
  let zero name :=
    match ArithmeticHelpers.term_bounds state (Var name) false with
    | Some (lo, hi) => (lo =? 0) && (hi =? 0)
    | None => false
    end in
  let packet name :=
    match find_pointer_fact state name with
    | Some ptr => Region.is_packet_family (ptr_ty ptr)
    | None => false
    end in
  let lhs := cond_dst cond in
  match cond_src cond with
  | SourceOperand.Imm imm => Int.eq imm Int.zero || disclosable state lhs
  | SourceOperand.Value rhs =>
      zero rhs || zero lhs || (packet lhs && packet rhs) ||
      (disclosable state lhs && disclosable state rhs)
  end.

(** [transfer.rs::validate_terminator] for a branch: [ensure_defined] on
    each register operand, then [leaks::check_comparison]. *)
Definition branch_operands_defined (state : abstract_state) (cond : condition) : bool :=
  ensure_defined state (cond_dst cond) &&
  match cond_src cond with
  | SourceOperand.Value name => ensure_defined state name
  | SourceOperand.Imm _ => true
  end &&
  check_comparison state cond.

(** Rocq adapters over the block post-state, after [check.rs::check_edge].
    [None] is a discharged edge ([edge_state_owned] gives [Ok(None)]); a
    branch's outer [None] is a Rust error. Edges keep the register naming:
    Rust substitutes successor parameters into the successor invariant.
    TODO(branch-sync [OWNERSHIP-ENTAIL]): Rust then requires the edge state to
    entail a successor invariant ([check_edge_entailment]) whose [Owns] atoms
    name every token the edge state owns ([ownership_preserved]); Rocq
    continues with the edge state itself and models neither check. *)
Definition transfer_jump (before : abstract_machine_state) : option abstract_machine_state :=
  option_map (fun state => AbstractMachineState state (register_name before))
    (edge_state_without_hints (facts before) None).

Definition transfer_branch (before : abstract_machine_state) (cond : condition)
    (size : OpSize.t) (taken : bool) : option (option abstract_machine_state) :=
  if branch_operands_defined (facts before) cond then
    Some (option_map (fun state => AbstractMachineState state (register_name before))
      (edge_state_without_hints (facts before) (Some (cond, size, taken))))
  else None.

(** A return that exits the whole program: the [Return] arm of
    [transfer.rs::validate_terminator] ([ensure_defined], then
    [ensure_nothing_held]) and the exit-value check of
    [check.rs::check_validated_program] ([leaks::ensure_disclosable],
    [ExitLeaksPointer]), which Rust applies to the blocks of the main
    program. Subprogram returns are not modeled. *)
Definition transfer_return (before : abstract_machine_state) : bool :=
  ensure_defined (facts before) (register_name before R0) &&
  ensure_nothing_held (facts before) &&
  disclosable (facts before) (register_name before R0).

(** =========== Soundness proof =========== *)

(** ** Theorem premises *)

(** ** Concrete comparisons *)

(** The comparison of [guard_is_true] against an arbitrary right operand. *)
Definition compare_values (memory : mem) (op : CmpOp.t) (size : OpSize.t)
    (lhs rhs : val) : option bool :=
  let narrow := match size with OpSize.Op32 => Val.loword | OpSize.Op64 => fun v => v end in
  let lhs := narrow lhs in
  let rhs := narrow rhs in
  let unsigned_cmp := match size with
    | OpSize.Op32 => Val.cmpu_bool (Mem.valid_pointer memory)
    | OpSize.Op64 => Val.cmplu_bool (Mem.valid_pointer memory) end in
  let signed_cmp := match size with
    | OpSize.Op32 => Val.cmp_bool | OpSize.Op64 => Val.cmpl_bool end in
  match op with
  | CmpOp.Eq => unsigned_cmp Ceq lhs rhs
  | CmpOp.Ne => unsigned_cmp Cne lhs rhs
  | CmpOp.UnsignedGt => unsigned_cmp Cgt lhs rhs
  | CmpOp.UnsignedGe => unsigned_cmp Cge lhs rhs
  | CmpOp.UnsignedLt => unsigned_cmp Clt lhs rhs
  | CmpOp.UnsignedLe => unsigned_cmp Cle lhs rhs
  | CmpOp.SignedGt => signed_cmp Cgt lhs rhs
  | CmpOp.SignedGe => signed_cmp Cge lhs rhs
  | CmpOp.SignedLt => signed_cmp Clt lhs rhs
  | CmpOp.SignedLe => signed_cmp Cle lhs rhs
  | CmpOp.BitSet =>
      match size with
      | OpSize.Op32 => unsigned_cmp Cne (Val.and lhs rhs) (Vint Int.zero)
      | OpSize.Op64 => unsigned_cmp Cne (Val.andl lhs rhs) (Vlong Int64.zero)
      end
  end.

Definition source_value (regs : regset) (source : ireg + int) : val :=
  match source with inl r => regs r | inr i => Vlong (int64_of_int i) end.

Lemma eqm32_of_eqm64 : forall x y, Int64.eqm x y -> Int.eqm x y.
Proof.
  intros x y EQM. eapply Zbits.eqmod_divides; [exact EQM |].
  exists 4294967296. reflexivity.
Qed.

Lemma loword_int64_of_int : forall i, Val.loword (Vlong (int64_of_int i)) = Vint i.
Proof.
  intros. cbn [Val.loword]. unfold Int64.loword, int64_of_int.
  now rewrite loword_repr64, Int.repr_signed.
Qed.

Lemma eval_cmp_compare : forall op size regs memory r source,
  (match lower_width size with W32 => eval_cmp32 | W64 => eval_cmp64 end)
    (lower_cmp_op op) regs memory r source =
  compare_values memory op size (regs r) (source_value regs source).
Proof.
  intros. destruct size, source; cbn [lower_width source_value];
    unfold eval_cmp32, eval_cmp64, compare_values;
    rewrite ?loword_int64_of_int; destruct op; reflexivity.
Qed.

Lemma land_le_left : forall a b, 0 <= a -> Z.land a b <= a.
Proof.
  intros a b NONNEG. apply Zbits.Ztestbit_le; [exact NONNEG |].
  intros i _ BIT. rewrite Z.land_spec in BIT. now apply andb_true_iff in BIT.
Qed.

Lemma unsigned_and64 : forall a b,
  Int64.unsigned (Int64.and a b) = Z.land (Int64.unsigned a) (Int64.unsigned b).
Proof.
  intros. unfold Int64.and. apply Int64.unsigned_repr.
  pose proof (Int64.unsigned_range_2 a). pose proof (Int64.unsigned_range_2 b).
  split; [apply Z.land_nonneg; lia |].
  pose proof (land_le_left (Int64.unsigned a) (Int64.unsigned b)). lia.
Qed.

Lemma unsigned_and32 : forall a b,
  Int.unsigned (Int.and a b) = Z.land (Int.unsigned a) (Int.unsigned b).
Proof.
  intros. unfold Int.and. apply Int.unsigned_repr.
  pose proof (Int.unsigned_range_2 a). pose proof (Int.unsigned_range_2 b).
  split; [apply Z.land_nonneg; lia |].
  pose proof (land_le_left (Int.unsigned a) (Int.unsigned b)). lia.
Qed.

Ltac decide_comparison :=
  repeat match goal with
  | |- context [zeq ?x ?y] => destruct (zeq x y)
  | |- context [zlt ?x ?y] => destruct (zlt x y)
  end;
  repeat match goal with
  | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
  | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
  | |- context [?x <=? ?y] => destruct (Z.leb_spec x y)
  end; cbn; try reflexivity; lia.

(** Defined comparisons of integers are Rust's [CmpOp::eval]. *)
Lemma compare_values_long : forall memory op size a b,
  compare_values memory op size (Vlong a) (Vlong b) =
  Some (cmp_eval op size (Int64.unsigned a) (Int64.unsigned b)).
Proof.
  intros. destruct size; unfold compare_values, cmp_eval;
    cbn [Val.loword Val.cmpu_bool Val.cmplu_bool Val.cmp_bool Val.cmpl_bool Val.and Val.andl];
    rewrite ?Int64.repr_unsigned; unfold Int64.loword;
    destruct op; f_equal;
    unfold Int.cmpu, Int.cmp, Int64.cmpu, Int64.cmp, Int.eq, Int.ltu, Int.lt,
      Int64.eq, Int64.ltu, Int64.lt;
    rewrite ?unsigned_and32, ?unsigned_and64, ?Int.unsigned_zero, ?Int64.unsigned_zero;
    decide_comparison.
Qed.

Lemma signed_max_repr : Int.signed (Int.repr Int.max_signed) = Int.max_signed.
Proof. reflexivity. Qed.
Lemma signed_min_repr : Int.signed (Int.repr Int.min_signed) = Int.min_signed.
Proof. reflexivity. Qed.
Lemma unsigned_mone_wide : Int64.unsigned (Int64.repr (Int.signed Int.mone)) = Int64.max_unsigned.
Proof. reflexivity. Qed.
Lemma unsigned_zero_wide : Int64.unsigned (Int64.repr (Int.signed Int.zero)) = 0.
Proof. reflexivity. Qed.

(** On scalar operands a static decision is the dynamic comparison. *)
Lemma static_compare : forall op size memory (regs : regset) r source c,
  eval_cmp_static (lower_cmp_op op) (lower_width size) r source = Some c ->
  (exists n, regs r = Vlong n) ->
  compare_values memory op size (regs r) (source_value regs source) = Some c.
Proof.
  intros op size memory regs r source c STATIC [a LEFT].
  destruct source as [s | i]; cbn [source_value]; unfold eval_cmp_static in STATIC.
  - destruct (ireg_eqb r s) eqn:SAME; try discriminate.
    assert (r = s) by (unfold ireg_eqb in SAME; destruct (ireg_eq r s); congruence).
    subst s. rewrite LEFT, compare_values_long. unfold cmp_eval.
    destruct op; inversion STATIC; subst c; destruct size; decide_comparison.
  - rewrite LEFT, compare_values_long. unfold cmp_eval, int64_of_int.
    rewrite ?Int64.repr_unsigned, ?loword_repr64, ?Int.repr_signed.
    pose proof (Int.signed_range (Int.repr (Int64.unsigned a))).
    pose proof (Int.unsigned_range_2 (Int.repr (Int64.unsigned a))).
    pose proof (Int64.unsigned_range_2 a).
    destruct size, op; cbn [lower_cmp_op lower_width] in STATIC; try discriminate;
      match type of STATIC with
      | (if Int.eq i ?bound then _ else _) = _ =>
          destruct (Int.eq i bound) eqn:EQ; inversion STATIC; subst c;
          apply Int.same_if_eq in EQ; subst i
      end;
      rewrite ?signed_max_repr, ?signed_min_repr, ?unsigned_mone_wide, ?unsigned_zero_wide,
        ?Int.unsigned_mone, ?Int.unsigned_zero;
      unfold Int.max_unsigned in *; decide_comparison.
Qed.

(** The edge a concrete branch takes is decided by [compare_values]. *)
Lemma branch_step_outcome : forall op size r source offset program regions
    (regs : regset) stack code_id count memory after,
  static_operands_scalar regs (Pjmpcmp (lower_cmp_op op) (lower_width size) r source offset) ->
  instruction_step regions program (Pjmpcmp (lower_cmp_op op) (lower_width size) r source offset)
    (TLS_State regs stack code_id count memory) after ->
  exists taken,
    compare_values memory op size (regs r) (source_value regs source) = Some taken /\
    after = TLS_State (nextinstr (if taken then regs # PC <- (Val.offset_ptr (regs PC) offset)
                                  else regs)) stack code_id count memory.
Proof.
  intros op size r source offset program regions regs stack code_id count memory after
    SCALAR STEP.
  destruct after as [regs' stack' code_id' count' memory'].
  unfold instruction_step in STEP. cbn [exec_instr] in STEP. unfold exec_jmpcmp in STEP.
  cbn [static_operands_scalar] in SCALAR.
  destruct (eval_cmp_static (lower_cmp_op op) (lower_width size) r source) as [c |] eqn:STATIC.
  - exists c. split; [apply static_compare; [exact STATIC | apply SCALAR; discriminate] |].
    inversion STEP; reflexivity.
  - pose proof (eval_cmp_compare op size regs memory r source) as COMPARE.
    destruct size; cbn [lower_width] in COMPARE, STEP; rewrite COMPARE in STEP;
      destruct (compare_values memory op _ (regs r) (source_value regs source)) as [c |];
      try discriminate; exists c; split; try reflexivity; inversion STEP; reflexivity.
Qed.

(** The comparison a taken edge establishes: Rust's [outcome]. *)
Definition cmp_outcome (op : CmpOp.t) (taken : bool) : option CmpOp.t :=
  if taken then Some op else cmp_negated op.

Lemma compare_values_negate : forall memory op op' size lhs rhs,
  cmp_negated op = Some op' ->
  compare_values memory op' size lhs rhs = option_map negb (compare_values memory op size lhs rhs).
Proof.
  intros memory op op' size lhs rhs NEGATED.
  destruct op; inversion NEGATED; subst op'; destruct size; unfold compare_values;
    first [ apply (Val.negate_cmpu_bool _ Cne) | apply (Val.negate_cmpu_bool _ Ceq)
          | apply (Val.negate_cmplu_bool _ Cne) | apply (Val.negate_cmplu_bool _ Ceq)
          | apply (Val.negate_cmpu_bool _ Cgt) | apply (Val.negate_cmpu_bool _ Cge)
          | apply (Val.negate_cmpu_bool _ Clt) | apply (Val.negate_cmpu_bool _ Cle)
          | apply (Val.negate_cmplu_bool _ Cgt) | apply (Val.negate_cmplu_bool _ Cge)
          | apply (Val.negate_cmplu_bool _ Clt) | apply (Val.negate_cmplu_bool _ Cle)
          | apply (Val.negate_cmp_bool Cgt) | apply (Val.negate_cmp_bool Cge)
          | apply (Val.negate_cmp_bool Clt) | apply (Val.negate_cmp_bool Cle)
          | apply (Val.negate_cmpl_bool Cgt) | apply (Val.negate_cmpl_bool Cge)
          | apply (Val.negate_cmpl_bool Clt) | apply (Val.negate_cmpl_bool Cle) ].
Qed.

Lemma compare_values_outcome : forall memory op op' size lhs rhs taken,
  compare_values memory op size lhs rhs = Some taken ->
  cmp_outcome op taken = Some op' ->
  compare_values memory op' size lhs rhs = Some true.
Proof.
  intros memory op op' size lhs rhs taken COMPARE OUTCOME.
  destruct taken; cbn [cmp_outcome] in OUTCOME.
  - inversion OUTCOME; subst op'. exact COMPARE.
  - rewrite (compare_values_negate _ _ _ _ _ _ OUTCOME), COMPARE. reflexivity.
Qed.

Lemma compare_values_loword : forall memory op lhs rhs rhs',
  Val.loword rhs = Val.loword rhs' ->
  compare_values memory op OpSize.Op32 lhs rhs = compare_values memory op OpSize.Op32 lhs rhs'.
Proof.
  intros memory op lhs rhs rhs' LOW. unfold compare_values. cbv beta iota zeta.
  now rewrite LOW.
Qed.

Lemma cmp_eval_widen_unsigned : forall op a b,
  op = CmpOp.Eq \/ op = CmpOp.Ne \/ cmp_is_signed op = false ->
  0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  cmp_eval op OpSize.Op32 a b = cmp_eval op OpSize.Op64 a b.
Proof.
  intros op a b KIND A B. unfold cmp_eval.
  rewrite !Int.unsigned_repr by lia.
  assert (WIDE : Int.max_unsigned < Int64.max_unsigned) by reflexivity.
  rewrite !Int64.unsigned_repr by lia.
  destruct op; cbn in KIND; intuition discriminate || reflexivity.
Qed.

Lemma cmp_eval_widen_signed : forall op a b,
  cmp_is_signed op = true ->
  Int.min_signed <= Int64.signed a <= Int.max_signed ->
  Int.min_signed <= Int64.signed b <= Int.max_signed ->
  cmp_eval op OpSize.Op32 (Int64.unsigned a) (Int64.unsigned b) =
  cmp_eval op OpSize.Op64 (Int64.unsigned a) (Int64.unsigned b).
Proof.
  intros op a b SIGNED A B. unfold cmp_eval. rewrite !Int64.repr_unsigned.
  assert (NARROW : forall x, Int.min_signed <= Int64.signed x <= Int.max_signed ->
    Int.signed (Int.repr (Int64.unsigned x)) = Int64.signed x).
  { intros x RANGE. rewrite <- (Int.signed_repr (Int64.signed x)) by exact RANGE.
    f_equal. apply Int.eqm_samerepr, eqm32_of_eqm64.
    apply Int64.eqm_sym, Int64.eqm_signed_unsigned. }
  rewrite (NARROW a A), (NARROW b B).
  destruct op; cbn in SIGNED; try discriminate; reflexivity.
Qed.

Lemma cmplu_eq_true : forall valid lhs rhs,
  Val.cmplu_bool valid Ceq lhs rhs = Some true -> runtime_value lhs /\ lhs = rhs.
Proof.
  intros valid lhs rhs COMPARE.
  destruct lhs, rhs; cbn in COMPARE; try discriminate;
    repeat match type of COMPARE with
    | context [if ?test then _ else _] => destruct test eqn:?; try discriminate
    end;
    try (inversion COMPARE; fail).
  - inversion COMPARE. apply Int64.same_if_eq in H0. subst. split; [constructor | reflexivity].
  - subst. inversion COMPARE. unfold Ptrofs.cmpu in H0. apply Ptrofs.same_if_eq in H0.
    subst. split; [constructor | reflexivity].
Qed.

Lemma cmplu_ne_true : forall valid lhs rhs,
  Val.cmplu_bool valid Cne lhs rhs = Some true ->
  runtime_value lhs /\ runtime_value rhs /\ lhs <> rhs.
Proof.
  intros valid lhs rhs COMPARE.
  destruct lhs, rhs; cbn in COMPARE; try discriminate;
    repeat match type of COMPARE with
    | context [if ?test then _ else _] => destruct test eqn:?; try discriminate
    end;
    repeat split; try constructor; try discriminate; inversion COMPARE.
  - intros SAME. inversion SAME; subst. rewrite Int64.eq_true in H0. discriminate.
  - intros SAME. inversion SAME; subst. unfold Ptrofs.cmpu in H0.
    rewrite Ptrofs.eq_true in H0. discriminate.
  - intros SAME. inversion SAME; subst. contradiction.
Qed.

(** ** Branch refinement *)

(** The right operand as the concrete branch reads it. *)
Definition operand_value (world : interpretation) (cond : condition) : val :=
  match cond_src cond with
  | SourceOperand.Imm imm => Vlong (int64_of_int imm)
  | SourceOperand.Value name => variable_value world name
  end.

(** The comparison selecting the edge of [taken]. *)
Definition branch_outcome (world : interpretation) (memory : mem) (cond : condition)
    (size : OpSize.t) (taken : bool) : Prop :=
  compare_values memory (cond_op cond) size
    (variable_value world (cond_dst cond)) (operand_value world cond) = Some taken.

Lemma branch_provably_not_taken_sound : forall world memory state cond size taken,
  Forall (atom_holds world memory) state ->
  branch_outcome world memory cond size taken ->
  branch_provably_not_taken state cond size taken = false.
Proof.
  intros world memory state cond size taken FACTS OUTCOME.
  unfold branch_provably_not_taken.
  destruct (ArithmeticHelpers.pinned state (Var (cond_dst cond))) as [lhs |] eqn:LEFT;
    [| reflexivity].
  destruct (ArithmeticHelpers.pinned_sound _ _ _ _ _ FACTS LEFT) as [a [A UA]]. cbn [eval_term] in A.
  unfold branch_outcome, operand_value in OUTCOME. rewrite A in OUTCOME.
  destruct (cond_src cond) as [imm | name].
  - rewrite compare_values_long in OUTCOME. injection OUTCOME as EVAL.
    unfold int64_of_int in EVAL. unfold ArithmeticHelpers.unsigned64.
    rewrite <- UA, EVAL. now destruct taken.
  - destruct (ArithmeticHelpers.pinned state (Var name)) as [rhs |] eqn:RIGHT;
      [| reflexivity].
    destruct (ArithmeticHelpers.pinned_sound _ _ _ _ _ FACTS RIGHT) as [b [B UB]]. cbn [eval_term] in B.
    rewrite B, compare_values_long in OUTCOME. injection OUTCOME as EVAL.
    rewrite <- UA, <- UB, EVAL. now destruct taken.
Qed.

Lemma operand_rhs_compare : forall world memory op size cond lhs,
  compare_values memory op size lhs (operand_value world cond) =
  compare_values memory op size lhs (eval_term world (branch_rhs_term cond size)).
Proof.
  intros. unfold operand_value, branch_rhs_term.
  destruct (cond_src cond) as [imm | name]; [| reflexivity].
  destruct size; [| reflexivity].
  apply compare_values_loword. cbn [eval_term Val.loword]. f_equal.
  unfold Int64.loword, int64_of_int, jmp_imm_const. rewrite !loword_repr64.
  destruct (cmp_is_signed (cond_op cond)); now rewrite ?Int.repr_signed, ?Int.repr_unsigned.
Qed.

Lemma ne32_widens : forall memory lhs rhs,
  compare_values memory CmpOp.Ne OpSize.Op32 lhs rhs = Some true ->
  compare_values memory CmpOp.Ne OpSize.Op64 lhs rhs = Some true.
Proof.
  intros memory lhs rhs COMPARE.
  destruct lhs, rhs; cbn in COMPARE; try discriminate.
  cbn. injection COMPARE as NE. f_equal.
  destruct (Int64.eq i i0) eqn:SAME; [| reflexivity].
  apply Int64.same_if_eq in SAME. subst. now rewrite Int.eq_true in NE.
Qed.

Lemma outcome_kind : forall op taken op' domain,
  cmp_outcome op taken = Some op' ->
  jmp32_widening_domain op taken = Some domain ->
  match domain with
  | WidenUnsigned => op' = CmpOp.Eq \/ op' = CmpOp.Ne \/ cmp_is_signed op' = false
  | WidenSigned => cmp_is_signed op' = true
  end.
Proof.
  intros op taken op' domain OUTCOME DOMAIN.
  destruct op, taken; cbn in OUTCOME, DOMAIN; inversion OUTCOME; inversion DOMAIN; subst;
    cbn; auto.
Qed.

Lemma confined_unsigned : forall world memory state expression,
  Forall (atom_holds world memory) state ->
  operand_confined_to state expression WidenUnsigned = true ->
  exists n, eval_term world expression = Vlong n /\ 0 <= Int64.unsigned n <= Int.max_unsigned.
Proof.
  intros world memory state expression FACTS CONFINED. cbn [operand_confined_to] in CONFINED.
  destruct (ArithmeticHelpers.term_bounds state expression false) as [[lo hi] |] eqn:BOUNDS;
    try discriminate.
  apply Z.leb_le in CONFINED.
  destruct (ArithmeticHelpers.term_bounds_unsigned_sound _ _ _ _ _ _ FACTS BOUNDS)
    as [n [VALUE RANGE]].
  exists n. split; [exact VALUE |]. pose proof (Int64.unsigned_range n). lia.
Qed.

Lemma confined_signed : forall world memory state expression,
  Forall (atom_holds world memory) state ->
  ArithmeticHelpers.eq_constants_fit_i64 state ->
  (forall constant, expression = Const constant ->
    Int64.min_signed <= constant <= Int64.max_signed) ->
  operand_confined_to state expression WidenSigned = true ->
  exists n, eval_term world expression = Vlong n /\
    Int.min_signed <= Int64.signed n <= Int.max_signed.
Proof.
  intros world memory state expression FACTS FIT CONST CONFINED.
  cbn [operand_confined_to] in CONFINED.
  destruct (ArithmeticHelpers.term_bounds state expression true) as [[lo hi] |] eqn:BOUNDS;
    try discriminate.
  apply andb_true_iff in CONFINED as [LO HI]. apply Z.leb_le in LO, HI.
  destruct (ArithmeticHelpers.term_bounds_signed_sound _ _ _ _ _ _ FACTS FIT CONST BOUNDS)
    as [n [VALUE RANGE]].
  exists n. split; [exact VALUE | lia].
Qed.

Lemma branch_rhs_fits : forall cond size constant,
  branch_rhs_term cond size = Const constant ->
  Int64.min_signed <= constant <= Int64.max_signed.
Proof.
  intros cond size constant RHS. unfold branch_rhs_term in RHS.
  destruct (cond_src cond) as [imm |]; try discriminate. inversion RHS; subst.
  pose proof (Int.signed_range imm). pose proof (Int.unsigned_range_2 imm).
  assert (Int64.min_signed < Int.min_signed) by reflexivity.
  assert (Int.max_unsigned < Int64.max_signed) by reflexivity.
  assert (Int.max_signed < Int.max_unsigned) by reflexivity.
  assert (Int.min_signed < 0) by reflexivity.
  unfold jmp_imm_const. destruct size; [destruct (cmp_is_signed _) |]; lia.
Qed.

(** Every injected comparison holds at full width. *)
Lemma branch_true64 : forall world memory state cond size taken op',
  cond_op cond <> CmpOp.BitSet ->
  Forall (atom_holds world memory) state ->
  ArithmeticHelpers.eq_constants_fit_i64 state ->
  branch_outcome world memory cond size taken ->
  branch_suppressed state cond size taken = false ->
  cmp_outcome (cond_op cond) taken = Some op' ->
  compare_values memory op' OpSize.Op64 (variable_value world (cond_dst cond))
    (eval_term world (branch_rhs_term cond size)) = Some true.
Proof.
  intros world memory state cond size taken op' NOT_SET FACTS FIT OUTCOME SUPPRESSED OUT.
  unfold branch_outcome in OUTCOME. rewrite operand_rhs_compare in OUTCOME.
  pose proof (compare_values_outcome _ _ _ _ _ _ _ OUTCOME OUT) as TRUE.
  destruct size; [| exact TRUE].
  unfold branch_suppressed in SUPPRESSED.
  destruct (jmp32_widening_domain (cond_op cond) taken) as [domain |] eqn:DOMAIN.
  - apply negb_false_iff, andb_true_iff in SUPPRESSED as [LEFT RIGHT].
    pose proof (outcome_kind _ _ _ _ OUT DOMAIN) as KIND.
    destruct domain.
    + destruct (confined_unsigned _ _ _ _ FACTS LEFT) as [a [A RA]].
      destruct (confined_unsigned _ _ _ _ FACTS RIGHT) as [b [B RB]].
      cbn [eval_term] in A. rewrite A, B, compare_values_long in TRUE |- *.
      rewrite <- cmp_eval_widen_unsigned by assumption. exact TRUE.
    + destruct (confined_signed world memory state (Var (cond_dst cond)) FACTS FIT
        ltac:(discriminate) LEFT) as [a [A RA]].
      destruct (confined_signed world memory state _ FACTS FIT
        (branch_rhs_fits cond OpSize.Op32) RIGHT) as [b [B RB]].
      cbn [eval_term] in A. rewrite A, B, compare_values_long in TRUE |- *.
      rewrite <- cmp_eval_widen_signed by assumption. exact TRUE.
  - destruct (cond_op cond), taken; cbn in DOMAIN, OUT; try discriminate;
      try contradiction; inversion OUT; subst op'; now apply ne32_widens.
Qed.

Lemma outcome_atoms_hold : forall world memory dst rhs op taken op' imm_zero,
  cmp_outcome op taken = Some op' ->
  compare_values memory op' OpSize.Op64 (variable_value world dst) (eval_term world rhs) =
    Some true ->
  (imm_zero = true -> eval_term world rhs = Vlong Int64.zero) ->
  Forall (atom_holds world memory) (comparison_atoms (Var dst) rhs op taken imm_zero).
Proof.
  intros world memory dst rhs op taken op' imm_zero OUT TRUE ZERO.
  destruct op, taken; cbn in OUT; inversion OUT; subst op'; cbn in TRUE;
    cbn [comparison_atoms];
    try (destruct imm_zero eqn:IS_ZERO);
    repeat constructor; cbn [atom_holds eval_term]; unfold comparison_is_true;
    first
      [ exact TRUE
      | rewrite <- Val.swap_cmplu_bool; exact TRUE
      | rewrite <- Val.swap_cmpl_bool; exact TRUE
      | idtac ].
  all: try (apply cmplu_eq_true in TRUE; tauto).
  all: apply cmplu_ne_true in TRUE as [L [R NE]];
    try rewrite <- (ZERO eq_refl); tauto.
Qed.

Lemma branch_atoms_hold : forall world memory state cond size taken,
  Forall (atom_holds world memory) state ->
  ArithmeticHelpers.eq_constants_fit_i64 state ->
  branch_outcome world memory cond size taken ->
  Forall (atom_holds world memory) (branch_atoms state cond size taken).
Proof.
  intros world memory state cond size taken FACTS FIT OUTCOME.
  unfold branch_atoms.
  destruct (branch_suppressed state cond size taken) eqn:SUPPRESSED; [constructor |].
  destruct (cmp_op_eq_dec (cond_op cond) CmpOp.BitSet) as [SET | NOT_SET].
  { rewrite SET. constructor. }
  destruct (cmp_outcome (cond_op cond) taken) as [op' |] eqn:OUT.
  - eapply outcome_atoms_hold; [exact OUT |
      exact (branch_true64 _ _ _ _ _ _ _ NOT_SET FACTS FIT OUTCOME SUPPRESSED OUT) |].
    destruct (cond_src cond) as [imm |] eqn:SOURCE; [| discriminate].
    intros IS_ZERO. apply Int.same_if_eq in IS_ZERO. subst imm.
    unfold branch_rhs_term. rewrite SOURCE. unfold jmp_imm_const.
    destruct size; [destruct (cmp_is_signed _) |]; reflexivity.
  - destruct (cond_op cond), taken; cbn in OUT; try discriminate. constructor.
Qed.

(** ** Contradiction detection *)

(** Rust [Term::Const] holds an [i64]; the order scan reads its constants. *)
Definition order_constants_fit_i64 (state : abstract_state) : Prop :=
  forall lhs rhs signed,
    In (Lt lhs rhs signed) state \/ In (Le lhs rhs signed) state ->
    (forall constant, lhs = Const constant -> Int64.min_signed <= constant <= Int64.max_signed) /\
    (forall constant, rhs = Const constant -> Int64.min_signed <= constant <= Int64.max_signed).

Definition scalar_holds (world : interpretation) (expression : term) (fact : scalar_fact) : Prop :=
  match fact with
  | EqConst constant => eval_term world expression = Vlong (Int64.repr constant)
  | NeqConst constant => eval_term world expression <> Vlong (Int64.repr constant)
  | UnsignedFact bounds => exists n, eval_term world expression = Vlong n /\
      u_lower bounds <= Int64.unsigned n <= u_upper bounds
  | SignedFact bounds => exists n, eval_term world expression = Vlong n /\
      lower bounds <= Int64.signed n <= upper bounds
  end.

Definition scalar_fits (fact : scalar_fact) : Prop :=
  match fact with
  | EqConst constant => Int64.min_signed <= constant <= Int64.max_signed
  | _ => True
  end.

Lemma scalar_fact_holds : forall world memory fact expression scalar,
  atom_holds world memory fact -> scalar_fact_of fact = Some (expression, scalar) ->
  scalar_holds world expression scalar.
Proof.
  intros world memory fact expression scalar HOLDS SCALAR.
  destruct fact; cbn in SCALAR; try discriminate;
    repeat match type of SCALAR with
    | context [match ?t with _ => _ end] => destruct t
    end; inversion SCALAR; subst; cbn [atom_holds value_holds eval_term] in HOLDS; cbn;
    try solve [destruct HOLDS; congruence | tauto].
  all: try (destruct (eval_term world expression); try contradiction; eexists; split; eauto).
  all: try (intros SAME; apply (proj2 HOLDS); rewrite SAME; reflexivity).
  all: destruct HOLDS as [_ [_ NE]]; intros SAME; apply NE; congruence.
Qed.

Lemma scalar_fact_eq_const : forall fact expression constant,
  scalar_fact_of fact = Some (expression, EqConst constant) ->
  ArithmeticHelpers.eq_const fact = Some (expression, constant).
Proof.
  intros fact expression constant SCALAR.
  destruct fact; cbn in SCALAR |- *; try discriminate;
    repeat match type of SCALAR with
    | context [match ?t with _ => _ end] => destruct t
    end; inversion SCALAR; subst; reflexivity.
Qed.

Lemma scalar_fact_fits : forall state fact expression scalar,
  ArithmeticHelpers.eq_constants_fit_i64 state -> In fact state ->
  scalar_fact_of fact = Some (expression, scalar) -> scalar_fits scalar.
Proof.
  intros state fact expression scalar FIT IN SCALAR.
  destruct scalar; cbn; trivial.
  eapply FIT; [exact IN | apply scalar_fact_eq_const; exact SCALAR].
Qed.

Lemma repr_signed_fits : forall constant,
  Int64.min_signed <= constant <= Int64.max_signed ->
  Int64.signed (Int64.repr constant) = constant.
Proof. intros. now apply Int64.signed_repr. Qed.

(** Two facts about one term without a common model: the conflicts
    [facts_conflict] finds between a pair of facts. *)
Definition scalar_facts_conflict (first second : scalar_fact) : bool :=
  let u64 := ArithmeticHelpers.unsigned64 in
  match first, second with
  | EqConst x, EqConst y => negb (x =? y)
  | EqConst x, NeqConst y | NeqConst y, EqConst x => x =? y
  | NeqConst c, UnsignedFact r | UnsignedFact r, NeqConst c =>
      (u_lower r =? u_upper r) && (u_lower r =? u64 c)
  | NeqConst c, SignedFact r | SignedFact r, NeqConst c =>
      (lower r =? upper r) && (lower r =? c)
  | EqConst c, UnsignedFact r | UnsignedFact r, EqConst c =>
      (u64 c <? u_lower r) || (u_upper r <? u64 c)
  | EqConst c, SignedFact r | SignedFact r, EqConst c =>
      (c <? lower r) || (upper r <? c)
  | UnsignedFact x, UnsignedFact y =>
      Z.min (u_upper x) (u_upper y) <? Z.max (u_lower x) (u_lower y)
  | SignedFact x, SignedFact y =>
      Z.min (upper x) (upper y) <? Z.max (lower x) (lower y)
  | NeqConst _, NeqConst _ | UnsignedFact _, SignedFact _ | SignedFact _, UnsignedFact _ => false
  end.

Lemma scalar_facts_no_conflict : forall world expression scalar scalar',
  scalar_holds world expression scalar -> scalar_holds world expression scalar' ->
  scalar_fits scalar -> scalar_fits scalar' ->
  scalar_facts_conflict scalar scalar' = false.
Proof.
  intros world expression scalar scalar' HOLDS HOLDS' FITS FITS'.
  unfold ArithmeticHelpers.unsigned64.
  destruct scalar, scalar'; cbn [scalar_holds scalar_fits scalar_facts_conflict] in *; trivial;
    repeat match goal with
    | H : exists n, _ /\ _ |- _ => destruct H as [? [? ?]]
    end;
    try match goal with
    | H : eval_term world expression = _, H' : eval_term world expression = _ |- _ =>
        rewrite H in H'; inversion H'; subst
    | H : eval_term world expression = _, H' : eval_term world expression <> _ |- _ =>
        rewrite H in H'
    end.
  all: unfold ArithmeticHelpers.unsigned64 in *;
    repeat match goal with
    | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
    | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
    end; cbn; trivial; exfalso.
  all: cbn [scalar_fits] in *; rewrite ?repr_signed_fits in * by assumption; try lia; try congruence.
  all: match goal with
    | SAME : Vlong (Int64.repr ?a) = Vlong (Int64.repr ?b), DIFFERENT : ?a <> ?b |- _ =>
        apply DIFFERENT; rewrite <- (repr_signed_fits a), <- (repr_signed_fits b) by assumption;
        congruence
    | NE : Vlong ?n <> Vlong (Int64.repr ?c) |- _ =>
        apply NE; f_equal;
        first [ rewrite <- (Int64.repr_unsigned n), <- (Int64.repr_unsigned (Int64.repr c));
                f_equal; lia
              | rewrite <- (Int64.repr_signed n); f_equal; lia ]
    end.
Qed.

Definition summary_holds (world : interpretation) (expression : term)
    (summary : fact_summary) : Prop :=
  (forall c, summary_pinned summary = Some c ->
     scalar_holds world expression (EqConst c) /\ scalar_fits (EqConst c)) /\
  (forall r, summary_unsigned summary = Some r -> scalar_holds world expression (UnsignedFact r)) /\
  (forall r, summary_signed summary = Some r -> scalar_holds world expression (SignedFact r)).

Lemma summarize_fact_sound : forall world expression summary fact,
  summary_holds world expression summary ->
  scalar_holds world expression fact -> scalar_fits fact ->
  exists summary', summarize_fact summary fact = Some summary' /\
    summary_holds world expression summary'.
Proof.
  intros world expression [pinned unsigned signed] fact [PINNED [UNSIGNED SIGNED]] HOLDS FITS.
  cbn [summary_pinned summary_unsigned summary_signed] in PINNED, UNSIGNED, SIGNED.
  destruct fact as [c | c | r | r]; cbn [summarize_fact].
  - assert (NEXT : summary_holds world expression (FactSummary (Some c) unsigned signed)).
    { split; [| exact (conj UNSIGNED SIGNED)]. intros c' SAME. now inversion SAME; subst. }
    destruct pinned as [p |]; [| eexists; split; [reflexivity | exact NEXT]].
    destruct (PINNED p eq_refl) as [HOLDS_P FITS_P].
    pose proof (scalar_facts_no_conflict _ _ _ _ HOLDS_P HOLDS FITS_P FITS) as NO.
    apply negb_false_iff in NO. rewrite NO. eexists. split; [reflexivity | exact NEXT].
  - eexists. split; [reflexivity | exact (conj PINNED (conj UNSIGNED SIGNED))].
  - destruct HOLDS as [n [VALUE RANGE]].
    set (meet := match unsigned with
      | Some u => URange (Z.max (u_lower u) (u_lower r)) (Z.min (u_upper u) (u_upper r))
      | None => r
      end).
    assert (MEET : u_lower meet <= Int64.unsigned n <= u_upper meet).
    { subst meet. destruct unsigned as [u |]; [| exact RANGE].
      destruct (UNSIGNED u eq_refl) as [n' [VALUE' RANGE']].
      rewrite VALUE in VALUE'. inversion VALUE'; subst n'. cbn [u_lower u_upper]. lia. }
    destruct (Z.ltb_spec (u_upper meet) (u_lower meet)); [lia |].
    eexists. split; [reflexivity |]. split; [exact PINNED | split; [| exact SIGNED]].
    intros r' SAME. inversion SAME; subst r'. exists n. split; [exact VALUE | exact MEET].
  - destruct HOLDS as [n [VALUE RANGE]].
    set (meet := match signed with
      | Some s => Range (Z.max (lower s) (lower r)) (Z.min (upper s) (upper r))
      | None => r
      end).
    assert (MEET : lower meet <= Int64.signed n <= upper meet).
    { subst meet. destruct signed as [s |]; [| exact RANGE].
      destruct (SIGNED s eq_refl) as [n' [VALUE' RANGE']].
      rewrite VALUE in VALUE'. inversion VALUE'; subst n'. cbn [lower upper]. lia. }
    destruct (Z.ltb_spec (upper meet) (lower meet)); [lia |].
    eexists. split; [reflexivity |]. split; [exact PINNED | split; [exact UNSIGNED |]].
    intros r' SAME. inversion SAME; subst r'. exists n. split; [exact VALUE | exact MEET].
Qed.

Lemma summarize_facts_sound : forall world expression facts summary,
  Forall (fun fact => scalar_holds world expression fact /\ scalar_fits fact) facts ->
  summary_holds world expression summary ->
  exists summary', summarize_facts summary facts = Some summary' /\
    summary_holds world expression summary'.
Proof.
  intros world expression facts. induction facts as [| fact rest IH]; intros summary FACTS HOLDS.
  - exists summary. split; [reflexivity | exact HOLDS].
  - inversion FACTS as [| ? ? [FACT FITS] REST]; subst.
    destruct (summarize_fact_sound _ _ _ _ HOLDS FACT FITS) as [next [STEP NEXT]].
    cbn [summarize_facts]. rewrite STEP. exact (IH next REST NEXT).
Qed.

(** Facts about one term that all hold never conflict. *)
Lemma facts_conflict_sound : forall world expression facts,
  Forall (fun fact => scalar_holds world expression fact /\ scalar_fits fact) facts ->
  facts_conflict facts = false.
Proof.
  intros world expression facts FACTS. unfold facts_conflict.
  destruct (summarize_facts_sound world expression facts (FactSummary None None None) FACTS)
    as [[pinned unsigned signed] [SUMMARY [PINNED [UNSIGNED SIGNED]]]];
    [repeat split; discriminate |].
  rewrite SUMMARY. cbn [summary_pinned summary_unsigned summary_signed] in PINNED, UNSIGNED, SIGNED.
  apply orb_false_iff. split.
  - destruct pinned as [c |]; [| reflexivity].
    destruct (PINNED c eq_refl) as [HOLDS_C FITS_C].
    apply orb_false_iff. split.
    + destruct unsigned as [r |]; [| reflexivity].
      exact (scalar_facts_no_conflict _ _ (EqConst c) (UnsignedFact r)
        HOLDS_C (UNSIGNED r eq_refl) FITS_C I).
    + destruct signed as [r |]; [| reflexivity].
      exact (scalar_facts_no_conflict _ _ (EqConst c) (SignedFact r)
        HOLDS_C (SIGNED r eq_refl) FITS_C I).
  - destruct (existsb _ facts) eqn:CONFLICT; [| reflexivity].
    apply existsb_exists in CONFLICT as [fact [IN CHECK]].
    destruct ((proj1 (Forall_forall _ _) FACTS) _ IN) as [HOLDS _].
    destruct fact as [| c | |]; try discriminate.
    apply orb_true_iff in CHECK as [CHECK | CHECK]; [apply orb_true_iff in CHECK as [CHECK | CHECK] |].
    + destruct pinned as [p |]; [| discriminate].
      destruct (PINNED p eq_refl) as [HOLDS_P FITS_P].
      assert (CONFLICTS : scalar_facts_conflict (NeqConst c) (EqConst p) = true) by exact CHECK.
      now rewrite (scalar_facts_no_conflict _ _ _ _ HOLDS HOLDS_P I FITS_P) in CONFLICTS.
    + destruct unsigned as [r |]; [| discriminate].
      assert (CONFLICTS : scalar_facts_conflict (NeqConst c) (UnsignedFact r) = true) by exact CHECK.
      now rewrite (scalar_facts_no_conflict _ _ _ _ HOLDS (UNSIGNED r eq_refl) I I) in CONFLICTS.
    + destruct signed as [r |]; [| discriminate].
      assert (CONFLICTS : scalar_facts_conflict (NeqConst c) (SignedFact r) = true) by exact CHECK.
      now rewrite (scalar_facts_no_conflict _ _ _ _ HOLDS (SIGNED r eq_refl) I I) in CONFLICTS.
Qed.

Lemma scalar_facts_about_hold : forall world memory state expression,
  Forall (atom_holds world memory) state ->
  ArithmeticHelpers.eq_constants_fit_i64 state ->
  Forall (fun fact => scalar_holds world expression fact /\ scalar_fits fact)
    (scalar_facts_about state expression).
Proof.
  intros world memory state expression FACTS FIT. apply Forall_forall.
  intros scalar IN. unfold scalar_facts_about in IN.
  apply in_flat_map in IN as [fact [IN_STATE SCALAR]].
  destruct (scalar_fact_of fact) as [[other scalar'] |] eqn:OF; [| contradiction].
  destruct (term_beq expression other) eqn:SAME; [| contradiction].
  destruct SCALAR as [<- | []]. apply internal_term_dec_bl in SAME. subst other.
  split.
  - eapply scalar_fact_holds; [exact ((proj1 (Forall_forall _ _) FACTS) _ IN_STATE) | exact OF].
  - eapply scalar_fact_fits; eauto.
Qed.

Lemma scalar_contradiction_sound : forall world memory state,
  Forall (atom_holds world memory) state ->
  ArithmeticHelpers.eq_constants_fit_i64 state ->
  scalar_contradiction state = false.
Proof.
  intros world memory state FACTS FIT. unfold scalar_contradiction.
  destruct (existsb _ state) eqn:CONFLICT; [| reflexivity].
  apply existsb_exists in CONFLICT as [fact [_ CHECK]].
  destruct (scalar_fact_of fact) as [[expression _] |]; [| discriminate].
  rewrite (facts_conflict_sound world expression) in CHECK; [discriminate |].
  eapply scalar_facts_about_hold; eauto.
Qed.

Lemma comparison_bounds : forall world memory state expression signed lo hi,
  Forall (atom_holds world memory) state ->
  ArithmeticHelpers.eq_constants_fit_i64 state ->
  (forall constant, expression = Const constant ->
    Int64.min_signed <= constant <= Int64.max_signed) ->
  ArithmeticHelpers.term_bounds state expression signed = Some (lo, hi) ->
  exists n, eval_term world expression = Vlong n /\
    lo <= (if signed then Int64.signed n else Int64.unsigned n) <= hi.
Proof.
  intros world memory state expression signed lo hi FACTS FIT CONST BOUNDS.
  destruct signed.
  - eapply ArithmeticHelpers.term_bounds_signed_sound; eauto.
  - eapply ArithmeticHelpers.term_bounds_unsigned_sound; eauto.
Qed.

Lemma order_contradiction_sound : forall world memory state,
  Forall (atom_holds world memory) state ->
  ArithmeticHelpers.eq_constants_fit_i64 state ->
  order_constants_fit_i64 state ->
  order_contradiction state = false.
Proof.
  intros world memory state FACTS FIT ORDER. unfold order_contradiction.
  destruct (existsb _ state) eqn:CONTRADICTION; [| reflexivity].
  apply existsb_exists in CONTRADICTION as [fact [IN CHECK]].
  pose proof ((proj1 (Forall_forall _ _) FACTS) _ IN) as HOLDS.
  destruct fact; cbv beta iota zeta in CHECK; try discriminate;
    [destruct (ORDER lhs rhs signed (or_intror IN)) as [LEFT RIGHT]
    | destruct (ORDER lhs rhs signed (or_introl IN)) as [LEFT RIGHT]];
    destruct (ArithmeticHelpers.term_bounds state lhs signed) as [[lo ?] |] eqn:LOWER;
      try discriminate;
    destruct (ArithmeticHelpers.term_bounds state rhs signed) as [[? hi] |] eqn:UPPER;
      try discriminate;
    destruct (comparison_bounds _ _ _ _ _ _ _ FACTS FIT LEFT LOWER) as [a [A RA]];
    destruct (comparison_bounds _ _ _ _ _ _ _ FACTS FIT RIGHT UPPER) as [b [B RB]];
    cbn [atom_holds] in HOLDS; unfold comparison_is_true in HOLDS; rewrite A, B in HOLDS;
    destruct signed; cbn in HOLDS; injection HOLDS as COMPARE;
    unfold Int64.lt, Int64.ltu in COMPARE;
    repeat match type of COMPARE with
    | context [zlt ?x ?y] => destruct (zlt x y)
    end; cbn in COMPARE; try discriminate;
    first [apply Z.leb_le in CHECK | apply Z.ltb_lt in CHECK]; lia.
Qed.

Lemma is_contradictory_sound : forall world memory state,
  Forall (atom_holds world memory) state ->
  ArithmeticHelpers.eq_constants_fit_i64 state ->
  order_constants_fit_i64 state ->
  is_contradictory state = false.
Proof.
  intros world memory state FACTS FIT ORDER. unfold is_contradictory.
  now rewrite (scalar_contradiction_sound _ _ _ FACTS FIT),
    (order_contradiction_sound _ _ _ FACTS FIT ORDER).
Qed.

Lemma comparison_atoms_fit : forall dst rhs op taken zero fact,
  (forall constant, rhs = Const constant -> Int64.min_signed <= constant <= Int64.max_signed) ->
  In fact (comparison_atoms (Var dst) rhs op taken zero) ->
  (forall expression constant, ArithmeticHelpers.eq_const fact = Some (expression, constant) ->
     Int64.min_signed <= constant <= Int64.max_signed) /\
  (forall lhs rhs' signed, fact = Lt lhs rhs' signed \/ fact = Le lhs rhs' signed ->
     (forall constant, lhs = Const constant -> Int64.min_signed <= constant <= Int64.max_signed) /\
     (forall constant, rhs' = Const constant -> Int64.min_signed <= constant <= Int64.max_signed)).
Proof.
  intros dst rhs op taken zero fact RHS IN.
  destruct op, taken; try destruct zero; cbn [comparison_atoms In] in IN;
    try contradiction; destruct IN as [<- | []]; split;
    try (intros expression constant EQ; destruct rhs; cbn in EQ; inversion EQ; subst;
         apply RHS; reflexivity);
    intros lhs rhs' signed [SAME | SAME]; inversion SAME; subst;
    split; intros constant CONSTANT; try discriminate; apply RHS; exact CONSTANT.
Qed.

Lemma branch_atoms_fit : forall state cond size taken,
  ArithmeticHelpers.eq_constants_fit_i64 state -> order_constants_fit_i64 state ->
  ArithmeticHelpers.eq_constants_fit_i64 (state ++ branch_atoms state cond size taken) /\
  order_constants_fit_i64 (state ++ branch_atoms state cond size taken).
Proof.
  intros state cond size taken FIT ORDER.
  assert (ATOMS : forall fact, In fact (branch_atoms state cond size taken) ->
    (forall expression constant, ArithmeticHelpers.eq_const fact = Some (expression, constant) ->
       Int64.min_signed <= constant <= Int64.max_signed) /\
    (forall lhs rhs signed, fact = Lt lhs rhs signed \/ fact = Le lhs rhs signed ->
       (forall constant, lhs = Const constant -> Int64.min_signed <= constant <= Int64.max_signed) /\
       (forall constant, rhs = Const constant -> Int64.min_signed <= constant <= Int64.max_signed))).
  { intros fact IN. unfold branch_atoms in IN.
    destruct (branch_suppressed state cond size taken); [contradiction |].
    eapply comparison_atoms_fit; [apply branch_rhs_fits | exact IN]. }
  split.
  - intros fact expression constant IN EQ. apply in_app_or in IN as [IN | IN].
    + eapply FIT; eauto.
    + eapply (proj1 (ATOMS fact IN)); eauto.
  - intros lhs rhs signed IN.
    destruct IN as [IN | IN]; apply in_app_or in IN as [IN | IN].
    + apply (ORDER lhs rhs signed). left. exact IN.
    + apply (proj2 (ATOMS _ IN) lhs rhs signed). left. reflexivity.
    + apply (ORDER lhs rhs signed). right. exact IN.
    + apply (proj2 (ATOMS _ IN) lhs rhs signed). right. reflexivity.
Qed.

(** ** Edge states *)

Lemma edge_state_branch_sound : forall world memory state cond size taken,
  Forall (atom_holds world memory) state ->
  ArithmeticHelpers.eq_constants_fit_i64 state ->
  order_constants_fit_i64 state ->
  branch_outcome world memory cond size taken ->
  exists post, edge_state_without_hints state (Some (cond, size, taken)) = Some post /\
    Forall (atom_holds world memory) post.
Proof.
  intros world memory state cond size taken FACTS FIT ORDER OUTCOME.
  unfold edge_state_without_hints.
  rewrite (branch_provably_not_taken_sound _ _ _ _ _ _ FACTS OUTCOME).
  destruct (branch_atoms_fit state cond size taken FIT ORDER) as [FIT' ORDER'].
  assert (REFINED : Forall (atom_holds world memory) (state ++ branch_atoms state cond size taken)).
  { apply Forall_app. split; [exact FACTS | now apply branch_atoms_hold]. }
  rewrite (is_contradictory_sound _ _ _ REFINED FIT' ORDER').
  eexists. split; [reflexivity | exact REFINED].
Qed.

Lemma edge_state_jump_sound : forall world memory state,
  Forall (atom_holds world memory) state ->
  ArithmeticHelpers.eq_constants_fit_i64 state ->
  order_constants_fit_i64 state ->
  exists post, edge_state_without_hints state None = Some post /\
    Forall (atom_holds world memory) post.
Proof.
  intros world memory state FACTS FIT ORDER. unfold edge_state_without_hints.
  rewrite (is_contradictory_sound _ _ _ FACTS FIT ORDER).
  eexists. split; [reflexivity | exact FACTS].
Qed.

(** ** Terminator soundness *)

Lemma nextinstr_ireg : forall (regs : regset) (reg : ireg), nextinstr regs reg = regs reg.
Proof. intros. unfold nextinstr. now rewrite Pregmap.gso by discriminate. Qed.

Lemma set_pc_ireg : forall (regs : regset) value (reg : ireg), (regs # PC <- value) reg = regs reg.
Proof. intros. now rewrite Pregmap.gso by discriminate. Qed.

(** The jump edge out of a state with a concretization is not discharged, and
    its state concretizes the jump's successor configuration. *)
Theorem transfer_jump_sound :
  forall (attrs : load_attrs) program regions before concrete offset,
    concretizes attrs regions before concrete ->
    ArithmeticHelpers.eq_constants_fit_i64 (facts before) ->
    order_constants_fit_i64 (facts before) ->
    exists after concrete',
      transfer_jump before = Some after /\
      instruction_step regions program (Pjmp64 offset) concrete concrete' /\
      concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before concrete offset CONCRETE FIT ORDER.
  destruct concrete as [regs stack code_id count memory].
  destruct CONCRETE as [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]].
  destruct (edge_state_jump_sound _ _ _ FACTS FIT ORDER) as [post [EDGE POST]].
  exists (AbstractMachineState post (register_name before)).
  unfold transfer_jump. rewrite EDGE.
  exists (TLS_State (nextinstr (regs # PC <- (Val.offset_ptr (regs PC) offset)))
    stack code_id count memory). split; [reflexivity | split; [reflexivity |]].
  exists world. split; [| auto].
  intros reg NOT_AUX. cbn [register_name]. rewrite nextinstr_ireg, set_pc_ireg.
  exact (REGISTERS reg NOT_AUX).
Qed.

(** Soundness of both edges of a conditional branch: the edge the concrete
    comparison selects is not discharged and its state concretizes the
    successor configuration. Holds for edges without hints. *)
Theorem transfer_branch_sound :
  forall (attrs : load_attrs) program regions before cond size offset executable
         (regs : regset) stack code_id count memory concrete',
    concretizes attrs regions before (TLS_State regs stack code_id count memory) ->
    ArithmeticHelpers.eq_constants_fit_i64 (facts before) ->
    order_constants_fit_i64 (facts before) ->
    branch_operands_defined (facts before) cond = true ->
    lowers_branch (register_name before) offset cond size executable ->
    static_operands_scalar regs executable ->
    instruction_step regions program executable
      (TLS_State regs stack code_id count memory) concrete' ->
    exists taken after,
      transfer_branch before cond size taken = Some (Some after) /\
      concretizes attrs regions after concrete' /\
      concrete' = TLS_State
        (nextinstr (if taken then regs # PC <- (Val.offset_ptr (regs PC) offset) else regs))
        stack code_id count memory.
Proof.
  intros attrs program regions before cond size offset executable regs stack code_id count
    memory concrete' CONCRETE FIT ORDER DEFINED LOWER SCALAR STEP.
  destruct CONCRETE as [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]].
  assert (EXEC : exists op r source,
    executable = Pjmpcmp (lower_cmp_op op) (lower_width size) r source offset /\
    cond_op cond = op /\ variable_value world (cond_dst cond) = regs r /\
    operand_value world cond = source_value regs source).
  { inversion LOWER; subst; unfold program_register in *.
    all: do 3 eexists; split; [reflexivity |];
      cbn [cond_op cond_dst operand_value cond_src source_value];
      repeat split; auto. }
  destruct EXEC as [op [r [source [EXECUTABLE [OP [LEFT RIGHT]]]]]]. subst executable.
  destruct (branch_step_outcome _ _ _ _ _ _ _ _ _ _ _ _ _ SCALAR STEP)
    as [taken [COMPARE AFTER]].
  assert (OUTCOME : branch_outcome world memory cond size taken).
  { unfold branch_outcome. now rewrite OP, LEFT, RIGHT. }
  destruct (edge_state_branch_sound _ _ _ _ _ _ FACTS FIT ORDER OUTCOME) as [post [EDGE POST]].
  exists taken, (AbstractMachineState post (register_name before)).
  unfold transfer_branch. rewrite DEFINED, EDGE.
  split; [reflexivity |]. split; [| exact AFTER].
  subst concrete'. exists world. split; [| auto].
  intros reg NOT_AUX. cbn [register_name]. rewrite nextinstr_ireg.
  destruct taken; [rewrite set_pc_ireg |]; exact (REGISTERS reg NOT_AUX).
Qed.

(** Program exit with an empty call stack: the state is unchanged and the
    returned [R0] is defined. Subprogram returns are out of scope. *)
Theorem transfer_return_sound :
  forall (attrs : load_attrs) program regions before (regs : regset) code_id count memory,
    concretizes attrs regions before (TLS_State regs [] code_id count memory) ->
    transfer_return before = true ->
    exists concrete',
      instruction_step regions program Pret (TLS_State regs [] code_id count memory) concrete' /\
      concretizes attrs regions before concrete' /\
      runtime_value (regs R0).
Proof.
  intros attrs program regions before regs code_id count memory CONCRETE RETURN.
  unfold transfer_return in RETURN. rewrite !andb_true_iff in RETURN.
  destruct RETURN as [[DEFINED _] _].
  exists (TLS_State (regs # PC <- Vnullptr) [] code_id count memory).
  split; [reflexivity |].
  destruct CONCRETE as [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]]. split.
  - exists world. split; [| auto]. intros reg NOT_AUX. rewrite set_pc_ireg.
    exact (REGISTERS reg NOT_AUX).
  - rewrite <- REGISTERS by discriminate. eapply ensure_defined_sound; eauto.
Qed.

