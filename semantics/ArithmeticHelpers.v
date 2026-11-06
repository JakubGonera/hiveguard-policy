From Coq Require Import Bool List ZArith Lia.
From compcert Require Import Integers Values Memory AST Zbits Coqlib.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.
From TrustNoBPF.Semantics Require Import AbstractDomain Concretization Transfer Common.

Import ListNotations.
Open Scope Z_scope.

Module AssignmentExpr.
  Inductive t := Const (value : Z) | VarOffset (name : var) (offset : Z).
End AssignmentExpr.

Scheme Equality for term.

(** Executable models of the internal Rust functions used by arithmetic.
    As in [AbstractDomain], integer fields use [Z]; correspondence with Rust
    presupposes that inputs fit their Rust field types. Casts and checked
    arithmetic below implement the corresponding Rust operations.
    Allocation failures and panics
    are outside this successful-transfer model. No helper soundness axioms
    are supplied. Definitions and proved properties are separated below. *)
Module ArithmeticHelpers.

  Definition unsigned64 (value : Z) := Int64.unsigned (Int64.repr value).
  Definition signed64 (value : Z) := Int64.signed (Int64.repr value).
  Definition checked_u64 (value : Z) : option Z :=
    if (0 <=? value) && (value <=? Int64.max_unsigned) then Some value else None.
  Definition to_i64 (value : Z) : option Z :=
    if (0 <=? value) && (value <=? Int64.max_signed) then Some value else None.

  Definition add_const (name : var) (offset : Z) : term :=
    if offset =? 0 then Var name else AddConst name offset.
  Definition ghost_add_const (name : ghost) (offset : Z) : term :=
    if offset =? 0 then Ghost name else GhostAddConst name offset.
  Definition as_affine (expression : term) : option (var * Z) :=
    match expression with Var name => Some (name, 0)
    | AddConst name offset => Some (name, offset) | _ => None end.
  Definition term_offset_for_var (expression : term) (name : var) : option Z :=
    match as_affine expression with
    | Some (found, offset) => if Nat.eqb found name then Some offset else None
    | None => None end.
  Definition add_const_to_term (expression : term) (offset : Z) : option term :=
    match expression with
    | Var name => Some (add_const name offset)
    | Ghost name => Some (ghost_add_const name offset)
    | Const value => option_map Const (i64_checked_add value offset)
    | AddConst name old => option_map (add_const name) (i64_checked_add old offset)
    | GhostAddConst name old => option_map (ghost_add_const name) (i64_checked_add old offset)
    | Sub _ _ => if offset =? 0 then Some expression else None
    end.

  Definition eq_const (fact : atom) : option (term * Z) :=
    match fact with Eq expression (Const value) | Eq (Const value) expression =>
      Some (expression, value) | _ => None end.
  Definition fact_bounds (expression : term) (signed : bool) (fact : atom) : option (Z * Z) :=
    match eq_const fact with
    | Some (found, value) => if term_beq found expression
        then let value := if signed then value else unsigned64 value in Some (value, value)
        else None
    | None => match fact with
        | AbstractValue found (URangeValue bounds) =>
            if term_beq found expression then
              if signed then
                if u_upper bounds <? Int64.half_modulus
                then Some (u_lower bounds, u_upper bounds)
                else if Int64.half_modulus <=? u_lower bounds
                     then Some (u64_as_i64 (u_lower bounds), u64_as_i64 (u_upper bounds))
                     else None
              else Some (u_lower bounds, u_upper bounds)
            else None
        | AbstractValue found (RangeValue bounds) =>
            if signed && term_beq found expression then Some (lower bounds, upper bounds) else None
        | _ => None
        end
    end.
  Definition tighten (available next : option (Z * Z)) : option (Z * Z) :=
    match available, next with
    | Some (lo, hi), Some (lo', hi') => Some (Z.max lo lo', Z.min hi hi')
    | None, _ => next | _, None => available
    end.
  (** [facts.rs::term_bounds], including intersection of all applicable facts. *)
  Definition term_bounds (state : abstract_state) (expression : term) (signed : bool) :=
    fold_left (fun bounds fact => tighten bounds (fact_bounds expression signed fact)) state
      (match expression with Const value => let value := if signed then value else unsigned64 value in
        Some (value, value) | _ => None end).
  (** Rust [transfer.rs::u32_bounds]. *)
  Definition u32_bounds (state : abstract_state) (name : var) : option (Z * Z) :=
    match term_bounds state (Var name) false with
    | Some (lo, hi) => if (0 <=? lo) && (hi <=? Int.max_unsigned) then Some (lo, hi) else None
    | None => None end.
  (** Rust [transfer.rs::fits_u32]. *)
  Definition fits_u32 (state : abstract_state) (name : var) : bool :=
    match u32_bounds state name with Some _ => true | None => false end.
  (** Rust [transfer.rs::op32_shift_exact]. *)
  Definition op32_shift_exact (state : abstract_state) (name : var) (offset : Z) : bool :=
    match u32_bounds state name with
    | Some (lo, hi) => (0 <=? lo + offset) && (hi + offset <=? Int.max_unsigned)
    | None => false end.
  (** Rust [transfer.rs::op32_binop_bounds]. *)
  Definition op32_binop_bounds (state : abstract_state) (lhs rhs : var) (op : ArithmeticOp.t) :=
    match u32_bounds state lhs, u32_bounds state rhs with
    | Some (lo, hi), Some (lo', hi') =>
        let bounds := match op with ArithmeticOp.Add => Some (lo + lo', hi + hi')
          | ArithmeticOp.Sub => Some (lo - hi', hi - lo') | _ => None end in
        match bounds with Some (lo, hi) =>
          if (0 <=? lo) && (hi <=? Int.max_unsigned) then
            match checked_u64 lo, checked_u64 hi with
            | Some lo, Some hi => Some (lo, hi) | _, _ => None end
          else None
        | None => None end
    | _, _ => None end.
  (** Rust [transfer.rs::and32_upper_bound]. *)
  Definition and32_upper_bound (state : abstract_state) (lhs : var) (src : SourceOperand.t) : Z :=
    let operand name := match u32_bounds state name with Some (_, hi) =>
      if (0 <=? hi) && (hi <=? Int.max_unsigned) then Some hi else None | None => None end in
    let rhs := match src with SourceOperand.Imm imm => Some (Int.unsigned imm)
      | SourceOperand.Value name => operand name end in
    match operand lhs, rhs with Some lo, Some hi => Z.min lo hi
    | Some only, None | None, Some only => only | None, None => Int.max_unsigned end.

  (** Rust [ptr_arith.rs::urange_fact]: the intersection of every unsigned range
      fact about [name], unless it is empty. *)
  Definition urange_fact (state : abstract_state) (name : var) : option urange :=
    match fold_left (fun held fact => match fact with
      | AbstractValue (Var found) (URangeValue bounds) =>
          if Nat.eqb found name then Some (match held with
            | Some previous => URange (Z.max (u_lower previous) (u_lower bounds))
                (Z.min (u_upper previous) (u_upper bounds))
            | None => bounds end)
          else held
      | _ => held end) state None with
    | Some bounds => if u_lower bounds <=? u_upper bounds then Some bounds else None
    | None => None end.
  (** Rust [ptr_arith.rs::congruence_fact]. *)
  Fixpoint congruence_fact (state : abstract_state) (name : var) : option congruence :=
    match state with [] => None | AbstractValue (Var found) (CongruenceValue class) :: rest =>
      if Nat.eqb found name then Some class else congruence_fact rest name
    | _ :: rest => congruence_fact rest name end.
  (** Rust [PtrState::shifted_end]. *)
  Definition shifted_end (ptr : ptr_state) (delta : Z) : option Z :=
    match ptr_end_min ptr with Some bound => i64_checked_sub bound delta | None => None end.
  Definition pointer_offsets (ptr : ptr_state) (lo hi stride delta : Z) : ptr_state :=
    PtrState (ptr_ty ptr) (ptr_nullability ptr) (ptr_flags ptr) lo hi (ptr_size ptr)
      (shifted_end ptr delta) stride (ptr_permission ptr) (ptr_ref_obj ptr).
  Definition nullable_displacement_allowed (ptr : ptr_state) (lo hi : Z) : bool :=
    match ptr_nullability ptr with MaybeNull => Region.probe_readable (ptr_ty ptr) ||
      ((lo =? 0) && (hi =? 0)) | _ => true end.
  (** BRANCH RUST CHANGE [PTR-STRIDE-SNAP], introduced in commit fcaccf9: Rust
      [ptr_arith.rs::derive_ptr_offset_add] now computes the differences in i128 before taking Euclidean remainders.
      Main's wrapping i64 differences can change the class for non-power-of-two
      moduli. For Rust-sized inputs, i128 differences are exact and each remainder
      fits i64; checked updates of the bounds remain unchanged. *)
  Definition derive_ptr_offset_add (ptr : ptr_state) (bounds : urange)
      (class : option congruence) : option ptr_state :=
    match to_i64 (u_lower bounds), to_i64 (u_upper bounds) with
    | Some lo, Some hi =>
        let stride := match class with Some class => modulus class | None => 1 end in
        let snapped := if 1 <? stride then
          match to_i64 stride with
          | Some m => let r := match class with Some class => residue class | None => 0 end in
              match i64_checked_add lo ((r - lo) mod m),
                    i64_checked_sub hi ((hi - r) mod m) with
              | Some lo, Some hi => if lo <=? hi then Some (lo, hi) else None | _, _ => None end
          | None => None end
          else Some (lo, hi) in
        match snapped with Some (lo, hi) =>
          if nullable_displacement_allowed ptr lo hi then
            match i64_checked_add (ptr_off_min ptr) lo, i64_checked_add (ptr_off_max ptr) hi with
            | Some low, Some high => Some (pointer_offsets ptr low high
                (if ptr_off_min ptr =? ptr_off_max ptr then Z.max stride 1
                 else Z.gcd (Z.max (ptr_align ptr) 1) (Z.max stride 1)) hi)
            | _, _ => None end
          else None
        | None => None end
    | _, _ => None end.
  (** Rust [ptr_arith.rs::derived_ptr_add_reg]. *)
  Definition derived_ptr_add_reg (state : abstract_state) (lhs rhs : var) : option ptr_state :=
    let pair := match find_pointer_fact state lhs, find_pointer_fact state rhs with
      | Some ptr, None => Some (ptr, rhs) | None, Some ptr => Some (ptr, lhs) | _, _ => None end in
    match pair with Some (ptr, scalar) => match urange_fact state scalar with
      | Some bounds => derive_ptr_offset_add ptr bounds (congruence_fact state scalar)
      | None => None end | None => None end.

  Fixpoint trailing_zeros (fuel : nat) (value : Z) : Z :=
    match fuel with O => 0 | S remaining =>
      if Z.odd value then 0 else 1 + trailing_zeros remaining (Z.shiftr value 1) end.
  (** Rust [ptr_arith.rs::pow2_stride]. *)
  Definition pow2_stride (op : ArithmeticOp.t) (imm : Z) : option Z :=
    let bits := match op with
      | ArithmeticOp.And | ArithmeticOp.Mul => Some (Z.min (trailing_zeros 64 (unsigned64 imm)) 63)
      | ArithmeticOp.Lsh => if (0 <=? imm) && (imm <? 64) then Some (Z.min imm 63) else None
      | _ => None end in
    match bits with Some bits => if 0 <? bits then Some (2 ^ bits) else None | None => None end.

  (** A copy cannot wrap. Otherwise the signed bounds on the input term must
      place every possible shifted value inside the signed 64-bit range. *)
  Definition signed_shift_no_wrap (state : abstract_state) (expression : term)
      (shift : Z) : bool :=
    (shift =? 0) || match term_bounds state expression true with
      | Some (lo, hi) => (Int64.min_signed <=? lo + shift) &&
                        (hi + shift <=? Int64.max_signed)
      | None => false
      end.

  (** BRANCH RUST CHANGE [CONGRUENCE-ADD], introduced in commit dfb9c20: mirrors
      the changed Rust [transfer.rs::shift_congruence]; main updated the residue
      with checked arithmetic and kept the modulus. A zero modulus is an exact
      value. For positive moduli, retain the full stride only for a copy or when
      signed bounds establish no wrap; otherwise retain its power-of-two part,
      i.e. gcd(modulus, 2^64). A unit modulus supplies no constraint and is
      dropped. Residue arithmetic is mathematical (Rust uses i128), then a
      congruent representative is chosen that fits the Rust i64 field. *)
  Definition shift_congruence (state : abstract_state) (expression : term)
      (class : congruence) (shift : Z) : option congruence :=
    let next := residue class + shift in
    if modulus class =? 0 then Some (Congruence 0 (signed64 next))
    else
      let m := if signed_shift_no_wrap state expression shift then modulus class
               else 2 ^ trailing_zeros 64 (modulus class) in
      if m =? 1 then None else
        let r := next mod m in
        Some (Congruence m (if Int64.max_signed <? r then r - m else r)).

  (** Rust [transfer.rs::shift_ptr]. *)
  Definition shift_ptr (ptr : ptr_state) (shift : Z) : option ptr_state :=
    if nullable_displacement_allowed ptr shift shift then
      match i64_checked_add (ptr_off_min ptr) shift, i64_checked_add (ptr_off_max ptr) shift with
      | Some lo, Some hi => Some (pointer_offsets ptr lo hi (ptr_align ptr) shift)
      | _, _ => None end
    else None.

  Definition pinned (state : abstract_state) (expression : term) : option Z :=
    match term_bounds state expression false with Some (lo, hi) =>
      if lo =? hi then checked_u64 lo else None | None => None end.
  (** Rust [transfer.rs::fold_alu_constants]. *)
  Definition fold_alu_constants (state : abstract_state) (op : ArithmeticOp.t)
      (lhs : var) (src : SourceOperand.t) : option Z :=
    let rhs_value := match src with SourceOperand.Imm imm => Some (unsigned64 (Int.signed imm))
      | SourceOperand.Value name => pinned state (Var name) end in
    match pinned state (Var lhs), rhs_value with Some a, Some b =>
      match op with
      | ArithmeticOp.And => Some (Z.land a b) | ArithmeticOp.Or => Some (Z.lor a b)
      | ArithmeticOp.Xor => Some (Z.lxor a b)
      | ArithmeticOp.Lsh => Some (unsigned64 (Z.shiftl a (Z.land b 63)))
      | ArithmeticOp.Rsh => Some (Z.shiftr a (Z.land b 63))
      | ArithmeticOp.Arsh => Some (unsigned64 (Z.shiftr (signed64 a) (Z.land b 63)))
      | ArithmeticOp.Mul => Some (unsigned64 (a * b)) | _ => None end
    | _, _ => None end.

  (** One candidate-selection step of Rust [identity.rs::representative]. Only
      equalities filed under [name] ([key::subject]) are scanned: with both
      sides affine, those whose left side is about [name]. *)
  Definition representative_step (name : var) (offset : Z) (best : var * Z)
      (fact : atom) : var * Z :=
    let candidate := match fact with Eq lhs rhs => match as_affine lhs, as_affine rhs with
      | Some (a, x), Some (b, y) =>
          if Nat.eqb a name then match i64_checked_sub y x with Some delta =>
            option_map (fun shifted => (b, shifted)) (i64_checked_add offset delta)
          | None => None end
          else None
      | _, _ => None end | _ => None end in
    match candidate with Some (name', offset') =>
      if (Nat.ltb name' (fst best)) || (Nat.eqb name' (fst best) && (offset' <? snd best))
      then (name', offset') else best | None => best end.

  (** [identity.rs::representative]: one scan, not transitive closure. *)
  Definition representative (state : abstract_state) (expression : term) : term :=
    match as_affine expression with Some (name, offset) =>
      let best := fold_left (representative_step name offset) state (name, offset) in
      add_const (fst best) (snd best)
    | None => expression end.

  (** Rust [transfer.rs::derive_value_state]: the value fact [fact] about [src]
      plus a constant gives [src + offset], when it survives the shift. *)
  Definition derive_value_state (state : abstract_state) (fact : atom) (src : var)
      (offset : Z) : option value_state :=
    match fact with
    | AbstractValue expression value =>
        match term_offset_for_var expression src with
        | Some old =>
            match i64_checked_sub offset old with
            | Some shift =>
                match value with
                | URangeValue bounds => match checked_u64 (u_lower bounds + shift),
                    checked_u64 (u_upper bounds + shift) with
                    | Some lo, Some hi => Some (URangeValue (URange lo hi)) | _, _ => None end
                | RangeValue bounds => match i64_checked_add (lower bounds) shift,
                    i64_checked_add (upper bounds) shift with
                    | Some lo, Some hi => Some (RangeValue (Range lo hi)) | _, _ => None end
                | CongruenceValue class =>
                    option_map CongruenceValue (shift_congruence state expression class shift)
                | Ptr ptr => option_map Ptr (shift_ptr ptr shift)
                | Scalar => Some Scalar
                | Unknown | Uninit => None
                end
            | None => None end
        | None => None end
    | _ => None end.

  (** The [VarOffset] arm of Rust [transfer.rs::apply_assignment]: only the
      source's value facts travel, folded into one per kind. *)
  Definition apply_assignment_var_offset (entails : value_state -> value_state -> bool)
      (state : abstract_state) (dst src : var) (offset : Z) : option abstract_state :=
    let original := Var src in
    let repr := representative state original in
    let identity := if negb (term_beq repr original) then
      match add_const_to_term repr offset with Some shifted =>
        if negb (term_mentions dst shifted) then [Eq (Var dst) shifted] else [] | None => [] end else [] in
    let derived := flat_map (fun fact => match derive_value_state state fact src offset with
      | Some value => [value] | None => [] end) state in
    let values := filter (fun value => match value with Unknown | Uninit => false | _ => true end)
      (fold entails derived) in
    Some (filter (fun fact => negb (atom_mentions dst fact)) state ++
      [Eq (Var dst) (add_const src offset); AbstractValue (Var dst) Unknown] ++ identity ++
      List.map (AbstractValue (Var dst)) values).

(** =========== Proved properties =========== *)

(** Affine equalities use wrapping addition, for both integers and pointers. *)
Lemma addl_zero_runtime : forall value,
  runtime_value value -> Val.addl value (Vlong Int64.zero) = value.
Proof.
  intros value RUNTIME. inversion RUNTIME; subst; cbn [Val.addl Archi.ptr64].
  - now rewrite Int64.add_zero.
  - change (Vptr b (Ptrofs.add ofs Ptrofs.zero) = Vptr b ofs).
    now rewrite Ptrofs.add_zero.
Qed.

Lemma add_const_eval : forall world name offset,
  runtime_value (variable_value world name) ->
  eval_term world (add_const name offset) =
    Val.addl (variable_value world name) (Vlong (Int64.repr offset)).
Proof.
  intros world name offset RUNTIME. unfold add_const.
  destruct (offset =? 0) eqn:ZERO; [|reflexivity].
  apply Z.eqb_eq in ZERO. subst offset. cbn [eval_term].
  symmetry. now apply addl_zero_runtime.
Qed.

Lemma affine_eval : forall world expression name offset,
  as_affine expression = Some (name, offset) ->
  runtime_value (variable_value world name) ->
  eval_term world expression =
    Val.addl (variable_value world name) (Vlong (Int64.repr offset)).
Proof.
  intros world expression name offset AFFINE RUNTIME.
  destruct expression; cbn [as_affine] in AFFINE; try discriminate;
    inversion AFFINE; subst; cbn [eval_term]; [|reflexivity].
  symmetry. now apply addl_zero_runtime.
Qed.

Lemma affine_runtime : forall world expression name offset,
  as_affine expression = Some (name, offset) ->
  runtime_value (eval_term world expression) ->
  runtime_value (variable_value world name).
Proof.
  intros world expression name offset AFFINE RUNTIME.
  destruct expression; cbn [as_affine] in AFFINE; try discriminate;
    inversion AFFINE; subst; cbn [eval_term] in RUNTIME; [exact RUNTIME |].
  destruct (variable_value world name); cbn [Val.addl Archi.ptr64] in RUNTIME;
    inversion RUNTIME; constructor.
Qed.

Lemma repr_add : forall x y,
  Int64.add (Int64.repr x) (Int64.repr y) = Int64.repr (x + y).
Proof.
  intros. unfold Int64.add. apply Int64.eqm_samerepr.
  apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma affine_equality_rebase : forall world lhs rhs left right x y,
  as_affine lhs = Some (left, x) -> as_affine rhs = Some (right, y) ->
  runtime_value (eval_term world lhs) -> eval_term world lhs = eval_term world rhs ->
  variable_value world left =
    Val.addl (variable_value world right) (Vlong (Int64.repr (y - x))).
Proof.
  intros world lhs rhs left right x y LEFT RIGHT RUNTIME EQUAL.
  pose proof (affine_runtime _ _ _ _ LEFT RUNTIME) as LEFT_RUNTIME.
  assert (RIGHT_RUNTIME : runtime_value (variable_value world right)).
  { eapply affine_runtime; [exact RIGHT |]. now rewrite <- EQUAL. }
  rewrite (affine_eval _ _ _ _ LEFT LEFT_RUNTIME),
    (affine_eval _ _ _ _ RIGHT RIGHT_RUNTIME) in EQUAL.
  replace (Int64.repr (y - x)) with (Int64.add (Int64.repr y) (Int64.repr (-x)))
    by (rewrite repr_add; f_equal; lia).
  change (variable_value world left = Val.addl (variable_value world right)
    (Val.addl (Vlong (Int64.repr y)) (Vlong (Int64.repr (-x))))).
  rewrite <- Val.addl_assoc, <- EQUAL, Val.addl_assoc.
  cbn [Val.addl]. rewrite repr_add.
  replace (x + -x) with 0 by lia. now rewrite addl_zero_runtime.
Qed.

(** Copying a guard changes its variable name, not the test on its value.
    Rust normalizes the constant modulo 2^64; CompCert already does that when
    constructing the comparison operand. *)
Lemma addl_runtime_left : forall value offset,
  runtime_value (Val.addl value (Vlong (Int64.repr offset))) -> runtime_value value.
Proof.
  intros value offset RUNTIME. destruct value;
    cbn [Val.addl Archi.ptr64] in RUNTIME; inversion RUNTIME; constructor.
Qed.

Lemma add_const_to_term_eval : forall world expression offset shifted,
  runtime_value (eval_term world expression) ->
  add_const_to_term expression offset = Some shifted ->
  eval_term world shifted =
    Val.addl (eval_term world expression) (Vlong (Int64.repr offset)).
Proof.
  intros world expression offset shifted RUNTIME SHIFT.
  destruct expression as [name | ghost | constant | name old | ghost old | left right];
    cbn [add_const_to_term] in SHIFT.
  - inversion SHIFT; subst shifted. apply add_const_eval. exact RUNTIME.
  - inversion SHIFT; subst shifted. unfold ghost_add_const.
    destruct (offset =? 0) eqn:ZERO; [|reflexivity].
    apply Z.eqb_eq in ZERO. subst offset. symmetry. now apply addl_zero_runtime.
  - destruct (i64_checked_add constant offset) as [sum|] eqn:SUM; try discriminate.
    inversion SHIFT; subst shifted. apply i64_checked_add_value in SUM. subst sum.
    cbn [eval_term Val.addl]. now rewrite repr_add.
  - destruct (i64_checked_add old offset) as [sum|] eqn:SUM; try discriminate.
    inversion SHIFT; subst shifted. apply i64_checked_add_value in SUM. subst sum.
    rewrite add_const_eval by (eapply addl_runtime_left; exact RUNTIME).
    cbn [eval_term]. rewrite Val.addl_assoc. cbn [Val.addl]. now rewrite repr_add.
  - destruct (i64_checked_add old offset) as [sum|] eqn:SUM; try discriminate.
    inversion SHIFT; subst shifted. apply i64_checked_add_value in SUM. subst sum.
    unfold ghost_add_const. destruct (old + offset =? 0) eqn:ZERO.
    + apply Z.eqb_eq in ZERO. cbn [eval_term]. rewrite Val.addl_assoc.
      cbn [Val.addl]. rewrite repr_add, ZERO. symmetry.
      apply addl_zero_runtime. eapply addl_runtime_left. exact RUNTIME.
    + cbn [eval_term]. rewrite Val.addl_assoc. cbn [Val.addl]. now rewrite repr_add.
  - destruct (offset =? 0) eqn:ZERO; try discriminate.
    inversion SHIFT; subst shifted. apply Z.eqb_eq in ZERO. subst offset.
    symmetry. now apply addl_zero_runtime.
Qed.

Lemma term_offset_affine : forall expression src offset,
  term_offset_for_var expression src = Some offset ->
  as_affine expression = Some (src, offset).
Proof.
  intros expression src offset FOUND. unfold term_offset_for_var in FOUND.
  destruct (as_affine expression) as [[name old]|] eqn:AFFINE; try discriminate.
  destruct (Nat.eqb name src) eqn:NAME; try discriminate.
  apply Nat.eqb_eq in NAME. inversion FOUND; subst. reflexivity.
Qed.

Lemma runtime_addl_offset : forall value offset,
  runtime_value value -> runtime_value (Val.addl value (Vlong (Int64.repr offset))).
Proof.
  intros value offset RUNTIME. inversion RUNTIME; subst; cbn [Val.addl Archi.ptr64]; constructor.
Qed.

Lemma repr_add32 : forall x y,
  Int.add (Int.repr x) (Int.repr y) = Int.repr (x + y).
Proof.
  intros. unfold Int.add. apply Int.eqm_samerepr.
  apply Int.eqm_add; apply Int.eqm_sym, Int.eqm_unsigned_repr.
Qed.

(** CompCert compares a pointer only with zero, so a rewritten guard on a
    pointer can hold only when it is [!= 0] and the offset is zero. *)
(** Rust's representative selection adds only an equality already implied by
    the pre-state. It remains sound when either side denotes a pointer. *)
Lemma representative_var_sound : forall world memory state src,
  Forall (atom_holds world memory) state ->
  eval_term world (representative state (Var src)) = variable_value world src.
Proof.
  intros world memory state src FACTS.
  set (select := representative_step src 0).
  assert (STEP : forall best fact,
    In fact state ->
    eval_term world (add_const (fst best) (snd best)) = variable_value world src ->
    eval_term world (add_const (fst (select best fact)) (snd (select best fact))) =
      variable_value world src).
  { intros best fact IN KEPT.
    pose proof ((proj1 (Forall_forall _ _) FACTS) fact IN) as HOLDS.
    unfold select, representative_step. destruct fact; cbn beta iota zeta; try exact KEPT.
    cbn [atom_holds] in HOLDS. destruct HOLDS as [VALID EQUAL].
    destruct (as_affine lhs) as [[a x]|] eqn:LEFT; [|exact KEPT].
    destruct (as_affine rhs) as [[b y]|] eqn:RIGHT; [|exact KEPT].
    destruct (Nat.eqb a src) eqn:A.
    - apply Nat.eqb_eq in A. subst a.
      destruct (i64_checked_sub y x) as [delta|] eqn:DELTA; [|exact KEPT].
      destruct (i64_checked_add 0 delta) as [shift|] eqn:SHIFT; [|exact KEPT].
      cbn [option_map].
      destruct (_ || _); [|exact KEPT]. cbn [fst snd].
      apply i64_checked_add_value in SHIFT.
      unfold i64_checked_sub in DELTA. apply i64_checked_add_value in DELTA.
      assert (BRUNTIME : runtime_value (variable_value world b)).
      { eapply affine_runtime; [exact RIGHT |]. now rewrite <- EQUAL. }
      rewrite add_const_eval by exact BRUNTIME. replace shift with (y - x) by lia.
      symmetry. eapply affine_equality_rebase; eauto.
    - exact KEPT. }
  assert (FOLD : forall items best,
    (forall fact, In fact items -> In fact state) ->
    eval_term world (add_const (fst best) (snd best)) = variable_value world src ->
    eval_term world (add_const (fst (fold_left select items best))
      (snd (fold_left select items best))) = variable_value world src).
  { induction items as [|fact rest IH]; intros best IN KEPT; [exact KEPT |].
    cbn [fold_left]. apply IH.
    - intros. apply IN. now right.
    - apply STEP; [apply IN; now left |exact KEPT]. }
  unfold representative. cbn [as_affine].
  change (eval_term world (add_const (fst (fold_left select state (src, 0)))
    (snd (fold_left select state (src, 0)))) = variable_value world src).
  apply FOLD; [auto |reflexivity].
Qed.

Lemma eq_const_holds : forall world memory fact expression constant,
  atom_holds world memory fact -> eq_const fact = Some (expression, constant) ->
  eval_term world expression = Vlong (Int64.repr constant).
Proof.
  intros world memory fact expression constant HOLDS FOUND.
  destruct fact; cbn [eq_const] in FOUND; try discriminate.
  destruct lhs, rhs; cbn [eq_const] in FOUND; try discriminate;
    inversion FOUND; subst; cbn [atom_holds eval_term] in HOLDS |- *;
    intuition congruence.
Qed.

Lemma fact_bounds_unsigned_sound : forall world memory expression fact lo hi,
  atom_holds world memory fact ->
  fact_bounds expression false fact = Some (lo, hi) ->
  exists n, eval_term world expression = Vlong n /\ lo <= Int64.unsigned n <= hi.
Proof.
  intros world memory expression fact lo hi HOLDS BOUNDS.
  unfold fact_bounds in BOUNDS.
  destruct (eq_const fact) as [[found constant]|] eqn:EQ.
  - destruct (term_beq found expression) eqn:TERM; try discriminate.
    apply internal_term_dec_bl in TERM. subst found.
    inversion BOUNDS; subst lo hi. exists (Int64.repr constant). split.
    + eapply eq_const_holds; eauto.
    + unfold unsigned64. lia.
  - destruct fact; try discriminate.
    destruct value; cbn in BOUNDS; try discriminate.
    destruct (term_beq term expression) eqn:TERM; try discriminate.
    apply internal_term_dec_bl in TERM. subst term.
    inversion BOUNDS; subst lo hi.
    cbn [atom_holds value_holds] in HOLDS.
    destruct (eval_term world expression) eqn:VALUE; try contradiction.
    eexists. split; [reflexivity |exact HOLDS].
Qed.

Lemma tighten_unsigned_sound : forall world expression bounds next,
  (match bounds with Some (lo, hi) => exists n,
    eval_term world expression = Vlong n /\ lo <= Int64.unsigned n <= hi | None => True end) ->
  (match next with Some (lo, hi) => exists n,
    eval_term world expression = Vlong n /\ lo <= Int64.unsigned n <= hi | None => True end) ->
  match tighten bounds next with Some (lo, hi) => exists n,
    eval_term world expression = Vlong n /\ lo <= Int64.unsigned n <= hi | None => True end.
Proof.
  intros world expression [[lo hi]|] [[lo' hi']|]; cbn [tighten]; auto.
  intros [n [VALUE BOUNDS]] [n' [VALUE' BOUNDS']].
  rewrite VALUE in VALUE'. inversion VALUE'; subst n'.
  exists n. split; [exact VALUE |].
  split; [apply Z.max_lub |apply Z.min_glb]; lia.
Qed.

Lemma term_bounds_unsigned_sound : forall world memory state expression lo hi,
  Forall (atom_holds world memory) state ->
  term_bounds state expression false = Some (lo, hi) ->
  exists n, eval_term world expression = Vlong n /\ lo <= Int64.unsigned n <= hi.
Proof.
  intros world memory state expression lo hi FACTS.
  unfold term_bounds.
  assert (INITIAL : match expression with Const constant =>
    exists n, eval_term world expression = Vlong n /\
      unsigned64 constant <= Int64.unsigned n <= unsigned64 constant | _ => True end).
  { destruct expression as [name|name|constant|name offset|name offset|lhs rhs]; cbn; auto.
    exists (Int64.repr constant). unfold unsigned64. split; [reflexivity |lia]. }
  generalize dependent hi. generalize dependent lo.
  remember (match expression with Const constant =>
    Some (unsigned64 constant, unsigned64 constant) | _ => None end) as bounds.
  assert (VALID : match bounds with Some (lo, hi) => exists n,
    eval_term world expression = Vlong n /\ lo <= Int64.unsigned n <= hi | None => True end).
  { subst bounds. destruct expression; exact INITIAL. }
  clear INITIAL Heqbounds. revert bounds VALID.
  induction FACTS as [|fact state HOLDS FACTS IH]; intros bounds VALID lo hi BOUNDS.
  - cbn in BOUNDS. subst bounds. exact VALID.
  - cbn in BOUNDS. eapply IH; [|exact BOUNDS].
    apply tighten_unsigned_sound; [exact VALID |].
    destruct (fact_bounds expression false fact) as [[lower upper]|] eqn:FOUND; [|exact I].
    eapply fact_bounds_unsigned_sound; eauto.
Qed.

Lemma u32_bounds_sound : forall world memory state name lo hi,
  Forall (atom_holds world memory) state -> u32_bounds state name = Some (lo, hi) ->
  exists n, variable_value world name = Vlong n /\
    lo <= Int64.unsigned n <= hi /\ 0 <= lo /\ hi <= Int.max_unsigned.
Proof.
  intros world memory state name lo hi FACTS BOUNDS. unfold u32_bounds in BOUNDS.
  destruct (term_bounds state (Var name) false) as [[lower upper]|] eqn:FOUND;
    try discriminate.
  destruct ((0 <=? lower) && (upper <=? Int.max_unsigned)) eqn:FITS; try discriminate.
  inversion BOUNDS; subst lower upper. apply andb_true_iff in FITS.
  destruct FITS as [LOW HIGH]. apply Z.leb_le in LOW, HIGH.
  destruct (term_bounds_unsigned_sound world memory state (Var name) lo hi FACTS FOUND)
    as [n [VALUE RANGE]]. exists n. cbn [eval_term] in VALUE. auto.
Qed.

Lemma op32_shift_exact_sound : forall world memory state name offset,
  Forall (atom_holds world memory) state -> op32_shift_exact state name offset = true ->
  exists n, variable_value world name = Vlong n /\
    0 <= Int64.unsigned n <= Int.max_unsigned /\
    0 <= Int64.unsigned n + offset <= Int.max_unsigned.
Proof.
  intros world memory state name offset FACTS EXACT. unfold op32_shift_exact in EXACT.
  destruct (u32_bounds state name) as [[lo hi]|] eqn:BOUNDS; try discriminate.
  apply andb_true_iff in EXACT. destruct EXACT as [LOW HIGH].
  apply Z.leb_le in LOW, HIGH.
  destruct (u32_bounds_sound world memory state name lo hi FACTS BOUNDS)
    as [n [VALUE [RANGE [MIN MAX]]]]. exists n. repeat split; auto; lia.
Qed.

Lemma op32_binop_bounds_sound : forall world memory state lhs rhs op lo hi,
  Forall (atom_holds world memory) state ->
  op32_binop_bounds state lhs rhs op = Some (lo, hi) ->
  exists a b, variable_value world lhs = Vlong a /\
    variable_value world rhs = Vlong b /\
    (op = ArithmeticOp.Add \/ op = ArithmeticOp.Sub) /\
    0 <= Int64.unsigned a <= Int.max_unsigned /\
    0 <= Int64.unsigned b <= Int.max_unsigned /\
    lo <= (match op with ArithmeticOp.Sub => Int64.unsigned a - Int64.unsigned b
                        | _ => Int64.unsigned a + Int64.unsigned b end) <= hi /\
    0 <= lo /\ hi <= Int.max_unsigned.
Proof.
  intros world memory state lhs rhs op lo hi FACTS BOUNDS.
  unfold op32_binop_bounds in BOUNDS.
  destruct (u32_bounds state lhs) as [[ll lh]|] eqn:LEFT; try discriminate.
  destruct (u32_bounds state rhs) as [[rl rh]|] eqn:RIGHT; try discriminate.
  destruct (u32_bounds_sound world memory state lhs ll lh FACTS LEFT)
    as [a [AVALUE [ARANGE [AMIN AMAX]]]].
  destruct (u32_bounds_sound world memory state rhs rl rh FACTS RIGHT)
    as [b [BVALUE [BRANGE [BMIN BMAX]]]].
  destruct op; cbn in BOUNDS; try discriminate.
  all: match type of BOUNDS with context [if ?test then _ else _] =>
    destruct test eqn:FITS; try discriminate end.
  all: unfold checked_u64 in BOUNDS.
  all: repeat match type of BOUNDS with context [if ?test then _ else _] =>
    destruct test eqn:?; try discriminate end.
  all: inversion BOUNDS; subst lo hi; apply andb_true_iff in FITS;
    destruct FITS as [LOW HIGH]; apply Z.leb_le in LOW, HIGH.
  all: exists a, b; cbn -[Int.max_unsigned]; repeat split; auto; lia.
Qed.

Lemma pinned_sound : forall world memory state expression value,
  Forall (atom_holds world memory) state -> pinned state expression = Some value ->
  exists n, eval_term world expression = Vlong n /\ Int64.unsigned n = value.
Proof.
  intros world memory state expression value FACTS PINNED. unfold pinned in PINNED.
  destruct (term_bounds state expression false) as [[lo hi]|] eqn:BOUNDS; try discriminate.
  destruct (lo =? hi) eqn:SAME; try discriminate. apply Z.eqb_eq in SAME. subst hi.
  unfold checked_u64 in PINNED.
  destruct ((0 <=? lo) && (lo <=? Int64.max_unsigned)); try discriminate.
  inversion PINNED; subst value.
  destruct (term_bounds_unsigned_sound world memory state expression lo lo FACTS BOUNDS)
    as [n [VALUE RANGE]]. exists n. split; [exact VALUE |lia].
Qed.

(** Rust's constant fields are i64. This is a representation condition, not
    an extra semantic constraint on register values. *)
Definition eq_constants_fit_i64 (state : abstract_state) : Prop :=
  forall fact expression constant,
    In fact state -> eq_const fact = Some (expression, constant) ->
    Int64.min_signed <= constant <= Int64.max_signed.

Lemma fact_bounds_signed_sound : forall world memory expression fact lo hi,
  (forall found constant, eq_const fact = Some (found, constant) ->
    Int64.min_signed <= constant <= Int64.max_signed) ->
  atom_holds world memory fact -> fact_bounds expression true fact = Some (lo, hi) ->
  exists n, eval_term world expression = Vlong n /\ lo <= Int64.signed n <= hi.
Proof.
  intros world memory expression fact lo hi CONSTANTS HOLDS BOUNDS.
  unfold fact_bounds in BOUNDS.
  destruct (eq_const fact) as [[found constant]|] eqn:EQ.
  - destruct (term_beq found expression) eqn:TERM; try discriminate.
    apply internal_term_dec_bl in TERM. subst found.
    inversion BOUNDS; subst lo hi. exists (Int64.repr constant). split.
    + eapply eq_const_holds; eauto.
    + rewrite Int64.signed_repr by (eapply CONSTANTS; eauto). lia.
  - destruct fact; try discriminate. destruct value;
      cbn -[term_beq Z.ltb Z.leb Int64.half_modulus] in BOUNDS; try discriminate.
    all: destruct (term_beq term expression) eqn:TERM; try discriminate;
      apply internal_term_dec_bl in TERM; subst term;
      cbn [atom_holds value_holds] in HOLDS;
      destruct (eval_term world expression) eqn:VALUE; try contradiction.
    + destruct (u_upper bounds <? Int64.half_modulus) eqn:POSITIVE.
      * inversion BOUNDS; subst lo hi. apply Z.ltb_lt in POSITIVE.
        exists i. split; [reflexivity |]. unfold Int64.signed.
        destruct (zlt (Int64.unsigned i) Int64.half_modulus); lia.
      * destruct (Int64.half_modulus <=? u_lower bounds) eqn:NEGATIVE; try discriminate.
        inversion BOUNDS; subst lo hi. apply Z.leb_le in NEGATIVE.
        exists i. split; [reflexivity |]. unfold u64_as_i64, Int64.signed.
        change Int64.half_modulus with 9223372036854775808 in *.
        change Int64.modulus with 18446744073709551616.
        destruct (u_lower bounds <? 9223372036854775808) eqn:LOW;
          destruct (u_upper bounds <? 9223372036854775808) eqn:HIGH;
          destruct (zlt (Int64.unsigned i) 9223372036854775808);
          apply Z.ltb_lt in LOW || apply Z.ltb_ge in LOW;
          apply Z.ltb_lt in HIGH || apply Z.ltb_ge in HIGH; lia.
    + inversion BOUNDS; subst lo hi. eexists; split; [reflexivity |exact HOLDS].
Qed.

Lemma term_bounds_signed_sound : forall world memory state expression lo hi,
  Forall (atom_holds world memory) state -> eq_constants_fit_i64 state ->
  (forall constant, expression = Const constant ->
    Int64.min_signed <= constant <= Int64.max_signed) ->
  term_bounds state expression true = Some (lo, hi) ->
  exists n, eval_term world expression = Vlong n /\ lo <= Int64.signed n <= hi.
Proof.
  intros world memory state expression lo hi FACTS CONSTANTS LITERAL.
  unfold term_bounds.
  assert (INITIAL : match expression with Const constant => exists n,
    eval_term world expression = Vlong n /\ constant <= Int64.signed n <= constant
    | _ => True end).
  { destruct expression as [name|name|constant|name offset|name offset|lhs rhs]; cbn; auto.
    exists (Int64.repr constant). split; [reflexivity |].
    rewrite Int64.signed_repr by (apply LITERAL; reflexivity). lia. }
  generalize dependent hi. generalize dependent lo.
  remember (match expression with Const constant => Some (constant, constant) | _ => None end) as bounds.
  assert (VALID : match bounds with Some (lo, hi) => exists n,
    eval_term world expression = Vlong n /\ lo <= Int64.signed n <= hi | None => True end).
  { subst bounds. destruct expression; exact INITIAL. }
  clear INITIAL Heqbounds. revert bounds VALID CONSTANTS.
  induction FACTS as [|fact state HOLDS FACTS IH]; intros bounds VALID CONSTANTS lo hi BOUNDS.
  - cbn in BOUNDS. subst bounds. exact VALID.
  - cbn in BOUNDS. eapply IH; [| |exact BOUNDS].
    + destruct bounds as [[lower upper]|], (fact_bounds expression true fact)
        as [[lower' upper']|] eqn:FOUND; cbn [tighten]; try exact VALID.
      all: destruct (fact_bounds_signed_sound world memory expression fact lower' upper'
        (fun found constant EQ => CONSTANTS fact found constant (or_introl eq_refl) EQ)
        HOLDS FOUND) as [n [VALUE RANGE]].
      * destruct VALID as [n' [VALUE' RANGE']]. rewrite VALUE in VALUE'. inversion VALUE'; subst n'.
        exists n. split; [exact VALUE |]. split; [apply Z.max_lub |apply Z.min_glb]; lia.
      * exists n. auto.
    + intros item found constant IN EQ. eapply CONSTANTS; [right; exact IN |exact EQ].
Qed.

Lemma trailing_zeros_divides : forall fuel value,
  0 <= trailing_zeros fuel value <= Z.of_nat fuel /\
  (2 ^ trailing_zeros fuel value | value).
Proof.
  induction fuel as [|fuel IH]; intros value; cbn [trailing_zeros].
  - split; [lia |exists value; ring].
  - destruct (Z.odd value) eqn:ODD.
    + split; [lia |exists value; ring].
    + destruct (IH (Z.shiftr value 1)) as [BOUNDS [k DIVIDES]].
      split; [lia |]. rewrite Z.pow_add_r by lia. exists k.
      pose proof (Z.div2_odd value) as EVEN. rewrite ODD, Z.div2_spec in EVEN.
      cbn [Z.b2z] in EVEN. rewrite DIVIDES in EVEN.
      change (value = k * (2 * 2 ^ trailing_zeros fuel (Z.shiftr value 1))). nia.
Qed.

Lemma wrapping_stride_divides : forall modulus,
  (2 ^ trailing_zeros 64 modulus | modulus) /\
  (2 ^ trailing_zeros 64 modulus | Int64.modulus).
Proof.
  intros modulus. destruct (trailing_zeros_divides 64 modulus) as [BOUNDS DIVIDES].
  split; [exact DIVIDES |]. exists (2 ^ (64 - trailing_zeros 64 modulus)).
  change Int64.modulus with (2 ^ 64).
  rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma signed64_mod_divisor : forall value m,
  0 < m -> (m | Int64.modulus) -> signed64 value mod m = value mod m.
Proof.
  intros value m POS DIVIDES. apply eqmod_mod_eq; [lia |].
  eapply eqmod_divides; [|exact DIVIDES].
  eapply Int64.eqm_trans; [apply Int64.eqm_signed_unsigned |].
  apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma shift_congruence_holds :
  forall world memory state expression class src old shift n result,
    Forall (atom_holds world memory) state -> eq_constants_fit_i64 state ->
    term_offset_for_var expression src = Some old ->
    eval_term world expression = Vlong n ->
    value_holds world memory (CongruenceValue class) (Vlong n) ->
    shift_congruence state expression class shift = Some result ->
    value_holds world memory (CongruenceValue result)
      (Vlong (Int64.repr (Int64.signed n + shift))).
Proof.
  intros world memory state expression class src old shift n result
    FACTS CONSTANTS OFFSET VALUE HOLDS DERIVED.
  unfold shift_congruence in DERIVED.
  cbn [value_holds] in HOLDS. destruct (modulus class =? 0) eqn:EXACT.
  - inversion DERIVED; subst result. cbn [value_holds modulus residue].
    unfold signed64. rewrite HOLDS. reflexivity.
  - destruct HOLDS as [POS CLASS].
    set (m := if signed_shift_no_wrap state expression shift then modulus class
      else 2 ^ trailing_zeros 64 (modulus class)) in *.
    destruct (m =? 1) eqn:UNIT; try discriminate.
    inversion DERIVED; subst result; clear DERIVED.
    assert (MPOS : 0 < m).
    { unfold m. destruct (signed_shift_no_wrap state expression shift); [exact POS |].
      apply Z.pow_pos_nonneg; [lia |pose proof (trailing_zeros_divides 64 (modulus class)); lia]. }
    assert (SHIFTED : signed64 (Int64.signed n + shift) mod m = (residue class + shift) mod m).
    { unfold m. destruct (signed_shift_no_wrap state expression shift) eqn:NO_WRAP.
      - assert (BOUNDS : Int64.min_signed <= Int64.signed n + shift <= Int64.max_signed).
        { unfold signed_shift_no_wrap in NO_WRAP. apply orb_true_iff in NO_WRAP as [ZERO |BOUNDS].
          - apply Z.eqb_eq in ZERO. rewrite ZERO, Z.add_0_r. apply Int64.signed_range.
          - destruct (term_bounds state expression true) as [[lo hi]|] eqn:FOUND; try discriminate.
            apply andb_true_iff in BOUNDS as [LOW HIGH]. apply Z.leb_le in LOW, HIGH.
            assert (LITERAL : forall constant, expression = Const constant ->
              Int64.min_signed <= constant <= Int64.max_signed).
            { intros constant E. subst expression. discriminate OFFSET. }
            destruct (term_bounds_signed_sound world memory state expression lo hi
              FACTS CONSTANTS LITERAL FOUND) as [n' [VALUE' RANGE]].
            rewrite VALUE in VALUE'. inversion VALUE'; subst n'. lia. }
        unfold signed64. rewrite Int64.signed_repr by exact BOUNDS.
        rewrite (Z.add_mod (Int64.signed n)), (Z.add_mod (residue class)) by lia.
        now rewrite CLASS.
      - destruct (wrapping_stride_divides (modulus class)) as [OLD WORD].
        change (0 < 2 ^ trailing_zeros 64 (modulus class)) in MPOS.
        rewrite signed64_mod_divisor by assumption.
        assert (WEAK : Int64.signed n mod (2 ^ trailing_zeros 64 (modulus class)) =
          residue class mod (2 ^ trailing_zeros 64 (modulus class))).
        { apply eqmod_mod_eq; [lia |].
          eapply eqmod_divides; [|exact OLD].
          exists (Int64.signed n / modulus class - residue class / modulus class).
          pose proof (Z.div_mod (Int64.signed n) (modulus class) ltac:(lia)).
          pose proof (Z.div_mod (residue class) (modulus class) ltac:(lia)). nia. }
        rewrite (Z.add_mod (Int64.signed n)), (Z.add_mod (residue class)) by lia.
        now rewrite WEAK. }
    cbn [value_holds modulus residue].
    assert (NONZERO : m =? 0 = false) by (apply Z.eqb_neq; lia).
    rewrite NONZERO. split; [exact MPOS |].
    change (signed64 (Int64.signed n + shift) mod m =
      (if Int64.max_signed <? (residue class + shift) mod m
       then (residue class + shift) mod m - m else (residue class + shift) mod m) mod m).
    rewrite SHIFTED. destruct (Int64.max_signed <? (residue class + shift) mod m).
    + replace ((residue class + shift) mod m - m) with
        ((residue class + shift) mod m + (-1) * m) by ring.
      rewrite Z.mod_add, Z.mod_mod by lia. reflexivity.
    + rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma checked_u64_bounds : forall value checked,
  checked_u64 value = Some checked ->
  checked = value /\ 0 <= value <= Int64.max_unsigned.
Proof.
  intros value checked CHECK. unfold checked_u64 in CHECK.
  destruct ((0 <=? value) && (value <=? Int64.max_unsigned)) eqn:BOUNDS;
    try discriminate. inversion CHECK; subst checked.
  apply andb_true_iff in BOUNDS as [LOW HIGH]. apply Z.leb_le in LOW, HIGH. auto.
Qed.

Lemma shift_urange_holds : forall world memory bounds shift lo hi n,
  value_holds world memory (URangeValue bounds) (Vlong n) ->
  checked_u64 (u_lower bounds + shift) = Some lo ->
  checked_u64 (u_upper bounds + shift) = Some hi ->
  value_holds world memory (URangeValue (URange lo hi))
    (Vlong (Int64.repr (Int64.signed n + shift))).
Proof.
  intros world memory bounds shift lo hi n RANGE LOW HIGH.
  destruct (checked_u64_bounds _ _ LOW) as [LO LBOUND].
  destruct (checked_u64_bounds _ _ HIGH) as [HI HBOUND].
  cbn [value_holds u_lower u_upper] in *.
  assert (REPR : Int64.repr (Int64.signed n + shift) = Int64.repr (Int64.unsigned n + shift)).
  { apply Int64.eqm_samerepr. apply Int64.eqm_add;
      [apply Int64.eqm_signed_unsigned | apply Int64.eqm_refl]. }
  rewrite REPR, Int64.unsigned_repr by lia. lia.
Qed.

Lemma shift_srange_holds : forall world memory bounds shift lo hi n,
  value_holds world memory (RangeValue bounds) (Vlong n) ->
  i64_checked_add (lower bounds) shift = Some lo ->
  i64_checked_add (upper bounds) shift = Some hi ->
  value_holds world memory (RangeValue (Range lo hi))
    (Vlong (Int64.repr (Int64.signed n + shift))).
Proof.
  intros world memory bounds shift lo hi n RANGE LOW HIGH.
  destruct (checked_i64_bounds _ _ _ LOW) as [LO LBOUND].
  destruct (checked_i64_bounds _ _ _ HIGH) as [HI HBOUND].
  cbn [value_holds lower upper] in *. rewrite Int64.signed_repr by lia. lia.
Qed.

Lemma add_repr_signed : forall n k,
  Int64.add n (Int64.repr k) = Int64.repr (Int64.signed n + k).
Proof.
  intros n k. unfold Int64.add. apply Int64.eqm_samerepr. apply Int64.eqm_add.
  - apply Int64.eqm_sym, Int64.eqm_signed_unsigned.
  - apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma shifted_end_well_formed : forall ptr delta,
  match shifted_end ptr delta with
  | Some bound => Int64.min_signed <= bound <= Int64.max_signed
  | None => True end.
Proof.
  intros ptr delta. unfold shifted_end.
  destruct (ptr_end_min ptr) as [bound|]; [|exact I].
  unfold i64_checked_sub.
  destruct (i64_checked_add bound (-delta)) as [result|] eqn:CHECK; [|exact I].
  exact (proj2 (checked_i64_bounds _ _ _ CHECK)).
Qed.

Lemma pointer_offsets_fields_well_formed : forall ptr delta lo hi,
  pointer_fields_well_formed ptr ->
  i64_checked_add (ptr_off_min ptr) delta = Some lo ->
  i64_checked_add (ptr_off_max ptr) delta = Some hi ->
  pointer_fields_well_formed (pointer_offsets ptr lo hi (ptr_align ptr) delta).
Proof.
  intros ptr delta lo hi [_ [_ [SIZE [ALIGN [FLAGS _]]]]] LOW HIGH.
  destruct (checked_i64_bounds _ _ _ LOW) as [_ L].
  destruct (checked_i64_bounds _ _ _ HIGH) as [_ H].
  unfold pointer_fields_well_formed, pointer_offsets.
  cbn [ptr_off_min ptr_off_max ptr_size ptr_align ptr_flags ptr_end_min].
  split; [exact L |]. split; [exact H |]. split; [exact SIZE |].
  split; [exact ALIGN |]. split; [exact FLAGS |apply shifted_end_well_formed].
Qed.

Lemma pointer_offset_shift : forall ptr coordinate delta lo hi,
  pointer_offset_holds ptr coordinate ->
  i64_checked_add (ptr_off_min ptr) delta = Some lo ->
  i64_checked_add (ptr_off_max ptr) delta = Some hi ->
  pointer_offset_holds (pointer_offsets ptr lo hi (ptr_align ptr) delta) (coordinate + delta).
Proof.
  intros ptr coordinate delta lo hi [RANGE [steps OFFSET]] LOW HIGH.
  destruct (checked_i64_bounds _ _ _ LOW) as [L _].
  destruct (checked_i64_bounds _ _ _ HIGH) as [H _].
  unfold pointer_offset_holds, pointer_offsets. cbn [ptr_off_min ptr_off_max ptr_align].
  split; [lia |]. exists steps. lia.
Qed.

(** ** Shifting pointers *)

Lemma addl_pointer_repr : forall b address delta,
  Val.addl (Vptr b address) (Vlong (Int64.repr delta)) =
  Vptr b (Ptrofs.add address (Ptrofs.repr delta)).
Proof.
  intros. cbn [Val.addl Archi.ptr64].
  now rewrite (Ptrofs.agree64_of_int_eq _ _ (Ptrofs.agree64_repr eq_refl delta)).
Qed.

(** Offsets moved by [lo..hi] and the end bound by [hi] keep every window of
    the moved pointer inside a window of the original, for any [delta] in
    [lo..hi]. *)
Lemma shifted_window : forall ptr result lo hi delta offset width,
  lo <= delta <= hi ->
  ptr_off_min result = ptr_off_min ptr + lo -> ptr_off_max result = ptr_off_max ptr + hi ->
  ptr_end_min result = shifted_end ptr hi ->
  ptr_size result = ptr_size ptr -> ptr_ty result = ptr_ty ptr ->
  verified_window result offset width -> verified_window ptr (offset + delta) width.
Proof.
  intros ptr result lo hi delta offset width RANGE LOW HIGH ENDING SIZE TYPE WINDOW.
  unfold verified_window in *. rewrite LOW, HIGH, ENDING, SIZE, TYPE in WINDOW.
  destruct (Region.grows_down (ptr_ty ptr)); cbn [lower upper] in *.
  all: destruct WINDOW as [LOWER UPPER]; split; [lia |].
  all: destruct UPPER as [UPPER | [bound [SHIFTED WITHIN]]]; [left; lia |].
  all: unfold shifted_end in SHIFTED; destruct (ptr_end_min ptr) as [ending |]; try discriminate.
  all: unfold i64_checked_sub in SHIFTED; apply i64_checked_add_value in SHIFTED.
  all: right; exists ending; split; [reflexivity | lia].
Qed.

(** A pointer moved by [delta] is described by any state of its region,
    nullness and permission whose offsets and windows move consistently. *)
Lemma pointer_shift_holds : forall world memory ptr result value delta,
  pointer_fields_well_formed result ->
  ptr_ty result = ptr_ty ptr -> ptr_nullability result = ptr_nullability ptr ->
  ptr_permission result = ptr_permission ptr ->
  (forall offset, pointer_offset_holds ptr offset ->
    pointer_offset_holds result (offset + delta)) ->
  (forall offset width, verified_window result offset width ->
    verified_window ptr (offset + delta) width) ->
  value_holds world memory (Ptr ptr) value ->
  value_holds world memory (Ptr result) (Val.addl value (Vlong (Int64.repr delta))).
Proof.
  intros world memory ptr result value delta FIELDS TYPE NULLABLE PERMISSION
    OFFSETS WINDOWS [_ [REGION [ACCESS [NULLNESS RUNTIME]]]].
  assert (NULL_BASE : null_base_pointer_holds ptr value ->
    null_base_pointer_holds result (Val.addl value (Vlong (Int64.repr delta)))).
  { intros [coordinate [OFFSET VALUE]]. subst value.
    exists (coordinate + delta). split; [now apply OFFSETS |].
    cbn [Val.addl]. now rewrite repr_add. }
  assert (NON_NULL : non_null_base_pointer_holds ptr value ->
    non_null_base_pointer_holds result (Val.addl value (Vlong (Int64.repr delta)))).
  { destruct value; cbn [non_null_base_pointer_holds Val.addl Archi.ptr64];
      try contradiction; try (intros; exact I).
    intros [PROBE [WRITE [coordinate [OFFSET NONZERO]]]].
    rewrite TYPE, PERMISSION. split; [exact PROBE |]. split; [exact WRITE |].
    exists (coordinate + delta). split; [now apply OFFSETS |].
    rewrite <- repr_add, Int64.sub_shifted. exact NONZERO. }
  assert (NUMERIC : forall n m, Region.probe_readable (ptr_ty ptr) = true ->
    (if Region.eqb (ptr_ty ptr) (Region.btf None)
     then permission_includes (ptr_permission ptr) Write = false
     else pointer_address world ptr (Vlong n)) ->
    if Region.eqb (ptr_ty ptr) (Region.btf None)
    then permission_includes (ptr_permission ptr) Write = false
    else pointer_address world result (Vlong m)).
  { intros n m PROBE. destruct (Region.eqb (ptr_ty ptr) (Region.btf None)); [auto |].
    unfold pointer_address. destruct (Region.cells (ptr_ty ptr)) as [region |] eqn:CELLS.
    - rewrite (cells_not_probe_readable _ _ CELLS) in PROBE. discriminate.
    - intros [b [origin [offset [_ [_ VALUE]]]]]. discriminate. }
  assert (ADDRESS : forall b address,
    (if Region.eqb (ptr_ty ptr) (Region.btf None)
     then permission_includes (ptr_permission ptr) Write = false
     else pointer_address world ptr (Vptr b address)) ->
    if Region.eqb (ptr_ty ptr) (Region.btf None)
    then permission_includes (ptr_permission ptr) Write = false
    else pointer_address world result (Vptr b (Ptrofs.add address (Ptrofs.repr delta)))).
  { intros b address. destruct (Region.eqb (ptr_ty ptr) (Region.btf None)); [auto |].
    unfold pointer_address. rewrite TYPE.
    destruct (Region.cells (ptr_ty ptr)) as [region |].
    - intros [offset [OFFSET VALUE]]. exists (offset + delta). split; [now apply OFFSETS |].
      unfold region_address in *.
      destruct (region_location world region) as [[block origin] |]; [| discriminate VALUE].
      inversion VALUE; subst. rewrite ptrofs_repr_add. f_equal. f_equal. lia.
    - intros [block [origin [offset [ALLOCATION [OFFSET VALUE]]]]]. inversion VALUE; subst.
      exists block, origin, (offset + delta). split; [exact ALLOCATION |].
      split; [now apply OFFSETS |]. rewrite ptrofs_repr_add. f_equal. f_equal. lia. }
  assert (RIGHTS : forall b address, pointer_access_holds memory ptr (Vptr b address) ->
    pointer_access_holds memory result (Vptr b (Ptrofs.add address (Ptrofs.repr delta)))).
  { intros b address. cbn [pointer_access_holds]. intros RIGHTS offset width POSITIVE WINDOW.
    specialize (RIGHTS (offset + delta) width POSITIVE (WINDOWS _ _ WINDOW)).
    cbv zeta in RIGHTS |- *. rewrite PERMISSION.
    rewrite Ptrofs.add_assoc, ptrofs_repr_add, (Z.add_comm delta offset). exact RIGHTS. }
  unfold value_holds, pointer_state_holds.
  unfold pointer_region_holds, pointer_permissions_holds, pointer_nullability_holds in *.
  rewrite TYPE, NULLABLE, PERMISSION.
  split; [exact FIELDS |].
  destruct value as [|i32|n|f64|f32|b address]; try solve [inversion RUNTIME].
  - assert (READONLY : non_null_base_pointer_holds ptr (Vlong n) ->
      Region.probe_readable (ptr_ty ptr) = true /\
      permission_includes (ptr_permission ptr) Write = false)
      by (intros [PROBE [WRITE _]]; auto).
    destruct (ptr_nullability ptr).
    + destruct NULLNESS as [NULL | NUMBER].
      * split; [left; exact (NULL_BASE NULL) | split; [left; exact (NULL_BASE NULL) |
          split; [left; exact (NULL_BASE NULL) | constructor]]].
      * destruct (READONLY NUMBER) as [PROBE WRITE].
        split; [destruct REGION as [NULL | OLD];
          [left; exact (NULL_BASE NULL) | right; exact (NUMERIC n _ PROBE OLD)] |].
        split; [right; rewrite PROBE; intros ALLOWED; rewrite WRITE in ALLOWED; discriminate |].
        split; [right; exact (NON_NULL NUMBER) | constructor].
    + destruct (READONLY NULLNESS) as [PROBE WRITE].
      split; [exact (NUMERIC n _ PROBE REGION) |].
      split; [rewrite PROBE; intros ALLOWED; rewrite WRITE in ALLOWED; discriminate |].
      split; [exact (NON_NULL NULLNESS) | constructor].
    + split; [exact I | split; [exact I | split; [exact (NULL_BASE NULLNESS) | constructor]]].
  - assert (NOT_NULL : ~ null_base_pointer_holds ptr (Vptr b address))
      by (intros [coordinate [_ VALUE]]; discriminate VALUE).
    assert (ACCESS_SHIFT : (if Region.probe_readable (ptr_ty ptr)
        then permission_includes (ptr_permission ptr) Write = true ->
          pointer_access_holds memory ptr (Vptr b address)
        else pointer_access_holds memory ptr (Vptr b address)) ->
      if Region.probe_readable (ptr_ty ptr)
      then permission_includes (ptr_permission ptr) Write = true ->
        pointer_access_holds memory result (Vptr b (Ptrofs.add address (Ptrofs.repr delta)))
      else pointer_access_holds memory result (Vptr b (Ptrofs.add address (Ptrofs.repr delta)))).
    { destruct (Region.probe_readable (ptr_ty ptr)); [intros OLD ALLOWED | intros OLD];
        apply RIGHTS; auto. }
    rewrite addl_pointer_repr.
    destruct (ptr_nullability ptr).
    + destruct REGION as [NULL | OLD]; [contradiction |].
      destruct ACCESS as [NULL | RIGHT]; [contradiction |].
      split; [right; exact (ADDRESS b address OLD) |].
      split; [right; exact (ACCESS_SHIFT RIGHT) | split; [right; exact I | constructor]].
    + split; [exact (ADDRESS b address REGION) |].
      split; [exact (ACCESS_SHIFT ACCESS) | split; [exact I | constructor]].
    + contradiction.
Qed.

Lemma pointer_offsets_holds : forall world memory ptr value delta lo hi,
  value_holds world memory (Ptr ptr) value ->
  i64_checked_add (ptr_off_min ptr) delta = Some lo ->
  i64_checked_add (ptr_off_max ptr) delta = Some hi ->
  value_holds world memory (Ptr (pointer_offsets ptr lo hi (ptr_align ptr) delta))
    (Val.addl value (Vlong (Int64.repr delta))).
Proof.
  intros world memory ptr value delta lo hi HOLDS LOW HIGH.
  destruct (checked_i64_bounds _ _ _ LOW) as [L _].
  destruct (checked_i64_bounds _ _ _ HIGH) as [H _].
  apply pointer_shift_holds with (ptr := ptr); try reflexivity; try assumption.
  - exact (pointer_offsets_fields_well_formed ptr delta lo hi (proj1 HOLDS) LOW HIGH).
  - intros offset OFFSET. eapply pointer_offset_shift; eauto.
  - intros offset width.
    apply shifted_window with (lo := delta) (hi := delta); cbn; try lia; reflexivity.
Qed.

Lemma shift_ptr_holds : forall world memory ptr value shift result,
  value_holds world memory (Ptr ptr) value ->
  shift_ptr ptr shift = Some result ->
  value_holds world memory (Ptr result) (Val.addl value (Vlong (Int64.repr shift))).
Proof.
  intros world memory ptr value shift result HOLDS SHIFT. unfold shift_ptr in SHIFT.
  destruct (nullable_displacement_allowed ptr shift shift); [| discriminate].
  destruct (i64_checked_add (ptr_off_min ptr) shift) as [lo|] eqn:LOW; [| discriminate].
  destruct (i64_checked_add (ptr_off_max ptr) shift) as [hi|] eqn:HIGH; [| discriminate].
  injection SHIFT as <-. exact (pointer_offsets_holds world memory ptr value shift lo hi HOLDS LOW HIGH).
Qed.

(** A value fact about [src] plus a constant, shifted by Rust
    [derive_value_state], holds of [src + offset]. *)
Lemma derive_value_holds : forall world memory state original src offset derived,
  Forall (atom_holds world memory) state -> eq_constants_fit_i64 state ->
  runtime_value (variable_value world src) ->
  In original state -> derive_value_state state original src offset = Some derived ->
  value_holds world memory derived
    (Val.addl (variable_value world src) (Vlong (Int64.repr offset))).
Proof.
  intros world memory state original src offset derived FACTS CONSTANTS RUNTIME IN RAW.
  pose proof ((proj1 (Forall_forall _ _) FACTS) original IN) as HOLDS.
  destruct original; try discriminate RAW. unfold derive_value_state in RAW.
  destruct (term_offset_for_var term src) as [old|] eqn:FOUND; [| discriminate].
  destruct (i64_checked_sub offset old) as [shift|] eqn:SHIFT; [| discriminate].
  unfold i64_checked_sub in SHIFT. apply i64_checked_add_value in SHIFT.
  cbn [atom_holds] in HOLDS.
  pose proof (affine_eval _ _ _ _ (term_offset_affine _ _ _ FOUND) RUNTIME) as EVAL.
  assert (TARGET : Val.addl (variable_value world src) (Vlong (Int64.repr offset)) =
    Val.addl (eval_term world term) (Vlong (Int64.repr shift))).
  { rewrite EVAL, Val.addl_assoc. cbn [Val.addl]. rewrite repr_add.
    do 3 f_equal. lia. }
  rewrite TARGET.
  destruct value as [| | |bounds|bounds|class|ptr]; try discriminate RAW.
  - injection RAW as <-. destruct HOLDS as [n ->]. cbn [Val.addl value_holds]. eauto.
  - destruct (checked_u64 (u_lower bounds + shift)) as [lo|] eqn:LOW; [| discriminate].
    destruct (checked_u64 (u_upper bounds + shift)) as [hi|] eqn:HIGH; [| discriminate].
    injection RAW as <-.
    destruct (eval_term world term) as [| | n | | |]; cbn [value_holds] in HOLDS; try contradiction.
    cbn [Val.addl]. rewrite add_repr_signed. eapply shift_urange_holds; eauto.
  - destruct (i64_checked_add (lower bounds) shift) as [lo|] eqn:LOW; [| discriminate].
    destruct (i64_checked_add (upper bounds) shift) as [hi|] eqn:HIGH; [| discriminate].
    injection RAW as <-.
    destruct (eval_term world term) as [| | n | | |]; cbn [value_holds] in HOLDS; try contradiction.
    cbn [Val.addl]. rewrite add_repr_signed. eapply shift_srange_holds; eauto.
  - destruct (shift_congruence state term class shift) as [result|] eqn:CLASS;
      [| discriminate]. injection RAW as <-.
    destruct (eval_term world term) as [| | n | | |] eqn:VALUE;
      cbn [value_holds] in HOLDS; try contradiction.
    cbn [Val.addl]. rewrite add_repr_signed. eapply shift_congruence_holds; eauto.
  - destruct (shift_ptr ptr shift) as [result|] eqn:MOVED; [| discriminate].
    injection RAW as <-. exact (shift_ptr_holds _ _ _ _ _ _ HOLDS MOVED).
Qed.

Lemma apply_assignment_offset_holds :
  forall entails world memory state dst src offset value post,
    Forall (atom_holds world memory) state ->
    runtime_value (variable_value world src) ->
    value = Val.addl (variable_value world src) (Vlong (Int64.repr offset)) ->
    variable_value (assign_value world dst value) src = variable_value world src ->
    (forall original derived, In original state ->
      derive_value_state state original src offset = Some derived ->
      value_holds world memory derived value) ->
    apply_assignment_var_offset entails state dst src offset = Some post ->
    Forall (atom_holds (assign_value world dst value) memory) post.
Proof.
  intros entails world memory state dst src offset value post FACTS RUNTIME RESULT SOURCE
    DERIVED TRANSFER.
  set (updated := assign_value world dst value).
  fold updated in SOURCE.
  assert (DEST : variable_value updated dst = value) by apply variable_value_assign_same.
  assert (VALUE : runtime_value value) by (rewrite RESULT; now apply runtime_addl_offset).
  pose proof (representative_var_sound world memory state src FACTS) as REPRESENTATIVE.
  unfold apply_assignment_var_offset in TRANSFER. inversion TRANSFER; subst post; clear TRANSFER.
  apply Forall_app. split.
  - apply Forall_forall. intros fact IN. apply filter_In in IN as [IN NAME].
    apply negb_true_iff in NAME. eapply atom_holds_assign;
      [exact NAME |exact ((proj1 (Forall_forall _ _) FACTS) fact IN)].
  - constructor.
    + change (runtime_value (variable_value updated dst) /\
        variable_value updated dst = eval_term updated (add_const src offset)).
      rewrite DEST. split; [exact VALUE |].
      rewrite add_const_eval by (rewrite SOURCE; exact RUNTIME).
      now rewrite SOURCE.
    + constructor.
      * cbn [atom_holds eval_term value_holds]. now rewrite DEST.
      * apply Forall_app. split.
        -- destruct (negb (term_beq (representative state (Var src)) (Var src)));
             [|constructor].
           destruct (add_const_to_term (representative state (Var src)) offset)
             as [shifted|] eqn:SHIFT; [|constructor].
           destruct (negb (term_mentions dst shifted)) eqn:NAME; [|constructor].
           apply negb_true_iff in NAME. constructor; [|constructor].
           cbn [atom_holds eval_term]. rewrite DEST. split; [exact VALUE |].
           unfold updated. rewrite term_value_assign by exact NAME.
           rewrite (add_const_to_term_eval world _ offset shifted
             ltac:(rewrite REPRESENTATIVE; exact RUNTIME) SHIFT).
           now rewrite REPRESENTATIVE.
        -- apply Forall_forall. intros fact IN. apply in_map_iff in IN as [folded [<- IN]].
           apply filter_In in IN as [IN _].
           assert (EACH : Forall (fun state => value_holds world memory state value)
             (flat_map (fun fact => match derive_value_state state fact src offset with
               | Some value => [value] | None => [] end) state)).
           { apply Forall_forall. intros derived IN'.
             apply in_flat_map in IN' as [original [OLD IN']].
             destruct (derive_value_state state original src offset) as [found |] eqn:RAW;
               [| contradiction].
             destruct IN' as [<- | []]. exact (DERIVED original found OLD RAW). }
           pose proof ((proj1 (Forall_forall _ _) (fold_holds entails _ _ _ _ EACH)) _ IN)
             as HOLDS.
           cbn [atom_holds eval_term]. rewrite DEST. unfold updated.
           now rewrite value_holds_assign.
Qed.

Lemma apply_assignment_copy_holds : forall entails world memory state dst src post,
  Forall (atom_holds world memory) state -> eq_constants_fit_i64 state ->
  runtime_value (variable_value world src) ->
  apply_assignment_var_offset entails state dst src 0 = Some post ->
  Forall (atom_holds (assign_value world dst (variable_value world src)) memory) post.
Proof.
  intros entails world memory state dst src post FACTS CONSTANTS RUNTIME TRANSFER.
  eapply apply_assignment_offset_holds; [exact FACTS |exact RUNTIME | | | |exact TRANSFER].
  - symmetry. now apply addl_zero_runtime.
  - cbn [assign_value variable_value]. destruct (Nat.eq_dec src dst); reflexivity.
  - intros original derived IN RAW.
    pose proof (derive_value_holds _ _ _ _ _ _ _ FACTS CONSTANTS RUNTIME IN RAW) as HOLDS.
    now rewrite addl_zero_runtime in HOLDS by exact RUNTIME.
Qed.

Lemma apply_assignment_scalar_offset_holds :
  forall entails world memory state dst src offset a post,
    Forall (atom_holds world memory) state -> eq_constants_fit_i64 state ->
    dst <> src ->
    variable_value world src = Vlong a ->
    apply_assignment_var_offset entails state dst src offset = Some post ->
    Forall (atom_holds (assign_value world dst (Vlong (Int64.add a (Int64.repr offset)))) memory)
      post.
Proof.
  intros entails world memory state dst src offset a post FACTS CONSTANTS DIFFERENT SOURCE
    TRANSFER.
  assert (RUNTIME : runtime_value (variable_value world src)) by (rewrite SOURCE; constructor).
  eapply apply_assignment_offset_holds; [exact FACTS |exact RUNTIME | | | |exact TRANSFER].
  - rewrite SOURCE. reflexivity.
  - rewrite variable_value_assign_other; [reflexivity |apply Nat.eqb_neq; exact DIFFERENT].
  - intros original derived IN RAW.
    pose proof (derive_value_holds _ _ _ _ _ _ _ FACTS CONSTANTS RUNTIME IN RAW) as HOLDS.
    rewrite SOURCE in HOLDS. exact HOLDS.
Qed.

(** Exact subtraction before Euclidean remainder keeps every value in the
    input range satisfying the congruence. This is the numerical obligation
    of Rust's corrected bound snapping, not full pointer-add soundness. The
    former wrapping calculation failed it for [1,4], modulus 3, i64::MIN. *)
Lemma snap_congruence_bounds_sound : forall lo hi r m scalar,
  0 < m -> lo <= scalar <= hi -> scalar mod m = r mod m ->
  lo + (r - lo) mod m <= scalar <= hi - (hi - r) mod m.
Proof.
  intros lo hi r m scalar POS RANGE CONG.
  assert (LOW : (r - lo) mod m = (scalar - lo) mod m).
  { rewrite (Zminus_mod r lo m), (Zminus_mod scalar lo m), CONG. reflexivity. }
  assert (HIGH : (hi - r) mod m = (hi - scalar) mod m).
  { rewrite (Zminus_mod hi r m), (Zminus_mod hi scalar m), CONG. reflexivity. }
  rewrite LOW, HIGH.
  pose proof (Z.mod_le (scalar - lo) m ltac:(lia) ltac:(lia)).
  pose proof (Z.mod_le (hi - scalar) m ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma to_i64_bounds : forall value result,
  to_i64 value = Some result -> result = value /\ 0 <= value <= Int64.max_signed.
Proof.
  intros value result CHECK. unfold to_i64 in CHECK.
  destruct ((0 <=? value) && (value <=? Int64.max_signed)) eqn:WIDTH; try discriminate.
  inversion CHECK; subst result. apply andb_true_iff in WIDTH as [LOW HIGH].
  apply Z.leb_le in LOW, HIGH. auto.
Qed.

Lemma pointer_offset_sum : forall ptr coordinate scalar lo hi stride delta,
  ptr_off_min ptr <= coordinate <= ptr_off_max ptr -> lo <= scalar <= hi ->
  (stride | coordinate - ptr_off_min ptr) -> (stride | scalar - lo) ->
  pointer_offset_holds
    (pointer_offsets ptr (ptr_off_min ptr + lo) (ptr_off_max ptr + hi) stride delta)
    (coordinate + scalar).
Proof.
  intros ptr coordinate scalar lo hi stride delta POINTER SCALAR [left LEFT] [right RIGHT].
  unfold pointer_offset_holds, pointer_offsets. cbn [ptr_off_min ptr_off_max ptr_align].
  split; [lia |]. exists (left + right). nia.
Qed.

Lemma derive_ptr_offset_add_fields : forall ptr bounds class result,
  pointer_fields_well_formed ptr -> derive_ptr_offset_add ptr bounds class = Some result ->
  pointer_fields_well_formed result /\
  (ptr_ty result = ptr_ty ptr /\ ptr_nullability result = ptr_nullability ptr /\
   ptr_flags result = ptr_flags ptr /\ ptr_permission result = ptr_permission ptr /\
   ptr_ref_obj result = ptr_ref_obj ptr).
Proof.
  intros ptr bounds class result FIELDS DERIVED.
  pose proof FIELDS as [_ [_ [SIZE [ALIGN_WIDTH [FLAGS END]]]]].
  assert (CAP : Int64.max_signed < Int64.modulus) by
    (change (9223372036854775807 < 18446744073709551616); lia).
  unfold derive_ptr_offset_add in DERIVED.
  destruct (to_i64 (u_lower bounds)) as [lower|]; try discriminate.
  destruct (to_i64 (u_upper bounds)) as [upper|]; try discriminate.
  set (stride := match class with Some class => modulus class | None => 1 end) in *.
  set (r := match class with Some class => residue class | None => 0 end) in *.
  set (snapped := if 1 <? stride then
    match to_i64 stride with Some m =>
      match i64_checked_add (lower) ((r - lower) mod m),
            i64_checked_sub (upper) ((upper - r) mod m) with
      | Some lo, Some hi => if lo <=? hi then Some (lo, hi) else None | _, _ => None end
    | None => None end else Some (lower, upper)) in *.
  assert (SNAP_WIDTH : forall lo hi, snapped = Some (lo, hi) ->
    0 < Z.max stride 1 < Int64.modulus).
  { intros lo hi SNAP. unfold snapped in SNAP.
    destruct (1 <? stride) eqn:POS.
    - apply Z.ltb_lt in POS. destruct (to_i64 stride) as [m|] eqn:MODULUS; try discriminate.
      destruct (to_i64_bounds _ _ MODULUS) as [M WIDTH]. rewrite Z.max_l by lia. lia.
    - apply Z.ltb_ge in POS. rewrite Z.max_r by lia.
      change (0 < 1 < 18446744073709551616). lia. }
  destruct snapped as [[lo hi]|] eqn:SNAP; try discriminate.
  destruct (nullable_displacement_allowed ptr lo hi); try discriminate.
  destruct (i64_checked_add (ptr_off_min ptr) lo) as [low|] eqn:LO; try discriminate.
  destruct (i64_checked_add (ptr_off_max ptr) hi) as [high|] eqn:HI; try discriminate.
  destruct (checked_i64_bounds _ _ _ LO) as [L LOW_WIDTH].
  destruct (checked_i64_bounds _ _ _ HI) as [H HIGH_WIDTH]. subst low high.
  inversion DERIVED; subst result.
  pose proof (SNAP_WIDTH lo hi eq_refl) as STRIDE_WIDTH.
  split.
  { unfold pointer_fields_well_formed, pointer_offsets.
    cbn [ptr_off_min ptr_off_max ptr_size ptr_align ptr_flags ptr_end_min].
    split; [exact LOW_WIDTH |]. split; [exact HIGH_WIDTH |]. split; [exact SIZE |].
    split.
    - destruct (ptr_off_min ptr =? ptr_off_max ptr).
      + lia.
      + pose proof (Z.gcd_nonneg (Z.max (ptr_align ptr) 1) (Z.max stride 1)).
        pose proof (Z.le_max_r (ptr_align ptr) 1).
        pose proof (Z.divide_pos_le
          (Z.gcd (Z.max (ptr_align ptr) 1) (Z.max stride 1)) (Z.max (ptr_align ptr) 1) ltac:(lia)
          (Z.gcd_divide_l (Z.max (ptr_align ptr) 1) (Z.max stride 1))).
        assert (Z.max (ptr_align ptr) 1 < Int64.modulus) by
          (apply Z.max_lub_lt; [lia |change (1 < 18446744073709551616); lia]).
        lia.
    - split; [exact FLAGS |apply shifted_end_well_formed]. }
  repeat apply conj; reflexivity.
Qed.

Lemma derive_ptr_offset_add_properties : forall ptr bounds class result coordinate scalar,
  pointer_fields_well_formed ptr -> pointer_offset_holds ptr coordinate ->
  u_lower bounds <= scalar <= u_upper bounds ->
  (match class with Some class => 1 < modulus class ->
     scalar mod modulus class = residue class mod modulus class | None => True end) ->
  derive_ptr_offset_add ptr bounds class = Some result ->
  pointer_fields_well_formed result /\ pointer_offset_holds result (coordinate + scalar) /\
  ptr_ty result = ptr_ty ptr /\ ptr_nullability result = ptr_nullability ptr /\
  ptr_flags result = ptr_flags ptr /\ ptr_permission result = ptr_permission ptr /\
  ptr_ref_obj result = ptr_ref_obj ptr.
Proof.
  intros ptr bounds class result coordinate scalar FIELDS [POINTER [steps OFFSET]] RANGE CONG DERIVED.
  pose proof FIELDS as [_ [_ [_ [ALIGN_WIDTH _]]]].
  pose proof (derive_ptr_offset_add_fields ptr bounds class result FIELDS DERIVED) as [RESULT_FIELDS KIND].
  assert (ALIGN : 0 <= ptr_align ptr) by lia.
  unfold derive_ptr_offset_add in DERIVED.
  destruct (to_i64 (u_lower bounds)) as [lower|] eqn:LOWER; try discriminate.
  destruct (to_i64 (u_upper bounds)) as [upper|] eqn:UPPER; try discriminate.
  destruct (to_i64_bounds _ _ LOWER) as [LOW _].
  destruct (to_i64_bounds _ _ UPPER) as [HIGH _]. subst lower upper.
  set (stride := match class with Some class => modulus class | None => 1 end) in *.
  set (r := match class with Some class => residue class | None => 0 end) in *.
  assert (CLASS : 1 < stride -> scalar mod stride = r mod stride).
  { unfold stride, r. destruct class; cbn in *; auto; lia. }
  set (snapped := if 1 <? stride then
    match to_i64 stride with Some m =>
      match i64_checked_add (u_lower bounds) ((r - u_lower bounds) mod m),
            i64_checked_sub (u_upper bounds) ((u_upper bounds - r) mod m) with
      | Some lo, Some hi => if lo <=? hi then Some (lo, hi) else None | _, _ => None end
    | None => None end else Some (u_lower bounds, u_upper bounds)) in *.
  assert (SNAPPED : forall lo hi, snapped = Some (lo, hi) ->
    lo <= scalar <= hi /\ (Z.max stride 1 | scalar - lo)).
  { intros lo hi SNAP. unfold snapped in SNAP.
    destruct (1 <? stride) eqn:STRIDE.
    - apply Z.ltb_lt in STRIDE. destruct (to_i64 stride) as [m|] eqn:MODULUS; try discriminate.
      destruct (to_i64_bounds _ _ MODULUS) as [M _]. subst m.
      destruct (i64_checked_add (u_lower bounds) ((r - u_lower bounds) mod stride))
        as [low|] eqn:LO; try discriminate.
      destruct (i64_checked_sub (u_upper bounds) ((u_upper bounds - r) mod stride))
        as [high|] eqn:HI; try discriminate.
      destruct (low <=? high); try discriminate. inversion SNAP; subst lo hi.
      destruct (checked_i64_bounds _ _ _ LO) as [L _].
      unfold i64_checked_sub in HI. destruct (checked_i64_bounds _ _ _ HI) as [H _].
      pose proof (snap_congruence_bounds_sound (u_lower bounds) (u_upper bounds) r stride scalar
        ltac:(lia) RANGE (CLASS STRIDE)) as BOUNDS.
      split; [lia |]. rewrite Z.max_l by lia.
      assert (DELTA : (r - u_lower bounds) mod stride = (scalar - u_lower bounds) mod stride).
      { rewrite (Zminus_mod r (u_lower bounds) stride),
          (Zminus_mod scalar (u_lower bounds) stride), (CLASS STRIDE). reflexivity. }
      rewrite L, DELTA. exists ((scalar - u_lower bounds) / stride).
      pose proof (Z.div_mod (scalar - u_lower bounds) stride ltac:(lia)). nia.
    - apply Z.ltb_ge in STRIDE. inversion SNAP; subst lo hi. split; [exact RANGE |].
      rewrite Z.max_r by lia. apply Z.divide_1_l. }
  destruct snapped as [[lo hi]|] eqn:SNAP; try discriminate.
  destruct (nullable_displacement_allowed ptr lo hi); try discriminate.
  destruct (i64_checked_add (ptr_off_min ptr) lo) as [low|] eqn:LO; try discriminate.
  destruct (i64_checked_add (ptr_off_max ptr) hi) as [high|] eqn:HI; try discriminate.
  destruct (checked_i64_bounds _ _ _ LO) as [L LOW_WIDTH].
  destruct (checked_i64_bounds _ _ _ HI) as [H HIGH_WIDTH]. subst low high.
  inversion DERIVED; subst result.
  destruct (SNAPPED lo hi eq_refl) as [SCALAR DIVIDES].
  split; [exact RESULT_FIELDS |]. split; [|exact KIND].
  destruct (ptr_off_min ptr =? ptr_off_max ptr) eqn:PRECISE.
  - apply Z.eqb_eq in PRECISE. apply pointer_offset_sum; try assumption.
    replace (coordinate - ptr_off_min ptr) with 0 by lia. apply Z.divide_0_r.
  - apply pointer_offset_sum; try assumption.
    + rewrite OFFSET. replace (ptr_off_min ptr + ptr_align ptr * steps - ptr_off_min ptr)
        with (steps * ptr_align ptr) by ring.
      apply Z.divide_mul_r. destruct (Z.eq_dec (ptr_align ptr) 0) as [ZERO |NONZERO].
      * rewrite ZERO. apply Z.divide_0_r.
      * rewrite Z.max_l by lia. apply Z.gcd_divide_l.
    + eapply Z.divide_trans; [apply Z.gcd_divide_r |exact DIVIDES].
Qed.

(** The shape of a register-offset result: offsets moved by the snapped
    bounds [lo..hi], which contain every scalar the bounds and class admit. *)
Lemma derive_ptr_offset_add_shape : forall ptr bounds class result scalar,
  u_lower bounds <= scalar <= u_upper bounds ->
  (match class with Some class => 1 < modulus class ->
     scalar mod modulus class = residue class mod modulus class | None => True end) ->
  derive_ptr_offset_add ptr bounds class = Some result ->
  exists lo hi, lo <= scalar <= hi /\
    ptr_off_min result = ptr_off_min ptr + lo /\ ptr_off_max result = ptr_off_max ptr + hi /\
    ptr_end_min result = shifted_end ptr hi /\ ptr_size result = ptr_size ptr /\
    ptr_ty result = ptr_ty ptr.
Proof.
  intros ptr bounds class result scalar RANGE CONG DERIVED.
  unfold derive_ptr_offset_add in DERIVED.
  destruct (to_i64 (u_lower bounds)) as [lower|] eqn:LOWER; try discriminate.
  destruct (to_i64 (u_upper bounds)) as [upper|] eqn:UPPER; try discriminate.
  destruct (to_i64_bounds _ _ LOWER) as [LOW _].
  destruct (to_i64_bounds _ _ UPPER) as [HIGH _]. subst lower upper.
  set (stride := match class with Some class => modulus class | None => 1 end) in *.
  set (r := match class with Some class => residue class | None => 0 end) in *.
  assert (CLASS : 1 < stride -> scalar mod stride = r mod stride).
  { unfold stride, r. destruct class; cbn in *; auto; lia. }
  set (snapped := if 1 <? stride then
    match to_i64 stride with Some m =>
      match i64_checked_add (u_lower bounds) ((r - u_lower bounds) mod m),
            i64_checked_sub (u_upper bounds) ((u_upper bounds - r) mod m) with
      | Some lo, Some hi => if lo <=? hi then Some (lo, hi) else None | _, _ => None end
    | None => None end else Some (u_lower bounds, u_upper bounds)) in *.
  assert (SNAPPED : forall lo hi, snapped = Some (lo, hi) -> lo <= scalar <= hi).
  { intros lo hi SNAP. unfold snapped in SNAP.
    destruct (1 <? stride) eqn:STRIDE.
    - apply Z.ltb_lt in STRIDE. destruct (to_i64 stride) as [m|] eqn:MODULUS; try discriminate.
      destruct (to_i64_bounds _ _ MODULUS) as [M _]. subst m.
      destruct (i64_checked_add (u_lower bounds) ((r - u_lower bounds) mod stride))
        as [low|] eqn:LO; try discriminate.
      destruct (i64_checked_sub (u_upper bounds) ((u_upper bounds - r) mod stride))
        as [high|] eqn:HI; try discriminate.
      destruct (low <=? high); try discriminate. inversion SNAP; subst lo hi.
      destruct (checked_i64_bounds _ _ _ LO) as [L _].
      unfold i64_checked_sub in HI. destruct (checked_i64_bounds _ _ _ HI) as [H _].
      pose proof (snap_congruence_bounds_sound (u_lower bounds) (u_upper bounds) r stride scalar
        ltac:(lia) RANGE (CLASS STRIDE)) as BOUNDS.
      lia.
    - inversion SNAP; subst lo hi. exact RANGE. }
  destruct snapped as [[lo hi]|] eqn:SNAP; try discriminate.
  destruct (nullable_displacement_allowed ptr lo hi); try discriminate.
  destruct (i64_checked_add (ptr_off_min ptr) lo) as [low|] eqn:LO; try discriminate.
  destruct (i64_checked_add (ptr_off_max ptr) hi) as [high|] eqn:HI; try discriminate.
  destruct (checked_i64_bounds _ _ _ LO) as [L _].
  destruct (checked_i64_bounds _ _ _ HI) as [H _]. subst low high.
  inversion DERIVED; subst result.
  exists lo, hi. split; [exact (SNAPPED lo hi eq_refl) |].
  cbn [pointer_offsets ptr_off_min ptr_off_max ptr_end_min ptr_size ptr_ty].
  repeat split; reflexivity.
Qed.

Lemma derive_ptr_offset_add_input_widths : forall ptr bounds class result,
  derive_ptr_offset_add ptr bounds class = Some result ->
  0 <= u_lower bounds /\ u_upper bounds <= Int64.max_signed.
Proof.
  intros ptr bounds class result DERIVED. unfold derive_ptr_offset_add in DERIVED.
  destruct (to_i64 (u_lower bounds)) as [lo|] eqn:LOW; try discriminate.
  destruct (to_i64 (u_upper bounds)) as [hi|] eqn:HIGH; try discriminate.
  destruct (to_i64_bounds _ _ LOW) as [_ L].
  destruct (to_i64_bounds _ _ HIGH) as [_ H]. lia.
Qed.

Lemma derive_ptr_offset_add_congruence : forall world memory ptr bounds class result n,
  value_holds world memory (URangeValue bounds) (Vlong n) ->
  (match class with Some class => value_holds world memory (CongruenceValue class) (Vlong n)
   | None => True end) ->
  derive_ptr_offset_add ptr bounds class = Some result ->
  match class with Some class => 1 < modulus class ->
    Int64.unsigned n mod modulus class = residue class mod modulus class | None => True end.
Proof.
  intros world memory ptr bounds class result n RANGE CONG DERIVED.
  pose proof (derive_ptr_offset_add_input_widths _ _ _ _ DERIVED) as WIDTH.
  cbn [value_holds] in RANGE.
  assert (SIGNED : Int64.signed n = Int64.unsigned n) by (apply Int64.signed_eq_unsigned; lia).
  destruct class as [class|]; [|exact I]. intros POS.
  cbn [value_holds] in CONG. destruct (modulus class =? 0) eqn:ZERO.
  - apply Z.eqb_eq in ZERO. lia.
  - rewrite <- SIGNED. exact (proj2 CONG).
Qed.

Lemma derive_ptr_offset_add_holds : forall world memory ptr bounds class result value n,
  value_holds world memory (Ptr ptr) value ->
  value_holds world memory (URangeValue bounds) (Vlong n) ->
  (match class with Some class => value_holds world memory (CongruenceValue class) (Vlong n)
   | None => True end) ->
  derive_ptr_offset_add ptr bounds class = Some result ->
  value_holds world memory (Ptr result) (Val.addl value (Vlong n)).
Proof.
  intros world memory ptr bounds class result value n HOLDS RANGE CONG DERIVED.
  pose proof (derive_ptr_offset_add_congruence world memory ptr bounds class result n
    RANGE CONG DERIVED) as CLASS.
  cbn [value_holds] in RANGE.
  destruct (derive_ptr_offset_add_fields ptr bounds class result (proj1 HOLDS) DERIVED)
    as [RESULT_FIELDS [RTYPE [RNULL [_ [RPERM _]]]]].
  destruct (derive_ptr_offset_add_shape ptr bounds class result (Int64.unsigned n)
    RANGE CLASS DERIVED) as [lo [hi [SCALAR [LOW [HIGH [ENDING [SIZE _]]]]]]].
  rewrite <- (Int64.repr_unsigned n).
  apply pointer_shift_holds with (ptr := ptr); try assumption.
  - intros offset OFFSET.
    exact (proj1 (proj2 (derive_ptr_offset_add_properties ptr bounds class result offset
      (Int64.unsigned n) (proj1 HOLDS) OFFSET RANGE CLASS DERIVED))).
  - intros offset width. apply shifted_window with (lo := lo) (hi := hi); assumption.
Qed.

Lemma urange_fact_holds : forall world memory state name bounds,
  Forall (atom_holds world memory) state ->
  urange_fact state name = Some bounds ->
  value_holds world memory (URangeValue bounds) (variable_value world name).
Proof.
  intros world memory state name bounds FACTS FOUND. unfold urange_fact in FOUND.
  match type of FOUND with
  | match fold_left ?step _ _ with _ => _ end = _ =>
      assert (FOLDED : forall found, fold_left step state None = Some found ->
        value_holds world memory (URangeValue found) (variable_value world name));
      [| destruct (fold_left step state None) as [found |]; [| discriminate];
         destruct (u_lower found <=? u_upper found); [| discriminate];
         injection FOUND as <-; exact (FOLDED _ eq_refl)]
  end.
  apply fold_left_preserves with (item_holds := atom_holds world memory);
    [exact FACTS | discriminate |].
  intros fact held HOLDS HELD found.
  destruct fact; try exact (HELD found). destruct term; try exact (HELD found).
  destruct value; try exact (HELD found).
  destruct (Nat.eqb x name) eqn:NAME; [| exact (HELD found)].
  apply Nat.eqb_eq in NAME. subst x. intros AFTER. injection AFTER as <-.
  cbn [atom_holds eval_term] in HOLDS.
  destruct held as [previous |]; [| exact HOLDS].
  pose proof (HELD _ eq_refl) as PREVIOUS. cbn [value_holds u_lower u_upper] in *.
  destruct (variable_value world name); try contradiction. lia.
Qed.

Lemma congruence_fact_present : forall state name class,
  congruence_fact state name = Some class -> In (AbstractValue (Var name) (CongruenceValue class)) state.
Proof.
  intros state name class. induction state as [|fact state IH]; intros FOUND; [discriminate |].
  destruct fact; cbn [congruence_fact] in FOUND; try solve [right; now apply IH].
  destruct term; cbn [congruence_fact] in FOUND; try solve [right; now apply IH].
  destruct value; cbn [congruence_fact] in FOUND; try solve [right; now apply IH].
  destruct (Nat.eqb x name) eqn:NAME; [|right; now apply IH].
  apply Nat.eqb_eq in NAME. subst x. inversion FOUND; subst. left. reflexivity.
Qed.

Lemma derived_ptr_add_reg_holds : forall world memory state lhs rhs a b result,
  Forall (atom_holds world memory) state ->
  variable_value world lhs = a -> variable_value world rhs = b ->
  derived_ptr_add_reg state lhs rhs = Some result ->
  value_holds world memory (Ptr result) (Val.addl a b).
Proof.
  intros world memory state lhs rhs a b result FACTS LEFT RIGHT DERIVED.
  unfold derived_ptr_add_reg in DERIVED.
  destruct (find_pointer_fact state lhs) as [left|] eqn:LPTR;
    destruct (find_pointer_fact state rhs) as [right|] eqn:RPTR; try discriminate.
  - destruct (urange_fact state rhs) as [bounds|] eqn:RANGE; try discriminate.
    pose proof ((proj1 (Forall_forall _ _) FACTS) _ (find_pointer_fact_present _ _ _ LPTR)) as POINTER.
    pose proof (urange_fact_holds _ _ _ _ _ FACTS RANGE) as SCALAR.
    cbn [atom_holds eval_term] in POINTER. rewrite LEFT in POINTER. rewrite RIGHT in SCALAR.
    destruct b as [|i32|n|f64|f32|block address]; cbn [value_holds] in SCALAR; try contradiction.
    assert (CONG : match congruence_fact state rhs with Some class =>
      value_holds world memory (CongruenceValue class) (Vlong n) | None => True end).
    { destruct (congruence_fact state rhs) as [class|] eqn:FOUND; [|exact I].
      pose proof ((proj1 (Forall_forall _ _) FACTS) _ (congruence_fact_present _ _ _ FOUND)) as HOLDS.
      cbn [atom_holds eval_term] in HOLDS. now rewrite RIGHT in HOLDS. }
    eapply derive_ptr_offset_add_holds; eauto.
  - destruct (urange_fact state lhs) as [bounds|] eqn:RANGE; try discriminate.
    pose proof ((proj1 (Forall_forall _ _) FACTS) _ (find_pointer_fact_present _ _ _ RPTR)) as POINTER.
    pose proof (urange_fact_holds _ _ _ _ _ FACTS RANGE) as SCALAR.
    cbn [atom_holds eval_term] in POINTER. rewrite RIGHT in POINTER. rewrite LEFT in SCALAR.
    destruct a as [|i32|n|f64|f32|block address]; cbn [value_holds] in SCALAR; try contradiction.
    assert (CONG : match congruence_fact state lhs with Some class =>
      value_holds world memory (CongruenceValue class) (Vlong n) | None => True end).
    { destruct (congruence_fact state lhs) as [class|] eqn:FOUND; [|exact I].
      pose proof ((proj1 (Forall_forall _ _) FACTS) _ (congruence_fact_present _ _ _ FOUND)) as HOLDS.
      cbn [atom_holds eval_term] in HOLDS. now rewrite LEFT in HOLDS. }
    rewrite Val.addl_commut. eapply derive_ptr_offset_add_holds; eauto.
Qed.


End ArithmeticHelpers.
