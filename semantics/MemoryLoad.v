From Coq Require Import Bool List ZArith Lia.
From compcert Require Import Integers Values Memory.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.
From TrustNoBPF.Semantics Require Import AbstractDomain Concretization Transfer CompCertAssms
  KernelAssms IRLevelAssms Common ArithmeticHelpers Arithmetic.

Import ListNotations.
Open Scope Z_scope.

(** [entails] is the load's [attr_entails], consulted by [meet::fold]. *)
Section MemoryLoad.
Variable entails : value_state -> value_state -> bool.

(** =========== Transfer definitions =========== *)


(** Rust [transfer.rs::stack_frame_of]. *)
Definition stack_frame_of (ty : Region.t) : option frame :=
  Region.frame ty.

(** Rust [transfer.rs::push_loaded_value]. *)
Definition loaded_value (dst : var) (value : value_state) : abstract_state :=
  match value with Unknown => [] | _ => [AbstractValue (Var dst) value] end.

Definition range_eqb (left right : range) : bool :=
  Z.eqb (lower left) (lower right) && Z.eqb (upper left) (upper right).

(** The cells Rust [transfer_load_mem] recovers: those whose both endpoints
    equal the loaded range (main commit [b658aae]), in state order. *)
Fixpoint recover_memory_values (region : option Region.t) (window : range)
    (state : abstract_state) : bool * list value_state :=
  match state with
  | [] => (false, [])
  | fact :: rest =>
      let '(loaded, values) := recover_memory_values region window rest in
      match region, fact with
      | Some region, MemoryCell cell_region bytes value =>
          if Region.eqb region cell_region && range_eqb bytes window
          then (true, value :: values) else (loaded, values)
      | _, _ => (loaded, values)
      end
  end.

Definition term_as_affine (expression : term) : option (var * Z) :=
  match expression with
  | Var name => Some (name, 0)
  | AddConst name offset => Some (name, offset)
  | _ => None
  end.

(** The window search of Rust [readable.rs::window_covers]. *)
Definition readable_window_at (state : abstract_state) (base : var)
    (window : range) (delta : Z) : bool :=
  match i64_checked_add (lower window) delta, i64_checked_add (upper window) delta with
  | Some start, Some finish =>
      existsb (fun fact =>
        match fact with
        | AbstractDomain.Readable found bytes =>
            Nat.eqb found base && range_covers bytes (Range start finish)
        | _ => false
        end) state
  | _, _ => false
  end.

(** Rust [readable.rs::window_covers]. Only equalities filed under [base]
    ([key::subject]) are followed: with both sides affine, those whose left
    side is about [base]. *)
Definition readable_window_covers (state : abstract_state) (base : var)
    (window : range) : bool :=
  let covers := readable_window_at state in
  covers base window 0 || existsb (fun fact =>
    match fact with
    | Eq lhs rhs =>
        match term_as_affine lhs, term_as_affine rhs with
        | Some (a, x), Some (b, y) =>
            Nat.eqb a base && negb (Nat.eqb b base) &&
            match i64_checked_sub y x with Some delta => covers b window delta | None => false end
        | _, _ => false
        end
    | _ => false
    end) state.

(** Rust [transfer.rs::window_load_allowed]. *)
Definition window_load_allowed (state : abstract_state) (base : var)
    (offset : Z) (size : sizeOp) (strict_alignment : bool) : bool :=
  match find_pointer_fact state base with
  | Some _ => false
  | None =>
      negb (strict_alignment && (1 <? load_width size)) &&
      readable_window_covers state base (Range offset (offset + load_width size))
  end.

(** The 8-byte [ReadableCell] recovery loop of Rust [transfer.rs::transfer_load_mem]. *)
Definition recover_readable_windows (region : option Region.t) (start : Z)
    (dst : var) (state : abstract_state) : abstract_state :=
  flat_map (fun fact =>
    match region, fact with
    | Some region, ReadableCell cell_region offset bytes =>
        if Region.eqb region cell_region && Z.eqb offset start
        then [AbstractDomain.Readable dst bytes] else []
    | _, _ => []
    end) state.

(** Rust [transfer.rs::probe_loaded_ptr_state]. *)
Definition probe_loaded_ptr_state : ptr_state :=
  PtrState (Region.btf None) MaybeNull 0 0 0 0 None 1 Read None.

(** The context-field push of Rust [transfer.rs::transfer_load_mem], through
    [ctx_field_for]: a read of a whole pointer-typed context field contributes
    the pointer description supplied by the kernel field table. It is added before memory
    recovery, exactly as in Rust; partial field reads add no pointer fact. *)
Definition loaded_context_values (context : ctx_policy) (ptr : ptr_state)
    (bytes : range) (dst : var) (size : sizeOp) (offset : Z) : abstract_state :=
  if Region.is (ptr_ty ptr) RegionClass.CTX then
    match ctx_field_for context ptr offset (load_width size) false with
    | Some field =>
        if range_eqb (ctx_field_range field) bytes then
          match ctx_field_value field with
          | Some value => loaded_value dst (Ptr value)
          | None => []
          end
        else []
    | None => []
    end
  else [].

(** The test of Rust [transfer.rs::loaded_scalar] with leaks forbidden: a
    stack load reads a value the load may disclose only if every byte is, a
    full-width read through a probe-readable pointer never, other memory
    always. *)
Definition loads_scalar (state : abstract_state) (access : checked_access) (size : sizeOp) : bool :=
  match stack_frame_of (ptr_ty (access_ptr access)) with
  | Some frame => cells_disclosable state (Region.stack frame) (access_range access)
  | None => negb (Region.probe_readable (ptr_ty (access_ptr access)) && Z.eqb (load_width size) 8)
  end.

(** Rust [transfer_load_mem], including exact-range recovery, context fields
    and the [loaded_scalar] mark.
    BRANCH RUST CHANGE [CTX-PTR-SCALAR], introduced in commit (uncommitted): Rust
    marks the result [Scalar] after pushing a context field's pointer, so
    [mark_scalar] skips it; main marked it before, giving a loaded context
    pointer both facts (issue #12). *)
Definition transfer_load_mem (state : abstract_state) (dst base : var)
    (size : sizeOp) (offset : Z) (strict_alignment : bool) (maps : map_special_fields) (context : ctx_policy) : option abstract_state :=
  match checked_access_range state base offset (load_width size) strict_alignment maps context with
  | None =>
      if window_load_allowed state base offset size strict_alignment
      then Some (apply_havoc_with_size state dst size) else None
  | Some access =>
      let loaded := apply_havoc_with_size state dst size ++
        loaded_context_values context (access_ptr access) (access_range access)
          dst size offset in
      let after_havoc := if loads_scalar loaded access size
                         then mark_scalar loaded dst else loaded in
      let load_frame := stack_frame_of (ptr_ty (access_ptr access)) in
      let load_region := Region.cells (ptr_ty (access_ptr access)) in
      let stack_initialized :=
        match load_frame with
        | Some frame => cells_cover after_havoc (Region.stack frame) (access_range access)
        | None => true
        end in
      if negb (access_exact access) then
        if stack_initialized then Some after_havoc else None
      else
        let '(loaded_any, cells) :=
          recover_memory_values load_region (access_range access) after_havoc in
        if loaded_any || stack_initialized then
          let recovered := after_havoc ++ flat_map (loaded_value dst) (fold entails cells) in
          let with_windows :=
            match size with
            | DBWord => recovered ++ recover_readable_windows load_region
                          (lower (access_range access)) dst after_havoc
            | _ => recovered
            end in
          if negb loaded_any && Region.probe_readable (ptr_ty (access_ptr access)) &&
             Z.eqb (load_width size) 8
          then Some (with_windows ++ loaded_value dst (Ptr probe_loaded_ptr_state))
          else Some with_windows
        else None
  end.

(** Rocq adapters. Rust's instruction wrapper checks the base using
    [ensure_defined] from [Transfer.v]. Loads read only the base operand;
    the destination is defined by the instruction. *)

Definition transfer_load_local (before : abstract_machine_state) (dst base : ireg)
    (dst_value : var) (size : sizeOp) (offset : Z) (strict_alignment : bool) (maps : map_special_fields) (context : ctx_policy) :
    option abstract_machine_state :=
  if ensure_defined (facts before) (register_name before base) then
    match transfer_load_mem (facts before) dst_value (register_name before base)
            size offset strict_alignment maps context with
    | Some after =>
        Some (AbstractMachineState after
                (set_register_name (register_name before) dst dst_value))
    | None => None
    end
  else None.

Definition transfer_load (before : abstract_machine_state) (dst base : ireg)
    (dst_value : var) (size : sizeOp) (offset : Z) (strict_alignment : bool) (maps : map_special_fields) (context : ctx_policy) :
    option abstract_machine_state :=
  transfer_at_entry
    (SpillProvenance.LoadMem (register_name before base) dst_value offset (load_width size))
    before (transfer_load_local before dst base dst_value size offset strict_alignment maps context).

(** Rust maps each [KernelAccess] to the equally named [AccessPtrKind].
    Its unresolved [None] case is the surrounding [option] below. *)
Definition access_kind_of (ptr : ptr_state) : KernelAccess.t :=
  Region.kernel_access (ptr_ty ptr).

(** [transfer/write.rs] records either the checked pointer's kind or a
    [window_read]; [insn_facts.rs] labels the latter [AccessPtrKind::Other]. *)
Definition load_access_kind (before : abstract_machine_state) (base : ireg)
    (size : sizeOp) (offset : Z) (strict_alignment : bool) (maps : map_special_fields) (context : ctx_policy) : option KernelAccess.t :=
  let state := facts before in
  let name := register_name before base in
  match checked_access_range state name offset (load_width size) strict_alignment maps context with
  | Some access => Some (access_kind_of (access_ptr access))
  | None =>
      if window_load_allowed state name offset size strict_alignment
      then Some KernelAccess.Other else None
  end.

Definition loaded_pointer (ty : Region.t) (offset size : Z) (perm : permission) : ptr_state :=
  PtrState ty NonNull 0 offset offset size None 8 perm None.

(** The description pushed by Rust's pointer-producing arms. *)
Definition ld_imm64_pointer (maps : map_policy) (load : LdImm64.t) : option ptr_state :=
  match load with
  | LdImm64.LoadImm64 _ => None
  | LdImm64.LoadMapFd id => Some (loaded_pointer (Region.map id) 0 0 Read)
  | LdImm64.LoadMapValue id offset =>
      Some (match map_value_specs maps id with
            | Some spec => loaded_pointer (Region.map_value id) offset
                             (map_value_size spec) (map_value_perm spec)
            | None => loaded_pointer (Region.map_value id) offset 0 Read
            end)
  | LdImm64.LoadSubprogAddr id => Some (loaded_pointer (Region.func id) 0 0 Read)
  end.

(** Rust [transfer_instruction] arms for [LoadImm64], [LoadMapFd],
    [LoadMapValue] and [LoadSubprogAddr]. Map loads naming a proof family
    fail. *)
Definition transfer_ld_imm64 (maps : map_policy) (state : abstract_state)
    (dst : var) (load : LdImm64.t) : option abstract_state :=
  let push_pointer :=
    option_map (fun ptr => apply_havoc state dst ++ [AbstractValue (Var dst) (Ptr ptr)])
      (ld_imm64_pointer maps load) in
  match load with
  | LdImm64.LoadImm64 imm => apply_assignment entails state dst (AssignmentExpr.Const imm)
  | LdImm64.LoadMapFd id | LdImm64.LoadMapValue id _ =>
      if map_is_proof_family maps id then None else push_pointer
  | LdImm64.LoadSubprogAddr _ => push_pointer
  end.

(** The instruction loop's premise-index path ([premises.rs]): the
    [ld_imm64] family reads no operand, so with a fresh destination Rust runs
    the transfer without spill tracking. *)
Definition transfer_ld_imm64_local (maps : map_policy) (before : abstract_machine_state)
    (dst : ireg) (dst_value : var) (load : LdImm64.t) : option abstract_machine_state :=
  option_map (fun after =>
      AbstractMachineState after (set_register_name (register_name before) dst dst_value))
    (transfer_ld_imm64 maps (facts before) dst_value load).

(** =========== Soundness proof =========== *)

(** ** Theorem premises *)

Lemma lowers_load_base : forall size dst base offset kind executable,
  lowers_load size dst base offset kind executable -> base <> RAX.
Proof. intros size dst base offset kind executable LOWER. now destruct LOWER. Qed.

(** Context field checks are transcribed above, but their kernel instruction
    rewriting is not in [lowers_load]. Existing load proofs cover only the
    ordinary and BTF lowerings; no context-field meaning is assumed. *)
Lemma lowered_load_not_context : forall ptr size dst base offset executable,
  lowers_load size dst base offset (access_kind_of ptr) executable ->
  Region.is (ptr_ty ptr) RegionClass.CTX = false.
Proof.
  intros ptr size dst base offset executable LOWER.
  destruct (Region.is (ptr_ty ptr) RegionClass.CTX) eqn:CTX; [|reflexivity].
  assert (KIND : access_kind_of ptr = KernelAccess.Ctx).
  { unfold access_kind_of, Region.kernel_access, Region.desc.
    destruct (ptr_ty ptr) as [index key] eqn:TY.
    unfold Region.is in CTX. cbn in CTX.
    apply Nat.eqb_eq in CTX. subst index. reflexivity. }
  rewrite KIND in LOWER. inversion LOWER.
Qed.

(** The untyped BTF fallback has no flags or reference token. Its metadata
    consists only of Rust field-width checks, proved directly here. *)
Lemma probe_loaded_ptr_state_holds : forall world memory value,
  runtime_value value ->
  value_holds world memory (Ptr probe_loaded_ptr_state) value.
Proof.
  intros world memory value RUNTIME.
  split.
  { vm_compute. intuition discriminate. }
  split; [right; reflexivity |].
  split; [right; discriminate |].
  split.
  - inversion RUNTIME; subst.
    + destruct (Int64.eq n Int64.zero) eqn:ZERO.
      * apply Int64.same_if_eq in ZERO. subst n. left. exists 0. split.
        -- split; [cbn; lia |exists 0; reflexivity].
        -- reflexivity.
      * right. split; [reflexivity |]. split; [reflexivity |]. exists 0. split.
        -- split; [cbn; lia |exists 0; reflexivity].
        -- change (Int64.sub n Int64.zero <> Int64.zero).
           rewrite Int64.sub_zero_l. intro SAME. subst n. discriminate.
    + right. exact I.
  - exact RUNTIME.
Qed.

(** ** Whole-cell reads *)

(** Adding an instruction offset reaches the same address as adding it to the
    region offset.  If there is no object, both reads fail. *)
Lemma load_region_address : forall world memory region start offset size,
  load_at_offset memory (region_address world region start) offset size =
  load size (region_address world region (start + offset)) memory.
Proof.
  intros world memory region start offset size.
  unfold load_at_offset, region_address.
  destruct (region_location world region) as [[b origin] |].
  - cbn [Val.offset_ptr].
    assert (ADDRESS : Ptrofs.add (Ptrofs.repr (origin + start)) (Ptrofs.repr offset) =
                      Ptrofs.repr (origin + (start + offset))).
    { unfold Ptrofs.add. apply Ptrofs.eqm_samerepr.
      rewrite Z.add_assoc. apply Ptrofs.eqm_add;
        apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr. }
    now rewrite ADDRESS.
  - destruct size; reflexivity.
Qed.

(** A checked read through a pointer with cells uses that region's address.
    Ordinary reads establish non-nullness; BTF pointers already have the link
    even when null. *)
Lemma checked_pointer_address : forall world memory ptr value region offset width strict access,
  Region.cells (ptr_ty ptr) = Some region ->
  checked_access_for_ptr ptr offset width strict = Some access ->
  pointer_state_holds world memory ptr value ->
  pointer_address world ptr value.
Proof.
  intros world memory ptr value region offset width strict access REGION CHECK
    [_ [ADDRESS [_ [_ _]]]].
  pose proof (cells_not_probe_readable _ _ REGION) as PROBE.
  destruct (checked_ordinary_window ptr offset width strict access PROBE CHECK)
    as [NONNULL _].
  unfold pointer_region_holds in ADDRESS. rewrite NONNULL in ADDRESS.
  eapply cells_pointer_address; eauto.
Qed.

(** A singleton pointer offset fixes the region address of the load. *)
Lemma exact_pointer_load_address : forall world memory ptr base region offset size,
  Region.cells (ptr_ty ptr) = Some region ->
  pointer_address world ptr base ->
  ptr_off_min ptr = ptr_off_max ptr ->
  load_at_offset memory base offset size =
    load size (region_address world region (ptr_off_min ptr + offset)) memory.
Proof.
  intros world memory ptr base region offset size REGION ADDRESS EXACT.
  unfold pointer_address in ADDRESS. rewrite REGION in ADDRESS.
  destruct ADDRESS as [start [[[LOW HIGH] _] BASE]].
  assert (start = ptr_off_min ptr) by (rewrite EXACT in LOW; lia).
  subst start base. apply load_region_address.
Qed.

(** An exact-offset read of the WHOLE cell recovers its precise value.
    Containment alone, as tested by Rust, is not sufficient. *)
Lemma cell_holds_load : forall world memory ptr base region bytes abstract offset size,
  Region.cells (ptr_ty ptr) = Some region ->
  pointer_address world ptr base ->
  ptr_off_min ptr = ptr_off_max ptr ->
  bytes = Range (ptr_off_min ptr + offset)
                (ptr_off_max ptr + offset + load_width size) ->
  abstract <> Uninit ->
  abstract <> Unknown ->
  abstract <> Scalar ->
  cell_holds world memory region bytes abstract ->
  cell_result_holds world memory region abstract (load_at_offset memory base offset size).
Proof.
  intros world memory ptr base region bytes abstract offset size
    REGION ADDRESS EXACT RANGE INITIALIZED KNOWN NOT_SCALAR CELL.
  rewrite (exact_pointer_load_address world memory ptr base region offset size
    REGION ADDRESS EXACT). subst bytes.
  eapply cell_holds_value with
    (bytes := Range (ptr_off_min ptr + offset)
                    (ptr_off_max ptr + offset + load_width size));
    [exact INITIALIZED | exact KNOWN | exact NOT_SCALAR | | exact CELL].
  cbn. rewrite EXACT. lia.
Qed.

(** ** Destination assignment and surviving facts *)

Lemma havoc_holds : forall world memory state dst value size,
  Forall (atom_holds world memory) state -> load_bounds size value ->
  Forall (atom_holds (assign_value world dst value) memory)
    (apply_havoc_with_size state dst size).
Proof.
  intros world memory state dst value size FACTS [INITIALIZED BOUNDS].
  assert (ASSIGNED : variable_value (assign_value world dst value) dst = value).
  { cbn [assign_value variable_value]. destruct (Nat.eq_dec dst dst); congruence. }
  assert (HAVOC : Forall (atom_holds (assign_value world dst value) memory)
                   (apply_havoc state dst)).
  { apply apply_havoc_holds; assumption. }
  destruct size; cbn [apply_havoc_with_size]; try exact HAVOC;
    apply Forall_app; split; try exact HAVOC;
    destruct (BOUNDS ltac:(discriminate)) as [n [VALUE [UNSIGNED SIGNED]]];
    subst value; repeat constructor; cbn [atom_holds eval_term]; rewrite ASSIGNED;
    assumption.
Qed.

(** ** Readable windows and content recovery *)

Lemma range_eqb_eq : forall left right,
  range_eqb left right = true -> left = right.
Proof.
  intros [lo hi] [lo' hi'] EQ. apply andb_true_iff in EQ as [LOW HIGH].
  apply Z.eqb_eq in LOW, HIGH. cbn in LOW, HIGH. now subst.
Qed.

(** Equal affine terms reach the same address after adding the same offset,
    even when the underlying pointer arithmetic wraps. *)
Lemma term_as_affine_offset : forall world expression name constant offset,
  term_as_affine expression = Some (name, constant) ->
  Val.offset_ptr (eval_term world expression) (Ptrofs.repr offset) =
  Val.offset_ptr (variable_value world name) (Ptrofs.repr (constant + offset)).
Proof.
  intros world expression name constant offset AFFINE.
  destruct expression; cbn [term_as_affine] in AFFINE; try discriminate;
    inversion AFFINE; subst; cbn [eval_term];
    [reflexivity | apply offset_ptr_addl_repr].
Qed.

Lemma readable_window_at_initialized : forall world memory state base offset size delta,
  Forall (atom_holds world memory) state ->
  readable_window_at state base (Range offset (offset + load_width size)) delta = true ->
  initialized_bytes memory
    (Val.offset_ptr (variable_value world base) (Ptrofs.repr (offset + delta))) (load_width size).
Proof.
  intros world memory state base offset size delta FACTS WINDOW.
  unfold readable_window_at in WINDOW. cbn [lower upper] in WINDOW.
  destruct (i64_checked_add offset delta) as [start |] eqn:START; try discriminate.
  destruct (i64_checked_add (offset + load_width size) delta) as [finish |]
    eqn:FINISH; try discriminate.
  apply i64_checked_add_value in START, FINISH. subst start finish.
  apply existsb_exists in WINDOW as [fact [IN WINDOW]].
  destruct fact; try discriminate WINDOW.
  apply andb_true_iff in WINDOW as [NAME RANGE]. apply Nat.eqb_eq in NAME. subst.
  apply (proj1 (Forall_forall _ _) FACTS) in IN.
  unfold range_covers in RANGE. apply andb_true_iff in RANGE as [LOW HIGH].
  apply Z.leb_le in LOW, HIGH. cbn [lower upper] in LOW, HIGH.
  eapply initialized_readable_window_initialized; [exact IN | exact LOW | lia].
Qed.

(** The window search either uses the base's own window or transports one
    along the single affine equality that Rust checks. *)
Lemma readable_window_covers_initialized : forall world memory state base offset size,
  Forall (atom_holds world memory) state ->
  readable_window_covers state base (Range offset (offset + load_width size)) = true ->
  initialized_bytes memory
    (Val.offset_ptr (variable_value world base) (Ptrofs.repr offset)) (load_width size).
Proof.
  intros world memory state base offset size FACTS COVER.
  unfold readable_window_covers in COVER. apply orb_true_iff in COVER as [DIRECT | EQ].
  - replace offset with (offset + 0) by lia.
    eapply readable_window_at_initialized; eauto.
  - apply existsb_exists in EQ as [fact [IN EQ]].
    destruct fact; try discriminate EQ.
    destruct (term_as_affine lhs) as [[a x] |] eqn:LEFT; try discriminate EQ.
    destruct (term_as_affine rhs) as [[b y] |] eqn:RIGHT; try discriminate EQ.
    apply (proj1 (Forall_forall _ _) FACTS) in IN.
    cbn [atom_holds] in IN. destruct IN as [_ EQUAL].
    assert (STEP : forall left right from to from_offset to_offset,
      term_as_affine left = Some (from, from_offset) ->
      term_as_affine right = Some (to, to_offset) ->
      eval_term world left = eval_term world right ->
      (Nat.eqb from base && negb (Nat.eqb to base) &&
       match i64_checked_sub to_offset from_offset with
       | Some delta => readable_window_at state to
           (Range offset (offset + load_width size)) delta
       | None => false
       end) = true ->
      initialized_bytes memory
        (Val.offset_ptr (variable_value world base) (Ptrofs.repr offset)) (load_width size)).
    { intros left right from to from_offset to_offset L R E ALLOWED.
      apply andb_true_iff in ALLOWED as [NAMES WINDOW].
      apply andb_true_iff in NAMES as [NAME _]. apply Nat.eqb_eq in NAME. subst from.
      unfold i64_checked_sub in WINDOW.
      destruct (i64_checked_add to_offset (- from_offset)) as [delta |] eqn:DELTA;
        try discriminate WINDOW.
      apply i64_checked_add_value in DELTA. subst delta.
      pose proof (readable_window_at_initialized world memory state to offset size
        (to_offset + - from_offset) FACTS WINDOW) as INIT.
      pose proof (f_equal (fun value => Val.offset_ptr value
        (Ptrofs.repr (offset - from_offset))) E) as ADDRESS.
      cbn beta in ADDRESS.
      rewrite (term_as_affine_offset world left base from_offset _ L),
              (term_as_affine_offset world right to to_offset _ R) in ADDRESS.
      replace (from_offset + (offset - from_offset)) with offset in ADDRESS by lia.
      replace (to_offset + (offset - from_offset))
        with (offset + (to_offset + - from_offset)) in ADDRESS by lia.
      now rewrite ADDRESS. }
    eapply (STEP lhs rhs a b x y); eauto.
Qed.

Lemma readable_window_covers_load : forall world memory state base offset size,
  Forall (atom_holds world memory) state ->
  readable_window_covers state base (Range offset (offset + load_width size)) = true ->
  exists loaded, load_at_offset memory (variable_value world base) offset size = Some loaded.
Proof.
  intros. apply initialized_load_exists. eapply readable_window_covers_initialized; eauto.
Qed.

Lemma loaded_value_holds : forall world memory dst value abstract,
  variable_value world dst = value -> value_holds world memory abstract value ->
  Forall (atom_holds world memory) (loaded_value dst abstract).
Proof.
  intros world memory dst value abstract ASSIGNED HOLDS.
  destruct abstract; cbn [loaded_value]; constructor;
    try (cbn [atom_holds eval_term]; rewrite ASSIGNED; exact HOLDS); constructor.
Qed.

Lemma recover_memory_holds : forall world memory state region window value,
  Forall (atom_holds world memory) state ->
  (forall found bytes abstract,
    region = Some found ->
    cell_holds world memory found bytes abstract ->
    bytes = window -> value_holds world memory abstract value) ->
  Forall (fun abstract => value_holds world memory abstract value)
    (snd (recover_memory_values region window state)).
Proof.
  intros world memory state region window value FACTS CELL.
  induction FACTS as [| fact state HEAD TAIL IH]; [constructor |].
  cbn [recover_memory_values].
  destruct (recover_memory_values region window state) as [found values]. cbn in IH.
  destruct region as [target |]; destruct fact; try exact IH.
  destruct (_ && _) eqn:MATCH; [| exact IH]. cbn [snd].
  apply andb_true_iff in MATCH as [REGION EXACT]. apply Region.eqb_eq in REGION.
  apply range_eqb_eq in EXACT. subst target.
  constructor; [| exact IH].
  eapply CELL; [reflexivity | exact HEAD | exact EXACT].
Qed.

Lemma loaded_values_holds : forall world memory dst value values,
  variable_value world dst = value ->
  Forall (fun abstract => value_holds world memory abstract value) values ->
  Forall (atom_holds world memory) (flat_map (loaded_value dst) values).
Proof.
  intros world memory dst value values ASSIGNED VALUES.
  apply Forall_forall. intros fact IN. apply in_flat_map in IN as [abstract [MEMBER FACT]].
  pose proof (loaded_value_holds world memory dst value abstract ASSIGNED
    ((proj1 (Forall_forall _ _) VALUES) _ MEMBER)) as HOLDS.
  exact ((proj1 (Forall_forall _ _) HOLDS) _ FACT).
Qed.

(** Loading the actual contents of a spilled window transfers its read
    permission to the destination; it does not recover any numeric value. *)
Lemma recover_readable_windows_holds : forall world memory state region start dst value,
  variable_value world dst = value ->
  Forall (atom_holds world memory) state ->
  (forall found loaded,
    region = Some found ->
    load DBWord (region_address world found start) memory = Some loaded ->
    load_value_casting loaded = value) ->
  Forall (atom_holds world memory) (recover_readable_windows region start dst state).
Proof.
  intros world memory state region start dst value ASSIGNED FACTS RESULT.
  induction FACTS as [| fact state HEAD TAIL IH]; [constructor |].
  cbn [recover_readable_windows flat_map] in *.
  destruct fact; try (destruct region; exact IH).
  destruct region as [target |]; [| exact IH].
  destruct (_ && _) eqn:MATCH; [| exact IH].
  apply andb_true_iff in MATCH as [REGION OFFSET].
  apply Region.eqb_eq in REGION. apply Z.eqb_eq in OFFSET. subst target offset.
  destruct HEAD as [_ [loaded [LOAD WINDOW]]].
  constructor; [| exact IH]. cbn [atom_holds]. rewrite ASSIGNED.
  now rewrite <- (RESULT region0 loaded eq_refl LOAD).
Qed.

(** ** Concrete execution and its output facts *)

Lemma load_value_unique : forall regs (dst : ireg) stack code_id count memory x y,
  Next (nextinstr (Pregmap.set dst x regs)) stack code_id count memory =
  Next (nextinstr (Pregmap.set dst y regs)) stack code_id count memory -> x = y.
Proof.
  intros regs dst stack code_id count memory x y EQ.
  injection EQ as EQ. apply (f_equal (fun rs : regset => rs dst)) in EQ.
  now rewrite !nextinstr_set_value in EQ.
Qed.

Definition load_result_defined (concrete : tls_state) (base : ireg)
    (size : sizeOp) (offset : Z) : Prop :=
  match concrete with
  | TLS_State regs _ _ _ memory =>
      forall loaded,
        load_at_offset memory (regs base) offset size = Some loaded ->
        load_value_casting loaded <> Vundef
  end.

(** Execute a checked load. Bounds and permissions supply ordinary read
    success; [load_result_defined] excludes undefined results. Protected reads
    may fail, in which case the instruction returns zero. *)
Lemma checked_load_execution :
  forall world memory ptr (regs : regset) stack code_id count program regions
         size (dst base : ireg) offset strict access executable,
    checked_access_for_ptr ptr offset (load_width size) strict = Some access ->
    pointer_state_holds world memory ptr (regs base) ->
    load_result_defined (TLS_State regs stack code_id count memory) base size offset ->
    lowers_load size dst base offset (access_kind_of ptr) executable ->
    exists value, load_bounds size value /\
      exec_instr program executable regs stack code_id count memory regions =
      Next (nextinstr (Pregmap.set dst value regs)) stack code_id count memory.
Proof.
  intros world memory ptr regs stack code_id count program regions size dst base offset
    strict access executable CHECK POINTER DEFINED LOWER.
  remember (access_kind_of ptr) as kind eqn:KIND in LOWER. destruct LOWER.
  - assert (ORDINARY : Region.probe_readable (ptr_ty ptr) = false).
    { rewrite Region.probe_readable_access. unfold access_kind_of in KIND.
      rewrite <- KIND. reflexivity. }
    destruct (checked_ordinary_read world memory ptr (regs base) offset size strict access
      ORDINARY CHECK POINTER) as [loaded LOAD].
    exists (load_value_casting loaded). split.
    + eapply load_bounds_result; [exact LOAD |].
      eapply load_result_runtime; [exact LOAD | exact (DEFINED loaded LOAD)].
    + cbn [exec_instr]. unfold load_at_offset in LOAD. unfold exec_load, Pregmap.get.
      destruct (regs base); try (destruct size; discriminate LOAD).
      now rewrite LOAD.
  - cbn [exec_instr]. unfold exec_load_probe.
    destruct (load size (Val.offset_ptr (regs base) (Ptrofs.repr offset)) memory)
      as [loaded |] eqn:LOAD.
    + exists (load_value_casting loaded). split; [| reflexivity].
      eapply load_bounds_result; [exact LOAD |].
      eapply load_result_runtime; [exact LOAD | exact (DEFINED loaded LOAD)].
    + exists (Vlong Int64.zero). split; [apply load_bounds_zero | reflexivity].
Qed.

Lemma executed_load_result :
  forall program regions (regs : regset) stack code_id count memory
         size (dst base : ireg) offset kind executable value loaded,
    lowers_load size dst base offset kind executable ->
    exec_instr program executable regs stack code_id count memory regions =
      Next (nextinstr (Pregmap.set dst value regs)) stack code_id count memory ->
    load_at_offset memory (regs base) offset size = Some loaded ->
    load_value_casting loaded = value.
Proof.
  intros program regions regs stack code_id count memory size dst base offset
    kind executable value loaded LOWER EXEC LOAD.
  destruct LOWER; cbn [exec_instr] in EXEC; unfold load_at_offset in LOAD.
  - unfold exec_load, Pregmap.get in EXEC.
    destruct (regs base); try (destruct size; discriminate LOAD).
    rewrite LOAD in EXEC. eapply load_value_unique; exact EXEC.
  - unfold exec_load_probe in EXEC. rewrite LOAD in EXEC.
    eapply load_value_unique; exact EXEC.
Qed.

(** A whole-cell fact describes the actual result of this execution.
    Rust now uses the same exact-range recovery. *)
Lemma executed_load_cell_holds :
  forall world memory ptr (regs : regset) stack code_id count program regions
         size (dst base : ireg) offset strict access executable value,
    checked_access_for_ptr ptr offset (load_width size) strict = Some access ->
    pointer_state_holds world memory ptr (regs base) ->
    runtime_value value ->
    load_result_defined (TLS_State regs stack code_id count memory) base size offset ->
    lowers_load size dst base offset (access_kind_of ptr) executable ->
    exec_instr program executable regs stack code_id count memory regions =
      Next (nextinstr (Pregmap.set dst value regs)) stack code_id count memory ->
    forall region bytes abstract,
      Region.cells (ptr_ty ptr) = Some region ->
      ptr_off_min ptr = ptr_off_max ptr ->
      bytes = Range (ptr_off_min ptr + offset)
                    (ptr_off_max ptr + offset + load_width size) ->
      cell_holds world memory region bytes abstract ->
      value_holds world memory abstract value.
Proof.
  intros world memory ptr regs stack code_id count program regions size dst base offset
    strict access executable value CHECK POINTER RUNTIME DEFINED LOWER EXEC
    region bytes abstract REGION EXACT RANGE CELL.
  pose proof (checked_pointer_address world memory ptr (regs base) region
    offset _ strict access REGION CHECK POINTER) as ADDRESS.
  (* Uninit and Unknown need no cell-content reasoning; a Scalar cell's
     pointer-free bytes decode to an integer. *)
  assert (CASES : abstract = Uninit \/ abstract = Unknown \/ abstract = Scalar \/
    (abstract <> Uninit /\ abstract <> Unknown /\ abstract <> Scalar)).
  { destruct abstract; auto; right; right; right; repeat split; discriminate. }
  destruct CASES as [-> | [-> | [-> | [INITIALIZED [KNOWN NOT_SCALAR]]]]];
    [exact I | exact RUNTIME | |].
  { destruct (checked_ordinary_read world memory ptr (regs base) offset size strict access
      (cells_not_probe_readable _ _ REGION) CHECK POINTER) as [loaded LOAD].
    rewrite <- (executed_load_result program regions regs stack code_id count memory
      size dst base offset _ executable value loaded LOWER EXEC LOAD).
    pose proof (DEFINED loaded LOAD) as LOADED.
    rewrite (exact_pointer_load_address world memory ptr (regs base) region offset size
      REGION ADDRESS EXACT) in LOAD.
    destruct CELL as [_ [_ [_ FREE]]]. cbn [cell_value_holds] in FREE. subst bytes.
    cbn [lower upper] in FREE. rewrite EXACT in LOAD, FREE.
    replace (ptr_off_max ptr + offset + load_width size - (ptr_off_max ptr + offset))
      with (load_width size) in FREE by lia.
    destruct (region_address world region (ptr_off_max ptr + offset)) as [| | | | | b address];
      try contradiction.
    exact (load_pointer_free_long _ _ _ _ _ LOAD FREE LOADED). }
  pose proof (cell_holds_load world memory ptr (regs base) region bytes abstract
    offset size REGION ADDRESS EXACT RANGE INITIALIZED KNOWN NOT_SCALAR CELL) as RESULT.
  destruct (load_at_offset memory (regs base) offset size) as [loaded |] eqn:LOAD.
  - cbn [cell_result_holds] in RESULT.
    rewrite (executed_load_result program regions regs stack code_id count memory
      size dst base offset _ executable value loaded LOWER EXEC LOAD) in RESULT.
    exact RESULT.
  - apply Region.cells_self in REGION. subst region.
    remember (access_kind_of ptr) as kind eqn:KIND in LOWER. destruct LOWER.
    + assert (ORDINARY : Region.probe_readable (ptr_ty ptr) = false).
      { rewrite Region.probe_readable_access. unfold access_kind_of in KIND.
        rewrite <- KIND. reflexivity. }
      unfold cell_result_holds in RESULT. rewrite ORDINARY in RESULT. contradiction.
    + assert (PROBE : Region.probe_readable (ptr_ty ptr) = true).
      { rewrite Region.probe_readable_access. unfold access_kind_of in KIND.
        rewrite <- KIND. reflexivity. }
      unfold cell_result_holds in RESULT. rewrite PROBE in RESULT.
      cbn [exec_instr] in EXEC. unfold exec_load_probe in EXEC.
      unfold load_at_offset in LOAD. rewrite LOAD in EXEC.
      apply load_value_unique in EXEC. now rewrite <- EXEC.
Qed.

(** ** Transfer soundness *)

(** Preservation for the Rust exact-range transfer outside context accesses. The cell-result
    premise is discharged from execution in the soundness proof below. *)
Lemma transfer_load_mem_preserves :
  forall world memory state dst base ptr value size offset strict maps context after,
    Forall (atom_holds world memory) state ->
    find_pointer_fact state base = Some ptr ->
    Region.is (ptr_ty ptr) RegionClass.CTX = false ->
    load_bounds size value ->
    (forall loaded,
      load_at_offset memory (variable_value world base) offset size = Some loaded ->
      load_value_casting loaded = value) ->
    (forall region bytes abstract,
      Region.cells (ptr_ty ptr) = Some region ->
      ptr_off_min ptr = ptr_off_max ptr ->
      bytes = Range (ptr_off_min ptr + offset)
                    (ptr_off_max ptr + offset + load_width size) ->
      cell_holds world memory region bytes abstract -> value_holds world memory abstract value) ->
    (forall access,
      checked_access_for_ptr ptr offset (load_width size) strict = Some access ->
      loads_scalar (apply_havoc_with_size state dst size) access size = true ->
      exists n, value = Vlong n) ->
    transfer_load_mem state dst base size offset strict maps context = Some after ->
    Forall (atom_holds (assign_value world dst value) memory) after.
Proof.
  intros world memory state dst base ptr value size offset strict maps context after
    FACTS FIND NONCTX BOUNDS RESULT CELLS MARKED TRANSFER.
  assert (POINTER : pointer_state_holds world memory ptr (variable_value world base)).
  { pose proof (find_pointer_fact_present state base ptr FIND) as IN.
    apply (proj1 (Forall_forall _ _) FACTS) in IN. exact IN. }
  unfold transfer_load_mem, checked_access_range in TRANSFER. rewrite FIND in TRANSFER.
  destruct (checked_access_for_ptr ptr offset (load_width size) strict) as [access |] eqn:CHECK.
  2: { cbn [filter_context_access filter_special_access] in TRANSFER. unfold window_load_allowed in TRANSFER. rewrite FIND in TRANSFER. discriminate. }
  assert (ACCESS_CTX : Region.is (ptr_ty (access_ptr access)) RegionClass.CTX = false).
  { rewrite (checked_access_shape _ _ _ _ _ CHECK). exact NONCTX. }
  cbn [filter_context_access] in TRANSFER. rewrite ACCESS_CTX in TRANSFER.
  destruct (check_special_fields maps (access_ptr access) (access_range access)) eqn:SPECIAL;
    cbn [filter_special_access] in TRANSFER; rewrite SPECIAL in TRANSFER.
  2: { cbn [filter_special_access] in TRANSFER. unfold window_load_allowed in TRANSFER. rewrite FIND in TRANSFER. discriminate. }
  unfold loaded_context_values in TRANSFER. rewrite ACCESS_CTX in TRANSFER.
  rewrite app_nil_r in TRANSFER.
  set (havoced := apply_havoc_with_size state dst size) in *.
  set (updated := assign_value world dst value).
  assert (ASSIGNED : variable_value updated dst = value).
  { unfold updated, assign_value; cbn. destruct (Nat.eq_dec dst dst); congruence. }
  assert (HAVOC : Forall (atom_holds updated memory) havoced).
  { apply havoc_holds; assumption. }
  assert (MARK : Forall (atom_holds updated memory)
    (if loads_scalar havoced access size then mark_scalar havoced dst else havoced)).
  { destruct (loads_scalar havoced access size) eqn:SCALAR; [| exact HAVOC].
    apply mark_scalar_holds; [exact HAVOC |]. intros _. rewrite ASSIGNED.
    exact (MARKED access eq_refl SCALAR). }
  set (marked := if loads_scalar havoced access size then mark_scalar havoced dst else havoced)
    in *.
  pose proof (checked_access_shape ptr offset (load_width size) strict access CHECK) as SHAPE.
  subst access.
  cbn [access_ptr access_range access_exact] in TRANSFER.
  destruct (Z.eqb (ptr_off_min ptr) (ptr_off_max ptr)) eqn:EXACT;
    cbn [negb] in TRANSFER.
  - apply Z.eqb_eq in EXACT.
    assert (VALUES : Forall (fun abstract => value_holds updated memory abstract value)
      (snd (recover_memory_values (Region.cells (ptr_ty ptr))
        (Range (ptr_off_min ptr + offset) (ptr_off_max ptr + offset + load_width size))
        marked))).
    { eapply recover_memory_holds; [exact MARK |].
      intros region bytes abstract REGION CELL RANGE.
      unfold updated in CELL |- *. rewrite cell_holds_assign in CELL.
      rewrite value_holds_assign. eapply CELLS; eauto. }
    destruct (recover_memory_values _ _ marked) as [found cells].
    cbn [snd] in VALUES.
    destruct (found || _); try discriminate.
    assert (RECOVERED : Forall (atom_holds updated memory)
      (marked ++ flat_map (loaded_value dst) (fold entails cells))).
    { apply Forall_app. split; [exact MARK |].
      apply loaded_values_holds with (value := value); [exact ASSIGNED |].
      exact (fold_holds entails _ _ _ _ VALUES). }
    set (with_windows := match size with
      | DBWord => (marked ++ flat_map (loaded_value dst) (fold entails cells)) ++
          recover_readable_windows (Region.cells (ptr_ty ptr)) (lower
            (Range (ptr_off_min ptr + offset) (ptr_off_max ptr + offset + load_width size)))
          dst marked
      | _ => marked ++ flat_map (loaded_value dst) (fold entails cells)
      end) in *.
    assert (WINDOWS : Forall (atom_holds updated memory) with_windows).
    { unfold with_windows. destruct size; try exact RECOVERED.
      apply Forall_app. split; [exact RECOVERED |].
      eapply recover_readable_windows_holds; [exact ASSIGNED | exact MARK |].
      intros region loaded REGION LOAD.
      pose proof (checked_pointer_address world memory ptr (variable_value world base)
        region offset _ strict _ REGION CHECK POINTER) as ADDRESS.
      apply RESULT. rewrite (exact_pointer_load_address world memory ptr
        (variable_value world base) region offset DBWord REGION ADDRESS EXACT).
      exact LOAD. }
    destruct (_ && _); inversion TRANSFER; subst after; [| exact WINDOWS].
    apply Forall_app. split; [exact WINDOWS |].
    eapply (loaded_value_holds updated memory dst value (Ptr probe_loaded_ptr_state));
      [exact ASSIGNED |].
    apply probe_loaded_ptr_state_holds. exact (proj1 BOUNDS).
  - destruct (match stack_frame_of (ptr_ty ptr) with
      | Some frame => cells_cover marked (Region.stack frame)
          (Range (ptr_off_min ptr + offset) (ptr_off_max ptr + offset + load_width size))
      | None => true
      end); inversion TRANSFER; subst after; exact MARK.
Qed.

(** ** Initialization of loaded bytes *)

Lemma cell_holds_initialized : forall world memory region bytes abstract,
  Region.uninit_by_default region = true ->
  abstract <> Uninit ->
  cell_holds world memory region bytes abstract ->
  region_bytes_addressable world region bytes /\
  initialized_bytes memory (region_address world region (lower bytes))
    (upper bytes - lower bytes).
Proof.
  intros world memory region bytes abstract STACK DEFINED CELL.
  destruct abstract; try contradiction; cbn [cell_holds] in CELL;
    try rewrite STACK in CELL; tauto.
Qed.

Lemma cell_positions_initialized : forall world memory region b origin bytes,
  region_location world region = Some (b, origin) ->
  region_bytes_addressable world region bytes ->
  initialized_bytes memory (region_address world region (lower bytes))
    (upper bytes - lower bytes) ->
  forall position, lower bytes <= position < upper bytes ->
    byte_initialized memory b (Ptrofs.unsigned (Ptrofs.repr (origin + position))).
Proof.
  intros world memory region b origin bytes LOCATION ADDRESSABLE INIT position BOUNDS.
  unfold region_bytes_addressable, region_address in ADDRESSABLE, INIT.
  rewrite LOCATION in ADDRESSABLE, INIT.
  pose proof (initialized_bytes_positions _ _ _ _ INIT (position - lower bytes)
    ltac:(lia)) as BYTE.
  replace (origin + position) with (origin + (lower bytes + (position - lower bytes))) by lia.
  rewrite (repr_subrange_start origin (lower bytes) (upper bytes - lower bytes));
    [exact BYTE | exact ADDRESSABLE | lia].
Qed.

(** Rust's [cells_cover] chain of cells initializes every byte it covers. *)
Lemma cells_cover_from_initialized :
  forall fuel world memory state region b origin window point,
    region_location world region = Some (b, origin) ->
    (forall cell_region bytes abstract,
      In (MemoryCell cell_region bytes abstract) state ->
      Region.eqb region cell_region = true ->
      region_bytes_addressable world cell_region bytes /\
      initialized_bytes memory (region_address world cell_region (lower bytes))
        (upper bytes - lower bytes)) ->
    cells_cover_from fuel state region window point = true ->
    forall position, point <= position < upper window ->
      byte_initialized memory b (Ptrofs.unsigned (Ptrofs.repr (origin + position))).
Proof.
  induction fuel as [| fuel IH];
    intros world memory state region b origin window point LOCATION CELLS COVER
      position BOUNDS;
    cbn [cells_cover_from] in COVER;
    (destruct (upper window <=? point) eqn:DONE; [apply Z.leb_le in DONE; lia |]).
  { discriminate. }
  destruct (find _ state) as [fact |] eqn:FIND; [| discriminate].
  assert (CELL : exists cell_region bytes abstract,
    fact = MemoryCell cell_region bytes abstract)
    by (destruct fact; try discriminate COVER; eauto).
  destruct CELL as [cell_region [bytes [abstract ->]]].
  apply find_some in FIND as [IN TEST].
  apply andb_true_iff in TEST as [TEST UPPER]. apply andb_true_iff in TEST as [SAME LOWER].
  apply Z.leb_le in LOWER. apply Z.ltb_lt in UPPER.
  destruct (Z_lt_dec position (upper bytes)) as [INSIDE | BEYOND].
  - destruct (CELLS _ _ _ IN SAME) as [ADDRESSABLE INIT].
    apply Region.eqb_eq in SAME. subst cell_region.
    eapply cell_positions_initialized; eauto. lia.
  - eapply IH; eauto. lia.
Qed.

Lemma recover_memory_values_found : forall region window state,
  fst (recover_memory_values (Some region) window state) = true ->
  exists cell_region bytes abstract,
    In (MemoryCell cell_region bytes abstract) state /\
    Region.eqb region cell_region = true /\ range_eqb bytes window = true.
Proof.
  intros region window state.
  induction state as [| fact rest IH]; intros FOUND; [discriminate |].
  cbn [recover_memory_values] in FOUND.
  destruct (recover_memory_values (Some region) window rest) as [loaded values].
  cbn [fst] in IH.
  assert (OLD : loaded = true -> exists cell_region bytes abstract,
    In (MemoryCell cell_region bytes abstract) (fact :: rest) /\
    Region.eqb region cell_region = true /\ range_eqb bytes window = true).
  { intros LOADED. destruct (IH LOADED) as [found [bytes [abstract [IN MATCH]]]].
    exists found, bytes, abstract. split; [now right | exact MATCH]. }
  destruct fact; try exact (OLD FOUND).
  match type of FOUND with context [if ?test then _ else _] =>
    destruct test eqn:TEST end; [| exact (OLD FOUND)].
  apply andb_true_iff in TEST as [SAME RANGE].
  eexists _, _, _. split; [now left | split; eassumption].
Qed.

Lemma load_havoc_cells : forall state dst size extra cell_region bytes abstract,
  (forall fact, In fact extra -> match fact with MemoryCell _ _ _ => False | _ => True end) ->
  In (MemoryCell cell_region bytes abstract) (apply_havoc_with_size state dst size ++ extra) ->
  In (MemoryCell cell_region bytes abstract) state.
Proof.
  intros state dst size extra cell_region bytes abstract EXTRA IN.
  apply in_app_or in IN as [IN | IN]; [| exact (False_ind _ (EXTRA _ IN))].
  unfold apply_havoc_with_size, apply_havoc in IN.
  destruct size; repeat (apply in_app_or in IN as [IN | IN]);
    try (apply filter_In in IN as [IN _]; exact IN);
    cbn in IN; intuition discriminate.
Qed.

Lemma loaded_context_values_cells : forall context ptr bytes dst size offset fact,
  In fact (loaded_context_values context ptr bytes dst size offset) ->
  match fact with MemoryCell _ _ _ => False | _ => True end.
Proof.
  intros context ptr bytes dst size offset fact IN.
  unfold loaded_context_values in IN.
  destruct (Region.is (ptr_ty ptr) RegionClass.CTX); [| contradiction].
  destruct (ctx_field_for context ptr offset (load_width size) false); [| contradiction].
  destruct (range_eqb _ bytes); [| contradiction].
  destruct (ctx_field_value _); [| contradiction].
  destruct IN as [<- | []]. exact I.
Qed.

(** The transfer's access to [ptr], which a successful transfer checked. *)
Lemma transfer_load_mem_access :
  forall state dst base ptr size offset strict maps context post,
    find_pointer_fact state base = Some ptr ->
    transfer_load_mem state dst base size offset strict maps context = Some post ->
    exists access,
      checked_access_range state base offset (load_width size) strict maps context =
        Some access /\
      checked_access_for_ptr ptr offset (load_width size) strict = Some access.
Proof.
  intros state dst base ptr size offset strict maps context post FIND TRANSFER.
  unfold transfer_load_mem in TRANSFER.
  destruct (checked_access_range state base offset (load_width size) strict maps context)
    as [access |] eqn:ACCESS.
  - exists access. split; [reflexivity |].
    unfold checked_access_range in ACCESS. rewrite FIND in ACCESS.
    apply filter_special_access_some in ACCESS.
    exact (filter_context_access_some _ _ _ _ _ _ ACCESS).
  - unfold window_load_allowed in TRANSFER. rewrite FIND in TRANSFER. discriminate.
Qed.

(** A checked ordinary load reads [width] bytes inside one CompCert block,
    without wrapping. *)
Lemma checked_ordinary_access :
  forall world memory ptr value offset size strict access loaded,
    Region.probe_readable (ptr_ty ptr) = false ->
    checked_access_for_ptr ptr offset (load_width size) strict = Some access ->
    pointer_state_holds world memory ptr value ->
    load_at_offset memory value offset size = Some loaded ->
    exists b address,
      value = Vptr b address /\
      Ptrofs.unsigned (Ptrofs.add address (Ptrofs.repr offset)) + load_width size
        <= Ptrofs.modulus /\
      Mem.range_perm memory b (Ptrofs.unsigned (Ptrofs.add address (Ptrofs.repr offset)))
        (Ptrofs.unsigned (Ptrofs.add address (Ptrofs.repr offset)) + load_width size)
        Cur Memtype.Readable.
Proof.
  intros world memory ptr value offset size strict access loaded ORDINARY CHECK POINTER LOAD.
  destruct (checked_ordinary_window _ _ _ _ _ ORDINARY CHECK) as [NONNULL WINDOW].
  destruct value as [| | | | | b address]; unfold load_at_offset in LOAD;
    cbn [Val.offset_ptr] in LOAD; try (destruct size; discriminate LOAD).
  exists b, address. split; [reflexivity |].
  destruct POINTER as [_ [_ [PERMISSIONS _]]].
  unfold pointer_permissions_holds in PERMISSIONS.
  rewrite ORDINARY, NONNULL in PERMISSIONS.
  assert (WIDTH : 0 < load_width size) by (destruct size; cbn; lia).
  destruct (PERMISSIONS offset (load_width size) WIDTH WINDOW) as [END _].
  split; [exact END |].
  destruct (load_loadbytes _ _ _ _ _ LOAD) as [bytes READ].
  exact (Mem.loadbytes_range_perm _ _ _ _ _ READ).
Qed.

Lemma stack_load_initialized :
  forall world memory state dst base ptr size offset strict maps context post loaded frame,
    Forall (atom_holds world memory) state ->
    no_uninit_memory_cells state ->
    find_pointer_fact state base = Some ptr ->
    ptr_ty ptr = Region.stack frame ->
    transfer_load_mem state dst base size offset strict maps context = Some post ->
    load_at_offset memory (variable_value world base) offset size = Some loaded ->
    initialized_bytes memory
      (Val.offset_ptr (variable_value world base) (Ptrofs.repr offset)) (load_width size).
Proof.
  intros world memory state dst base ptr size offset strict maps context post loaded frame
    FACTS VALID FIND TY TRANSFER LOAD.
  destruct (transfer_load_mem_access _ _ _ _ _ _ _ _ _ _ FIND TRANSFER)
    as [access [ACCESS CHECK]].
  assert (POINTER : pointer_state_holds world memory ptr (variable_value world base)).
  { exact ((proj1 (Forall_forall _ _) FACTS) _ (find_pointer_fact_present _ _ _ FIND)). }
  assert (CELLS_TY : Region.cells (ptr_ty ptr) = Some (Region.stack frame))
    by (rewrite TY; reflexivity).
  assert (ORDINARY : Region.probe_readable (ptr_ty ptr) = false) by (rewrite TY; reflexivity).
  pose proof (checked_pointer_address _ _ _ _ _ _ _ _ _ CELLS_TY CHECK POINTER) as ADDRESS.
  unfold pointer_address in ADDRESS. rewrite CELLS_TY in ADDRESS.
  destruct ADDRESS as [start [[[LOW HIGH] _] BASE]].
  destruct (checked_ordinary_access _ _ _ _ _ _ _ _ _ ORDINARY CHECK POINTER LOAD)
    as [b [address [VALUE [END PERM]]]].
  rewrite BASE in VALUE. unfold region_address in VALUE.
  destruct (region_location world (Region.stack frame)) as [[b' origin] |] eqn:LOCATION;
    [| discriminate]. injection VALUE as -> ADDRESS_EQ. subst address.
  rewrite BASE. unfold region_address. rewrite LOCATION. cbn [Val.offset_ptr].
  rewrite ptrofs_repr_add in END, PERM |- *.
  set (window := Range (ptr_off_min ptr + offset)
    (ptr_off_max ptr + offset + load_width size)).
  assert (COVERED : forall position, lower window <= position < upper window ->
    byte_initialized memory b (Ptrofs.unsigned (Ptrofs.repr (origin + position)))).
  { unfold transfer_load_mem in TRANSFER. rewrite ACCESS in TRANSFER.
    rewrite (checked_access_shape _ _ _ _ _ CHECK) in TRANSFER.
    cbn [access_ptr access_range access_exact] in TRANSFER. fold window in TRANSFER.
    rewrite TY in TRANSFER. cbn [stack_frame_of Region.frame Region.key Region.stack] in TRANSFER.
    set (pushed := apply_havoc_with_size state dst size ++
      loaded_context_values context ptr window dst size offset) in TRANSFER.
    match type of TRANSFER with context [if loads_scalar pushed ?access size then _ else _] =>
      set (after_havoc := if loads_scalar pushed access size then mark_scalar pushed dst
                          else pushed) in TRANSFER end.
    assert (CELLS : forall cell_region bytes abstract,
      In (MemoryCell cell_region bytes abstract) after_havoc ->
      Region.eqb (Region.stack frame) cell_region = true ->
      region_bytes_addressable world cell_region bytes /\
      initialized_bytes memory (region_address world cell_region (lower bytes))
        (upper bytes - lower bytes)).
    { intros cell_region bytes abstract IN SAME.
      assert (LOADED : In (MemoryCell cell_region bytes abstract) pushed).
      { unfold after_havoc in IN. destruct (loads_scalar _ _ _); [| exact IN].
        exact (mark_scalar_cells _ _ _ _ _ IN). }
      apply load_havoc_cells in LOADED; [clear IN; rename LOADED into IN | apply loaded_context_values_cells].
      apply Region.eqb_eq in SAME. subst cell_region.
      apply (cell_holds_initialized world memory _ bytes abstract); [reflexivity | |].
      - intros UNINIT. subst abstract.
        exact ((proj1 (Forall_forall _ _) VALID) _ IN).
      - exact ((proj1 (Forall_forall _ _) FACTS) _ IN). }
    destruct (cells_cover after_havoc (Region.stack frame) window) eqn:COVER.
    - intros position BOUNDS.
      eapply cells_cover_from_initialized; [exact LOCATION | exact CELLS | exact COVER | lia].
    - destruct (negb _); [discriminate |].
      destruct (recover_memory_values _ window after_havoc) as [found values] eqn:RECOVER.
      destruct found; [| discriminate].
      change (Region.cells (Region.stack frame)) with (Some (Region.stack frame)) in RECOVER.
      pose proof (f_equal fst RECOVER) as FOUND. cbn [fst] in FOUND.
      destruct (recover_memory_values_found _ _ _ FOUND)
        as [cell_region [bytes [abstract [IN [SAME RANGE]]]]].
      destruct (CELLS _ _ _ IN SAME) as [ADDRESSABLE INIT].
      apply Region.eqb_eq in SAME. subst cell_region.
      unfold range_eqb in RANGE. apply andb_true_iff in RANGE as [L U].
      apply Z.eqb_eq in L, U.
      intros position BOUNDS.
      eapply cell_positions_initialized; [exact LOCATION | exact ADDRESSABLE | exact INIT |].
      lia. }
  apply initialized_bytes_from_positions; [exact PERM |].
  intros delta DELTA.
  replace (origin + start + offset) with (origin + (start + offset)) in END |- * by lia.
  rewrite <- (repr_subrange_start origin (start + offset) (load_width size) delta END DELTA).
  apply COVERED. cbn [lower upper window]. lia.
Qed.

(** A successful load through a pointer into any region but the stack and
    untyped BTF reads initialized bytes. *)
Lemma non_stack_load_initialized : forall world memory ptr value offset size loaded,
  regions_initialized world memory ->
  Region.uninit_by_default (ptr_ty ptr) = false ->
  Region.eqb (ptr_ty ptr) (Region.btf None) = false ->
  pointer_state_holds world memory ptr value ->
  load_at_offset memory value offset size = Some loaded ->
  initialized_bytes memory (Val.offset_ptr value (Ptrofs.repr offset)) (load_width size).
Proof.
  intros world memory ptr value offset size loaded [LOCATIONS ALLOCATIONS] DEFINED TYPED
    POINTER LOAD.
  destruct value as [| | | | | b address]; unfold load_at_offset in LOAD;
    cbn [Val.offset_ptr] in LOAD; try (destruct size; discriminate LOAD).
  assert (BLOCK : block_initialized memory b).
  { destruct POINTER as [_ [REGION [_ [NULLABILITY _]]]].
    unfold pointer_region_holds in REGION. rewrite TYPED in REGION.
    assert (ADDRESS : pointer_address world ptr (Vptr b address)).
    { unfold pointer_nullability_holds in NULLABILITY.
      destruct (ptr_nullability ptr).
      - destruct REGION as [[o [_ NULL]] | ADDRESS]; [discriminate NULL | exact ADDRESS].
      - exact REGION.
      - destruct NULLABILITY as [o [_ NULL]]. discriminate NULL. }
    unfold pointer_address in ADDRESS.
    destruct (Region.cells (ptr_ty ptr)) as [region |] eqn:CELLS.
    - destruct ADDRESS as [o [_ VALUE]]. unfold region_address in VALUE.
      destruct (region_location world region) as [[b' origin] |] eqn:LOCATION;
        [| discriminate].
      injection VALUE as BLOCK _. subst b'.
      apply Region.cells_self in CELLS. subst region.
      exact (LOCATIONS _ _ _ DEFINED LOCATION).
    - destruct ADDRESS as [b' [origin [o [ALLOCATED [_ VALUE]]]]].
      injection VALUE as BLOCK _. subst b'.
      exact (ALLOCATIONS _ _ _ DEFINED ALLOCATED). }
  destruct (load_loadbytes _ _ _ _ _ LOAD) as [bytes READ].
  pose proof (Mem.loadbytes_range_perm _ _ _ _ _ READ) as PERM.
  apply initialized_bytes_from_positions; [exact PERM |].
  intros delta DELTA. unfold byte_initialized. apply BLOCK. apply PERM. lia.
Qed.

(** The bytes of every load the local transfer accepts are initialized,
    except through untyped BTF pointers. *)
(** ** Disclosable loads *)

Lemma disclosable_cell_end_witness : forall state region point next,
  disclosable_cell_end state region point = Some next ->
  exists cell_region bytes value,
    In (MemoryCell cell_region bytes value) state /\ Region.eqb cell_region region = true /\
    lower bytes <= point < upper bytes /\ state_disclosable value = true /\ upper bytes = next.
Proof.
  intros state region point next END. unfold disclosable_cell_end in END.
  revert next END. apply fold_left_preserves with (item_holds := fun fact => In fact state).
  - apply Forall_forall. auto.
  - discriminate.
  - intros fact held IN HELD next.
    destruct fact as [cell_region bytes value | | | | | | | | | | | | | |];
      try exact (HELD next).
    destruct (Region.eqb cell_region region && (lower bytes <=? point) &&
      (point <? upper bytes) && state_disclosable value) eqn:TEST; [| exact (HELD next)].
    intros AFTER. injection AFTER as <-.
    repeat rewrite andb_true_iff in TEST. destruct TEST as [[[SAME LOW] HIGH] DISCLOSED].
    apply Z.leb_le in LOW. apply Z.ltb_lt in HIGH.
    destruct held as [furthest |].
    + destruct (Z.max_spec furthest (upper bytes)) as [[_ ->] | [_ ->]].
      * exists cell_region, bytes, value. repeat split; auto.
      * exact (HELD furthest eq_refl).
    + exists cell_region, bytes, value. repeat split; auto.
Qed.

Lemma cell_positions_pointer_free : forall world memory region b origin bytes,
  region_location world region = Some (b, origin) ->
  region_bytes_addressable world region bytes ->
  pointer_free_bytes memory (region_address world region (lower bytes))
    (upper bytes - lower bytes) ->
  forall position, lower bytes <= position < upper bytes ->
    byte_pointer_free memory b (Ptrofs.unsigned (Ptrofs.repr (origin + position))).
Proof.
  intros world memory region b origin bytes LOCATION ADDRESSABLE FREE position BOUNDS.
  unfold region_bytes_addressable, region_address in ADDRESSABLE, FREE.
  rewrite LOCATION in ADDRESSABLE, FREE.
  pose proof (pointer_free_bytes_positions _ _ _ _ FREE (position - lower bytes)
    ltac:(lia)) as BYTE.
  replace (origin + position) with (origin + (lower bytes + (position - lower bytes))) by lia.
  rewrite (repr_subrange_start origin (lower bytes) (upper bytes - lower bytes));
    [exact BYTE | exact ADDRESSABLE | lia].
Qed.

(** Rust's [cells_disclosable] chain of cells leaves no byte of a stored pointer
    in the window it covers. *)
Lemma cells_disclosable_from_pointer_free :
  forall fuel world memory state region b origin window point,
    region_location world region = Some (b, origin) ->
    (forall cell_region bytes value,
      In (MemoryCell cell_region bytes value) state ->
      Region.eqb cell_region region = true -> state_disclosable value = true ->
      region_bytes_addressable world cell_region bytes /\
      pointer_free_bytes memory (region_address world cell_region (lower bytes))
        (upper bytes - lower bytes)) ->
    cells_disclosable_from fuel state region window point = true ->
    forall position, point <= position < upper window ->
      byte_pointer_free memory b (Ptrofs.unsigned (Ptrofs.repr (origin + position))).
Proof.
  induction fuel as [| fuel IH];
    intros world memory state region b origin window point LOCATION CELLS FROM
      position BOUNDS;
    cbn [cells_disclosable_from] in FROM;
    (destruct (upper window <=? point) eqn:DONE; [apply Z.leb_le in DONE; lia |]).
  { discriminate. }
  destruct (disclosable_cell_end state region point) as [next |] eqn:END; [| discriminate].
  destruct (disclosable_cell_end_witness _ _ _ _ END)
    as [cell_region [bytes [value [IN [SAME [[LOW HIGH] [DISCLOSED UPPER]]]]]]].
  destruct (Z_lt_dec position next) as [INSIDE | BEYOND].
  - destruct (CELLS _ _ _ IN SAME DISCLOSED) as [ADDRESSABLE FREE].
    apply Region.eqb_eq in SAME. subst cell_region.
    eapply cell_positions_pointer_free; eauto. lia.
  - eapply IH; eauto. lia.
Qed.

(** A stack load whose window [cells_disclosable] covers reads pointer-free
    bytes. *)
Lemma stack_load_pointer_free :
  forall world memory state cells ptr value size offset strict access loaded frame,
    Forall (atom_holds world memory) state ->
    (forall region bytes abstract,
      In (MemoryCell region bytes abstract) cells -> In (MemoryCell region bytes abstract) state) ->
    ptr_ty ptr = Region.stack frame ->
    pointer_state_holds world memory ptr value ->
    checked_access_for_ptr ptr offset (load_width size) strict = Some access ->
    cells_disclosable cells (Region.stack frame) (access_range access) = true ->
    load_at_offset memory value offset size = Some loaded ->
    pointer_free_bytes memory (Val.offset_ptr value (Ptrofs.repr offset)) (load_width size).
Proof.
  intros world memory state cells ptr value size offset strict access loaded frame
    FACTS MEMBER TY POINTER CHECK DISCLOSABLE LOAD.
  assert (CELLS_TY : Region.cells (ptr_ty ptr) = Some (Region.stack frame))
    by (rewrite TY; reflexivity).
  assert (ORDINARY : Region.probe_readable (ptr_ty ptr) = false) by (rewrite TY; reflexivity).
  pose proof (checked_pointer_address _ _ _ _ _ _ _ _ _ CELLS_TY CHECK POINTER) as ADDRESS.
  unfold pointer_address in ADDRESS. rewrite CELLS_TY in ADDRESS.
  destruct ADDRESS as [start [[[LOW HIGH] _] BASE]].
  destruct (checked_ordinary_access _ _ _ _ _ _ _ _ _ ORDINARY CHECK POINTER LOAD)
    as [b [address [VALUE [END PERM]]]].
  rewrite BASE in VALUE. unfold region_address in VALUE.
  destruct (region_location world (Region.stack frame)) as [[b' origin] |] eqn:LOCATION;
    [| discriminate]. injection VALUE as -> ADDRESS_EQ. subst address.
  rewrite BASE. unfold region_address. rewrite LOCATION. cbn [Val.offset_ptr].
  rewrite ptrofs_repr_add in END, PERM |- *.
  rewrite (checked_access_shape _ _ _ _ _ CHECK) in DISCLOSABLE.
  cbn [access_range] in DISCLOSABLE.
  set (window := Range (ptr_off_min ptr + offset)
    (ptr_off_max ptr + offset + load_width size)) in *.
  unfold cells_disclosable in DISCLOSABLE. cbn [negb orb Region.uninit_by_default] in DISCLOSABLE.
  assert (COVERED : forall position, lower window <= position < upper window ->
    byte_pointer_free memory b (Ptrofs.unsigned (Ptrofs.repr (origin + position)))).
  { intros position BOUNDS.
    eapply cells_disclosable_from_pointer_free;
      [exact LOCATION | | exact DISCLOSABLE | exact BOUNDS].
    intros cell_region bytes abstract IN SAME DISCLOSED.
    pose proof ((proj1 (Forall_forall _ _) FACTS) _ (MEMBER _ _ _ IN)) as CELL.
    cbn [atom_holds] in CELL. apply Region.eqb_eq in SAME. subst cell_region.
    destruct (disclosable_cell_scalar world memory (Region.stack frame) bytes abstract DISCLOSED eq_refl CELL)
      as [_ [ADDRESSABLE [_ FREE]]].
    split; [exact ADDRESSABLE | exact FREE]. }
  apply pointer_free_bytes_from_positions; [exact PERM |].
  intros delta DELTA.
  replace (origin + start + offset) with (origin + (start + offset)) in END |- * by lia.
  rewrite <- (repr_subrange_start origin (start + offset) (load_width size) delta END DELTA).
  apply COVERED. cbn [lower upper window]. lia.
Qed.

(** A defined load is an integer unless it reads a whole stored pointer;
    a failed protected read returns zero. *)
Lemma executed_load_long :
  forall world memory ptr (regs : regset) stack code_id count program regions
         size (dst base : ireg) offset strict access executable value,
    checked_access_for_ptr ptr offset (load_width size) strict = Some access ->
    pointer_state_holds world memory ptr (regs base) ->
    load_result_defined (TLS_State regs stack code_id count memory) base size offset ->
    lowers_load size dst base offset (access_kind_of ptr) executable ->
    exec_instr program executable regs stack code_id count memory regions =
      Next (nextinstr (Pregmap.set dst value regs)) stack code_id count memory ->
    (forall loaded, load_at_offset memory (regs base) offset size = Some loaded ->
      size = DBWord -> forall b o, loaded <> Vptr b o) ->
    exists n, value = Vlong n.
Proof.
  intros world memory ptr regs stack code_id count program regions size dst base offset
    strict access executable value CHECK POINTER DEFINED LOWER EXEC NOT_POINTER.
  destruct (load_at_offset memory (regs base) offset size) as [loaded |] eqn:LOAD.
  - rewrite <- (executed_load_result program regions regs stack code_id count memory
      size dst base offset _ executable value loaded LOWER EXEC LOAD).
    pose proof (DEFINED loaded LOAD) as LOADED. pose proof (NOT_POINTER loaded eq_refl) as WHOLE.
    unfold load_at_offset in LOAD.
    destruct (regs base) as [| | | | | b address]; cbn [Val.offset_ptr] in LOAD;
      try (destruct size; discriminate LOAD).
    exact (load_result_long _ _ _ _ _ LOAD LOADED WHOLE).
  - remember (access_kind_of ptr) as kind eqn:KIND in LOWER. destruct LOWER.
    + assert (ORDINARY : Region.probe_readable (ptr_ty ptr) = false).
      { rewrite Region.probe_readable_access. unfold access_kind_of in KIND.
        rewrite <- KIND. reflexivity. }
      destruct (checked_ordinary_read world memory ptr (regs base) offset size strict access
        ORDINARY CHECK POINTER) as [loaded READ].
      rewrite READ in LOAD. discriminate.
    + cbn [exec_instr] in EXEC. unfold exec_load_probe in EXEC.
      unfold load_at_offset in LOAD. rewrite LOAD in EXEC.
      apply load_value_unique in EXEC. eauto.
Qed.

(** Checked-pointer soundness for the Rust exact-range transfer.
    Definedness is an explicit premise about this one concrete load, not a
    consequence of the pointer fact. No post-load metadata is assumed.
    This lemma does not cover the pointer-free readable-window branch. *)
Theorem transfer_load_mem_checked_sound :
  forall world memory state dst base ptr size offset strict maps context after
         program regions (regs : regset) stack code_id count
         (dst_reg base_reg : ireg) executable,
    Forall (atom_holds world memory) state ->
    variable_value world base = regs base_reg ->
    find_pointer_fact state base = Some ptr ->
    frame_key_valid (ptr_ty ptr) ->
    (forall loaded,
      Region.frame (ptr_ty ptr) = None -> Region.probe_readable (ptr_ty ptr) = false ->
      Region.is (ptr_ty ptr) RegionClass.CTX = false -> size = DBWord ->
      load_at_offset memory (regs base_reg) offset size = Some loaded ->
      forall b o, loaded <> Vptr b o) ->
    load_result_defined (TLS_State regs stack code_id count memory) base_reg size offset ->
    transfer_load_mem state dst base size offset strict maps context = Some after ->
    lowers_load size dst_reg base_reg offset (access_kind_of ptr) executable ->
    exists value,
      exec_instr program executable regs stack code_id count memory regions =
        Next (nextinstr (Pregmap.set dst_reg value regs)) stack code_id count memory /\
      Forall (atom_holds (assign_value world dst value) memory) after.
Proof.
  intros world memory state dst base ptr size offset strict maps context after program regions
    regs stack code_id count dst_reg base_reg executable FACTS BASE FIND KEY KERNEL DEFINED
    TRANSFER LOWER.
  assert (CHECKED : exists access,
    checked_access_for_ptr ptr offset (load_width size) strict = Some access).
  { unfold transfer_load_mem, checked_access_range in TRANSFER. rewrite FIND in TRANSFER.
    destruct (checked_access_for_ptr ptr offset (load_width size) strict) as [access |]
      eqn:CHECK; [eauto |].
    cbn [filter_context_access filter_special_access] in TRANSFER.
    unfold window_load_allowed in TRANSFER. rewrite FIND in TRANSFER. discriminate. }
  destruct CHECKED as [access CHECK].
  assert (POINTER : pointer_state_holds world memory ptr (regs base_reg)).
  { rewrite <- BASE.
    pose proof (find_pointer_fact_present state base ptr FIND) as IN.
    apply (proj1 (Forall_forall _ _) FACTS) in IN. exact IN. }
  destruct (checked_load_execution world memory ptr regs stack code_id count
    program regions size dst_reg base_reg offset strict access executable CHECK POINTER DEFINED LOWER)
    as [value [BOUNDS EXEC]].
  exists value. split; [exact EXEC |].
  eapply transfer_load_mem_preserves;
    [exact FACTS | exact FIND | eapply lowered_load_not_context; exact LOWER
    | exact BOUNDS | | | | exact TRANSFER].
  - intros loaded LOAD. rewrite BASE in LOAD.
    eapply executed_load_result; eauto.
  - intros region bytes abstract REGION EXACT RANGE CELL.
    eapply executed_load_cell_holds; eauto. exact (proj1 BOUNDS).
  - intros access' CHECK' SCALAR. rewrite CHECK in CHECK'. injection CHECK' as <-.
    assert (PTR : access_ptr access = ptr) by (rewrite (checked_access_shape _ _ _ _ _ CHECK); reflexivity).
    unfold loads_scalar, stack_frame_of in SCALAR. rewrite PTR in SCALAR.
    destruct (Region.frame (ptr_ty ptr)) as [frame |] eqn:FRAME.
    + assert (TY : ptr_ty ptr = Region.stack frame).
      { unfold frame_key_valid in KEY. rewrite FRAME in KEY. exact KEY. }
      destruct (checked_ordinary_read world memory ptr (regs base_reg) offset size strict access
        ltac:(rewrite TY; reflexivity) CHECK POINTER) as [loaded LOAD].
      pose proof (stack_load_pointer_free world memory state (apply_havoc_with_size state dst size)
        ptr (regs base_reg) size offset strict access loaded frame FACTS
        ltac:(intros r b v IN; apply (load_havoc_cells state dst size []);
          [intros fact [] | rewrite app_nil_r; exact IN])
        TY POINTER CHECK SCALAR LOAD) as FREE.
      rewrite <- (executed_load_result program regions regs stack code_id count memory
        size dst_reg base_reg offset _ executable value loaded LOWER EXEC LOAD).
      pose proof (DEFINED loaded LOAD) as LOADED.
      unfold load_at_offset in LOAD.
      destruct (regs base_reg) as [| | | | | b address]; cbn [Val.offset_ptr] in LOAD, FREE;
        try (destruct size; discriminate LOAD).
      exact (load_pointer_free_long _ _ _ _ _ LOAD FREE LOADED).
    + eapply executed_load_long; [exact CHECK | exact POINTER | exact DEFINED | exact LOWER
        | exact EXEC |].
      intros loaded LOAD DOUBLE b o. subst size.
      destruct (Region.probe_readable (ptr_ty ptr)) eqn:PROBE; [discriminate SCALAR |].
      exact (KERNEL loaded eq_refl eq_refl (lowered_load_not_context _ _ _ _ _ _ LOWER)
        eq_refl LOAD b o).
Qed.

Lemma transfer_load_local_initialized :
  forall (attrs : load_attrs) regions before concrete dst base dst_value size offset strict
         maps context after,
    base <> RAX ->
    concretizes attrs regions before concrete ->
    no_uninit_memory_cells (facts before) ->
    load_initialized_if_unmodeled before concrete base size offset ->
    transfer_load_local before dst base dst_value size offset strict maps context = Some after ->
    match concrete with
    | TLS_State regs _ _ _ memory =>
        forall loaded,
          load_at_offset memory (regs base) offset size = Some loaded ->
          initialized_bytes memory (Val.offset_ptr (regs base) (Ptrofs.repr offset))
            (load_width size)
    end.
Proof.
  intros attrs regions before concrete dst base dst_value size offset strict maps context after
    BASE_REGISTER CONCRETE VALID UNMODELED TRANSFER.
  destruct concrete as [regs stack code_id count memory].
  destruct CONCRETE as [world [REGISTERS [FACTS [_ [_ [[_ INITIALIZED] _]]]]]].
  intros loaded LOAD.
  unfold transfer_load_local in TRANSFER.
  destruct (ensure_defined (facts before) (register_name before base)); try discriminate.
  destruct (transfer_load_mem (facts before) dst_value (register_name before base)
    size offset strict maps context) as [post |] eqn:MEMORY; try discriminate.
  destruct (find_pointer_fact (facts before) (register_name before base))
    as [ptr |] eqn:FIND.
  - destruct (load_initialization_modeled ptr) eqn:MODELED;
      [| exact (UNMODELED ptr loaded FIND MODELED LOAD)].
    rewrite <- (REGISTERS base BASE_REGISTER) in LOAD |- *.
    unfold load_initialization_modeled in MODELED.
    destruct (Region.uninit_by_default (ptr_ty ptr)) eqn:STACK.
    + destruct (Region.frame (ptr_ty ptr)) as [frame |]; [| discriminate].
      apply Region.eqb_eq in MODELED.
      eapply stack_load_initialized; eauto.
    + apply negb_true_iff in MODELED.
      eapply non_stack_load_initialized; eauto.
      exact ((proj1 (Forall_forall _ _) FACTS) _ (find_pointer_fact_present _ _ _ FIND)).
  - rewrite <- (REGISTERS base BASE_REGISTER) in LOAD |- *.
    unfold transfer_load_mem, checked_access_range in MEMORY. rewrite FIND in MEMORY.
    cbn [filter_context_access filter_special_access] in MEMORY.
    destruct (window_load_allowed (facts before) (register_name before base)
      offset size strict) eqn:ALLOWED; try discriminate.
    unfold window_load_allowed in ALLOWED. rewrite FIND in ALLOWED.
    apply andb_true_iff in ALLOWED as [_ COVER].
    eapply readable_window_covers_initialized; eauto.
Qed.

Lemma load_result_defined_of_initialized : forall concrete base size offset,
  load_fragments_defined concrete base size offset ->
  match concrete with
  | TLS_State regs _ _ _ memory =>
      forall loaded,
        load_at_offset memory (regs base) offset size = Some loaded ->
        initialized_bytes memory (Val.offset_ptr (regs base) (Ptrofs.repr offset))
          (load_width size)
  end ->
  load_result_defined concrete base size offset.
Proof.
  intros [regs stack code_id count memory] base size offset FRAGMENTS INITIALIZED
    loaded LOAD.
  exact (FRAGMENTS loaded LOAD (INITIALIZED loaded LOAD)).
Qed.

(** ** Spill tracking around loads *)

(** The local transfer with its concrete witness exposed: the loaded value
    and the world in which the post-state holds. *)
Lemma transfer_load_local_execution :
  forall world memory program regions dst base dst_value size offset strict_alignment maps context
         before after (regs : regset) stack code_id count kind executable,
    (forall reg, reg <> RAX -> variable_value world (register_name before reg) = regs reg) ->
    Forall (atom_holds world memory) (facts before) ->
    Forall memory_coordinates_valid (facts before) ->
    load_outside_stack_scalar before (TLS_State regs stack code_id count memory) base size offset ->
    load_result_defined (TLS_State regs stack code_id count memory) base size offset ->
    transfer_load_local before dst base dst_value size offset strict_alignment maps context = Some after ->
    load_access_kind before base size offset strict_alignment maps context = Some kind ->
    lowers_load size dst base offset kind executable ->
    exists value,
      register_name after = set_register_name (register_name before) dst dst_value /\
      exec_instr program executable regs stack code_id count memory regions =
        Next (nextinstr (Pregmap.set dst value regs)) stack code_id count memory /\
      Forall (atom_holds (assign_value world dst_value value) memory) (facts after).
Proof.
  intros world memory program regions dst base dst_value size offset strict_alignment maps context
    before after regs stack code_id count kind executable REGISTERS FACTS COORDINATES KERNEL
    DEFINED TRANSFER KIND LOWER.
  unfold transfer_load_local in TRANSFER.
  destruct (ensure_defined (facts before) (register_name before base));
    try discriminate.
  destruct (transfer_load_mem (facts before) dst_value (register_name before base)
    size offset strict_alignment maps context) as [post |] eqn:MEMORY; try discriminate.
  inversion TRANSFER; subst after; clear TRANSFER. cbn [register_name facts].
  destruct (find_pointer_fact (facts before) (register_name before base))
    as [ptr |] eqn:FIND.
  - unfold load_access_kind in KIND.
    destruct (checked_access_range (facts before) (register_name before base)
      offset (load_width size) strict_alignment maps context) as [access|] eqn:ACCESS.
    2: { unfold window_load_allowed in KIND. rewrite FIND in KIND. discriminate. }
    inversion KIND; subst kind.
    unfold checked_access_range in ACCESS. rewrite FIND in ACCESS.
    apply filter_special_access_some in ACCESS.
    apply filter_context_access_some in ACCESS.
    rewrite (checked_access_shape _ _ _ _ _ ACCESS) in LOWER.
    cbn [access_ptr] in LOWER.
    destruct (transfer_load_mem_checked_sound world memory (facts before) dst_value
      (register_name before base) ptr size offset strict_alignment maps context post program regions
      regs stack code_id count dst base executable FACTS (REGISTERS base (lowers_load_base _ _ _ _ _ _ LOWER)) FIND
      ltac:(exact ((proj1 (Forall_forall _ _) COORDINATES) _ (find_pointer_fact_present _ _ _ FIND)))
      (fun loaded FRAME PROBE NONCTX DOUBLE LOAD =>
        KERNEL ptr loaded FIND FRAME PROBE NONCTX DOUBLE LOAD)
      DEFINED MEMORY LOWER)
      as [value [EXEC POST]].
    exists value. auto.
  - unfold load_access_kind, checked_access_range in KIND. rewrite FIND in KIND.
    destruct (window_load_allowed (facts before) (register_name before base)
      offset size strict_alignment) eqn:ALLOWED; try discriminate.
    inversion KIND; subst kind. inversion LOWER; subst executable.
    unfold transfer_load_mem, checked_access_range in MEMORY.
    rewrite FIND, ALLOWED in MEMORY. inversion MEMORY; subst post.
    unfold window_load_allowed in ALLOWED. rewrite FIND in ALLOWED.
    apply andb_true_iff in ALLOWED as [_ COVER].
    destruct (readable_window_covers_load world memory (facts before)
      (register_name before base) offset size FACTS COVER) as [loaded LOAD].
    rewrite REGISTERS in LOAD by exact (lowers_load_base _ _ _ _ _ _ LOWER).
    assert (BOUNDS : load_bounds size (load_value_casting loaded)).
    { eapply load_bounds_result; [exact LOAD |].
      eapply load_result_runtime; [exact LOAD | exact (DEFINED loaded LOAD)]. }
    exists (load_value_casting loaded). split; [reflexivity | split].
    + cbn [exec_instr]. unfold exec_load, Pregmap.get.
      unfold load_at_offset in LOAD.
      destruct (regs base); try (destruct size; discriminate LOAD).
      now rewrite LOAD.
    + apply havoc_holds; assumption.
Qed.

Lemma exact_cell_pointer : forall state base offset width region bytes,
  SpillProvenance.exact_cell state base offset width = Some (region, bytes) ->
  exists ptr, find_pointer_fact state base = Some ptr.
Proof.
  intros state base offset width region bytes EXACT.
  unfold SpillProvenance.exact_cell, SpillProvenance.resolve_write in EXACT.
  destruct (find_pointer_fact state base) as [ptr |]; [eauto | discriminate].
Qed.

(** A checked full-width load of an exact cell reads the bytes a [MemoryEq]
    on that cell describes. Cells exclude probe reads, so it cannot fail. *)
Lemma exact_cell_load_memory_eq :
  forall world memory state base region bytes offset size strict maps context access,
    Forall (atom_holds world memory) state ->
    SpillProvenance.exact_cell state base offset 8 = Some (region, bytes) ->
    checked_access_range state base offset (load_width size) strict maps context = Some access ->
    load_width size = 8 ->
    exists loaded,
      load_at_offset memory (variable_value world base) offset size = Some loaded /\
      memory_eq_holds memory (region_address world region (lower bytes))
        (load_value_casting loaded).
Proof.
  Local Transparent Mem.loadbytes.
  intros world memory state base region bytes offset size strict maps context access
    FACTS EXACT ACCESS WIDTH.
  unfold SpillProvenance.exact_cell, SpillProvenance.resolve_write in EXACT.
  destruct (find_pointer_fact state base) as [ptr |] eqn:FIND; try discriminate.
  destruct (Region.cells (ptr_ty ptr)) as [cells |] eqn:REGION; try discriminate.
  destruct (Z.eqb (ptr_off_min ptr) (ptr_off_max ptr)) eqn:SINGLE; try discriminate.
  destruct (i64_checked_add (ptr_off_min ptr) offset) as [start |] eqn:START;
    try discriminate.
  destruct (i64_checked_add start 8) as [finish |]; try discriminate.
  inversion EXACT; subst cells bytes; clear EXACT.
  assert (START_EQ : start = ptr_off_min ptr + offset).
  { unfold i64_checked_add in START. destruct (_ && _); congruence. }
  unfold checked_access_range in ACCESS. rewrite FIND in ACCESS.
  apply filter_special_access_some, filter_context_access_some in ACCESS.
  assert (POINTER : pointer_state_holds world memory ptr (variable_value world base)).
  { pose proof (find_pointer_fact_present state base ptr FIND) as IN.
    apply (proj1 (Forall_forall _ _) FACTS) in IN. exact IN. }
  destruct (checked_ordinary_read world memory ptr (variable_value world base) offset size
    strict access (cells_not_probe_readable _ _ REGION) ACCESS POINTER) as [loaded LOAD].
  exists loaded. split; [exact LOAD |].
  pose proof (checked_pointer_address world memory ptr _ region offset _ strict access
    REGION ACCESS POINTER) as ADDRESS.
  rewrite (exact_pointer_load_address world memory ptr _ region offset size REGION ADDRESS
    (proj1 (Z.eqb_eq _ _) SINGLE)) in LOAD.
  cbn [lower]. rewrite START_EQ.
  destruct size; cbn in WIDTH; try discriminate.
  cbn [load] in LOAD. unfold loadv_unaligned in LOAD. unfold memory_eq_holds.
  destruct (region_address world region (ptr_off_min ptr + offset)); try discriminate.
  unfold Mem.loadbytes in LOAD.
  destruct (Mem.range_perm_dec _ _ _ _ _ _); try discriminate.
  now inversion LOAD.
Qed.

Lemma memory_eq_holds_unique : forall memory address x y,
  memory_eq_holds memory address x -> memory_eq_holds memory address y -> x = y.
Proof.
  intros memory [] x y; cbn [memory_eq_holds]; congruence || contradiction.
Qed.

Lemma from_entry_binding : forall state item,
  In item (SpillProvenance.entries (SpillProvenance.from_entry state)) ->
  In (MemoryEq (SpillProvenance.binding_region item)
    (lower (SpillProvenance.binding_range item)) (SpillProvenance.binding_value item)) state.
Proof.
  intros state item IN.
  unfold SpillProvenance.from_entry in IN. cbn [SpillProvenance.entries] in IN.
  apply in_flat_map in IN as [fact [FACT ITEM]].
  destruct fact; try contradiction.
  destruct (i64_checked_add offset 8); [| contradiction].
  destruct ITEM as [<- | []]. exact FACT.
Qed.

Lemma holder_binding : forall items region bytes value,
  SpillProvenance.holder items region bytes = Some value ->
  exists item, In item items /\ SpillProvenance.binding_region item = region /\
    lower (SpillProvenance.binding_range item) = lower bytes /\
    SpillProvenance.binding_value item = value.
Proof.
  intros items region bytes value HOLDER. unfold SpillProvenance.holder in HOLDER.
  destruct (find _ items) as [item |] eqn:FIND; inversion HOLDER; subst value.
  apply find_some in FIND as [IN MATCH].
  apply andb_true_iff in MATCH as [[REGION LOWER]%andb_true_iff _].
  exists item. split; [exact IN |]. split; [now apply Region.eqb_eq |].
  split; [now apply Z.eqb_eq | reflexivity].
Qed.

(** Soundness of the load transition INCLUDING spill tracking and cleanup.
    Beyond the local theorem's premises, it needs Rust's SSA freshness
    [fresh_in_facts]: otherwise a pre-state [MemoryEq] naming [dst_value]
    would be re-materialized after [dst_value] is reassigned. *)
Theorem transfer_load_mem_sound :
  forall (attrs : load_attrs) program regions dst base dst_value size offset strict_alignment maps context
         before after concrete kind executable,
    fresh_destination before dst dst_value ->
    fresh_in_facts before dst_value ->
    concretizes attrs regions before concrete ->
    no_uninit_memory_cells (facts before) ->
    Forall memory_coordinates_valid (facts before) ->
    load_initialized_if_unmodeled before concrete base size offset ->
    load_fragments_defined concrete base size offset ->
    load_outside_stack_scalar before concrete base size offset ->
    transfer_load before dst base dst_value size offset strict_alignment maps context = Some after ->
    load_access_kind before base size offset strict_alignment maps context = Some kind ->
    lowers_load size dst base offset kind executable ->
    exists concrete',
      instruction_step regions program executable concrete concrete' /\
      concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions dst base dst_value size offset strict_alignment maps context
    before after concrete kind executable FRESH FRESH_FACTS CONCRETE VALID COORDINATES UNMODELED
    FRAGMENTS KERNEL TRANSFER KIND LOWER.
  assert (DEFINED : forall local,
    transfer_load_local before dst base dst_value size offset strict_alignment maps context =
      Some local ->
    load_result_defined concrete base size offset).
  { intros local LOCAL. apply load_result_defined_of_initialized; [exact FRAGMENTS |].
    eapply transfer_load_local_initialized; eauto.
    exact (lowers_load_base _ _ _ _ _ _ LOWER). }
  destruct concrete as [regs stack code_id count memory].
  destruct CONCRETE as [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]].
  unfold transfer_load, transfer_at_entry, transfer_with_provenance in TRANSFER.
  destruct (SpillProvenance.update (SpillProvenance.from_entry (facts before)) (facts before)
    (SpillProvenance.LoadMem (register_name before base) dst_value offset (load_width size)))
    as [provenance refilled] eqn:UPDATE.
  remember (SpillProvenance.from_entry (facts before)) as entry eqn:ENTRY_DEF in UPDATE.
  destruct (transfer_load_local before dst base dst_value size offset strict_alignment maps context)
    as [local |] eqn:LOCAL; try discriminate.
  cbn [option_map fst] in TRANSFER. inversion TRANSFER; subst after; clear TRANSFER.
  specialize (DEFINED local eq_refl).
  destruct (transfer_load_local_execution world memory program regions dst base dst_value size
    offset strict_alignment maps context before local regs stack code_id count kind executable
    REGISTERS FACTS COORDINATES KERNEL DEFINED LOCAL KIND LOWER) as [value [NAMES [EXEC POST]]].
  exists (TLS_State (nextinstr (Pregmap.set dst value regs)) stack code_id count memory).
  split; [exact EXEC |].
  rewrite NAMES.
  eapply concretizes_register_update;
    [exact FRESH | exact REGISTERS | exact POLICY | exact LAYOUT |exact ENVIRONMENT |].
  set (updated := assign_value world dst_value value).
  assert (ENTRY : forall item,
    In item (SpillProvenance.entries entry) ->
    Nat.eqb dst_value (SpillProvenance.binding_value item) = false /\
    atom_holds world memory (MemoryEq (SpillProvenance.binding_region item)
      (lower (SpillProvenance.binding_range item)) (SpillProvenance.binding_value item))).
  { intros item IN. rewrite ENTRY_DEF in IN. apply from_entry_binding in IN.
    split; [exact (proj1 (Forall_forall _ _) FRESH_FACTS _ IN) |].
    exact (proj1 (Forall_forall _ _) FACTS _ IN). }
  assert (ENTRY_UPDATED : forall item,
    In item (SpillProvenance.entries entry) ->
    atom_holds updated memory (MemoryEq (SpillProvenance.binding_region item)
      (lower (SpillProvenance.binding_range item)) (SpillProvenance.binding_value item))).
  { intros item IN. destruct (ENTRY item IN) as [MENTIONS HOLDS].
    apply atom_holds_assign; [exact MENTIONS | exact HOLDS]. }
  cbn [SpillProvenance.update] in UPDATE.
  destruct (Z.eqb (load_width size) 8) eqn:WIDTH;
    [| inversion UPDATE; subst; apply materialize_holds; assumption].
  destruct (SpillProvenance.exact_cell (facts before) (register_name before base) offset 8)
    as [[region bytes] |] eqn:EXACT;
    [| inversion UPDATE; subst; apply materialize_holds; assumption].
  apply Z.eqb_eq in WIDTH.
  destruct (exact_cell_pointer _ _ _ _ _ _ EXACT) as [ptr FIND].
  unfold load_access_kind in KIND.
  destruct (checked_access_range (facts before) (register_name before base)
    offset (load_width size) strict_alignment maps context) as [access |] eqn:ACCESS.
  2: { unfold window_load_allowed in KIND. rewrite FIND in KIND. discriminate. }
  destruct (exact_cell_load_memory_eq world memory (facts before) (register_name before base)
    region bytes offset size strict_alignment maps context access FACTS EXACT ACCESS WIDTH)
    as [loaded [LOAD MEMORY_EQ]].
  rewrite REGISTERS in LOAD by exact (lowers_load_base _ _ _ _ _ _ LOWER).
  pose proof (executed_load_result program regions regs stack code_id count memory size dst base
    offset kind executable value loaded LOWER EXEC LOAD) as LOADED.
  subst value.
  assert (LOADED_EQ : atom_holds updated memory (MemoryEq region (lower bytes) dst_value)).
  { cbn [atom_holds]. unfold updated.
    cbn [region_address assign_value region_location].
    rewrite variable_value_assign_same. exact MEMORY_EQ. }
  inversion UPDATE; subst provenance refilled; clear UPDATE.
  assert (MATERIALIZED : forall bindings disturbed, Forall (atom_holds updated memory)
    (SpillProvenance.materialize (SpillProvenance.Provenance
      (SpillProvenance.keep_disjoint (SpillProvenance.entries entry) region bytes ++
       [SpillProvenance.Binding region bytes dst_value]) bindings disturbed) (facts local))).
  { intros bindings disturbed. apply materialize_holds; [exact POST |].
    intros item IN. cbn [SpillProvenance.entries] in IN.
    apply in_app_or in IN as [IN | [<- | []]]; [| exact LOADED_EQ].
    apply filter_In in IN as [IN _]. exact (ENTRY_UPDATED item IN). }
  destruct (SpillProvenance.holder (SpillProvenance.entries entry) region bytes)
    as [held |] eqn:HOLDER; cbn [option_map]; [| apply MATERIALIZED].
  apply Forall_app. split; [apply MATERIALIZED |].
  destruct (holder_binding _ _ _ _ HOLDER) as [item [IN [<- [LOWER_EQ <-]]]].
  destruct (ENTRY item IN) as [MENTIONS HOLDS].
  cbn [atom_holds] in HOLDS. rewrite LOWER_EQ in HOLDS.
  constructor; [| constructor].
  cbn [atom_holds eval_term]. unfold updated.
  rewrite variable_value_assign_same, variable_value_assign_other by exact MENTIONS.
  split.
  - eapply load_result_runtime; [exact LOAD | exact (DEFINED loaded LOAD)].
  - exact (memory_eq_holds_unique _ _ _ _ MEMORY_EQ HOLDS).
Qed.

(** ** [ld_imm64] family *)

Lemma concretizes_nextinstr :
  forall (attrs : load_attrs) regions abstract (regs : regset) stack code_id count memory,
    concretizes attrs regions abstract (TLS_State regs stack code_id count memory) ->
    concretizes attrs regions abstract (TLS_State (nextinstr regs) stack code_id count memory).
Proof.
  intros attrs regions abstract regs stack code_id count memory [world [REGISTERS REST]].
  exists world. split; [| exact REST].
  intros reg NOT_AUX. rewrite REGISTERS by exact NOT_AUX. unfold nextinstr.
  now rewrite Pregmap.gso by discriminate.
Qed.

(** The loader-supplied address resolves to a value satisfying the pushed
    pointer description. *)
Definition ld_imm64_pointer_resolved (world : interpretation) (memory : mem)
    (regions : list addr_region) (ptr : ptr_state) (executable : instruction) : Prop :=
  match executable with
  | Plddw _ _ lo hi =>
      exists value, cast_i2p (Int64.ofwords hi lo) regions = Some value /\
        value_holds world memory (Ptr ptr) value
  | _ => False
  end.

Lemma loaded_pointer_fields_well_formed : forall ty offset size perm,
  0 <= offset <= Int.max_unsigned ->
  0 <= size <= Int.max_unsigned ->
  pointer_fields_well_formed (loaded_pointer ty offset size perm).
Proof.
  intros ty offset size perm OFFSET SIZE.
  unfold pointer_fields_well_formed, loaded_pointer. cbn.
  change Int.max_unsigned with 4294967295 in *.
  change Int64.min_signed with (-9223372036854775808).
  change Int64.max_signed with 9223372036854775807.
  change Int64.modulus with 18446744073709551616.
  change Int.modulus with 4294967296.
  lia.
Qed.

(** A pointer pushed by an [ld_imm64] arm describes [offset] within an
    allocation of its region, which backs its [size] bytes. *)
Lemma loaded_pointer_holds : forall world memory ty offset size perm b origin,
  Region.cells ty = None ->
  Region.eqb ty (Region.btf None) = false ->
  Region.probe_readable ty = false ->
  Region.grows_down ty = false ->
  region_allocation world ty b origin ->
  0 <= offset <= Int.max_unsigned ->
  0 <= size <= Int.max_unsigned ->
  (0 < size ->
    0 <= origin /\ origin + size <= Ptrofs.modulus /\
    Mem.range_perm memory b origin (origin + size) Cur
      (match perm with Read => Memtype.Readable | _ => Writable end)) ->
  value_holds world memory (Ptr (loaded_pointer ty offset size perm))
    (Vptr b (Ptrofs.repr (origin + offset))).
Proof.
  intros world memory ty offset size perm b origin CELLS UNTYPED ORDINARY UP
    REGION OFFSET SIZE BACKED.
  split; [now apply loaded_pointer_fields_well_formed |].
  split.
  { unfold pointer_region_holds, pointer_address. cbn [loaded_pointer ptr_ty ptr_nullability].
    rewrite UNTYPED, CELLS.
    exists b, origin, offset. split; [exact REGION |]. split; [| reflexivity].
    unfold pointer_offset_holds. cbn. split; [lia | exists 0; lia]. }
  split.
  { unfold pointer_permissions_holds. cbn [loaded_pointer ptr_ty ptr_nullability].
    rewrite ORDINARY. unfold pointer_access_holds.
    intros k width WIDTH WINDOW. unfold verified_window in WINDOW.
    cbn [loaded_pointer ptr_ty ptr_size ptr_off_min ptr_off_max ptr_end_min] in WINDOW.
    rewrite UP in WINDOW. cbn [lower upper] in WINDOW.
    destruct WINDOW as [LOW [HIGH | [bound [NONE _]]]]; [| discriminate NONE].
    destruct (BACKED ltac:(lia)) as [ORIGIN [END PERM]].
    cbn [loaded_pointer ptr_permission]. cbv zeta.
    rewrite ptrofs_repr_add, Ptrofs.unsigned_repr
      by (unfold Ptrofs.max_unsigned; lia).
    split; [lia |]. intros address RANGE. apply PERM. lia. }
  split; [exact I | constructor].
Qed.

(** The loader resolution and map value backing named by [environment_holds]
    establish the description each pointer-producing arm pushes. *)
Lemma ld_imm64_pointer_resolves :
  forall world memory attrs regions load ptr dst executable,
    environment_holds world memory attrs regions ->
    ld_imm64_pointer (attr_maps attrs) load = Some ptr ->
    lowers_ld_imm64 (attr_loader attrs) dst load executable ->
    ld_imm64_pointer_resolved world memory regions ptr executable.
Proof.
  intros world memory attrs regions load ptr dst executable
    [[MAPS _] [MAP [MAP_VALUE SUBPROG]]] POINTER LOWER.
  destruct LOWER as [lo hi | id ty lo hi _ LOADED
    | id offset ty lo hi base size _ LOADED OFFSET IMM | id lo hi LOADED];
    cbn [ld_imm64_pointer] in POINTER; try discriminate POINTER;
    unfold ld_imm64_pointer_resolved.
  - injection POINTER as <-.
    destruct (MAP _ _ LOADED) as [b [origin [REGION CAST]]].
    exists (Vptr b (Ptrofs.repr origin)). split; [exact CAST |].
    replace (Ptrofs.repr origin) with (Ptrofs.repr (origin + 0)) by (f_equal; lia).
    apply loaded_pointer_holds; try reflexivity; try exact REGION;
      change Int.max_unsigned with 4294967295; lia.
  - destruct (MAP_VALUE _ _ _ LOADED) as [b [origin [REGION [SIZE CAST]]]].
    exists (Vptr b (Ptrofs.repr (origin + offset))).
    split; [rewrite IMM; apply CAST; exact OFFSET |].
    destruct (map_value_specs (attr_maps attrs) id) as [spec |] eqn:SPEC;
      injection POINTER as <-.
    + destruct (MAPS _ _ SPEC) as [SPEC_SIZE ALLOCATIONS].
      apply loaded_pointer_holds; try reflexivity; try exact REGION; try lia.
      intros _. exact (ALLOCATIONS _ _ REGION).
    + apply loaded_pointer_holds; try reflexivity; try exact REGION;
        change Int.max_unsigned with 4294967295 in *; lia.
  - injection POINTER as <-.
    destruct (SUBPROG _ _ LOADED) as [b [origin [REGION CAST]]].
    exists (Vptr b (Ptrofs.repr origin)). split; [exact CAST |].
    replace (Ptrofs.repr origin) with (Ptrofs.repr (origin + 0)) by (f_equal; lia).
    apply loaded_pointer_holds; try reflexivity; try exact REGION;
      change Int.max_unsigned with 4294967295; lia.
Qed.

Lemma lowers_ld_imm64_pointer_instruction : forall loader maps dst load ptr executable,
  ld_imm64_pointer maps load = Some ptr ->
  lowers_ld_imm64 loader dst load executable ->
  exists ty lo hi, executable = Plddw ty dst lo hi /\ ty <> PSEUDO_Constant.
Proof.
  intros loader maps dst load ptr executable POINTER LOWER.
  inversion LOWER; subst; try discriminate POINTER;
    do 3 eexists; split; try reflexivity; intuition (subst; discriminate).
Qed.

(** The pointer-producing arms execute to the pushed pointer, for the
    interpretation witnessing the pre-state, once the resolved address
    satisfies the pushed description. *)
Lemma ld_imm64_pointer_execution :
  forall world memory maps before after load ptr dst dst_value executable
         regions program (regs : regset) stack code_id count,
    Forall (atom_holds world memory) (facts before) ->
    transfer_ld_imm64_local maps before dst dst_value load = Some after ->
    ld_imm64_pointer maps load = Some ptr ->
    (exists ty lo hi, executable = Plddw ty dst lo hi /\ ty <> PSEUDO_Constant) ->
    ld_imm64_pointer_resolved world memory regions ptr executable ->
    exists value,
      register_name after = set_register_name (register_name before) dst dst_value /\
      instruction_step regions program executable (TLS_State regs stack code_id count memory)
        (TLS_State (nextinstr (nextinstr (Pregmap.set dst value regs))) stack code_id count memory) /\
      Forall (atom_holds (assign_value world dst_value value) memory) (facts after).
Proof.
  intros world memory maps before after load ptr dst dst_value executable
    regions program regs stack code_id count FACTS TRANSFER POINTER TYPE RESOLVED.
  assert (POST : transfer_ld_imm64 maps (facts before) dst_value load =
    Some (apply_havoc (facts before) dst_value ++ [AbstractValue (Var dst_value) (Ptr ptr)])).
  { unfold transfer_ld_imm64_local, transfer_ld_imm64 in TRANSFER |- *.
    destruct load; cbn [ld_imm64_pointer] in POINTER; try discriminate POINTER;
      injection POINTER as <-; cbn [ld_imm64_pointer option_map] in TRANSFER |- *;
      try destruct (map_is_proof_family maps id); cbn [option_map] in TRANSFER;
      try discriminate TRANSFER; reflexivity. }
  unfold transfer_ld_imm64_local in TRANSFER. rewrite POST in TRANSFER.
  cbn [option_map] in TRANSFER. inversion TRANSFER; subst after; clear TRANSFER.
  destruct TYPE as [ty [lo [hi [EXEC CONSTANT]]]]. subst executable.
  destruct RESOLVED as [value [CAST HOLDS]].
  exists value. split; [reflexivity |]. split.
  - unfold instruction_step. cbn [exec_instr]. unfold exec_lddw. cbv zeta.
    destruct ty; try contradiction; rewrite CAST; reflexivity.
  - cbn [facts]. apply Forall_app. split.
    + apply apply_havoc_holds; [exact FACTS |].
      destruct HOLDS as [_ [_ [_ [_ RUNTIME]]]]. exact RUNTIME.
    + constructor; [| constructor]. cbn [atom_holds eval_term assign_value variable_value].
      destruct (Nat.eq_dec dst_value dst_value); [exact HOLDS | contradiction].
Qed.

Lemma ld_imm64_constant_execution :
  forall world memory maps loader before after imm dst dst_value executable
         regions program (regs : regset) stack code_id count,
    Forall (atom_holds world memory) (facts before) ->
    transfer_ld_imm64_local maps before dst dst_value (LdImm64.LoadImm64 imm) = Some after ->
    lowers_ld_imm64 loader dst (LdImm64.LoadImm64 imm) executable ->
    exists value,
      register_name after = set_register_name (register_name before) dst dst_value /\
      instruction_step regions program executable (TLS_State regs stack code_id count memory)
        (TLS_State (nextinstr (nextinstr (Pregmap.set dst value regs))) stack code_id count memory) /\
      Forall (atom_holds (assign_value world dst_value value) memory) (facts after).
Proof.
  intros world memory maps loader before after imm dst dst_value executable
    regions program regs stack code_id count FACTS TRANSFER LOWER.
  inversion LOWER as [lo hi IMM EXEC | | |]; subst executable imm.
  unfold transfer_ld_imm64_local, transfer_ld_imm64, apply_assignment in TRANSFER.
  cbn [option_map] in TRANSFER. inversion TRANSFER; subst after; clear TRANSFER.
  exists (Vlong (Int64.ofwords hi lo)). split; [reflexivity |]. split; [reflexivity |].
  cbn [facts].
  replace (Vlong (Int64.ofwords hi lo))
    with (Vlong (Int64.repr (Int64.signed (Int64.ofwords hi lo))))
    by now rewrite Int64.repr_signed.
  apply assignment_const_holds; [exact FACTS | apply Int64.signed_range].
Qed.

Lemma transfer_ld_imm64_local_execution :
  forall world memory (attrs : load_attrs) regions before after load dst dst_value executable
         program (regs : regset) stack code_id count,
    Forall (atom_holds world memory) (facts before) ->
    environment_holds world memory attrs regions ->
    transfer_ld_imm64_local (attr_maps attrs) before dst dst_value load = Some after ->
    lowers_ld_imm64 (attr_loader attrs) dst load executable ->
    exists value,
      register_name after = set_register_name (register_name before) dst dst_value /\
      instruction_step regions program executable (TLS_State regs stack code_id count memory)
        (TLS_State (nextinstr (nextinstr (Pregmap.set dst value regs))) stack code_id count memory) /\
      Forall (atom_holds (assign_value world dst_value value) memory) (facts after).
Proof.
  intros world memory attrs regions before after load dst dst_value executable
    program regs stack code_id count FACTS ENVIRONMENT TRANSFER LOWER.
  destruct (ld_imm64_pointer (attr_maps attrs) load) as [ptr |] eqn:POINTER.
  - eapply ld_imm64_pointer_execution; eauto.
    + eapply lowers_ld_imm64_pointer_instruction; eauto.
    + eapply ld_imm64_pointer_resolves; eauto.
  - destruct load; try discriminate POINTER.
    eapply ld_imm64_constant_execution; eauto.
Qed.

(** Soundness of every [ld_imm64] form. *)
Theorem transfer_ld_imm64_sound :
  forall (attrs : load_attrs) program regions before after concrete dst dst_value load
         executable,
    fresh_destination before dst dst_value ->
    concretizes attrs regions before concrete ->
    transfer_ld_imm64_local (attr_maps attrs) before dst dst_value load = Some after ->
    lowers_ld_imm64 (attr_loader attrs) dst load executable ->
    exists concrete',
      instruction_step regions program executable concrete concrete' /\
      concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions before after concrete dst dst_value load executable
    FRESH CONCRETE TRANSFER LOWER.
  destruct concrete as [regs stack code_id count memory].
  destruct CONCRETE as [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]].
  destruct (transfer_ld_imm64_local_execution world memory attrs regions before after load
    dst dst_value executable program regs stack code_id count FACTS ENVIRONMENT TRANSFER LOWER)
    as [value [NAMES [EXEC POST]]].
  eexists. split; [exact EXEC |].
  destruct after as [post names]. cbn [register_name facts] in NAMES, POST. subst names.
  apply concretizes_nextinstr.
  eapply concretizes_register_update;
    [exact FRESH | exact REGISTERS | exact POLICY | exact LAYOUT | exact ENVIRONMENT | exact POST].
Qed.

End MemoryLoad.
