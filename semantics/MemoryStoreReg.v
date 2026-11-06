From Coq Require Import Bool List ZArith Lia.
From compcert Require Import Integers Values Memory Memdata AST.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.
From TrustNoBPF.Semantics Require Import AbstractDomain Concretization Transfer IRLevelAssms Common.

Import ListNotations.
Open Scope Z_scope.

(** Rust reference: [verifier/transfer.rs::transfer_store_reg] *)

(** =========== Transfer definitions =========== *)

(** Rust [transfer.rs::abstract_values_for_var]: every direct value fact for
    the source, in order. *)
Definition abstract_values_for_var (state : abstract_state) (src : var) : list value_state :=
  flat_map (fun fact =>
    match fact with
    | AbstractValue (Var name) value => if Nat.eqb name src then [value] else []
    | _ => []
    end) state.

(** Rust [MemSize::max_value] and [stored_values], main commit [b658aae].
    A full-width store keeps every description. A narrow store keeps every
    [Scalar] fact, since the bytes of a disclosable value are disclosable, and
    the other non-pointer descriptions only if at least one source range proves
    that the value fits. If nothing is kept, the caller records [Unknown]. *)
Definition value_fits_store (size : sizeOp) (value : value_state) : bool :=
  let max := 2 ^ (8 * load_width size) - 1 in
  match value with
  | URangeValue bounds => u_upper bounds <=? max
  | RangeValue bounds =>
      (0 <=? lower bounds) && (0 <=? upper bounds) &&
      (upper bounds <? Int64.modulus) && (upper bounds <=? max)
  | _ => false
  end.

Definition stored_values (values : list value_state) (size : sizeOp) : list value_state :=
  match size with
  | DBWord => values
  | _ =>
      let fits := existsb (value_fits_store size) values in
      filter (fun value =>
        match value with Scalar => true | _ => false end ||
        (fits && negb (match value with Ptr _ => true | _ => false end))) values
  end.

(** Rust [transfer_store_reg] with [allow_ptr_leaks] false. A store outside
    a stack frame ([stack_frame_of] is [None]) needs a disclosable source,
    else Rust rejects it ([StoreLeaksPointer]). Imprecise writes immediately
    weaken cells, keeping disclosable cells [Scalar] when the source is
    disclosable. Exact writes fold the source descriptions ([meet::fold],
    deciding through [entails]) and filter them ([stored_values]) before
    clearing overlapping cells. The instruction adapter checks initialization;
    full-width spills are tracked by the shared instruction wrapper. *)
Definition transfer_store_reg (entails : value_state -> value_state -> bool)
    (state : abstract_state) (base src : var)
    (size : sizeOp) (offset : Z) (policy : store_policy) : option abstract_state :=
  match checked_write_access_range state base offset (load_width size) policy with
  | Some access =>
      let ptr := access_ptr access in
      let bytes := access_range access in
      if match Region.frame (ptr_ty ptr) with
         | Some _ => true
         | None => disclosable state src
         end then
        if access_exact access then
          let values := stored_values (fold entails (abstract_values_for_var state src)) size in
          let cleared := remove_overlapping_content state ptr bytes in
          Some (match values with
                | [] => push_memory_state cleared ptr bytes Unknown
                | _ => fold_left (fun post value =>
                           push_memory_state post ptr bytes value)
                         values cleared
                end)
        else Some (degrade_overlapping_content state ptr bytes (disclosable state src))
      else None
  | None => None
  end.

(** Rust's instruction wrapper checks each operand with [ensure_defined]: a
    direct initialized value fact and no [Uninit] one. Register names remain unchanged. *)
Definition transfer_store_reg_local (entails : value_state -> value_state -> bool)
    (before : abstract_machine_state)
    (base source : ireg) (size : sizeOp) (offset : Z)
    (policy : store_policy) : option abstract_machine_state :=
  if ensure_defined (facts before) (register_name before base) then
    if ensure_defined (facts before) (register_name before source) then
      option_map (fun post => AbstractMachineState post (register_name before))
        (transfer_store_reg entails (facts before) (register_name before base)
          (register_name before source) size offset policy)
    else None
  else None.

Definition transfer_store_reg_instruction (entails : value_state -> value_state -> bool)
    (before : abstract_machine_state)
    (base : ireg) (source : ireg) (size : sizeOp) (offset : Z) (policy : store_policy) :
    option abstract_machine_state :=
  transfer_at_entry (SpillProvenance.StoreReg (register_name before base) (register_name before source) offset (load_width size)) before
    (transfer_store_reg_local entails before base source size offset policy).

(** Includes the trusted [InvalidUninitMemoryFact] input check and Rust-sized
    memory coordinates. Their Rust provenance and the limits of modeled
    validation/representation checks are in [Transfer.v]. *)
Definition accepted_store_reg (entails : value_state -> value_state -> bool)
    (before after : abstract_machine_state)
    (base source : ireg) (size : sizeOp) (offset : Z) (policy : store_policy) : Prop :=
  accepted_transfer before after
    (transfer_store_reg_instruction entails before base source size offset policy).

(** =========== Soundness proof =========== *)

Definition store_reg_chunk (size : sizeOp) : memory_chunk :=
  match size with Byte => Mint8unsigned | HalfWord => Mint16unsigned
  | Word => Mint32 | DBWord => Mint64 end.

Definition store_reg_bytes (size : sizeOp) (value : val) : list memval :=
  encode_val (store_reg_chunk size)
    (match size with
     | DBWord => value
     | _ => match value with
            | Vlong n => Vint (Int.repr (Int64.unsigned n))
            | _ => Vundef end
     end).

Lemma store_reg_bytes_length : forall size value,
  Z.of_nat (length (store_reg_bytes size value)) = load_width size.
Proof.
  intros. unfold store_reg_bytes. rewrite encode_val_length, <- size_chunk_conv.
  destruct size; reflexivity.
Qed.

Lemma store_reg_bytes_initialized : forall size value,
  runtime_value value ->
  (size <> DBWord -> exists n, value = Vlong n) ->
  Forall initialized_byte (store_reg_bytes size value).
Proof.
  intros size value RUNTIME SCALAR.
  destruct size; try (destruct (SCALAR ltac:(discriminate)) as [n ->]).
  all: try solve [unfold store_reg_bytes, store_reg_chunk; cbn [encode_val];
    unfold inj_bytes; apply Forall_forall; intros entry IN;
    apply in_map_iff in IN as [byte [-> _]]; exact I].
  all: inversion RUNTIME; subst; unfold store_reg_bytes, store_reg_chunk;
    cbn [encode_val]; unfold inj_bytes, inj_value;
    repeat constructor; cbn [initialized_byte]; discriminate.
Qed.

Lemma store_reg_bytes_pointer_free : forall size n,
  Forall pointer_free_byte (store_reg_bytes size (Vlong n)).
Proof.
  intros. apply encode_pointer_free. intros b o. destruct size; discriminate.
Qed.

(** A disclosable source is an integer. *)
Lemma abstract_values_holds : forall world memory state source value,
  Forall (atom_holds world memory) state ->
  In value (abstract_values_for_var state source) ->
  value_holds world memory value (variable_value world source).
Proof.
  intros world memory state source value FACTS IN.
  apply in_flat_map in IN as [fact [OLD IN]].
  destruct fact; cbn in IN; try contradiction.
  destruct term as [name | name | n | name offset | name offset | lhs rhs]; try contradiction.
  destruct (Nat.eqb name source) eqn:NAME; try contradiction.
  apply Nat.eqb_eq in NAME; subst name.
  destruct IN as [-> | []].
  exact ((proj1 (Forall_forall _ _) FACTS) _ OLD).
Qed.

Lemma store_reg_decode_integer : forall size n,
  load_value_casting (decode_val (store_reg_chunk size)
    (store_reg_bytes size (Vlong n))) =
  match size with
  | DBWord => Vlong n
  | _ => Vlong (Int64.repr (Int64.unsigned n mod (2 ^ (8 * load_width size))))
  end.
Proof.
  intros size n.
  pose proof (decode_encode_val_general
    (match size with DBWord => Vlong n | _ => Vint (Int.repr (Int64.unsigned n)) end)
    (store_reg_chunk size) (store_reg_chunk size)) as DECODE.
  unfold store_reg_bytes. destruct size;
    cbn [store_reg_chunk decode_encode_val] in DECODE;
    cbn [store_reg_chunk]; rewrite DECODE;
    cbn [load_value_casting load_width].
  - rewrite Int.zero_ext_mod by (cbn; lia).
    rewrite Int.unsigned_repr_eq, Z.mod_mod_divide; [reflexivity | exists 16777216; reflexivity].
  - rewrite Int.zero_ext_mod by (cbn; lia).
    rewrite Int.unsigned_repr_eq, Z.mod_mod_divide; [reflexivity | exists 65536; reflexivity].
  - rewrite Int.unsigned_repr_eq. reflexivity.
  - reflexivity.
Qed.

Lemma store_reg_decode_full : forall value,
  runtime_value value ->
  load_value_casting (decode_val Mint64 (store_reg_bytes DBWord value)) = value.
Proof.
  intros value RUNTIME. inversion RUNTIME; subst.
  - exact (store_reg_decode_integer DBWord n).
  - pose proof (decode_encode_val_general (Vptr b ofs) Mint64 Mint64) as DECODE.
    cbn [decode_encode_val] in DECODE.
    unfold store_reg_bytes, store_reg_chunk. rewrite DECODE. reflexivity.
Qed.

Lemma value_fits_store_sound : forall world memory size abstract value,
  value_holds world memory abstract value ->
  value_fits_store size abstract = true ->
  exists n, value = Vlong n /\
    Int64.unsigned n < 2 ^ (8 * load_width size).
Proof.
  intros world memory size abstract value HOLDS FIT.
  destruct abstract; cbn [value_fits_store] in FIT; try discriminate.
  - destruct value; try contradiction. exists i. split; [reflexivity|].
    apply Z.leb_le in FIT. cbn [value_holds] in HOLDS. lia.
  - repeat rewrite andb_true_iff in FIT.
    destruct FIT as [[[LOW NONNEG] WIDTH] HIGH].
    apply Z.leb_le in LOW, NONNEG, HIGH. apply Z.ltb_lt in WIDTH.
    destruct value; try contradiction. exists i. split; [reflexivity|].
    cbn [value_holds] in HOLDS.
    unfold Int64.signed in HOLDS.
    pose proof (Int64.unsigned_range i).
    destruct (Coqlib.zlt (Int64.unsigned i) Int64.half_modulus);
      unfold Int64.half_modulus, Int64.modulus, Int64.wordsize in *; lia.
Qed.

(** Every retained source description holds of the whole-cell load result.
    A fitting range makes truncation the identity for all descriptions,
    including congruences; a kept [Scalar] fact makes the source an integer,
    so its truncation is one too; full-width stores preserve the source value. *)
Lemma stored_values_holds : forall world memory size values value,
  runtime_value value ->
  Forall (fun abstract => value_holds world memory abstract value) values ->
  Forall (fun abstract => value_holds world memory abstract
    (load_value_casting (decode_val (store_reg_chunk size)
      (store_reg_bytes size value)))) (stored_values values size).
Proof.
  intros world memory size values value RUNTIME HOLDS.
  destruct size eqn:SIZE.
  all: try solve [cbn [stored_values store_reg_chunk];
    rewrite (store_reg_decode_full _ RUNTIME); exact HOLDS].
  all: cbn [stored_values]; apply Forall_forall; intros abstract MEMBER;
    apply filter_In in MEMBER as [MEMBER KEEP];
    pose proof ((proj1 (Forall_forall _ _) HOLDS) _ MEMBER) as SOURCE.
  all: destruct (value_state_eq_dec abstract Scalar) as [-> | NOT_SCALAR];
    [cbn [value_holds] in SOURCE |- *; destruct SOURCE as [n ->];
     rewrite store_reg_decode_integer; eexists; reflexivity |].
  all: apply orb_true_iff in KEEP as [KEEP | KEEP];
    [destruct abstract; try discriminate KEEP; contradiction |];
    apply andb_true_iff in KEEP as [FIT _];
    apply existsb_exists in FIT as [fitting [IN FIT]];
    pose proof ((proj1 (Forall_forall _ _) HOLDS) _ IN) as VALUE;
    destruct (value_fits_store_sound _ _ _ _ _ VALUE FIT) as [n [-> BOUND]];
    rewrite store_reg_decode_integer; cbn [load_width] in BOUND |- *;
    rewrite Z.mod_small by (pose proof (Int64.unsigned_range n); lia);
    rewrite Int64.repr_unsigned; exact SOURCE.
Qed.

Lemma store_reg_load_same : forall memory memory' b address size value,
  Mem.storebytes memory b (Ptrofs.unsigned address) (store_reg_bytes size value) =
    Some memory' ->
  load size (Vptr b address) memory' =
    Some (decode_val (store_reg_chunk size) (store_reg_bytes size value)).
Proof.
  intros memory memory' b address size value STORE.
  pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ STORE) as READ.
  rewrite store_reg_bytes_length in READ.
  destruct size; cbn [load store_reg_chunk load_width] in *;
    unfold loadv_unaligned; cbn [size_chunk]; now rewrite READ.
Qed.

(** Each newly recorded value fact describes the bytes actually written.
    The defined-source premise is explicit: merely mentioning the source in
    an entry [MemoryEq] does not establish it. This lemma does not address
    preservation of other cells or spill equalities. *)
Lemma store_reg_written_cell :
  forall world memory memory' region window b address size abstract value,
    runtime_value value ->
    (size <> DBWord -> exists n, value = Vlong n) ->
    value_holds world memory abstract
      (load_value_casting (decode_val (store_reg_chunk size) (store_reg_bytes size value))) ->
    Mem.storebytes memory b (Ptrofs.unsigned address) (store_reg_bytes size value) =
      Some memory' ->
    region_address world region (lower window) = Vptr b address ->
    upper window - lower window = load_width size ->
    Ptrofs.unsigned address + load_width size <= Ptrofs.modulus ->
    cell_holds world memory' region window (memory_stored_value region abstract).
Proof.
  intros world memory memory' region window b address size abstract value
    RUNTIME SCALAR HOLDS STORE ADDRESS WIDTH NONWRAP.
  assert (ORDER : lower window <= upper window)
    by (destruct size; cbn in WIDTH; lia).
  assert (INIT : initialized_bytes memory' (region_address world region (lower window))
    (upper window - lower window)).
  { rewrite ADDRESS, WIDTH. exists (store_reg_bytes size value). split.
    - rewrite <- (store_reg_bytes_length size value).
      now apply Mem.loadbytes_storebytes_same in STORE.
    - now apply store_reg_bytes_initialized. }
  assert (ADDRESSABLE : region_bytes_addressable world region window)
    by (unfold region_bytes_addressable; rewrite ADDRESS; lia).
  pose proof HOLDS as RESULT.
  apply (value_holds_storebytes _ _ _ _ _ _ _ _ STORE) in RESULT.
  assert (DEFINED : runtime_value (load_value_casting
    (decode_val (store_reg_chunk size) (store_reg_bytes size value)))).
  { destruct size.
    all: try (destruct (SCALAR ltac:(discriminate)) as [n ->];
      rewrite store_reg_decode_integer; constructor).
    cbn [store_reg_chunk]. rewrite (store_reg_decode_full _ RUNTIME). exact RUNTIME. }
  assert (STORED : value_holds world memory' (memory_stored_value region abstract)
    (load_value_casting (decode_val (store_reg_chunk size) (store_reg_bytes size value)))).
  { destruct abstract; cbn [memory_stored_value]; try exact RESULT.
    destruct (Region.uninit_by_default region); [exact RESULT|exact DEFINED]. }
  destruct (value_state_eq_dec (memory_stored_value region abstract) Scalar)
    as [IS_SCALAR | NOT_SCALAR].
  { rewrite IS_SCALAR in STORED |- *. destruct STORED as [n DECODED].
    eapply written_scalar_cell; [exact STORE | now apply store_reg_bytes_initialized | | exact ADDRESS
      | rewrite store_reg_bytes_length; lia | lia].
    exact (decode_long_pointer_free _ _ _ DECODED). }
  destruct (memory_stored_value region abstract); cbn [cell_holds cell_value_holds] in *.
  all: try exact I; try congruence.
  all: try solve [destruct (Region.uninit_by_default region); auto].
  all: split; [exact ORDER |]; split; [exact ADDRESSABLE |]; split; [exact INIT |];
    exists size; split; [lia |]; rewrite ADDRESS,
      (store_reg_load_same _ _ _ _ _ _ STORE); exact STORED.
Qed.

Lemma stored_cells_origin : forall values state ptr window fact,
  In fact (fold_left (fun post value =>
    push_memory_state post ptr window value) values state) ->
  In fact state \/ exists region abstract,
    Region.cells (ptr_ty ptr) = Some region /\ In abstract values /\
    fact = MemoryCell region window (memory_stored_value region abstract).
Proof.
  induction values as [|value rest IH]; intros state ptr window fact IN.
  - now left.
  - cbn [fold_left] in IN.
    destruct (IH _ _ _ _ IN) as [OLD | [region [abstract [TARGET [IN_VALUE EQ]]]]].
    + unfold push_memory_state in OLD.
      destruct (Region.cells (ptr_ty ptr)) as [region|] eqn:TARGET; [|now left].
      apply in_app_iff in OLD as [OLD | [EQ | []]]; [now left |].
      right. exists region, value. split; [reflexivity |]. split; [now left |congruence].
    + right. exists region, abstract. split; [exact TARGET |]. split; [now right |exact EQ].
Qed.


Lemma store_reg_other_fact_origin : forall entails state post base source size offset policy fact,
  transfer_store_reg entails state base source size offset policy = Some post ->
  (match fact with MemoryCell _ _ _ => False | _ => True end) ->
  In fact post -> In fact state.
Proof.
  intros entails state post base source size offset policy fact TRANSFER NONCELL IN.
  unfold transfer_store_reg in TRANSFER.
  destruct (checked_write_access_range state base offset (load_width size) policy)
    as [access|]; try discriminate.
  destruct (match Region.frame (ptr_ty (access_ptr access)) with
    | Some _ => true | None => disclosable state source end); try discriminate.
  destruct (access_exact access).
  - inversion TRANSFER; subst post; clear TRANSFER.
    assert (OLD : In fact (remove_overlapping_content state (access_ptr access) (access_range access))).
    { destruct (stored_values (fold entails (abstract_values_for_var state source)) size)
        as [|value rest].
      - unfold push_memory_state in IN.
        destruct (Region.cells (ptr_ty (access_ptr access))) as [target|]; [|exact IN].
        apply in_app_iff in IN as [IN | [EQ | []]]; [exact IN |]. subst fact; contradiction.
      - destruct (stored_cells_origin _ _ _ _ _ IN)
          as [OLD | [region [abstract [_ [_ EQ]]]]]; [exact OLD |]. subst fact; contradiction. }
    unfold remove_overlapping_content in OLD.
    destruct (Region.cells (ptr_ty (access_ptr access))) as [target|]; [|exact OLD].
    apply in_flat_map in OLD as [old [OLD IN_OLD]].
    destruct old; cbn in IN_OLD; try (destruct IN_OLD as [EQ | []]; now subst fact).
    destruct (_ && _); [|destruct IN_OLD as [EQ | []]; now subst fact].
    apply in_app_iff in IN_OLD as [IN_OLD | IN_OLD];
      destruct (_ <? _); try contradiction;
      destruct IN_OLD as [EQ | []]; subst fact; contradiction.
  - unfold degrade_overlapping_content in TRANSFER.
    destruct (Region.cells (ptr_ty (access_ptr access))) as [target|];
      inversion TRANSFER; subst post; [|exact IN].
    apply in_map_iff in IN as [old [EQ OLD]].
    destruct old; try (now subst fact).
    destruct (Region.eqb _ _ && overlaps _ _) in EQ; subst fact; contradiction.
Qed.


Lemma store_reg_cells_preserved :
  forall entails world memory memory' state post base source size offset policy access b address,
    Forall (atom_holds world memory) state -> transfer_input_valid state ->
    runtime_value (variable_value world source) ->
    (size <> DBWord -> exists n, variable_value world source = Vlong n) ->
    checked_write_access_range state base offset (load_width size) policy = Some access ->
    transfer_store_reg entails state base source size offset policy = Some post ->
    Mem.storebytes memory b (Ptrofs.unsigned address)
      (store_reg_bytes size (variable_value world source)) = Some memory' ->
    Ptrofs.unsigned address + load_width size <= Ptrofs.modulus ->
    store_footprints_separated world state (Region.cells (ptr_ty (access_ptr access)))
      (access_range access) b (Ptrofs.unsigned address) (load_width size) ->
    (access_exact access = true -> forall region,
      Region.cells (ptr_ty (access_ptr access)) = Some region ->
      region_address world region (lower (access_range access)) = Vptr b address) ->
    forall region window abstract, In (MemoryCell region window abstract) post ->
      cell_holds world memory' region window abstract.
Proof.
  intros entails world memory memory' state post base source size offset policy access b address
    FACTS [VALID COORDINATES] RUNTIME SCALAR CHECK TRANSFER STORE NOWRAP SEPARATE
    EXACT_ADDRESS.
  unfold transfer_store_reg in TRANSFER. rewrite CHECK in TRANSFER.
  destruct (match Region.frame (ptr_ty (access_ptr access)) with
    | Some _ => true | None => disclosable state source end); [| discriminate].
  assert (INIT : Forall initialized_byte (store_reg_bytes size (variable_value world source)))
    by (apply store_reg_bytes_initialized; assumption).
  pose proof (checked_write_window_i64 _ _ _ _ _ _ CHECK) as [WLOW WHIGH].
  assert (UNCHANGED : forall region window abstract,
    In (MemoryCell region window abstract) state ->
    (Region.cells (ptr_ty (access_ptr access)) <> Some region \/
      overlaps window (access_range access) = false) ->
    cell_holds world memory' region window abstract).
  { intros region window abstract IN UNTOUCHED.
    eapply cell_holds_storebytes_disjoint; [exact STORE | exact INIT | |].
    - intros other addr LOCATION. rewrite store_reg_bytes_length.
      eapply SEPARATE; [exact IN | reflexivity | exact UNTOUCHED | exact LOCATION].
    - exact ((proj1 (Forall_forall _ _) FACTS) _ IN). }
  assert (SUBCELL : forall region outer inner abstract,
    In (MemoryCell region outer abstract) state ->
    lower outer <= lower inner -> upper inner <= upper outer ->
    lower inner <= upper inner -> cell_holds world memory' region inner Unknown).
  { intros. eapply unknown_subcell_after_store; eauto. }
  destruct (access_exact access) eqn:EXACT.
  - inversion TRANSFER; subst post; clear TRANSFER. intros region window abstract IN.
    pose proof (exact_store_width _ _ _ _ _ _ CHECK EXACT) as WIDTH.
    assert (OLD_OR_NEW : In (MemoryCell region window abstract)
      (remove_overlapping_content state (access_ptr access) (access_range access)) \/
      exists value, abstract = memory_stored_value region value /\
        value_holds world memory value (load_value_casting (decode_val (store_reg_chunk size)
          (store_reg_bytes size (variable_value world source)))) /\
        Region.cells (ptr_ty (access_ptr access)) = Some region /\
        window = access_range access).
    { destruct (stored_values (fold entails (abstract_values_for_var state source)) size)
        as [|value rest] eqn:VALUES.
      - cbn in IN. unfold push_memory_state in IN.
        destruct (Region.cells (ptr_ty (access_ptr access))) as [target|] eqn:TARGET;
          [|now left].
        apply in_app_iff in IN as [IN | [EQ | []]]; [now left |].
        inversion EQ; subst region window abstract. right. exists Unknown.
        split; [reflexivity|]. split; [|auto].
        cbn [value_holds]. destruct size.
        all: try (destruct (SCALAR ltac:(discriminate)) as [n ->];
          rewrite store_reg_decode_integer; constructor).
        cbn [store_reg_chunk]. rewrite (store_reg_decode_full _ RUNTIME). exact RUNTIME.
      - destruct (stored_cells_origin _ _ _ _ _ IN)
          as [OLD | [target [value' [TARGET [IN_VALUE EQ]]]]]; [now left |].
        inversion EQ; subst region window abstract. right. exists value'.
        split; [reflexivity |]. split; [|auto].
        assert (ORIGINAL : Forall (fun value =>
          value_holds world memory value (variable_value world source))
          (fold entails (abstract_values_for_var state source))).
        { apply fold_holds. apply Forall_forall. intros described MEMBER.
          eapply abstract_values_holds; eauto. }
        pose proof (stored_values_holds world memory size _ _ RUNTIME ORIGINAL) as STORED.
        rewrite VALUES in STORED. exact ((proj1 (Forall_forall _ _) STORED) _ IN_VALUE). }
    destruct OLD_OR_NEW as [OLD | [value [VALUE [HOLDS [TARGET WINDOW]]]]].
    + unfold remove_overlapping_content in OLD.
      destruct (Region.cells (ptr_ty (access_ptr access))) as [target|] eqn:TARGET.
      * destruct (removed_cell_origin _ _ _ _ _ _ OLD)
          as [[PRE DISJOINT] | [outer [old [PRE [REGION [VALUE BOUNDS]]]]]].
        -- apply UNCHANGED; [exact PRE |].
           destruct DISJOINT as [DIFFERENT | DISJOINT]; [left; congruence | now right].
        -- subst region abstract. destruct BOUNDS as [LEFT [RIGHT ORDER]].
           destruct (removed_cell_untouched _ _ _ _ _ _ OLD) as [DIFFERENT | DISJOINT];
             [congruence |].
           refine (remainder_cell_after_store _ _ _ _ _ _ _ _ _ _ _ _ FACTS
             (conj VALID COORDINATES) PRE LEFT RIGHT ORDER DISJOINT WLOW WHIGH
             (EXACT_ADDRESS eq_refl target eq_refl) STORE INIT _).
           rewrite store_reg_bytes_length. lia.
      * apply UNCHANGED; [exact OLD |left; discriminate].
    + subst abstract window. eapply store_reg_written_cell; eauto.
  - unfold degrade_overlapping_content in TRANSFER.
    destruct (Region.cells (ptr_ty (access_ptr access))) as [target|] eqn:TARGET.
    + inversion TRANSFER; subst post; clear TRANSFER. intros region window abstract IN.
      apply in_map_iff in IN as [fact [EQ OLD]]. destruct fact; try discriminate EQ.
      destruct (Region.eqb region0 target && overlaps bytes (access_range access)) eqn:OVERLAP.
      * pose proof ((proj1 (Forall_forall _ _) COORDINATES) _ OLD) as BOUNDS.
        destruct (disclosable state source && state_disclosable value) eqn:DISCLOSABLE.
        -- inversion EQ; subst region window abstract.
           apply andb_true_iff in DISCLOSABLE as [SOURCE DISCLOSABLE].
           destruct (disclosable_sound _ _ _ _ FACTS SOURCE) as [n LONG].
           rewrite LONG in STORE, INIT.
           eapply scalar_cell_storebytes;
             [exact STORE | exact INIT | apply store_reg_bytes_pointer_free |].
           eapply disclosable_cell_scalar; [exact DISCLOSABLE | |
             exact ((proj1 (Forall_forall _ _) FACTS) _ OLD)].
           exact (cells_not_probe_readable _ _ (proj1 BOUNDS)).
        -- inversion EQ; subst region window abstract.
           eapply SUBCELL; [exact OLD | lia | lia |].
           exact (proj2 (proj2 (proj2 BOUNDS))).
      * inversion EQ; subst region window abstract. apply UNCHANGED; [exact OLD |].
        apply andb_false_iff in OVERLAP as [DIFFERENT | DISJOINT].
        -- left. intros SAME. inversion SAME; subst region0.
           rewrite region_eqb_refl in DIFFERENT; discriminate.
        -- now right.
    + inversion TRANSFER; subst post. intros. apply UNCHANGED; [assumption |left; discriminate].
Qed.

Lemma transfer_store_reg_preserves :
  forall entails world memory memory' state post base source size offset policy access b address,
    Forall (atom_holds world memory) state -> transfer_input_valid state ->
    runtime_value (variable_value world source) ->
    (size <> DBWord -> exists n, variable_value world source = Vlong n) ->
    checked_write_access_range state base offset (load_width size) policy = Some access ->
    transfer_store_reg entails state base source size offset policy = Some post ->
    Mem.storebytes memory b (Ptrofs.unsigned address)
      (store_reg_bytes size (variable_value world source)) = Some memory' ->
    Ptrofs.unsigned address + load_width size <= Ptrofs.modulus ->
    store_footprints_separated world state (Region.cells (ptr_ty (access_ptr access)))
      (access_range access) b (Ptrofs.unsigned address) (load_width size) ->
    (access_exact access = true -> forall region,
      Region.cells (ptr_ty (access_ptr access)) = Some region ->
      region_address world region (lower (access_range access)) = Vptr b address) ->
    Forall (atom_holds world memory')
      (SpillProvenance.materialize
        (fst (SpillProvenance.update (SpillProvenance.from_entry state) state
          (SpillProvenance.StoreReg base source offset (load_width size)))) post).
Proof.
  intros entails world memory memory' state post base source size offset policy access b address
    FACTS VALID RUNTIME SCALAR CHECK TRANSFER STORE NOWRAP SEPARATE EXACT_ADDRESS.
  assert (INIT : Forall initialized_byte (store_reg_bytes size (variable_value world source)))
    by (apply store_reg_bytes_initialized; assumption).
  rewrite (materialize_register_store _ _ _ _ _ _ _ _ CHECK).
  apply Forall_app. split.
  - eapply materialized_write_holds; eauto using store_reg_bytes_length,
      store_reg_cells_preserved, store_reg_other_fact_origin.
  - destruct (Region.cells (ptr_ty (access_ptr access))) as [region|] eqn:TARGET; [|constructor].
    destruct (access_exact access) eqn:EXACT; [|constructor].
    destruct size; cbn [load_width]; try solve [constructor].
    constructor; [|constructor]. cbn [atom_holds].
    rewrite (EXACT_ADDRESS eq_refl region eq_refl).
    eapply memory_eq_storebytes_same; [exact STORE | |].
    + pose proof (store_reg_bytes_length DBWord (variable_value world source)) as LENGTH.
      cbn [load_width] in LENGTH. lia.
    + exact (store_reg_decode_full _ RUNTIME).
Qed.

Lemma store_reg_step :
  forall memory memory' (regs : regset) stack code_id count regions program
    size (base source : ireg) offset b address,
    regs base = Vptr b address ->
    Mem.storebytes memory b
      (Ptrofs.unsigned (Ptrofs.add address (Ptrofs.repr offset)))
      (store_reg_bytes size (regs source)) = Some memory' ->
    instruction_step regions program
      (Pstore size base (inl source) (Ptrofs.repr offset))
      (TLS_State regs stack code_id count memory)
      (TLS_State (nextinstr regs) stack code_id count memory').
Proof.
  intros memory memory' regs stack code_id count regions program
    size base source offset b address BASE STORE.
  unfold instruction_step. cbn [exec_instr]. unfold exec_store, Pregmap.get.
  rewrite BASE. cbn [Val.offset_ptr].
  destruct size; unfold store_reg_bytes, store_reg_chunk in STORE;
    cbn [store sizew eval_reg_immw]; unfold storev_unaligned;
    rewrite STORE; reflexivity.
Qed.

(** Soundness of every accepted register store the kernel leaves in place,
    including spill tracking, for any [entails]: [meet::fold] keeps only facts
    that hold whatever [entails] decides. EXTRA PROOF PREMISE from the CompCert memory
    model: a narrow store's source is an integer. CompCert encodes a narrow
    store of a pointer as [Undef] bytes, where the hardware writes the low bytes
    of the address; Rust then records an [Unknown] cell, which promises
    initialized bytes. *)
Theorem transfer_store_reg_sound :
  forall (attrs : load_attrs) entails regions program before after base source size offset
         kind executable concrete,
    concretizes attrs regions before concrete ->
    accepted_store_reg entails before after base source size offset attrs ->
    store_access_kind (facts before) (register_name before base) offset (load_width size)
      attrs = Some kind ->
    lowers_store size base (inl source) offset kind executable ->
    (size <> DBWord ->
      match concrete with TLS_State regs _ _ _ _ => exists n, regs source = Vlong n end) ->
    exists concrete',
      instruction_step regions program executable concrete concrete' /\
      concretizes attrs regions after concrete'.
Proof.
  intros attrs entails regions program before after base source size offset kind executable
    concrete CONCRETE [VALID TRANSFER] KIND LOWER SCALAR.
  pose proof (lowers_store_instruction _ _ _ _ _ _ LOWER) as EXECUTABLE. subst executable.
  pose proof (lowers_store_base _ _ _ _ _ _ LOWER) as BASE_REGISTER.
  pose proof (lowers_store_source _ _ _ _ _ _ LOWER) as SOURCE_REGISTER.
  cbn [program_operand program_register] in SOURCE_REGISTER.
  unfold transfer_store_reg_instruction, transfer_at_entry,
    transfer_with_provenance in TRANSFER.
  destruct (SpillProvenance.update (SpillProvenance.from_entry (facts before))
    (facts before) (SpillProvenance.StoreReg (register_name before base)
      (register_name before source) offset (load_width size)))
    as [provenance refilled] eqn:UPDATE.
  assert (NO_REFILL : refilled = None).
  { pose proof UPDATE as SHAPE. cbn [SpillProvenance.update] in SHAPE.
    destruct (SpillProvenance.invalidate_write (SpillProvenance.from_entry (facts before))
      (facts before) (register_name before base) offset (load_width size)) as [p written].
    destruct written as [[region window]|]; [destruct (load_width size =? 8)|];
      inversion SHAPE; reflexivity. }
  subst refilled.
  destruct (transfer_store_reg_local entails before base source size offset attrs)
    as [local |] eqn:LOCAL; try discriminate.
  unfold transfer_store_reg_local in LOCAL.
  destruct (ensure_defined (facts before) (register_name before base)); try discriminate.
  destruct (ensure_defined (facts before) (register_name before source))
    eqn:SOURCE_DEFINED; try discriminate.
  destruct (transfer_store_reg entails (facts before) (register_name before base)
    (register_name before source) size offset attrs) as [post |] eqn:RAW; try discriminate.
  inversion LOCAL; subst local. cbn [option_map] in TRANSFER.
  inversion TRANSFER; subst after; clear TRANSFER LOCAL.
  pose proof RAW as CHECK.
  unfold transfer_store_reg in CHECK.
  destruct (checked_write_access_range (facts before) (register_name before base)
    offset (load_width size) attrs) as [access |] eqn:ACCESS; try discriminate.
  clear CHECK.
  pose proof ACCESS as FIND. unfold checked_write_access_range in FIND.
  destruct (find_pointer_fact (facts before) (register_name before base))
    as [ptr |] eqn:POINTER_FACT; try discriminate. clear FIND.
  unfold store_access_kind in KIND. rewrite ACCESS in KIND. injection KIND as KIND.
  rewrite (checked_write_access_type _ _ _ _ _ _ _ POINTER_FACT ACCESS) in KIND.
  pose proof (lowered_store_not_context _ _ _ _ _ _ _ LOWER KIND) as NONCTX.
  destruct concrete as [regs stack code_id count memory].
  destruct CONCRETE as [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]].
  pose proof (ensure_defined_sound _ _ _ _ FACTS SOURCE_DEFINED) as RUNTIME.
  pose proof ((proj1 (Forall_forall _ _) FACTS) _
    (find_pointer_fact_present _ _ _ POINTER_FACT)) as POINTER.
  cbn [atom_holds eval_term] in POINTER. rewrite REGISTERS in POINTER by exact BASE_REGISTER.
  destruct (checked_write_access_permissions world memory (facts before)
    (register_name before base) ptr (regs base) attrs offset (load_width size) access
    ltac:(destruct size; cbn; lia) NONCTX POINTER_FACT POINTER POLICY ACCESS)
    as [b [address [BASE [NOWRAP WRITE]]]].
  rewrite BASE in POINTER.
  assert (WRITABLE : Mem.range_perm memory b
    (Ptrofs.unsigned (Ptrofs.add address (Ptrofs.repr offset)))
    (Ptrofs.unsigned (Ptrofs.add address (Ptrofs.repr offset)) +
      Z.of_nat (length (store_reg_bytes size (regs source)))) Cur Writable).
  { rewrite store_reg_bytes_length. exact WRITE. }
  destruct (Mem.range_perm_storebytes _ _ _ _ WRITABLE) as [memory' STORE].
  assert (SOURCE : variable_value world (register_name before source) = regs source)
    by exact (REGISTERS source SOURCE_REGISTER).
  exists (TLS_State (nextinstr regs) stack code_id count memory'). split.
  - eapply store_reg_step; eauto.
  - exists world. split; [| split; [| split; [| split]]].
    + intros reg NOT_AUX. cbn [register_name]. rewrite REGISTERS by exact NOT_AUX.
      unfold nextinstr, Pregmap.get. rewrite Pregmap.gso; [reflexivity |discriminate].
    + pose proof (transfer_store_reg_preserves entails world memory memory' (facts before) post
        (register_name before base) (register_name before source) size offset attrs access
        b (Ptrofs.add address (Ptrofs.repr offset)) FACTS VALID RUNTIME
        ltac:(rewrite SOURCE; exact SCALAR) ACCESS RAW) as PRESERVES.
      rewrite SOURCE in PRESERVES. rewrite UPDATE in PRESERVES. cbn [fst] in PRESERVES.
      apply PRESERVES; [exact STORE | exact NOWRAP | |].
      * eapply checked_write_separated; eauto. exact (proj2 VALID).
      * intros EXACT region CELLS.
        exact (exact_checked_store_address _ _ _ _ _ _ _ _ _ _ _
          POINTER_FACT POINTER ACCESS EXACT CELLS).
    + eapply store_policy_holds_storebytes; eauto.
    + exact LAYOUT.
    + eapply environment_holds_storebytes; [exact STORE | | exact ENVIRONMENT].
      apply store_reg_bytes_initialized; [rewrite <- SOURCE; exact RUNTIME |].
      intros NARROW. destruct (SCALAR NARROW) as [n VALUE]. now exists n.
Qed.
