From Coq Require Import Bool List ZArith Lia.
From compcert Require Import Integers Values Memory Memdata AST.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.
From TrustNoBPF.Semantics Require Import AbstractDomain Concretization Transfer IRLevelAssms Common.

Import ListNotations.
Open Scope Z_scope.

(** Rust reference: [verifier/transfer.rs::transfer_store_imm] *)

(** =========== Transfer definitions =========== *)

(** Rust [transfer_store_imm] and [MemSize::stored_imm], main commit [feba2c3],
    with [allow_ptr_leaks] false. Narrow stores truncate the immediate and
    loads zero-extend the bytes; an eight-byte store sign-extends it. The
    [URange] and [Range] facts describe the same 64-bit whole-cell load
    result, and the [Scalar] fact keeps the bytes disclosable after a later
    narrower store over part of them. A variable-offset store writes a
    disclosable constant. *)
Definition transfer_store_imm (state : abstract_state) (base : var) (size : sizeOp)
    (offset immediate : Z) (policy : store_policy) : option abstract_state :=
  match checked_write_access_range state base offset (load_width size) policy with
  | Some access =>
      let ptr := access_ptr access in
      let bytes := access_range access in
      if access_exact access then
        let cleared := remove_overlapping_content state ptr bytes in
        let unsigned := match size with
          | Byte => immediate mod 256
          | HalfWord => immediate mod 65536
          | Word => Int.unsigned (Int.repr immediate)
          | DBWord => Int64.unsigned (Int64.repr immediate)
          end in
        let signed := Int64.signed (Int64.repr unsigned) in
        let post := push_memory_state cleared ptr bytes
          (URangeValue (URange unsigned unsigned)) in
        let post := push_memory_state post ptr bytes (RangeValue (Range signed signed)) in
        Some (push_memory_state post ptr bytes Scalar)
      else Some (degrade_overlapping_content state ptr bytes true)
  | None => None
  end.

(** Rust's instruction wrapper checks the base with [ensure_defined]: a direct
    initialized value fact and no [Uninit] one. Register names remain unchanged. *)
Definition transfer_store_imm_local (before : abstract_machine_state)
    (base : ireg) (immediate : imm) (size : sizeOp) (offset : Z)
    (policy : store_policy) : option abstract_machine_state :=
  if ensure_defined (facts before) (register_name before base) then
    option_map (fun post => AbstractMachineState post (register_name before))
      (transfer_store_imm (facts before) (register_name before base)
        size offset (Int.signed immediate) policy)
  else None.

Definition transfer_store_imm_instruction (before : abstract_machine_state)
    (base : ireg) (immediate : imm) (size : sizeOp) (offset : Z) (policy : store_policy) :
    option abstract_machine_state :=
  transfer_at_entry
    (SpillProvenance.StoreImm (register_name before base) offset (load_width size)) before
    (transfer_store_imm_local before base immediate size offset policy).

(** Rust validates invariants before executing a block. This relation includes
    the [InvalidUninitMemoryFact] check and Rust-sized memory coordinates,
    modeled by [accepted_transfer] in [Transfer.v], followed by the unchanged
    instruction transfer. *)
Definition accepted_store_imm (before after : abstract_machine_state)
    (base : ireg) (immediate : imm) (size : sizeOp) (offset : Z)
    (policy : store_policy) : Prop :=
  accepted_transfer before after
    (transfer_store_imm_instruction before base immediate size offset policy).

(** =========== Soundness proof =========== *)

(** Concrete bytes written by the ISA's immediate-store instruction. *)
Definition store_imm_chunk (size : sizeOp) : memory_chunk :=
  match size with
  | Byte => Mint8unsigned | HalfWord => Mint16unsigned
  | Word => Mint32 | DBWord => Mint64
  end.

Definition store_imm_bytes (size : sizeOp) (immediate : imm) : list memval :=
  encode_val (store_imm_chunk size)
    (match size with DBWord => Vlong (int64_of_int immediate) | _ => Vint immediate end).

(** Exactly the unsigned constant used by the Rust transfer above. *)
Definition store_imm_unsigned (size : sizeOp) (immediate : imm) : Z :=
  match size with
  | Byte => Int.signed immediate mod 256
  | HalfWord => Int.signed immediate mod 65536
  | Word => Int.unsigned (Int.repr (Int.signed immediate))
  | DBWord => Int64.unsigned (Int64.repr (Int.signed immediate))
  end.

Lemma store_imm_bytes_length : forall size immediate,
  Z.of_nat (length (store_imm_bytes size immediate)) = load_width size.
Proof.
  intros. unfold store_imm_bytes. rewrite encode_val_length, <- size_chunk_conv.
  destruct size; reflexivity.
Qed.

Lemma store_imm_bytes_initialized : forall size immediate,
  Forall initialized_byte (store_imm_bytes size immediate).
Proof.
  intros. destruct size; cbn [store_imm_bytes store_imm_chunk encode_val];
    unfold inj_bytes; apply Forall_forall; intros entry IN;
    apply in_map_iff in IN as [byte [ENTRY _]]; subst entry; exact I.
Qed.

Lemma store_imm_bytes_pointer_free : forall size immediate,
  Forall pointer_free_byte (store_imm_bytes size immediate).
Proof.
  intros. apply encode_pointer_free. intros b o. destruct size; discriminate.
Qed.

Lemma store_imm_unsigned_bounds : forall size immediate,
  0 <= store_imm_unsigned size immediate <= Int64.max_unsigned.
Proof.
  intros. destruct size; cbn [store_imm_unsigned].
  - pose proof (Z.mod_pos_bound (Int.signed immediate) 256 ltac:(lia)).
    unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize; cbn; lia.
  - pose proof (Z.mod_pos_bound (Int.signed immediate) 65536 ltac:(lia)).
    unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize; cbn; lia.
  - rewrite Int.repr_signed. pose proof (Int.unsigned_range immediate) as BOUND.
    change (0 <= Int.unsigned immediate < 4294967296) in BOUND.
    change (0 <= Int.unsigned immediate <= 18446744073709551615). lia.
  - pose proof (Int64.unsigned_range (Int64.repr (Int.signed immediate))).
    unfold Int64.max_unsigned; lia.
Qed.

Lemma store_imm_decode : forall size immediate,
  load_value_casting (decode_val (store_imm_chunk size) (store_imm_bytes size immediate)) =
  Vlong (Int64.repr (store_imm_unsigned size immediate)).
Proof.
  intros size immediate.
  pose proof (decode_encode_val_general
    (match size with DBWord => Vlong (int64_of_int immediate) | _ => Vint immediate end)
    (store_imm_chunk size) (store_imm_chunk size)) as DECODE.
  unfold store_imm_bytes. destruct size;
    cbn [store_imm_chunk decode_encode_val] in DECODE;
    cbn [store_imm_chunk]; rewrite DECODE;
    cbn [load_value_casting store_imm_unsigned].
  - rewrite Int.zero_ext_mod by (cbn; lia).
    unfold Int.signed. destruct (Coqlib.zlt (Int.unsigned immediate) Int.half_modulus).
    + reflexivity.
    + rewrite Zminus_mod. change (Int.modulus mod 256) with 0.
      rewrite Z.sub_0_r, Z.mod_mod by lia.
      reflexivity.
  - rewrite Int.zero_ext_mod by (cbn; lia).
    unfold Int.signed. destruct (Coqlib.zlt (Int.unsigned immediate) Int.half_modulus).
    + reflexivity.
    + rewrite Zminus_mod. change (Int.modulus mod 65536) with 0.
      rewrite Z.sub_0_r, Z.mod_mod by lia. reflexivity.
  - now rewrite Int.repr_signed.
  - unfold int64_of_int. now rewrite Int64.repr_unsigned.
Qed.

Lemma store_imm_load_same : forall memory memory' b address size immediate,
  Mem.storebytes memory b (Ptrofs.unsigned address) (store_imm_bytes size immediate) =
    Some memory' ->
  load size (Vptr b address) memory' =
    Some (decode_val (store_imm_chunk size) (store_imm_bytes size immediate)).
Proof.
  intros memory memory' b address size immediate STORE.
  pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ STORE) as READ.
  rewrite store_imm_bytes_length in READ.
  destruct size; cbn [load store_imm_chunk load_width] in *;
    unfold loadv_unaligned; cbn [size_chunk]; now rewrite READ.
Qed.

Lemma store_imm_written_cell : forall world memory memory' region window b address size immediate,
  Mem.storebytes memory b (Ptrofs.unsigned address) (store_imm_bytes size immediate) =
    Some memory' ->
  region_address world region (lower window) = Vptr b address ->
  upper window - lower window = load_width size ->
  Ptrofs.unsigned address + load_width size <= Ptrofs.modulus ->
  cell_holds world memory' region window
    (URangeValue (URange (store_imm_unsigned size immediate) (store_imm_unsigned size immediate))) /\
  cell_holds world memory' region window
    (RangeValue (Range (Int64.signed (Int64.repr (store_imm_unsigned size immediate)))
      (Int64.signed (Int64.repr (store_imm_unsigned size immediate))))).
Proof.
  intros world memory memory' region window b address size immediate STORE ADDRESS WIDTH NONWRAP.
  assert (ORDER : lower window <= upper window) by (destruct size; cbn in WIDTH; lia).
  assert (INIT : initialized_bytes memory' (region_address world region (lower window))
    (upper window - lower window)).
  { rewrite ADDRESS, WIDTH. exists (store_imm_bytes size immediate). split.
    - rewrite <- (store_imm_bytes_length size immediate).
      now apply Mem.loadbytes_storebytes_same in STORE.
    - apply store_imm_bytes_initialized. }
  assert (ADDRESSABLE : region_bytes_addressable world region window)
    by (unfold region_bytes_addressable; rewrite ADDRESS; lia).
  pose proof (store_imm_load_same _ _ _ _ _ _ STORE) as LOAD.
  pose proof (store_imm_unsigned_bounds size immediate) as BOUNDS.
  split.
  all: cbn [cell_holds cell_value_holds]; split; [exact ORDER |].
  all: split; [exact ADDRESSABLE |]; split; [exact INIT |].
  all: exists size; split; [lia |].
  all:
    rewrite ADDRESS, LOAD; cbn [cell_result_holds]; rewrite store_imm_decode;
    cbn [value_holds u_lower u_upper lower upper];
    rewrite ?Int64.unsigned_repr by exact BOUNDS; lia.
Qed.


Lemma store_imm_other_fact_origin : forall state post base size offset immediate policy fact,
  transfer_store_imm state base size offset immediate policy = Some post ->
  (match fact with MemoryCell _ _ _ => False | _ => True end) ->
  In fact post -> In fact state.
Proof.
  intros state post base size offset immediate policy fact TRANSFER NONCELL IN.
  unfold transfer_store_imm in TRANSFER.
  destruct (checked_write_access_range state base offset (load_width size) policy)
    as [access|]; try discriminate.
  destruct (access_exact access).
  - unfold push_memory_state, remove_overlapping_content in TRANSFER.
    destruct (Region.cells (ptr_ty (access_ptr access))) as [target|];
      inversion TRANSFER; subst post; [| exact IN].
    repeat (apply in_app_iff in IN as [IN | IN];
      [| destruct IN as [EQ | []]; subst fact; contradiction]).
    apply in_flat_map in IN as [old [OLD IN]].
    destruct old; cbn in IN; try (destruct IN as [EQ | []]; now subst fact).
    destruct (_ && _); [| destruct IN as [EQ | []]; now subst fact].
    apply in_app_iff in IN as [IN | IN];
      destruct (_ <? _); try contradiction;
      destruct IN as [EQ | []]; subst fact; contradiction.
  - unfold degrade_overlapping_content in TRANSFER.
    destruct (Region.cells (ptr_ty (access_ptr access))) as [target|];
      inversion TRANSFER; subst post; [| exact IN].
    apply in_map_iff in IN as [old [EQ OLD]].
    destruct old; try (now subst fact).
    destruct (Region.eqb _ _ && overlaps _ _) in EQ; subst fact; contradiction.
Qed.



Lemma store_imm_cells_preserved :
  forall world memory memory' state post base size offset immediate policy access b address,
    Forall (atom_holds world memory) state -> transfer_input_valid state ->
    checked_write_access_range state base offset (load_width size) policy = Some access ->
    transfer_store_imm state base size offset (Int.signed immediate) policy = Some post ->
    Mem.storebytes memory b (Ptrofs.unsigned address) (store_imm_bytes size immediate) =
      Some memory' ->
    Ptrofs.unsigned address + load_width size <= Ptrofs.modulus ->
    store_footprints_separated world state (Region.cells (ptr_ty (access_ptr access)))
      (access_range access) b (Ptrofs.unsigned address) (load_width size) ->
    (access_exact access = true -> forall region,
      Region.cells (ptr_ty (access_ptr access)) = Some region ->
      region_address world region (lower (access_range access)) = Vptr b address) ->
    forall region window abstract, In (MemoryCell region window abstract) post ->
      cell_holds world memory' region window abstract.
Proof.
  intros world memory memory' state post base size offset immediate policy access b address
    FACTS [VALID COORDINATES] CHECK TRANSFER STORE NOWRAP SEPARATE EXACT_ADDRESS.
  assert (INIT : Forall initialized_byte (store_imm_bytes size immediate))
    by apply store_imm_bytes_initialized.
  pose proof (store_imm_bytes_pointer_free size immediate) as FREE.
  pose proof (checked_write_window_i64 _ _ _ _ _ _ CHECK) as [WLOW WHIGH].
  assert (UNCHANGED : forall region window abstract,
    In (MemoryCell region window abstract) state ->
    (Region.cells (ptr_ty (access_ptr access)) <> Some region \/
      overlaps window (access_range access) = false) ->
    cell_holds world memory' region window abstract).
  { intros region window abstract IN UNTOUCHED.
    eapply cell_holds_storebytes_disjoint; [exact STORE | exact INIT | |].
    - intros other addr LOCATION. rewrite store_imm_bytes_length.
      eapply SEPARATE; [exact IN | reflexivity | exact UNTOUCHED | exact LOCATION].
    - exact ((proj1 (Forall_forall _ _) FACTS) _ IN). }
  assert (SUBCELL : forall region outer inner abstract,
    In (MemoryCell region outer abstract) state ->
    lower outer <= lower inner -> upper inner <= upper outer ->
    lower inner <= upper inner -> cell_holds world memory' region inner Unknown).
  { intros. eapply unknown_subcell_after_store; eauto. }
  unfold transfer_store_imm in TRANSFER. rewrite CHECK in TRANSFER.
  fold (store_imm_unsigned size immediate) in TRANSFER.
  destruct (access_exact access) eqn:EXACT.
  - pose proof (exact_store_width _ _ _ _ _ _ CHECK EXACT) as WIDTH.
    assert (LENGTH : Z.of_nat (length (store_imm_bytes size immediate)) =
      upper (access_range access) - lower (access_range access))
      by (rewrite store_imm_bytes_length; lia).
    unfold push_memory_state, remove_overlapping_content in TRANSFER.
    destruct (Region.cells (ptr_ty (access_ptr access))) as [target|] eqn:TARGET.
    + inversion TRANSFER; subst post; clear TRANSFER.
      pose proof (EXACT_ADDRESS eq_refl target eq_refl) as ADDRESS.
      intros region window abstract IN.
      apply in_app_iff in IN as [IN | [EQ | []]];
        [apply in_app_iff in IN as [IN | [EQ | []]];
          [apply in_app_iff in IN as [IN | [EQ | []]] |] |].
      * destruct (removed_cell_origin _ _ _ _ _ _ IN)
           as [[OLD DISJOINT] | [outer [old [OLD [REGION [VALUE BOUNDS]]]]]].
        -- apply UNCHANGED; [exact OLD |].
           destruct DISJOINT as [DIFFERENT | DISJOINT];
             [left; congruence | now right].
        -- subst region abstract. destruct BOUNDS as [LEFT [RIGHT ORDER]].
           destruct (removed_cell_untouched _ _ _ _ _ _ IN) as [DIFFERENT | DISJOINT];
             [congruence |].
           eapply remainder_cell_after_store; eauto. exact (conj VALID COORDINATES).
      * inversion EQ; subst region window abstract.
        exact (proj1 (store_imm_written_cell _ _ _ _ _ _ _ _ _ STORE ADDRESS
          WIDTH NOWRAP)).
      * inversion EQ; subst region window abstract.
        exact (proj2 (store_imm_written_cell _ _ _ _ _ _ _ _ _ STORE ADDRESS
          WIDTH NOWRAP)).
      * inversion EQ; subst region window abstract.
        eapply written_scalar_cell; eauto. lia.
    + inversion TRANSFER; subst post. intros. apply UNCHANGED; [assumption |].
      left; discriminate.
  - unfold degrade_overlapping_content in TRANSFER.
    destruct (Region.cells (ptr_ty (access_ptr access))) as [target|] eqn:TARGET.
    + inversion TRANSFER; subst post; clear TRANSFER. intros region window abstract IN.
      apply in_map_iff in IN as [fact [EQ OLD]].
      destruct fact; try discriminate EQ.
      destruct (Region.eqb region0 target && overlaps bytes (access_range access)) eqn:OVERLAP.
      * pose proof ((proj1 (Forall_forall _ _) COORDINATES) _ OLD) as BOUNDS.
        cbn [andb] in EQ. destruct (state_disclosable value) eqn:DISCLOSABLE.
        -- inversion EQ; subst region window abstract.
           eapply scalar_cell_storebytes; [exact STORE | exact INIT | exact FREE |].
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
    + inversion TRANSFER; subst post. intros. apply UNCHANGED; [assumption |].
      left; discriminate.
Qed.

(** Includes Rust's spill-tracking cleanup, not merely the local transfer. *)
Lemma transfer_store_imm_preserves :
  forall world memory memory' state post base size offset immediate policy access b address,
    Forall (atom_holds world memory) state -> transfer_input_valid state ->
    checked_write_access_range state base offset (load_width size) policy = Some access ->
    transfer_store_imm state base size offset (Int.signed immediate) policy = Some post ->
    Mem.storebytes memory b (Ptrofs.unsigned address) (store_imm_bytes size immediate) =
      Some memory' ->
    Ptrofs.unsigned address + load_width size <= Ptrofs.modulus ->
    store_footprints_separated world state (Region.cells (ptr_ty (access_ptr access)))
      (access_range access) b (Ptrofs.unsigned address) (load_width size) ->
    (access_exact access = true -> forall region,
      Region.cells (ptr_ty (access_ptr access)) = Some region ->
      region_address world region (lower (access_range access)) = Vptr b address) ->
    Forall (atom_holds world memory')
      (SpillProvenance.materialize
        (fst (SpillProvenance.invalidate_write (SpillProvenance.from_entry state)
          state base offset (load_width size))) post).
Proof.
  intros world memory memory' state post base size offset immediate policy access b address
    FACTS VALID CHECK TRANSFER STORE NOWRAP SEPARATE EXACT_ADDRESS.
  eapply materialized_write_holds; eauto using store_imm_bytes_initialized,
    store_imm_bytes_length, store_imm_cells_preserved, store_imm_other_fact_origin.
Qed.

Lemma store_imm_step :
  forall memory memory' (regs : regset) stack code_id count regions program
    size (base : ireg) immediate offset b address,
    regs base = Vptr b address ->
    Mem.storebytes memory b
      (Ptrofs.unsigned (Ptrofs.add address (Ptrofs.repr offset)))
      (store_imm_bytes size immediate) = Some memory' ->
    instruction_step regions program
      (Pstore size base (inr immediate) (Ptrofs.repr offset))
      (TLS_State regs stack code_id count memory)
      (TLS_State (nextinstr regs) stack code_id count memory').
Proof.
  intros memory memory' regs stack code_id count regions program
    size base immediate offset b address BASE STORE.
  unfold instruction_step. cbn [exec_instr]. unfold exec_store, Pregmap.get.
  rewrite BASE. cbn [Val.offset_ptr].
  destruct size; unfold store_imm_bytes, store_imm_chunk in STORE;
    cbn [store sizew eval_reg_immw]; unfold storev_unaligned;
    rewrite STORE; reflexivity.
Qed.

(** Soundness of every accepted immediate store the kernel leaves in place,
    including spill tracking: execution and post-state concretization for all
    widths, exact and imprecise writes and policy grants. *)
Theorem transfer_store_imm_sound :
  forall (attrs : load_attrs) regions program before after base immediate size offset kind
         executable concrete,
    concretizes attrs regions before concrete ->
    accepted_store_imm before after base immediate size offset attrs ->
    store_access_kind (facts before) (register_name before base) offset (load_width size)
      attrs = Some kind ->
    lowers_store size base (inr immediate) offset kind executable ->
    exists concrete',
      instruction_step regions program executable concrete concrete' /\
      concretizes attrs regions after concrete'.
Proof.
  intros attrs regions program before after base immediate size offset kind executable concrete
    CONCRETE [VALID TRANSFER] KIND LOWER.
  pose proof (lowers_store_instruction _ _ _ _ _ _ LOWER) as EXECUTABLE. subst executable.
  pose proof (lowers_store_base _ _ _ _ _ _ LOWER) as BASE_REGISTER.
  unfold transfer_store_imm_instruction, transfer_at_entry,
    transfer_with_provenance in TRANSFER.
  cbn [SpillProvenance.update] in TRANSFER.
  destruct (transfer_store_imm_local before base immediate size offset attrs)
    as [local |] eqn:LOCAL; try discriminate.
  unfold transfer_store_imm_local in LOCAL.
  destruct (ensure_defined (facts before) (register_name before base));
    try discriminate.
  destruct (transfer_store_imm (facts before) (register_name before base)
    size offset (Int.signed immediate) attrs) as [post |] eqn:RAW; try discriminate.
  inversion LOCAL; subst local. cbn [option_map] in TRANSFER.
  inversion TRANSFER; subst after; clear TRANSFER LOCAL.
  pose proof RAW as CHECK.
  unfold transfer_store_imm in CHECK.
  destruct (checked_write_access_range (facts before) (register_name before base)
    offset (load_width size) attrs) as [access |] eqn:ACCESS; try discriminate.
  clear CHECK.
  pose proof ACCESS as FIND.
  unfold checked_write_access_range in FIND.
  destruct (find_pointer_fact (facts before) (register_name before base))
    as [ptr |] eqn:POINTER_FACT; try discriminate.
  clear FIND.
  unfold store_access_kind in KIND. rewrite ACCESS in KIND. injection KIND as KIND.
  rewrite (checked_write_access_type _ _ _ _ _ _ _ POINTER_FACT ACCESS) in KIND.
  pose proof (lowered_store_not_context _ _ _ _ _ _ _ LOWER KIND) as NONCTX.
  destruct concrete as [regs stack code_id count memory].
  destruct CONCRETE as [world [REGISTERS [FACTS [POLICY [LAYOUT ENVIRONMENT]]]]].
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
      Z.of_nat (length (store_imm_bytes size immediate))) Cur Writable).
  { rewrite store_imm_bytes_length. exact WRITE. }
  destruct (Mem.range_perm_storebytes _ _ _ _ WRITABLE) as [memory' STORE].
  exists (TLS_State (nextinstr regs) stack code_id count memory'). split.
  - eapply store_imm_step; eauto.
  - exists world. split; [| split; [| split; [| split]]].
    + intros reg NOT_AUX. cbn [register_name]. rewrite REGISTERS by exact NOT_AUX.
      unfold nextinstr, Pregmap.get. rewrite Pregmap.gso; [reflexivity | discriminate].
    + eapply transfer_store_imm_preserves; eauto.
      * eapply checked_write_separated; eauto. exact (proj2 VALID).
      * intros EXACT region CELLS.
        pose proof (exact_checked_store_address _ _ _ _ _ _ _ _ _ _ _
          POINTER_FACT POINTER ACCESS EXACT CELLS) as ADDRESS.
        exact ADDRESS.
    + eapply store_policy_holds_storebytes; eauto.
    + exact LAYOUT.
    + eapply environment_holds_storebytes; eauto using store_imm_bytes_initialized.
Qed.
