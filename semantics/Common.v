From Coq Require Import Bool List ZArith Lia.
From compcert Require Import Integers Values Memory Memdata Maps AST Archi Coqlib Zbits.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.
From TrustNoBPF.Semantics Require Import AbstractDomain Concretization Transfer IRLevelAssms.

Import ListNotations.
Open Scope Z_scope.

(** Shared lemmas about the concretization definitions. *)

Lemma fold_left_preserves : forall A B (step : A -> B -> A) items initial
    (invariant : A -> Prop) (item_holds : B -> Prop),
  Forall item_holds items -> invariant initial ->
  (forall item accumulator, item_holds item -> invariant accumulator ->
    invariant (step accumulator item)) ->
  invariant (fold_left step items initial).
Proof.
  intros A B step items initial invariant item_holds ITEMS INITIAL STEP.
  revert initial INITIAL. induction ITEMS; intros; cbn; auto.
Qed.

Lemma initialized_value_holds : forall world memory abstract value,
  abstract <> Uninit -> value_holds world memory abstract value -> runtime_value value.
Proof.
  intros world memory abstract value NOT_UNINIT HOLDS.
  destruct abstract; cbn [value_holds] in HOLDS; try contradiction; try assumption.
  all: try solve [destruct HOLDS as [n ->]; constructor].
  all: try solve [destruct value; try contradiction; constructor].
  unfold pointer_state_holds in HOLDS. tauto.
Qed.

Lemma has_initialized_value_sound : forall world memory state name,
  Forall (atom_holds world memory) state ->
  has_initialized_value state name = true -> runtime_value (variable_value world name).
Proof.
  intros world memory state name FACTS CHECK.
  apply existsb_exists in CHECK as [fact [IN CHECK]].
  pose proof ((proj1 (Forall_forall _ _) FACTS) _ IN) as HOLDS.
  destruct fact; cbn in CHECK; try discriminate.
  destruct term; try discriminate.
  destruct value; try discriminate; apply Nat.eqb_eq in CHECK; subst.
  all: eapply initialized_value_holds; [| exact HOLDS]; discriminate.
Qed.

Lemma ensure_defined_sound : forall world memory state name,
  Forall (atom_holds world memory) state -> ensure_defined state name = true ->
  runtime_value (variable_value world name).
Proof.
  intros world memory state name FACTS DEFINED. unfold ensure_defined in DEFINED.
  apply andb_true_iff in DEFINED as [INITIALIZED _].
  exact (has_initialized_value_sound _ _ _ _ FACTS INITIALIZED).
Qed.

Lemma ensure_defined_fresh_name : forall state src dst,
  Forall (fun fact => atom_mentions dst fact = false) state ->
  ensure_defined state src = true -> dst <> src.
Proof.
  intros state src dst FRESH DEFINED EQUAL. subst dst.
  unfold ensure_defined in DEFINED. apply andb_true_iff in DEFINED as [DEFINED _].
  unfold has_initialized_value in DEFINED.
  apply existsb_exists in DEFINED as [fact [IN CHECK]].
  pose proof ((proj1 (Forall_forall _ _) FRESH) _ IN) as NAME.
  destruct fact; cbn in CHECK; try discriminate. destruct term; try discriminate.
  destruct value; try discriminate; apply Nat.eqb_eq in CHECK; subst x;
    cbn [atom_mentions term_mentions] in NAME; rewrite Nat.eqb_refl in NAME; discriminate.
Qed.

Lemma fresh_destination_operand_name : forall before dst dst_value,
  fresh_destination before dst dst_value ->
  dst_value <> register_name before dst ->
  forall reg, dst_value <> register_name before reg.
Proof.
  intros before dst dst_value FRESH OLD reg.
  destruct (ireg_eq reg dst) as [-> | OTHER]; [exact OLD |].
  pose proof (FRESH reg OTHER). congruence.
Qed.

(** [storebytes] changes contents but neither allocates blocks nor changes
    permissions. Hence it cannot change the input seen by pointer metadata. *)
Lemma allocation_metadata_storebytes : forall memory memory' b offset bytes,
  Mem.storebytes memory b offset bytes = Some memory' ->
  allocation_metadata_of memory' = allocation_metadata_of memory.
Proof.
  intros memory memory' b offset bytes STORE.
  unfold allocation_metadata_of.
  rewrite (Mem.nextblock_storebytes _ _ _ _ _ STORE),
    (Mem.storebytes_access _ _ _ _ _ STORE). reflexivity.
Qed.

Lemma pointer_access_storebytes : forall memory memory' ptr value b offset bytes,
  Mem.storebytes memory b offset bytes = Some memory' ->
  pointer_access_holds memory ptr value -> pointer_access_holds memory' ptr value.
Proof.
  intros memory memory' ptr value b offset bytes STORE ACCESS.
  destruct value; cbn [pointer_access_holds] in *; try exact ACCESS.
  intros delta width POS WINDOW.
  destruct (ACCESS delta width POS WINDOW) as [HIGH PERM].
  repeat split; try assumption.
  intros address INSIDE. eapply Mem.perm_storebytes_1; eauto.
Qed.

Lemma pointer_state_storebytes : forall world memory memory' ptr value b offset bytes,
  Mem.storebytes memory b offset bytes = Some memory' ->
  pointer_state_holds world memory ptr value -> pointer_state_holds world memory' ptr value.
Proof.
  intros world memory memory' ptr value b offset bytes STORE
    [FIELDS [ADDRESS [ACCESS [NULL VALUE]]]].
  split; [exact FIELDS |].
  split; [exact ADDRESS |]. split; [| now split].
  unfold pointer_permissions_holds in *.
  destruct (ptr_nullability ptr).
  - destruct ACCESS as [NULL_BASE | ACCESS]; [now left |right].
    destruct (Region.probe_readable (ptr_ty ptr)).
    + intros WRITE. eapply pointer_access_storebytes; eauto.
    + eapply pointer_access_storebytes; eauto.
  - destruct (Region.probe_readable (ptr_ty ptr)).
    + intros WRITE. eapply pointer_access_storebytes; eauto.
    + eapply pointer_access_storebytes; eauto.
  - exact I.
Qed.

Lemma value_holds_storebytes : forall world memory memory' abstract value b offset bytes,
  Mem.storebytes memory b offset bytes = Some memory' ->
  value_holds world memory abstract value -> value_holds world memory' abstract value.
Proof.
  intros. destruct abstract; cbn [value_holds] in *; try assumption.
  eapply pointer_state_storebytes; eauto.
Qed.

Lemma memory_eq_storebytes_same : forall memory memory' b address bytes value,
  Mem.storebytes memory b (Ptrofs.unsigned address) bytes = Some memory' ->
  length bytes = 8%nat -> load_value_casting (decode_val Mint64 bytes) = value ->
  memory_eq_holds memory' (Vptr b address) value.
Proof.
  intros memory memory' b address bytes value STORE LENGTH DECODE.
  cbn [memory_eq_holds]. rewrite (Mem.storebytes_mem_contents _ _ _ _ _ STORE), PMap.gss.
  rewrite <- LENGTH, Mem.getN_setN_same. exact DECODE.
Qed.

Lemma valid_pointer_storebytes : forall memory memory' b offset bytes,
  Mem.storebytes memory b offset bytes = Some memory' ->
  Mem.valid_pointer memory' = Mem.valid_pointer memory.
Proof.
  intros. unfold Mem.valid_pointer, Mem.perm_dec, Mem.perm.
  now rewrite (Mem.storebytes_access _ _ _ _ _ H).
Qed.

(** A byte interval is initialized exactly when each of its entries is. *)
Lemma initialized_getN : forall n start contents,
  Forall initialized_byte (Mem.getN n start contents) <->
  (forall address, start <= address < start + Z.of_nat n ->
    initialized_byte (ZMap.get address contents)).
Proof.
  induction n as [| n IH]; intros start contents; cbn [Mem.getN].
  - split; [intros _ address BOUNDS; lia | intros; constructor].
  - rewrite Forall_cons_iff, IH. rewrite Nat2Z.inj_succ.
    split.
    + intros [HEAD TAIL] address BOUNDS.
      destruct (Z.eq_dec address start); [now subst | apply TAIL; lia].
    + intros ALL. split; [apply ALL; lia | intros; apply ALL; lia].
Qed.

(** Writing initialized bytes cannot make an already initialized interval
    uninitialized, even when the intervals overlap. *)
Lemma initialized_bytes_storebytes : forall memory memory' b offset bytes address count,
  Mem.storebytes memory b offset bytes = Some memory' ->
  Forall initialized_byte bytes ->
  initialized_bytes memory address count -> initialized_bytes memory' address count.
Proof.
  Local Transparent Mem.loadbytes.
  intros memory memory' b offset bytes address count STORE WRITTEN INIT.
  destruct address; cbn [initialized_bytes] in *; try contradiction.
  destruct INIT as [old [READ INIT]].
  unfold Mem.loadbytes in READ.
  destruct (Mem.range_perm_dec memory b0 (Ptrofs.unsigned i)
    (Ptrofs.unsigned i + count) Cur Memtype.Readable) as [PERM |]; try discriminate.
  inversion READ; subst old.
  pose proof (proj1 (initialized_getN (Z.to_nat count) (Ptrofs.unsigned i)
    (PMap.get b0 (Mem.mem_contents memory))) INIT) as EACH.
  exists (Mem.getN (Z.to_nat count) (Ptrofs.unsigned i)
    (PMap.get b0 (Mem.mem_contents memory'))). split.
  - unfold Mem.loadbytes. rewrite pred_dec_true; [reflexivity |].
    intros pos BOUNDS. eapply Mem.perm_storebytes_1; eauto.
  - apply (proj2 (initialized_getN _ _ _)). intros pos BOUNDS.
    rewrite (Mem.storebytes_mem_contents _ _ _ _ _ STORE), PMap.gsspec.
    destruct (peq b0 b); [subst b0 | now apply EACH].
    destruct (Z_le_dec offset pos), (Z_lt_dec pos (offset + Z.of_nat (length bytes))).
    + apply Forall_forall with (x := ZMap.get pos
        (Mem.setN bytes offset (PMap.get b (Mem.mem_contents memory)))) in WRITTEN.
      * exact WRITTEN.
      * apply Mem.setN_in; lia.
    + rewrite Mem.setN_outside by lia. now apply EACH.
    + rewrite Mem.setN_outside by lia. now apply EACH.
    + rewrite Mem.setN_outside by lia. now apply EACH.
Qed.

Definition byte_initialized (memory : mem) (b : block) (position : Z) : Prop :=
  initialized_byte (ZMap.get position (PMap.get b (Mem.mem_contents memory))).

Lemma initialized_bytes_positions : forall memory b address width,
  initialized_bytes memory (Vptr b address) width ->
  forall delta, 0 <= delta < width ->
    byte_initialized memory b (Ptrofs.unsigned address + delta).
Proof.
  intros memory b address width [contents [READ INIT]] delta DELTA.
  unfold Mem.loadbytes in READ.
  destruct (Mem.range_perm_dec _ _ _ _ _ _); try discriminate.
  inversion READ; subst contents.
  apply (proj1 (initialized_getN _ _ _) INIT). rewrite Z2Nat.id by lia. lia.
Qed.

Lemma initialized_bytes_from_positions : forall memory b address width,
  Mem.range_perm memory b (Ptrofs.unsigned address) (Ptrofs.unsigned address + width)
    Cur Memtype.Readable ->
  (forall delta, 0 <= delta < width ->
    byte_initialized memory b (Ptrofs.unsigned address + delta)) ->
  initialized_bytes memory (Vptr b address) width.
Proof.
  intros memory b address width PERM EACH.
  destruct (Z_le_dec width 0) as [EMPTY | NONEMPTY].
  - exists []. split; [apply Mem.loadbytes_empty; exact EMPTY | constructor].
  - exists (Mem.getN (Z.to_nat width) (Ptrofs.unsigned address)
      (PMap.get b (Mem.mem_contents memory))). split.
    + unfold Mem.loadbytes. rewrite pred_dec_true by exact PERM. reflexivity.
    + apply (proj2 (initialized_getN _ _ _)). intros position BOUNDS.
      rewrite Z2Nat.id in BOUNDS by lia.
      replace position
        with (Ptrofs.unsigned address + (position - Ptrofs.unsigned address)) by lia.
      apply EACH. lia.
Qed.

Lemma load_loadbytes : forall size b address memory loaded,
  load size (Vptr b address) memory = Some loaded ->
  exists bytes, Mem.loadbytes memory b (Ptrofs.unsigned address) (load_width size) = Some bytes.
Proof.
  intros size b address memory loaded LOAD.
  unfold load, loadv_unaligned in LOAD.
  destruct size; cbn [size_chunk load_width] in *;
    destruct (Mem.loadbytes _ _ _ _) as [bytes |]; try discriminate; eauto.
Qed.

Lemma initialized_load_exists : forall memory base offset size,
  initialized_bytes memory (Val.offset_ptr base (Ptrofs.repr offset)) (load_width size) ->
  exists loaded, load_at_offset memory base offset size = Some loaded.
Proof.
  intros memory base offset size INIT.
  destruct base; cbn [Val.offset_ptr initialized_bytes] in INIT; try contradiction.
  destruct INIT as [contents [READ _]].
  unfold load_at_offset, load, loadv_unaligned. cbn [Val.offset_ptr].
  destruct size; cbn [size_chunk load_width] in *; rewrite READ; eauto.
Qed.

Lemma initialized_window_storebytes : forall memory memory' b offset bytes address window,
  Mem.storebytes memory b offset bytes = Some memory' ->
  Forall initialized_byte bytes ->
  initialized_readable_window memory address window ->
  initialized_readable_window memory' address window.
Proof.
  intros memory memory' b offset bytes address window STORE WRITTEN [RANGE INIT].
  split; [exact RANGE |]. destruct address; try contradiction.
  destruct INIT as [HIGH INIT]. split; [exact HIGH |].
  eapply initialized_bytes_storebytes; eauto.
Qed.

Lemma region_bytes_addressable_subrange : forall world region outer inner,
  region_bytes_addressable world region outer ->
  lower outer <= lower inner -> upper inner <= upper outer -> lower inner <= upper inner ->
  region_bytes_addressable world region inner.
Proof.
  intros world region outer inner ADDRESSABLE LEFT RIGHT ORDER.
  unfold region_bytes_addressable, region_address in *.
  destruct (region_location world region) as [[b origin] |]; [| contradiction].
  pose proof (Ptrofs.unsigned_range (Ptrofs.repr (origin + lower inner))).
  destruct (Z.eq_dec (lower inner) (upper outer)) as [TOP | INSIDE]; [lia |].
  replace (origin + lower inner) with (origin + (lower outer + (lower inner - lower outer))) by lia.
  rewrite (repr_subrange_start origin (lower outer) (upper outer - lower outer)
    (lower inner - lower outer) ADDRESSABLE ltac:(lia)). lia.
Qed.

(** An initialized, addressable interval has initialized subintervals.
    This is the byte-level argument needed for residual cells after a store;
    it does not claim that partial reads decode to a defined register value. *)
Lemma initialized_bytes_subrange : forall memory b origin outer inner,
  Ptrofs.unsigned (Ptrofs.repr (origin + lower outer)) + (upper outer - lower outer)
    <= Ptrofs.modulus ->
  lower outer <= lower inner -> upper inner <= upper outer ->
  lower inner <= upper inner ->
  initialized_bytes memory (Vptr b (Ptrofs.repr (origin + lower outer)))
    (upper outer - lower outer) ->
  initialized_bytes memory (Vptr b (Ptrofs.repr (origin + lower inner)))
    (upper inner - lower inner).
Proof.
  intros memory b origin outer inner ADDRESSABLE LEFT RIGHT ORDER [contents [READ INIT]].
  destruct (Z.eq_dec (lower inner) (upper inner)) as [EMPTY | NONEMPTY].
  - exists []; split; [apply Mem.loadbytes_empty; lia | constructor].
  - assert (SUBSTART : Ptrofs.unsigned (Ptrofs.repr (origin + lower inner)) =
      Ptrofs.unsigned (Ptrofs.repr (origin + lower outer)) + (lower inner - lower outer)).
    { replace (origin + lower inner)
        with (origin + (lower outer + (lower inner - lower outer))) by lia.
      apply (repr_subrange_start origin (lower outer) (upper outer - lower outer));
        [exact ADDRESSABLE | lia]. }
    replace (upper outer - lower outer) with
      ((lower inner - lower outer) + (upper outer - lower inner)) in READ by lia.
    destruct (Mem.loadbytes_split _ _ _ _ _ _ READ ltac:(lia) ltac:(lia))
      as [prefix [rest [_ [REST CONTENTS]]]].
    rewrite <- SUBSTART in REST.
    replace (upper outer - lower inner) with
      ((upper inner - lower inner) + (upper outer - upper inner)) in REST by lia.
    destruct (Mem.loadbytes_split _ _ _ _ _ _ REST ltac:(lia) ltac:(lia))
      as [middle [suffix [MIDDLE [_ REST_CONTENTS]]]].
    exists middle. split; [exact MIDDLE |].
    rewrite CONTENTS, REST_CONTENTS in INIT.
    apply Forall_app in INIT as [_ INIT].
    now apply Forall_app in INIT as [INIT _].
Qed.

(** ** Pointer-free bytes *)

Lemma getN_forall : forall (property : memval -> Prop) n start contents,
  Forall property (Mem.getN n start contents) <->
  (forall address, start <= address < start + Z.of_nat n ->
    property (ZMap.get address contents)).
Proof.
  intros property. induction n as [| n IH]; intros start contents; cbn [Mem.getN].
  - split; [intros _ address BOUNDS; lia | intros; constructor].
  - rewrite Forall_cons_iff, IH. rewrite Nat2Z.inj_succ.
    split.
    + intros [HEAD TAIL] address BOUNDS.
      destruct (Z.eq_dec address start); [now subst | apply TAIL; lia].
    + intros ALL. split; [apply ALL; lia | intros; apply ALL; lia].
Qed.

Definition byte_pointer_free (memory : mem) (b : block) (position : Z) : Prop :=
  pointer_free_byte (ZMap.get position (PMap.get b (Mem.mem_contents memory))).

Lemma pointer_free_bytes_positions : forall memory b address width,
  pointer_free_bytes memory (Vptr b address) width ->
  forall delta, 0 <= delta < width ->
    byte_pointer_free memory b (Ptrofs.unsigned address + delta).
Proof.
  intros memory b address width [contents [READ FREE]] delta DELTA.
  unfold Mem.loadbytes in READ.
  destruct (Mem.range_perm_dec _ _ _ _ _ _); try discriminate.
  inversion READ; subst contents.
  apply (proj1 (getN_forall _ _ _ _) FREE). rewrite Z2Nat.id by lia. lia.
Qed.

Lemma pointer_free_bytes_from_positions : forall memory b address width,
  Mem.range_perm memory b (Ptrofs.unsigned address) (Ptrofs.unsigned address + width)
    Cur Memtype.Readable ->
  (forall delta, 0 <= delta < width ->
    byte_pointer_free memory b (Ptrofs.unsigned address + delta)) ->
  pointer_free_bytes memory (Vptr b address) width.
Proof.
  intros memory b address width PERM EACH.
  destruct (Z_le_dec width 0) as [EMPTY | NONEMPTY].
  - exists []. split; [apply Mem.loadbytes_empty; exact EMPTY | constructor].
  - exists (Mem.getN (Z.to_nat width) (Ptrofs.unsigned address)
      (PMap.get b (Mem.mem_contents memory))). split.
    + unfold Mem.loadbytes. rewrite pred_dec_true by exact PERM. reflexivity.
    + apply (proj2 (getN_forall _ _ _ _)). intros position BOUNDS.
      rewrite Z2Nat.id in BOUNDS by lia.
      replace position
        with (Ptrofs.unsigned address + (position - Ptrofs.unsigned address)) by lia.
      apply EACH. lia.
Qed.

(** Writing pointer-free bytes keeps every pointer-free interval so, even when
    the intervals overlap. *)
Lemma pointer_free_bytes_storebytes : forall memory memory' b offset bytes address count,
  Mem.storebytes memory b offset bytes = Some memory' ->
  Forall pointer_free_byte bytes ->
  pointer_free_bytes memory address count -> pointer_free_bytes memory' address count.
Proof.
  intros memory memory' b offset bytes address count STORE WRITTEN FREE.
  destruct address; cbn [pointer_free_bytes] in *; try contradiction.
  destruct FREE as [old [READ FREE]].
  unfold Mem.loadbytes in READ.
  destruct (Mem.range_perm_dec memory b0 (Ptrofs.unsigned i)
    (Ptrofs.unsigned i + count) Cur Memtype.Readable) as [PERM |]; try discriminate.
  inversion READ; subst old.
  pose proof (proj1 (getN_forall _ (Z.to_nat count) (Ptrofs.unsigned i)
    (PMap.get b0 (Mem.mem_contents memory))) FREE) as EACH.
  exists (Mem.getN (Z.to_nat count) (Ptrofs.unsigned i)
    (PMap.get b0 (Mem.mem_contents memory'))). split.
  - unfold Mem.loadbytes. rewrite pred_dec_true; [reflexivity |].
    intros pos BOUNDS. eapply Mem.perm_storebytes_1; eauto.
  - apply (proj2 (getN_forall _ _ _ _)). intros pos BOUNDS.
    rewrite (Mem.storebytes_mem_contents _ _ _ _ _ STORE), PMap.gsspec.
    destruct (peq b0 b); [subst b0 | now apply EACH].
    destruct (Z_le_dec offset pos), (Z_lt_dec pos (offset + Z.of_nat (length bytes))).
    + apply Forall_forall with (x := ZMap.get pos
        (Mem.setN bytes offset (PMap.get b (Mem.mem_contents memory)))) in WRITTEN.
      * exact WRITTEN.
      * apply Mem.setN_in; lia.
    + rewrite Mem.setN_outside by lia. now apply EACH.
    + rewrite Mem.setN_outside by lia. now apply EACH.
    + rewrite Mem.setN_outside by lia. now apply EACH.
Qed.

Lemma pointer_free_bytes_storebytes_disjoint :
  forall memory memory' b start bytes other address count,
    Mem.storebytes memory b start bytes = Some memory' ->
    (count <= 0 \/ other <> b \/ Ptrofs.unsigned address + count <= start \/
      start + Z.of_nat (length bytes) <= Ptrofs.unsigned address) ->
    pointer_free_bytes memory (Vptr other address) count ->
    pointer_free_bytes memory' (Vptr other address) count.
Proof.
  intros memory memory' b start bytes other address count STORE DISJOINT
    [contents [READ FREE]].
  destruct (Z_le_dec count 0) as [EMPTY | NONEMPTY].
  - exists []. split; [apply Mem.loadbytes_empty; exact EMPTY | constructor].
  - exists contents. split; [| exact FREE].
    rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ STORE); [exact READ | lia |].
    destruct DISJOINT as [EMPTY | DISJOINT]; [lia | exact DISJOINT].
Qed.

Lemma pointer_free_bytes_subrange : forall memory b origin outer inner,
  Ptrofs.unsigned (Ptrofs.repr (origin + lower outer)) + (upper outer - lower outer)
    <= Ptrofs.modulus ->
  lower outer <= lower inner -> upper inner <= upper outer ->
  lower inner <= upper inner ->
  pointer_free_bytes memory (Vptr b (Ptrofs.repr (origin + lower outer)))
    (upper outer - lower outer) ->
  pointer_free_bytes memory (Vptr b (Ptrofs.repr (origin + lower inner)))
    (upper inner - lower inner).
Proof.
  intros memory b origin outer inner ADDRESSABLE LEFT RIGHT ORDER [contents [READ FREE]].
  destruct (Z.eq_dec (lower inner) (upper inner)) as [EMPTY | NONEMPTY].
  - exists []; split; [apply Mem.loadbytes_empty; lia | constructor].
  - assert (SUBSTART : Ptrofs.unsigned (Ptrofs.repr (origin + lower inner)) =
      Ptrofs.unsigned (Ptrofs.repr (origin + lower outer)) + (lower inner - lower outer)).
    { replace (origin + lower inner)
        with (origin + (lower outer + (lower inner - lower outer))) by lia.
      apply (repr_subrange_start origin (lower outer) (upper outer - lower outer));
        [exact ADDRESSABLE | lia]. }
    replace (upper outer - lower outer) with
      ((lower inner - lower outer) + (upper outer - lower inner)) in READ by lia.
    destruct (Mem.loadbytes_split _ _ _ _ _ _ READ ltac:(lia) ltac:(lia))
      as [prefix [rest [_ [REST CONTENTS]]]].
    rewrite <- SUBSTART in REST.
    replace (upper outer - lower inner) with
      ((upper inner - lower inner) + (upper outer - upper inner)) in REST by lia.
    destruct (Mem.loadbytes_split _ _ _ _ _ _ REST ltac:(lia) ltac:(lia))
      as [middle [suffix [MIDDLE [_ REST_CONTENTS]]]].
    exists middle. split; [exact MIDDLE |].
    rewrite CONTENTS, REST_CONTENTS in FREE.
    apply Forall_app in FREE as [_ FREE].
    now apply Forall_app in FREE as [FREE _].
Qed.

Lemma check_value_fragments : forall n v q bytes,
  check_value n v q bytes = true ->
  Forall (fun entry => exists q' m, entry = Fragment v q' m) bytes.
Proof.
  induction n as [| n IH]; intros v q bytes CHECK;
    destruct bytes as [| entry rest]; cbn in CHECK; try discriminate.
  - constructor.
  - destruct entry as [| | v' q' m]; try discriminate.
    repeat rewrite andb_true_iff in CHECK. destruct CHECK as [[[SAME _] _] REST].
    apply proj_sumbool_true in SAME. subst v'.
    constructor; [eauto | exact (IH _ _ _ REST)].
Qed.

Lemma proj_value_pointer_free : forall q bytes,
  proj_value q bytes <> Vundef -> (forall b o, proj_value q bytes <> Vptr b o) ->
  Forall pointer_free_byte bytes.
Proof.
  intros q bytes DEFINED NOT_POINTER. unfold proj_value in *.
  destruct bytes as [| [| | v q' m] rest]; try contradiction.
  destruct (check_value (size_quantity_nat q) v q (Fragment v q' m :: rest)) eqn:CHECK;
    [| contradiction].
  apply check_value_fragments in CHECK.
  apply Forall_forall. intros entry IN.
  destruct (proj1 (Forall_forall _ _) CHECK entry IN) as [q'' [m' ->]].
  destruct v; cbn; try exact I. exact (NOT_POINTER b i eq_refl).
Qed.

(** Bytes that decode to an integer hold no part of a stored pointer. *)
Lemma decode_long_pointer_free : forall chunk bytes n,
  load_value_casting (decode_val chunk bytes) = Vlong n ->
  Forall pointer_free_byte bytes.
Proof.
  intros chunk bytes n DECODE. unfold decode_val in DECODE.
  destruct (proj_bytes bytes) as [bl |] eqn:PROJ.
  - rewrite (inj_proj_bytes _ _ PROJ). unfold inj_bytes.
    apply Forall_forall. intros entry IN. apply in_map_iff in IN as [x [<- _]]. exact I.
  - destruct chunk; cbn in DECODE; try discriminate.
    all: match type of DECODE with context [proj_value ?q _] =>
      apply (proj_value_pointer_free q);
      [intros UNDEF; rewrite UNDEF in DECODE; discriminate
      | intros b o POINTER; rewrite POINTER in DECODE; discriminate] end.
Qed.

Lemma decode_pointer_free_not_pointer : forall bytes b o,
  Forall pointer_free_byte bytes -> decode_val Mint64 bytes <> Vptr b o.
Proof.
  intros bytes b o FREE. unfold decode_val.
  destruct (proj_bytes bytes); [discriminate |]. cbn. unfold proj_value.
  destruct bytes as [| [| | v q m] rest]; try discriminate.
  inversion FREE as [| entry others HEAD]; subst.
  destruct (check_value _ _ _ _); [| discriminate].
  destruct v; cbn in HEAD |- *; try discriminate. contradiction.
Qed.

(** A defined load is an integer unless it reads a whole stored pointer. *)
Lemma load_result_long : forall size b address memory loaded,
  load size (Vptr b address) memory = Some loaded ->
  load_value_casting loaded <> Vundef ->
  (size = DBWord -> forall b' o, loaded <> Vptr b' o) ->
  exists n, load_value_casting loaded = Vlong n.
Proof.
  intros size b address memory loaded LOAD DEFINED NOT_POINTER.
  unfold load, loadv_unaligned in LOAD.
  destruct size; cbn [size_chunk] in LOAD;
    destruct (Mem.loadbytes memory b (Ptrofs.unsigned address) _) as [bytes |];
    try discriminate; injection LOAD as <-; unfold decode_val in *;
    destruct (proj_bytes bytes); cbn [Archi.ptr64] in *; cbn in *; eauto; try contradiction.
  destruct (proj_value Q64 bytes); cbn in *; eauto; try contradiction.
  exfalso. eapply NOT_POINTER; reflexivity.
Qed.

Lemma load_pointer_free_long : forall size b address memory loaded,
  load size (Vptr b address) memory = Some loaded ->
  pointer_free_bytes memory (Vptr b address) (load_width size) ->
  load_value_casting loaded <> Vundef ->
  exists n, load_value_casting loaded = Vlong n.
Proof.
  intros size b address memory loaded LOAD [contents [READ FREE]] DEFINED.
  apply (load_result_long _ _ _ _ _ LOAD DEFINED). intros DOUBLE b' o POINTER. subst size.
  unfold load, loadv_unaligned in LOAD. cbn [size_chunk load_width] in *.
  rewrite READ in LOAD. injection LOAD as LOADED. rewrite POINTER in LOADED.
  exact (decode_pointer_free_not_pointer _ _ _ FREE LOADED).
Qed.

(** Encoding a value that is not a pointer stores no part of one. *)
Lemma encode_pointer_free : forall chunk value,
  (forall b o, value <> Vptr b o) -> Forall pointer_free_byte (encode_val chunk value).
Proof.
  intros chunk value NOT_POINTER.
  assert (BYTES : forall bl, Forall pointer_free_byte (inj_bytes bl)).
  { intros bl. apply Forall_forall. intros entry IN.
    apply in_map_iff in IN as [x [<- _]]. exact I. }
  assert (UNDEF : forall n, Forall pointer_free_byte (List.repeat Undef n)).
  { intros n. apply Forall_forall. intros entry IN.
    apply repeat_spec in IN. subst entry. exact I. }
  assert (FRAGMENTS : forall q, Forall pointer_free_byte (inj_value q value)).
  { intros q. unfold inj_value. induction (size_quantity_nat q); cbn; constructor; auto.
    destruct value; cbn; try exact I. exact (NOT_POINTER b i eq_refl). }
  destruct value; [| | | | | exfalso; exact (NOT_POINTER b i eq_refl)];
    destruct chunk; cbn [encode_val]; auto.
Qed.

(** Ordinary writes preserve facts about values, comparisons, ownership and
    already initialized readable windows. Facts describing stored contents
    require a separate disjointness or overwrite argument. *)
Lemma atom_holds_storebytes_without_cell :
  forall world memory memory' fact b offset bytes,
    Mem.storebytes memory b offset bytes = Some memory' ->
    Forall initialized_byte bytes ->
    (match fact with
     | MemoryCell _ _ _ | MemoryEq _ _ _ | ReadableCell _ _ _ => False
     | _ => True
     end) ->
    atom_holds world memory fact -> atom_holds world memory' fact.
Proof.
  intros world memory memory' fact b offset bytes STORE INIT NOT_CELL HOLDS.
  destruct fact; cbn [atom_holds] in *; try contradiction; try exact HOLDS.
  - now rewrite (allocation_metadata_storebytes _ _ _ _ _ STORE).
  - eapply value_holds_storebytes; eauto.
  - unfold comparison_is_true in *.
    now rewrite (valid_pointer_storebytes _ _ _ _ _ STORE).
  - unfold comparison_is_true in *.
    now rewrite (valid_pointer_storebytes _ _ _ _ _ STORE).
  - intros GUARD. eapply value_holds_storebytes; [exact STORE | apply HOLDS].
    unfold guard_is_true in *.
    now rewrite (valid_pointer_storebytes _ _ _ _ _ STORE) in GUARD.
  - eapply initialized_window_storebytes; eauto.
Qed.

Lemma load_storebytes_disjoint : forall memory memory' b start bytes other address size,
  Mem.storebytes memory b start bytes = Some memory' ->
  (other <> b \/ Ptrofs.unsigned address + load_width size <= start \/
    start + Z.of_nat (length bytes) <= Ptrofs.unsigned address) ->
  load size (Vptr other address) memory' = load size (Vptr other address) memory.
Proof.
  intros memory memory' b start bytes other address size STORE DISJOINT.
  destruct size; cbn [load load_width] in *; unfold loadv_unaligned;
    rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ STORE)
      by (cbn; auto with zarith); reflexivity.
Qed.

(** Integer writes preserve initialization everywhere; the stored-value part
    of a cell additionally needs its read footprint to be disjoint. *)
Lemma cell_holds_storebytes_disjoint :
  forall world memory memory' b start bytes region window abstract,
    Mem.storebytes memory b start bytes = Some memory' ->
    Forall initialized_byte bytes ->
    (forall other address,
      region_address world region (lower window) = Vptr other address ->
      upper window <= lower window \/
      other <> b \/ Ptrofs.unsigned address + (upper window - lower window) <= start \/
        start + Z.of_nat (length bytes) <= Ptrofs.unsigned address) ->
    cell_holds world memory region window abstract ->
    cell_holds world memory' region window abstract.
Proof.
  intros world memory memory' b start bytes region window abstract STORE INIT DISJOINT CELL.
  destruct abstract; cbn [cell_holds cell_value_holds] in *; try exact I.
  all: try solve [destruct CELL as [ORDER [ADDRESSABLE [INITIALIZED FREE]]];
    split; [exact ORDER |]; split; [exact ADDRESSABLE |]; split;
    [eapply initialized_bytes_storebytes; eauto |];
    unfold region_address in FREE |- *;
    destruct (region_location world region) as [[other origin]|] eqn:LOCATION;
    [| contradiction];
    eapply pointer_free_bytes_storebytes_disjoint; [exact STORE | | exact FREE];
    destruct (DISJOINT other (Ptrofs.repr (origin + lower window))) as [EMPTY | SEPARATE];
    [unfold region_address; now rewrite LOCATION | left; lia | right; exact SEPARATE]].
  all: try (destruct (Region.uninit_by_default region);
    [destruct CELL as [ORDER [ADDRESSABLE INITIALIZED]];
      split; [exact ORDER |]; split; [exact ADDRESSABLE |];
      eapply initialized_bytes_storebytes; eauto | exact I]).
  all: destruct CELL as [ORDER [ADDRESSABLE [INITIALIZED [size [WIDTH VALUE]]]]];
    split; [exact ORDER |]; split; [exact ADDRESSABLE |]; split;
    [eapply initialized_bytes_storebytes; eauto |];
    exists size; split; [exact WIDTH |].
  all: assert (LOAD : load size (region_address world region (lower window)) memory' =
    load size (region_address world region (lower window)) memory).
  all: try (unfold region_address;
    destruct (region_location world region) as [[other origin]|] eqn:LOCATION;
    [apply load_storebytes_disjoint with (b := b) (start := start) (bytes := bytes);
      [exact STORE | rewrite WIDTH;
        destruct (DISJOINT other (Ptrofs.repr (origin + lower window)))
          as [EMPTY | SEPARATE];
        [unfold region_address; now rewrite LOCATION
        | destruct size; cbn [load_width] in WIDTH; lia
        | exact SEPARATE]]
    | destruct size; reflexivity]).
  all: rewrite LOAD; unfold cell_result_holds in *;
    destruct (load size (region_address world region (lower window)) memory);
    [eapply value_holds_storebytes; eauto
    | destruct (Region.probe_readable region); try contradiction;
      eapply value_holds_storebytes; eauto].
Qed.

Lemma memory_eq_storebytes_disjoint :
  forall memory memory' b start bytes other address value,
    Mem.storebytes memory b start bytes = Some memory' ->
    (other <> b \/ Ptrofs.unsigned address + 8 <= start \/
      start + Z.of_nat (length bytes) <= Ptrofs.unsigned address) ->
    memory_eq_holds memory (Vptr other address) value ->
    memory_eq_holds memory' (Vptr other address) value.
Proof.
  intros memory memory' b start bytes other address value STORE DISJOINT EQ.
  cbn [memory_eq_holds] in *. rewrite (Mem.storebytes_mem_contents _ _ _ _ _ STORE).
  rewrite PMap.gsspec. destruct (peq other b) as [SAME | DIFFERENT]; [subst other | exact EQ].
  rewrite Mem.getN_setN_outside; [exact EQ |]. cbn.
  destruct DISJOINT as [DIFFERENT | DISJOINT]; [contradiction | exact DISJOINT].
Qed.


(** A residual [Unknown] cell is justified by the original cell's initialized
    bytes, not by the mere existence of a [MemoryCell] atom. *)
Lemma unknown_subcell_after_store :
  forall world memory memory' state b start bytes region outer inner abstract,
    Forall (atom_holds world memory) state ->
    no_uninit_memory_cells state ->
    In (MemoryCell region outer abstract) state ->
    lower outer <= lower inner -> upper inner <= upper outer ->
    lower inner <= upper inner ->
    Mem.storebytes memory b start bytes = Some memory' ->
    Forall initialized_byte bytes ->
    cell_holds world memory' region inner Unknown.
Proof.
  intros world memory memory' state b start bytes region outer inner abstract
    FACTS VALID IN LEFT RIGHT ORDER STORE INIT.
  cbn [cell_holds]. destruct (Region.uninit_by_default region) eqn:STACK; [| exact I].
  unfold no_uninit_memory_cells in VALID. rewrite Forall_forall in FACTS, VALID.
  pose proof (FACTS _ IN) as CELL. pose proof (VALID _ IN) as DEFINED.
  assert (OLD : region_bytes_addressable world region outer /\
    initialized_bytes memory (region_address world region (lower outer))
      (upper outer - lower outer)).
  { destruct abstract; cbn [atom_holds cell_holds] in CELL;
      try contradiction DEFINED; try tauto.
    rewrite STACK in CELL. tauto. }
  destruct OLD as [ADDRESSABLE OLD].
  split; [exact ORDER |].
  split; [eapply region_bytes_addressable_subrange; eauto |].
  unfold region_bytes_addressable, region_address in ADDRESSABLE, OLD |- *.
  destruct (region_location world region) as [[other origin]|] eqn:LOCATION;
    [| contradiction].
  eapply initialized_bytes_subrange; eauto.
  eapply initialized_bytes_storebytes; eauto.
Qed.

(** Permission promotion changes no address field. A precise accepted write
    therefore addresses exactly the cell named by its checked range. *)
Lemma exact_checked_store_address :
  forall world memory state base ptr value policy offset width access region,
    find_pointer_fact state base = Some ptr ->
    pointer_state_holds world memory ptr value ->
    checked_write_access_range state base offset width policy = Some access ->
    access_exact access = true ->
    Region.cells (ptr_ty (access_ptr access)) = Some region ->
    region_address world region (lower (access_range access)) =
      Val.offset_ptr value (Ptrofs.repr offset).
Proof.
  intros world memory state base ptr value policy offset width access region
    FIND [_ [ADDRESS [_ [NULL _]]]] CHECK EXACT CELLS.
  unfold checked_write_access_range in CHECK. rewrite FIND in CHECK.
  destruct (Region.is (ptr_ty ptr) RegionClass.CTX ||
    (negb (permission_includes (ptr_permission ptr) Write) &&
     write_window_grants policy ptr offset width));
    apply filter_special_access_some in CHECK;
    apply filter_context_access_some in CHECK;
    pose proof (checked_write_window _ _ _ _ _ CHECK) as [_ [NONNULL _]];
    apply checked_write_access_shape in CHECK; subst access.
  all: change (ptr_nullability ptr = NonNull) in NONNULL;
    change (Z.eqb (ptr_off_min ptr) (ptr_off_max ptr) = true) in EXACT;
    change (Region.cells (ptr_ty ptr) = Some region) in CELLS;
    change (region_address world region (ptr_off_min ptr + offset) =
      Val.offset_ptr value (Ptrofs.repr offset)).
  all: unfold pointer_nullability_holds in NULL; rewrite NONNULL in NULL;
    pose proof (non_null_base_ordinary_value ptr value NULL
      (or_introl (cells_not_probe_readable _ _ CELLS))) as NONZERO;
    unfold pointer_region_holds in ADDRESS; rewrite NONNULL in ADDRESS;
    assert (POINTER : pointer_address world ptr value)
      by (eapply cells_pointer_address; eauto);
    unfold pointer_address in POINTER; rewrite CELLS in POINTER;
    destruct POINTER as [actual [[[LOW HIGH] _] VALUE]];
    apply Z.eqb_eq in EXACT;
    assert (actual = ptr_off_min ptr) by lia; subst actual.
  all: unfold region_address in VALUE |- *;
    destruct (region_location world region) as [[b origin]|];
    [subst value | subst value; contradiction].
  all: cbn [Val.offset_ptr]; rewrite ptrofs_add_repr; f_equal;
    replace (origin + (ptr_off_min ptr + offset))
      with ((origin + ptr_off_min ptr) + offset) by lia;
    apply Ptrofs.eqm_samerepr; apply Ptrofs.eqm_add;
    [apply Ptrofs.eqm_unsigned_repr | apply Ptrofs.eqm_refl].
Qed.

(** Stores preserve permissions, so policy guarantees survive even though
    memory contents change. This does not establish preservation of facts. *)
Lemma store_policy_holds_storebytes : forall world attrs memory memory' b offset bytes,
  Mem.storebytes memory b offset bytes = Some memory' ->
  store_policy_holds world memory attrs ->
  store_policy_holds world memory' attrs.
Proof.
  intros world attrs memory memory' b offset bytes STORE POLICY.
  unfold store_policy_holds in *. apply Forall_forall.
  intros window IN. rewrite Forall_forall in POLICY.
  destruct (POLICY window IN) as [RANGE [ORDINARY OBJECTS]].
  split; [exact RANGE |]. split; [exact ORDINARY |].
  intros block origin OBJECT.
  destruct (OBJECTS block origin OBJECT) as [ADDRESSABLE WRITE].
  split; [exact ADDRESSABLE |].
  cbv zeta in WRITE |- *.
  intros address BOUNDS. eapply Mem.perm_storebytes_1; eauto.
Qed.

Lemma offset_ptr_addl_repr : forall value x y,
  Val.offset_ptr (Val.addl value (Vlong (Int64.repr x))) (Ptrofs.repr y) =
  Val.offset_ptr value (Ptrofs.repr (x + y)).
Proof.
  intros value x y. destruct value;
    cbn [Val.addl Val.offset_ptr Archi.ptr64]; try reflexivity.
  rewrite (Ptrofs.agree64_of_int_eq _ _
    (Ptrofs.agree64_repr eq_refl x)).
  rewrite Ptrofs.add_assoc. f_equal. f_equal.
  unfold Ptrofs.add. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

(** The bytes of a load contained in a readable window are initialized. *)
Lemma initialized_readable_window_initialized : forall memory base bytes offset size,
  initialized_readable_window memory base bytes ->
  lower bytes <= offset -> offset + load_width size <= upper bytes ->
  initialized_bytes memory (Val.offset_ptr base (Ptrofs.repr offset)) (load_width size).
Proof.
  intros memory base bytes offset size [_ WINDOW] LOW HIGH.
  destruct base; try contradiction.
  destruct WINDOW as [END INIT].
  assert (WIDTH : 0 < load_width size) by (destruct size; cbn; lia).
  pose proof INIT as [contents [READ _]].
  cbn [Val.offset_ptr] in READ, INIT |- *.
  set (start := Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr (lower bytes)))) in *.
  pose proof (Ptrofs.unsigned_range (Ptrofs.add i (Ptrofs.repr (lower bytes)))) as START.
  fold start in START.
  assert (LOAD_START : Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr offset)) =
                       start + (offset - lower bytes)).
  { replace (Ptrofs.add i (Ptrofs.repr offset)) with
      (Ptrofs.add (Ptrofs.add i (Ptrofs.repr (lower bytes))) (Ptrofs.repr (offset - lower bytes))).
    - rewrite ptrofs_add_repr. fold start. apply Ptrofs.unsigned_repr.
      unfold Ptrofs.max_unsigned. lia.
    - rewrite Ptrofs.add_assoc. f_equal. unfold Ptrofs.add. apply Ptrofs.eqm_samerepr.
      apply Ptrofs.eqm_trans with (lower bytes + (offset - lower bytes)).
      + apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
      + replace (lower bytes + (offset - lower bytes)) with offset by lia.
        apply Ptrofs.eqm_refl. }
  pose proof (Mem.loadbytes_range_perm _ _ _ _ _ READ) as PERMISSIONS.
  apply initialized_bytes_from_positions; rewrite LOAD_START.
  - intros address INSIDE. apply PERMISSIONS. lia.
  - intros delta DELTA.
    replace (start + (offset - lower bytes) + delta)
      with (start + (offset - lower bytes + delta)) by lia.
    apply (initialized_bytes_positions _ _ _ _ INIT). lia.
Qed.

(** Integer load chunks can decode only an integer, a pointer, or [Vundef]. *)
Lemma load_result_runtime : forall size address memory loaded,
  load size address memory = Some loaded ->
  load_value_casting loaded <> Vundef ->
  runtime_value (load_value_casting loaded).
Proof.
  intros size address memory loaded LOAD DEFINED.
  destruct size; destruct address; try discriminate LOAD;
    unfold load, loadv_unaligned in LOAD;
    destruct (Mem.loadbytes _ _ _ _) as [bytes |]; try discriminate LOAD;
    inversion LOAD; subst loaded; clear LOAD;
    match type of DEFINED with
    | context [decode_val ?chunk ?bytes] =>
        pose proof (decode_val_type chunk bytes) as TYPE;
        destruct (decode_val chunk bytes)
    end;
    cbn [Val.has_type Archi.ptr64 type_of_chunk load_value_casting] in *;
    try contradiction; constructor.
Qed.


(** * Load-result bounds *)

(** Maximum result of a zero-extended subword load. The zero entry for
    [DBWord] is unused: [load_bounds] imposes no numeric bound at that size. *)
Definition load_upper_bound (size : sizeOp) : Z :=
  match size with Byte => 255 | HalfWord => 65535 | Word => 4294967295 | DBWord => 0 end.

(** Result facts emitted by the load transfer: a 64-bit integer or pointer,
    and, for subword loads, an integer within the zero-extended type range. *)
Definition load_bounds (size : sizeOp) (value : val) : Prop :=
  runtime_value value /\
  (size <> DBWord -> exists n,
    value = Vlong n /\
    0 <= Int64.unsigned n <= load_upper_bound size /\
    0 <= Int64.signed n <= load_upper_bound size).

Lemma load_bounds_repr : forall size n,
  0 <= n <= load_upper_bound size -> load_bounds size (Vlong (Int64.repr n)).
Proof.
  intros size n BOUND. split; [constructor |].
  intros NARROW. exists (Int64.repr n). split; [reflexivity |].
  rewrite Int64.unsigned_repr, Int64.signed_repr;
    unfold Int64.min_signed, Int64.max_signed, Int64.max_unsigned;
    destruct size; cbn in *; lia.
Qed.

Lemma load_bounds_zero : forall size, load_bounds size (Vlong Int64.zero).
Proof.
  intros size. apply load_bounds_repr. destruct size; cbn; lia.
Qed.

Lemma load_bounds_result : forall size address memory loaded,
  load size address memory = Some loaded ->
  runtime_value (load_value_casting loaded) ->
  load_bounds size (load_value_casting loaded).
Proof.
  intros size address memory loaded LOAD INITIALIZED.
  split; [exact INITIALIZED |]. intros NARROW.
  destruct size; try contradiction; destruct address; try discriminate LOAD;
    unfold load, loadv_unaligned in LOAD;
    destruct (Mem.loadbytes _ _ _ _) as [bytes |] eqn:BYTES; try discriminate LOAD;
    inversion LOAD; subst loaded; clear LOAD;
    unfold decode_val in *; destruct (proj_bytes bytes) as [bs |];
    cbn [load_value_casting] in *;
    try unfold Archi.ptr64 in *; try solve [inversion INITIALIZED].
  - apply load_bounds_repr; [| discriminate].
    pose proof (Int.zero_ext_range 8 (Int.repr (decode_int bs))) as BOUND.
    specialize (BOUND ltac:(change (0 <= 8 < 32); lia)).
    change (0 <= Int.unsigned (Int.zero_ext 8 (Int.repr (decode_int bs))) < 256) in BOUND.
    change (0 <= Int.unsigned (Int.zero_ext 8 (Int.repr (decode_int bs))) <= 255). lia.
  - apply load_bounds_repr; [| discriminate].
    pose proof (Int.zero_ext_range 16 (Int.repr (decode_int bs))) as BOUND.
    specialize (BOUND ltac:(change (0 <= 16 < 32); lia)).
    change (0 <= Int.unsigned (Int.zero_ext 16 (Int.repr (decode_int bs))) < 65536) in BOUND.
    change (0 <= Int.unsigned (Int.zero_ext 16 (Int.repr (decode_int bs))) <= 65535). lia.
  - apply load_bounds_repr; [| discriminate].
    pose proof (Int.unsigned_range_2 (Int.repr (decode_int bs))) as BOUND.
    exact BOUND.
Qed.

Lemma load_width_injective : forall x y,
  load_width x = load_width y -> x = y.
Proof. destruct x, y; cbn; intros EQ; discriminate || reflexivity. Qed.

(** Value recovery requires the cell's complete width and a precise value.
    [Uninit] promises no read; [Unknown] only promises byte initialization;
    [Scalar] promises pointer-free bytes, which still decode to [Vundef] when
    they are fragments of different values. *)
Lemma cell_holds_value : forall world memory region bytes abstract size,
  abstract <> Uninit ->
  abstract <> Unknown ->
  abstract <> Scalar ->
  load_width size = upper bytes - lower bytes ->
  cell_holds world memory region bytes abstract ->
  cell_result_holds world memory region abstract
    (load size (region_address world region (lower bytes)) memory).
Proof.
  intros world memory region bytes abstract size INITIALIZED KNOWN NOT_SCALAR WIDTH CELL.
  destruct abstract; try contradiction;
    destruct CELL as [_ [_ [_ CELL]]]; cbn [cell_value_holds] in CELL;
    destruct CELL as [stored_size [STORED VALUE]];
    assert (stored_size = size) by (apply load_width_injective; congruence);
    now subst stored_size.
Qed.

(** * Checked reads, shared by memory loads and helper inputs *)

Lemma checked_access_shape : forall ptr offset width strict access,
  checked_access_for_ptr ptr offset width strict = Some access ->
  access = CheckedAccess ptr
    (Range (ptr_off_min ptr + offset) (ptr_off_max ptr + offset + width))
    (Z.eqb (ptr_off_min ptr) (ptr_off_max ptr)).
Proof.
  intros ptr offset width strict access CHECK.
  unfold checked_access_for_ptr, i64_checked_add in CHECK.
  repeat match type of CHECK with
  | context [if ?test then _ else _] =>
      destruct test eqn:?; cbn beta iota zeta in CHECK; try discriminate
  end.
  now inversion CHECK.
Qed.

Lemma checked_read_permission : forall ptr offset width strict access,
  checked_access_for_ptr ptr offset width strict = Some access ->
  permission_includes (ptr_permission ptr) Read = true.
Proof.
  intros ptr offset width strict access CHECK.
  unfold checked_access_for_ptr in CHECK.
  destruct (permission_includes (ptr_permission ptr) Read) eqn:PERMISSION;
    [reflexivity | discriminate].
Qed.

Lemma checked_ordinary_window : forall ptr offset width strict access,
  Region.probe_readable (ptr_ty ptr) = false ->
  checked_access_for_ptr ptr offset width strict = Some access ->
  ptr_nullability ptr = NonNull /\ verified_window ptr offset width.
Proof.
  intros ptr offset width strict access ORDINARY CHECK.
  unfold checked_access_for_ptr in CHECK. rewrite ORDINARY in CHECK.
  destruct (permission_includes (ptr_permission ptr) Read); try discriminate.
  destruct (ptr_nullability ptr) eqn:NULL; try discriminate.
  destruct (i64_checked_add (ptr_off_min ptr) offset) as [start |] eqn:START;
    try discriminate.
  destruct (i64_checked_add (ptr_off_max ptr) offset) as [last |] eqn:LAST;
    try discriminate.
  destruct (i64_checked_add last width) as [finish |] eqn:FINISH;
    try discriminate.
  apply i64_checked_add_value in START, LAST, FINISH. subst start last finish.
  cbn beta iota zeta in CHECK. cbn [orb] in CHECK.
  destruct (_ && _) eqn:TEST; try discriminate.
  apply andb_true_iff in TEST as [BOUNDS _].
  apply andb_true_iff in BOUNDS as [LOW HIGH].
  apply Z.leb_le in LOW. apply orb_true_iff in HIGH.
  pose proof (u64_as_i64_le (ptr_size ptr)) as CAST.
  pose proof (stack_size_lower_le (ptr_size ptr)) as STACK_SIZE.
  split; [reflexivity |]. split.
  { unfold verified_window. destruct (Region.grows_down (ptr_ty ptr));
      cbn in LOW |- *; lia. }
  destruct HIGH as [HIGH | HIGH].
  - apply Z.leb_le in HIGH. left.
    destruct (Region.grows_down (ptr_ty ptr)); cbn in HIGH |- *; lia.
  - right. destruct (i64_checked_add offset width) as [needed |] eqn:NEEDED;
      try discriminate.
    destruct (ptr_end_min ptr) as [bound |] eqn:END; try discriminate.
    apply i64_checked_add_value in NEEDED. subst needed.
    exists bound. split; [reflexivity | now apply Z.leb_le].
Qed.

(** Bounds and read permissions establish a successful access, not that its
    bytes decode to a defined value. No initialization premise is used. *)
Lemma checked_ordinary_read : forall world memory ptr value offset size strict access,
  Region.probe_readable (ptr_ty ptr) = false ->
  checked_access_for_ptr ptr offset (load_width size) strict = Some access ->
  pointer_state_holds world memory ptr value ->
  exists loaded, load_at_offset memory value offset size = Some loaded.
Proof.
  intros world memory ptr value offset size strict access ORDINARY CHECK
    [_ [_ [RIGHTS [NULL _]]]].
  pose proof (checked_read_permission ptr offset (load_width size) strict access CHECK) as READ.
  destruct (checked_ordinary_window ptr offset (load_width size) strict access ORDINARY CHECK)
    as [NONNULL WINDOW].
  unfold pointer_nullability_holds in NULL. rewrite NONNULL in NULL.
  pose proof (non_null_base_ordinary_value ptr value NULL (or_introl ORDINARY)) as NONZERO.
  unfold pointer_permissions_holds in RIGHTS. rewrite NONNULL, ORDINARY in RIGHTS.
  destruct value as [| n32 | n64 | f64 | f32 | b address];
    cbn [pointer_access_holds] in RIGHTS; try discriminate RIGHTS; try congruence.
  assert (WIDTH : 0 < load_width size) by (destruct size; cbn; lia).
  specialize (RIGHTS offset (load_width size) WIDTH WINDOW).
  destruct RIGHTS as [_ PERMISSIONS].
  set (start := Ptrofs.unsigned (Ptrofs.add address (Ptrofs.repr offset))) in PERMISSIONS.
  assert (ACCESS : Mem.range_perm memory b start (start + load_width size) Cur Memtype.Readable).
  { destruct (ptr_permission ptr); cbn [permission_includes] in READ;
      try discriminate; [exact PERMISSIONS |].
    eapply Mem.range_perm_implies; [exact PERMISSIONS | constructor]. }
  destruct (Mem.range_perm_loadbytes _ _ _ _ ACCESS) as [bytes LOAD].
  unfold load_at_offset, load, loadv_unaligned. cbn [Val.offset_ptr]. fold start.
  destruct size; cbn [size_chunk]; cbn [load_width] in LOAD;
    rewrite LOAD; eauto.
Qed.

(** * SSA assignment and architectural register updates *)

Lemma value_holds_assign : forall world dst value memory abstract concrete,
  value_holds (assign_value world dst value) memory abstract concrete =
  value_holds world memory abstract concrete.
Proof. reflexivity. Qed.

Lemma cell_holds_assign : forall world dst value memory region bytes abstract,
  cell_holds (assign_value world dst value) memory region bytes abstract =
  cell_holds world memory region bytes abstract.
Proof. reflexivity. Qed.

Lemma loword_repr64 : forall value,
  Int.repr (Int64.unsigned (Int64.repr value)) = Int.repr value.
Proof.
  intros value. apply Int.eqm_samerepr.
  eapply eqmod_divides; [apply Int64.eqm_sym, Int64.eqm_unsigned_repr |].
  exists 4294967296. reflexivity.
Qed.

Lemma variable_value_assign_same : forall world dst value,
  variable_value (assign_value world dst value) dst = value.
Proof.
  intros. cbn [assign_value variable_value]. destruct (Nat.eq_dec dst dst); congruence.
Qed.

Lemma variable_value_assign_other : forall world dst value x,
  Nat.eqb dst x = false ->
  variable_value (assign_value world dst value) x = variable_value world x.
Proof.
  intros world dst value x DIFFERENT. apply Nat.eqb_neq in DIFFERENT.
  cbn [assign_value variable_value]. destruct (Nat.eq_dec x dst); congruence.
Qed.

Lemma term_value_assign : forall world dst value expression,
  term_mentions dst expression = false ->
  eval_term (assign_value world dst value) expression = eval_term world expression.
Proof.
  intros world dst value expression MENTIONS.
  destruct expression; cbn [term_mentions eval_term] in *; try reflexivity;
    try (now rewrite variable_value_assign_other by exact MENTIONS).
  apply orb_false_iff in MENTIONS as [LEFT RIGHT].
  now rewrite !variable_value_assign_other by assumption.
Qed.

Lemma atom_holds_assign : forall world memory dst value fact,
  atom_mentions dst fact = false -> atom_holds world memory fact ->
  atom_holds (assign_value world dst value) memory fact.
Proof.
  intros world memory dst value fact MENTIONS HOLDS.
  destruct fact; cbn [atom_mentions atom_holds] in *; try exact HOLDS.
  - cbn [region_address assign_value region_location].
    rewrite variable_value_assign_other by exact MENTIONS. exact HOLDS.
  - cbn [assign_value ghost_value].
    now rewrite term_value_assign by exact MENTIONS.
  - rewrite term_value_assign by exact MENTIONS. now rewrite value_holds_assign.
  - repeat rewrite orb_false_iff in MENTIONS.
    destruct MENTIONS as [[DEST LEFT] RIGHT].
    rewrite variable_value_assign_other by exact DEST.
    now rewrite !term_value_assign by assumption.
  - apply orb_false_iff in MENTIONS as [LEFT RIGHT].
    now rewrite !term_value_assign by assumption.
  - now rewrite !term_value_assign by exact MENTIONS.
  - apply orb_false_iff in MENTIONS as [LEFT RIGHT].
    now rewrite !term_value_assign by assumption.
  - apply orb_false_iff in MENTIONS as [LEFT RIGHT].
    now rewrite !term_value_assign by assumption.
  - apply orb_false_iff in MENTIONS as [LEFT RIGHT].
    now rewrite !term_value_assign by assumption.
  - apply orb_false_iff in MENTIONS as [POINTER INDEX].
    cbn [assign_value region_location].
    now rewrite !variable_value_assign_other by assumption.
  - apply orb_false_iff in MENTIONS as [GUARD TERM].
    rewrite variable_value_assign_other by exact GUARD.
    rewrite term_value_assign by exact TERM. now rewrite value_holds_assign.
  - rewrite variable_value_assign_other by exact MENTIONS. exact HOLDS.
Qed.

(** Havoc records initialization, independently of an instruction's bounds. *)
Lemma apply_havoc_holds : forall world memory state dst value,
  Forall (atom_holds world memory) state ->
  runtime_value value ->
  Forall (atom_holds (assign_value world dst value) memory) (apply_havoc state dst).
Proof.
  intros world memory state dst value FACTS INITIALIZED.
  unfold apply_havoc. apply Forall_app. split.
  - apply Forall_forall. intros fact IN.
    apply filter_In in IN as [IN KEEP]. apply negb_true_iff in KEEP.
    eapply atom_holds_assign; [exact KEEP |].
    now apply Forall_forall with (x := fact) in FACTS.
  - constructor; [| constructor]. cbn [atom_holds eval_term value_holds].
    assert (ASSIGNED : variable_value (assign_value world dst value) dst = value).
    { cbn [assign_value variable_value]. destruct (Nat.eq_dec dst dst); congruence. }
    rewrite ASSIGNED. exact INITIALIZED.
Qed.

Lemma nextinstr_set_value : forall regs (dst : ireg) value,
  (nextinstr (Pregmap.set dst value regs)) dst = value.
Proof.
  intros. unfold nextinstr. rewrite Pregmap.gso by discriminate. apply Pregmap.gss.
Qed.

Lemma find_pointer_fact_present : forall state base ptr,
  find_pointer_fact state base = Some ptr ->
  In (AbstractValue (Var base) (Ptr ptr)) state.
Proof.
  intros state base ptr. unfold find_pointer_fact.
  remember (fun found fact =>
    match found, fact with
    | Some ptr, _ => Some ptr
    | None, AbstractValue (Var x) (Ptr ptr) => if Nat.eqb x base then Some ptr else None
    | None, _ => None
    end) as select eqn:SELECT.
  assert (FOUND : forall state acc,
    fold_left select state acc = Some ptr ->
    acc = Some ptr \/ In (AbstractValue (Var base) (Ptr ptr)) state).
  { intro items. induction items as [| fact rest IH]; intros acc H; cbn in H.
    - now left.
    - apply IH in H as [H | H]; [| right; now right].
      rewrite SELECT in H. destruct acc as [old |]; [now left |].
      destruct fact; try discriminate H.
      match goal with t : AbstractDomain.term |- _ => destruct t end; try discriminate H.
      match goal with v : value_state |- _ => destruct v end; try discriminate H.
      destruct (Nat.eqb x base) eqn:NAME; try discriminate H.
      apply Nat.eqb_eq in NAME. inversion H; subst. right; now left. }
  intros H. apply FOUND in H as [H | H]; [discriminate | exact H].
Qed.


Lemma concretizes_register_update :
  forall (attrs : load_attrs) regions before post world memory (regs : regset) stack code_id count
         (dst : ireg) dst_value value,
    fresh_destination before dst dst_value ->
    (forall reg, reg <> RAX -> variable_value world (register_name before reg) = regs reg) ->
    store_policy_holds world memory attrs ->
    cell_blocks_exclusive world ->
    environment_holds world memory attrs regions ->
    Forall (atom_holds (assign_value world dst_value value) memory) post ->
    concretizes attrs regions
      (AbstractMachineState post (set_register_name (register_name before) dst dst_value))
      (TLS_State (nextinstr (Pregmap.set dst value regs)) stack code_id count memory).
Proof.
  intros attrs regions before post world memory regs stack code_id count dst dst_value value
    FRESH REGISTERS POLICY LAYOUT ENVIRONMENT POST.
  exists (assign_value world dst_value value).
  split; [| split; [exact POST | split; [exact POLICY | split; [exact LAYOUT | exact ENVIRONMENT]]]].
  intros reg NOT_AUX. cbn [register_name]. unfold set_register_name.
  destruct (ireg_eq reg dst) as [SAME | OTHER].
  - subst reg. rewrite nextinstr_set_value. cbn [assign_value variable_value].
    destruct (Nat.eq_dec dst_value dst_value); congruence.
  - rewrite variable_value_assign_other.
    + rewrite REGISTERS by exact NOT_AUX. unfold nextinstr.
      rewrite Pregmap.gso by discriminate. rewrite Pregmap.gso by congruence. reflexivity.
    + apply Nat.eqb_neq. intro SAME. apply (FRESH reg OTHER). congruence.
Qed.

(** ** Writes *)

(** The byte interval whose stored contents a memory fact describes.
    [Readable] concerns initialization only; ordinary integer writes preserve
    it even when they overlap. [ReadableCell] additionally reads its slot. *)
Definition memory_footprint (fact : atom) : option (Region.t * range) :=
  match fact with
  | MemoryCell region bytes _ => Some (region, bytes)
  | MemoryEq region offset _ | ReadableCell region offset _ =>
      Some (region, Range offset (offset + 8))
  | _ => None
  end.

(** Byte-level separation of a write: every pre-state footprint the abstract
    transfer regards as untouched lies in other concrete bytes.
    [checked_write_separated] derives it from concretization. *)
Definition store_footprints_separated (world : interpretation) (state : abstract_state)
    (target : option Region.t) (window : range) (block : block)
    (start count : Z) : Prop :=
  forall fact region bytes other address,
    In fact state -> memory_footprint fact = Some (region, bytes) ->
    (target <> Some region \/ overlaps bytes window = false) ->
    region_address world region (lower bytes) = Vptr other address ->
    upper bytes <= lower bytes \/
    other <> block \/ Ptrofs.unsigned address + (upper bytes - lower bytes) <= start \/
      start + count <= Ptrofs.unsigned address.

Lemma atom_holds_storebytes_separated :
  forall world memory memory' b start bytes fact,
    Mem.storebytes memory b start bytes = Some memory' ->
    Forall initialized_byte bytes ->
    (forall region window other address,
      memory_footprint fact = Some (region, window) ->
      region_address world region (lower window) = Vptr other address ->
      upper window <= lower window \/
      other <> b \/ Ptrofs.unsigned address + (upper window - lower window) <= start \/
        start + Z.of_nat (length bytes) <= Ptrofs.unsigned address) ->
    atom_holds world memory fact -> atom_holds world memory' fact.
Proof.
  intros world memory memory' b start bytes fact STORE INIT SEPARATE HOLDS.
  destruct fact; try (eapply atom_holds_storebytes_without_cell; eauto; exact I).
  - eapply cell_holds_storebytes_disjoint; eauto.
    intros. eapply SEPARATE; [reflexivity | assumption].
  - cbn [atom_holds] in *.
    unfold region_address in HOLDS |- *.
    destruct (region_location world region) as [[other origin]|] eqn:LOCATION;
      [| contradiction].
    eapply memory_eq_storebytes_disjoint; eauto.
    specialize (SEPARATE region (Range offset (offset + 8)) other
      (Ptrofs.repr (origin + offset)) eq_refl).
    cbn [lower upper] in SEPARATE. replace (offset + 8 - offset) with 8 in SEPARATE by lia.
    destruct SEPARATE as [EMPTY | SEPARATE];
      [unfold region_address; now rewrite LOCATION | lia | exact SEPARATE].
  - cbn [atom_holds stack_cell_points_to_window] in *.
    destruct HOLDS as [STACK [loaded [LOAD WINDOW]]].
    split; [exact STACK |]. exists loaded. split.
    + unfold region_address in LOAD |- *.
      destruct (region_location world region) as [[other origin]|] eqn:LOCATION;
        [| discriminate].
      rewrite load_storebytes_disjoint with (memory := memory) (b := b)
        (start := start) (bytes := bytes);
        [exact LOAD | exact STORE |].
      specialize (SEPARATE region (Range offset (offset + 8)) other
        (Ptrofs.repr (origin + offset)) eq_refl).
      cbn [lower upper load_width] in *.
      replace (offset + 8 - offset) with 8 in SEPARATE by lia.
      destruct SEPARATE as [EMPTY | SEPARATE];
        [unfold region_address; now rewrite LOCATION | lia | exact SEPARATE].
    + eapply initialized_window_storebytes; eauto.
Qed.

(** Shared preservation after write invalidation. Instruction-specific
    proofs supply the new cells and the origin of every other local fact. *)
Lemma materialized_write_holds :
  forall world memory memory' state post base offset width policy access b address bytes,
    Forall (atom_holds world memory) state ->
    checked_write_access_range state base offset width policy = Some access ->
    Mem.storebytes memory b (Ptrofs.unsigned address) bytes = Some memory' ->
    Forall initialized_byte bytes -> Z.of_nat (length bytes) = width ->
    store_footprints_separated world state (Region.cells (ptr_ty (access_ptr access)))
      (access_range access) b (Ptrofs.unsigned address) width ->
    (forall region window abstract, In (MemoryCell region window abstract) post ->
      cell_holds world memory' region window abstract) ->
    (forall fact, (match fact with MemoryCell _ _ _ => False | _ => True end) ->
      In fact post -> In fact state) ->
    Forall (atom_holds world memory')
      (SpillProvenance.materialize
        (fst (SpillProvenance.invalidate_write (SpillProvenance.from_entry state)
          state base offset width)) post).
Proof.
  intros world memory memory' state post base offset width policy access b address bytes
    FACTS CHECK STORE INIT LENGTH SEPARATE CELLS OTHER.
  apply Forall_forall. intros fact IN.
  destruct (materialized_store_origin _ _ _ _ _ _ _ _ CHECK IN)
    as [[LOCAL KEPT] | [region [start [name [EQ [OLD UNTOUCHED]]]]]].
  - assert (SOURCE : (match fact with MemoryCell _ _ _ => False | _ => True end) ->
      In fact state) by (intro NONCELL; eapply OTHER; eauto).
    destruct fact; try contradiction.
    all: try solve [apply CELLS; exact LOCAL].
    all: try solve [eapply atom_holds_storebytes_separated;
      [exact STORE | exact INIT | | exact ((proj1 (Forall_forall _ _) FACTS) _ (SOURCE I))];
      intros region window other addr FOOT LOCATION; discriminate FOOT].
    eapply atom_holds_storebytes_separated; [exact STORE | exact INIT | |].
    + intros region0 window other addr FOOT LOCATION. cbn [memory_footprint] in FOOT.
      inversion FOOT; subst region0 window. rewrite LENGTH.
      eapply SEPARATE; [apply SOURCE; exact I | reflexivity | exact KEPT | exact LOCATION].
    + exact ((proj1 (Forall_forall _ _) FACTS) _ (SOURCE I)).
  - subst fact. eapply atom_holds_storebytes_separated;
      [exact STORE | exact INIT | | exact ((proj1 (Forall_forall _ _) FACTS) _ OLD)].
    intros region0 window other addr FOOT LOCATION. cbn [memory_footprint] in FOOT.
    inversion FOOT; subst region0 window. rewrite LENGTH.
    eapply SEPARATE; [exact OLD | reflexivity | exact UNTOUCHED | exact LOCATION].
Qed.


(** Two disjoint nonempty intervals of [i64] offsets denote disjoint bytes
    after adding a common origin modulo [2^64], provided the second does not
    wrap: the [i64] span is exactly [2^64] wide. *)
Lemma modular_intervals_disjoint : forall origin l1 u1 l2 u2,
  Int64.min_signed <= l1 -> u1 <= Int64.max_signed ->
  Int64.min_signed <= l2 -> u2 <= Int64.max_signed ->
  (u1 <= l2 \/ u2 <= l1) ->
  Ptrofs.unsigned (Ptrofs.repr (origin + l1)) + (u1 - l1) <=
    Ptrofs.unsigned (Ptrofs.repr (origin + l2)) \/
  Ptrofs.unsigned (Ptrofs.repr (origin + l2)) + (u2 - l2) <=
    Ptrofs.unsigned (Ptrofs.repr (origin + l1)).
Proof.
  intros origin l1 u1 l2 u2 L1 U1 L2 U2 DISJOINT.
  rewrite !Ptrofs.unsigned_repr_eq in *.
  change Ptrofs.modulus with 18446744073709551616 in *.
  change Int64.min_signed with (-9223372036854775808) in *.
  change Int64.max_signed with 9223372036854775807 in *.
  pose proof (Z.div_mod (origin + l1) 18446744073709551616 ltac:(lia)) as D1.
  pose proof (Z.div_mod (origin + l2) 18446744073709551616 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (origin + l1) 18446744073709551616 ltac:(lia)) as M1.
  pose proof (Z.mod_pos_bound (origin + l2) 18446744073709551616 ltac:(lia)) as M2.
  set (k1 := (origin + l1) / 18446744073709551616) in *.
  set (k2 := (origin + l2) / 18446744073709551616) in *.
  set (s1 := (origin + l1) mod 18446744073709551616) in *.
  set (s2 := (origin + l2) mod 18446744073709551616) in *.
  destruct (Z.lt_total k1 k2) as [LT | [EQ | GT]]; [| subst k2 |]; lia.
Qed.

Lemma ptrofs_repr_add : forall x y,
  Ptrofs.add (Ptrofs.repr x) (Ptrofs.repr y) = Ptrofs.repr (x + y).
Proof.
  intros. unfold Ptrofs.add. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

Lemma memory_footprint_valid : forall fact region bytes,
  memory_coordinates_valid fact ->
  memory_footprint fact = Some (region, bytes) ->
  Region.cells region = Some region /\
  Int64.min_signed <= lower bytes /\ upper bytes <= Int64.max_signed.
Proof.
  intros fact region bytes VALID FOOTPRINT.
  destruct fact; cbn [memory_footprint] in FOOTPRINT; inversion FOOTPRINT; subst;
    unfold memory_coordinates_valid, memory_range_valid, i64_coordinate in VALID;
    cbn [lower upper]; intuition lia.
Qed.

Lemma checked_i64_bounds : forall x y sum,
  i64_checked_add x y = Some sum ->
  sum = x + y /\ Int64.min_signed <= sum <= Int64.max_signed.
Proof.
  intros x y sum ADD. unfold i64_checked_add in ADD.
  destruct ((_ <=? x + y) && (x + y <=? _)) eqn:BOUNDS; [| discriminate].
  injection ADD as <-. apply andb_true_iff in BOUNDS as [LOW HIGH].
  apply Z.leb_le in LOW, HIGH.
  change Int64.min_signed with (-9223372036854775808).
  change Int64.max_signed with 9223372036854775807. lia.
Qed.

Lemma checked_write_access_bounds : forall ptr offset width strict access,
  checked_write_access_for_ptr ptr offset width strict = Some access ->
  Int64.min_signed <= ptr_off_min ptr + offset /\
  ptr_off_max ptr + offset + width <= Int64.max_signed.
Proof.
  intros ptr offset width strict access CHECK. unfold checked_write_access_for_ptr in CHECK.
  destruct (permission_includes _ _); [| discriminate].
  destruct (ptr_nullability ptr); try discriminate.
  destruct (i64_checked_add (ptr_off_min ptr) offset) as [start |] eqn:START; [| discriminate].
  destruct (i64_checked_add (ptr_off_max ptr) offset) as [last |] eqn:LAST; [| discriminate].
  destruct (i64_checked_add last width) as [finish |] eqn:FINISH; [| discriminate].
  apply checked_i64_bounds in START, LAST, FINISH. lia.
Qed.

(** A checked write reads its pointer's offsets and its bounds from [i64]
    arithmetic; a policy grant only changes its permission. *)
Lemma checked_write_access_range_shape : forall state base ptr offset width policy access,
  find_pointer_fact state base = Some ptr ->
  checked_write_access_range state base offset width policy = Some access ->
  ptr_ty (access_ptr access) = ptr_ty ptr /\
  access_range access =
    Range (ptr_off_min ptr + offset) (ptr_off_max ptr + offset + width) /\
  Int64.min_signed <= ptr_off_min ptr + offset /\
  ptr_off_max ptr + offset + width <= Int64.max_signed.
Proof.
  intros state base ptr offset width policy access FIND CHECK.
  unfold checked_write_access_range in CHECK. rewrite FIND in CHECK.
  apply filter_special_access_some in CHECK.
  apply filter_context_access_some in CHECK.
  set (local := if _ || _ then with_write_permission ptr else ptr) in CHECK.
  assert (SAME : ptr_ty local = ptr_ty ptr /\ ptr_off_min local = ptr_off_min ptr /\
    ptr_off_max local = ptr_off_max ptr) by (unfold local; destruct (_ || _); auto).
  destruct SAME as [TY [MIN MAX]].
  destruct (checked_write_access_bounds _ _ _ _ _ CHECK) as [LOW HIGH].
  rewrite (checked_write_access_shape _ _ _ _ _ CHECK). cbn [access_ptr access_range].
  rewrite TY, MIN, MAX in *. auto.
Qed.

(** A checked non-context write goes through an offset of one of its region's
    objects. *)
Lemma checked_write_pointer_object :
  forall world memory state base ptr attrs offset width access b address,
    Region.is (ptr_ty ptr) RegionClass.CTX = false ->
    store_policy_holds world memory attrs ->
    find_pointer_fact state base = Some ptr ->
    pointer_state_holds world memory ptr (Vptr b address) ->
    checked_write_access_range state base offset width attrs = Some access ->
    exists origin actual,
      region_object world (ptr_ty ptr) b origin /\
      ptr_off_min ptr <= actual <= ptr_off_max ptr /\
      address = Ptrofs.repr (origin + actual).
Proof.
  intros world memory state base ptr attrs offset width access b address
    NONCTX POLICY FIND [_ [REGION _]] CHECK.
  unfold checked_write_access_range in CHECK. rewrite FIND in CHECK.
  destruct (Region.is (ptr_ty ptr) RegionClass.CTX ||
    (negb (permission_includes (ptr_permission ptr) Write) &&
     write_window_grants attrs ptr offset width)) eqn:GRANT;
    apply filter_special_access_some in CHECK;
    apply filter_context_access_some in CHECK;
    destruct (checked_write_window _ _ _ _ _ CHECK) as [WRITE [NONNULL _]];
    change (ptr_nullability ptr = NonNull) in NONNULL;
    unfold pointer_region_holds in REGION; rewrite NONNULL in REGION.
  - rewrite NONCTX in GRANT. cbn in GRANT. apply andb_true_iff in GRANT as [_ GRANT].
    unfold write_window_grants in GRANT.
    destruct (i64_checked_add (ptr_off_min ptr) offset); try discriminate.
    destruct (i64_checked_add (ptr_off_max ptr) offset) as [last |]; try discriminate.
    destruct (i64_checked_add last width); try discriminate.
    pose proof (write_window_allows_ordinary _ _ _ _ _ POLICY GRANT) as ORDINARY.
    destruct (Region.eqb (ptr_ty ptr) (Region.btf None)) eqn:UNTYPED.
    { apply Region.eqb_eq in UNTYPED. rewrite UNTYPED in ORDINARY. discriminate. }
    destruct (pointer_object _ _ _ _ REGION)
      as [origin [actual [OBJECT [[[MIN MAX] _] ADDRESS]]]].
    exists origin, actual. auto.
  - destruct (Region.eqb (ptr_ty ptr) (Region.btf None)) eqn:UNTYPED.
    { change (permission_includes (ptr_permission ptr) Write = true) in WRITE.
      congruence. }
    destruct (pointer_object _ _ _ _ REGION)
      as [origin [actual [OBJECT [[[MIN MAX] _] ADDRESS]]]].
    exists origin, actual. auto.
Qed.

(** The separation premise of [materialized_write_holds] for every checked
    non-context write: a footprint in the written region lies at other
    [i64] offsets, and one elsewhere lies in another block by
    [cell_blocks_exclusive]. *)
Lemma checked_write_separated :
  forall world memory state base ptr attrs offset width access b address,
    Forall memory_coordinates_valid state ->
    cell_blocks_exclusive world ->
    store_policy_holds world memory attrs ->
    Region.is (ptr_ty ptr) RegionClass.CTX = false ->
    find_pointer_fact state base = Some ptr ->
    pointer_state_holds world memory ptr (Vptr b address) ->
    checked_write_access_range state base offset width attrs = Some access ->
    Ptrofs.unsigned (Ptrofs.add address (Ptrofs.repr offset)) + width <= Ptrofs.modulus ->
    store_footprints_separated world state (Region.cells (ptr_ty (access_ptr access)))
      (access_range access) b (Ptrofs.unsigned (Ptrofs.add address (Ptrofs.repr offset))) width.
Proof.
  intros world memory state base ptr attrs offset width access b address
    VALID LAYOUT POLICY NONCTX FIND POINTER CHECK NOWRAP.
  destruct (checked_write_pointer_object _ _ _ _ _ _ _ _ _ _ _ NONCTX POLICY FIND POINTER CHECK)
    as [origin [actual [OBJECT [[MIN MAX] ADDRESS]]]].
  destruct (checked_write_access_range_shape _ _ _ _ _ _ _ FIND CHECK)
    as [TYPE [RANGE [LOW HIGH]]].
  rewrite TYPE, RANGE. subst address.
  rewrite ptrofs_repr_add in NOWRAP |- *.
  intros fact region bytes other position IN FOOTPRINT UNTOUCHED REGION_ADDRESS.
  destruct (memory_footprint_valid _ _ _ ((proj1 (Forall_forall _ _) VALID) _ IN) FOOTPRINT)
    as [CELLS [FLOW FHIGH]].
  unfold region_address in REGION_ADDRESS.
  destruct (region_location world region) as [[block region_origin] |] eqn:LOCATION;
    [| discriminate].
  injection REGION_ADDRESS as <- <-.
  destruct (Z_le_gt_dec (upper bytes) (lower bytes)) as [EMPTY | NONEMPTY]; [now left |].
  right.
  destruct (Region.eqb (ptr_ty ptr) region) eqn:SAME.
  - apply Region.eqb_eq in SAME. subst region.
    destruct UNTOUCHED as [DIFFERENT | DISJOINT]; [rewrite CELLS in DIFFERENT; congruence |].
    unfold region_object in OBJECT. rewrite CELLS, LOCATION in OBJECT.
    injection OBJECT as BLOCK ORIGIN. subst block region_origin. right.
    unfold overlaps in DISJOINT. cbn [lower upper] in DISJOINT.
    apply andb_false_iff in DISJOINT as [LEFT | RIGHT];
      [apply Z.ltb_ge in LEFT | apply Z.ltb_ge in RIGHT].
    all: replace (origin + actual + offset) with (origin + (actual + offset)) in NOWRAP |- * by lia;
      replace (actual + offset + width - (actual + offset)) with width in * by lia;
      pose proof (modular_intervals_disjoint origin (lower bytes) (upper bytes)
        (actual + offset) (actual + offset + width) FLOW FHIGH ltac:(lia) ltac:(lia)
        ltac:(lia)) as SEPARATE;
      replace (actual + offset + width - (actual + offset)) with width in SEPARATE by lia;
      destruct SEPARATE; [left | right]; lia.
  - left. intros BLOCK. subst block.
    destruct (LAYOUT region b region_origin CELLS LOCATION) as [LOCATIONS ALLOCATIONS].
    unfold region_object in OBJECT.
    destruct (Region.cells (ptr_ty ptr)) eqn:OWN.
    + refine (LOCATIONS (ptr_ty ptr) b origin _ OBJECT eq_refl).
      intros EQUAL. rewrite EQUAL, region_eqb_refl in SAME. discriminate.
    + exact (ALLOCATIONS (ptr_ty ptr) b origin OBJECT eq_refl).
Qed.

Lemma block_initialized_storebytes : forall memory memory' b start bytes block,
  Mem.storebytes memory b start bytes = Some memory' ->
  Forall initialized_byte bytes ->
  block_initialized memory block -> block_initialized memory' block.
Proof.
  intros memory memory' b start bytes block STORE WRITTEN INITIALIZED position PERM.
  apply (Mem.perm_storebytes_2 _ _ _ _ _ STORE) in PERM.
  rewrite (Mem.storebytes_mem_contents _ _ _ _ _ STORE), PMap.gsspec.
  destruct (peq block b) as [SAME | OTHER]; [subst block | now apply INITIALIZED].
  destruct (Z_le_dec start position), (Z_lt_dec position (start + Z.of_nat (length bytes))).
  - apply Forall_forall with (x := ZMap.get position
      (Mem.setN bytes start (PMap.get b (Mem.mem_contents memory)))) in WRITTEN;
      [exact WRITTEN | apply Mem.setN_in; lia].
  - rewrite Mem.setN_outside by lia. now apply INITIALIZED.
  - rewrite Mem.setN_outside by lia. now apply INITIALIZED.
  - rewrite Mem.setN_outside by lia. now apply INITIALIZED.
Qed.

(** A store keeps every permission and writes defined bytes, so the memory
    environment survives it. *)
Lemma environment_holds_storebytes :
  forall world memory memory' (attrs : load_attrs) regions b start bytes,
    Mem.storebytes memory b start bytes = Some memory' ->
    Forall initialized_byte bytes ->
    environment_holds world memory attrs regions ->
    environment_holds world memory' attrs regions.
Proof.
  intros world memory memory' attrs regions b start bytes STORE WRITTEN
    [[MAPS [LOCATIONS ALLOCATIONS]] LOADER].
  split; [| exact LOADER]. split; [| split].
  - intros id spec SPEC. destruct (MAPS id spec SPEC) as [SIZE BACKED].
    split; [exact SIZE |]. intros block origin ALLOCATED.
    destruct (BACKED block origin ALLOCATED) as [ORIGIN [END PERM]].
    split; [exact ORIGIN |]. split; [exact END |].
    intros position INSIDE. eapply Mem.perm_storebytes_1; eauto.
  - intros region block origin STACK LOCATION.
    eapply block_initialized_storebytes; eauto.
  - intros region block origin STACK ALLOCATED.
    eapply block_initialized_storebytes; eauto.
Qed.

Lemma lowered_store_not_context : forall size base source offset kind executable region,
  lowers_store size base source offset kind executable ->
  Region.kernel_access region = kind -> Region.is region RegionClass.CTX = false.
Proof.
  intros size base source offset kind executable region LOWER KIND.
  destruct (Region.is region RegionClass.CTX) eqn:CTX; [| reflexivity].
  rewrite (context_kernel_access _ CTX) in KIND. subst kind.
  inversion LOWER as [kind' KINDS]. destruct KINDS; discriminate.
Qed.

Lemma lowers_store_base : forall size base source offset kind executable,
  lowers_store size base source offset kind executable -> base <> RAX.
Proof. intros size base source offset kind executable LOWER. now destruct LOWER. Qed.

Lemma lowers_store_source : forall size base source offset kind executable,
  lowers_store size base source offset kind executable -> program_operand source.
Proof. intros size base source offset kind executable LOWER. now destruct LOWER. Qed.

Lemma lowers_store_instruction : forall size base source offset kind executable,
  lowers_store size base source offset kind executable ->
  executable = Pstore size base source (Ptrofs.repr offset).
Proof. intros size base source offset kind executable LOWER. now destruct LOWER. Qed.

Lemma materialize_holds : forall world memory provenance state,
  Forall (atom_holds world memory) state ->
  (forall item, In item (SpillProvenance.entries provenance) ->
    atom_holds world memory (MemoryEq (SpillProvenance.binding_region item)
      (lower (SpillProvenance.binding_range item)) (SpillProvenance.binding_value item))) ->
  Forall (atom_holds world memory) (SpillProvenance.materialize provenance state).
Proof.
  intros world memory provenance state STATE ENTRIES.
  unfold SpillProvenance.materialize. rewrite Forall_forall in *.
  intros fact IN. apply in_app_or in IN as [IN | IN].
  - apply filter_In in IN as [IN _]. exact (STATE fact IN).
  - apply in_map_iff in IN as [item [<- IN]]. exact (ENTRIES item IN).
Qed.

(** * Meets *)

(** Both facts hold, so their meet does: a range meet is the intersection, and
    every other meet keeps one of the two. *)
Lemma meet_holds : forall entails world memory a b value met,
  value_holds world memory a value -> value_holds world memory b value ->
  meet entails a b = Some met -> value_holds world memory met value.
Proof.
  intros entails world memory a b value met LEFT RIGHT MEET.
  destruct a, b; cbn [meet] in MEET;
    repeat match type of MEET with context [if ?test then _ else _] => destruct test end;
    try (injection MEET as <-; assumption); try discriminate MEET.
  - injection MEET as <-. cbn [value_holds u_lower u_upper] in *.
    destruct value; try contradiction. lia.
  - injection MEET as <-. cbn [value_holds lower upper] in *.
    destruct value; try contradiction. lia.
Qed.

Lemma fold_kind_holds : forall entails world memory states value kind found,
  Forall (fun state => value_holds world memory state value) states ->
  fold_kind entails states kind = Some found -> value_holds world memory found value.
Proof.
  intros entails world memory states value kind found STATES FOLD.
  unfold fold_kind in FOLD.
  revert found FOLD. apply fold_left_preserves with
    (item_holds := fun state => value_holds world memory state value); [exact STATES | discriminate |].
  intros state held HOLDS HELD found.
  destruct (Nat.eqb (state_kind state) kind); [| exact (HELD found)].
  intros AFTER. injection AFTER as <-.
  destruct held as [previous |]; [| exact HOLDS].
  destruct (meet entails previous state) as [met |] eqn:MEET; [| exact HOLDS].
  exact (meet_holds _ _ _ _ _ _ _ (HELD _ eq_refl) HOLDS MEET).
Qed.

(** Rust [meet::fold] keeps only facts that hold of the value. *)
Lemma fold_holds : forall entails world memory states value,
  Forall (fun state => value_holds world memory state value) states ->
  Forall (fun state => value_holds world memory state value) (fold entails states).
Proof.
  intros entails world memory states value STATES. unfold fold.
  apply Forall_forall. intros found IN. apply in_flat_map in IN as [kind [_ IN]].
  destruct (fold_kind entails states kind) as [folded |] eqn:FOLD; [| contradiction].
  destruct IN as [<- | []]. exact (fold_kind_holds _ _ _ _ _ _ _ STATES FOLD).
Qed.

(** * Pointer-leak rules *)

Lemma disclosable_sound : forall world memory state name,
  Forall (atom_holds world memory) state -> disclosable state name = true ->
  exists n, variable_value world name = Vlong n.
Proof.
  intros world memory state name FACTS DISCLOSABLE. unfold disclosable in DISCLOSABLE.
  apply existsb_exists in DISCLOSABLE as [fact [IN CHECK]].
  pose proof ((proj1 (Forall_forall _ _) FACTS) _ IN) as HOLDS.
  destruct fact; try discriminate. destruct term; try discriminate.
  apply andb_true_iff in CHECK as [NAME DISCLOSED]. apply Nat.eqb_eq in NAME. subst x.
  cbn [atom_holds eval_term] in HOLDS.
  destruct value; cbn [state_disclosable] in DISCLOSED; try discriminate;
    cbn [value_holds] in HOLDS; [exact HOLDS | |];
    destruct (variable_value world name); try contradiction; eauto.
Qed.

Lemma mark_scalar_holds : forall world memory state name,
  Forall (atom_holds world memory) state ->
  (find_pointer_fact state name = None -> exists n, variable_value world name = Vlong n) ->
  Forall (atom_holds world memory) (mark_scalar state name).
Proof.
  intros world memory state name FACTS INTEGER. unfold mark_scalar.
  destruct (find_pointer_fact state name) eqn:FIND; [exact FACTS |].
  destruct (existsb _ state); [exact FACTS |].
  apply Forall_app. split; [exact FACTS |]. constructor; [| constructor].
  cbn [atom_holds eval_term value_holds]. exact (INTEGER eq_refl).
Qed.

(** Marking a register's value [Scalar] keeps a concrete state whose register
    holds a defined non-pointer. *)
Lemma concretizes_mark_scalar :
  forall attrs regions state names regs stack code_id count memory reg name,
    concretizes attrs regions (AbstractMachineState state names)
      (TLS_State regs stack code_id count memory) ->
    names reg = name -> reg <> RAX -> has_initialized_value state name = true ->
    (forall b o, regs reg <> Vptr b o) ->
    concretizes attrs regions (AbstractMachineState (mark_scalar state name) names)
      (TLS_State regs stack code_id count memory).
Proof.
  intros attrs regions state names regs stack code_id count memory reg name
    [world [REGISTERS [FACTS REST]]] NAME REG INIT NOT_POINTER.
  cbn [facts register_name] in REGISTERS, FACTS.
  exists world. split; [exact REGISTERS |]. split; [| exact REST]. cbn [facts].
  apply mark_scalar_holds; [exact FACTS |]. intros _.
  pose proof (has_initialized_value_sound _ _ _ _ FACTS INIT) as RUNTIME.
  rewrite <- NAME, (REGISTERS reg REG) in RUNTIME |- *.
  destruct RUNTIME as [n | b o]; [eauto | exfalso; exact (NOT_POINTER b o eq_refl)].
Qed.

Lemma has_initialized_value_present : forall state name value,
  In (AbstractValue (Var name) value) state -> value <> Uninit ->
  has_initialized_value state name = true.
Proof.
  intros state name value IN DEFINED. apply existsb_exists.
  exists (AbstractValue (Var name) value). split; [exact IN |].
  destruct value; try contradiction; apply Nat.eqb_refl.
Qed.

(** * Disclosable cells across a store *)

Lemma scalar_cell_subrange : forall world memory region outer inner,
  cell_holds world memory region outer Scalar ->
  lower outer <= lower inner -> upper inner <= upper outer -> lower inner <= upper inner ->
  cell_holds world memory region inner Scalar.
Proof.
  intros world memory region outer inner [ORDER [ADDRESSABLE [INIT FREE]]] LEFT RIGHT INNER.
  cbn [cell_holds cell_value_holds] in *.
  split; [exact INNER |].
  split; [eapply region_bytes_addressable_subrange; eauto |].
  unfold region_bytes_addressable, region_address in *.
  destruct (region_location world region) as [[b origin] |]; [| contradiction].
  split; [eapply initialized_bytes_subrange | eapply pointer_free_bytes_subrange]; eauto.
Qed.

Lemma scalar_cell_storebytes : forall world memory memory' b start bytes region window,
  Mem.storebytes memory b start bytes = Some memory' ->
  Forall initialized_byte bytes -> Forall pointer_free_byte bytes ->
  cell_holds world memory region window Scalar ->
  cell_holds world memory' region window Scalar.
Proof.
  intros world memory memory' b start bytes region window STORE INIT FREE
    [ORDER [ADDRESSABLE [INITIALIZED POINTER_FREE]]].
  cbn [cell_holds cell_value_holds] in *.
  split; [exact ORDER |]. split; [exact ADDRESSABLE |]. split.
  - eapply initialized_bytes_storebytes; eauto.
  - eapply pointer_free_bytes_storebytes; eauto.
Qed.

Lemma load_long_pointer_free : forall size b address memory loaded n,
  load size (Vptr b address) memory = Some loaded ->
  load_value_casting loaded = Vlong n ->
  pointer_free_bytes memory (Vptr b address) (load_width size).
Proof.
  intros size b address memory loaded n LOAD LONG.
  unfold load, loadv_unaligned in LOAD.
  destruct size; cbn [size_chunk load_width] in *;
    destruct (Mem.loadbytes memory b (Ptrofs.unsigned address) _) as [bytes |] eqn:READ;
    try discriminate; injection LOAD as <-;
    exists bytes; split; [exact READ | | exact READ | | exact READ | | exact READ |];
    eapply decode_long_pointer_free; exact LONG.
Qed.

(** A cell Rust may disclose holds no part of a pointer: a [Scalar] cell by
    definition, a constant one because its load is an integer. *)
Lemma disclosable_cell_scalar : forall world memory region bytes value,
  state_disclosable value = true -> Region.probe_readable region = false ->
  cell_holds world memory region bytes value -> cell_holds world memory region bytes Scalar.
Proof.
  intros world memory region bytes value DISCLOSABLE PROBE CELL.
  destruct value; cbn [state_disclosable] in DISCLOSABLE; try discriminate; [exact CELL | |].
  all: destruct CELL as [ORDER [ADDRESSABLE [INIT [size [WIDTH RESULT]]]]];
    cbn [cell_holds cell_value_holds];
    split; [exact ORDER |]; split; [exact ADDRESSABLE |]; split; [exact INIT |];
    unfold region_bytes_addressable in ADDRESSABLE;
    destruct (region_address world region (lower bytes)) as [| | | | | b address] eqn:ADDRESS;
    try contradiction;
    unfold cell_result_holds in RESULT;
    destruct (load size (Vptr b address) memory) as [loaded |] eqn:LOAD;
    [| rewrite PROBE in RESULT; contradiction];
    cbn [value_holds] in RESULT;
    destruct (load_value_casting loaded) eqn:LONG; try contradiction;
    rewrite <- WIDTH; eapply load_long_pointer_free; eauto.
Qed.

Lemma written_scalar_cell : forall world memory memory' region window b address bytes,
  Mem.storebytes memory b (Ptrofs.unsigned address) bytes = Some memory' ->
  Forall initialized_byte bytes -> Forall pointer_free_byte bytes ->
  region_address world region (lower window) = Vptr b address ->
  Z.of_nat (length bytes) = upper window - lower window ->
  Ptrofs.unsigned address + (upper window - lower window) <= Ptrofs.modulus ->
  cell_holds world memory' region window Scalar.
Proof.
  intros world memory memory' region window b address bytes STORE INIT FREE ADDRESS
    LENGTH NOWRAP.
  pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ STORE) as READ.
  rewrite LENGTH in READ.
  cbn [cell_holds cell_value_holds]. split; [lia |].
  split; [unfold region_bytes_addressable; rewrite ADDRESS; exact NOWRAP |].
  rewrite ADDRESS. split; exists bytes; split; assumption.
Qed.

(** Every piece [remove_overlapping_cells] keeps of the target region lies
    outside the overwritten window. *)
Lemma removed_cell_untouched : forall state target window region bytes value,
  In (MemoryCell region bytes value) (remove_overlapping_cells state target window) ->
  region <> target \/ overlaps bytes window = false.
Proof.
  intros state target window region bytes value IN.
  apply in_flat_map in IN as [fact [OLD IN]].
  destruct fact; cbn in IN; try (destruct IN as [EQ | []]; discriminate EQ).
  destruct (Region.eqb region0 target && overlaps bytes0 window) eqn:OVERLAP.
  - apply andb_true_iff in OVERLAP as [REGION _].
    apply Region.eqb_eq in REGION. subst region0. right.
    apply in_app_iff in IN as [IN | IN];
      [destruct (lower bytes0 <? lower window) eqn:PART
      | destruct (upper window <? upper bytes0) eqn:PART]; try contradiction;
      destruct IN as [EQ | []]; inversion EQ; subst;
      unfold overlaps; cbn [lower upper]; apply andb_false_iff;
      [right | left]; apply Z.ltb_ge; lia.
  - destruct IN as [EQ | []]. inversion EQ; subst.
    apply andb_false_iff in OVERLAP as [DIFFERENT | DISJOINT]; [left | now right].
    intros SAME. subst. rewrite region_eqb_refl in DIFFERENT. discriminate.
Qed.

Lemma subcell_store_separated :
  forall world target window inner b address other position,
    Int64.min_signed <= lower inner -> upper inner <= Int64.max_signed ->
    Int64.min_signed <= lower window -> upper window <= Int64.max_signed ->
    overlaps inner window = false ->
    region_address world target (lower window) = Vptr b address ->
    region_address world target (lower inner) = Vptr other position ->
    upper inner <= lower inner \/ other <> b \/
    Ptrofs.unsigned position + (upper inner - lower inner) <= Ptrofs.unsigned address \/
    Ptrofs.unsigned address + (upper window - lower window) <= Ptrofs.unsigned position.
Proof.
  intros world target window inner b address other position
    ILOW IHIGH WLOW WHIGH DISJOINT WINDOW INNER.
  unfold region_address in WINDOW, INNER.
  destruct (region_location world target) as [[block origin] |]; [| discriminate].
  injection WINDOW as <- <-. injection INNER as <- <-.
  right; right.
  unfold overlaps in DISJOINT.
  apply andb_false_iff in DISJOINT as [D | D]; apply Z.ltb_ge in D;
    apply modular_intervals_disjoint; lia.
Qed.

(** The untouched piece of an overwritten cell after an exact store: a [Scalar]
    piece keeps its pointer-free bytes because the store misses them. *)
Lemma remainder_cell_after_store :
  forall world memory memory' state target window outer inner abstract b address bytes,
    Forall (atom_holds world memory) state -> transfer_input_valid state ->
    In (MemoryCell target outer abstract) state ->
    lower outer <= lower inner -> upper inner <= upper outer -> lower inner <= upper inner ->
    overlaps inner window = false ->
    Int64.min_signed <= lower window -> upper window <= Int64.max_signed ->
    region_address world target (lower window) = Vptr b address ->
    Mem.storebytes memory b (Ptrofs.unsigned address) bytes = Some memory' ->
    Forall initialized_byte bytes ->
    Z.of_nat (length bytes) = upper window - lower window ->
    cell_holds world memory' target inner (remainder_value abstract).
Proof.
  intros world memory memory' state target window outer inner abstract b address bytes
    FACTS [NO_UNINIT COORDINATES] IN LEFT RIGHT ORDER DISJOINT WLOW WHIGH WINDOW
    STORE INIT LENGTH.
  destruct abstract; cbn [remainder_value];
    try solve [eapply unknown_subcell_after_store; eauto].
  pose proof ((proj1 (Forall_forall _ _) FACTS) _ IN) as CELL. cbn [atom_holds] in CELL.
  destruct (memory_footprint_valid _ _ _ ((proj1 (Forall_forall _ _) COORDINATES) _ IN)
    eq_refl) as [_ [OLOW OHIGH]].
  eapply cell_holds_storebytes_disjoint; [exact STORE | exact INIT | |
    exact (scalar_cell_subrange _ _ _ _ _ CELL LEFT RIGHT ORDER)].
  intros other position LOCATION. rewrite LENGTH.
  eapply subcell_store_separated; eauto; lia.
Qed.

Lemma checked_write_window_i64 : forall state base offset width policy access,
  checked_write_access_range state base offset width policy = Some access ->
  Int64.min_signed <= lower (access_range access) /\
  upper (access_range access) <= Int64.max_signed.
Proof.
  intros state base offset width policy access CHECK.
  destruct (find_pointer_fact state base) as [ptr |] eqn:FIND.
  - destruct (checked_write_access_range_shape _ _ _ _ _ _ _ FIND CHECK)
      as [_ [RANGE [LOW HIGH]]].
    rewrite RANGE. cbn [lower upper]. lia.
  - unfold checked_write_access_range in CHECK. rewrite FIND in CHECK. discriminate.
Qed.

Lemma mark_scalar_cells : forall state name region bytes value,
  In (MemoryCell region bytes value) (mark_scalar state name) ->
  In (MemoryCell region bytes value) state.
Proof.
  intros state name region bytes value IN. unfold mark_scalar in IN.
  destruct (find_pointer_fact state name); [exact IN |].
  destruct (existsb _ state); [exact IN |].
  apply in_app_or in IN as [IN | [EQ | []]]; [exact IN | discriminate EQ].
Qed.
