From Coq Require Import Bool List ZArith Lia.
From compcert Require Import Coqlib Integers Values Memory.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.
From TrustNoBPF.Semantics Require Import AbstractDomain Concretization Transfer IRLevelAssms Common
  ArithmeticHelpers.

Import ListNotations.
Open Scope Z_scope.

(** =========== Transfer definitions =========== *)

(** Rust [policy/helper.rs::WrittenValue]. *)
Inductive written_value :=
  | WrittenConst (value : Z)
  | WrittenScalar (bounds : urange)
  | WrittenUnknown.

(** Rust [policy/helper.rs::HelperEffect]. *)
Inductive helper_effect :=
  | ReadRegion (region : Region.t) (bytes : range)
  | WriteRegion (region : Region.t) (bytes : range)
  | InitStack (bytes : range)
  | InitMemArg (ptr_arg size_arg : nat)
  | InitMemFromMapValue (ptr_arg map_arg : nat)
  | InvalidateArg (arg : nat)
  | ReleaseToken (arg : nat)
  | WriteThroughArg (arg : nat) (offset width : Z) (value : written_value).

(** The fields of Rust's [policy/spec.rs::SpecView] that shape the post-call
    state; [spec_fresh_tokens] lists the slots of the [SpecBinding::FreshToken]
    entries of [params]. Precondition fields only gate acceptance and are not
    modeled: [check_call_preconditions] only adds rejections.
    TODO(branch-sync [PTR-LEAK]): among those rejections,
    [check_mem_read_constraints] rejects a helper read buffer whose stack bytes
    are not [leaks::cells_disclosable]; transcribing it needs the read-length
    resolution ([read_byte_counts]) and is left out with the other
    preconditions.
    [spec_trusted] is set for a helper or kfunc spec and clear for a proof's
    [FunctionSpec].
    BRANCH RUST CHANGE [VOID-CALL], introduced in commit 2656ae6: Rust's
    [returns_void] leaves a void callee's destination undefined; main havocked
    every destination to [Unknown], which [transfer_non_void_tail_call_r0_unsound]
    shows is unsound for [bpf_tail_call]. Rust's [machine_spec]
    (TEMP FIX FOR FORMALISATION [VOID-CALL], introduced in commit (uncommitted))
    clears [returns_void] on a machine call, arguing that a machine register
    always holds bits; in this model a machine-target [bpf_tail_call] is thus
    the case [transfer_non_void_tail_call_r0_unsound] refutes. *)
Record call_spec := CallSpec {
  spec_post : abstract_state;
  spec_effects : list helper_effect;
  spec_fresh_tokens : list nat;
  spec_has_callback : bool;
  spec_ret_size_arg : option nat;
  spec_changes_pkt_data : bool;
  spec_trusted : bool;
  spec_returns_void : bool;
}.

(** Rust [HELPER_RETURN_VAR = VarId::MAX]. *)
Definition helper_return_var : var := Z.to_nat 4294967295.
Global Opaque helper_return_var.

Definition read_only_effect (effect : helper_effect) : bool :=
  match effect with ReadRegion _ _ => true | _ => false end.

(** Rust [id.rs::SLOT_BASE]: ids from [0xFFFF_FF00] up name a spec parameter
    slot, which [substitute.rs::substitute_atom_with_slots] lowers to the id
    bound at the call site. *)
Definition id_slot_free (id : nat) : bool := Z.of_nat id <? 4294967040.

Definition region_slot_free (region : Region.t) : bool :=
  match Region.key region with
  | RegionKey.Frame id | RegionKey.Map id | RegionKey.Token id | RegionKey.Btf id =>
      id_slot_free id
  | RegionKey.None | RegionKey.Subprog _ => true
  end.

Definition value_slot_free (value : value_state) : bool :=
  match value with
  | Ptr ptr =>
      region_slot_free (ptr_ty ptr) &&
      match ptr_ref_obj ptr with Some token => id_slot_free token | None => true end
  | _ => true
  end.

Definition resource_slot_free (resource : Resource.t) : bool :=
  match resource with
  | Resource.RefcountedKptr region ty => region_slot_free region && id_slot_free ty
  | _ => true
  end.

(** The ids [substitute_atom_with_slots] lowers. *)
Definition atom_slot_free (fact : atom) : bool :=
  match fact with
  | MemoryCell region _ value => region_slot_free region && value_slot_free value
  | Owns token resource => id_slot_free token && resource_slot_free resource
  | AbstractValue _ value | Guarded _ _ value => value_slot_free value
  | MemoryEq region _ _ | ReadableCell region _ _ => region_slot_free region
  | _ => true
  end.

(** The modeled subset of [apply_spec_call]: every effect is a [ReadRegion]
    (a no-op in [apply_helper_effects]), so no memory write, whose
    [written_bytes] are [Scalar] for a trusted spec, and no [ReleaseToken]
    ([ReleaseNotOwned]); no [FreshToken] binding, so [acquire_minted_tokens]
    neither pushes an [Owns] atom nor rejects; no callback, no
    [ret_size_arg], no map-value result for [retype_map_of_maps_result] to
    retype, and no slot-encoded id in the postcondition, so lowering is the
    identity. *)
Definition effect_free_spec (spec : call_spec) : Prop :=
  forallb read_only_effect (spec_effects spec) = true /\
  spec_fresh_tokens spec = [] /\
  spec_has_callback spec = false /\
  spec_ret_size_arg spec = None /\
  (forall ptr, In (AbstractValue (Var helper_return_var) (Ptr ptr)) (spec_post spec) ->
    Region.is (ptr_ty ptr) RegionClass.MAP_VALUE = false) /\
  forallb atom_slot_free (spec_post spec) = true.

(** [substitute.rs::substitute_var]. *)
Fixpoint substitute_var (params values : list var) (name : var) : option var :=
  match params, values with
  | param :: params, value :: values =>
      if Nat.eqb param name then Some value else substitute_var params values name
  | _, _ => None
  end.

Definition substitute_name (params values : list var) (name : var) : var :=
  match substitute_var params values name with Some value => value | None => name end.

(** [substitute.rs::substitute_term]. *)
Definition substitute_term (params values : list var) (expression : term) : term :=
  match expression with
  | Var name => Var (substitute_name params values name)
  | AddConst name offset =>
      match substitute_var params values name with
      | Some value => ArithmeticHelpers.add_const value offset
      | None => expression
      end
  | Sub lhs rhs => Sub (substitute_name params values lhs) (substitute_name params values rhs)
  | Ghost _ | Const _ | GhostAddConst _ _ => expression
  end.

(** [substitute.rs::substitute_atom_with_slots] on atoms without slot-encoded
    ids ([atom_slot_free]), where region lowering is the identity. *)
Definition substitute_atom (params values : list var) (fact : atom) : atom :=
  let name := substitute_name params values in
  let term := substitute_term params values in
  match fact with
  | MemoryCell _ _ _ | Owns _ _ | ReadableCell _ _ _ => fact
  | GhostEq ghost expression => GhostEq ghost (term expression)
  | AbstractValue expression value => AbstractValue (term expression) value
  | Def dst op lhs rhs => Def (name dst) op (term lhs) (term rhs)
  | Eq lhs rhs => Eq (term lhs) (term rhs)
  | NeqZero expression => NeqZero (term expression)
  | Neq lhs rhs => Neq (term lhs) (term rhs)
  | Le lhs rhs signed => Le (term lhs) (term rhs) signed
  | Lt lhs rhs signed => Lt (term lhs) (term rhs) signed
  | MemoryEq region offset value => MemoryEq region offset (name value)
  | LinearInduction pointer index stride base =>
      LinearInduction (name pointer) (name index) stride base
  | Guarded condition expression value =>
      Guarded (Guard (name (guard_var condition)) (guard_op condition)
        (guard_rhs condition) (guard_size condition)) (term expression) value
  | AbstractDomain.Readable base bytes => AbstractDomain.Readable (name base) bytes
  end.

(** [calls.rs::instantiate_helper_invariant]: argument [i] replaces spec
    variable [i]; the call's destination replaces [HELPER_RETURN_VAR]. *)
Definition instantiate_spec_atoms (atoms : abstract_state) (args : list var)
    (dst : option var) : option abstract_state :=
  let indices := seq 0 (length args) in
  if existsb (atom_mentions helper_return_var) atoms then
    match dst with
    | Some dst =>
        Some (List.map (substitute_atom (indices ++ [helper_return_var]) (args ++ [dst])) atoms)
    | None => None
    end
  else Some (List.map (substitute_atom indices args) atoms).

Definition is_packet_value (value : value_state) : bool :=
  match value with Ptr ptr => Region.is_packet_family (ptr_ty ptr) | _ => false end.

(** Rust [GhostId::PACKET_LEN]. *)
Definition packet_len_ghost : ghost := 0%nat.

Definition is_packet_length (expression : term) : bool :=
  match expression with
  | Ghost name | GhostAddConst name _ => Nat.eqb name packet_len_ghost
  | _ => false
  end.

(** [transfer.rs::mentions_packet_length]. *)
Definition mentions_packet_length (fact : atom) : bool :=
  match fact with
  | GhostEq name expression => Nat.eqb name packet_len_ghost || is_packet_length expression
  | AbstractValue expression _ | NeqZero expression => is_packet_length expression
  | Eq lhs rhs | Neq lhs rhs | Le lhs rhs _ | Lt lhs rhs _ | Def _ _ lhs rhs =>
      is_packet_length lhs || is_packet_length rhs
  | Guarded _ expression _ => is_packet_length expression
  | _ => false
  end.

(** [transfer.rs::invalidate_packet_pointers]. *)
Definition invalidate_packet_pointers (state : abstract_state) : abstract_state :=
  let invalidated := flat_map (fun fact =>
    match fact with
    | AbstractValue (Var name) value => if is_packet_value value then [name] else []
    | _ => []
    end) state in
  let kept := filter (fun fact =>
    match fact with
    | AbstractValue _ value =>
        if is_packet_value value then false else negb (mentions_packet_length fact)
    | LinearInduction pointer _ _ _ => negb (existsb (Nat.eqb pointer) invalidated)
    | _ => negb (mentions_packet_length fact)
    end) state in
  List.map (fun fact =>
    match fact with
    | MemoryCell region bytes value =>
        if Region.uninit_by_default region && is_packet_value value
        then MemoryCell region bytes Unknown else fact
    | _ => fact
    end) kept ++
  List.map (fun name => AbstractValue (Var name) Unknown) invalidated.

(** The pre-state facts [apply_spec_call] keeps before defining the
    destination: effects are no-ops in the modeled subset, and a callback may
    itself change packet data. *)
Definition call_kept_facts (spec : call_spec) (state : abstract_state) : abstract_state :=
  if spec_changes_pkt_data spec || spec_has_callback spec
  then invalidate_packet_pointers state else state.

(** [transfer.rs::apply_undef]: no fact remains about [dst], so it is
    undefined. *)
Definition apply_undef (state : abstract_state) (dst : var) : abstract_state :=
  filter (fun fact => negb (atom_mentions dst fact)) state.

(** The last step of [apply_spec_call]: a trusted callee's result without a
    pointer fact is an integer, so [leaks::mark_scalar] records it
    disclosable.
    BRANCH RUST CHANGE [VOID-CALL], introduced in commit (uncommitted): Rust
    skips a void callee (issue #11); main also marked its undefined
    destination [Scalar], which made it readable. *)
Definition mark_call_result (spec : call_spec) (state : abstract_state) (dst : var) :
    abstract_state :=
  if spec_trusted spec && negb (spec_returns_void spec) then mark_scalar state dst else state.

(** [calls.rs::apply_spec_call] after its precondition checks, on the
    subset [effect_free_spec], where [acquire_minted_tokens] is a no-op. A
    void callee leaves its destination undefined; any other callee's is
    havocked, and a trusted one's marked by [mark_call_result]. *)
Definition transfer_spec_call (spec : call_spec) (state : abstract_state)
    (args : list var) (dst : var) : option abstract_state :=
  let kept := call_kept_facts spec state in
  option_map (fun post =>
      mark_call_result spec
        ((if spec_returns_void spec then apply_undef kept dst else apply_havoc kept dst) ++ post)
        dst)
    (instantiate_spec_atoms (spec_post spec) args (Some dst)).

(** [decode_jmp] passes [R1]-[R5] as arguments and defines [R0]. *)
Definition call_args (names : ireg -> var) : list var :=
  [names R1; names R2; names R3; names R4; names R5].

(** [ssa.rs]: [R0] receives the call's destination and each of [R1]-[R5]
    is rebound to a fresh name defined by [Instruction::Undef], whose
    transfer adds no fact. *)
Definition call_register_names (names : ireg -> var) (dst : var)
    (clobbered : ireg -> var) : ireg -> var :=
  fun reg =>
    match reg with
    | R0 => dst
    | R1 | R2 | R3 | R4 | R5 => clobbered reg
    | _ => names reg
    end.

(** [transfer.rs::transfer_instruction] before every call: a callee may
    invalidate what a guarded fact claims, so none survives, and a packet
    pointer's verified end is forgotten. *)
Definition forget_packet_end (value : value_state) : value_state :=
  match value with
  | Ptr ptr =>
      if Region.is_bounded_by_cmp (ptr_ty ptr)
      then Ptr (PtrState (ptr_ty ptr) (ptr_nullability ptr) (ptr_flags ptr) (ptr_off_min ptr)
        (ptr_off_max ptr) (ptr_size ptr) None (ptr_align ptr) (ptr_permission ptr)
        (ptr_ref_obj ptr))
      else value
  | _ => value
  end.

Definition prepare_call (state : abstract_state) : abstract_state :=
  List.map (fun fact =>
    match fact with
    | AbstractValue expression value => AbstractValue expression (forget_packet_end value)
    | MemoryCell region bytes value => MemoryCell region bytes (forget_packet_end value)
    | _ => fact
    end)
    (filter (fun fact => match fact with Guarded _ _ _ => false | _ => true end) state).

(** A call in Rust's instruction loop: calls never take the premise-index
    path, so spill tracking runs with the [Call] effect around
    [transfer_instruction]'s [Call] arm. That arm rejects a tail call
    ([tail_call] is Rust's [PolicyEnv::is_tail_call]) while a resource is held
    ([ensure_nothing_held]), prepares the state and runs [apply_spec_call]. *)
Definition transfer_call (spec : call_spec) (tail_call : bool) (before : abstract_machine_state)
    (dst : var) (clobbered : ireg -> var) : option abstract_machine_state :=
  transfer_at_entry SpillProvenance.Call before
    (if tail_call && negb (ensure_nothing_held (facts before)) then None
     else option_map (fun post =>
         AbstractMachineState post (call_register_names (register_name before) dst clobbered))
       (transfer_spec_call spec (prepare_call (facts before))
         (call_args (register_name before)) dst)).

(** =========== Soundness proof =========== *)

(** ** Concrete calls *)

(** [exec_step_external] once the instruction at [PC] is found. Upstream
    leaves the code identifier and tail-call count after a helper call
    unconstrained; so does this relation. *)
Definition external_call_step
    (call : imm -> val -> val -> val -> val -> val -> outcome -> option (val * mem))
    (immediate : imm) (before after : tls_state) : Prop :=
  match before, after with
  | TLS_State regs stack code_id count memory, TLS_State regs' stack' _ _ memory' =>
      exists result,
        call immediate (regs R1) (regs R2) (regs R3) (regs R4) (regs R5)
          (Next regs stack code_id count memory) = Some (result, memory') /\
        regs' = nextinstr ((undef_caller_save_regs regs) # R0 <- result) # PC <-
          (Val.offset_ptr (regs PC) Ptrofs.one) /\
        stack' = stack
  end.

Lemma external_call_step_of_step : forall find_instr call addr_map program before after,
  step find_instr call addr_map program before [eBPF_ext_call] after ->
  exists immediate, external_call_step call immediate before after.
Proof.
  intros find_instr call addr_map program before after STEP.
  inversion STEP; subst.
  - match goal with
    | EVENT : exec_instr_event ?i = _ |- _ => destruct i; discriminate EVENT
    end.
  - exists i. cbn. exists res. auto.
Qed.

(** The trusted summary of a callee (helper, kfunc or subprogram) on the
    modeled subset: a non-void callee returns a defined [R0]; every callee
    keeps the store policy's and the memory environment's guarantees and every fact the
    transfer retains, and establishes its instantiated postcondition; a
    trusted non-void callee whose postcondition gives the result no pointer
    fact returns an integer. This is assumed kernel behaviour; the last
    conjunct is Rust's justification of [mark_scalar] in [apply_spec_call]:
    "Every modelled helper or kfunc result that is not a pointer is an
    integer". *)
Definition call_contract (world : interpretation) (attrs : load_attrs) (spec : call_spec)
    (state : abstract_state) (args : list var) (dst : var) (memory memory' : mem)
    (result : val) : Prop :=
  (spec_returns_void spec = false -> runtime_value result) /\
  store_policy_holds world memory' attrs /\
  memory_environment_holds world memory' attrs /\
  (forall fact, In fact (call_kept_facts spec state) ->
     atom_holds world memory fact -> atom_holds world memory' fact) /\
  (forall post, instantiate_spec_atoms (spec_post spec) args (Some dst) = Some post ->
     Forall (atom_holds (assign_value world dst result) memory') post) /\
  (forall post, instantiate_spec_atoms (spec_post spec) args (Some dst) = Some post ->
     spec_trusted spec = true -> spec_returns_void spec = false ->
     find_pointer_fact post dst = None -> exists n, result = Vlong n).

(** The register file after a call returns: [R0] holds the result and the
    callee-saved registers are kept. The argument registers may hold
    anything: their new names carry no fact. *)
Definition call_result_registers (regs regs' : regset) (result : val) : Prop :=
  regs' R0 = result /\
  (forall reg, In reg [R6; R7; R8; R9; R10] -> regs' reg = regs reg).

(** ** Transfer facts *)

Lemma invalidate_packet_pointers_holds : forall world memory state,
  Forall (atom_holds world memory) state ->
  Forall (atom_holds world memory) (invalidate_packet_pointers state).
Proof.
  intros world memory state FACTS. unfold invalidate_packet_pointers.
  apply Forall_app. split.
  - apply Forall_forall. intros fact IN. apply in_map_iff in IN as [source [<- IN]].
    apply filter_In in IN as [IN _].
    pose proof ((proj1 (Forall_forall _ _) FACTS) _ IN) as HOLDS.
    destruct source; try exact HOLDS.
    destruct (Region.uninit_by_default region && is_packet_value value) eqn:PACKET;
      [| exact HOLDS].
    apply andb_true_iff in PACKET as [UNINIT PACKET].
    destruct value; try discriminate. cbn [atom_holds cell_holds] in HOLDS |- *.
    rewrite UNINIT. tauto.
  - apply Forall_forall. intros fact IN. apply in_map_iff in IN as [name [<- IN]].
    apply in_flat_map in IN as [source [SOURCE IN]].
    destruct source; try contradiction. destruct term; try contradiction.
    destruct (is_packet_value value) eqn:PACKET; [| contradiction].
    destruct IN as [<- | []].
    pose proof ((proj1 (Forall_forall _ _) FACTS) _ SOURCE) as HOLDS.
    destruct value; try discriminate. cbn [atom_holds eval_term value_holds] in HOLDS |- *.
    unfold pointer_state_holds in HOLDS. tauto.
Qed.

Lemma call_kept_facts_hold : forall world memory spec state,
  Forall (atom_holds world memory) state ->
  Forall (atom_holds world memory) (call_kept_facts spec state).
Proof.
  intros world memory spec state FACTS. unfold call_kept_facts.
  destruct (spec_changes_pkt_data spec || spec_has_callback spec);
    [now apply invalidate_packet_pointers_holds | exact FACTS].
Qed.

Lemma forget_packet_end_holds : forall world memory value concrete,
  value_holds world memory value concrete ->
  value_holds world memory (forget_packet_end value) concrete.
Proof.
  intros world memory [| | | | | | ptr] concrete HOLDS; cbn [forget_packet_end]; try exact HOLDS.
  destruct (Region.is_bounded_by_cmp (ptr_ty ptr)); [| exact HOLDS].
  pose proof HOLDS as [FIELDS [_ [_ [_ RUNTIME]]]].
  rewrite <- (ArithmeticHelpers.addl_zero_runtime concrete RUNTIME).
  apply ArithmeticHelpers.pointer_shift_holds with (ptr := ptr); try reflexivity; try exact HOLDS.
  - unfold pointer_fields_well_formed in *.
    cbn [ptr_off_min ptr_off_max ptr_size ptr_align ptr_flags ptr_end_min].
    destruct FIELDS as [MIN [MAX [SIZE [ALIGN [FLAGS _]]]]].
    exact (conj MIN (conj MAX (conj SIZE (conj ALIGN (conj FLAGS I))))).
  - intros offset OFFSET. now rewrite Z.add_0_r.
  - intros offset width WINDOW. rewrite Z.add_0_r. unfold verified_window in *.
    cbn [ptr_ty ptr_size ptr_off_min ptr_off_max ptr_end_min] in WINDOW.
    destruct WINDOW as [LOW [HIGH | [bound [NONE _]]]]; [| discriminate NONE].
    split; [exact LOW | left; exact HIGH].
Qed.

Lemma prepare_call_holds : forall world memory state,
  Forall (atom_holds world memory) state ->
  Forall (atom_holds world memory) (prepare_call state).
Proof.
  intros world memory state FACTS. apply Forall_forall. intros fact IN.
  unfold prepare_call in IN. apply in_map_iff in IN as [source [<- IN]].
  apply filter_In in IN as [IN _].
  pose proof ((proj1 (Forall_forall _ _) FACTS) _ IN) as HOLDS.
  destruct source; try exact HOLDS; cbn [atom_holds] in HOLDS |- *.
  - destruct value as [| | | | | | ptr]; try exact HOLDS.
    pose proof (forget_packet_end_holds world memory (Ptr ptr)) as WEAKEN.
    assert (SHAPE : exists ptr', forget_packet_end (Ptr ptr) = Ptr ptr').
    { cbn [forget_packet_end]. destruct (Region.is_bounded_by_cmp (ptr_ty ptr));
        eexists; reflexivity. }
    destruct SHAPE as [ptr' SHAPE]. rewrite SHAPE in WEAKEN |- *.
    cbn [cell_holds cell_value_holds] in HOLDS |- *.
    destruct HOLDS as [ORDER [ADDRESSABLE [INIT [size [WIDTH RESULT]]]]].
    repeat split; try assumption. exists size. split; [exact WIDTH |].
    unfold cell_result_holds in *.
    destruct (load size (region_address world region (lower bytes)) memory);
      [| destruct (Region.probe_readable region); [| contradiction]];
      exact (WEAKEN _ RESULT).
  - exact (forget_packet_end_holds _ _ _ _ HOLDS).
Qed.

Lemma apply_undef_holds : forall world memory state dst value,
  Forall (atom_holds world memory) state ->
  Forall (atom_holds (assign_value world dst value) memory) (apply_undef state dst).
Proof.
  intros world memory state dst value FACTS. apply Forall_forall. intros fact IN.
  apply filter_In in IN as [IN KEEP]. apply negb_true_iff in KEEP.
  eapply atom_holds_assign; [exact KEEP |].
  exact ((proj1 (Forall_forall _ _) FACTS) _ IN).
Qed.

Lemma find_pointer_fact_app_none : forall prefix state name,
  find_pointer_fact (prefix ++ state) name = None -> find_pointer_fact state name = None.
Proof.
  intros prefix state name FIND. unfold find_pointer_fact in *. rewrite fold_left_app in FIND.
  destruct (fold_left _ prefix None) as [ptr |]; [| exact FIND].
  exfalso. revert FIND. induction state as [| fact state IH]; cbn; [discriminate | exact IH].
Qed.

Lemma mark_call_result_keeps : forall spec state dst fact,
  In fact state -> In fact (mark_call_result spec state dst).
Proof.
  intros spec state dst fact IN. unfold mark_call_result, mark_scalar.
  destruct (spec_trusted spec && negb (spec_returns_void spec)); [| exact IN].
  destruct (find_pointer_fact state dst); [exact IN |].
  destruct (existsb _ state); [exact IN | apply in_or_app; now left].
Qed.

Lemma transfer_spec_call_holds :
  forall world attrs spec state args dst memory memory' result post,
    Forall (atom_holds world memory) state ->
    call_contract world attrs spec state args dst memory memory' result ->
    transfer_spec_call spec state args dst = Some post ->
    Forall (atom_holds (assign_value world dst result) memory') post.
Proof.
  intros world attrs spec state args dst memory memory' result post FACTS
    [RUNTIME [_ [_ [KEPT [POST SCALAR]]]]] TRANSFER.
  unfold transfer_spec_call in TRANSFER.
  destruct (instantiate_spec_atoms (spec_post spec) args (Some dst)) as [instantiated |]
    eqn:INSTANTIATED; try discriminate.
  cbn [option_map] in TRANSFER. inversion TRANSFER; subst post.
  assert (RETAINED : Forall (atom_holds world memory') (call_kept_facts spec state)).
  { apply Forall_forall. intros fact IN. apply KEPT; [exact IN |].
    exact ((proj1 (Forall_forall _ _) (call_kept_facts_hold _ _ spec _ FACTS)) _ IN). }
  assert (DEFINED : Forall (atom_holds (assign_value world dst result) memory')
    ((if spec_returns_void spec then apply_undef (call_kept_facts spec state) dst
      else apply_havoc (call_kept_facts spec state) dst) ++ instantiated)).
  { apply Forall_app. split; [| exact (POST _ eq_refl)].
    destruct (spec_returns_void spec).
    - now apply apply_undef_holds.
    - apply apply_havoc_holds; [exact RETAINED | exact (RUNTIME eq_refl)]. }
  unfold mark_call_result.
  destruct (spec_trusted spec && negb (spec_returns_void spec)) eqn:MARK; [| exact DEFINED].
  apply andb_true_iff in MARK as [TRUSTED NOT_VOID]. apply negb_true_iff in NOT_VOID.
  apply mark_scalar_holds; [exact DEFINED |]. intros FIND.
  cbn [assign_value variable_value]. destruct (Nat.eq_dec dst dst) as [_ | DIFFERENT];
    [| contradiction].
  exact (SCALAR _ eq_refl TRUSTED NOT_VOID (find_pointer_fact_app_none _ _ _ FIND)).
Qed.

(** ** Tail-call rejection *)

Lemma transfer_call_accepted : forall spec tail_call before dst clobbered after,
  transfer_call spec tail_call before dst clobbered = Some after ->
  transfer_call spec false before dst clobbered = Some after.
Proof.
  intros spec tail_call before dst clobbered after TRANSFER.
  unfold transfer_call in *.
  destruct (tail_call && negb (ensure_nothing_held (facts before))); [| exact TRANSFER].
  unfold transfer_at_entry, transfer_with_provenance in TRANSFER.
  destruct (SpillProvenance.update _ _ _). discriminate.
Qed.

(** ** Registers after a call *)

(** Assigns each fresh argument-register name the value its register holds
    after the call. *)
Definition clobber_world (world : interpretation) (clobbered : ireg -> var)
    (regs : regset) : interpretation :=
  fold_left (fun current reg => assign_value current (clobbered reg) (regs reg))
    [R1; R2; R3; R4; R5] world.

Lemma clobber_world_clobbered : forall world clobbered (regs : regset) reg,
  call_names_distinct clobbered -> In reg [R1; R2; R3; R4; R5] ->
  variable_value (clobber_world world clobbered regs) (clobbered reg) = regs reg.
Proof.
  intros world clobbered regs reg DISTINCT IN. unfold clobber_world.
  cbn [fold_left assign_value variable_value].
  destruct IN as [<- | [<- | [<- | [<- | [<- | []]]]]];
    repeat match goal with |- context [Nat.eq_dec ?x ?y] => destruct (Nat.eq_dec x y) end;
    try reflexivity;
    exfalso; match goal with
    | DIFFERENT : ?x <> ?x |- _ => exact (DIFFERENT eq_refl)
    | SAME : ?f ?reg = ?f ?other |- _ =>
        apply (DISTINCT reg other); [cbn; tauto | cbn; tauto | discriminate | exact SAME]
    end.
Qed.

Lemma clobber_world_other : forall world clobbered (regs : regset) name,
  (forall reg, In reg [R1; R2; R3; R4; R5] -> clobbered reg <> name) ->
  variable_value (clobber_world world clobbered regs) name = variable_value world name.
Proof.
  intros world clobbered regs name FRESH. unfold clobber_world.
  cbn [fold_left assign_value variable_value].
  repeat match goal with |- context [Nat.eq_dec ?x ?y] => destruct (Nat.eq_dec x y) end;
    try reflexivity.
  all: exfalso; match goal with
    | SAME : _ = ?f ?reg |- _ =>
        apply (FRESH reg); [cbn; tauto | symmetry; exact SAME]
    end.
Qed.

Lemma clobber_world_atoms : forall world memory clobbered (regs : regset) post,
  (forall reg, In reg [R1; R2; R3; R4; R5] ->
    Forall (fun fact => atom_mentions (clobbered reg) fact = false) post) ->
  Forall (atom_holds world memory) post ->
  Forall (atom_holds (clobber_world world clobbered regs) memory) post.
Proof.
  intros world memory clobbered regs post FRESH FACTS. apply Forall_forall. intros fact IN.
  pose proof ((proj1 (Forall_forall _ _) FACTS) _ IN) as HOLDS.
  assert (MENTIONS : forall reg, In reg [R1; R2; R3; R4; R5] ->
    atom_mentions (clobbered reg) fact = false).
  { intros reg REG. exact ((proj1 (Forall_forall _ _) (FRESH reg REG)) _ IN). }
  unfold clobber_world. cbn [fold_left].
  repeat (apply atom_holds_assign; [apply MENTIONS; cbn; tauto |]). exact HOLDS.
Qed.

Lemma call_registers_agree : forall world before dst clobbered (regs regs' : regset) result post,
  (forall reg, reg <> RAX -> variable_value world (register_name before reg) = regs reg) ->
  call_names_fresh before dst clobbered post ->
  call_result_registers regs regs' result ->
  forall reg, reg <> RAX ->
    variable_value (clobber_world (assign_value world dst result) clobbered regs')
      (call_register_names (register_name before) dst clobbered reg) = regs' reg.
Proof.
  intros world before dst clobbered regs regs' result post REGISTERS [DISTINCT FRESH]
    [RESULT SAVED] reg NOT_AUX.
  assert (ASSIGNED : forall name, name <> dst ->
    variable_value (assign_value world dst result) name = variable_value world name).
  { intros name DIFFERENT. cbn [assign_value variable_value].
    destruct (Nat.eq_dec name dst); congruence. }
  destruct reg; cbn [call_register_names]; [| | | | | | | | | | | contradiction].
  1: { rewrite clobber_world_other.
       - cbn [assign_value variable_value]. destruct (Nat.eq_dec dst dst); congruence.
       - intros argument IN. now apply FRESH. }
  1-5: apply clobber_world_clobbered; [exact DISTINCT | cbn; tauto].
  all: rewrite SAVED by (cbn; tauto); rewrite <- REGISTERS by discriminate;
    match goal with
    | |- variable_value _ (?names ?saved) = _ =>
        destruct (proj2 (proj2 (FRESH R1 ltac:(cbn; tauto))) saved ltac:(cbn; tauto))
          as [_ NOT_DST];
        rewrite clobber_world_other;
        [ apply ASSIGNED; exact NOT_DST
        | intros argument IN; apply not_eq_sym;
          exact (proj1 (proj2 (proj2 (FRESH argument IN)) saved ltac:(cbn; tauto))) ]
    end.
Qed.

(** The state after any call returning [result] with these registers. *)
Lemma call_post_concretizes :
  forall world (attrs : load_attrs) regions spec tail_call before after dst clobbered
         (regs regs' : regset) memory memory' result stack code_id count,
    (forall reg, reg <> RAX -> variable_value world (register_name before reg) = regs reg) ->
    Forall (atom_holds world memory) (facts before) ->
    cell_blocks_exclusive world ->
    environment_holds world memory attrs regions ->
    transfer_call spec tail_call before dst clobbered = Some after ->
    call_names_fresh before dst clobbered (facts after) ->
    call_contract world attrs spec (prepare_call (facts before))
      (call_args (register_name before)) dst memory memory' result ->
    call_result_registers regs regs' result ->
    concretizes attrs regions after (TLS_State regs' stack code_id count memory').
Proof.
  intros world attrs regions spec tail_call before after dst clobbered regs regs' memory memory'
    result stack code_id count REGISTERS FACTS LAYOUT ENVIRONMENT TRANSFER FRESH CONTRACT RESULT.
  apply transfer_call_accepted in TRANSFER.
  unfold transfer_call, transfer_at_entry, transfer_with_provenance in TRANSFER.
  cbn [SpillProvenance.update andb] in TRANSFER.
  destruct (transfer_spec_call spec (prepare_call (facts before))
    (call_args (register_name before)) dst) as [post |] eqn:POST; try discriminate.
  cbn [option_map fst] in TRANSFER. inversion TRANSFER; subst after. clear TRANSFER.
  exists (clobber_world (assign_value world dst result) clobbered regs').
  split; [| split; [| split]].
  - intros reg. cbn [register_name]. eapply call_registers_agree; eauto.
  - apply clobber_world_atoms; [intros reg IN; now apply (proj2 FRESH) |].
    apply materialize_holds; [| cbn; contradiction].
    eapply transfer_spec_call_holds; [apply prepare_call_holds; exact FACTS | exact CONTRACT
      | exact POST].
  - exact (proj1 (proj2 CONTRACT)).
  - split; [exact LAYOUT |].
    split; [exact (proj1 (proj2 (proj2 CONTRACT))) | exact (proj2 ENVIRONMENT)].
Qed.

(** ** Helper and kfunc calls *)

(** CONDITIONAL soundness of an effect-free helper or kfunc call relative to
    upstream's parametrized external call: the call function must satisfy
    [call_contract] on this call's arguments. [transfer_spec_call] equals
    Rust's [apply_spec_call] only under [effect_free_spec]. *)
Theorem transfer_helper_call_sound_if_contract :
  forall call immediate (attrs : load_attrs) regions spec tail_call before after dst clobbered
         world (regs : regset) stack code_id count memory concrete',
    effect_free_spec spec ->
    (forall reg, reg <> RAX -> variable_value world (register_name before reg) = regs reg) ->
    Forall (atom_holds world memory) (facts before) ->
    cell_blocks_exclusive world ->
    environment_holds world memory attrs regions ->
    transfer_call spec tail_call before dst clobbered = Some after ->
    call_names_fresh before dst clobbered (facts after) ->
    external_call_step call immediate (TLS_State regs stack code_id count memory) concrete' ->
    (forall result memory',
      call immediate (regs R1) (regs R2) (regs R3) (regs R4) (regs R5)
        (Next regs stack code_id count memory) = Some (result, memory') ->
      call_contract world attrs spec (prepare_call (facts before))
        (call_args (register_name before))
        dst memory memory' result) ->
    concretizes attrs regions after concrete'.
Proof.
  intros call immediate attrs regions spec tail_call before after dst clobbered world regs stack
    code_id count memory concrete' _ REGISTERS FACTS LAYOUT ENVIRONMENT TRANSFER FRESH STEP CONTRACT.
  destruct concrete' as [regs' stack' code_id' count' memory'].
  destruct STEP as [result [CALL [REGS' _]]].
  eapply call_post_concretizes; eauto.
  subst regs'. split.
  - unfold nextinstr. rewrite !Pregmap.gso by discriminate. apply Pregmap.gss.
  - intros reg IN. unfold nextinstr. rewrite !Pregmap.gso by discriminate.
    rewrite Pregmap.gso by (destruct IN as [<- | [<- | [<- | [<- | [<- | []]]]]]; discriminate).
    destruct IN as [<- | [<- | [<- | [<- | [<- | []]]]]]; reflexivity.
Qed.

(** ** Subprogram calls *)

(** The frame [exec_call_internal] pushes. *)
Definition call_frame (regs : regset) : cstk' :=
  mk_cstk' (Val.offset_ptr (regs PC) Ptrofs.one)
    (regs R6) (regs R7) (regs R8) (regs R9) (regs R10).

Lemma local_call_pushes_frame :
  forall regions program immediate (regs : regset) stack code_id count memory
         regs' stack' code_id' count' memory',
    instruction_step regions program (Pcall CallInternal immediate)
      (TLS_State regs stack code_id count memory)
      (TLS_State regs' stack' code_id' count' memory') ->
    stack' = call_frame regs :: stack.
Proof.
  intros regions program immediate regs stack code_id count memory
    regs' stack' code_id' count' memory' STEP.
  unfold instruction_step in STEP. cbn [exec_instr] in STEP. unfold exec_call_internal in STEP.
  destruct (Mem.alloc memory 0 bpf_stack_size). inversion STEP. reflexivity.
Qed.

Lemma local_return_restores_frame :
  forall regions program frame (regs : regset) stack code_id count memory
         regs' stack' code_id' count' memory',
    instruction_step regions program Pret
      (TLS_State regs (frame :: stack) code_id count memory)
      (TLS_State regs' stack' code_id' count' memory') ->
    regs' = (undef_caller_save_regs regs) # PC <- (stk_ra frame) # R6 <- (stk_r6 frame)
      # R7 <- (stk_r7 frame) # R8 <- (stk_r8 frame) # R9 <- (stk_r9 frame)
      # R10 <- (stk_r10 frame) /\
    stack' = stack.
Proof.
  intros regions program frame regs stack code_id count memory
    regs' stack' code_id' count' memory' STEP.
  unfold instruction_step in STEP. cbn [exec_instr] in STEP. unfold exec_ret in STEP.
  destruct (regs R10); try discriminate.
  destruct (Mem.free memory b 0 bpf_stack_size); try discriminate.
  inversion STEP. auto.
Qed.

(** CONDITIONAL soundness of an effect-free subprogram call, from the call
    instruction to the matching return. Between the two steps the callee may
    run arbitrarily, provided the frame pushed by the call is again on top of
    the stack at its return. The callee summary [call_contract] is what
    [check_function_specs] is meant to establish for the callee's body; it is
    assumed here. *)
Theorem transfer_local_call_sound_if_contract :
  forall regions program immediate (attrs : load_attrs) spec tail_call before after dst clobbered
         world (regs0 : regset) stack0 code_id0 count0 memory0
         (regs1 : regset) stack1 code_id1 count1 memory1
         (regs2 : regset) code_id2 count2 memory2
         (regs3 : regset) stack3 code_id3 count3 memory3,
    effect_free_spec spec ->
    (forall reg, reg <> RAX -> variable_value world (register_name before reg) = regs0 reg) ->
    Forall (atom_holds world memory0) (facts before) ->
    cell_blocks_exclusive world ->
    environment_holds world memory0 attrs regions ->
    transfer_call spec tail_call before dst clobbered = Some after ->
    call_names_fresh before dst clobbered (facts after) ->
    instruction_step regions program (Pcall CallInternal immediate)
      (TLS_State regs0 stack0 code_id0 count0 memory0)
      (TLS_State regs1 stack1 code_id1 count1 memory1) ->
    instruction_step regions program Pret
      (TLS_State regs2 stack1 code_id2 count2 memory2)
      (TLS_State regs3 stack3 code_id3 count3 memory3) ->
    call_contract world attrs spec (prepare_call (facts before))
      (call_args (register_name before))
      dst memory0 memory3 (regs2 R0) ->
    concretizes attrs regions after (TLS_State regs3 stack3 code_id3 count3 memory3) /\
    regs3 PC = Val.offset_ptr (regs0 PC) Ptrofs.one /\
    stack3 = stack0.
Proof.
  intros regions program immediate attrs spec tail_call before after dst clobbered world
    regs0 stack0 code_id0 count0 memory0 regs1 stack1 code_id1 count1 memory1
    regs2 code_id2 count2 memory2 regs3 stack3 code_id3 count3 memory3
    _ REGISTERS FACTS LAYOUT ENVIRONMENT TRANSFER FRESH CALL RETURN CONTRACT.
  rewrite (local_call_pushes_frame _ _ _ _ _ _ _ _ _ _ _ _ _ CALL) in RETURN.
  destruct (local_return_restores_frame _ _ _ _ _ _ _ _ _ _ _ _ _ RETURN) as [REGS3 STACK3].
  subst regs3 stack3. split; [| split; [| reflexivity]].
  - eapply call_post_concretizes; eauto.
    split.
    + rewrite !Pregmap.gso by discriminate. reflexivity.
    + intros reg IN.
      destruct IN as [<- | [<- | [<- | [<- | [<- | []]]]]];
        cbn [call_frame stk_r6 stk_r7 stk_r8 stk_r9 stk_r10];
        repeat first [rewrite Pregmap.gss; reflexivity | rewrite Pregmap.gso by discriminate].
  - rewrite !Pregmap.gso by discriminate. now rewrite Pregmap.gss.
Qed.

(** ** Tail calls *)

(** The kernel's [do_misc_fixups] rewrites the [bpf_tail_call] helper call
    into [BPF_JMP | BPF_TAIL_CALL] ([verifier.c:22399]): [Ptail_call]. *)

Lemma tail_call_keeps_r0 :
  forall regions program (regs : regset) stack code_id count memory
         regs' stack' code_id' count' memory',
    instruction_step regions program Ptail_call
      (TLS_State regs stack code_id count memory)
      (TLS_State regs' stack' code_id' count' memory') ->
    regs' R0 = regs R0.
Proof.
  intros regions program regs stack code_id count memory regs' stack' code_id' count' memory'
    STEP.
  unfold instruction_step in STEP. cbn [exec_instr] in STEP. unfold exec_tail_call in STEP.
  repeat match type of STEP with
  | context [match ?x with _ => _ end] => destruct x eqn:?; try discriminate
  end;
  inversion STEP; subst; unfold nextinstr; now rewrite Pregmap.gso by discriminate.
Qed.

(** The transfer before [bpf_tail_call] carried Rust's [returns_void]: a
    non-void spec havocs [R0] to an initialized [Unknown]. A failing tail
    call falls through with [R0] unchanged, so when [R0] was never written,
    no state the post-state describes is reached. Rust's [machine_spec] still
    clears [returns_void] for a machine-target [bpf_tail_call]. *)
Theorem transfer_non_void_tail_call_r0_unsound :
  forall (attrs : load_attrs) program regions spec tail_call before after dst clobbered
         (regs : regset) stack code_id count memory concrete',
    spec_returns_void spec = false ->
    transfer_call spec tail_call before dst clobbered = Some after ->
    regs R0 = Vundef ->
    instruction_step regions program Ptail_call
      (TLS_State regs stack code_id count memory) concrete' ->
    ~ concretizes attrs regions after concrete'.
Proof.
  intros attrs program regions spec tail_call before after dst clobbered regs stack code_id count
    memory concrete' NON_VOID TRANSFER UNDEFINED STEP CONCRETE.
  destruct concrete' as [regs' stack' code_id' count' memory'].
  pose proof (tail_call_keeps_r0 _ _ _ _ _ _ _ _ _ _ _ _ STEP) as KEPT.
  destruct CONCRETE as [world [REGISTERS [FACTS _]]].
  apply transfer_call_accepted in TRANSFER.
  unfold transfer_call, transfer_at_entry, transfer_with_provenance in TRANSFER.
  cbn [SpillProvenance.update andb] in TRANSFER.
  destruct (transfer_spec_call spec (prepare_call (facts before))
    (call_args (register_name before)) dst) as [post |] eqn:POST; try discriminate.
  cbn [option_map fst] in TRANSFER. injection TRANSFER as <-.
  unfold transfer_spec_call in POST. rewrite NON_VOID in POST.
  destruct (instantiate_spec_atoms (spec_post spec) (call_args (register_name before)) (Some dst))
    as [instantiated |]; try discriminate.
  cbn [option_map] in POST. injection POST as <-.
  cbn [facts] in FACTS.
  assert (HAVOCKED : In (AbstractValue (Var dst) Unknown) (mark_call_result spec
    (apply_havoc (call_kept_facts spec (prepare_call (facts before))) dst ++ instantiated) dst)).
  { apply mark_call_result_keeps. apply in_or_app. left. unfold apply_havoc.
    apply in_or_app. right. now left. }
  match type of FACTS with
  | Forall _ (SpillProvenance.materialize ?provenance ?atoms) =>
      assert (IN : In (AbstractValue (Var dst) Unknown)
        (SpillProvenance.materialize provenance atoms))
  end.
  { unfold SpillProvenance.materialize. apply in_or_app. left. apply filter_In.
    split; [exact HAVOCKED | reflexivity]. }
  pose proof ((proj1 (Forall_forall _ _) FACTS) _ IN) as HOLDS.
  cbn [atom_holds eval_term value_holds] in HOLDS.
  specialize (REGISTERS R0 ltac:(discriminate)). cbn [register_name call_register_names] in REGISTERS.
  rewrite REGISTERS, KEPT, UNDEFINED in HOLDS. inversion HOLDS.
Qed.

(** Soundness of a failing tail call under Rust's [returns_void]
    [bpf_tail_call] spec, whose postcondition is empty: the fall-through
    state, with every register and the memory unchanged, is described by the
    post-state. A successful tail call leaves this program, which
    [ensure_nothing_held] lets it do only while no resource is held. *)
Theorem transfer_void_tail_call_falls_through_sound :
  forall (attrs : load_attrs) program regions spec tail_call before after dst clobbered world
         (regs : regset) stack code_id count memory count',
    spec_returns_void spec = true ->
    spec_post spec = [] ->
    (forall reg, reg <> RAX -> variable_value world (register_name before reg) = regs reg) ->
    Forall (atom_holds world memory) (facts before) ->
    store_policy_holds world memory attrs ->
    cell_blocks_exclusive world ->
    environment_holds world memory attrs regions ->
    transfer_call spec tail_call before dst clobbered = Some after ->
    call_names_fresh before dst clobbered (facts after) ->
    instruction_step regions program Ptail_call
      (TLS_State regs stack code_id count memory)
      (TLS_State (nextinstr regs) stack code_id count' memory) ->
    concretizes attrs regions after (TLS_State (nextinstr regs) stack code_id count' memory).
Proof.
  intros attrs program regions spec tail_call before after dst clobbered world regs stack code_id
    count memory count' VOID EMPTY REGISTERS FACTS POLICY LAYOUT ENVIRONMENT TRANSFER FRESH _.
  eapply call_post_concretizes with (memory := memory) (result := regs R0); eauto.
  - split; [| split; [exact POLICY | split; [exact (proj1 ENVIRONMENT) | split; [| split]]]].
    + rewrite VOID. discriminate.
    + intros fact _ HOLDS. exact HOLDS.
    + rewrite EMPTY. intros post INSTANTIATED. cbn in INSTANTIATED.
      inversion INSTANTIATED. constructor.
    + intros post _ _ NON_VOID. rewrite VOID in NON_VOID. discriminate.
  - split.
    + unfold nextinstr. now rewrite Pregmap.gso by discriminate.
    + intros reg IN. unfold nextinstr.
      rewrite Pregmap.gso by (destruct IN as [<- | [<- | [<- | [<- | [<- | []]]]]]; discriminate).
      reflexivity.
Qed.
