From Coq Require Import Bool List ZArith Lia.
From compcert Require Import Coqlib Integers Values Memory AST.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.
From TrustNoBPF.Semantics Require Import AbstractDomain Concretization Transfer CompCertAssms
  KernelAssms IRLevelAssms Common ArithmeticHelpers Arithmetic MemoryLoad MemoryStoreImm MemoryStoreReg
  ControlFlow.
Import ListNotations.
Open Scope Z_scope.

(** * Global soundness of the Rust verifier

    The theorem has four groups of hypotheses, each defined in this file from
    the named assumptions of the other files:
    - [ir_level_assumptions]: The underlying small-step semantics operates on
      the kernel-level eBPF bytecode, whereas the verifier works on an IR equivalent
      to the user-level eBPF bytecode. These state the assumptions about the correspondance
      and the rewrites performed by the kernel between user and kernel space.
    - [compcert_assumptions]: The small-step semantics uses the CompCert memory model
      which is stronger than the one used by the verifier, and as such we need some
      additional assumptions.
    - [kernel_assumptions]: What Rust assumes of the kernel memory a program reads
      and concretization does not describe.
    - [verifier_assumptions]: These are roughly speaking the global conditions maintained
      by the verifier whose precise implementation was out of scope for this mechanisation.

    Scope: Limited by the implementation scope of the underlying small-step semantics
           the soundness theorem covers only programs without calls, tail calls and
           atomic instructions. The verifier is the Rust one checking bytecode for a
           load without [allow_ptr_leaks]. *)

Section Soundness.

(** The program's load attributes: access rules, maps, loader image. *)
Variable attrs : load_attrs.
(** The semantics' table of loader-resolved addresses. *)
Variable regions : list addr_region.
(** The semantics' program image. Only tail calls read it. *)
Variable image : ebpf_prog.

(** ** Programs *)

(** An instruction in the Rust IR. *)
Inductive ir_instruction :=
  | Alu (size : OpSize.t) (op : ArithmeticOp.t) (dst : ireg) (lhs : option ireg)
      (source : ireg + imm)
  | Load (size : sizeOp) (dst base : ireg) (offset : Z)
  | StoreImm (size : sizeOp) (base : ireg) (offset : Z) (immediate : imm)
  | StoreReg (size : sizeOp) (base : ireg) (offset : Z) (source : ireg)
  | LoadImm64 (dst : ireg) (load : LdImm64.t)
  | Jump (offset : off)
  | Branch (op : CmpOp.t) (size : OpSize.t) (dst : ireg) (source : ireg + imm) (offset : off)
  | Exit.

(** A program is essentially two lists:
    - Intermediate representation instructions used by the verifier
    - Corresponding concrete kernel-level bytecode instructions interpretable by
      the small-step semantics
    
    These are indexed by ptrofs as this is what is used by small-step semantics for
    PC. *)
Record program := Program {
  ir_at : ptrofs -> option ir_instruction;
  kernel_at : ptrofs -> option instruction;
}.

Definition next (pc : ptrofs) : ptrofs := Ptrofs.add pc Ptrofs.one.

Definition jump_target (pc : ptrofs) (offset : off) : ptrofs := next (Ptrofs.add pc offset).

(** ** Abstract execution *)

(** Rust's SSA allocation: a name no register holds and no fact mentions. *)
Definition fresh_name (state : abstract_machine_state) (name : var) : Prop :=
  (forall reg, register_name state reg <> name) /\ fresh_in_facts state name.

Definition branch_condition (state : abstract_machine_state) (op : CmpOp.t) (dst : ireg)
    (source : ireg + imm) : condition :=
  Condition (register_name state dst)
    (match source with
     | inl reg => SourceOperand.Value (register_name state reg)
     | inr immediate => SourceOperand.Imm immediate
     end) op.

Definition continue_at (pc : ptrofs) (result : option abstract_machine_state) :
    option (list (ptrofs * abstract_machine_state)) :=
  option_map (fun after => [(pc, after)]) result.

Definition edge (pc : ptrofs) (result : option abstract_machine_state) :
    list (ptrofs * abstract_machine_state) :=
  match result with Some after => [(pc, after)] | None => [] end.

(** Rust's transfer of the instruction at [pc], naming the value it defines
    [fresh]. [None] is a verifier error; otherwise the successor instructions
    with their abstract states. An edge Rust proves infeasible has none.
    Two differences from Rust's blocks: Rust also runs the edge transfer
    (refinement and discharge) on the implicit edge into each block leader,
    and it keeps spill tracking across a block, where each instruction here
    starts it afresh from the facts ([transfer_at_entry]). *)
Definition successors (pc : ptrofs) (insn : ir_instruction) (before : abstract_machine_state)
    (fresh : var) : option (list (ptrofs * abstract_machine_state)) :=
  match insn with
  | Alu size op dst lhs source =>
      continue_at (next pc)
        (transfer_arithmetic_local (attr_entails attrs) before dst fresh lhs source size op)
  | Load size dst base offset =>
      continue_at (next pc) (transfer_load (attr_entails attrs) before dst base fresh size offset
        (store_strict_alignment attrs) (store_map_special_fields attrs)
        (store_ctx_policy attrs))
  | StoreImm size base offset immediate =>
      continue_at (next pc)
        (transfer_store_imm_instruction before base immediate size offset attrs)
  | StoreReg size base offset source =>
      continue_at (next pc)
        (transfer_store_reg_instruction (attr_entails attrs) before base source size offset attrs)
  | LoadImm64 dst load =>
      continue_at (next (next pc))
        (transfer_ld_imm64_local (attr_entails attrs) (attr_maps attrs) before dst fresh load)
  | Jump offset => Some (edge (jump_target pc offset) (transfer_jump before))
  | Branch op size dst source offset =>
      let cond := branch_condition before op dst source in
      match transfer_branch before cond size true, transfer_branch before cond size false with
      | Some taken, Some fallthrough =>
          Some (edge (jump_target pc offset) taken ++ edge (next pc) fallthrough)
      | _, _ => None
      end
  | Exit => if transfer_return before then Some [] else None
  end.

(** The instructions and abstract states Rust's analysis reaches from the
    entry invariant, along every path. *)
Inductive abstract_reachable (P : program) (entry : abstract_machine_state) :
    ptrofs -> abstract_machine_state -> Prop :=
  | ReachEntry : abstract_reachable P entry Ptrofs.zero entry
  | ReachStep : forall pc before insn fresh next_states pc' after,
      abstract_reachable P entry pc before ->
      ir_at P pc = Some insn ->
      fresh_name before fresh ->
      successors pc insn before fresh = Some next_states ->
      In (pc', after) next_states ->
      abstract_reachable P entry pc' after.

(** Rust accepts the program: wherever its analysis gets, there is an
    instruction and its transfer succeeds. *)
Definition verifier_accepts (P : program) (entry : abstract_machine_state) : Prop :=
  forall pc before, abstract_reachable P entry pc before ->
    exists insn fresh,
      ir_at P pc = Some insn /\ fresh_name before fresh /\
      successors pc insn before fresh <> None.

(** ** Concrete execution *)

(** The semantics executes the kernel instruction at the PC. Decoding is not
    modeled. *)
Definition concrete_step (P : program) (before after : tls_state) : Prop :=
  match before with
  | TLS_State regs _ _ _ _ =>
      exists b pc executed,
        regs PC = Vptr b pc /\ kernel_at P pc = Some executed /\
        instruction_step regions image executed before after
  end.

Inductive runs (P : program) : nat -> tls_state -> tls_state -> Prop :=
  | RunsNone : forall state, runs P O state state
  | RunsStep : forall n initial middle final,
      runs P n initial middle -> concrete_step P middle final -> runs P (S n) initial final.

Definition at_pc (state : tls_state) (pc : ptrofs) : Prop :=
  match state with TLS_State regs _ _ _ _ => exists b, regs PC = Vptr b pc end.

Definition call_stack (state : tls_state) : cstk :=
  match state with TLS_State _ stack _ _ _ => stack end.

(** A running state that an abstract state Rust reached at its instruction
    describes. *)
Definition described (P : program) (entry : abstract_machine_state) (state : tls_state) : Prop :=
  exists pc abstract,
    abstract_reachable P entry pc abstract /\ at_pc state pc /\
    concretizes attrs regions abstract state /\ call_stack state = [].

(** The program has exited with a defined return value, as in upstream's
    [final_lst_state]. *)
Definition exited (state : tls_state) : Prop :=
  match state with
  | TLS_State regs stack _ _ _ => regs PC = Vnullptr /\ stack = [] /\ runtime_value (regs R0)
  end.

(** ** Assumptions *)

(** *** IR level *)

(** How the kernel lowers each instruction Rust checked. *)
Definition lowers (before : abstract_machine_state) (insn : ir_instruction)
    (executed : instruction) : Prop :=
  match insn with
  | Alu size op dst lhs source =>
      program_register dst /\ program_operand source /\ arithmetic_in_place op lhs dst /\
      lowers_arithmetic size op dst source executed
  | Load size dst base offset =>
      exists kind,
        load_access_kind before base size offset (store_strict_alignment attrs)
          (store_map_special_fields attrs) (store_ctx_policy attrs) = Some kind /\
        lowers_load size dst base offset kind executed
  | StoreImm size base offset immediate =>
      exists kind,
        store_access_kind (facts before) (register_name before base) offset (load_width size)
          attrs = Some kind /\
        lowers_store size base (inr immediate) offset kind executed
  | StoreReg size base offset source =>
      exists kind,
        store_access_kind (facts before) (register_name before base) offset (load_width size)
          attrs = Some kind /\
        lowers_store size base (inl source) offset kind executed
  | LoadImm64 dst load => lowers_ld_imm64 (attr_loader attrs) dst load executed
  | Jump offset => executed = Pjmp64 offset
  | Branch op size dst source offset =>
      lowers_branch (register_name before) offset (branch_condition before op dst source) size
        executed
  | Exit => executed = Pret
  end.

Definition ir_level_assumptions (P : program) (entry : abstract_machine_state) : Prop :=
  forall pc before insn,
    abstract_reachable P entry pc before -> ir_at P pc = Some insn ->
    exists executed, kernel_at P pc = Some executed /\ lowers before insn executed.

(** *** CompCert *)

(** CompCert's semantics of the instruction is defined in [concrete] wherever
    the hardware's is: the [CompCertAssms.v] conditions it needs. *)
Definition compcert_defined (before : abstract_machine_state) (concrete : tls_state)
    (insn : ir_instruction) (executed : instruction) : Prop :=
  match concrete with
  | TLS_State regs _ _ _ memory =>
      match insn with
      | Alu size op dst _ source => alu_integer_operands before regs size dst source op
      | Load size _ base offset =>
          load_initialized_if_unmodeled before concrete base size offset /\
          load_fragments_defined concrete base size offset
      | StoreReg size _ _ source => narrow_store_integer regs size source
      | Branch _ _ _ _ _ =>
          static_operands_scalar regs executed /\ comparison_defined regs memory executed
      | _ => True
      end
  end.

(** CompCert's semantics is defined for the instruction at every point Rust
    reached, in every concrete state its abstract state describes. *)
Definition compcert_assumptions (P : program) (entry : abstract_machine_state) : Prop :=
  forall pc before concrete insn executed,
    abstract_reachable P entry pc before -> at_pc concrete pc ->
    concretizes attrs regions before concrete ->
    ir_at P pc = Some insn -> kernel_at P pc = Some executed ->
    compcert_defined before concrete insn executed.

(** *** Kernel *)

(** The kernel memory the instruction reads holds what Rust assumes of it: the
    [KernelAssms.v] conditions. *)
Definition kernel_defined (before : abstract_machine_state) (concrete : tls_state)
    (insn : ir_instruction) : Prop :=
  match insn with
  | Load size _ base offset => load_outside_stack_scalar before concrete base size offset
  | _ => True
  end.

(** The kernel memory is as Rust assumes at every point Rust reached, in every
    concrete state its abstract state describes. *)
Definition kernel_assumptions (P : program) (entry : abstract_machine_state) : Prop :=
  forall pc before concrete insn,
    abstract_reachable P entry pc before -> at_pc concrete pc ->
    concretizes attrs regions before concrete ->
    ir_at P pc = Some insn -> kernel_defined before concrete insn.

(** *** Verifier *)

(** A state Rust can represent and accepts: constants and memory coordinates
    fit in [i64], memory facts name regions with cells, and no memory cell is
    [Uninit]. Rust gets the first two from its types and certificate parser,
    and checks the last with [validate_invariant] at block entries. *)
Definition well_formed_state (state : abstract_state) : Prop :=
  transfer_input_valid state /\ ArithmeticHelpers.eq_constants_fit_i64 state /\
  order_constants_fit_i64 state.

(** Every abstract state Rust's analysis reaches is well formed. The Rocq
    transfers are not yet proved to preserve this. *)
Definition verifier_assumptions (P : program) (entry : abstract_machine_state) : Prop :=
  forall pc before, abstract_reachable P entry pc before -> well_formed_state (facts before).

(** ** The theorem *)

(** Take a program Rust accepts from the entry invariant [entry], and an
    initial state of the semantics that [entry] describes. For any [n], the
    program either runs [n] steps to a state Rust's analysis describes, or
    exits with a defined return value within [n] steps. Proved below as
    [global_soundness]. *)
Definition soundness_claim : Prop :=
  forall (P : program) (entry : abstract_machine_state) (initial : tls_state),
    verifier_accepts P entry ->
    ir_level_assumptions P entry ->
    compcert_assumptions P entry ->
    kernel_assumptions P entry ->
    verifier_assumptions P entry ->
    (exists ctx code stack, initial_lst_state ctx code stack initial) ->
    concretizes attrs regions entry initial ->
    forall n, exists final,
      (runs P n initial final /\ described P entry final) \/
      (exists m, (m <= n)%nat /\ runs P m initial final /\ exited final).

(** =========== Proofs =========== *)

Lemma fresh_name_destination : forall state dst name,
  fresh_name state name ->
  fresh_destination state dst name /\ name <> register_name state dst /\
  Forall (fun fact => atom_mentions name fact = false) (facts state).
Proof.
  intros state dst name [REGISTERS FACTS]. split; [| split].
  - intros reg _. apply REGISTERS.
  - intros EQUAL. exact (REGISTERS dst (eq_sym EQUAL)).
  - exact FACTS.
Qed.

Lemma nextinstr_pc : forall regs, nextinstr regs PC = Val.offset_ptr (regs PC) Ptrofs.one.
Proof. intros. apply Pregmap.gss. Qed.

Lemma set_ireg_pc : forall (regs : regset) (reg : ireg) value, (regs # reg <- value) PC = regs PC.
Proof. intros. apply Pregmap.gso. discriminate. Qed.

Lemma straight_line_step : forall executed regs stack code_id count memory
    regs' stack' code_id' count' memory',
  instruction_step regions image executed (TLS_State regs stack code_id count memory)
    (TLS_State regs' stack' code_id' count' memory') ->
  match executed with
  | Palu _ _ _ _ | Pload _ _ _ _ | Pload_probe _ _ _ _ | Pstore _ _ _ _ =>
      stack' = stack /\ regs' PC = Val.offset_ptr (regs PC) Ptrofs.one
  | Plddw _ _ _ _ =>
      stack' = stack /\
      regs' PC = Val.offset_ptr (Val.offset_ptr (regs PC) Ptrofs.one) Ptrofs.one
  | Pjmp64 offset =>
      stack' = stack /\ regs' PC = Val.offset_ptr (Val.offset_ptr (regs PC) offset) Ptrofs.one
  | _ => True
  end.
Proof.
  intros executed regs stack code_id count memory regs' stack' code_id' count' memory' STEP.
  unfold instruction_step in STEP.
  destruct executed; cbn [exec_instr] in STEP; try exact I;
    unfold exec_lddw, exec_load_probe, exec_load, exec_store, exec_alu, exec_jmp64 in STEP;
    repeat match type of STEP with context [match ?x with _ => _ end] => destruct x end;
    inversion STEP; subst; split; try reflexivity;
    rewrite !nextinstr_pc; rewrite ?set_ireg_pc, ?Pregmap.gss; reflexivity.
Qed.

Lemma exit_step : forall regs code_id count memory after,
  instruction_step regions image Pret (TLS_State regs [] code_id count memory) after ->
  after = TLS_State (regs # PC <- Vnullptr) [] code_id count memory.
Proof.
  intros regs code_id count memory [regs' stack' code_id' count' memory'] STEP.
  unfold instruction_step in STEP. cbn [exec_instr exec_ret] in STEP.
  inversion STEP. reflexivity.
Qed.

Lemma branch_progress : forall names offset cond size executed regs stack code_id count memory,
  lowers_branch names offset cond size executed ->
  comparison_defined regs memory executed ->
  exists after,
    instruction_step regions image executed (TLS_State regs stack code_id count memory) after.
Proof.
  intros names offset cond size executed regs stack code_id count memory LOWER DEFINED.
  inversion LOWER; subst; cbn [comparison_defined] in DEFINED;
    unfold instruction_step; cbn [exec_instr]; unfold exec_jmpcmp;
    match goal with |- context [eval_cmp_static ?op ?w ?r ?source] =>
      destruct (eval_cmp_static op w r source) end;
    try (eexists (TLS_State _ _ _ _ _); reflexivity);
    specialize (DEFINED eq_refl); destruct (lower_width size);
    match goal with |- context [match ?comparison with Some _ => _ | None => Stuck end] =>
      destruct comparison end;
    solve [eexists (TLS_State _ _ _ _ _); reflexivity | contradiction].
Qed.

Lemma initial_described : forall P entry initial,
  (exists ctx code stack, initial_lst_state ctx code stack initial) ->
  concretizes attrs regions entry initial -> described P entry initial.
Proof.
  intros P entry initial [ctx [code [stack INITIAL]]] CONCRETE.
  inversion INITIAL; subst.
  exists Ptrofs.zero, entry. split; [constructor |]. split; [| split; [exact CONCRETE | reflexivity]].
  cbn [at_pc]. exists code. rewrite !set_ireg_pc. apply Pregmap.gss.
Qed.

(** Progress and preservation: a described state steps to a described or an
    exited state. *)
Lemma described_step : forall P entry state,
  verifier_accepts P entry -> ir_level_assumptions P entry ->
  compcert_assumptions P entry -> kernel_assumptions P entry -> verifier_assumptions P entry ->
  described P entry state ->
  exists state', concrete_step P state state' /\ (described P entry state' \/ exited state').
Proof.
  intros P entry state ACCEPTS IR COMPCERT MEMORY VERIFIER
    [pc [before [REACH [AT [CONCRETE STACK]]]]].
  destruct (ACCEPTS _ _ REACH) as [insn [fresh [INSN [FRESH SUCCEEDS]]]].
  destruct (successors pc insn before fresh) as [next_states |] eqn:NEXT; [| contradiction].
  destruct (IR _ _ _ REACH INSN) as [executed [KERNEL LOWER]].
  pose proof (COMPCERT _ _ _ _ _ REACH AT CONCRETE INSN KERNEL) as COMPCERT_DEFINED.
  pose proof (MEMORY _ _ _ _ REACH AT CONCRETE INSN) as KERNEL_DEFINED.
  destruct (VERIFIER _ _ REACH) as [[NO_UNINIT COORDINATES] [EQ_FIT ORDER_FIT]].
  destruct state as [regs stack code_id count memory].
  cbn [at_pc call_stack] in AT, STACK. destruct AT as [b AT]. subst stack.
  assert (ADVANCE : forall pc' after state',
    In (pc', after) next_states ->
    instruction_step regions image executed (TLS_State regs [] code_id count memory) state' ->
    at_pc state' pc' -> call_stack state' = [] -> concretizes attrs regions after state' ->
    exists state'', concrete_step P (TLS_State regs [] code_id count memory) state'' /\
      (described P entry state'' \/ exited state'')).
  { intros pc' after state' IN STEP AT' STACK' CONCRETE'. exists state'. split.
    - exists b, pc, executed. auto.
    - left. exists pc', after. split; [eapply ReachStep; eauto | auto]. }
  destruct insn; cbn [successors continue_at] in NEXT; cbn [lowers] in LOWER;
    cbn [compcert_defined] in COMPCERT_DEFINED.
  - (* Alu *)
    destruct LOWER as [DST_REGISTER [SOURCE_REGISTER [IN_PLACE LOWER]]].
    destruct (transfer_arithmetic_local (attr_entails attrs) before dst fresh lhs source size op)
      as [after |] eqn:TRANSFER; [| discriminate].
    injection NEXT as <-.
    destruct (fresh_name_destination before dst fresh FRESH) as [FRESH_DST [NEW FRESH_FACTS]].
    unfold lowers_arithmetic in LOWER.
    destruct (arithmetic_opcode op) as [opcode |] eqn:OPCODE.
    + subst executed.
      destruct (transfer_arithmetic_sound (attr_entails attrs) attrs image regions before after
        regs [] code_id count
        memory dst fresh lhs source size op opcode FRESH_DST NEW FRESH_FACTS EQ_FIT DST_REGISTER
        SOURCE_REGISTER COMPCERT_DEFINED CONCRETE TRANSFER
        OPCODE IN_PLACE) as [[regs' stack' code_id' count' memory'] [STEP POST]].
      destruct (straight_line_step _ _ _ _ _ _ _ _ _ _ _ STEP) as [STACK' PC'].
      apply (ADVANCE (next pc) after _ (or_introl eq_refl) STEP); [| exact STACK' | exact POST].
      exists b. rewrite PC', AT. reflexivity.
    + destruct op; try discriminate OPCODE.
      destruct LOWER as [direction [width [SOURCE EXECUTED]]]. subst source executed.
      destruct IN_PLACE as [[MOV _] | LHS]; [discriminate MOV | subst lhs].
      destruct COMPCERT_DEFINED as [[a DST] NARROW].
      destruct (transfer_end_sound (attr_entails attrs) attrs image regions before after regs []
        code_id count memory dst fresh size direction width a) as [[regs' stack' code_id' count'
        memory'] [STEP POST]]; auto.
      { intros SIZE WIDTH. subst width. exact (NARROW SIZE eq_refl). }
      destruct (straight_line_step _ _ _ _ _ _ _ _ _ _ _ STEP) as [STACK' PC'].
      apply (ADVANCE (next pc) after _ (or_introl eq_refl) STEP); [| exact STACK' | exact POST].
      exists b. rewrite PC', AT. reflexivity.
  - (* Load *)
    destruct LOWER as [kind [KIND LOWER]].
    destruct (transfer_load (attr_entails attrs) before dst base fresh size offset
      (store_strict_alignment attrs) (store_map_special_fields attrs) (store_ctx_policy attrs))
      as [after |] eqn:TRANSFER; [| discriminate].
    injection NEXT as <-.
    destruct (fresh_name_destination before dst fresh FRESH) as [FRESH_DST [_ _]].
    destruct COMPCERT_DEFINED as [UNMODELED FRAGMENTS].
    destruct (transfer_load_mem_sound (attr_entails attrs) attrs image regions dst base fresh
      size offset (store_strict_alignment attrs) (store_map_special_fields attrs)
      (store_ctx_policy attrs) before after (TLS_State regs [] code_id count memory) kind
      executed FRESH_DST (proj2 FRESH) CONCRETE NO_UNINIT COORDINATES UNMODELED FRAGMENTS
      KERNEL_DEFINED TRANSFER KIND LOWER)
      as [[regs' stack' code_id' count' memory'] [STEP POST]].
    pose proof (straight_line_step _ _ _ _ _ _ _ _ _ _ _ STEP) as SHAPE.
    destruct LOWER; destruct SHAPE as [STACK' PC'];
      (apply (ADVANCE (next pc) after _ (or_introl eq_refl) STEP); [| exact STACK' | exact POST]);
      exists b; rewrite PC', AT; reflexivity.
  - (* StoreImm *)
    destruct LOWER as [kind [KIND LOWER]].
    destruct (transfer_store_imm_instruction before base immediate size offset attrs)
      as [after |] eqn:TRANSFER; [| discriminate].
    injection NEXT as <-.
    destruct (transfer_store_imm_sound attrs regions image before after base immediate size
      offset kind executed (TLS_State regs [] code_id count memory) CONCRETE
      (conj (conj NO_UNINIT COORDINATES) TRANSFER) KIND LOWER)
      as [[regs' stack' code_id' count' memory'] [STEP POST]].
    pose proof (straight_line_step _ _ _ _ _ _ _ _ _ _ _ STEP) as SHAPE.
    destruct LOWER. destruct SHAPE as [STACK' PC'].
    apply (ADVANCE (next pc) after _ (or_introl eq_refl) STEP); [| exact STACK' | exact POST].
    exists b. rewrite PC', AT. reflexivity.
  - (* StoreReg *)
    destruct LOWER as [kind [KIND LOWER]].
    destruct (transfer_store_reg_instruction (attr_entails attrs) before base source size offset
      attrs) as [after |] eqn:TRANSFER; [| discriminate].
    injection NEXT as <-.
    destruct (transfer_store_reg_sound attrs (attr_entails attrs) regions image before after
      base source size
      offset kind executed (TLS_State regs [] code_id count memory) CONCRETE
      (conj (conj NO_UNINIT COORDINATES) TRANSFER) KIND LOWER COMPCERT_DEFINED)
      as [[regs' stack' code_id' count' memory'] [STEP POST]].
    pose proof (straight_line_step _ _ _ _ _ _ _ _ _ _ _ STEP) as SHAPE.
    destruct LOWER. destruct SHAPE as [STACK' PC'].
    apply (ADVANCE (next pc) after _ (or_introl eq_refl) STEP); [| exact STACK' | exact POST].
    exists b. rewrite PC', AT. reflexivity.
  - (* LoadImm64 *)
    destruct (transfer_ld_imm64_local (attr_entails attrs) (attr_maps attrs) before dst fresh load)
      as [after |] eqn:TRANSFER; [| discriminate].
    injection NEXT as <-.
    destruct (fresh_name_destination before dst fresh FRESH) as [FRESH_DST [_ _]].
    destruct (transfer_ld_imm64_sound (attr_entails attrs) attrs image regions before after
      (TLS_State regs [] code_id count memory) dst fresh load executed FRESH_DST
      CONCRETE TRANSFER LOWER) as [[regs' stack' code_id' count' memory'] [STEP POST]].
    pose proof (straight_line_step _ _ _ _ _ _ _ _ _ _ _ STEP) as SHAPE.
    destruct LOWER; destruct SHAPE as [STACK' PC'];
      (apply (ADVANCE (next (next pc)) after _ (or_introl eq_refl) STEP);
        [| exact STACK' | exact POST]);
      exists b; rewrite PC', AT; reflexivity.
  - (* Jump *)
    subst executed.
    destruct (transfer_jump_sound attrs image regions before
      (TLS_State regs [] code_id count memory) offset CONCRETE EQ_FIT ORDER_FIT)
      as [after [[regs' stack' code_id' count' memory'] [TRANSFER [STEP POST]]]].
    rewrite TRANSFER in NEXT. injection NEXT as <-.
    destruct (straight_line_step _ _ _ _ _ _ _ _ _ _ _ STEP) as [STACK' PC'].
    apply (ADVANCE (jump_target pc offset) after _ (or_introl eq_refl) STEP);
      [| exact STACK' | exact POST].
    exists b. rewrite PC', AT. reflexivity.
  - (* Branch *)
    set (cond := branch_condition before op dst source) in *.
    destruct (transfer_branch before cond size true) as [taken_edge |] eqn:TAKEN;
      [| discriminate].
    destruct (transfer_branch before cond size false) as [fallthrough_edge |] eqn:FALLTHROUGH;
      [| discriminate].
    injection NEXT as <-.
    destruct COMPCERT_DEFINED as [STATIC DEFINED].
    destruct (branch_progress _ _ _ _ _ regs [] code_id count memory LOWER DEFINED)
      as [state' STEP].
    assert (OPERANDS : branch_operands_defined (facts before) cond = true).
    { unfold transfer_branch in TAKEN.
      destruct (branch_operands_defined (facts before) cond); [reflexivity | discriminate]. }
    destruct (transfer_branch_sound attrs image regions before cond size offset executed regs []
      code_id count memory state' CONCRETE EQ_FIT ORDER_FIT OPERANDS LOWER STATIC STEP)
      as [taken [after [EDGE [POST SHAPE]]]].
    subst state'. destruct taken.
    + rewrite EDGE in TAKEN. injection TAKEN as <-.
      refine (ADVANCE (jump_target pc offset) after _ _ STEP _ eq_refl POST);
        [apply in_or_app; left; now left |].
      exists b. rewrite nextinstr_pc, Pregmap.gss, AT. reflexivity.
    + rewrite EDGE in FALLTHROUGH. injection FALLTHROUGH as <-.
      refine (ADVANCE (next pc) after _ _ STEP _ eq_refl POST);
        [apply in_or_app; right; now left |].
      exists b. rewrite nextinstr_pc, AT. reflexivity.
  - (* Exit *)
    destruct (transfer_return before) eqn:RETURN; [| discriminate].
    subst executed.
    destruct (transfer_return_sound attrs image regions before regs code_id count memory
      CONCRETE RETURN) as [state' [STEP [_ RESULT]]].
    pose proof (exit_step _ _ _ _ _ STEP) as EXIT. subst state'.
    eexists. split; [exists b, pc, Pret; split; [exact AT | split; [exact KERNEL | exact STEP]] |].
    right. cbn [exited]. split; [apply Pregmap.gss | split; [reflexivity |]].
    rewrite Pregmap.gso by discriminate. exact RESULT.
Qed.

Theorem global_soundness : soundness_claim.
Proof.
  intros P entry initial ACCEPTS IR COMPCERT MEMORY VERIFIER INITIAL CONCRETE n.
  induction n as [| n [final [[RUNS DESCRIBED] | [m [LE [RUNS EXITED]]]]]].
  - exists initial. left. split; [constructor | eapply initial_described; eauto].
  - destruct (described_step P entry final ACCEPTS IR COMPCERT MEMORY VERIFIER DESCRIBED)
      as [final' [STEP [DESCRIBED' | EXITED']]].
    + exists final'. left. split; [econstructor; eauto | exact DESCRIBED'].
    + exists final'. right. exists (S n). split; [lia | split; [econstructor; eauto | exact EXITED']].
  - exists final. right. exists m. split; [lia | auto].
Qed.

End Soundness.
