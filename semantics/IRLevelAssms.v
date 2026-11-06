From Coq Require Import Bool List ZArith.
From compcert Require Import Integers Values Memory AST Ctypes.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.
From TrustNoBPF.Semantics Require Import AbstractDomain Concretization Transfer.

Import ListNotations.
Open Scope Z_scope.

(** Assumptions bridging the two instruction levels. The Rust verifier checks
    an SSA IR built from the user-level bytecode, while [instruction_step]
    executes the kernel's bytecode after loader and verifier rewrites. Nothing
    here is proved: each definition is a premise that ties an IR instruction,
    or its SSA names, to the executed kernel instruction. *)

(** ** SSA naming

    Kernel registers are reused; IR names are not. These premises state the
    SSA discipline of Rust's [ssa.rs] for the names an instruction defines. *)

Definition fresh_destination (before : abstract_machine_state)
    (dst : ireg) (dst_value : var) : Prop :=
  forall reg, reg <> dst -> register_name before reg <> dst_value.

(** Rust allocates every destination SSA name fresh, so no pre-state fact
    mentions it. [fresh_destination] alone only constrains register names. *)
Definition fresh_in_facts (before : abstract_machine_state) (value : var) : Prop :=
  Forall (fun fact => atom_mentions value fact = false) (facts before).

Definition call_names_distinct (clobbered : ireg -> var) : Prop :=
  forall argument other, In argument [R1; R2; R3; R4; R5] -> In other [R1; R2; R3; R4; R5] ->
    argument <> other -> clobbered argument <> clobbered other.

(** SSA freshness of the names a call defines. *)
Definition call_names_fresh (before : abstract_machine_state) (dst : var)
    (clobbered : ireg -> var) (post : abstract_state) : Prop :=
  call_names_distinct clobbered /\
  forall argument, In argument [R1; R2; R3; R4; R5] ->
    clobbered argument <> dst /\
    Forall (fun fact => atom_mentions (clobbered argument) fact = false) post /\
    forall saved, In saved [R6; R7; R8; R9; R10] ->
      register_name before saved <> clobbered argument /\ register_name before saved <> dst.

(** ** Registers

    IR operands are eBPF registers R0-R10. [RAX] is the semantics' hidden
    auxiliary: no IR instruction names it, and [concretizes] does not relate it. *)

Definition program_register (reg : ireg) : Prop := reg <> RAX.

Definition program_operand (source : ireg + imm) : Prop :=
  match source with inl reg => program_register reg | inr _ => True end.

(** ** Lowering: IR instruction to executed kernel instruction *)

(** *** Loads *)

(** Kernel lowering from a loader-visible [BPF_MEM] load to the instruction
    executed by the concrete semantics.  Other rewrite families remain
    deliberately unmodeled, so no constructor is available for them yet. *)
Inductive lowers_load (size : sizeOp) (dst base : ireg) (offset : Z) :
    KernelAccess.t -> instruction -> Prop :=
  | LowersRegular :
      program_register base ->
      lowers_load size dst base offset KernelAccess.Other
        (Pload size dst base (Ptrofs.repr offset))
  | LowersProbe :
      program_register base ->
      lowers_load size dst base offset KernelAccess.BtfId
        (Pload_probe size dst base (Ptrofs.repr offset)).

(** *** Stores *)

(** Kernel lowering from a loader-visible [BPF_MEM] store. The kernel keeps
    ordinary and [PTR_TO_BTF_ID] stores as they are. It rewrites context and
    socket field writes ([convert_ctx_accesses]) into stores to its own objects,
    and arena stores into [PROBE_MEM32] accesses, which upstream lacks. Neither
    rewrite is modeled, so those kinds have no constructor and their stores no
    theorem. *)
Inductive lowers_store (size : sizeOp) (base : ireg) (source : ireg + imm) (offset : Z) :
    KernelAccess.t -> instruction -> Prop :=
  | LowersStore : forall kind,
      kind = KernelAccess.Other \/ kind = KernelAccess.BtfId ->
      program_register base -> program_operand source ->
      lowers_store size base source offset kind (Pstore size base source (Ptrofs.repr offset)).

(** *** [ld_imm64] *)

(** Kernel lowering of a loader-visible [ld_imm64]. The constant form keeps
    its immediate: [decode_ld] reads [(hi << 32) | (lo as u32)] as [i64].
    Pseudo forms carry the address [loader] resolved for the reference; the
    semantics maps it to a pointer with [cast_i2p]. The fd and index forms
    decode identically. Rust reads a direct value offset as a signed [imm],
    the kernel as a [u32] it requires to be below [value_size], so the
    offsets of accepted programs agree. *)
Inductive lowers_ld_imm64 (loader : loader_image) (dst : ireg) :
    LdImm64.t -> instruction -> Prop :=
  | LowersImm64 : forall lo hi,
      lowers_ld_imm64 loader dst (LdImm64.LoadImm64 (Int64.signed (Int64.ofwords hi lo)))
        (Plddw PSEUDO_Constant dst lo hi)
  | LowersMapFd : forall id ty lo hi,
      ty = PSEUDO_MAP_FD \/ ty = PSEUDO_MAP_IDX ->
      loaded_map loader id = Some (Int64.ofwords hi lo) ->
      lowers_ld_imm64 loader dst (LdImm64.LoadMapFd id) (Plddw ty dst lo hi)
  | LowersMapValue : forall id offset ty lo hi base size,
      ty = PSEUDO_MAP_VALUE \/ ty = PSEUDO_MAP_IDX_VALUE ->
      loaded_map_value loader id = Some (base, size) ->
      0 <= offset < size ->
      Int64.ofwords hi lo = Int64.add base (Int64.repr offset) ->
      lowers_ld_imm64 loader dst (LdImm64.LoadMapValue id offset) (Plddw ty dst lo hi)
  | LowersSubprogAddr : forall id lo hi,
      loaded_subprog loader id = Some (Int64.ofwords hi lo) ->
      lowers_ld_imm64 loader dst (LdImm64.LoadSubprogAddr id) (Plddw PSEUDO_FUNC dst lo hi).

(** *** Conditional branches *)

Definition lower_cmp_op (op : CmpOp.t) : cmpOp :=
  match op with
  | CmpOp.Eq => EQ | CmpOp.Ne => NE | CmpOp.BitSet => SET
  | CmpOp.UnsignedGt => GT Unsigned | CmpOp.UnsignedGe => GE Unsigned
  | CmpOp.UnsignedLt => LT Unsigned | CmpOp.UnsignedLe => LE Unsigned
  | CmpOp.SignedGt => GT Signed | CmpOp.SignedGe => GE Signed
  | CmpOp.SignedLt => LT Signed | CmpOp.SignedLe => LE Signed
  end.

Definition lower_width (size : OpSize.t) : width :=
  match size with OpSize.Op32 => W32 | OpSize.Op64 => W64 end.

(** [decode_jmp]: [BPF_JMP] branches are [Op64], [BPF_JMP32] ones [Op32]. *)
Inductive lowers_branch (names : ireg -> var) (offset : off) :
    condition -> OpSize.t -> instruction -> Prop :=
  | LowersBranchImm : forall op size dst imm,
      program_register dst ->
      lowers_branch names offset (Condition (names dst) (SourceOperand.Imm imm) op) size
        (Pjmpcmp (lower_cmp_op op) (lower_width size) dst (inr imm) offset)
  | LowersBranchReg : forall op size dst src,
      program_register dst -> program_register src ->
      lowers_branch names offset (Condition (names dst) (SourceOperand.Value (names src)) op) size
        (Pjmpcmp (lower_cmp_op op) (lower_width size) dst (inl src) offset).

(** *** Arithmetic *)

(** Signed division and sign-extending moves are absent from Rust's opcode enum.
    END's direction and width are supplied separately in its theorem. *)
Definition arithmetic_opcode (op : ArithmeticOp.t) : option aluOp :=
  match op with
  | ArithmeticOp.Add => Some ADD | ArithmeticOp.Sub => Some SUB
  | ArithmeticOp.Mul => Some MUL | ArithmeticOp.Div => Some DIV
  | ArithmeticOp.Or => Some OR | ArithmeticOp.And => Some AND
  | ArithmeticOp.Lsh => Some LSH | ArithmeticOp.Rsh => Some RSH
  | ArithmeticOp.Neg => Some NEG | ArithmeticOp.Mod => Some MOD
  | ArithmeticOp.Xor => Some XOR | ArithmeticOp.Mov => Some MOV
  | ArithmeticOp.Arsh => Some ARSH | ArithmeticOp.End => None
  end.

(** The ISA's arithmetic is in-place while the IR names a separate [lhs]:
    except for a move, [lhs] must be the old architectural destination. *)
Definition arithmetic_in_place (op : ArithmeticOp.t) (lhs : option ireg) (dst : ireg) : Prop :=
  (op = ArithmeticOp.Mov /\ lhs = None) \/ lhs = Some dst.

(** The kernel keeps an ALU instruction as it is. Rust's [End] carries the swap
    width as its immediate but not the direction. *)
Definition lowers_arithmetic (size : OpSize.t) (op : ArithmeticOp.t) (dst : ireg)
    (source : ireg + imm) (executed : instruction) : Prop :=
  match arithmetic_opcode op with
  | Some opcode => executed = Palu opcode (lower_width size) dst source
  | None => exists direction width,
      source = inr (Int.repr (match width with S16 => 16 | S32 => 32 | S64 => 64 end)) /\
      executed = Palu (END direction width) (lower_width size) dst source
  end.
