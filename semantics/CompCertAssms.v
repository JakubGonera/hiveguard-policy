From Coq Require Import Bool List ZArith.
From compcert Require Import Integers Values Memory Memdata AST Coqlib.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.
From TrustNoBPF.Semantics Require Import AbstractDomain Concretization Transfer ArithmeticHelpers.

Open Scope Z_scope.

(** Extra premisses used in soundness theorems resulting from small-step
    semantics using CompCert memory model which right now has a stronger
    memory model than the one used in the verifier. *)

(** * Loads *)

(** Initialized bytes still decode to [Vundef] when they are fragments of a
    stored pointer read partially or out of order, where the hardware reads the
    pointer's bytes. *)
Definition load_fragments_defined (concrete : tls_state) (base : ireg)
    (size : sizeOp) (offset : Z) : Prop :=
  match concrete with
  | TLS_State regs _ _ _ memory =>
      forall loaded,
        load_at_offset memory (regs base) offset size = Some loaded ->
        initialized_bytes memory (Val.offset_ptr (regs base) (Ptrofs.repr offset))
          (load_width size) ->
        load_value_casting loaded <> Vundef
  end.

(** Loads whose bytes are known to be initialized: from a stack frame through
    Rust's cell coverage, and from every other region except untyped BTF
    through [regions_initialized]. *)
Definition load_initialization_modeled (ptr : ptr_state) : bool :=
  if Region.uninit_by_default (ptr_ty ptr) then
    match Region.frame (ptr_ty ptr) with
    | Some frame => Region.eqb (ptr_ty ptr) (Region.stack frame)
    | None => false
    end
  else negb (Region.eqb (ptr_ty ptr) (Region.btf None)).

(** Untyped BTF pointers are not modelled in concretizes as initialized memory
    regions, yet they need to yield initialized values when loading. Here we
    make this assumption. *)
Definition load_initialized_if_unmodeled (before : abstract_machine_state)
    (concrete : tls_state) (base : ireg) (size : sizeOp) (offset : Z) : Prop :=
  match concrete with
  | TLS_State regs _ _ _ memory =>
      forall ptr loaded,
        find_pointer_fact (facts before) (register_name before base) = Some ptr ->
        load_initialization_modeled ptr = false ->
        load_at_offset memory (regs base) offset size = Some loaded ->
        initialized_bytes memory (Val.offset_ptr (regs base) (Ptrofs.repr offset))
          (load_width size)
  end.

(** * Arithmetic operands *)

(** An integer ALU operation on a CompCert pointer can return [Vundef], whereas
    the transfer havocs its result to [Unknown] (a runtime value). The scalar
    premise excludes that unresolved pointer case. *)
Definition scalar_source (regs : regset) (source : ireg + int) : Prop :=
  match source with inl reg => exists n, regs reg = Vlong n | inr _ => True end.

(** The integer conditions of the ALU theorems: every operand CompCert would
    read as a pointer in an integer-only operation is an integer. Upstream's
    32-bit [END] reads only the low word, so a 64-bit swap there is excluded
    too. *)
Definition alu_integer_operands (before : abstract_machine_state) (regs : regset)
    (size : OpSize.t) (dst : ireg) (source : ireg + int) (op : ArithmeticOp.t) : Prop :=
  let dst_integer := exists a, regs dst = Vlong a in
  match op, source, size with
  | ArithmeticOp.Mov, inl src, OpSize.Op32 =>
      ArithmeticHelpers.fits_u32 (facts before) (register_name before src) = false ->
      exists a, regs src = Vlong a
  | ArithmeticOp.Mov, _, _ => True
  | (ArithmeticOp.Add | ArithmeticOp.Sub), inr _, OpSize.Op64 => True
  | ArithmeticOp.Add, inl src, OpSize.Op64 => dst_integer \/ exists b, regs src = Vlong b
  | ArithmeticOp.Sub, inl src, OpSize.Op64 => runtime_value (Val.subl (regs dst) (regs src))
  | (ArithmeticOp.Lsh | ArithmeticOp.Rsh), inr _, OpSize.Op64 => dst_integer
  | ArithmeticOp.Neg, _, OpSize.Op64 => dst_integer
  | ArithmeticOp.End, _, _ => dst_integer /\ (size = OpSize.Op32 -> source <> inr (Int.repr 64))
  | _, _, _ => dst_integer /\ scalar_source regs source
  end.

(** * Stores *)

(** CompCert encodes a narrow store of a pointer as [Undef] bytes, where the
    hardware writes the low bytes of the address. *)
Definition narrow_store_integer (regs : regset) (size : sizeOp) (source : ireg) : Prop :=
  size <> DBWord -> exists n, regs source = Vlong n.

(** * Conditional branches *)

(** [eval_cmp_static] decides a branch without reading its operands; CompCert
    comparisons of pointers are partial, while the kernel compares raw
    addresses. A statically decided branch must therefore compare a scalar; a
    register source is then the same register. *)
Definition static_operands_scalar (regs : regset) (instruction : instruction) : Prop :=
  match instruction with
  | Pjmpcmp op w r source _ =>
      eval_cmp_static op w r source <> None -> exists n, regs r = Vlong n
  | _ => True
  end.

(** CompCert compares pointers only in some cases: never at 32 bits or signed,
    against an immediate only as a null check of a weakly valid pointer, and
    against each other only within one block (both weakly valid) or for
    equality of valid pointers. The kernel compares raw addresses. *)
Definition comparison_defined (regs : regset) (memory : mem) (instruction : instruction) : Prop :=
  match instruction with
  | Pjmpcmp op w r source _ =>
      eval_cmp_static op w r source = None ->
      match w with
      | W32 => eval_cmp32 op regs memory r source
      | W64 => eval_cmp64 op regs memory r source
      end <> None
  | _ => True
  end.
