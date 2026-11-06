From Coq Require Import ZArith.
From compcert Require Import Values Memory.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.
From TrustNoBPF.Semantics Require Import AbstractDomain Concretization Transfer.

Open Scope Z_scope.

(** Premises about the kernel memory a program reads, which concretization
    does not describe. *)

(** * Loads *)

(** With pointer leaks forbidden, Rust's [transfer.rs::loaded_scalar] reads a
    full-width load from memory outside the stack as a scalar unless its
    pointer is probe-readable: only the stack keeps a pointer the program
    stored ([transfer.rs::transfer_store_reg] rejects storing an undisclosable
    value elsewhere), and the kernel keeps no address the program may load as a
    value in other memory. A pointer-typed context field is read as its
    pointer instead, so context loads are excluded. *)
Definition load_outside_stack_scalar (before : abstract_machine_state)
    (concrete : tls_state) (base : ireg) (size : sizeOp) (offset : Z) : Prop :=
  match concrete with
  | TLS_State regs _ _ _ memory =>
      forall ptr loaded,
        find_pointer_fact (facts before) (register_name before base) = Some ptr ->
        Region.frame (ptr_ty ptr) = None ->
        Region.probe_readable (ptr_ty ptr) = false ->
        Region.is (ptr_ty ptr) RegionClass.CTX = false ->
        size = DBWord ->
        load_at_offset memory (regs base) offset size = Some loaded ->
        forall b o, loaded <> Vptr b o
  end.
