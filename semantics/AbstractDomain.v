From Coq Require Import List ZArith.

Import ListNotations.
Open Scope Z_scope.

(** This file models the data language of [bpf_verifier/core/src/logic].

    The Rust verifier calls a single fact about a value [AbstractState].  We
    call it [value_state] here, reserving [abstract_state] for the verifier
    state: the atoms of Rust's [Invariant], which every transfer transforms. *)

Definition var := nat.
Definition ghost := nat.
Definition frame := nat.
Definition map := nat.
Definition token := nat.
Definition btf_id := nat.
Definition subprog := nat.

Record range := Range { lower : Z; upper : Z }.
Record urange := URange { u_lower : Z; u_upper : Z }.
Record congruence := Congruence { modulus : Z; residue : Z }.

Inductive permission := Read | Write | ReadWrite.
Inductive nullability := MaybeNull | NonNull | Null.

Module RegionClass.
  Local Open Scope nat_scope.
  Definition t := nat. (* Rust's [u8] class-table index. *)
  Definition CTX : t := 0.
  Definition STACK : t := 1.
  Definition MAP : t := 2.
  Definition MAP_VALUE : t := 4.
  Definition MEM : t := 5.
  Definition BTF : t := 8.
  Definition FUNC : t := 10.
  Definition PACKET : t := 12.
  Definition PACKET_META : t := 13.
  Definition PACKET_END : t := 14.
  Definition INSN : t := 18.
End RegionClass.

Module RegionKey.
  Inductive t := None | Frame (id : frame) | Map (id : map)
    | Token (id : token) | Btf (id : btf_id) | Subprog (id : subprog).

  Definition eqb (x y : t) : bool :=
    match x, y with
    | None, None => true
    | Frame x, Frame y | Map x, Map y | Token x, Token y
    | Btf x, Btf y | Subprog x, Subprog y => Nat.eqb x y
    | _, _ => false
    end.

  Lemma eqb_eq : forall x y, eqb x y = true -> x = y.
  Proof.
    destruct x, y; cbn; try discriminate; intros EQ; try reflexivity;
      apply Nat.eqb_eq in EQ; now subst.
  Qed.
End RegionKey.

Module Cells.
  Inductive t := None | UninitByDefault | UnknownByDefault | Shared.
End Cells.

Module KernelAccess.
  Inductive t := Ctx | Socket | SockCommon | TcpSock | XdpSock | BtfId | Arena | Other.
End KernelAccess.

(** Load-relevant projection of Rust's [RegionClassDesc]. Its [name], [kind]
    and [key] fields and other policy fields (ownership, nominal subtyping,
    packet bounds, etc.) are not modeled yet. *)
Record region_class_desc := RegionClassDesc {
  class_cells : Cells.t;
  class_typed_cells : bool;
  class_grows_down : bool;
  class_probe_read : bool;
  class_access : KernelAccess.t;
}.

(** Rows of [verifier/policy/generated.rs::REGION_CLASSES], in index order. *)
Definition REGION_CLASSES : list region_class_desc := [
  RegionClassDesc Cells.Shared          false false false KernelAccess.Ctx; (* CTX *)
  RegionClassDesc Cells.UninitByDefault  false true  false KernelAccess.Other; (* STACK *)
  RegionClassDesc Cells.None            false false false KernelAccess.Other; (* MAP *)
  RegionClassDesc Cells.None            false false false KernelAccess.Other; (* MAP_KEY *)
  RegionClassDesc Cells.Shared          false false false KernelAccess.Other; (* MAP_VALUE *)
  RegionClassDesc Cells.None            false false false KernelAccess.Other; (* MEM *)
  RegionClassDesc Cells.UnknownByDefault false false false KernelAccess.Other; (* RINGBUF *)
  RegionClassDesc Cells.Shared          false false false KernelAccess.Other; (* DYNPTR *)
  RegionClassDesc Cells.Shared          false false true  KernelAccess.BtfId; (* BTF *)
  RegionClassDesc Cells.None            false false false KernelAccess.Socket; (* SOCKET *)
  RegionClassDesc Cells.None            false false false KernelAccess.Other; (* FUNC *)
  RegionClassDesc Cells.Shared          false false false KernelAccess.Arena; (* ARENA *)
  RegionClassDesc Cells.Shared          false false false KernelAccess.Other; (* PACKET *)
  RegionClassDesc Cells.Shared          false false false KernelAccess.Other; (* PACKET_META *)
  RegionClassDesc Cells.None            false false false KernelAccess.Other; (* PACKET_END *)
  RegionClassDesc Cells.UnknownByDefault false false false KernelAccess.Other; (* FLOW_KEYS *)
  RegionClassDesc Cells.UnknownByDefault false false false KernelAccess.Other; (* TP_BUFFER *)
  RegionClassDesc Cells.Shared          false false false KernelAccess.Other; (* BUF *)
  RegionClassDesc Cells.None            false false false KernelAccess.Other; (* INSN *)
  RegionClassDesc Cells.None            false false false KernelAccess.Other; (* DYNPTR_DESC *)
  RegionClassDesc Cells.None            false false false KernelAccess.SockCommon; (* SOCK_COMMON *)
  RegionClassDesc Cells.None            false false false KernelAccess.TcpSock; (* TCP_SOCK *)
  RegionClassDesc Cells.None            false false false KernelAccess.XdpSock (* XDP_SOCK *)
].

Module Region.
  Record t := new { class : RegionClass.t; key : RegionKey.t }.

  Definition opt_btf class (ty : option btf_id) : t :=
    new class (match ty with Some id => RegionKey.Btf id | None => RegionKey.None end).
  Definition ctx ty := opt_btf RegionClass.CTX ty.
  Definition stack id := new RegionClass.STACK (RegionKey.Frame id).
  Definition map id := new RegionClass.MAP (RegionKey.Map id).
  Definition map_value id := new RegionClass.MAP_VALUE (RegionKey.Map id).
  Definition btf ty := opt_btf RegionClass.BTF ty.
  Definition func id := new RegionClass.FUNC (RegionKey.Subprog id).
  Definition insn id := new RegionClass.INSN (RegionKey.Subprog id).
  Definition mem := new RegionClass.MEM RegionKey.None.

  Definition eqb (x y : t) : bool :=
    Nat.eqb (class x) (class y) && RegionKey.eqb (key x) (key y).
  Definition desc (region : t) := nth_error REGION_CLASSES (class region).
  Definition is (region : t) (expected : RegionClass.t) := Nat.eqb (class region) expected.
  Definition frame (region : t) : option frame :=
    match key region with RegionKey.Frame id => Some id | _ => None end.
  Definition btf_type (region : t) : option btf_id :=
    match key region with RegionKey.Btf id => Some id | _ => None end.

  Definition cells (region : t) : option t :=
    match desc region with
    | Some properties =>
        match class_cells properties with
        | Cells.None | Cells.Shared => None
        | _ =>
            if class_typed_cells properties then
              match btf_type region with Some _ => Some region | None => None end
            else Some region
        end
    | None => None
    end.

  Definition grows_down (region : t) : bool :=
    match desc region with Some properties => class_grows_down properties | None => false end.
  Definition uninit_by_default (region : t) : bool :=
    match desc region with
    | Some properties =>
        match class_cells properties with Cells.UninitByDefault => true | _ => false end
    | None => false
    end.
  Definition contents_shared (region : t) : bool :=
    match desc region with
    | Some properties =>
        match class_cells properties with Cells.Shared => true | _ => false end
    | None => false
    end.
  Definition is_packet_family (region : t) : bool :=
    is region RegionClass.PACKET || is region RegionClass.PACKET_META ||
    is region RegionClass.PACKET_END.
  (** Rust's [bounded_by().is_some()]: the packet and packet-meta rows. *)
  Definition is_bounded_by_cmp (region : t) : bool :=
    is region RegionClass.PACKET || is region RegionClass.PACKET_META.
  Definition probe_readable (region : t) : bool :=
    match desc region with Some properties => class_probe_read properties | None => false end.
  Definition kernel_access (region : t) : KernelAccess.t :=
    match desc region with Some properties => class_access properties | None => KernelAccess.Other end.

  Lemma eqb_eq : forall x y, eqb x y = true -> x = y.
  Proof.
    intros [xc xk] [yc yk] EQ. apply Bool.andb_true_iff in EQ as [CLASS KEY].
    apply Nat.eqb_eq in CLASS. apply RegionKey.eqb_eq in KEY.
    cbn in CLASS, KEY. now subst.
  Qed.

  Lemma cells_self : forall source target, cells source = Some target -> target = source.
  Proof.
    intros source target CELL. unfold cells in CELL.
    destruct (desc source) as [properties |]; try discriminate.
    destruct (class_cells properties); try discriminate;
      destruct (class_typed_cells properties);
      try destruct (btf_type source); inversion CELL; reflexivity.
  Qed.

  Lemma probe_readable_access : forall region,
    probe_readable region =
      match kernel_access region with KernelAccess.BtfId => true | _ => false end.
  Proof.
    intros [index key]. unfold probe_readable, kernel_access, desc. cbn [class].
    do 23 (destruct index as [| index]; [reflexivity |]). destruct index; reflexivity.
  Qed.
End Region.

(** Rust [logic/atom/ptr.rs::PtrState]. *)
Record ptr_state := PtrState {
  ptr_ty : Region.t;
  ptr_nullability : nullability;
  ptr_flags : Z;
  ptr_off_min : Z;
  ptr_off_max : Z;
  ptr_size : Z;
  ptr_end_min : option Z;
  ptr_align : Z;
  ptr_permission : permission;
  ptr_ref_obj : option token;
}.

(** Rust [logic/atom/state.rs::AbstractState]. [Scalar] is a value the load
    may disclose: these proofs fix Rust's [PolicyEnv::allow_ptr_leaks] to
    [false], where it is never a pointer. *)
Inductive value_state :=
  | Uninit
  | Unknown
  | Scalar
  | URangeValue (bounds : urange)
  | RangeValue (bounds : range)
  | CongruenceValue (class : congruence)
  | Ptr (state : ptr_state).

(** Rust [logic/term.rs::Term]. *)
Inductive term :=
  | Var (x : var)
  | Ghost (x : ghost)
  | Const (x : Z)
  | AddConst (x : var) (offset : Z)
  | GhostAddConst (x : ghost) (offset : Z)
  | Sub (lhs rhs : var).

(** Rust [logic/atom/resource.rs::Resource]. *)
Module Resource.
  Inductive t :=
    | RingbufReservation (region : Region.t) (size : Z)
    | Dynptr (region : Region.t) (size : Z)
    | RefcountedKptr (region : Region.t) (ty : btf_id).
End Resource.

(** Namespaced constructors keep the Rust names without colliding with terms. *)
Module OpSize.
  Inductive t := Op32 | Op64.
End OpSize.

(** Rust [ir/cfg/inst.rs::FlagOp]. *)
Module FlagOp.
  Inductive t := Sub | Add | And.
End FlagOp.

(** Rust [logic/atom/def.rs::DefOp]. *)
Module DefOp.
  Inductive t :=
    | Add | Sub | AddWrap (size : OpSize.t)
    | And | Or | Xor | Lsh | Rsh | Arsh | Mul | Div | Mod
    | Flags (op : FlagOp.t) (size : OpSize.t).
End DefOp.

Definition def_op := DefOp.t.

Module CmpOp.
  Inductive t := Eq | Ne | UnsignedGt | UnsignedGe | UnsignedLt | UnsignedLe
    | SignedGt | SignedGe | SignedLt | SignedLe | BitSet. (* Rust [Set]. *)
End CmpOp.

(** Rust [logic/atom/guard.rs::Guard]. [guard_rhs] stands for Rust's [u64]. *)
Record guard := Guard {
  guard_var : var;
  guard_op : CmpOp.t;
  guard_rhs : Z;
  guard_size : OpSize.t;
}.

(** Rust [logic/atom/mod.rs::Atom]. [GhostEq] is Rust's [Atom::Ghost], renamed
    because [Ghost] is a term constructor here. *)
Inductive atom :=
  | MemoryCell (region : Region.t) (bytes : range) (value : value_state)
  | MemoryEq (region : Region.t) (offset : Z) (value : var)
  | Owns (token : token) (value : Resource.t)
  | GhostEq (name : ghost) (value : term)
  | AbstractValue (term : term) (value : value_state)
  | Def (dst : var) (op : def_op) (lhs rhs : term)
  | Eq (lhs rhs : term)
  | NeqZero (value : term)
  | Neq (lhs rhs : term)
  | Le (lhs rhs : term) (signed : bool)
  | Lt (lhs rhs : term) (signed : bool)
  | LinearInduction (pointer index : var) (stride base : Z)
  | Guarded (condition : guard) (term : term) (value : value_state)
  | Readable (base : var) (bytes : range)
  | ReadableCell (region : Region.t) (offset : Z) (bytes : range).

Definition abstract_state := list atom.

(** Rust's [policy/memory.rs::WriteWindow]: a writable exception to a
    pointer's own permissions, expressed as region-relative byte offsets. *)
Record write_window := WriteWindow {
  write_region : Region.t;
  write_range : range;
}.

(** Access-relevant projection of Rust's map policy. Special-field offsets
    and sizes represent [u32]; lists represent [SpecialFields::as_slice].
    An absent map spec and one with no special fields both yield []. *)
Record special_field := SpecialField {
  special_field_offset : Z;
  special_field_size : Z;
}.
Definition map_special_fields := map -> list special_field.

(** Projection of Rust's [PolicyEnv] used by [ld_imm64] map loads: whether
    [proof_map_family] resolves the id, and the [value_size] ([u32]) and
    [value_perm] of [map]. Family ids are rejected before [map] is consulted,
    so [map_value_specs] stands for the dynamic map table. *)
Record map_value_spec := MapValueSpec {
  map_value_size : Z;
  map_value_perm : permission;
}.
Record map_policy := MapPolicy {
  map_is_proof_family : map -> bool;
  map_value_specs : map -> option map_value_spec;
}.

(** Rust [verifier/policy/ctx.rs]. Attach-type identities are supplied by the
    selected policy; only equality is used here. The generated per-program
    field table is a policy input, not a verifier invariant. *)
Module CtxGate.
  Inductive t := Never | Always | AttachTypes (types : list nat) | BpfCapable.
End CtxGate.

Record ctx_access := CtxAccess {
  ctx_access_sizes : Z;
  ctx_access_gate : CtxGate.t;
}.

Record ctx_field := CtxField {
  ctx_field_range : range;
  ctx_field_interior : bool;
  ctx_field_read : ctx_access;
  ctx_field_write : ctx_access;
  ctx_field_value : option ptr_state;
}.

Record ctx_policy := CtxPolicy {
  ctx_fields : list ctx_field;
  ctx_expected_attach_type : option nat;
  ctx_bpf_capable : bool;
}.

(** Access-relevant projection of Rust's [PolicyEnv], not proof-generator
    facts. A write grant must come from one covering window. *)
Record store_policy := StorePolicy {
  store_strict_alignment : bool;
  store_write_windows : list write_window;
  store_map_special_fields : map_special_fields;
  store_ctx_policy : ctx_policy;
}.

(** Rust [Perm::includes]. *)
Definition permission_includes (actual required : permission) : bool :=
  match actual, required with
  | ReadWrite, _ | Read, Read | Write, Write => true
  | _, _ => false
  end.

(** The [covers] closure of Rust [write_window_allows]. *)
Definition range_covers (outer inner : range) : bool :=
  (lower outer <=? lower inner) && (upper inner <=? upper outer).

(** Rust [transfer.rs::term_mentions_var]. *)
Definition term_mentions (x : var) (t : term) : bool :=
  match t with
  | Var y | AddConst y _ => Nat.eqb x y
  | Sub y z => Nat.eqb x y || Nat.eqb x z
  | Ghost _ | Const _ | GhostAddConst _ _ => false
  end.

(** Rust [transfer.rs::atom_mentions_var]. *)
Definition atom_mentions (x : var) (a : atom) : bool :=
  match a with
  | AbstractValue t _ | GhostEq _ t | NeqZero t => term_mentions x t
  | MemoryEq _ _ y => Nat.eqb x y
  | Def dst _ lhs rhs => Nat.eqb x dst || term_mentions x lhs || term_mentions x rhs
  | Eq lhs rhs | Neq lhs rhs | Le lhs rhs _ | Lt lhs rhs _ =>
      term_mentions x lhs || term_mentions x rhs
  | LinearInduction p i _ _ => Nat.eqb x p || Nat.eqb x i
  | Guarded condition t _ => Nat.eqb x (guard_var condition) || term_mentions x t
  | Readable base _ => Nat.eqb x base
  | MemoryCell _ _ _ | Owns _ _ | ReadableCell _ _ _ => false
  end.
