From Coq Require Import Bool List ZArith.
From compcert Require Import Integers Values Memory Memdata Maps AST.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.
From TrustNoBPF.Semantics Require Import AbstractDomain.

Open Scope Z_scope.

(** The verifier's facts and the SSA name currently assigned to each register. *)
Record abstract_machine_state := AbstractMachineState {
  facts : abstract_state;
  register_name : ireg -> var;
}.

(** Supplies concrete values for the names in verifier facts and concrete
    addresses for their regions. [concretizes] requires that some such assignment
    agrees with the current registers and makes all facts hold in current memory.
    Names absent from registers still receive values; this records no execution history. *)
Record interpretation := Interpretation {
  (** Concrete value assigned to each SSA variable. *)
  variable_value : var -> val;
  (** Concrete value assigned to each proof-only ghost variable. *)
  ghost_value : ghost -> val;
  (** [Some (block, origin)] locates a region's offset zero in CompCert memory;
      [None] makes [region_address] return zero. This table alone grants no
      allocation, permissions or initialization. Only regions with cells use
      it: Rust keys their facts by region, and each such region (a stack frame,
      a ringbuf reservation, ...) describes one object. *)
  region_location : Region.t -> option (block * Z);
  (** The allocations a region without cells may denote: a block and the
      offset of the allocation's start. A region may denote several, e.g. every
      element of a hash map is a [Region.map_value] of that map, and every
      kernel object of a BTF type is a [Region.btf] of that type. This table
      alone grants no permissions or initialization. *)
  region_allocation : Region.t -> block -> Z -> Prop;
}.

(** Memory information available to pointer metadata: which block identifiers
    have been allocated and their current/maximal permissions. Object contents
    are interpreted by memory facts, not by nominal pointer metadata. *)
Record allocation_metadata := AllocationMetadata {
  allocation_nextblock : block;
  allocation_permissions : PMap.t (Z -> Memtype.perm_kind -> option Memtype.permission);
}.

Definition allocation_metadata_of (memory : mem) : allocation_metadata :=
  AllocationMetadata (Mem.nextblock memory) (Mem.mem_access memory).

(** Missing requirements, with no definitions or proof rules supplied.
    Declaring a predicate does not assert that it holds. Proofs cannot use it to
    obtain the intended memory/type properties; unchanged premises can still be
    carried through. These placeholders are neither [True] nor [False]. *)
Module Unimplemented.
  (** The table of concrete block/origin pairs assigned to abstract regions. *)
  Definition locations := Region.t -> option (block * Z).

  (** TODO(concretization): whether this token owns the described resource.
      Ownership is a lifetime/identity claim, not a claim about its bytes.
      Ordinary stores preserve the allocation metadata supplied here; freeing
      or releasing a resource still needs a separate interpretation. *)
  Parameter owns : locations -> allocation_metadata -> token -> Resource.t -> Prop.
  (** TODO(concretization): whether the pointer's region-relative offset equals
      [base + stride * index], as claimed by Rust's [LinearInduction] fact. *)
  Parameter linear_induction : locations -> val -> val -> Z -> Z -> Prop.
  (** TODO(concretization): whether [dst] describes the condition flags produced
      by the specified operation on [lhs] and [rhs]. *)
  Parameter flags : FlagOp.t -> OpSize.t -> val -> val -> val -> Prop.
End Unimplemented.

Definition pointer_fields_well_formed (abstract_ptr : ptr_state) : Prop :=
  (* [off_min], [off_max]: i64. *)
  Int64.min_signed <= ptr_off_min abstract_ptr <= Int64.max_signed /\
  Int64.min_signed <= ptr_off_max abstract_ptr <= Int64.max_signed /\
  (* [size], [align]: u64; [flags]: u32. *)
  0 <= ptr_size abstract_ptr < Int64.modulus /\
  0 <= ptr_align abstract_ptr < Int64.modulus /\
  0 <= ptr_flags abstract_ptr < Int.modulus /\
  (* [end_min]: Option<i64>. *)
  match ptr_end_min abstract_ptr with
  | Some bound => Int64.min_signed <= bound <= Int64.max_signed
  | None => True
  end.

(** Number of bytes read by a load of this size: 1, 2, 4 or 8. *)
Definition load_width (size : sizeOp) : Z :=
  match size with Byte => 1 | HalfWord => 2 | Word => 4 | DBWord => 8 end.

(** At the level of abstract facts we only reason about pointers and int64.
    If the memory contains floats or int32 we load the bytes and cast them. *)
Inductive runtime_value : val -> Prop :=
  | RuntimeLong : forall n, runtime_value (Vlong n)
  | RuntimePointer : forall b ofs, runtime_value (Vptr b ofs).

Definition region_address (world : interpretation) (region : Region.t)
    (offset : Z) : val :=
  match region_location world region with
  | Some (b, origin) => Vptr b (Ptrofs.repr (origin + offset))
  | None => Vlong Int64.zero
  end.

(** A region's byte range [bytes] is one interval of its block: it starts at
    [region_address], computed modulo 2^64 as [Val.offset_ptr] does, and ends
    within the block's offset range. *)
Definition region_bytes_addressable (world : interpretation) (region : Region.t)
    (bytes : range) : Prop :=
  match region_address world region (lower bytes) with
  | Vptr _ start => Ptrofs.unsigned start + (upper bytes - lower bytes) <= Ptrofs.modulus
  | _ => False
  end.

(** The object a region denotes: its location if it has cells, otherwise any of
    its allocations. *)
Definition region_object (world : interpretation) (region : Region.t)
    (b : block) (origin : Z) : Prop :=
  match Region.cells region with
  | Some _ => region_location world region = Some (b, origin)
  | None => region_allocation world region b origin
  end.

(** A policy write window makes its interval of every object of its region an
    addressable interval with current CompCert write permission. It grants no
    facts about the bytes' contents or initialization. Probe-readable (BTF)
    pointers may be bare kernel addresses, which no object relation covers, so
    no environment backs a window on such a region. *)
Definition write_window_holds (world : interpretation) (memory : mem)
    (window : write_window) : Prop :=
  let bytes := write_range window in
  lower bytes <= upper bytes /\
  Region.probe_readable (write_region window) = false /\
  forall b origin, region_object world (write_region window) b origin ->
    let start := Ptrofs.unsigned (Ptrofs.repr (origin + lower bytes)) in
    start + (upper bytes - lower bytes) <= Ptrofs.modulus /\
    Mem.range_perm memory b start (start + (upper bytes - lower bytes)) Cur Writable.

(** The environment really supplies every writable range listed by policy.
    Strict alignment is a transfer check, not a memory permission. *)
Definition store_policy_holds (world : interpretation) (memory : mem)
    (policy : store_policy) : Prop :=
  List.Forall (write_window_holds world memory) (store_write_windows policy).

Definition initialized_byte (entry : memval) : Prop :=
  match entry with
  | Undef => False
  | Memdata.Byte _ => True
  | Fragment value _ _ => value <> Vundef
  end.

(** Rust's [value_size] is a [u32]. Every allocation of a map's values backs
    that many bytes with the policy's permission, within one block's offset
    range. *)
Definition map_values_hold (world : interpretation) (memory : mem)
    (maps : map_policy) : Prop :=
  forall id spec, map_value_specs maps id = Some spec ->
    0 <= map_value_size spec <= Int.max_unsigned /\
    forall b origin, region_allocation world (Region.map_value id) b origin ->
      0 <= origin /\ origin + map_value_size spec <= Ptrofs.modulus /\
      Mem.range_perm memory b origin (origin + map_value_size spec) Cur
        (match map_value_perm spec with Read => Memtype.Readable | _ => Writable end).

Definition block_initialized (memory : mem) (b : block) : Prop :=
  forall position, Mem.perm memory b position Cur Memtype.Readable ->
    initialized_byte (ZMap.get position (PMap.get b (Mem.mem_contents memory))).

(** Only the BPF stack holds memory the program has not written: every other
    region's block has defined bytes wherever it is readable. Rust reads such
    memory without initialization evidence. *)
Definition regions_initialized (world : interpretation) (memory : mem) : Prop :=
  (forall region b origin,
    Region.uninit_by_default region = false ->
    region_location world region = Some (b, origin) -> block_initialized memory b) /\
  (forall region b origin,
    Region.uninit_by_default region = false ->
    region_allocation world region b origin -> block_initialized memory b).

(** The kernel's load-time resolution of pseudo [ld_imm64] immediates.
    [resolve_pseudo_ldimm64] writes a map's address, or the start of a map's
    direct value area ([map_direct_value_addr]) plus the instruction's offset,
    which it requires to be below [value_size]. The JIT writes subprogram
    addresses. *)
Record loader_image := LoaderImage {
  loaded_map : map -> option int64;
  loaded_map_value : map -> option (int64 * Z);
  loaded_subprog : subprog -> option int64;
}.

(** Resolved addresses denote allocations of the regions Rust assigns to them,
    through the semantics' integer-to-pointer table. *)
Definition loader_consistent (world : interpretation) (regions : list addr_region)
    (loader : loader_image) : Prop :=
  (forall id address, loaded_map loader id = Some address ->
     exists b origin, region_allocation world (Region.map id) b origin /\
       cast_i2p address regions = Some (Vptr b (Ptrofs.repr origin))) /\
  (forall id address size, loaded_map_value loader id = Some (address, size) ->
     exists b origin, region_allocation world (Region.map_value id) b origin /\
       (* The kernel's [value_size] is a [u32]. *)
       0 <= size <= Int.max_unsigned /\
       forall offset, 0 <= offset < size ->
         cast_i2p (Int64.add address (Int64.repr offset)) regions =
           Some (Vptr b (Ptrofs.repr (origin + offset)))) /\
  (forall id address, loaded_subprog loader id = Some address ->
     exists b origin, region_allocation world (Region.func id) b origin /\
       cast_i2p address regions = Some (Vptr b (Ptrofs.repr origin))).

(** The program's load attributes: what the kernel fixes when it loads the
    program (the hook's ctx fields and write grants, the maps it uses, the
    alignment mode), projected from Rust's [PolicyEnv] for a bytecode load
    without [allow_ptr_leaks], and the loader's resolution of the program's
    pseudo immediates. [attr_entails] is Rust's [entail.rs::abstract_state_entails]
    under that policy; only [meet::fold] consults it, and keeps one of the two
    facts it compares whatever it decides. *)
Record load_attrs := LoadAttrs {
  attr_stores :> store_policy;
  attr_maps : map_policy;
  attr_loader : loader_image;
  attr_entails : value_state -> value_state -> bool;
}.

(** The guarantees about memory that every instruction, and every callee,
    must keep. *)
Definition memory_environment_holds (world : interpretation) (memory : mem)
    (attrs : load_attrs) : Prop :=
  map_values_hold world memory (attr_maps attrs) /\ regions_initialized world memory.

Definition environment_holds (world : interpretation) (memory : mem)
    (attrs : load_attrs) (regions : list addr_region) : Prop :=
  memory_environment_holds world memory attrs /\
  loader_consistent world regions (attr_loader attrs).

Definition pointer_offset_holds (abstract_ptr : ptr_state) (offset : Z) : Prop :=
  ptr_off_min abstract_ptr <= offset <= ptr_off_max abstract_ptr /\
  (* Rust's [align] is an offset stride anchored at [off_min], not a claim
     that the concrete address itself is a multiple of [align]. *)
  exists steps, offset = ptr_off_min abstract_ptr + ptr_align abstract_ptr * steps.

Definition pointer_address (world : interpretation) (abstract_ptr : ptr_state)
    (concrete_ptr : val) : Prop :=
  match Region.cells (ptr_ty abstract_ptr) with
  | Some region =>
      exists offset,
        pointer_offset_holds abstract_ptr offset /\
        concrete_ptr = region_address world region offset
  | None =>
      (* Untyped [Region.btf None] bypasses this address relation. *)
      exists b origin offset,
        region_allocation world (ptr_ty abstract_ptr) b origin /\
        pointer_offset_holds abstract_ptr offset /\
        concrete_ptr = Vptr b (Ptrofs.repr (origin + offset))
  end.

(** verified_window checks if we definitely can fit a block at offset with size 
    of width in the allocation described by abstract_ptr. *)
Definition verified_window (abstract_ptr : ptr_state) (offset width : Z) : Prop :=
  let valid := if Region.grows_down (ptr_ty abstract_ptr)
               then Range (- ptr_size abstract_ptr) 0
               else Range 0 (ptr_size abstract_ptr) in
  lower valid <= ptr_off_min abstract_ptr + offset /\
  (ptr_off_max abstract_ptr + offset + width <= upper valid \/
   exists bound, ptr_end_min abstract_ptr = Some bound /\ offset + width <= bound).

(** Check if the concrete memory has the same permissions as described by abstract_ptr *)
Definition pointer_access_holds (memory : mem) (abstract_ptr : ptr_state)
    (concrete_ptr : val) : Prop :=
  match concrete_ptr with
  | Vptr b address =>
      forall offset width,
        0 < width -> verified_window abstract_ptr offset width ->
        (* The access address, computed modulo 2^64 as [Val.offset_ptr] does. *)
        let start := Ptrofs.unsigned (Ptrofs.add address (Ptrofs.repr offset)) in
        start + width <= Ptrofs.modulus /\
        Mem.range_perm memory b start (start + width) Cur
          (match ptr_permission abstract_ptr with Read => Memtype.Readable | _ => Writable end)
  | _ => concrete_ptr = Vlong Int64.zero
  end.

Definition load_at_offset (memory : mem) (base : val) (offset : Z)
    (size : sizeOp) : option val :=
  load size (Val.offset_ptr base (Ptrofs.repr offset)) memory.

(** Nullability describes the base before its offset.
    TODO(concretization): check compatibility with Rust's non-null refinements
    and zero-scalar entailment in [lemma.rs], [check.rs] and [entail.rs]. *)
Definition null_base_pointer_holds (abstract_ptr : ptr_state) (concrete_ptr : val) : Prop :=
  exists offset, pointer_offset_holds abstract_ptr offset /\
    concrete_ptr = Vlong (Int64.repr offset).

(** Numerical addresses are allowed only for read-only probe access. *)
Definition non_null_base_pointer_holds (abstract_ptr : ptr_state) (concrete_ptr : val) : Prop :=
  match concrete_ptr with
  | Vptr _ _ => True
  | Vlong address =>
      Region.probe_readable (ptr_ty abstract_ptr) = true /\
      permission_includes (ptr_permission abstract_ptr) Write = false /\
      exists offset, pointer_offset_holds abstract_ptr offset /\
        Int64.sub address (Int64.repr offset) <> Int64.zero
  | _ => False
  end.

Definition pointer_region_holds (world : interpretation)
    (abstract_ptr : ptr_state) (concrete_ptr : val) : Prop :=
  (* Only an untyped BTF pointer names no object: any probe-read address. Rust
     describes every such pointer as read-only; a writable one could reach any
     object, which no fact about other regions survives. *)
  let address_holds := if Region.eqb (ptr_ty abstract_ptr) (Region.btf None)
    then permission_includes (ptr_permission abstract_ptr) Write = false
    else pointer_address world abstract_ptr concrete_ptr in
  match ptr_nullability abstract_ptr with
  | Null => True
  | MaybeNull => null_base_pointer_holds abstract_ptr concrete_ptr \/ address_holds
  | NonNull => address_holds
  end.

Definition pointer_permissions_holds (world : interpretation) (memory : mem)
    (abstract_ptr : ptr_state) (concrete_ptr : val) : Prop :=
  let access_holds := if Region.probe_readable (ptr_ty abstract_ptr) then
    permission_includes (ptr_permission abstract_ptr) Write = true ->
    pointer_access_holds memory abstract_ptr concrete_ptr
  else pointer_access_holds memory abstract_ptr concrete_ptr in
  match ptr_nullability abstract_ptr with
  | Null => True
  | MaybeNull => null_base_pointer_holds abstract_ptr concrete_ptr \/ access_holds
  | NonNull => access_holds
  end.

Definition pointer_nullability_holds
    (abstract_ptr : ptr_state) (concrete_ptr : val) : Prop :=
  match ptr_nullability abstract_ptr with
  | Null => null_base_pointer_holds abstract_ptr concrete_ptr
  | MaybeNull => null_base_pointer_holds abstract_ptr concrete_ptr \/
      non_null_base_pointer_holds abstract_ptr concrete_ptr
  | NonNull => non_null_base_pointer_holds abstract_ptr concrete_ptr
  end.

(** [flags] and [ref_obj] have no counterpart in the semantics' registers or
    memory: only helper and kfunc contracts, which are assumed rather than
    verified, observe them. They therefore add no requirement here; the
    kernel-side properties they name are not covered by these proofs. *)
Definition pointer_state_holds (world : interpretation) (memory : mem)
    (abstract_ptr : ptr_state) (concrete_ptr : val) : Prop :=
  (* Numeric representation widths. *)
  pointer_fields_well_formed abstract_ptr /\
  (* [ty], [off_min], [off_max], [align]: region/address link. *)
  pointer_region_holds world abstract_ptr concrete_ptr /\
  (* [perm], [off_min], [off_max], [size], [end_min]: access rights/bounds. *)
  pointer_permissions_holds world memory abstract_ptr concrete_ptr /\
  (* [nullable]: base nullness. *)
  pointer_nullability_holds abstract_ptr concrete_ptr /\
  (* The register value is defined; no claim about values stored behind it. *)
  runtime_value concrete_ptr.

Definition value_holds (world : interpretation) (memory : mem)
    (abstract : value_state) (concrete : val) : Prop :=
  match abstract with
  | Uninit => True
  (* A 64-bit integer or pointer, with no further guarantees. *)
  | Unknown => runtime_value concrete
  (* Never a pointer: the load forbids pointer leaks. *)
  | Scalar => exists n, concrete = Vlong n
  | URangeValue bounds =>
      match concrete with
      | Vlong n => u_lower bounds <= Int64.unsigned n <= u_upper bounds
      | _ => False
      end
  | RangeValue bounds =>
      match concrete with
      | Vlong n => lower bounds <= Int64.signed n <= upper bounds
      | _ => False
      end
  | CongruenceValue class =>
      (* Strides abstraction. Rust still needs a fix with overflowing modulus
         when normalizing the residue. *)
      match concrete with
      | Vlong n =>
          if Z.eqb (modulus class) 0 then Int64.signed n = residue class
          else 0 < modulus class /\
               Int64.signed n mod modulus class = residue class mod modulus class
      | _ => False
      end
  | Ptr ptr => pointer_state_holds world memory ptr concrete
  end.

(** Protected reads return zero on failure. *)
Definition cell_result_holds (world : interpretation) (memory : mem)
    (region : Region.t) (abstract : value_state) (result : option val) : Prop :=
  match result with
  | Some loaded => value_holds world memory abstract (load_value_casting loaded)
  | None =>
      if Region.probe_readable region
      then value_holds world memory abstract (Vlong Int64.zero) else False
  end.

(** Parts of pointers in memory also count as initialized, even though incomplete
    read of a pointer will not satisfy even the Unknown fact about this memory as
    CompCert memory model defines this to be Vundef. *)

(** Initialization applies to the entire byte interval, of any length. *)
Definition initialized_bytes (memory : mem) (address : val) (length : Z) : Prop :=
  match address with
  | Vptr b offset =>
      exists contents,
        Mem.loadbytes memory b (Ptrofs.unsigned offset) length = Some contents /\
        Forall initialized_byte contents
  | _ => False
  end.

(** No byte is part of a stored pointer. *)
Definition pointer_free_byte (entry : memval) : Prop :=
  match entry with
  | Fragment (Vptr _ _) _ _ => False
  | _ => True
  end.

Definition pointer_free_bytes (memory : mem) (address : val) (length : Z) : Prop :=
  match address with
  | Vptr b offset =>
      exists contents,
        Mem.loadbytes memory b (Ptrofs.unsigned offset) length = Some contents /\
        Forall pointer_free_byte contents
  | _ => False
  end.

(** TODO(concretization): integer addresses resolved through [addr_map] are not
    represented by this pointer-only definition. *)
Definition initialized_readable_window (memory : mem) (base : val) (bytes : range) : Prop :=
  lower bytes < upper bytes /\
  match base with
  | Vptr _ address =>
      (* The window start, computed modulo 2^64 as [Val.offset_ptr] does. *)
      Ptrofs.unsigned (Ptrofs.add address (Ptrofs.repr (lower bytes))) +
        (upper bytes - lower bytes) <= Ptrofs.modulus /\
      initialized_bytes memory (Val.offset_ptr base (Ptrofs.repr (lower bytes)))
        (upper bytes - lower bytes)
  | _ => False
  end.

(** DONE *)
Definition stack_cell_points_to_window (world : interpretation) (memory : mem)
    (region : Region.t) (offset : Z) (bytes : range) : Prop :=
  Region.is region RegionClass.STACK = true /\
  exists loaded,
    load DBWord (region_address world region offset) memory = Some loaded /\
    initialized_readable_window memory (load_value_casting loaded) bytes.

Definition cell_value_holds (world : interpretation) (memory : mem)
    (region : Region.t) (bytes : range) (abstract : value_state) : Prop :=
  match abstract with
  | Uninit | Unknown => True
  (* Any width: the remainder of a partly overwritten cell keeps [Scalar]. *)
  | Scalar =>
      pointer_free_bytes memory (region_address world region (lower bytes))
        (upper bytes - lower bytes)
  | _ =>
      exists size,
        load_width size = upper bytes - lower bytes /\
        cell_result_holds world memory region abstract
          (load size (region_address world region (lower bytes)) memory)
  end.

Definition cell_holds (world : interpretation) (memory : mem)
    (region : Region.t) (bytes : range) (abstract : value_state) : Prop :=
  match abstract with
  | Uninit => True
  (* Rust entails an Unknown cell without evidence outside stack-like regions.
     There it adds no initialization or access claim to the relation. *)
  | Unknown =>
      if Region.uninit_by_default region then
        lower bytes <= upper bytes /\
        region_bytes_addressable world region bytes /\
        initialized_bytes memory (region_address world region (lower bytes))
          (upper bytes - lower bytes)
      else True
  | _ =>
      lower bytes <= upper bytes /\
      region_bytes_addressable world region bytes /\
      initialized_bytes memory (region_address world region (lower bytes))
        (upper bytes - lower bytes) /\
      cell_value_holds world memory region bytes abstract
  end.

(** The eight bytes at [address] decode to [value]. Inspecting the stored
    contents grants neither initialization nor permission to load them. *)
Definition memory_eq_holds (memory : mem) (address value : val) : Prop :=
  match address with
  | Vptr b offset =>
      load_value_casting (decode_val Mint64
        (Mem.getN 8 (Ptrofs.unsigned offset) (PMap.get b (Mem.mem_contents memory)))) = value
  | _ => False
  end.

Definition eval_term (world : interpretation) (expression : term) : val :=
  match expression with
  | Var x => variable_value world x
  | Ghost x => ghost_value world x
  | Const n => Vlong (Int64.repr n)
  | AddConst x offset => Val.addl (variable_value world x) (Vlong (Int64.repr offset))
  | GhostAddConst x offset => Val.addl (ghost_value world x) (Vlong (Int64.repr offset))
  | Sub lhs rhs => Val.subl (variable_value world lhs) (variable_value world rhs)
  end.


(** [Def] fact describes a symbolic relation built with a binary operator. Here
    we check if these hold with the concrete values.
    TODO(concretization): [Flags] has no implemented meaning in this eBPF model. *)
Definition definition_holds (op : def_op) (dst lhs rhs : val) : Prop :=
  match op with
  | DefOp.Flags flag_op size => Unimplemented.flags flag_op size dst lhs rhs
  | _ =>
      match dst, lhs, rhs with
      | Vlong d, Vlong l, Vlong r =>
          match op with
          | DefOp.Add => Int64.unsigned d = Int64.unsigned l + Int64.unsigned r
          | DefOp.Sub => Int64.unsigned d = Int64.unsigned l - Int64.unsigned r
          | DefOp.AddWrap OpSize.Op32 => dst = eval_alu32 ADD lhs (inl rhs)
          | DefOp.AddWrap OpSize.Op64 => dst = eval_alu64 ADD lhs (inl rhs)
          | DefOp.And => dst = eval_alu64 AND lhs (inl rhs)
          | DefOp.Or => dst = eval_alu64 OR lhs (inl rhs)
          | DefOp.Xor => dst = eval_alu64 XOR lhs (inl rhs)
          | DefOp.Lsh => dst = eval_alu64 LSH lhs (inl rhs)
          | DefOp.Rsh => dst = eval_alu64 RSH lhs (inl rhs)
          | DefOp.Arsh => dst = eval_alu64 ARSH lhs (inl rhs)
          | DefOp.Mul => dst = eval_alu64 MUL lhs (inl rhs)
          | DefOp.Div => dst = eval_alu64 DIV lhs (inl rhs)
          | DefOp.Mod => dst = eval_alu64 MOD lhs (inl rhs)
          | DefOp.Flags flag_op size => Unimplemented.flags flag_op size dst lhs rhs
          end
      | _, _, _ => False
      end
  end.

Definition comparison_is_true (memory : mem) (signed : bool) (op : comparison)
    (lhs rhs : val) : Prop :=
  (if signed then Val.cmpl_bool op lhs rhs
   else Val.cmplu_bool (Mem.valid_pointer memory) op lhs rhs) = Some true.

(** Requires the guard's test on [value] and its constant to return [Some true].
    The guard selects signed/unsigned comparison or a nonzero bitwise-AND test.
    A 32-bit guard uses only the low 32 bits of BOTH operands. False or undefined
    tests do not satisfy this predicate; unsigned pointer comparisons use
    CompCert's memory-validity rules. *)
Definition guard_is_true (memory : mem) (condition : guard) (value : val) : Prop :=
  let narrow := match guard_size condition with
                | OpSize.Op32 => Val.loword | OpSize.Op64 => fun v => v end in
  let lhs := narrow value in
  let rhs := narrow (Vlong (Int64.repr (guard_rhs condition))) in
  let unsigned_cmp := match guard_size condition with
    | OpSize.Op32 => Val.cmpu_bool (Mem.valid_pointer memory)
    | OpSize.Op64 => Val.cmplu_bool (Mem.valid_pointer memory) end in
  let signed_cmp := match guard_size condition with
    | OpSize.Op32 => Val.cmp_bool | OpSize.Op64 => Val.cmpl_bool end in
  match guard_op condition with
  | CmpOp.Eq => unsigned_cmp Ceq lhs rhs
  | CmpOp.Ne => unsigned_cmp Cne lhs rhs
  | CmpOp.UnsignedGt => unsigned_cmp Cgt lhs rhs
  | CmpOp.UnsignedGe => unsigned_cmp Cge lhs rhs
  | CmpOp.UnsignedLt => unsigned_cmp Clt lhs rhs
  | CmpOp.UnsignedLe => unsigned_cmp Cle lhs rhs
  | CmpOp.SignedGt => signed_cmp Cgt lhs rhs
  | CmpOp.SignedGe => signed_cmp Cge lhs rhs
  | CmpOp.SignedLt => signed_cmp Clt lhs rhs
  | CmpOp.SignedLe => signed_cmp Cle lhs rhs
  | CmpOp.BitSet =>
      match guard_size condition with
      | OpSize.Op32 => unsigned_cmp Cne (Val.and lhs rhs) (Vint Int.zero)
      | OpSize.Op64 => unsigned_cmp Cne (Val.andl lhs rhs) (Vlong Int64.zero)
      end
  end = Some true.

Definition atom_holds (world : interpretation) (memory : mem) (fact : atom) : Prop :=
  match fact with
  | MemoryCell region bytes abstract =>
      cell_holds world memory region bytes abstract
  | AbstractValue expression abstract =>
      value_holds world memory abstract (eval_term world expression)
  | MemoryEq region offset name =>
      memory_eq_holds memory (region_address world region offset) (variable_value world name)
  | GhostEq name expression => ghost_value world name = eval_term world expression
  | Def dst op lhs rhs =>
      definition_holds op (variable_value world dst) (eval_term world lhs) (eval_term world rhs)
  | Eq lhs rhs =>
      runtime_value (eval_term world lhs) /\ eval_term world lhs = eval_term world rhs
  | NeqZero expression =>
      runtime_value (eval_term world expression) /\
      eval_term world expression <> Vlong Int64.zero
  | Neq lhs rhs =>
      runtime_value (eval_term world lhs) /\ runtime_value (eval_term world rhs) /\
      eval_term world lhs <> eval_term world rhs
  | Le lhs rhs signed =>
      comparison_is_true memory signed Cle (eval_term world lhs) (eval_term world rhs)
  | Lt lhs rhs signed =>
      comparison_is_true memory signed Clt (eval_term world lhs) (eval_term world rhs)
  | Owns name resource =>
      Unimplemented.owns (region_location world) (allocation_metadata_of memory) name resource
  | LinearInduction pointer index stride base =>
      Unimplemented.linear_induction (region_location world)
        (variable_value world pointer) (variable_value world index) stride base
  | Guarded condition expression abstract =>
      guard_is_true memory condition (variable_value world (guard_var condition)) ->
      value_holds world memory abstract (eval_term world expression)
  | AbstractDomain.Readable base bytes =>
      initialized_readable_window memory (variable_value world base) bytes
  | ReadableCell region offset bytes =>
      stack_cell_points_to_window world memory region offset bytes
  end.


(** A region with cells occupies its own CompCert block: no other region's
    location or allocation shares it. Upstream allocates a fresh block for each
    stack frame; ringbuf reservations, flow keys and tracepoint buffers are
    modeled as separate objects in the same way. Regions without cells may
    still alias each other. *)
Definition cell_blocks_exclusive (world : interpretation) : Prop :=
  forall region b origin,
    Region.cells region = Some region ->
    region_location world region = Some (b, origin) ->
    (forall other b' origin', other <> region ->
       region_location world other = Some (b', origin') -> b' <> b) /\
    (forall other b' origin', region_allocation world other b' origin' -> b' <> b).

(** Registers agree on R0-R10 only: [RAX] is the semantics' hidden auxiliary,
    which no eBPF instruction names and the kernel's rewrites use as scratch.
    In the future we might also need to impose some conditions on the callstack
    etc for reasoning about instructions such as calls and ret. *)
Definition concretizes (attrs : load_attrs) (regions : list addr_region)
    (abstract : abstract_machine_state) (concrete : tls_state) : Prop :=
  match concrete with
  | TLS_State registers _ _ _ memory =>
      exists world,
        (forall reg, reg <> RAX ->
           variable_value world (register_name abstract reg) = registers reg) /\
        Forall (atom_holds world memory) (facts abstract) /\
        store_policy_holds world memory attrs /\
        cell_blocks_exclusive world /\
        environment_holds world memory attrs regions
  end.
