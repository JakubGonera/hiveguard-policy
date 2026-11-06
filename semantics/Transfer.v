From Coq Require Import Bool List ZArith Lia.
From compcert Require Import Integers Values Memory Memdata AST.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.
From TrustNoBPF.Semantics Require Import AbstractDomain Concretization.

Import ListNotations.
Open Scope Z_scope.

(** ** Rust IR instruction operands ([ir/cfg/inst.rs]) *)

Module ArithmeticOp.
  (** [ir/cfg/inst/opcodes.rs::ArithmeticOp]. *)
  Inductive t := Add | Sub | Mul | Div | Or | And | Lsh | Rsh
    | Neg | Mod | Xor | Mov | Arsh | End.
End ArithmeticOp.

Module SourceOperand.
  Inductive t := Imm (immediate : int) | Value (name : var).
End SourceOperand.

(** Rust [ir/cfg/inst.rs::Condition]: [dst <op> src]. *)
Record condition := Condition {
  cond_dst : var;
  cond_src : SourceOperand.t;
  cond_op : CmpOp.t;
}.

(** The [ld_imm64] family of Rust's IR ([ir/cfg/inst.rs]). None reads an
    operand or memory, so [check_defined_operands] checks nothing. *)
Module LdImm64.
  Inductive t :=
    | LoadImm64 (imm : Z)
    | LoadMapFd (id : map)
    | LoadMapValue (id : map) (offset : Z)
    | LoadSubprogAddr (id : subprog).
End LdImm64.

(** Instruction-independent transfer operations and SSA register naming.
    [apply_havoc] and [find_pointer_fact] follow Rust's [transfer.rs]. *)

Definition find_pointer_fact (state : abstract_state) (base : var) : option ptr_state :=
  fold_left
    (fun found fact =>
       match found, fact with
       | Some ptr, _ => Some ptr
       | None, AbstractValue (Var x) (Ptr ptr) => if Nat.eqb x base then Some ptr else None
       | None, _ => None
       end)
    state None.

(** Rust reference: [verifier/transfer.rs::ensure_defined]. After rebasing
    onto main, an operand requires a direct non-[Uninit] value fact on its
    own variable. Equality chains and other mentions are not evidence. *)
Definition has_initialized_value (state : abstract_state) (name : var) : bool :=
  existsb (fun fact => match fact with
    | AbstractValue (Var found) Uninit => false
    | AbstractValue (Var found) _ => Nat.eqb found name
    | _ => false
    end) state.

Definition has_uninit_value (state : abstract_state) (name : var) : bool :=
  existsb (fun fact => match fact with
    | AbstractValue (Var found) Uninit => Nat.eqb found name
    | _ => false
    end) state.

(** Boolean success of Rust's direct initialization check.
    BRANCH RUST CHANGE [DEFINED-NO-UNINIT], introduced in commit 86613c5: Rust
    [transfer.rs::ensure_defined]
    also rejects a value carrying an [Uninit] fact; main accepted it whenever
    another fact was initialized. A register store copies every fact of its
    source into memory cells ([stored_values]), so main could create the
    [Uninit] cell [no_uninit_memory_cells] excludes. *)
Definition ensure_defined (state : abstract_state) (name : var) : bool :=
  has_initialized_value state name && negb (has_uninit_value state name).

(** ** Pointer-leak rules

    Rust [transfer/leaks.rs] with [PolicyEnv::allow_ptr_leaks] false: a value
    leaves the program only with a [Scalar] fact or one constant, which only
    scalar sources and operations on disclosable values produce. *)

(** Rust [leaks::state_disclosable]. *)
Definition state_disclosable (value : value_state) : bool :=
  match value with
  | Scalar => true
  | URangeValue bounds => Z.eqb (u_lower bounds) (u_upper bounds)
  | RangeValue bounds => Z.eqb (lower bounds) (upper bounds)
  | _ => false
  end.

(** Rust [leaks::disclosable]. *)
Definition disclosable (state : abstract_state) (name : var) : bool :=
  existsb (fun fact => match fact with
    | AbstractValue (Var found) value => Nat.eqb found name && state_disclosable value
    | _ => false
    end) state.

(** The furthest end of a disclosable cell of [region] containing [point]:
    the [max] in Rust [leaks::cells_disclosable]. *)
Definition disclosable_cell_end (state : abstract_state) (region : Region.t)
    (point : Z) : option Z :=
  fold_left (fun found fact =>
    match fact with
    | MemoryCell cell_region bytes value =>
        if Region.eqb cell_region region && (lower bytes <=? point) &&
           (point <? upper bytes) && state_disclosable value
        then Some (match found with
                   | Some furthest => Z.max furthest (upper bytes)
                   | None => upper bytes
                   end)
        else found
    | _ => found
    end) state None.

Fixpoint cells_disclosable_from (fuel : nat) (state : abstract_state)
    (region : Region.t) (window : range) (point : Z) : bool :=
  if upper window <=? point then true else
  match fuel with
  | O => false
  | S fuel' =>
      match disclosable_cell_end state region point with
      | Some next => cells_disclosable_from fuel' state region window next
      | None => false
      end
  end.

(** Rust [leaks::cells_disclosable]: only the stack keeps stored pointers. Each
    step passes the end of a cell it cannot meet again, so [length state]
    steps suffice. *)
Definition cells_disclosable (state : abstract_state) (region : Region.t)
    (window : range) : bool :=
  negb (Region.uninit_by_default region) ||
  cells_disclosable_from (length state) state region window (lower window).

(** Rust [leaks::mark_scalar]. *)
Definition mark_scalar (state : abstract_state) (name : var) : abstract_state :=
  match find_pointer_fact state name with
  | Some _ => state
  | None =>
      if existsb (fun fact => match fact with
           | AbstractValue (Var found) Scalar => Nat.eqb found name
           | _ => false
           end) state
      then state else state ++ [AbstractValue (Var name) Scalar]
  end.

(** Rust [transfer.rs::ensure_nothing_held]: no resource may outlive the
    program or a tail call. *)
Definition ensure_nothing_held (state : abstract_state) : bool :=
  negb (existsb (fun fact => match fact with Owns _ _ => true | _ => false end) state).

(** ** Meets ([verifier/meet.rs]) *)

Definition value_state_eq_dec : forall a b : value_state, {a = b} + {a <> b}.
Proof.
  repeat decide equality; apply Z.eq_dec.
Defined.

(** Rust [meet::StateKind::index]. *)
Definition state_kind (value : value_state) : nat :=
  match value with
  | Uninit => 0 | Unknown => 1 | Scalar => 2 | URangeValue _ => 3
  | RangeValue _ => 4 | CongruenceValue _ => 5 | Ptr _ => 6
  end%nat.

(** Rust [meet::meet], with [stronger] deciding through [entails].
    BRANCH RUST CHANGE [MEET-PTR], introduced in commit (uncommitted): Rust
    [meet.rs::meet] no longer merges two pointer facts into a new one; main's
    [meet_ptr] intersected their offsets and took the larger size and end
    bound, which [pointer_access_holds] does not justify. *)
Definition meet (entails : value_state -> value_state -> bool)
    (a b : value_state) : option value_state :=
  match a, b with
  | URangeValue x, URangeValue y =>
      Some (URangeValue (URange (Z.max (u_lower x) (u_lower y)) (Z.min (u_upper x) (u_upper y))))
  | RangeValue x, RangeValue y =>
      Some (RangeValue (Range (Z.max (lower x) (lower y)) (Z.min (upper x) (upper y))))
  | _, _ =>
      if value_state_eq_dec a b then Some a
      else if entails a b then Some a
      else if entails b a then Some b
      else None
  end.

Definition fold_kind (entails : value_state -> value_state -> bool)
    (states : list value_state) (kind : nat) : option value_state :=
  fold_left (fun held value =>
    if Nat.eqb (state_kind value) kind then
      Some (match held with
            | Some previous =>
                match meet entails previous value with Some met => met | None => value end
            | None => value
            end)
    else held) states None.

(** Rust [meet::fold]: at most one fact per kind, in [StateKind] order. Without
    a single meet the later fact is kept. *)
Definition fold (entails : value_state -> value_state -> bool)
    (states : list value_state) : list value_state :=
  flat_map (fun kind => match fold_kind entails states kind with
                        | Some value => [value]
                        | None => []
                        end) (seq 0 7).

Definition apply_havoc (state : abstract_state) (dst : var) : abstract_state :=
  filter (fun fact => negb (atom_mentions dst fact)) state ++
  [AbstractValue (Var dst) Unknown].

(** Rust [apply_havoc_with_size], shared by loads and arithmetic transfers. *)
Definition apply_havoc_with_size (state : abstract_state) (dst : var)
    (size : sizeOp) : abstract_state :=
  let havoced := apply_havoc state dst in
  match size with
  | Byte => havoced ++ [AbstractValue (Var dst) (URangeValue (URange 0 255));
                        AbstractValue (Var dst) (RangeValue (Range 0 255))]
  | HalfWord => havoced ++ [AbstractValue (Var dst) (URangeValue (URange 0 65535));
                            AbstractValue (Var dst) (RangeValue (Range 0 65535))]
  | Word => havoced ++ [AbstractValue (Var dst) (URangeValue (URange 0 4294967295));
                        AbstractValue (Var dst) (RangeValue (Range 0 4294967295))]
  | DBWord => havoced
  end.

Definition set_register_name (names : ireg -> var) (dst : ireg) (value : var) :
    ireg -> var :=
  fun reg => if ireg_eq reg dst then value else names reg.

(** Updating an SSA value leaves the interpretation of memory unchanged. *)
Definition assign_value (world : interpretation) (dst : var) (value : val) : interpretation :=
  Interpretation (fun x => if Nat.eq_dec x dst then value else variable_value world x)
    (ghost_value world)
    (region_location world)
    (region_allocation world).

(** A successful checked access, corresponding to Rust's [CheckedAccess]. *)
Record checked_access := CheckedAccess {
  access_ptr : ptr_state;
  access_range : range;
  access_exact : bool;
}.

(** Rust integers are represented by [Z]. Inputs must have their Rust field
    widths; unlike plain [Z.add], [i64_checked_add] rejects signed overflow. *)
Definition i64_checked_add (x y : Z) : option Z :=
  let sum := x + y in
  if (-9223372036854775808 <=? sum) && (sum <=? 9223372036854775807)
  then Some sum else None.

Definition i64_checked_sub (x y : Z) : option Z := i64_checked_add x (- y).

(** Rust [CtxGate::admits] and [CtxField::admits_where]. The selected kernel
    field table and loader capabilities come from policy, not from facts. *)
Definition ctx_gate_admits (context : ctx_policy) (gate : CtxGate.t) : bool :=
  match gate with
  | CtxGate.Never => false
  | CtxGate.Always => true
  | CtxGate.AttachTypes types =>
      match ctx_expected_attach_type context with
      | Some attach => existsb (Nat.eqb attach) types
      | None => false
      end
  | CtxGate.BpfCapable => ctx_bpf_capable context
  end.

Definition ctx_field_admits (context : ctx_policy) (field : ctx_field)
    (offset width : Z) (write : bool) : bool :=
  let access := if write then ctx_field_write field else ctx_field_read field in
  match i64_checked_add offset width with
  | Some finish =>
      existsb (Z.eqb width) [1; 2; 4; 8] &&
      negb (Z.eqb (Z.land (ctx_access_sizes access) width) 0) &&
      ctx_gate_admits context (ctx_access_gate access) &&
      (lower (ctx_field_range field) <=? offset) &&
      (finish <=? upper (ctx_field_range field)) &&
      Z.eqb (offset mod width) 0 &&
      (ctx_field_interior field || Z.eqb offset (lower (ctx_field_range field)))
  | None => false
  end.

(** Rust [ctx_field_for]: only an unmodified context pointer can name a
    kernel context field. Width conversion is checked before table lookup. *)
Definition ctx_field_for (context : ctx_policy) (ptr : ptr_state)
    (offset width : Z) (write : bool) : option ctx_field :=
  if Z.eqb (ptr_off_min ptr) 0 && Z.eqb (ptr_off_max ptr) 0 &&
     (0 <=? width) && (width <=? 255)
  then find (fun field => ctx_field_admits context field offset width write)
         (ctx_fields context)
  else None.

Definition filter_context_access (context : ctx_policy) (offset width : Z)
    (write : bool) (checked : option checked_access) : option checked_access :=
  match checked with
  | Some access =>
      if Region.is (ptr_ty (access_ptr access)) RegionClass.CTX then
        match ctx_field_for context (access_ptr access) offset width write with
        | Some _ => Some access | None => None
        end
      else Some access
  | None => None
  end.

Lemma filter_context_access_some : forall context offset width write checked access,
  filter_context_access context offset width write checked = Some access ->
  checked = Some access.
Proof.
  intros context offset width write [found|] access CHECK;
    cbn [filter_context_access] in CHECK; try discriminate.
  destruct (Region.is (ptr_ty (access_ptr found)) RegionClass.CTX);
    [destruct (ctx_field_for context (access_ptr found) offset width write)|];
    congruence.
Qed.

(** The bit-preserving Rust cast [u64 as i64]. *)
Definition u64_as_i64 (x : Z) : Z :=
  if x <? 9223372036854775808 then x else x - 18446744073709551616.

(** [- (size as i64)] in two's-complement arithmetic, including the minimum
    signed value. Rust builds with overflow checks enabled panic at that one
    size; panics, like allocation failures, are outside the transfer model. *)
Definition stack_size_lower (size : Z) : Z :=
  if size =? 9223372036854775808 then -9223372036854775808
  else - u64_as_i64 size.

Definition checked_access_for_ptr (ptr : ptr_state) (offset width : Z)
    (strict_alignment : bool) : option checked_access :=
  if permission_includes (ptr_permission ptr) Read then
    let probe := Region.probe_readable (ptr_ty ptr) in
    if orb probe
         match ptr_nullability ptr with NonNull => true | _ => false end then
      match i64_checked_add (ptr_off_min ptr) offset,
            i64_checked_add (ptr_off_max ptr) offset with
      | Some start, Some last =>
          match i64_checked_add last width with
          | Some finish =>
              let valid := if Region.grows_down (ptr_ty ptr)
                           then Range (stack_size_lower (ptr_size ptr)) 0
                           else Range 0 (u64_as_i64 (ptr_size ptr)) in
              let relative_safe :=
                match i64_checked_add offset width, ptr_end_min ptr with
                | Some needed, Some bound => needed <=? bound
                | _, _ => false
                end in
              let in_bounds := probe ||
                ((lower valid <=? start) &&
                 ((finish <=? upper valid) || relative_safe)) in
              let exact := Z.eqb (ptr_off_min ptr) (ptr_off_max ptr) in
              let aligned :=
                if strict_alignment && (1 <? width) then
                  Z.eqb (start mod width) 0 &&
                  (exact || Z.eqb (ptr_align ptr mod width) 0)
                else true in
              if in_bounds && aligned
              then Some (CheckedAccess ptr (Range start finish) exact)
              else None
          | None => None
          end
      | _, _ => None
      end
    else None
  else None.

(** Rust [SpecialFields::overlap] and [transfer.rs::check_special_fields].
    Only MAP_VALUE pointers with a Map key select fields. Adjacent ranges
    do not overlap; the entire possible access range is checked. *)
Definition check_special_fields (maps : map_special_fields) (ptr : ptr_state)
    (bytes : range) : bool :=
  match Region.key (ptr_ty ptr) with
  | RegionKey.Map id =>
      negb (Region.is (ptr_ty ptr) RegionClass.MAP_VALUE &&
        existsb (fun field =>
          (lower bytes <? special_field_offset field + special_field_size field) &&
          (special_field_offset field <? upper bytes)) (maps id))
  | _ => true
  end.

Definition filter_special_access (maps : map_special_fields)
    (access : option checked_access) : option checked_access :=
  match access with
  | Some access => if check_special_fields maps (access_ptr access) (access_range access)
                   then Some access else None
  | None => None
  end.

Lemma filter_special_access_some : forall maps checked access,
  filter_special_access maps checked = Some access -> checked = Some access.
Proof.
  intros maps [found|] access CHECK; cbn [filter_special_access] in CHECK;
    try discriminate.
  destruct (check_special_fields maps (access_ptr found) (access_range found));
    congruence.
Qed.

Definition checked_access_range (state : abstract_state) (base : var)
    (offset width : Z) (strict_alignment : bool) (maps : map_special_fields)
    (context : ctx_policy) : option checked_access :=
  match find_pointer_fact state base with
  | Some ptr => filter_special_access maps
      (filter_context_access context offset width false
        (checked_access_for_ptr ptr offset width strict_alignment))
  | None => None
  end.

(** Rust's [Lookup::cells_cover] ([verifier/key.rs]), reached through
    [transfer/window.rs::cells_cover] and also used for helper inputs. *)
Fixpoint cells_cover_from (fuel : nat) (state : abstract_state)
    (region : Region.t) (window : range) (point : Z) : bool :=
  if upper window <=? point then true else
  match fuel with
  | O => false
  | S fuel' =>
      match find (fun fact =>
          match fact with
          | MemoryCell cell_region bytes _ =>
              Region.eqb region cell_region &&
              (lower bytes <=? point) && (point <? upper bytes)
          | _ => false
          end) state with
      | Some (MemoryCell _ bytes _) =>
          cells_cover_from fuel' state region window (upper bytes)
      | _ => false
      end
  end.

Definition cells_cover (state : abstract_state) (region : Region.t)
    (window : range) : bool :=
  cells_cover_from (length state) state region window (lower window).

(** Local execution of a supplied instruction.  To obtain [ebpfBinSem.step],
    also establish that instruction fetching at the current PC selects it. *)
Definition instruction_step (regions : list addr_region) (program : ebpf_prog)
    (instruction : instruction) (before after : tls_state) : Prop :=
  match before, after with
  | TLS_State regs stack code_id tail_call_count memory,
    TLS_State regs' stack' code_id' tail_call_count' memory' =>
      exec_instr program instruction regs stack code_id tail_call_count memory regions =
        Next regs' stack' code_id' tail_call_count' memory'
  end.

(** Shared store operations. *)

(** The local store definitions are wrapped by [transfer_with_provenance]
    below, modeling Rust's tracking update and [materialize] cleanup.
    Rust-sized inputs are required; allocation failures and panics are not
    modeled.

    Policy write windows are interpreted by [concretizes].
    [accepted_transfer] below excludes
    uninitialized memory-cell facts, following Rust's invariant validation.
    Ordinary byte writes preserve the allocation metadata seen by pointers
    and ownership; writable BTF pointers require concrete write permissions. *)

(** =========== Shared transfer definitions =========== *)

(** ** Write access *)

Definition write_window_allows (policy : store_policy) (region : Region.t)
    (bytes : range) : bool :=
  existsb (fun window => Region.eqb (write_region window) region &&
    range_covers (write_range window) bytes) (store_write_windows policy).


Definition write_window_grants (policy : store_policy) (ptr : ptr_state)
    (offset width : Z) : bool :=
  match i64_checked_add (ptr_off_min ptr) offset,
        i64_checked_add (ptr_off_max ptr) offset with
  | Some start, Some last =>
      match i64_checked_add last width with
      | Some finish => write_window_allows policy (ptr_ty ptr) (Range start finish)
      | None => false
      end
  | _, _ => false
  end.

Definition with_write_permission (ptr : ptr_state) : ptr_state :=
  PtrState (ptr_ty ptr) (ptr_nullability ptr) (ptr_flags ptr)
    (ptr_off_min ptr) (ptr_off_max ptr) (ptr_size ptr) (ptr_end_min ptr)
    (ptr_align ptr) ReadWrite (ptr_ref_obj ptr).

(** Exact specialization of Rust's [checked_access_for_ptr] to [Perm::Write].
    [probe_read] is ALWAYS false for writes, including through BTF pointers:
    write permission, non-nullness, bounds and alignment are all checked. *)
Definition checked_write_access_for_ptr (ptr : ptr_state) (offset width : Z)
    (strict_alignment : bool) : option checked_access :=
  if permission_includes (ptr_permission ptr) Write then
    match ptr_nullability ptr with
    | NonNull =>
        match i64_checked_add (ptr_off_min ptr) offset,
              i64_checked_add (ptr_off_max ptr) offset with
        | Some start, Some last =>
            match i64_checked_add last width with
            | Some finish =>
                let valid := if Region.grows_down (ptr_ty ptr)
                             then Range (stack_size_lower (ptr_size ptr)) 0
                             else Range 0 (u64_as_i64 (ptr_size ptr)) in
                let relative_safe :=
                  match i64_checked_add offset width, ptr_end_min ptr with
                  | Some needed, Some bound => needed <=? bound
                  | _, _ => false
                  end in
                let in_bounds := (lower valid <=? start) &&
                  ((finish <=? upper valid) || relative_safe) in
                let exact := Z.eqb (ptr_off_min ptr) (ptr_off_max ptr) in
                let aligned :=
                  if strict_alignment && (1 <? width) then
                    Z.eqb (start mod width) 0 &&
                    (exact || Z.eqb (ptr_align ptr mod width) 0)
                  else true in
                if in_bounds && aligned
                then Some (CheckedAccess ptr (Range start finish) exact)
                else None
            | None => None
            end
        | _, _ => None
        end
    | _ => None
    end
  else None.

(** Rust's [checked_access_range] with [required_perm = Write]. A policy
    grant upgrades only the LOCAL copy of the pointer, not the state's facts.
    Context fields grant writes independently of write windows. Both kinds
    of grant still require bounds, alignment and special-field checks. *)
Definition checked_write_access_range (state : abstract_state) (base : var)
    (offset width : Z) (policy : store_policy) : option checked_access :=
  match find_pointer_fact state base with
  | Some ptr =>
      let ptr :=
        if Region.is (ptr_ty ptr) RegionClass.CTX ||
           (negb (permission_includes (ptr_permission ptr) Write) &&
            write_window_grants policy ptr offset width)
        then with_write_permission ptr else ptr in
      filter_special_access (store_map_special_fields policy)
        (filter_context_access (store_ctx_policy policy) offset width true
          (checked_write_access_for_ptr ptr offset width (store_strict_alignment policy)))
  | None => None
  end.

(** ** Memory-cell updates *)

Definition overlaps (left right : range) : bool :=
  (lower left <? upper right) && (lower right <? upper left).

(** [window::degrade_overlapping_content]: keep every interval, but replace
    the value of each possibly overwritten cell by [Unknown], or by [Scalar]
    for a disclosable cell when the store writes a [disclosable] value. Other
    atom kinds, including [MemoryEq] and [ReadableCell], are left alone in
    Rust. *)
Definition degrade_overlapping_content (state : abstract_state) (ptr : ptr_state)
    (window : range) (disclosable : bool) : abstract_state :=
  match Region.cells (ptr_ty ptr) with
  | Some region =>
      List.map (fun fact =>
        match fact with
        | MemoryCell cell_region bytes value =>
            if Region.eqb cell_region region && overlaps bytes window
            then MemoryCell cell_region bytes
                   (if disclosable && state_disclosable value then Scalar else Unknown)
            else fact
        | _ => fact
        end) state
  | None => state
  end.

(** The value Rust keeps for the untouched part of an overwritten cell. *)
Definition remainder_value (value : value_state) : value_state :=
  match value with Scalar => Scalar | _ => Unknown end.

(** [remove_overlapping_cells] / [split_atoms_overlapping]: discard the
    overwritten part. Each non-overwritten piece keeps [Scalar] and is
    otherwise [Unknown], in original atom order, left piece before right
    piece. No cells are merged. *)
Definition remove_overlapping_cells (state : abstract_state) (region : Region.t)
    (window : range) : abstract_state :=
  flat_map (fun fact =>
    match fact with
    | MemoryCell cell_region bytes value =>
        if Region.eqb cell_region region && overlaps bytes window then
          (if lower bytes <? lower window
           then [MemoryCell region (Range (lower bytes) (lower window)) (remainder_value value)]
           else []) ++
          (if upper window <? upper bytes
           then [MemoryCell region (Range (upper window) (upper bytes)) (remainder_value value)]
           else [])
        else [fact]
    | _ => [fact]
    end) state.

Definition remove_overlapping_content (state : abstract_state) (ptr : ptr_state)
    (window : range) : abstract_state :=
  match Region.cells (ptr_ty ptr) with
  | Some region => remove_overlapping_cells state region window
  | None => state
  end.

(** Rust keeps stored pointer descriptions only in stack-like regions. *)
Definition memory_stored_value (region : Region.t) (value : value_state) : value_state :=
  match value with
  | Ptr _ => if Region.uninit_by_default region then value else Unknown
  | _ => value
  end.

Definition push_memory_state (state : abstract_state) (ptr : ptr_state)
    (bytes : range) (value : value_state) : abstract_state :=
  match Region.cells (ptr_ty ptr) with
  | Some region =>
      state ++ [MemoryCell region bytes (memory_stored_value region value)]
  | None => state
  end.

(** ** Instruction-loop spill tracking

    Rust reference: [transfer/spill_provenance.rs]. Lists model successful
    allocations. This state is passed between instructions in a block;
    [from_entry] initializes it only at block entry. *)
Module SpillProvenance.
  Record binding := Binding {
    binding_region : Region.t;
    binding_range : range;
    binding_value : var;
  }.

  Record disturbance := Disturbance {
    cells : list (Region.t * range);
    regions : list Region.t;
    everything : bool;
  }.

  Definition covers (d : disturbance) (region : Region.t) (bytes : range) : bool :=
    everything d || existsb (Region.eqb region) (regions d) ||
    existsb (fun cell => Region.eqb (fst cell) region && overlaps (snd cell) bytes) (cells d).

  Record t := Provenance {
    entries : list binding;
    entry_bindings : list binding;
    disturbed : disturbance;
  }.

  Definition from_entry (state : abstract_state) : t :=
    Provenance (flat_map (fun fact =>
      match fact with
      | MemoryEq region offset value =>
          match i64_checked_add offset 8 with
          | Some finish => [Binding region (Range offset finish) value]
          | None => []
          end
      | _ => []
      end) state) [] (Disturbance [] [] false).

  Definition holder (items : list binding) (region : Region.t) (bytes : range) : option var :=
    option_map binding_value (find (fun item =>
      Region.eqb (binding_region item) region &&
      Z.eqb (lower (binding_range item)) (lower bytes) &&
      Z.eqb (upper (binding_range item)) (upper bytes)) items).

  (** [None]: unresolved; [Some (region, None)]: imprecise offset;
      [Some (region, Some bytes)]: exact cell. Overflow is unresolved. *)
  Definition resolve_write (state : abstract_state) (base : var) (offset width : Z) :
      option (Region.t * option range) :=
    match find_pointer_fact state base with
    | Some ptr =>
        match Region.cells (ptr_ty ptr) with
        | Some region =>
            if Z.eqb (ptr_off_min ptr) (ptr_off_max ptr) then
              match i64_checked_add (ptr_off_min ptr) offset with
              | Some start =>
                  match i64_checked_add start width with
                  | Some finish => Some (region, Some (Range start finish))
                  | None => None
                  end
              | None => None
              end
            else Some (region, None)
        | None => None
        end
    | None => None
    end.

  Definition exact_cell (state : abstract_state) (base : var) (offset width : Z) :
      option (Region.t * range) :=
    match resolve_write state base offset width with
    | Some (region, Some bytes) => Some (region, bytes)
    | _ => None
    end.

  Definition keep_disjoint (items : list binding) (region : Region.t) (bytes : range) :=
    filter (fun item => negb (Region.eqb (binding_region item) region &&
      overlaps (binding_range item) bytes)) items.

  Definition targets_shared_memory (state : abstract_state) (base : var) : bool :=
    match find_pointer_fact state base with
    | Some ptr => Region.contents_shared (ptr_ty ptr)
    | None => false
    end.

  Definition invalidate_write (p : t) (state : abstract_state)
      (base : var) (offset width : Z) : t * option (Region.t * range) :=
    if targets_shared_memory state base then (p, None) else
    let d := disturbed p in
    match resolve_write state base offset width with
    | Some (region, Some bytes) =>
        (Provenance (keep_disjoint (entries p) region bytes) (entry_bindings p)
          (Disturbance (cells d ++ [(region, bytes)]) (regions d) (everything d)),
         Some (region, bytes))
    | Some (region, None) =>
        (Provenance (filter (fun item => negb (Region.eqb (binding_region item) region))
          (entries p)) (entry_bindings p)
          (Disturbance (cells d) (regions d ++ [region]) (everything d)), None)
    | None =>
        (Provenance [] (entry_bindings p) (Disturbance (cells d) (regions d) true), None)
    end.

  (** The projection of an instruction needed by [update]. [Unaffected]
      denotes Rust's default branch, not an unimplemented memory operation. *)
  Inductive effect :=
    | StoreImm (base : var) (offset width : Z)
    | StoreReg (base source : var) (offset width : Z)
    | LoadMem (base destination : var) (offset width : Z)
    | Atomic (base : var) (offset width : Z)
    | Call
    | Unaffected.

  Definition update (p : t) (state : abstract_state) (instruction : effect) :
      t * option (var * var) :=
    match instruction with
    | StoreImm base offset width | Atomic base offset width =>
        (fst (invalidate_write p state base offset width), None)
    | StoreReg base source offset width =>
        let '(p', written) := invalidate_write p state base offset width in
        match written with
        | Some (region, bytes) =>
            if Z.eqb width 8 then
              (Provenance (entries p' ++ [Binding region bytes source])
                (entry_bindings p') (disturbed p'), None)
            else (p', None)
        | None => (p', None)
        end
    | LoadMem base destination offset width =>
        if Z.eqb width 8 then
          match exact_cell state base offset 8 with
          | Some (region, bytes) =>
              let displaced := holder (entries p) region bytes in
              let bindings :=
                if negb (covers (disturbed p) region bytes) &&
                   match holder (entry_bindings p) region bytes with
                   | None => true | Some _ => false end
                then entry_bindings p ++ [Binding region bytes destination]
                else entry_bindings p in
              (Provenance (keep_disjoint (entries p) region bytes ++
                [Binding region bytes destination]) bindings (disturbed p),
               option_map (fun value => (destination, value)) displaced)
          | None => (p, None)
          end
        else (p, None)
    | Call =>
        let d := disturbed p in
        (Provenance [] (entry_bindings p) (Disturbance (cells d) (regions d) true), None)
    | Unaffected => (p, None)
    end.

  Definition materialize (p : t) (state : abstract_state) : abstract_state :=
    filter (fun fact =>
      match fact with
      | MemoryEq _ _ _ => false
      | ReadableCell region offset _ =>
          match i64_checked_add offset 8 with
          | Some finish => negb (covers (disturbed p) region (Range offset finish))
          | None => false
          end
      | _ => true
      end) state ++
    List.map (fun item => MemoryEq (binding_region item) (lower (binding_range item))
      (binding_value item)) (entries p).
End SpillProvenance.

(** Rust's loop order: update tracking from the PRE-state, run the local
    transfer, materialize memory equalities, then add any recovered equality.
    Access/write recording, hints and instruction groups are outside this
    wrapper. It models the branch of [transfer_block_recording] that memory
    operations and calls take. Pure instructions (arithmetic and the
    [ld_imm64] family) with a numerically fresh destination take the
    premise-index path instead ([premises.rs]), which runs neither tracking
    nor [materialize]; their Rocq transfers are the local ones. *)
Definition transfer_with_provenance (provenance : SpillProvenance.t)
    (effect : SpillProvenance.effect) (before : abstract_machine_state)
    (local_transfer : option abstract_machine_state) :
    option (abstract_machine_state * SpillProvenance.t) :=
  let '(provenance', refilled) := SpillProvenance.update provenance (facts before) effect in
  match local_transfer with
  | Some after =>
      let post := SpillProvenance.materialize provenance' (facts after) in
      let post := match refilled with
                  | Some (loaded, value) => post ++ [Eq (Var loaded) (Var value)]
                  | None => post
                  end in
      Some (AbstractMachineState post (register_name after), provenance')
  | None => None
  end.

(** One-instruction block entry. Block-level clients must use the persistent
    [transfer_with_provenance] interface instead of resetting this state. *)
Definition transfer_at_entry (effect : SpillProvenance.effect)
    (before : abstract_machine_state) (local_transfer : option abstract_machine_state) :
    option abstract_machine_state :=
  option_map fst (transfer_with_provenance (SpillProvenance.from_entry (facts before))
    effect before local_transfer).

(** ** Accepted transitions: trusted validation followed by transfer

    Provenance: [bpf_verifier/core/src/verifier/entail.rs::validate_invariant]
    rejects [Atom::MemoryCell { state: AbstractState::Uninit, .. }] with
    [InvalidUninitMemoryFact]. [verifier/check.rs::check_validated_program] calls
    validation on the entry invariant and each combined block invariant
    BEFORE executing the block's transfers. This is a trusted verifier check,
    not a promise made by the proof generator.

    This predicate models ONLY that rejection. TODO(validation): guarded
    value and readable-window validation, and the rejection of two facts with
    one key ([key::duplicate_key]), are not transcribed here yet.
    Explicit [Uninit] register/value facts are not rejected by this predicate;
    only memory-cell contents are checked. *)
Definition no_uninit_memory_cells (state : abstract_state) : Prop :=
  Forall (fun fact =>
    match fact with MemoryCell _ _ Uninit => False | _ => True end) state.

(** Rust [logic/term.rs::Range] stores both endpoints as [i64].
    [proof/parse.rs::decode_atom] reads memory coordinates using [cursor.i64()];
    for [MemoryCell], [Readable] and [ReadableCell] it also calls
    [check_srange], rejecting [lower > upper]. [MemoryEq] has a single [i64]
    offset. These are representation/parser restrictions, distinct from the
    invariant-validation check above. No truncating conversion is used here:
    an out-of-range Rocq integer is rejected, not wrapped to fit Rust.
    [proof/parse.rs::decode_mem_region] rejects a memory fact about a region
    without cells.
    The eight-byte slot of a [ReadableCell] or [MemoryEq] also ends in [i64]:
    [entail.rs::validate_invariant] rejects a [ReadableCell] whose
    [offset.checked_add(8)] fails, and entailment admits a [MemoryEq] only
    under the same condition, so no entailed block entry carries one. An
    invariant no edge entails may still carry such a [MemoryEq], which Rust
    transfers without effect; requiring this condition there is stronger than
    Rust. *)
Definition i64_coordinate (offset : Z) : Prop :=
  Int64.min_signed <= offset <= Int64.max_signed.

Definition memory_range_valid (bytes : range) : Prop :=
  i64_coordinate (lower bytes) /\ i64_coordinate (upper bytes) /\
  lower bytes <= upper bytes.

(** [proof/parse.rs::decode_region] rejects a region Rust's
    [Region::is_well_formed] refuses; only the stack class takes a frame key. *)
Definition frame_key_valid (region : Region.t) : Prop :=
  match Region.frame region with
  | Some frame => region = Region.stack frame
  | None => True
  end.

Definition memory_coordinates_valid (fact : atom) : Prop :=
  match fact with
  | AbstractValue _ (Ptr ptr) => frame_key_valid (ptr_ty ptr)
  | MemoryCell region bytes _ => Region.cells region = Some region /\ memory_range_valid bytes
  | AbstractDomain.Readable _ bytes => memory_range_valid bytes
  | MemoryEq region offset _ =>
      Region.cells region = Some region /\ i64_coordinate offset /\ i64_coordinate (offset + 8)
  | ReadableCell region offset bytes =>
      Region.cells region = Some region /\ i64_coordinate offset /\
      i64_coordinate (offset + 8) /\ memory_range_valid bytes
  | _ => True
  end.

(** Only the input restrictions currently needed for memory transfers.
    TODO(representation): this is not a complete Rust-width audit of terms,
    scalar descriptions, identifiers, policies or other domain fields. *)
Definition transfer_input_valid (state : abstract_state) : Prop :=
  no_uninit_memory_cells state /\ Forall memory_coordinates_valid state.

(** Packages the modeled input checks with successful transfer. It changes
    neither the Rust transfer transcription nor [concretizes]. For subsequent
    instructions within a block, preservation of the check must be proved;
    Rust does not re-run [validate_invariant] before every instruction.
    Acceptance here is relative to the validation subset modeled above, not
    a claim that every check performed by the Rust verifier has been modeled. *)
Definition accepted_transfer (before after : abstract_machine_state)
    (result : option abstract_machine_state) : Prop :=
  transfer_input_valid (facts before) /\ result = Some after.

(** =========== Shared proof lemmas =========== *)

Lemma cells_not_probe_readable : forall region cells,
  Region.cells region = Some cells -> Region.probe_readable region = false.
Proof.
  intros [index key] cells CELL.
  unfold Region.cells, Region.probe_readable, Region.desc in *.
  cbn [Region.class Region.key] in *.
  do 23 (destruct index as [|index]; [cbn in *; discriminate || reflexivity |]).
  destruct index; discriminate.
Qed.

(** A region with cells is never untyped BTF, so its address relation applies. *)
Lemma cells_pointer_address : forall world ptr value region,
  Region.cells (ptr_ty ptr) = Some region ->
  (if Region.eqb (ptr_ty ptr) (Region.btf None)
   then permission_includes (ptr_permission ptr) Write = false
   else pointer_address world ptr value) ->
  pointer_address world ptr value.
Proof.
  intros world ptr value region CELLS ADDRESS.
  destruct (Region.eqb (ptr_ty ptr) (Region.btf None)) eqn:UNTYPED; [| exact ADDRESS].
  apply Region.eqb_eq in UNTYPED. rewrite UNTYPED in CELLS. discriminate CELLS.
Qed.

Lemma non_null_base_ordinary_value : forall ptr value,
  non_null_base_pointer_holds ptr value ->
  (Region.probe_readable (ptr_ty ptr) = false \/
   permission_includes (ptr_permission ptr) Write = true) ->
  value <> Vlong Int64.zero.
Proof.
  intros ptr value BASE ORDINARY. destruct value; try discriminate.
  cbn [non_null_base_pointer_holds] in BASE.
  destruct BASE as [PROBE [READ _]]. destruct ORDINARY; congruence.
Qed.

Lemma region_eqb_refl : forall region, Region.eqb region region = true.
Proof.
  intros [class key]. unfold Region.eqb; cbn. rewrite Nat.eqb_refl.
  destruct key; cbn [RegionKey.eqb]; now rewrite ?Nat.eqb_refl.
Qed.

Lemma overlaps_sym : forall left right, overlaps left right = overlaps right left.
Proof. intros. unfold overlaps. apply andb_comm. Qed.

Lemma entry_binding_origin : forall state item,
  In item (SpillProvenance.entries (SpillProvenance.from_entry state)) ->
  exists region offset name,
    In (MemoryEq region offset name) state /\
    item = SpillProvenance.Binding region (Range offset (offset + 8)) name.
Proof.
  intros state item IN. cbn [SpillProvenance.from_entry SpillProvenance.entries] in IN.
  apply in_flat_map in IN as [fact [OLD IN]].
  destruct fact; cbn in IN; try contradiction.
  destruct (i64_checked_add offset 8) as [finish|] eqn:ADD; [| contradiction].
  destruct IN as [ITEM | []]. unfold i64_checked_add in ADD.
  destruct (_ && _) in ADD; inversion ADD; subst finish.
  exists region, offset, value. split; [exact OLD |]. now subst item.
Qed.

(** A retained cell either is untouched or is a subinterval of an overlapping
    original cell, holding its [remainder_value]. This lemma supplies no
    initialization claim. *)
Lemma removed_cell_origin : forall state target window region bytes value,
  In (MemoryCell region bytes value) (remove_overlapping_cells state target window) ->
  (In (MemoryCell region bytes value) state /\
    (region <> target \/ overlaps bytes window = false)) \/
  exists original abstract,
    In (MemoryCell target original abstract) state /\ region = target /\
    value = remainder_value abstract /\
    lower original <= lower bytes /\ upper bytes <= upper original /\
    lower bytes <= upper bytes.
Proof.
  intros state target window region bytes value IN.
  apply in_flat_map in IN as [fact [OLD IN]].
  destruct fact; cbn in IN; try (destruct IN as [EQ | []]; discriminate EQ).
  destruct (Region.eqb region0 target && overlaps bytes0 window) eqn:OVERLAP.
  - apply andb_true_iff in OVERLAP as [REGION OVERLAP].
    apply Region.eqb_eq in REGION. subst region0.
    unfold overlaps in OVERLAP. apply andb_true_iff in OVERLAP as [LEFT RIGHT].
    apply Z.ltb_lt in LEFT, RIGHT.
    apply in_app_iff in IN as [IN | IN].
    + destruct (lower bytes0 <? lower window) eqn:PART; [| contradiction].
      destruct IN as [EQ | []]. inversion EQ; subst region bytes value.
      right. exists bytes0, value0. repeat split; try assumption; try reflexivity; cbn;
        apply Z.ltb_lt in PART; lia.
    + destruct (upper window <? upper bytes0) eqn:PART; [| contradiction].
      destruct IN as [EQ | []]. inversion EQ; subst region bytes value.
      right. exists bytes0, value0. repeat split; try assumption; try reflexivity; cbn;
        apply Z.ltb_lt in PART; lia.
  - destruct IN as [EQ | []]. inversion EQ; subst region bytes value.
    left. split; [exact OLD |]. apply andb_false_iff in OVERLAP as [REGION | NO_OVERLAP].
    + left. intros SAME; subst target. rewrite region_eqb_refl in REGION. discriminate.
    + now right.
Qed.

(** Inside an addressable range, a later start is the earlier start plus the
    distance. *)
Lemma repr_subrange_start : forall base lo len delta,
  Ptrofs.unsigned (Ptrofs.repr (base + lo)) + len <= Ptrofs.modulus ->
  0 <= delta < len ->
  Ptrofs.unsigned (Ptrofs.repr (base + (lo + delta))) =
    Ptrofs.unsigned (Ptrofs.repr (base + lo)) + delta.
Proof.
  intros base lo len delta ADDRESSABLE DELTA.
  pose proof (Ptrofs.unsigned_range (Ptrofs.repr (base + lo))) as RANGE.
  rewrite <- (Ptrofs.unsigned_repr (Ptrofs.unsigned (Ptrofs.repr (base + lo)) + delta))
    by (unfold Ptrofs.max_unsigned; lia).
  f_equal. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_trans with (base + lo + delta).
  - replace (base + (lo + delta)) with (base + lo + delta) by lia. apply Ptrofs.eqm_refl.
  - apply Ptrofs.eqm_add; [apply Ptrofs.eqm_unsigned_repr | apply Ptrofs.eqm_refl].
Qed.

(** An accepted policy window supplies write permission for the selected
    subrange in the very same region mapping used by concretization. *)
Lemma write_window_allows_writable : forall world memory attrs region bytes b origin,
  store_policy_holds world memory attrs ->
  write_window_allows attrs region bytes = true ->
  lower bytes <= upper bytes ->
  region_object world region b origin ->
  Region.probe_readable region = false /\
  let start := Ptrofs.unsigned (Ptrofs.repr (origin + lower bytes)) in
  start + (upper bytes - lower bytes) <= Ptrofs.modulus /\
  Mem.range_perm memory b start (start + (upper bytes - lower bytes)) Cur Writable.
Proof.
  intros world memory attrs region bytes b origin POLICY GRANT RANGE OBJECT.
  unfold write_window_allows in GRANT. apply existsb_exists in GRANT.
  destruct GRANT as [window [IN GRANT]].
  apply andb_true_iff in GRANT as [REGION COVERS].
  apply Region.eqb_eq in REGION.
  unfold range_covers in COVERS. apply andb_true_iff in COVERS as [START END].
  apply Z.leb_le in START, END.
  unfold store_policy_holds in POLICY. rewrite Forall_forall in POLICY.
  destruct (POLICY window IN) as [ORDER [ORDINARY WINDOW]].
  rewrite REGION in ORDINARY, WINDOW.
  destruct (WINDOW b origin OBJECT) as [ADDRESSABLE WRITE].
  split; [exact ORDINARY |].
  cbv zeta in WRITE |- *.
  pose proof (Ptrofs.unsigned_range (Ptrofs.repr (origin + lower bytes))).
  destruct (Z.eq_dec (lower bytes) (upper (write_range window))) as [TOP | INSIDE].
  - split; [lia |]. intros position INSIDE. lia.
  - replace (origin + lower bytes) with
      (origin + (lower (write_range window) + (lower bytes - lower (write_range window)))) by lia.
    rewrite (repr_subrange_start origin (lower (write_range window))
      (upper (write_range window) - lower (write_range window))
      (lower bytes - lower (write_range window)) ADDRESSABLE ltac:(lia)).
    split; [lia |]. intros position POSITION. apply WRITE. lia.
Qed.

(** Pointer offsets are modular; readable windows separately rule out wrap. *)
Lemma ptrofs_add_repr : forall address offset,
  Ptrofs.add address (Ptrofs.repr offset) =
  Ptrofs.repr (Ptrofs.unsigned address + offset).
Proof.
  intros. unfold Ptrofs.add. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; [apply Ptrofs.eqm_refl |].
  apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

Lemma i64_checked_add_value : forall x y sum,
  i64_checked_add x y = Some sum -> sum = x + y.
Proof.
  intros x y sum ADD. unfold i64_checked_add in ADD.
  destruct (_ && _); inversion ADD; reflexivity.
Qed.

Lemma u64_as_i64_le : forall x, u64_as_i64 x <= x.
Proof. intros x. unfold u64_as_i64. destruct (x <? _); lia. Qed.

Lemma stack_size_lower_le : forall size, -size <= stack_size_lower size.
Proof.
  intros size. unfold stack_size_lower. destruct (size =? _) eqn:MIN.
  - apply Z.eqb_eq in MIN. lia.
  - pose proof (u64_as_i64_le size). lia.
Qed.

(** ** Checked-access properties *)

Lemma checked_write_access_shape : forall ptr offset width strict access,
  checked_write_access_for_ptr ptr offset width strict = Some access ->
  access = CheckedAccess ptr
    (Range (ptr_off_min ptr + offset) (ptr_off_max ptr + offset + width))
    (Z.eqb (ptr_off_min ptr) (ptr_off_max ptr)).
Proof.
  intros ptr offset width strict access CHECK.
  unfold checked_write_access_for_ptr, i64_checked_add in CHECK.
  destruct (permission_includes (ptr_permission ptr) Write); try discriminate.
  destruct (ptr_nullability ptr); try discriminate.
  repeat match type of CHECK with
  | context [if ?test then _ else _] =>
      destruct test eqn:?; cbn beta iota zeta in CHECK; try discriminate
  end.
  now inversion CHECK.
Qed.

Lemma exact_store_width : forall state base offset width policy access,
  checked_write_access_range state base offset width policy = Some access ->
  access_exact access = true ->
  upper (access_range access) - lower (access_range access) = width.
Proof.
  intros state base offset width policy access CHECK EXACT.
  unfold checked_write_access_range in CHECK.
  destruct (find_pointer_fact state base) as [ptr |]; try discriminate.
  apply filter_special_access_some in CHECK;
    apply filter_context_access_some in CHECK.
  apply checked_write_access_shape in CHECK. subst access.
  cbn [access_exact access_range lower upper] in EXACT |- *.
  apply Z.eqb_eq in EXACT. lia.
Qed.

(** The tracking update uses the same region and window as the accepted
    store check, despite the latter's local permission promotion. *)
Lemma resolve_checked_write : forall state base offset width policy access,
  checked_write_access_range state base offset width policy = Some access ->
  SpillProvenance.resolve_write state base offset width =
    match Region.cells (ptr_ty (access_ptr access)) with
    | Some region => Some (region,
        if access_exact access then Some (access_range access) else None)
    | None => None
    end.
Proof.
  intros state base offset width policy access CHECK.
  unfold checked_write_access_range in CHECK.
  destruct (find_pointer_fact state base) as [ptr|] eqn:FIND; try discriminate.
  apply filter_special_access_some in CHECK;
    apply filter_context_access_some in CHECK.
  unfold SpillProvenance.resolve_write. rewrite FIND.
  destruct (Region.is (ptr_ty ptr) RegionClass.CTX ||
    (negb (permission_includes (ptr_permission ptr) Write) &&
     write_window_grants policy ptr offset width)) eqn:GRANT;
    unfold checked_write_access_for_ptr, i64_checked_add in CHECK;
    cbn [with_write_permission ptr_permission ptr_nullability ptr_off_min ptr_off_max
      ptr_size ptr_ty ptr_end_min ptr_align] in CHECK;
    destruct (ptr_nullability ptr); try discriminate;
    try (destruct (permission_includes (ptr_permission ptr) Write); try discriminate).
  all: repeat match type of CHECK with
    | context [if ?test then _ else _] =>
        destruct test eqn:?; cbn beta iota zeta in CHECK; try discriminate
    end.
  all: inversion CHECK; subst access; clear CHECK;
    cbn [access_ptr access_exact access_range ptr_ty with_write_permission].
  all: destruct (Region.cells (ptr_ty ptr)); [| reflexivity].
  all: destruct (Z.eqb (ptr_off_min ptr) (ptr_off_max ptr)) eqn:EXACT;
    [apply Z.eqb_eq in EXACT; rewrite <- EXACT in * | reflexivity].
  all: unfold i64_checked_add; rewrite ?Heqb0, ?Heqb1, ?Heqb2, ?Heqb3, ?Heqb4,
      ?Heqb5, ?Heqb6; reflexivity.
Qed.

(** A register store uses the same invalidation as an immediate store, then
    adds one identity fact precisely for an exact full-width region write. *)
Lemma shared_region_has_no_cells : forall region,
  Region.contents_shared region = true -> Region.cells region = None.
Proof.
  intros region SHARED. unfold Region.contents_shared, Region.cells in *.
  destruct (Region.desc region) as [description|]; try discriminate.
  destruct (class_cells description); cbn in SHARED; discriminate || reflexivity.
Qed.

Lemma shared_write_has_no_cells : forall state base offset width policy access,
  checked_write_access_range state base offset width policy = Some access ->
  SpillProvenance.targets_shared_memory state base = true ->
  Region.cells (ptr_ty (access_ptr access)) = None.
Proof.
  intros state base offset width policy access CHECK SHARED.
  unfold checked_write_access_range in CHECK.
  unfold SpillProvenance.targets_shared_memory in SHARED.
  destruct (find_pointer_fact state base) as [ptr|]; try discriminate.
  apply filter_special_access_some in CHECK.
  apply filter_context_access_some in CHECK.
  apply checked_write_access_shape in CHECK.
  destruct (Region.is (ptr_ty ptr) RegionClass.CTX ||
    (negb (permission_includes (ptr_permission ptr) Write) &&
     write_window_grants policy ptr offset width));
    subst access; cbn [access_ptr ptr_ty with_write_permission];
    now apply shared_region_has_no_cells.
Qed.

Lemma materialize_register_store : forall state post base source offset width policy access,
  checked_write_access_range state base offset width policy = Some access ->
  SpillProvenance.materialize
    (fst (SpillProvenance.update (SpillProvenance.from_entry state) state
      (SpillProvenance.StoreReg base source offset width))) post =
  SpillProvenance.materialize
    (fst (SpillProvenance.invalidate_write (SpillProvenance.from_entry state)
      state base offset width)) post ++
  match Region.cells (ptr_ty (access_ptr access)) with
  | Some region => if access_exact access && Z.eqb width 8
      then [MemoryEq region (lower (access_range access)) source] else []
  | None => []
  end.
Proof.
  intros state post base source offset width policy access CHECK.
  cbn [SpillProvenance.update]. unfold SpillProvenance.invalidate_write.
  destruct (SpillProvenance.targets_shared_memory state base) eqn:SHARED.
  { rewrite (shared_write_has_no_cells _ _ _ _ _ _ CHECK SHARED).
    cbn [fst]. now rewrite app_nil_r. }
  rewrite (resolve_checked_write _ _ _ _ _ _ CHECK).
  destruct (Region.cells (ptr_ty (access_ptr access))) as [region|];
    destruct (access_exact access); destruct (width =? 8);
    unfold SpillProvenance.materialize;
    cbn [fst SpillProvenance.entries SpillProvenance.disturbed];
    rewrite ?map_app, ?app_assoc, ?app_nil_r; reflexivity.
Qed.

(** Materialization retains a local fact (never a local [MemoryEq]), or
    reconstructs an untouched equality from the pre-state tracking entries. *)
Lemma materialized_store_origin : forall state post base offset width policy access fact,
  checked_write_access_range state base offset width policy = Some access ->
  In fact (SpillProvenance.materialize
    (fst (SpillProvenance.invalidate_write (SpillProvenance.from_entry state)
      state base offset width)) post) ->
  (In fact post /\
    match fact with
    | MemoryEq _ _ _ => False
    | ReadableCell region start _ =>
        Region.cells (ptr_ty (access_ptr access)) <> Some region \/
        overlaps (Range start (start + 8)) (access_range access) = false
    | _ => True
    end) \/
  exists region start name,
    fact = MemoryEq region start name /\ In fact state /\
    (Region.cells (ptr_ty (access_ptr access)) <> Some region \/
      overlaps (Range start (start + 8)) (access_range access) = false).
Proof.
  intros state post base offset width policy access fact CHECK IN.
  unfold SpillProvenance.invalidate_write in IN.
  destruct (SpillProvenance.targets_shared_memory state base) eqn:SHARED.
  { pose proof (shared_write_has_no_cells _ _ _ _ _ _ CHECK SHARED) as TARGET.
    cbn [fst SpillProvenance.materialize] in IN.
    apply in_app_iff in IN as [IN|IN].
    - apply filter_In in IN as [OLD KEPT]. left. split; [exact OLD|].
      destruct fact; try exact I; try discriminate.
      left. rewrite TARGET. discriminate.
    - apply in_map_iff in IN as [item [FACT IN]].
      destruct (entry_binding_origin _ _ IN) as [region [start [name [PRE ITEM]]]].
      subst item fact. right. exists region, start, name.
      split; [reflexivity|]. split; [exact PRE|]. left. rewrite TARGET. discriminate. }
  rewrite (resolve_checked_write _ _ _ _ _ _ CHECK) in IN.
  destruct (Region.cells (ptr_ty (access_ptr access))) as [target|] eqn:TARGET;
    [destruct (access_exact access) eqn:EXACT |];
    cbn [SpillProvenance.materialize SpillProvenance.entries SpillProvenance.disturbed
      SpillProvenance.cells SpillProvenance.regions SpillProvenance.everything
      SpillProvenance.entry_bindings] in IN;
    apply in_app_iff in IN as [IN | IN].
  - apply filter_In in IN as [OLD KEPT]. left. split; [exact OLD |].
    destruct fact; try exact I; try discriminate.
    destruct (i64_checked_add offset0 8) as [finish|] eqn:ADD; try discriminate.
    apply i64_checked_add_value in ADD; subst finish.
    cbn [fst SpillProvenance.from_entry SpillProvenance.disturbed SpillProvenance.cells
      SpillProvenance.regions SpillProvenance.everything SpillProvenance.covers
      existsb] in KEPT. rewrite ?orb_false_r in KEPT.
    unfold SpillProvenance.covers in KEPT.
    cbn [SpillProvenance.cells SpillProvenance.regions SpillProvenance.everything
      app existsb fst snd] in KEPT. rewrite ?orb_false_r in KEPT.
    change (negb (Region.eqb target region &&
      overlaps (access_range access) (Range offset0 (offset0 + 8))) = true) in KEPT.
    apply negb_true_iff in KEPT. apply andb_false_iff in KEPT as [DIFFERENT | DISJOINT].
    + left. intros SAME. inversion SAME; subst region.
      rewrite region_eqb_refl in DIFFERENT. discriminate.
    + right. now rewrite overlaps_sym.
  - apply in_map_iff in IN as [item [FACT IN]].
    unfold SpillProvenance.keep_disjoint in IN.
    apply filter_In in IN as [OLD KEPT].
    destruct (entry_binding_origin _ _ OLD) as [region [start [name [PRE ITEM]]]].
    subst item fact. cbn in KEPT |- *.
    right. exists region, start, name. split; [reflexivity |]. split; [exact PRE |].
    apply negb_true_iff in KEPT. apply andb_false_iff in KEPT as [DIFFERENT | DISJOINT].
    + left. intros SAME. inversion SAME; subst region.
      rewrite region_eqb_refl in DIFFERENT. discriminate.
    + now right.
  - apply filter_In in IN as [OLD KEPT]. left. split; [exact OLD |].
    destruct fact; try exact I; try discriminate.
    destruct (i64_checked_add offset0 8); try discriminate.
    cbn [fst SpillProvenance.from_entry SpillProvenance.disturbed SpillProvenance.cells
      SpillProvenance.regions SpillProvenance.everything SpillProvenance.covers
      existsb] in KEPT. rewrite ?orb_false_r in KEPT.
    unfold SpillProvenance.covers in KEPT.
    cbn [SpillProvenance.cells SpillProvenance.regions SpillProvenance.everything
      app existsb fst snd] in KEPT. rewrite ?orb_false_r in KEPT.
    rewrite ?orb_false_l in KEPT.
    change (negb (Region.eqb region target) = true) in KEPT.
    apply negb_true_iff in KEPT.
    left. intros SAME. inversion SAME; subst region.
    rewrite region_eqb_refl in KEPT. discriminate.
  - apply in_map_iff in IN as [item [FACT IN]].
    apply filter_In in IN as [OLD KEPT].
    destruct (entry_binding_origin _ _ OLD) as [region [start [name [PRE ITEM]]]].
    subst item fact. cbn in KEPT |- *.
    right. exists region, start, name. split; [reflexivity |]. split; [exact PRE |].
    apply negb_true_iff in KEPT. left. intros SAME. inversion SAME; subst region.
    rewrite region_eqb_refl in KEPT. discriminate.
  - apply filter_In in IN as [OLD KEPT]. left. split; [exact OLD |].
    destruct fact; try exact I; try discriminate.
    destruct (i64_checked_add offset0 8); discriminate.
  - contradiction.
Qed.

Lemma checked_write_window : forall ptr offset width strict access,
  checked_write_access_for_ptr ptr offset width strict = Some access ->
  permission_includes (ptr_permission ptr) Write = true /\
  ptr_nullability ptr = NonNull /\ verified_window ptr offset width.
Proof.
  intros ptr offset width strict access CHECK.
  unfold checked_write_access_for_ptr in CHECK.
  destruct (permission_includes (ptr_permission ptr) Write) eqn:WRITE;
    try discriminate.
  destruct (ptr_nullability ptr) eqn:NULL; try discriminate.
  destruct (i64_checked_add (ptr_off_min ptr) offset) as [start |] eqn:START;
    try discriminate.
  destruct (i64_checked_add (ptr_off_max ptr) offset) as [last |] eqn:LAST;
    try discriminate.
  destruct (i64_checked_add last width) as [finish |] eqn:FINISH;
    try discriminate.
  apply i64_checked_add_value in START, LAST, FINISH. subst start last finish.
  cbn beta iota zeta in CHECK.
  destruct (_ && _) eqn:TEST; try discriminate.
  apply andb_true_iff in TEST as [BOUNDS _].
  apply andb_true_iff in BOUNDS as [LOW HIGH].
  apply Z.leb_le in LOW. apply orb_true_iff in HIGH.
  pose proof (u64_as_i64_le (ptr_size ptr)) as CAST.
  pose proof (stack_size_lower_le (ptr_size ptr)) as STACK_SIZE.
  split; [reflexivity |]. split; [reflexivity |]. split.
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

(** ** Concrete store execution *)

(** Accepted writes use either the pointer's own permissions or a concrete
    policy window. The latter changes no pointer fact in the pre-state. *)
Lemma write_window_allows_ordinary : forall world memory attrs region bytes,
  store_policy_holds world memory attrs ->
  write_window_allows attrs region bytes = true ->
  Region.probe_readable region = false.
Proof.
  intros world memory attrs region bytes POLICY GRANT.
  unfold write_window_allows in GRANT. apply existsb_exists in GRANT.
  destruct GRANT as [window [IN GRANT]].
  apply andb_true_iff in GRANT as [REGION _]. apply Region.eqb_eq in REGION.
  unfold store_policy_holds in POLICY. rewrite Forall_forall in POLICY.
  destruct (POLICY window IN) as [_ [ORDINARY _]]. now rewrite <- REGION.
Qed.

(** A pointer into a region with an address relation denotes an offset of one of
    the region's objects. *)
Lemma pointer_object : forall world ptr b address,
  pointer_address world ptr (Vptr b address) ->
  exists origin actual,
    region_object world (ptr_ty ptr) b origin /\
    pointer_offset_holds ptr actual /\
    address = Ptrofs.repr (origin + actual).
Proof.
  intros world ptr b address ADDRESS.
  unfold pointer_address, region_object in *.
  destruct (Region.cells (ptr_ty ptr)) as [region |] eqn:CELLS.
  - pose proof (Region.cells_self _ _ CELLS) as SAME. subst region.
    destruct ADDRESS as [actual [OFFSET VALUE]]. unfold region_address in VALUE.
    destruct (region_location world (ptr_ty ptr)) as [[b' origin] |] eqn:LOCATION;
      [| discriminate].
    injection VALUE as BLOCK POSITION. subst b'.
    exists origin, actual. auto.
  - destruct ADDRESS as [b' [origin [actual [ALLOCATED [OFFSET VALUE]]]]].
    injection VALUE as BLOCK POSITION. subst b'.
    exists origin, actual. auto.
Qed.

(** The kernel access kind of a checked write's pointer, which decides how
    the kernel lowers the store. *)
Definition store_access_kind (state : abstract_state) (base : var) (offset width : Z)
    (policy : store_policy) : option KernelAccess.t :=
  option_map (fun access => Region.kernel_access (ptr_ty (access_ptr access)))
    (checked_write_access_range state base offset width policy).

Lemma checked_write_access_type : forall state base ptr offset width policy access,
  find_pointer_fact state base = Some ptr ->
  checked_write_access_range state base offset width policy = Some access ->
  ptr_ty (access_ptr access) = ptr_ty ptr.
Proof.
  intros state base ptr offset width policy access FIND CHECK.
  unfold checked_write_access_range in CHECK. rewrite FIND in CHECK.
  apply filter_special_access_some in CHECK.
  apply filter_context_access_some in CHECK.
  rewrite (checked_write_access_shape _ _ _ _ _ CHECK).
  destruct (_ || _); reflexivity.
Qed.

(** A context pointer's kernel access kind is [Ctx]. *)
Lemma context_kernel_access : forall region,
  Region.is region RegionClass.CTX = true -> Region.kernel_access region = KernelAccess.Ctx.
Proof.
  intros [index key] CTX. unfold Region.is in CTX. cbn in CTX.
  apply Nat.eqb_eq in CTX. subst index. reflexivity.
Qed.

Lemma checked_write_access_permissions :
  forall world memory state base ptr value attrs offset width access,
    0 < width ->
    Region.is (ptr_ty ptr) RegionClass.CTX = false ->
    find_pointer_fact state base = Some ptr ->
    pointer_state_holds world memory ptr value ->
    store_policy_holds world memory attrs ->
    checked_write_access_range state base offset width attrs = Some access ->
    exists b address,
      value = Vptr b address /\
      let start := Ptrofs.unsigned (Ptrofs.add address (Ptrofs.repr offset)) in
      start + width <= Ptrofs.modulus /\
      Mem.range_perm memory b start (start + width) Cur Writable.
Proof.
  intros world memory state base ptr value attrs offset width access
    POS NONCTX FIND [_ [REGION [RIGHTS [NULL _]]]] POLICY CHECK.
  unfold pointer_nullability_holds in NULL.
  unfold checked_write_access_range in CHECK. rewrite FIND in CHECK.
  destruct (Region.is (ptr_ty ptr) RegionClass.CTX ||
    (negb (permission_includes (ptr_permission ptr) Write) &&
     write_window_grants attrs ptr offset width)) eqn:GRANT;
    apply filter_special_access_some in CHECK;
    apply filter_context_access_some in CHECK.
  - destruct (checked_write_window _ _ _ _ _ CHECK) as [_ [NONNULL _]].
    change (ptr_nullability ptr = NonNull) in NONNULL. rewrite NONNULL in NULL.
    rewrite NONCTX in GRANT. cbn in GRANT.
    apply andb_true_iff in GRANT as [_ GRANT].
    unfold write_window_grants in GRANT.
    destruct (i64_checked_add (ptr_off_min ptr) offset) as [start |] eqn:START;
      try discriminate.
    destruct (i64_checked_add (ptr_off_max ptr) offset) as [last |] eqn:LAST;
      try discriminate.
    destruct (i64_checked_add last width) as [finish |] eqn:FINISH;
      try discriminate.
    apply i64_checked_add_value in START, LAST, FINISH. subst start last finish.
    pose proof (write_window_allows_ordinary _ _ _ _ _ POLICY GRANT) as ORDINARY.
    assert (TYPED : Region.eqb (ptr_ty ptr) (Region.btf None) = false).
    { destruct (Region.eqb (ptr_ty ptr) (Region.btf None)) eqn:UNTYPED; [| reflexivity].
      apply Region.eqb_eq in UNTYPED. rewrite UNTYPED in ORDINARY. discriminate. }
    destruct value as [| | | | | b address]; cbn [non_null_base_pointer_holds] in NULL;
      try contradiction;
      try (destruct NULL as [PROBE _]; rewrite ORDINARY in PROBE; discriminate).
    unfold pointer_region_holds in REGION. rewrite TYPED, NONNULL in REGION.
    destruct (pointer_object _ _ _ _ REGION)
      as [origin [actual [OBJECT [[[MIN MAX] STRIDE] ADDRESS]]]].
    destruct (write_window_allows_writable world memory attrs (ptr_ty ptr)
      (Range (ptr_off_min ptr + offset) (ptr_off_max ptr + offset + width)) b origin
      POLICY GRANT ltac:(cbn; lia) OBJECT) as [_ [HIGH WRITE]].
    subst address. exists b, (Ptrofs.repr (origin + actual)). split; [reflexivity |].
    assert (SUM : Ptrofs.add (Ptrofs.repr (origin + actual)) (Ptrofs.repr offset) =
      Ptrofs.repr (origin + (ptr_off_min ptr + offset + (actual - ptr_off_min ptr)))).
    { rewrite ptrofs_add_repr. apply Ptrofs.eqm_samerepr.
      apply Ptrofs.eqm_trans with (origin + actual + offset).
      - apply Ptrofs.eqm_add;
          [apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr | apply Ptrofs.eqm_refl].
      - replace (origin + (ptr_off_min ptr + offset + (actual - ptr_off_min ptr)))
          with (origin + actual + offset) by lia.
        apply Ptrofs.eqm_refl. }
    cbn [lower upper] in HIGH, WRITE. cbv zeta in HIGH, WRITE |- *.
    rewrite SUM, (repr_subrange_start origin (ptr_off_min ptr + offset)
      (ptr_off_max ptr + offset + width - (ptr_off_min ptr + offset))
      (actual - ptr_off_min ptr) HIGH ltac:(lia)).
    split; [lia |]. intros position INSIDE. apply WRITE. lia.
  - destruct (checked_write_window _ _ _ _ _ CHECK) as [WRITE [NONNULL WINDOW]].
    rewrite NONNULL in NULL.
    unfold pointer_permissions_holds in RIGHTS. rewrite NONNULL in RIGHTS.
    pose proof (non_null_base_ordinary_value ptr value NULL (or_intror WRITE)) as NONZERO.
    assert (ACCESS_RIGHTS : pointer_access_holds memory ptr value).
    { destruct (Region.probe_readable (ptr_ty ptr)); auto. }
    destruct value; cbn [pointer_access_holds] in ACCESS_RIGHTS;
      try discriminate ACCESS_RIGHTS; try congruence.
    assert (PERMISSION :
      (match ptr_permission ptr with Read => Memtype.Readable | _ => Writable end) = Writable).
    { destruct (ptr_permission ptr); cbn [permission_includes] in WRITE;
        discriminate || reflexivity. }
    rewrite PERMISSION in ACCESS_RIGHTS.
    destruct (ACCESS_RIGHTS offset width POS WINDOW) as [END PERM].
    exists b, i. split; [reflexivity |]. split; [exact END | exact PERM].
Qed.
