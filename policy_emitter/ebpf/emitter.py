"""Generate a PolicyFile from the kernel proto descriptors.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from pdsl.ast import (
    And,
    BoolLit,
    Equality,
    Expr,
    Field,
    GlobalPredicate,
    ImmField,
    Implication,
    IntLit,
    Not,
    OpPolicy,
    OpSignature,
    Or,
    PolicyFile,
    PredicateCall,
    Reg,
    Static,
    TypeJudgment,
    Var,
)
from pdsl.parser import parse

from .ctx_emitter import build_ctx_predicates, write_debug_file
from .kfunc_emitter import build_kfunc_policies

_DATA_DIR = Path(__file__).parent.parent/ "scrapers"
_BUILTINS = Path(__file__).parent / "builtins.pol"


def _conjoin(atoms: list[Expr]) -> Expr:
    acc = atoms[0]
    for atom in atoms[1:]:
        acc = And(acc, atom)
    return acc


def _disjoin(exprs: list[Expr]) -> Expr:
    acc = exprs[0]
    for expr in exprs[1:]:
        acc = Or(acc, expr)
    return acc


def _add_var(policy: OpPolicy, name: str) -> None:
    if name not in policy.exists:
        policy.exists.append(name)


def _mem_size_var(size_reg: int) -> Var:
    """The byte count of the ARG_PTR_TO_MEM buffer sized by register `size_reg`.

    The kernel pairs each buffer with the argument right after it, and a helper
    may take several pairs (`bpf_csum_diff`), so each size is its own variable.
    """
    return Var(f"size_r{size_reg}")


def _stack_written_post(policy: OpPolicy, reg: int, size) -> None:
    """Post for a MEM_WRITE arg: the pointed-to stack region is initialized.

    `stack_bytes_written` constrains the post-state stack against the pre-state
    one, so bind `prev_stack = STACK` (once) in the preconditions.
    """
    if "prev_stack" not in policy.exists:
        policy.exists.append("prev_stack")
        policy.pre.append(Equality(Var("prev_stack"), Var("STACK")))
    r = Reg(reg)
    policy.post.append(
        Implication(
            TypeJudgment(r, "PTR_TO_STACK"),
            PredicateCall(
                "stack_bytes_written",
                [Field(r, "offset"), size, Var("prev_stack")],
            ),
        )
    )


# --- Argument-type emitters ------------------------------------------------


def emit_typed_ptr_pre(
    policy: OpPolicy,
    reg: int,
    base_type: str,
    check: Expr | None,
    maybe_null: bool,
) -> None:
    """Append the typed-pointer precondition(s), honouring PTR_MAYBE_NULL.

    `check` is the additional constraint on the pointer, or `None` for a type
    whose judgment is the whole requirement (e.g. the context pointer).

    Non-null shape (two atoms):
        r : <base_type>
        <check>
    Maybe-null shape (one disjunction):
        (r : INT && r.value = 0) || (r : <base_type>_OR_NULL && <check>)
    """
    r = Reg(reg)
    if maybe_null:
        judgment = TypeJudgment(r, f"{base_type}_OR_NULL")
        policy.pre.append(Or(
            And(TypeJudgment(r, "INT"), Equality(Field(r, "value"), IntLit(0))),
            judgment if check is None else And(judgment, check),
        ))
    else:
        policy.pre.append(TypeJudgment(r, base_type))
        if check is not None:
            policy.pre.append(check)


def arg_const_map_ptr(policy: OpPolicy, arg: dict, reg: int, pkt_access: bool) -> None:
    r = Reg(reg)
    policy.pre.append(TypeJudgment(r, "CONST_PTR_TO_MAP"))
    # map_ptr/map_uid are local vars; further equalities must stay consistent.
    policy.pre.append(Equality(Var("map_ptr"), Field(r, "map_ptr")))
    policy.pre.append(Equality(Var("map_uid"), Field(r, "map_uid")))
    _add_var(policy, "map_ptr")
    _add_var(policy, "map_uid")


def arg_ptr_to_map_key(policy: OpPolicy, arg: dict, reg: int, pkt_access: bool) -> None:
    r = Reg(reg)
    policy.pre.append(TypeJudgment(r, "HELPER_MEM"))
    policy.pre.append(
        PredicateCall(
            "check_helper_mem_access",
            [r, Static("map_ptr->key_size"), BoolLit(False), BoolLit(False), BoolLit(False), BoolLit(pkt_access)],
        )
    )
    _add_var(policy, "map_ptr")

# PTR_MAYBE_NULL: either the pointer is of type INT and 0, or it has the type HELPER_MEM with or without PTR_MAYBE_NULL.
# MEM_WRITE: writable memory in precondition, afterwards the region is initialized
# MEM_UNINIT:
def arg_ptr_to_map_value(policy: OpPolicy, arg: dict, reg: int, pkt_access: bool) -> None:
    r = Reg(reg)
    flags = arg["flags"]
    writeable = "MEM_WRITE" in flags
    not_initialized = "MEM_UNINIT" in flags
    check = PredicateCall(
        "check_helper_mem_access",
        [r, Static("map_ptr->value_size"), BoolLit(writeable), BoolLit(False), BoolLit(not_initialized), BoolLit(pkt_access)],
    )
    emit_typed_ptr_pre(policy, reg, "HELPER_MEM", check, "PTR_MAYBE_NULL" in flags)
    _add_var(policy, "map_ptr")

    if writeable:
        _stack_written_post(policy, reg, Static("map_ptr->value_size"))

def arg_ptr_to_btf_id(policy: OpPolicy, arg: dict, reg: int, pkt_access: bool) -> None:
    flags = arg["flags"]
    release = "OBJ_RELEASE" in flags

    _add_var(policy, "btf_id")
    # As btf_ids are assigned only at kernel/module load time, we store the name of the struct
    # and query for the actual id at verification time.
    policy.pre.append(Equality(Var("btf_id"), Static(f"get_btf_id({arg['btf']})")))

    # btf_struct_ids_match(reg_btf_id, reg_offset, expected_btf_id, strict_type_match)
    check = PredicateCall(
        "btf_struct_ids_match",
        [Field(Reg(reg), "btf_id"), Field(Reg(reg), "offset"), Var("btf_id"), BoolLit(release)],
    )
    emit_typed_ptr_pre(policy, reg, "PTR_TO_BTF_ID", check, "PTR_MAYBE_NULL" in flags)

    # Release/acquire semantics are not fully supported yet
    if release:
        policy.pre.append(Not(Equality(Static(f"R{reg}.ref_obj_id"), IntLit(0))))
        policy.pre.append(Equality(Static(f"R{reg}.offset"), IntLit(0)))


def arg_ptr_to_btf_id_sock_common(
    policy: OpPolicy, arg: dict, reg: int, pkt_access: bool
) -> None:
    """Emit the kernel's sock-common-compatible BTF pointer category."""
    check = PredicateCall("btf_sock_common", [Reg(reg)])
    emit_typed_ptr_pre(
        policy,
        reg,
        "PTR_TO_BTF_ID_SOCK_COMMON",
        check,
        "PTR_MAYBE_NULL" in arg["flags"],
    )


def arg_anything(policy: OpPolicy, arg: dict, reg: int, pkt_access: bool) -> None:
    policy.pre.append(TypeJudgment(Reg(reg), "INT"))


def arg_ptr_to_ctx(policy: OpPolicy, arg: dict, reg: int, pkt_access: bool) -> None:
    # The context pointer is the program's entry argument; the helper requires it
    # be the unadjusted program-type ctx. The type judgment is the whole
    # requirement, so there is no additional check. ARG_PTR_TO_CTX_OR_NULL
    # (bpf_get_netns_cookie) additionally admits a NULL argument.
    emit_typed_ptr_pre(
        policy, reg, "PTR_TO_CTX", None, "PTR_MAYBE_NULL" in arg["flags"]
    )

def arg_ptr_to_mem(policy: OpPolicy, arg: dict, reg: int, pkt_access: bool) -> None:
    r = Reg(reg)
    flags = arg["flags"]
    maybe_null = "PTR_MAYBE_NULL" in flags

    writeable = "MEM_WRITE" in flags
    not_initialized = "MEM_UNINIT" in flags
    size = _mem_size_var(reg + 1)
    _add_var(policy, size.name)

    # zero_size_allowed is the size arg's concern; it forbids size==0 when needed,
    # so the region check can pass it as already-allowed here.
    check = PredicateCall(
        "check_helper_mem_access",
        [r, size, BoolLit(writeable), BoolLit(True), BoolLit(not_initialized), BoolLit(pkt_access)],
    )
    emit_typed_ptr_pre(policy, reg, "HELPER_MEM", check, maybe_null)

    if writeable:
        _stack_written_post(policy, reg, size)


def arg_const_size(policy: OpPolicy, arg: dict, reg: int, pkt_access: bool) -> None:
    r = Reg(reg)
    zero_ok = arg["base"] == "ARG_CONST_SIZE_OR_ZERO"
    policy.pre.append(PredicateCall("check_mem_size", [r, BoolLit(zero_ok)]))
    size = _mem_size_var(reg)
    policy.pre.append(Equality(size, Field(r, "value")))
    _add_var(policy, size.name)


def arg_const_alloc_size(policy: OpPolicy, arg: dict, reg: int, pkt_access: bool) -> None:
    # ARG_CONST_ALLOC_SIZE_OR_ZERO: the register must hold one known constant
    # (the kernel rejects unknown or variable sizes); the value sizes the
    # region an allocating helper returns (e.g. bpf_ringbuf_reserve).
    r = Reg(reg)
    policy.pre.append(PredicateCall("check_alloc_size", [r, BoolLit(True)]))
    size = Var("alloc_size")
    policy.pre.append(Equality(size, Field(r, "value")))
    _add_var(policy, size.name)


def arg_ptr_to_ringbuf_mem(policy: OpPolicy, arg: dict, reg: int, pkt_access: bool) -> None:
    # A ring-buffer reservation pointer (kernel: PTR_TO_MEM | MEM_RINGBUF).
    # The kernel requires the unadjusted pointer; with OBJ_RELEASE the call
    # consumes the reservation's reference.
    r = Reg(reg)
    policy.pre.append(TypeJudgment(r, "PTR_TO_RINGBUF_MEM"))
    policy.pre.append(Equality(Field(r, "offset"), IntLit(0)))
    if "OBJ_RELEASE" in arg["flags"]:
        policy.pre.append(PredicateCall("releases_reference", [r]))


def arg_ptr_to_spin_lock(policy: OpPolicy, arg: dict, reg: int, pkt_access: bool) -> None:
    # The kernel additionally requires the pointed-to map value's BTF to place
    # a struct bpf_spin_lock at this exact offset; that structural check is not
    # yet modeled, so the judgment is informational for now.
    policy.pre.append(TypeJudgment(Reg(reg), "PTR_TO_SPIN_LOCK"))


def arg_ptr_to_func(policy: OpPolicy, arg: dict, reg: int, pkt_access: bool) -> None:
    policy.pre.append(TypeJudgment(Reg(reg), "PTR_TO_FUNC"))


def arg_ptr_to_stack(policy: OpPolicy, arg: dict, reg: int, pkt_access: bool) -> None:
    # ARG_PTR_TO_STACK appears only with PTR_MAYBE_NULL (nullable ctx pointer for
    # callback helpers like bpf_loop). The full nullable disjunction would produce an
    # Or-clause that the helper catalog parser cannot handle, so we emit a plain
    # TypeJudgment instead. policy.json is consumed exclusively by the catalog, which
    # ignores all non-CONST_PTR_TO_MAP TypeJudgments; the nullable distinction has no
    # effect on the generated HelperSpec.
    policy.pre.append(TypeJudgment(Reg(reg), "PTR_TO_STACK"))


ARG_EMITTERS = {
    "ARG_CONST_MAP_PTR": arg_const_map_ptr,
    "ARG_PTR_TO_MAP_KEY": arg_ptr_to_map_key,
    "ARG_PTR_TO_MAP_VALUE": arg_ptr_to_map_value,
    "ARG_PTR_TO_BTF_ID": arg_ptr_to_btf_id,
    "ARG_PTR_TO_BTF_ID_SOCK_COMMON": arg_ptr_to_btf_id_sock_common,
    "ARG_PTR_TO_MEM": arg_ptr_to_mem,
    "ARG_CONST_SIZE": arg_const_size,
    "ARG_CONST_SIZE_OR_ZERO": arg_const_size,
    "ARG_CONST_ALLOC_SIZE_OR_ZERO": arg_const_alloc_size,
    "ARG_PTR_TO_RINGBUF_MEM": arg_ptr_to_ringbuf_mem,
    "ARG_PTR_TO_SPIN_LOCK": arg_ptr_to_spin_lock,
    "ARG_ANYTHING": arg_anything,
    "ARG_PTR_TO_CTX": arg_ptr_to_ctx,
    "ARG_PTR_TO_FUNC": arg_ptr_to_func,
    "ARG_PTR_TO_STACK": arg_ptr_to_stack,
    "ARG_DONTCARE": lambda policy, arg, reg, pkt_access: None,
}

# Argument types whose emitter models OBJ_RELEASE itself (a `releases_reference`
# clause); any other argument carrying OBJ_RELEASE stays unsupported.
RELEASE_CAPABLE_ARGS = frozenset({"ARG_PTR_TO_RINGBUF_MEM"})


# --- Return-type emitters --------------------------------------------------


def ret_ptr_to_map_value(policy: OpPolicy, ret: dict) -> None:
    r = Reg(0)
    if "PTR_MAYBE_NULL" in ret["flags"]:
        policy.post.append(TypeJudgment(r, "PTR_TO_MAP_VALUE_OR_NULL"))
    else:
        policy.post.append(TypeJudgment(r, "PTR_TO_MAP_VALUE"))
    policy.post.append(Equality(Field(r, "map_ptr"), Var("map_ptr")))
    policy.post.append(Equality(Field(r, "map_uid"), Var("map_uid")))
    policy.post.append(Equality(Field(r, "offset"), IntLit(0)))


def ret_integer(policy: OpPolicy, ret: dict) -> None:
    r = Reg(0)
    policy.post.append(TypeJudgment(r, "INT"))


def ret_void(policy: OpPolicy, ret: dict) -> None:
    # A void helper still clobbers r0; the kernel marks it uninitialized. The
    # judgment records that no value contract exists, so consumers must treat
    # the destination as unconstrained.
    r = Reg(0)
    policy.post.append(TypeJudgment(r, "VOID"))


def ret_ptr_to_mem(policy: OpPolicy, ret: dict) -> bool:
    # Only the ring-buffer reservation shape (MEM_RINGBUF, optionally maybe
    # null) is modeled: the returned region spans the alloc-size argument and
    # the call acquires the reservation's reference. Other RET_PTR_TO_MEM
    # flavors stay unsupported.
    flags = set(ret["flags"])
    if not flags <= {"MEM_RINGBUF", "PTR_MAYBE_NULL"}:
        return False
    if "MEM_RINGBUF" not in flags:
        return False
    if "alloc_size" not in policy.exists:
        return False
    r = Reg(0)
    suffix = "_OR_NULL" if "PTR_MAYBE_NULL" in flags else ""
    policy.post.append(TypeJudgment(r, f"PTR_TO_RINGBUF_MEM{suffix}"))
    policy.post.append(Equality(Field(r, "size"), Var("alloc_size")))
    policy.post.append(PredicateCall("acquires_reference", [r]))
    return True


def ret_ptr_to_btf_id(policy: OpPolicy, ret: dict) -> None:
    # An opaque BTF-typed kernel pointer. The judgment carries the type name so
    # consumers may later model typed loads; current consumers treat the value
    # as initialized but unconstrained.
    r = Reg(0)
    suffix = "_OR_NULL" if "PTR_MAYBE_NULL" in ret["flags"] else ""
    policy.post.append(TypeJudgment(r, f"PTR_TO_BTF_ID{suffix}"))
    if "btf" in ret:
        policy.post.append(
            Equality(Field(r, "btf_id"), Static(f"get_btf_id({ret['btf']})"))
        )


# Return emitters may return False to mark the shape unsupported (a plain None
# return means success).
RET_EMITTERS = {
    "RET_PTR_TO_MAP_VALUE": ret_ptr_to_map_value,
    "RET_INTEGER": ret_integer,
    "RET_VOID": ret_void,
    "RET_PTR_TO_MEM": ret_ptr_to_mem,
    "RET_PTR_TO_BTF_ID": ret_ptr_to_btf_id,
}


# --- Map-type compatibility --------------------------------------------------


def load_kernel_protos(data_dir: Path) -> list[dict]:
    """The helper protos. `check_provenance` rejects the older bare-list shape."""
    return json.loads((data_dir / "kernel_proto_descriptors.json").read_text())["protos"]


# Descriptor files that carry a `provenance` stamp naming the kernel image they
# were scraped from. They must all name the same one: a policy assembled from
# two kernels describes neither, which is exactly the bug that moving the
# scrapers off the running kernel was meant to fix.
_PROVENANCED = (
    "kernel_proto_descriptors.json",
    "kfunc_descriptors.json",
    "struct_ops_descriptors.json",
)


def check_provenance(data_dir: Path) -> None:
    """Fails when the scraped inputs did not come from one kernel build."""
    seen: dict[str, str] = {}
    for name in _PROVENANCED:
        path = data_dir / name
        if not path.exists():
            continue
        stamp = json.loads(path.read_text())
        if not isinstance(stamp, dict) or "provenance" not in stamp:
            raise ValueError(
                f"{name} carries no provenance stamp; re-run its scraper against "
                "the vendored kernel build"
            )
        build = stamp["provenance"].get("build_id", "unknown")
        seen[name] = build
    builds = set(seen.values())
    if len(builds) > 1:
        detail = ", ".join(f"{n}={b[:12]}" for n, b in sorted(seen.items()))
        raise ValueError(
            f"scraped inputs come from different kernel builds ({detail}); "
            "re-run the scrapers against one `just linux-build` output"
        )


def load_map_compat(data_dir: Path) -> tuple[list[int], dict[int, set[int]], dict[int, set[int]]]:
    """Load helper_map_compat.json into numeric form.

    Returns `(all_types, reserved, requires)`: every kernel map type number,
    the reserved map types' allowed func ids (switch #1 of the kernel's
    `check_map_func_compatibility`), and the restricted helpers' accepted map
    types (switch #2).
    """
    d = json.loads((data_dir / "helper_map_compat.json").read_text())
    map_types = d["map_types"]
    func_ids = d["func_ids"]
    all_types = sorted(set(map_types.values()))
    reserved: dict[int, set[int]] = {}
    for type_name, funcs in d["map_allows_funcs"].items():
        reserved.setdefault(map_types[type_name], set()).update(func_ids[f] for f in funcs)
    requires = {
        func_ids[f]: {map_types[t] for t in types}
        for f, types in d["func_requires_types"].items()
    }
    return all_types, reserved, requires


def load_pkt_changing(data_dir: Path) -> tuple[frozenset[int], frozenset[str]]:
    """Load pkt_changing.json: the helper ids and kfunc names after which the
    kernel invalidates every packet pointer (`clear_all_pkt_pointers`)."""
    d = json.loads((data_dir / "pkt_changing.json").read_text())
    return frozenset(d["helpers"].values()), frozenset(d["kfuncs"])


def allowed_map_types(func_id: int, map_compat) -> list[int]:
    """Map types `func_id` may take: both directions of the kernel check pass."""
    all_types, reserved, requires = map_compat
    return [
        t
        for t in all_types
        if (t not in reserved or func_id in reserved[t])
        and (func_id not in requires or t in requires[func_id])
    ]


# --- Access predicate ------------------------------------------------------


def helper_access_predicate(
    proto_name: str,
    docs_helper_callers: dict,
    probed_proto_callers: dict,
) -> GlobalPredicate | None:
    """Build the `<proto>_access_check` predicate, or None if no callers."""
    probed = probed_proto_callers.get(proto_name)
    if probed is None or not probed.get("prog_types"):
        return None

    docs_by_pt: dict[str, dict] = {}
    for entry in docs_helper_callers.get(probed.get("func_name", ""), []):
        full = entry.get("program", "")
        if full.startswith("BPF_PROG_TYPE_"):
            docs_by_pt[full[len("BPF_PROG_TYPE_") :]] = entry

    disjuncts: list[Expr] = []
    for short_pt in sorted(set(probed["prog_types"])):
        entry = docs_by_pt.get(short_pt, {})
        attach_types = entry.get("attach_type") or [None]
        caps = entry.get("cap") or [None]
        kconfigs = entry.get("kconfig") or []
        for at in attach_types:
            for cap in caps:
                conj: list[Expr] = [
                    Equality(Var("PROG_TYPE"), Var(f"BPF_PROG_TYPE_{short_pt}"))
                ]
                if at is not None:
                    conj.append(Equality(Var("ATTACH_TYPE"), Var(at)))
                if cap is not None:
                    conj.append(PredicateCall("CAPABILITY", [Var(cap)]))
                conj.extend(PredicateCall("KCONFIG", [Var(k)]) for k in kconfigs)
                disjuncts.append(_conjoin(conj))

    return GlobalPredicate(
        name=f"{proto_name}_access_check",
        params=[],
        body=_disjoin(disjuncts),
    )


# --- Top-level build -------------------------------------------------------


def build_policy_file(data_dir: Path | None = None) -> PolicyFile:
    """Read the kernel proto JSONs and assemble a PolicyFile.

    Predicates and op policies from `builtins.pol` are loaded first, then
    merged with the helper policies derived from the kernel descriptors.
    """
    data_dir = data_dir or _DATA_DIR
    builtins = parse(_BUILTINS.read_text())
    predicates: list[GlobalPredicate] = list(builtins.predicates)
    policies: list[OpPolicy] = list(builtins.policies)

    # PTR_TO_CTX access predicates: merged into this file and dumped standalone.
    ctx_predicates = build_ctx_predicates(data_dir)
    predicates.extend(ctx_predicates)
    write_debug_file(ctx_predicates)

    probed = json.loads((data_dir / "probed_proto_callers.json").read_text())
    docs = json.loads((data_dir / "docs_helper_callers.json").read_text())
    kernel_protos = load_kernel_protos(data_dir)
    map_compat = load_map_compat(data_dir)
    pkt_changing_helpers, pkt_changing_kfuncs = load_pkt_changing(data_dir)
    check_provenance(data_dir)

    # Protos that share a func_id are prog-type-specialised overloads of a single
    # BPF_CALL; collect them per func_id, then merge each group below.
    helper_variants: dict[int, list[tuple[OpPolicy, Expr | None]]] = {}
    for helper in kernel_protos:
        policy = OpPolicy(comment=helper["name"])
        policy.post.append(PredicateCall("scratch", []))

        translation_ready = True
        for i, arg in enumerate(helper["args"]):
            emitter = ARG_EMITTERS.get(arg["base"])
            # OBJ_RELEASE is supported only for argument types whose emitter
            # models the release itself; MEM_FIXED_SIZE not yet supported.
            if (
                emitter is None
                or ("OBJ_RELEASE" in arg["flags"] and arg["base"] not in RELEASE_CAPABLE_ARGS)
                or "MEM_FIXED_SIZE" in arg["flags"]
            ):
                translation_ready = False
                break
            emitter(policy, arg, i + 1, helper.get("pkt_access", False))

        ret_emitter = RET_EMITTERS.get(helper["ret"]["base"])
        if ret_emitter is None:
            translation_ready = False
        elif translation_ready:
            # A ret emitter may reject an unsupported flag combination.
            if ret_emitter(policy, helper["ret"]) is False:
                translation_ready = False

        if not translation_ready:
            continue

        func_id = helper.get("func_id")
        if func_id is None:
            print(
                f"warning: no func id for {helper['name']}; skipping call policy",
                file=sys.stderr,
            )
            continue
        policy.signature = OpSignature(
            opcode=0x85, src=ImmField(0x0), imm=ImmField(func_id)
        )
        if func_id in pkt_changing_helpers:
            policy.post.append(PredicateCall("changes_pkt_data", []))

        # Map arguments carry the kernel's helper/map-type compatibility
        # relation (check_map_func_compatibility): the passed map's type must
        # be one of the listed numbers.
        for i, arg in enumerate(helper["args"]):
            if arg["base"] == "ARG_CONST_MAP_PTR":
                policy.pre.append(
                    PredicateCall(
                        "map_type_in",
                        [Reg(i + 1)]
                        + [IntLit(t) for t in allowed_map_types(func_id, map_compat)],
                    )
                )

        # TODO: omit the predicate if all configurations have access
        access_pred = helper_access_predicate(helper["name"], docs, probed)
        guard: Expr | None = None
        if access_pred is not None:
            predicates.append(access_pred)
            guard = PredicateCall(access_pred.name, [])
        else:
            print(
                f"warning: no access predicate for {helper['name']}",
                file=sys.stderr,
            )
        helper_variants.setdefault(func_id, []).append((policy, guard))

    # One variant: keep its access check as a plain precondition. Several: merge
    # into a single policy, each variant's conditions gated by its access check
    # plus a disjunction guard requiring some variant be selected (soundness:
    # otherwise an unmodelled context would pass vacuously). A missing access
    # predicate makes a variant ungated, so such groups are emitted separately.
    for func_id, variants in helper_variants.items():
        if len(variants) == 1:
            policy, guard = variants[0]
            if guard is not None:
                policy.pre.append(guard)
            policies.append(policy)
        elif all(guard is not None for _, guard in variants):
            policies.append(OpPolicy.merge_guarded(variants))
        else:
            print(
                f"warning: cannot merge overloads for func id {func_id} "
                "(missing access predicate); emitting separately",
                file=sys.stderr,
            )
            for policy, guard in variants:
                if guard is not None:
                    policy.pre.append(guard)
                policies.append(policy)

    # Skip kfuncs already hand-written as kfunc-call (src=2) op policies in builtins.
    builtin_kfunc_imms = frozenset(
        p.signature.imm.value
        for p in builtins.policies
        if p.signature is not None
        and isinstance(p.signature.src, ImmField)
        and p.signature.src.value == 0x2
        and isinstance(p.signature.imm, ImmField)
    )
    # A kfunc's map-pointer argument is unconstrained by map type, so it lists the
    # whole set the helper compatibility scrape knows about.
    all_map_types, _, _ = map_compat
    policies.extend(
        build_kfunc_policies(data_dir, builtin_kfunc_imms, all_map_types, pkt_changing_kfuncs)
    )

    return PolicyFile(
        predicates=predicates,
        prologue=builtins.prologue,
        policies=policies,
    )
