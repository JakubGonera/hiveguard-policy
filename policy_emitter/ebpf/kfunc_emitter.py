"""Generate kfunc-call op policies from the scraped kfunc descriptors.

A kfunc call is BPF_JMP|BPF_CALL with src=BPF_PSEUDO_KFUNC_CALL (0x2) and imm =
the kfunc's BTF id. Unlike a helper's func_id (a stable enum), that BTF id is
assigned at kernel/module load and changes per build, so it cannot key a policy
on its own. Each policy therefore PINS the scraped id in the signature (concrete
dispatch) and re-validates it with the precondition `imm = $get_btf_id(<name>)$`,
which re-resolves the id from the kfunc name at verification time. If the build
shifts the id, the pinned signature stops selecting this call and the drift-guard
flags a stale snapshot instead of silently mis-binding to the wrong kfunc.

Arguments are translated by an extensible classifier (the seed of the verifier's
get_kfunc_ptr_arg_type) that assigns each parameter a role: scalar; a trusted BTF-id
pointer to a vetted plain kernel object (_ALLOW_BTF_STRUCTS, required for
KF_TRUSTED_ARGS/KF_RCU kfuncs); a `void*`/scalar-pointer + `__sz` size pair
(mem_size, checked read+write via check_helper_mem_access); or `__ign` (verifier-
skipped, no obligation). A return is scalar, void, or a struct pointer (R0 becomes a
known-zero PTR_TO_BTF_ID of the return type, or PTR_TO_BTF_ID_OR_NULL under
KF_RET_NULL); acquire/iter pointer returns are out of scope (ref/iterator state). The
role dispatch (ROLE_EMITTERS) mirrors the helper emitter so more classes slot in later.

Soundness is enforced two ways and we never emit an undischarged hole: a kfunc we
cannot fully model -- a name-keyed special routine, a non-modelled arg, a non-scalar
return, an unmodelled flag, a non-vmlinux BTF, or a hook with no predicate -- is
skipped entirely; and where the kernel accepts more than we model (the rcu-protected
pointer arm of a KF_RCU arg) we emit the strictly-more-restrictive obligation
(require PTR_TO_BTF_ID_TRUSTED) rather than holing the unmodelled case.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

from pdsl.ast import (
    And,
    BoolLit,
    Equality,
    Expr,
    Field,
    ImmField,
    IntLit,
    OpPolicy,
    OpSignature,
    Or,
    PredicateCall,
    Reg,
    Static,
    TypeJudgment,
    Var,
)

_DATA_DIR = Path(__file__).parent.parent / "scrapers"

_SCALAR_TYPES = frozenset({
    "bool", "char", "short", "int", "long", "long long",
    "s8", "s16", "s32", "s64", "u8", "u16", "u32", "u64",
    "__s8", "__s16", "__s32", "__s64", "__u8", "__u16", "__u32", "__u64",
    "size_t", "unsigned int", "unsigned long", "unsigned long long",
    "__be16", "__be32", "__le16", "__le32",
})

# A `struct X *` kfunc argument is modelled as a trusted BTF-id pointer only when X
# is on this allowlist. Each entry is a vetted plain kernel object: never a program
# context type (mis-typing one as PTR_TO_BTF_ID would be unsound), never a special
# verifier struct (bpf_dynptr/bpf_iter_*/bpf_list_*/bpf_rb_*/bpf_wq/...), and never
# a by-value `__sz` memory/opts struct. Extend it only with structs verified to be
# trusted BTF-id objects; an unlisted struct arg conservatively skips the kfunc.
_ALLOW_BTF_STRUCTS = frozenset({
    "cpumask", "bpf_cpumask", "task_struct", "sock", "sock_common", "tcp_sock",
    "cgroup", "cgroup_subsys_state", "file", "dentry", "path", "bpf_key",
    "xfrm_state", "Qdisc", "bpf_crypto_ctx", "mm_struct",
})

# A BTF-id pointer argument is only sound to model when the kfunc requires its
# pointer args to be trusted or rcu-protected; otherwise the accepted provenance is
# wider than PTR_TO_BTF_ID_TRUSTED and we skip the kfunc.
_TRUSTED_FLAGS = frozenset({"KF_TRUSTED_ARGS", "KF_RCU"})

# Structs a `struct X *` argument models as a plain map pointer rather than a BTF-id
# pointer. `struct bpf_map *` is the only one: the kernel lists CONST_PTR_TO_MAP in
# reg2btf_ids, so a map pointer loaded by `ld_imm64` satisfies such an argument and
# counts as trusted (`is_trusted_reg`). That is also the only provenance a BPF
# program has for one, so requiring CONST_PTR_TO_MAP is no weaker than the kernel.
# The kernel puts no map-type condition on a kfunc argument, so the emitted
# `map_type_in` lists every map type.
_MAP_PTR_STRUCTS = frozenset({"bpf_map"})

# kernel BTF_KFUNC_HOOK_* -> the builtins.pol hook predicate gating it. FMODRET is
# intentionally absent: it is selected from the attach type, which the scraper's
# prog_type_to_hook regex does not capture, so a kfunc reachable only through it is
# skipped rather than modelled with a wrong predicate.
_HOOK_PREDICATE = {
    "BTF_KFUNC_HOOK_COMMON": "hook_common",
    "BTF_KFUNC_HOOK_XDP": "hook_xdp",
    "BTF_KFUNC_HOOK_TC": "hook_tc",
    "BTF_KFUNC_HOOK_STRUCT_OPS": "hook_struct_ops",
    "BTF_KFUNC_HOOK_TRACING": "hook_tracing",
    "BTF_KFUNC_HOOK_SYSCALL": "hook_syscall",
    "BTF_KFUNC_HOOK_CGROUP": "hook_cgroup",
    "BTF_KFUNC_HOOK_SCHED_ACT": "hook_sched_act",
    "BTF_KFUNC_HOOK_SK_SKB": "hook_sk_skb",
    "BTF_KFUNC_HOOK_SOCKET_FILTER": "hook_socket_filter",
    "BTF_KFUNC_HOOK_LWT": "hook_lwt",
    "BTF_KFUNC_HOOK_NETFILTER": "hook_netfilter",
    "BTF_KFUNC_HOOK_KPROBE": "hook_kprobe",
}

# KF_* flags we can model: the call-level gates (sleepable/destructive), the
# pointer-arg trust requirements (_TRUSTED_FLAGS, consumed by arg_btf_id), and
# KF_RET_NULL (a maybe-null pointer return, consumed by ret_btf_id). Any other flag
# (acquire/release/iter/...) means the contract is not captured -> skip.
_MODELLED_FLAGS = frozenset({"KF_SLEEPABLE", "KF_DESTRUCTIVE", "KF_RET_NULL"}) | _TRUSTED_FLAGS


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


# --- Argument / return classification & emitters ---------------------------


def _base_struct(ty: str) -> str | None:
    m = re.match(r"^(?:const\s+)?struct\s+(\w+)\s*\*+$", ty.strip())
    return m.group(1) if m else None


def _is_dyn_size(param: dict) -> bool:
    # A `__sz` (dynamic) scalar size operand. `__szk` (constant size) is not handled
    # yet -- a const-size kfunc falls through to a skip rather than a looser model.
    return param["name"].endswith("__sz") and param["type"] in _SCALAR_TYPES


def _classify_params(params: list[dict]) -> list[str] | None:
    """Assign each parameter a role, or return None if any is unmodelled (-> skip).

    Roles: scalar; btf_id (allowlisted trusted/rcu object); map_ptr (a
    `struct bpf_map *`, which a program holds as CONST_PTR_TO_MAP); ign (`__ign`,
    verifier-skipped); mem_size (a pointer whose next param is a `__sz` size); size
    (that consumed size operand). Lookahead pairs a mem pointer with its size operand.
    """
    n = len(params)
    roles: list[str | None] = [None] * n
    for i, p in enumerate(params):
        if roles[i] == "size":
            continue
        name, ty = p["name"], p["type"]
        if name.endswith("__ign"):
            roles[i] = "ign"
        elif "*" in ty:
            if i + 1 < n and _is_dyn_size(params[i + 1]):
                roles[i], roles[i + 1] = "mem_size", "size"
            elif "__" not in name and _base_struct(ty) in _MAP_PTR_STRUCTS:
                roles[i] = "map_ptr"
            elif "__" not in name and _base_struct(ty) in _ALLOW_BTF_STRUCTS:
                roles[i] = "btf_id"
            else:
                return None
        elif "__" in name:
            return None
        elif ty in _SCALAR_TYPES:
            roles[i] = "scalar"
        else:
            return None
    return roles  # type: ignore[return-value]


def arg_scalar(policy: OpPolicy, params: list[dict], idx: int) -> None:
    policy.pre.append(TypeJudgment(Reg(idx + 1), "INT"))


def arg_ign(policy: OpPolicy, params: list[dict], idx: int) -> None:
    # `__ign`: the verifier skips this argument entirely, so it carries no obligation.
    pass


def arg_btf_id(policy: OpPolicy, params: list[dict], idx: int) -> None:
    reg = idx + 1
    struct = _base_struct(params[idx]["type"])
    idvar = f"{struct}_id"
    if idvar not in policy.exists:
        policy.exists.append(idvar)
        policy.pre.append(Equality(Var(idvar), Static(f"get_btf_id({struct})")))
    # KF_TRUSTED_ARGS and KF_RCU both accept a trusted pointer; KF_RCU additionally
    # accepts an rcu-protected (MEM_RCU) one, which we do not model. We require
    # PTR_TO_BTF_ID_TRUSTED strictly -- rcu-only pointers are rejected, not holed.
    policy.pre.append(TypeJudgment(Reg(reg), "PTR_TO_BTF_ID_TRUSTED"))
    policy.pre.append(Static(f"btf_struct_ids_match(R{reg}.btf_id, R{reg}.offset, {idvar}, False)"))


def arg_map_ptr(
    policy: OpPolicy, params: list[dict], idx: int, all_map_types: list[int]
) -> None:
    # A `struct bpf_map *` argument. The only way a program holds one is the
    # `ld_imm64` map pointer the kernel types CONST_PTR_TO_MAP, which reg2btf_ids
    # resolves to `struct bpf_map` and `is_trusted_reg` treats as trusted; so
    # requiring CONST_PTR_TO_MAP is no weaker than the kernel's own check. Unlike a
    # helper's ARG_CONST_MAP_PTR there is no compatibility relation to consult: a
    # kfunc constrains no map type, so every type is listed.
    reg = Reg(idx + 1)
    policy.pre.append(TypeJudgment(reg, "CONST_PTR_TO_MAP"))
    policy.pre.append(
        PredicateCall("map_type_in", [reg] + [IntLit(t) for t in all_map_types])
    )


def arg_mem_size(policy: OpPolicy, params: list[dict], idx: int) -> None:
    buf, size_reg = idx + 1, idx + 2
    size = Var(f"mem_size{buf}")
    if size.name not in policy.exists:
        policy.exists.append(size.name)
    policy.pre.append(PredicateCall("check_mem_size", [Reg(size_reg), BoolLit(True)]))
    policy.pre.append(Equality(size, Field(Reg(size_reg), "value")))
    r = Reg(buf)
    policy.pre.append(TypeJudgment(r, "HELPER_MEM"))
    # check_mem_reg checks the region for BOTH read and write (kfunc mem is
    # bidirectional); zero size allowed, no uninit, no packet access.
    policy.pre.append(PredicateCall(
        "check_helper_mem_access",
        [r, size, BoolLit(False), BoolLit(True), BoolLit(False), BoolLit(False)],
    ))
    policy.pre.append(PredicateCall(
        "check_helper_mem_access",
        [r, size, BoolLit(True), BoolLit(True), BoolLit(False), BoolLit(False)],
    ))


def arg_size(policy: OpPolicy, params: list[dict], idx: int) -> None:
    # Consumed by the preceding mem_size pointer's emitter.
    pass


# Roles whose emitter takes `(policy, params, idx)` and nothing else. `map_ptr` is
# absent because it also needs the map-type list; `build_kfunc_policy` dispatches
# that one directly.
ROLE_EMITTERS = {
    "scalar": arg_scalar,
    "btf_id": arg_btf_id,
    "ign": arg_ign,
    "mem_size": arg_mem_size,
    "size": arg_size,
}


def ret_scalar(policy: OpPolicy) -> None:
    policy.post.append(TypeJudgment(Reg(0), "INT"))


def ret_void(policy: OpPolicy) -> None:
    policy.post.append(TypeJudgment(Reg(0), "POISON"))


def ret_btf_id(policy: OpPolicy, struct: str, maybe_null: bool) -> None:
    # A generic (non-acquire, non-special) struct-pointer return: the verifier marks
    # R0 a known-zero PTR_TO_BTF_ID of the return type; KF_RET_NULL adds maybe-null.
    r = Reg(0)
    policy.post.append(
        TypeJudgment(r, "PTR_TO_BTF_ID_OR_NULL" if maybe_null else "PTR_TO_BTF_ID")
    )
    policy.post.append(Equality(Field(r, "btf_id"), Static(f"get_btf_id({struct})")))
    policy.post.append(Equality(Field(r, "offset"), IntLit(0)))


# --- Callability -----------------------------------------------------------


def _callability(kfunc: dict) -> Expr | None:
    """Disjunction over the hooks the kfunc is registered in, or None if unmodelable.

    COMMON means callable from every program type, so when present it is `:= true`
    and dominates the disjunction -- emit it alone. Otherwise OR each mapped hook
    (AND-ed with the filters that gate it there); any unmapped hook makes the
    callable set inexpressible -> None (skip).
    """
    hooks = kfunc["hooks"]
    if "BTF_KFUNC_HOOK_COMMON" in hooks:
        return PredicateCall("hook_common", [])
    terms: list[Expr] = []
    for hook in sorted(hooks):
        pred = _HOOK_PREDICATE.get(hook)
        if pred is None:
            return None
        atoms: list[Expr] = [PredicateCall(pred, [])]
        atoms += [PredicateCall(f, []) for f in sorted(hooks[hook]["filters"])]
        terms.append(_conjoin(atoms))
    return _disjoin(terms) if terms else None


# --- Per-kfunc policy build ------------------------------------------------


def build_kfunc_policy(
    kfunc: dict,
    skip_imms: frozenset[int] = frozenset(),
    all_map_types: list[int] | None = None,
    pkt_changing: frozenset[str] = frozenset(),
) -> OpPolicy | None:
    if kfunc["btf"] != "vmlinux" or kfunc["special"] or kfunc["btf_id"] in skip_imms:
        return None

    flags: set[str] = set()
    for info in kfunc["hooks"].values():
        flags |= set(info["flags"])
    if flags - _MODELLED_FLAGS:
        return None

    sig = kfunc["signature"]
    roles = _classify_params(sig["params"])
    if roles is None:
        return None
    # A BTF-id argument is only modelled when the kfunc demands trusted args: we
    # check the pointer's family, not its type, so an untrusted-arg kfunc accepts
    # wider provenance than the model expresses.
    #
    # A map-pointer argument needs no such gate. CONST_PTR_TO_MAP is trusted by
    # construction (`reg2btf_ids` plus `is_trusted_reg`), and it is a program's
    # only provenance for a `struct bpf_map *`, so requiring it is narrower than
    # the kernel whether or not the kfunc asks for trusted args.
    if "btf_id" in roles and not (flags & _TRUSTED_FLAGS):
        return None
    # A map-pointer argument needs the map-type list to constrain; without it the
    # policy would carry a bare CONST_PTR_TO_MAP judgment the consumer drops anyway.
    if "map_ptr" in roles and not all_map_types:
        return None

    ret = sig["ret"]
    ret_struct = _base_struct(ret)
    if not (ret == "void" or ret in _SCALAR_TYPES or ret_struct is not None):
        return None

    callability = _callability(kfunc)
    if callability is None:
        return None

    name = kfunc["name"]
    policy = OpPolicy(comment=name)
    policy.signature = OpSignature(
        opcode=0x85, src=ImmField(0x2), imm=ImmField(kfunc["btf_id"])
    )

    policy.pre.append(callability)
    # imm is pinned to the scraped btf_id snapshot above; re-resolve it from the
    # name so a btf_id shift across builds is caught instead of mis-binding.
    policy.pre.append(Equality(Var("imm"), Static(f"get_btf_id({name})")))
    if "KF_SLEEPABLE" in flags:
        policy.pre.append(Static("prog_sleepable"))
    if "KF_DESTRUCTIVE" in flags:
        policy.pre.append(PredicateCall("CAPABILITY", [Var("CAP_SYS_BOOT")]))
    for i, role in enumerate(roles):
        if role == "map_ptr":
            arg_map_ptr(policy, sig["params"], i, all_map_types or [])
        else:
            ROLE_EMITTERS[role](policy, sig["params"], i)

    policy.post.append(PredicateCall("scratch", []))
    if name in pkt_changing:
        policy.post.append(PredicateCall("changes_pkt_data", []))
    if ret == "void":
        ret_void(policy)
    elif ret in _SCALAR_TYPES:
        ret_scalar(policy)
    else:
        ret_btf_id(policy, ret_struct, "KF_RET_NULL" in flags)
    return policy


def build_kfunc_policies(
    data_dir: Path | None = None,
    skip_imms: frozenset[int] = frozenset(),
    all_map_types: list[int] | None = None,
    pkt_changing: frozenset[str] = frozenset(),
) -> list[OpPolicy]:
    data_dir = data_dir or _DATA_DIR
    descriptors = json.loads((data_dir / "kfunc_descriptors.json").read_text())
    kfuncs = descriptors["kfuncs"]
    if any("special" not in k for k in kfuncs):
        raise ValueError(
            "kfunc_descriptors.json lacks the per-kfunc 'special' field; re-run "
            "scrapers/kfunc_descriptor_scraper.py to regenerate it"
        )
    if "provenance" not in descriptors:
        raise ValueError(
            "kfunc_descriptors.json carries no provenance stamp, so it was "
            "scraped from the running kernel rather than the vendored build; "
            "re-run scrapers/kfunc_descriptor_scraper.py"
        )
    return [
        p
        for k in kfuncs
        if (p := build_kfunc_policy(k, skip_imms, all_map_types, pkt_changing)) is not None
    ]
