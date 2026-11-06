import argparse
import json
import pathlib
import re
import subprocess
import sys

import drgn

import btf as btfmod
import vmlinux as vmlinux_mod

ap = argparse.ArgumentParser(
    description="Scrape bpf_func_proto helper descriptors from the vendored kernel "
    "build. A proto is a `const` object in the image's .rodata, so this reads the "
    "built vmlinux directly: no root, no running kernel, and the answers describe "
    "the kernel this repo boots in its VM."
)
ap.add_argument(
    "linux_src",
    type=pathlib.Path,
    help="Path to the vendored kernel source tree. Read for the func_id<->proto "
    "mapping (the get_func_proto() switches) and the bpf_helper_changes_pkt_data "
    "list (net/core/filter.c). Must be the tree the --vmlinux image was built from.",
)
vmlinux_mod.add_argument(ap)
ap.add_argument(
    "-o", "--out", type=pathlib.Path,
    default=pathlib.Path("kernel_proto_descriptors.json"),
    help="output JSON path (default: %(default)s)",
)
args = ap.parse_args()

# Kernel source tree matching the running kernel, used by build_func_id_by_proto()
# and build_changes_pkt_data_ids().
LINUX_SRC = args.linux_src
if not LINUX_SRC.exists():
    ap.error(f"{LINUX_SRC} not found; is it a kernel source tree?")

image = vmlinux_mod.open_from_args(args)
prog = image.program()

# Type names come from the image's own `.BTF`, not from the runtime
# `btf_vmlinux`: nothing has booted to parse that, so the pointer is null here.
_btf_blob = image.section(".BTF")
if _btf_blob is None:
    sys.exit(f"{image.path} has no .BTF section; build with CONFIG_DEBUG_INFO_BTF")
IMAGE_BTF = btfmod.Btf(_btf_blob)

BASE_BITS = 8  # BPF_BASE_TYPE_BITS in include/linux/bpf.h
BASE_MASK = (1 << BASE_BITS) - 1

# include/linux/poison.h: BPF_PTR_POISON = (void *)(0xeB9F + POISON_POINTER_DELTA).
# Used for ARG_PTR_TO_SPIN_LOCK and protos that overwrite ret_btf_id at runtime;
# always a non-canonical address, so blind dereference would fault. We try to
# resolve the macro from debug info but fall back on an exception-safe deref.
try:
    BPF_PTR_POISON = (0xeB9F + int(prog.constant('POISON_POINTER_DELTA'))) & ((1 << 64) - 1)
except Exception:
    BPF_PTR_POISON = None

# Skip the trailing sentinel enumerators (e.g. __BPF_TYPE_FLAG_MAX,
# __BPF_TYPE_LAST_FLAG). __BPF_TYPE_LAST_FLAG is defined as
# __BPF_TYPE_FLAG_MAX - 1, which aliases the numeric value of the last real
# flag; keyed by value it would otherwise clobber that flag's name.
def enum_names(name):
    return {e.value: e.name for e in prog.type(name).enumerators
            if not e.name.startswith('__')}

ret_names = enum_names('enum bpf_return_type')
arg_names = enum_names('enum bpf_arg_type')
flag_names = enum_names('enum bpf_type_flag')

func_id_by_short = {}
for e in prog.type('enum bpf_func_id').enumerators:
    if e.name.startswith('BPF_FUNC_'):
        func_id_by_short[e.name[len('BPF_FUNC_'):]] = e.value


def build_func_id_by_proto():
    """Authoritative `proto symbol name -> func id`, read from the source.

    The func_id<->proto mapping exists only in code: every program type's
    get_func_proto() callback is a `switch (func_id)` whose arms bind an id to a
    proto via `case BPF_FUNC_x: return &y_proto;`, `case ...: func = &y_proto;
    break;`, or `return <wrapper>();` where a thin wrapper returns &y_proto. We
    parse those arms directly, so a proto reached only through a program type
    (e.g. bpf_xdp_redirect_map_proto, which serves BPF_FUNC_redirect_map = 51)
    gets the right id — which a proto-name match cannot recover, since no
    bpf_redirect_map_proto symbol exists. Ids come from the running kernel's
    enum (func_id_by_short); the source only supplies the proto<->case pairing.
    """
    if not LINUX_SRC.exists():
        sys.exit(f"kernel source not found at {LINUX_SRC}")
    files = subprocess.check_output(
        ["grep", "-rl", "case BPF_FUNC_", "--include=*.c", str(LINUX_SRC)]
    ).decode().split()

    case_re = re.compile(r"case\s+BPF_FUNC_(\w+)\s*:")
    # A proto symbol may carry a per-attach suffix (`..._proto_trace`,
    # `_pe`, `_kmulti`), so the name is any identifier containing `_proto`,
    # not one ending in it. Anchoring on the end silently dropped every
    # variant arm, leaving those protos with no func id.
    ref_re = re.compile(r"&(\w*_proto\w*)\b")              # direct &proto reference
    call_re = re.compile(r"return\s+(\w*_proto\w*)\s*\(")  # return wrapper_proto(...)
    term_re = re.compile(r"\b(?:break|return|goto)\b")  # case-body terminators
    fndef_re = re.compile(r"bpf_func_proto\s*\*\s*(\w+)\s*\(")

    # Pass 1: thin wrappers `fn -> proto`. A *_func_proto fn is a switch
    # dispatcher, not a wrapper, so exclude it; a `case` before any `return
    # &proto` likewise means we mis-started on a dispatcher.
    wrapper = {}
    for fp in files:
        cur = None
        for line in pathlib.Path(fp).read_text().splitlines():
            d = fndef_re.search(line)
            if d:
                cur = d.group(1) if not d.group(1).endswith("_func_proto") else None
                continue
            if cur is None:
                continue
            if "case BPF_FUNC_" in line:
                cur = None
                continue
            m = ref_re.search(line)
            if m:
                wrapper[cur] = m.group(1)
                cur = None

    # Pass 2: case arm -> proto. Labels accumulate across fallthrough; a body
    # terminator ends the arm so the next `case` starts a fresh label set.
    proto_funcs = {}
    for fp in files:
        pending, body = [], False
        for line in pathlib.Path(fp).read_text().splitlines():
            for cm in case_re.finditer(line):
                if body:
                    pending, body = [], False
                pending.append(cm.group(1))
            protos = [m.group(1) for m in ref_re.finditer(line)]
            cl = call_re.search(line)
            if cl and cl.group(1) in wrapper:
                protos.append(wrapper[cl.group(1)])
            for p in protos:
                for f in pending:
                    proto_funcs.setdefault(p, set()).add(f)
                if pending:
                    body = True
            if term_re.search(line):
                body = True

    by_proto = {}
    for proto, funcs in proto_funcs.items():
        ids = {func_id_by_short[f] for f in funcs if f in func_id_by_short}
        if len(ids) == 1:
            by_proto[proto] = next(iter(ids))
        elif len(ids) > 1:
            print(
                f"warning: {proto} maps to func ids {sorted(ids)}; skipping",
                file=sys.stderr,
            )
    return by_proto


func_id_by_proto = build_func_id_by_proto()


def build_changes_pkt_data_ids():
    """Func ids whose helper invalidates packet pointers after the call.

    Unlike gpl_only/pkt_access this is not a bpf_func_proto field: it is a
    hardcoded `switch (func_id)` in net/core/filter.c (bpf_helper_changes_pkt_data),
    which verifier.c consults to fire clear_all_pkt_pointers() once the call
    returns. We parse the case arms that fall through to `return true` and map
    the BPF_FUNC_* names to ids via the running kernel's enum (func_id_by_short).
    """
    src = LINUX_SRC / "net" / "core" / "filter.c"
    if not src.exists():
        sys.exit(f"net/core/filter.c not found at {src}")
    m = re.search(
        r"\bbpf_helper_changes_pkt_data\s*\([^)]*\)\s*\{(.*?)\n\}",
        src.read_text(), re.S,
    )
    if not m:
        sys.exit("could not locate bpf_helper_changes_pkt_data() in filter.c")
    # Only arms preceding `return true` invalidate packet data; `default`
    # returns false. The switch has a single true-branch today; warn if a
    # future kernel grows another, which this split would silently drop.
    segments = m.group(1).split("return true")
    if len(segments) != 2:
        print(f"warning: bpf_helper_changes_pkt_data has {len(segments) - 1} "
              f"'return true' branches; parser assumes 1", file=sys.stderr)
    ids = set()
    for n in re.findall(r"case\s+BPF_FUNC_(\w+)\s*:", segments[0]):
        fid = func_id_by_short.get(n)
        if fid is None:
            print(f"warning: BPF_FUNC_{n} in changes_pkt_data has no func id",
                  file=sys.stderr)
        else:
            ids.add(fid)
    return ids


changes_pkt_data_ids = build_changes_pkt_data_ids()

def btf_type_name(type_id):
    """Resolve a vmlinux BTF type id to its name (struct tag etc.).

    Straight out of the image's `.BTF` section. The equivalent walk of the
    runtime `btf_vmlinux` object cannot work here: that pointer is filled in by
    `btf_parse_vmlinux()` at boot, and this image has not booted.

    Returns None if the id is 0 or names nothing.
    """
    return IMAGE_BTF.name_of(int(type_id))

def decode(v, base_names):
    v = int(v)
    base = v & BASE_MASK
    flags = v & ~BASE_MASK
    flag_list = []
    for fv, fname in flag_names.items():
        if fv != 0 and (flags & fv) == fv:
            flag_list.append(fname)
            flags &= ~fv
    if flags:
        flag_list.append(f"0x{flags:x}")
    return {
        "base": base_names.get(base, f"0x{base:x}"),
        "flags": flag_list,
    }

def deref_btf_id(ptr):
    """Dereference a u32 *btf_id / int *ret_btf_id, skipping NULL and
    BPF_PTR_POISON (used for ARG_PTR_TO_SPIN_LOCK and protos that pick
    the id at runtime — see verifier.c check_btf_id_ok)."""
    if not ptr:
        return None
    if BPF_PTR_POISON is not None and int(ptr) == BPF_PTR_POISON:
        return None
    try:
        return int(ptr[0])
    except Exception:
        return None

def ret_entry(v, btf_id_ptr):
    out = decode(v, ret_names)
    # verifier.c only consults ret_btf_id for base type RET_PTR_TO_BTF_ID.
    if out["base"] == "RET_PTR_TO_BTF_ID":
        tid = deref_btf_id(btf_id_ptr)
        if tid is not None:
            name = btf_type_name(tid)
            if name is not None:
                out["btf"] = name
    return out

def arg_entry(v, btf_id_ptr):
    out = decode(v, arg_names)
    # verifier.c only consults arg_btf_id for ARG_PTR_TO_BTF_ID (the
    # SPIN_LOCK case is always BPF_PTR_POISON, handled by deref_btf_id).
    if out["base"] == "ARG_PTR_TO_BTF_ID":
        tid = deref_btf_id(btf_id_ptr)
        if tid is not None:
            name = btf_type_name(tid)
            if name is not None:
                out["btf"] = name
    return out

rows = []
for sym in prog.symbols():
    # A proto symbol is usually `<helper>_proto`, but a helper with per-attach
    # variants suffixes them (`bpf_get_attach_cookie_proto_trace`, `_pe`,
    # `_kmulti`). Matching only the exact suffix silently dropped every one of
    # those, so accept any symbol whose name mentions `_proto` and let the type
    # check below decide.
    if '_proto' not in sym.name:
        continue
    try:
        obj = prog.object(sym.name)
    except Exception:
        continue
    t = obj.type_
    if t.kind != drgn.TypeKind.STRUCT or t.tag != 'bpf_func_proto':
        continue
    p = drgn.Object(prog, 'struct bpf_func_proto', address=sym.address)
    # Mirror verifier.c:bpf_get_helper_proto — a proto with NULL .func is
    # treated as -EINVAL, so skip weak stubs that were never overridden.
    if not p.func:
        continue
    arg_btf_ptrs = [p.arg1_btf_id, p.arg2_btf_id, p.arg3_btf_id, p.arg4_btf_id, p.arg5_btf_id]
    arg_types = [p.arg1_type, p.arg2_type, p.arg3_type, p.arg4_type, p.arg5_type]
    # Resolved from the get_func_proto() switches, not the symbol name, so
    # prog-type-specific protos get the helper id they actually serve.
    func_id = func_id_by_proto.get(sym.name)
    rows.append({
        "name": sym.name,
        "func_id": func_id,
        "ret": ret_entry(p.ret_type, p.ret_btf_id),
        "args": [arg_entry(at, ap) for at, ap in zip(arg_types, arg_btf_ptrs)],
        "gpl_only": bool(p.gpl_only),
        "pkt_access": bool(p.pkt_access),
        # Keyed by func id (filter.c:bpf_helper_changes_pkt_data), not a proto
        # field: true => the verifier invalidates all packet pointers post-call.
        "changes_pkt_data": func_id in changes_pkt_data_ids,
    })

unresolved = [r["name"] for r in rows if r["func_id"] is None]
if unresolved:
    print(f"warning: no func id for {len(unresolved)} protos: "
          f"{', '.join(unresolved)}", file=sys.stderr)

args.out.write_text(
    json.dumps({"provenance": vmlinux_mod.provenance(image), "protos": rows}, indent=2)
    + "\n"
)
print(
    f"wrote {args.out}: {len(rows)} protos from {image.path.name} ({image.release()})",
    file=sys.stderr,
)
