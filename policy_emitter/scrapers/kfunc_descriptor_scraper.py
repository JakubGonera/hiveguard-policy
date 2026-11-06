"""Scrape kfunc security metadata from the vendored kernel into a JSON descriptor.

A kfunc's KF_* flags and callable program types are not in BTF type info. On a
running kernel they live in each `struct btf`'s `kfunc_set_tab`, which is what
this scraper used to walk -- but that table is built at boot by
`register_btf_kfunc_id_set()`, so it does not exist in a built image, and
walking it described whatever kernel the host happened to boot rather than the
one this repo vendors and runs in its VM.

Every fact is recoverable without booting, from two places that do describe the
vendored kernel:

  * the source, for which kfuncs are in which id set
    (`BTF_KFUNCS_START(set)` ... `BTF_ID_FLAGS(func, name, FLAGS)`), which set a
    `struct btf_kfunc_id_set` wraps, which hook each `register_btf_kfunc_id_set`
    call registers it under, and which filter gates it;
  * the built image, for each kfunc's BTF id and signature (its `.BTF` section)
    and for the `struct btf_id_set8` a filter consults (static data that
    `resolve_btfids` patches at build time, readable straight out of the ELF).

The output schema is unchanged: `{ provenance, prog_type_to_hook, hook_filters,
kfuncs }`. Each kfunc records its signature and, per hook it is registered in,
the KF_* flags and the filters that actually gate it; the program types a hook
serves and the full filter list per hook live in the two shared maps. Each kfunc
also gets a `special` flag: whether the verifier dispatches it through a
name-keyed special routine (membership in `special_kfunc_list`, parsed from
verifier.c) -- such kfuncs cannot be modelled from signature+flags alone.

Needs no root and no running kernel; it needs `just linux-build` to have run.
"""

import argparse
import json
import pathlib
import re
import subprocess
import sys

import drgn

import btf as btfmod
import vmlinux as vmlinux_mod

# Registration helpers and the hook each one implies. `register_btf_kfunc_id_set`
# takes the program type as its first argument and is mapped through
# `bpf_prog_type_to_kfunc_hook`; the fmodret helper hardcodes its hook.
_REGISTER_RE = re.compile(
    r"register_btf_kfunc_id_set\s*\(\s*(BPF_PROG_TYPE_\w+)\s*,\s*&\s*(\w+)\s*\)"
)
_REGISTER_FMODRET_RE = re.compile(r"register_btf_fmodret_id_set\s*\(\s*&\s*(\w+)\s*\)")

# `static const struct btf_kfunc_id_set NAME = { .set = &IDS, .filter = FN };`
_KFUNC_SET_RE = re.compile(
    r"struct\s+btf_kfunc_id_set\s+(\w+)\s*=\s*\{(.*?)\}\s*;", re.S
)
_SET_FIELD_RE = re.compile(r"\.set\s*=\s*&\s*(\w+)")
_FILTER_FIELD_RE = re.compile(r"\.filter\s*=\s*(\w+)")

# One id set: `BTF_KFUNCS_START(name) BTF_ID_FLAGS(func, x, FLAGS) ... BTF_KFUNCS_END(name)`.
# `BTF_SET8_START/END` is the older spelling of the same thing, still used in a
# few places (net/mptcp/bpf.c).
_ID_SET_RE = re.compile(
    r"BTF_(?:KFUNCS|SET8)_START\s*\(\s*(\w+)\s*\)(.*?)BTF_(?:KFUNCS|SET8)_END\s*\(\s*\1\s*\)",
    re.S,
)
_ID_FLAGS_RE = re.compile(
    r"BTF_ID_FLAGS\s*\(\s*func\s*,\s*(\w+)\s*(?:,\s*([^()]*?))?\s*\)", re.S
)

# A filter gates only the kfuncs in its own btf_id_set, which it consults inside
# its body (not a walkable field), so the filter->set link is hand-maintained.
# Unmapped filters are treated as gating (conservative) and warned about.
FILTER_SETS = {
    "bpf_qdisc_kfunc_filter": "qdisc_kfunc_ids",
    "tracing_iter_filter": "bpf_sk_iter_kfunc_ids",
    "bpf_fs_kfuncs_filter": "bpf_fs_kfunc_set_ids",
    "bpf_get_fsverity_digest_filter": "fsverity_set_ids",
    "bpf_kprobe_multi_filter": "kprobe_multi_kfunc_set_ids",
    "bpf_session_filter": "session_kfunc_set_ids",
}


class Config:
    """The `.config` the image was built with, for evaluating source guards.

    A kfunc *row* under a disabled config needs no help: the function is not
    compiled, so it is absent from the image's BTF and drops out anyway. A
    guarded *registration* is the dangerous one, because claiming a hook the
    kernel never registers widens the policy. So registrations are evaluated
    against the real config, and a guard this cannot evaluate drops the
    registration rather than assuming it fires.
    """

    def __init__(self, path: pathlib.Path | None) -> None:
        self.enabled: set[str] = set()
        self.known = path is not None and path.exists()
        if not self.known:
            return
        for line in path.read_text(errors="replace").splitlines():
            match = re.match(r"(CONFIG_\w+)=([ym])", line)
            if match:
                self.enabled.add(match.group(1))

    def guard_holds(self, condition: str) -> bool | None:
        """Whether a `#if` condition holds; `None` if it cannot be evaluated.

        Only the shapes the kernel actually uses around these registrations are
        handled: `CONFIG_X`, `defined(CONFIG_X)`, and `IS_ENABLED(CONFIG_X)`,
        optionally negated. Anything else is unevaluated.
        """
        if not self.known:
            return None
        text = condition.strip()
        negated = False
        if text.startswith("!"):
            negated, text = True, text[1:].strip()
        match = re.fullmatch(r"(?:defined\s*\(\s*|IS_ENABLED\s*\(\s*)?(CONFIG_\w+)\s*\)?", text)
        if not match:
            return None
        holds = match.group(1) in self.enabled
        return not holds if negated else holds


def load_kf_flag_bits(btf_h):
    bits = {
        1 << int(m.group(2)): m.group(1)
        for m in re.finditer(r"#define\s+(KF_\w+)\s+\(1\s*<<\s*(\d+)\)", btf_h.read_text())
    }
    if not bits:
        sys.exit(f"no KF_* flag definitions in {btf_h}")
    return bits


def load_hook_names(btf_c):
    block = re.search(r"enum btf_kfunc_hook\s*\{(.*?)\}", btf_c.read_text(), re.S)
    if not block:
        sys.exit(f"enum btf_kfunc_hook not found in {btf_c}")
    names = re.findall(r"BTF_KFUNC_HOOK_\w+", block.group(1))
    if "BTF_KFUNC_HOOK_MAX" not in names:
        sys.exit("enum btf_kfunc_hook missing BTF_KFUNC_HOOK_MAX")
    return names


def load_hook_to_prog_types(btf_c):
    body = re.search(
        r"bpf_prog_type_to_kfunc_hook\s*\([^)]*\)\s*\{(.*?)\n\}", btf_c.read_text(), re.S
    )
    if not body:
        sys.exit(f"bpf_prog_type_to_kfunc_hook not found in {btf_c}")
    mapping, pending = {}, []
    for line in body.group(1).splitlines():
        pending += re.findall(r"case\s+(BPF_PROG_TYPE_\w+)\s*:", line)
        ret = re.search(r"return\s+(BTF_KFUNC_HOOK_\w+)\s*;", line)
        if ret:
            mapping.setdefault(ret.group(1), []).extend(pending)
            pending = []
    return mapping


def kernel_sources(linux_src, build_root):
    """Every `.c` file that mentions a kfunc registration or id set *and was built*.

    The build tree mirrors the source tree, so the presence of a matching `.o`
    is an exact answer to "did this file go into the image". That matters:
    `net/sched/bpf_qdisc.c` registers kfuncs unconditionally in its own text but
    is gated by its Makefile, and taking its registrations on a build that omits
    it would claim hooks the kernel never installs.

    `tools/` is excluded regardless: the selftest modules there register into the
    same tables once inserted, but they are not part of this image.
    """
    try:
        out = subprocess.check_output(
            [
                "grep", "-rl", "-e", "BTF_KFUNCS_START", "-e", "BTF_SET8_START",
                "-e", "register_btf_kfunc_id_set", "-e", "register_btf_fmodret_id_set",
                "--include=*.c", str(linux_src),
            ]
        ).decode()
    except subprocess.CalledProcessError:
        return []
    sources, skipped = [], []
    for raw in out.split():
        path = pathlib.Path(raw)
        if "/tools/" in raw or path.name == "btf.c":
            continue
        relative = path.relative_to(linux_src)
        if build_root is not None and not (build_root / relative).with_suffix(".o").exists():
            skipped.append(str(relative))
            continue
        sources.append(path)
    if skipped:
        print(
            f"note: {len(skipped)} kfunc source files were not built into this "
            f"image: {', '.join(sorted(skipped)[:6])}",
            file=sys.stderr,
        )
    return sources


def registration_lines(text, config, where):
    """Yields `(prog_type_or_None, wrapper)` for each *live* registration call.

    A call inside a `#if` whose condition the build config does not satisfy is
    skipped, and so is one whose guard cannot be evaluated: over-claiming a hook
    widens the policy, and there is no safe way to guess.
    """
    guards: list[str] = []
    for lineno, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        opener = re.match(r"#\s*(ifdef|ifndef|if)\s+(.*)", stripped)
        if opener:
            keyword, condition = opener.group(1), opener.group(2)
            if keyword == "ifndef":
                condition = f"!{condition}"
            guards.append(condition)
            continue
        if re.match(r"#\s*endif\b", stripped):
            if guards:
                guards.pop()
            continue
        if re.match(r"#\s*el(se|if)\b", stripped) and guards:
            # An `#else` arm inverts a condition this does not track; mark it
            # unevaluable so anything inside is dropped.
            guards[-1] = "<unevaluated>"
            continue

        calls = [(pt, w) for pt, w in _REGISTER_RE.findall(line)]
        calls += [(None, w) for w in _REGISTER_FMODRET_RE.findall(line)]
        if not calls:
            continue
        verdicts = [config.guard_holds(g) for g in guards]
        if any(v is False for v in verdicts):
            continue
        if any(v is None for v in verdicts):
            print(
                f"warning: {where}:{lineno}: registration guarded by an "
                f"unevaluated condition {guards}; skipped",
                file=sys.stderr,
            )
            continue
        yield from calls


def parse_registrations(linux_src, build_root, prog_type_to_hook, config):
    """Source scrape: hook -> {kfunc name -> (flags, filters)}.

    Three source facts compose into one: an id set lists its kfuncs and their
    flags, a `btf_kfunc_id_set` names that set and its filter, and a
    registration call binds the whole thing to a program type (hence a hook).
    """
    id_sets = {}      # set symbol -> {name: [flags]}
    kfunc_sets = {}   # wrapper symbol -> (set symbol, filter or None)
    registrations = []  # (hook, wrapper symbol)

    for path in kernel_sources(linux_src, build_root):
        text = path.read_text(errors="replace")
        for name, body in _ID_SET_RE.findall(text):
            rows = id_sets.setdefault(name, {})
            for func, flags in _ID_FLAGS_RE.findall(body):
                rows[func] = sorted(
                    f.strip() for f in (flags or "").split("|") if f.strip()
                )
        for name, body in _KFUNC_SET_RE.findall(text):
            set_match = _SET_FIELD_RE.search(body)
            if not set_match:
                continue
            filter_match = _FILTER_FIELD_RE.search(body)
            kfunc_sets[name] = (
                set_match.group(1),
                filter_match.group(1) if filter_match else None,
            )
        where = str(path).replace(str(linux_src), "")
        for prog_type, wrapper in registration_lines(text, config, where):
            if prog_type is None:
                registrations.append(("BTF_KFUNC_HOOK_FMODRET", wrapper))
                continue
            hook = prog_type_to_hook.get(prog_type)
            if hook is None:
                print(
                    f"warning: {where}: {prog_type} has no hook mapping; skipped",
                    file=sys.stderr,
                )
                continue
            registrations.append((hook, wrapper))

    per_hook = {}
    for hook, wrapper in registrations:
        entry = kfunc_sets.get(wrapper)
        if entry is None:
            print(f"warning: no btf_kfunc_id_set named {wrapper}; skipped", file=sys.stderr)
            continue
        set_name, filter_name = entry
        rows = id_sets.get(set_name)
        if rows is None:
            print(f"warning: no id set named {set_name}; skipped", file=sys.stderr)
            continue
        for func, flags in rows.items():
            slot = per_hook.setdefault(hook, {}).setdefault(func, {"flags": set(), "filters": set()})
            slot["flags"].update(flags)
            if filter_name:
                slot["filters"].add(filter_name)
    return per_hook


def read_id_set8(prog, sym):
    """The btf ids a filter's own `struct btf_id_set8` holds.

    Static data that `resolve_btfids` patched at build time, so it reads
    straight out of the image.
    """
    try:
        addr = prog.symbol(sym).address
        s = drgn.Object(prog, "struct btf_id_set8", address=addr)
        return {int(s.pairs[i].id) for i in range(int(s.cnt))}
    except Exception:
        return None


def load_special_kfunc_names(verifier_c):
    text = verifier_c.read_text()
    block = re.search(r"BTF_ID_LIST\(special_kfunc_list\)(.*?)\n\n", text, re.S)
    if not block:
        sys.exit(f"BTF_ID_LIST(special_kfunc_list) not found in {verifier_c}")
    names = set(re.findall(r"BTF_ID\(\s*func\s*,\s*(\w+)\s*\)", block.group(1)))
    if not names:
        sys.exit(f"no BTF_ID(func, ...) entries in special_kfunc_list of {verifier_c}")
    return names


def build_func_index(image_btf):
    """kfunc name -> (btf id, signature), from the image's own BTF."""
    index = {}
    for ty in image_btf.types:
        if ty.kind != btfmod.KIND_FUNC or not ty.name or ty.name in index:
            continue
        proto = image_btf.get(ty.ref)
        if proto is None or proto.kind != btfmod.KIND_FUNC_PROTO:
            continue
        params = [
            {"name": p.name, "type": image_btf.type_name(p.type_id) or "?"}
            for p in proto.params
        ]
        signature = {"ret": image_btf.type_name(proto.ref) or "?", "params": params}
        index[ty.name] = (ty.id, signature)
    return index


def scrape(per_hook, func_index, prog, kf_bits):
    """Joins the source registrations to the image's ids and signatures."""
    # Read a filter's own id set only when a surviving registration references
    # the filter: a set belonging to a config this build disables has no symbol,
    # and complaining about it would be noise, not a finding.
    filter_ids = {}
    unknown, unreadable, missing = set(), set(), set()

    def ids_for(filter_name):
        if filter_name not in filter_ids:
            filter_ids[filter_name] = read_id_set8(prog, FILTER_SETS[filter_name])
            if filter_ids[filter_name] is None:
                unreadable.add(filter_name)
        return filter_ids[filter_name]

    def gating_filters(filters, btf_id):
        out = []
        for f in sorted(filters):
            if f not in FILTER_SETS:
                unknown.add(f)
                out.append(f)
                continue
            ids = ids_for(f)
            if ids is None or btf_id in ids:
                out.append(f)
        return out

    kfuncs = {}
    hook_filters = {}
    for hook, funcs in per_hook.items():
        for name, entry in funcs.items():
            found = func_index.get(name)
            if found is None:
                # Registered in source but absent from this image's BTF: the
                # config that builds it is off. Skip rather than invent an id.
                missing.add(name)
                continue
            btf_id, signature = found
            unknown_flags = entry["flags"] - set(kf_bits.values())
            if unknown_flags:
                sys.exit(f"unknown KF_* flags on {name}: {sorted(unknown_flags)}")
            if entry["filters"]:
                hook_filters.setdefault(hook, set()).update(entry["filters"])
            rec = kfuncs.setdefault(
                btf_id,
                {
                    "name": name,
                    "btf": "vmlinux",
                    "btf_id": btf_id,
                    "signature": signature,
                    "hooks": {},
                },
            )
            rec["hooks"][hook] = {
                "flags": sorted(entry["flags"]),
                "filters": gating_filters(entry["filters"], btf_id),
            }

    for f in sorted(unknown):
        print(f"warning: filter {f} has no known set; treated as gating", file=sys.stderr)
    for f in sorted(unreadable):
        print(
            f"warning: filter {f}'s id set is not in this image; treated as gating",
            file=sys.stderr,
        )
    if missing:
        print(
            f"note: {len(missing)} kfuncs registered in source are absent from this "
            f"build's BTF (config-gated): {', '.join(sorted(missing)[:8])}",
            file=sys.stderr,
        )
    rows = sorted(kfuncs.values(), key=lambda r: (r["btf"], r["name"]))
    return rows, {h: sorted(v) for h, v in hook_filters.items()}


def main():
    ap = argparse.ArgumentParser(
        description="Scrape kfunc KF_* flags, callable program types and signatures "
        "from the vendored kernel build. Needs no root and no running kernel."
    )
    ap.add_argument(
        "linux_src",
        type=pathlib.Path,
        help="Path to the vendored kernel source tree. Read for the KF_* flag bits "
        "(include/linux/btf.h), the enum btf_kfunc_hook ordering and prog-type->hook "
        "mapping (kernel/bpf/btf.c), and every kfunc id set and its registration. "
        "Must be the tree the --vmlinux image was built from.",
    )
    vmlinux_mod.add_argument(ap)
    ap.add_argument(
        "-o", "--out", type=pathlib.Path, default=pathlib.Path("kfunc_descriptors.json"),
        help="output JSON path (default: %(default)s)",
    )
    args = ap.parse_args()

    btf_c = args.linux_src / "kernel/bpf/btf.c"
    btf_h = args.linux_src / "include/linux/btf.h"
    verifier_c = args.linux_src / "kernel/bpf/verifier.c"
    for p in (btf_c, btf_h, verifier_c):
        if not p.exists():
            ap.error(f"{p} not found; is {args.linux_src} a kernel source tree?")

    kf_bits = load_kf_flag_bits(btf_h)
    load_hook_names(btf_c)  # validates the enum is where we think it is
    prog_type_to_hook = {
        pt: hook for hook, pts in load_hook_to_prog_types(btf_c).items() for pt in pts
    }

    image = vmlinux_mod.open_from_args(args)
    blob = image.section(".BTF")
    if blob is None:
        sys.exit(f"{image.path} has no .BTF section; build with CONFIG_DEBUG_INFO_BTF")
    image_btf = btfmod.Btf(blob)

    config = Config(image.path.parent / ".config")
    if not config.known:
        print(
            f"warning: no .config beside {image.path}; guarded registrations "
            "cannot be evaluated and will be skipped",
            file=sys.stderr,
        )
    per_hook = parse_registrations(
        args.linux_src, image.path.parent, prog_type_to_hook, config
    )
    rows, hook_filters = scrape(per_hook, build_func_index(image_btf), image.program(), kf_bits)

    special_names = load_special_kfunc_names(verifier_c)
    for r in rows:
        r["special"] = r["name"] in special_names

    out = {
        "provenance": vmlinux_mod.provenance(image),
        "prog_type_to_hook": prog_type_to_hook,
        "hook_filters": hook_filters,
        "kfuncs": rows,
    }
    args.out.write_text(json.dumps(out, indent=2) + "\n")
    print(
        f"wrote {args.out}: {len(rows)} kfuncs from {image.path.name} "
        f"({image.release()})",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
