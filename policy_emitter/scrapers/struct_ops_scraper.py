"""Scrape struct_ops member prototypes from the vendored kernel.

A struct_ops program implements one member of one struct_ops struct, and the
kernel calls it with that member's arguments. Those arguments arrive in the
trampoline context, so knowing the prototype is what lets the verifier give a
context slot a *type* rather than "some kernel pointer" -- and a typed slot is
what makes a kfunc's `btf_struct_ids_match` obligation dischargeable.

Two sources, both describing the vendored build:

  * the source, for which structs are struct_ops at all
    (`register_bpf_struct_ops(&bpf_X, X)`), and whether the file was built;
  * the image's `.BTF`, for each struct's members and their function prototypes.

Only members the verifier could model are recorded. A member whose type is not a
function pointer, or whose prototype mentions a type this cannot name (an
anonymous struct, an array, a nested function pointer), is skipped: leaving a
program's context untyped costs coverage, while guessing a type would be a claim
the kernel never made.

Needs no root and no running kernel; it needs `just linux-build` to have run.
"""

import argparse
import json
import pathlib
import re
import subprocess
import sys

import btf as btfmod
import vmlinux as vmlinux_mod

# `register_bpf_struct_ops(&bpf_tcp_congestion_ops, tcp_congestion_ops)`: the
# second argument is the struct tag, which is what BTF knows it by.
_REGISTER_RE = re.compile(r"register_bpf_struct_ops\s*\(\s*&\s*\w+\s*,\s*(\w+)\s*\)")


def struct_ops_types(linux_src, build_root):
    """The struct tags registered as struct_ops by files this image was built from."""
    try:
        files = subprocess.check_output(
            ["grep", "-rl", "register_bpf_struct_ops", "--include=*.c", str(linux_src)]
        ).decode().split()
    except subprocess.CalledProcessError:
        return {}

    found = {}
    for raw in files:
        path = pathlib.Path(raw)
        if "/tools/" in raw or path.name == "btf.c":
            continue
        relative = path.relative_to(linux_src)
        if build_root is not None and not (build_root / relative).with_suffix(".o").exists():
            continue
        for tag in _REGISTER_RE.findall(path.read_text(errors="replace")):
            found.setdefault(tag, str(relative))
    return found


def member_prototypes(image_btf, tag):
    """Every function-pointer member of a struct, with its argument types by name."""
    struct = image_btf.struct_named(tag)
    if struct is None:
        return None

    members = []
    for member in struct.members:
        proto = image_btf.function_prototype(member.type_id)
        if proto is None:
            continue
        ret = image_btf.type_name(proto.ref)
        args = [
            {"name": p.name, "type": image_btf.type_name(p.type_id)}
            for p in proto.params
        ]
        # An argument this cannot name would leave a hole in the context typing,
        # and a partially typed context is worse than an untyped one: it looks
        # authoritative. Skip the whole member.
        if ret is None or any(a["type"] is None for a in args):
            continue
        members.append(
            {
                "name": member.name,
                "offset": member.bits_offset // 8,
                "signature": {"ret": ret, "params": args},
            }
        )
    return {"name": tag, "size": struct.size, "members": members}


def main():
    ap = argparse.ArgumentParser(
        description="Scrape struct_ops member prototypes from the vendored kernel "
        "build. Needs no root and no running kernel."
    )
    ap.add_argument(
        "linux_src",
        type=pathlib.Path,
        help="Path to the vendored kernel source tree, read for the "
        "register_bpf_struct_ops() call sites. Must be the tree the --vmlinux "
        "image was built from.",
    )
    vmlinux_mod.add_argument(ap)
    ap.add_argument(
        "-o", "--out", type=pathlib.Path,
        default=pathlib.Path("struct_ops_descriptors.json"),
        help="output JSON path (default: %(default)s)",
    )
    args = ap.parse_args()

    if not (args.linux_src / "kernel/bpf/btf.c").exists():
        ap.error(f"is {args.linux_src} a kernel source tree?")

    image = vmlinux_mod.open_from_args(args)
    blob = image.section(".BTF")
    if blob is None:
        sys.exit(f"{image.path} has no .BTF section; build with CONFIG_DEBUG_INFO_BTF")
    image_btf = btfmod.Btf(blob)

    tags = struct_ops_types(args.linux_src, image.path.parent)
    structs, missing = [], []
    for tag in sorted(tags):
        entry = member_prototypes(image_btf, tag)
        if entry is None:
            missing.append(tag)
            continue
        structs.append(entry)

    if missing:
        print(
            f"note: {len(missing)} registered struct_ops types are absent from this "
            f"image's BTF: {', '.join(missing)}",
            file=sys.stderr,
        )

    out = {"provenance": vmlinux_mod.provenance(image), "structs": structs}
    args.out.write_text(json.dumps(out, indent=2) + "\n")
    total = sum(len(s["members"]) for s in structs)
    print(
        f"wrote {args.out}: {len(structs)} struct_ops types, {total} modelled "
        f"members from {image.path.name} ({image.release()})",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
