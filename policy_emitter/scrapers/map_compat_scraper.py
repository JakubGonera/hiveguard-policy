#!/usr/bin/env python3
"""Scrape the kernel's helper/map-type compatibility relation into
helper_map_compat.json.

The kernel enforces which helpers may take which map types in
`check_map_func_compatibility` (kernel/bpf/verifier.c), a two-way check:

  1. `switch (map->map_type)`: a reserved map type allows only its listed
     helpers (any other helper `goto error`s).
  2. `switch (func_id)`: a specialised helper requires one of its listed map
     types.

Both switches are chains of `case LABEL:` groups whose body is a single
`if (x != A && x != B && ...) goto error;` (or a bare `goto error;` for types
with no BPF-side helpers), so this scraper parses the source text directly; no
running kernel is needed. Guards beyond the identifier chain (e.g.
`may_update_sockmap(env, func_id)`, the tail_call/bpf-to-bpf mixing check) are
conditional relaxations/restrictions we conservatively ignore: only the
explicitly listed identifiers are treated as allowed.

Output (JSON):
  map_types           BPF_MAP_TYPE_* name -> numeric value (aliases resolved,
                      `BPF_MAP_TYPE_UNSPEC` and the `__MAX` sentinel omitted)
  func_ids            BPF_FUNC_* name -> numeric id, for every func named in
                      the relation
  map_allows_funcs    reserved map type -> helpers allowed on it (switch #1;
                      an empty list means no helper may take the type)
  func_requires_types specialised helper -> map types it accepts (switch #2)

Map types absent from `map_allows_funcs` are unreserved (any helper the second
switch does not restrict may take them); helpers absent from
`func_requires_types` are unrestricted by the second switch.
"""

import argparse
import json
import pathlib
import re
import sys

ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
ap.add_argument(
    "linux_src",
    type=pathlib.Path,
    help="Path to the kernel source tree to scrape (the vendored tree; the "
    "relation is read from kernel/bpf/verifier.c and include/uapi/linux/bpf.h).",
)
args = ap.parse_args()

VERIFIER_C = args.linux_src / "kernel/bpf/verifier.c"
UAPI_BPF_H = args.linux_src / "include/uapi/linux/bpf.h"
OUT = pathlib.Path(__file__).resolve().parent / "helper_map_compat.json"


def strip_comments(src: str) -> str:
    return re.sub(r"/\*.*?\*/", "", src, flags=re.DOTALL)


def parse_map_type_enum(header: str) -> dict[str, int]:
    """`enum bpf_map_type` name -> value; sequential with `= ALIAS` entries."""
    m = re.search(r"enum bpf_map_type \{(.*?)\};", strip_comments(header), re.DOTALL)
    if not m:
        sys.exit("enum bpf_map_type not found")
    values: dict[str, int] = {}
    next_value = 0
    for entry in m.group(1).split(","):
        entry = entry.strip()
        if not entry:
            continue
        if "=" in entry:
            name, alias = (part.strip() for part in entry.split("=", 1))
            values[name] = values[alias]
            next_value = values[alias] + 1
        else:
            values[entry] = next_value
            next_value += 1
    return {
        name: value
        for name, value in values.items()
        if name.startswith("BPF_MAP_TYPE_") and value != 0
    }


def parse_func_id_mapper(header: str) -> dict[str, int]:
    """`___BPF_FUNC_MAPPER`'s `FN(name, id, ...)` list -> BPF_FUNC_name -> id."""
    ids = {
        f"BPF_FUNC_{m.group(1)}": int(m.group(2))
        for m in re.finditer(r"\bFN\((\w+), (\d+), ", header)
    }
    if not ids:
        sys.exit("__BPF_FUNC_MAPPER FN() list not found")
    return ids


def function_body(src: str, name: str) -> str:
    start = src.index(name)
    open_brace = src.index("{", start)
    depth = 0
    for i in range(open_brace, len(src)):
        if src[i] == "{":
            depth += 1
        elif src[i] == "}":
            depth -= 1
            if depth == 0:
                return src[open_brace : i + 1]
    sys.exit(f"unbalanced braces in {name}")


def parse_switch(body: str, label_re: str, cond_re: str) -> dict[str, list[str]]:
    """One switch's `case` groups: labels -> identifiers listed in the guard.

    Each group runs from its first `case` label to the next `break;`; the
    allowed set is every `cond_re` identifier in the group's `if` condition. A
    group that `goto error;`s without a condition allows nothing.
    """
    groups: dict[str, list[str]] = {}
    for chunk in body.split("break;"):
        labels = re.findall(rf"case ({label_re}):", chunk)
        if not labels:
            continue
        condition = chunk[chunk.rindex(labels[-1]) :]
        allowed = sorted(set(re.findall(cond_re, condition)))
        for label in labels:
            groups[label] = allowed
    return groups


verifier_src = strip_comments(VERIFIER_C.read_text())
header_src = UAPI_BPF_H.read_text()

body = function_body(verifier_src, "static int check_map_func_compatibility")
first, second = body.split("switch (func_id)")

map_types = parse_map_type_enum(header_src)
func_ids = parse_func_id_mapper(header_src)

map_allows_funcs = parse_switch(first, r"BPF_MAP_TYPE_\w+", r"BPF_FUNC_\w+")
func_requires_types = parse_switch(second, r"BPF_FUNC_\w+", r"BPF_MAP_TYPE_\w+")

unknown_types = (set(map_allows_funcs) | {t for ts in func_requires_types.values() for t in ts}) - set(map_types)
unknown_funcs = ({f for fs in map_allows_funcs.values() for f in fs} | set(func_requires_types)) - set(func_ids)
if unknown_types or unknown_funcs:
    sys.exit(f"identifiers missing from the UAPI header: {sorted(unknown_types | unknown_funcs)}")

referenced_funcs = set(func_requires_types) | {f for fs in map_allows_funcs.values() for f in fs}
out = {
    "map_types": dict(sorted(map_types.items(), key=lambda kv: kv[1])),
    "func_ids": {name: func_ids[name] for name in sorted(referenced_funcs, key=func_ids.get)},
    "map_allows_funcs": dict(sorted(map_allows_funcs.items())),
    "func_requires_types": dict(sorted(func_requires_types.items())),
}
OUT.write_text(json.dumps(out, indent=2) + "\n")
print(f"wrote {OUT}: {len(map_allows_funcs)} reserved map types, "
      f"{len(func_requires_types)} restricted helpers", file=sys.stderr)
