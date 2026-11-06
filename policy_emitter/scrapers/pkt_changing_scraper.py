#!/usr/bin/env python3
"""Scrape which helpers and kfuncs change packet data into pkt_changing.json.

After a call that may move or resize packet data, the kernel invalidates every
packet pointer the program holds (`clear_all_pkt_pointers`). Which calls do so
is decided by two predicates, both read from source here; no running kernel is
needed:

  helpers  `bpf_helper_changes_pkt_data` (net/core/filter.c), a `switch` whose
           `case BPF_FUNC_*:` labels all return true.
  kfuncs   `is_kfunc_pkt_changing` (kernel/bpf/verifier.c), a chain of
           `special_kfunc_list[KF_<name>]` comparisons.

`BPF_FUNC_tail_call` is listed as the kernel lists it: a tail call that
returns changed nothing, but one inside a subprogram returns to its caller
after the callee ran, so the kernel counts it.

Output (JSON):
  helpers  BPF_FUNC_* name -> numeric id
  kfuncs   kfunc names
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
    help="Path to the vendored kernel source tree.",
)
args = ap.parse_args()

FILTER_C = args.linux_src / "net/core/filter.c"
VERIFIER_C = args.linux_src / "kernel/bpf/verifier.c"
UAPI_BPF_H = args.linux_src / "include/uapi/linux/bpf.h"
OUT = pathlib.Path(__file__).resolve().parent / "pkt_changing.json"


def strip_comments(src: str) -> str:
    return re.sub(r"/\*.*?\*/", "", src, flags=re.DOTALL)


def function_body(src: str, signature: str) -> str:
    start = src.find(signature)
    if start < 0:
        sys.exit(f"{signature} not found")
    open_brace = src.index("{", start)
    depth = 0
    for i in range(open_brace, len(src)):
        if src[i] == "{":
            depth += 1
        elif src[i] == "}":
            depth -= 1
            if depth == 0:
                return src[open_brace : i + 1]
    sys.exit(f"unbalanced braces in {signature}")


def parse_func_id_mapper(header: str) -> dict[str, int]:
    """`___BPF_FUNC_MAPPER`'s `FN(name, id, ...)` list -> BPF_FUNC_name -> id."""
    ids = {
        f"BPF_FUNC_{m.group(1)}": int(m.group(2))
        for m in re.finditer(r"\bFN\((\w+), (\d+), ", header)
    }
    if not ids:
        sys.exit("__BPF_FUNC_MAPPER FN() list not found")
    return ids


def changing_helpers(filter_src: str) -> list[str]:
    body = function_body(filter_src, "bool bpf_helper_changes_pkt_data(")
    # Every label falls through to the one `return true;`; anything else is a
    # shape this parser does not understand.
    cases, _, rest = body.partition("return true;")
    if "return true;" in rest or "default:" not in rest:
        sys.exit("bpf_helper_changes_pkt_data has an unexpected shape")
    labels = re.findall(r"case (BPF_FUNC_\w+):", cases)
    if not labels:
        sys.exit("bpf_helper_changes_pkt_data lists no helpers")
    return labels


def changing_kfuncs(verifier_src: str) -> list[str]:
    body = function_body(verifier_src, "static bool is_kfunc_pkt_changing(")
    names = re.findall(r"special_kfunc_list\[KF_(\w+)\]", body)
    if not names:
        sys.exit("is_kfunc_pkt_changing names no kfunc")
    return sorted(set(names))


func_ids = parse_func_id_mapper(UAPI_BPF_H.read_text())
helpers = changing_helpers(strip_comments(FILTER_C.read_text()))
unknown = sorted(set(helpers) - set(func_ids))
if unknown:
    sys.exit(f"unknown helpers in bpf_helper_changes_pkt_data: {unknown}")

out = {
    "helpers": {name: func_ids[name] for name in sorted(set(helpers))},
    "kfuncs": changing_kfuncs(strip_comments(VERIFIER_C.read_text())),
}
OUT.write_text(json.dumps(out, indent=2) + "\n")
print(f"wrote {OUT} ({len(out['helpers'])} helpers, {len(out['kfuncs'])} kfuncs)")
