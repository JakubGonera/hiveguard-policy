#!/usr/bin/env python3
"""Invert dispatch_map.json into probed_proto_callers.json (in the parent
directory) keyed on the bpf_func_proto symbol, joining each entry with the
helper's C function name (`bpf_xxx`) read from the running kernel via drgn.

Input  (per-prog-type view from resolve.py, in this directory):
  { "XDP": { "25": {"proto": "bpf_xdp_event_output_proto", ...}, ...}, ...}

Output (per-proto view, in ../):
  { "bpf_xdp_event_output_proto": {
        "func_id":    25,
        "func_name":  "bpf_perf_event_output",
        "prog_types": ["XDP"] },
    ... }

Rows where the dispatcher returned NULL are dropped, so prog_types is
exactly the set of program types allowed to call that helper.

Requires root (drgn reads /proc/kcore for the enum)."""

import json
import sys
from collections import defaultdict
from pathlib import Path

import drgn

_HERE = Path(__file__).resolve().parent
_IN   = _HERE / "dispatch_map.json"
_OUT  = _HERE.parent / "probed_proto_callers.json"
_VERDICTS = _HERE / "dispatch_verdicts.json"
_DESCRIPTORS = _HERE.parent / "kernel_proto_descriptors.json"
_ATTRIBUTIONS = _HERE / "ambiguous_proto_attributions.json"

def _merge_verdicts(by_proto: dict, name_by_id: dict) -> None:
    """Fold the driver's verifier-verdict map into by_proto.

    The kretprobe pipeline is blind to helpers resolved directly inside
    dispatchers the kernel builds without an ftrace prologue
    (kernel/trace/bpf_trace.c: tracing_prog_func_proto, kprobe_prog_func_proto,
    ...), so e.g. seq_printf never shows up for TRACING. driver.py captures
    those from the verifier's own allow/deny verdict instead. Here we map each
    allowed (prog_type, func_id) to a proto via the descriptor dump and add the
    prog type. func_id is not unique across protos, so attribute only when
    unambiguous (single candidate, or a single one the kretprobe never saw) or
    when the choice cannot matter (all candidate descriptors are identical
    apart from their name, so any attribution yields the same contract; then
    add the prog type to every candidate); otherwise warn and skip
    """
    if not (_VERDICTS.exists() and _DESCRIPTORS.exists()):
        print("cleanup: no dispatch_verdicts.json/kernel_proto_descriptors.json; "
              "skipping verdict merge", file=sys.stderr)
        return

    verdicts = json.loads(_VERDICTS.read_text())
    descriptors = json.loads(_DESCRIPTORS.read_text())
    attributions = (
        json.loads(_ATTRIBUTIONS.read_text()) if _ATTRIBUTIONS.exists() else {}
    )
    protos_by_fid: dict[int, list[str]] = defaultdict(list)
    desc_by_name: dict[str, dict] = {}
    for d in descriptors:
        protos_by_fid[d["func_id"]].append(d["name"])
        desc_by_name[d["name"]] = {k: v for k, v in d.items() if k != "name"}

    def interchangeable(protos: list[str]) -> bool:
        """All protos declare the same descriptor apart from their name."""
        first = desc_by_name[protos[0]]
        return all(desc_by_name[p] == first for p in protos[1:])
    # protos the kretprobe already resolved for at least one prog type
    seen = {p for p, s in by_proto.items() if s["prog_types"]}

    added = ambiguous = 0
    for pt, fids in verdicts.items():
        for fid_s, allowed in fids.items():
            if not allowed:
                continue
            fid = int(fid_s)
            cands = protos_by_fid.get(fid, [])
            if not cands:
                print(f"warning: verdict allows func_id {fid} for {pt} but no "
                      f"proto carries that id in the descriptors", file=sys.stderr)
                continue
            if any(pt in by_proto.get(p, {}).get("prog_types", []) for p in cands):
                continue  # kretprobe already attributed this (prog_type, proto)
            attributed = attributions.get(pt, {}).get(fid_s)
            if attributed is not None:
                if attributed not in cands:
                    raise ValueError(
                        f"invalid attribution for ({pt}, {fid}): {attributed} "
                        f"is not one of {cands}"
                    )
                targets = [attributed]
            elif len(cands) == 1:
                targets = cands
            else:
                unseen = [p for p in cands if p not in seen]
                if len(unseen) == 1:
                    targets = unseen
                elif interchangeable(cands):
                    targets = cands
                else:
                    ambiguous += 1
                    print(f"warning: cannot disambiguate proto for func_id {fid} "
                          f"({pt}) among {cands}; skipping", file=sys.stderr)
                    continue
            for target in targets:
                slot = by_proto[target]
                if slot["func_id"] is None:
                    slot["func_id"]   = fid
                    slot["func_name"] = name_by_id.get(fid)
                if pt not in slot["prog_types"]:
                    slot["prog_types"].append(pt)
                    added += 1
    print(f"cleanup: verdict merge added {added} (prog_type, proto) "
          f"attributions, {ambiguous} ambiguous skipped", file=sys.stderr)

def main() -> int:
    # Load vmlinux debug info only — drgn's default also pulls in every
    # currently-loaded module, which spams "missing debugging symbols for X"
    # for any module without DWARF. We just need `enum bpf_func_id` from
    # vmlinux, so skip modules entirely.
    prog = drgn.Program()
    prog.set_kernel()
    prog.load_debug_info(main=True)

    # Convert the enum spelling `BPF_FUNC_xxx` to the C helper symbol
    # `bpf_xxx` — that's the kernel's own convention (BPF_CALL_N(bpf_xxx)
    # generates both the enum entry and the function definition).
    name_by_id: dict[int, str] = {
        int(e.value): "bpf_" + e.name[len("BPF_FUNC_"):]
        for e in prog.type("enum bpf_func_id").enumerators
        if e.name.startswith("BPF_FUNC_") and int(e.value) != 0
    }

    with open(_IN) as f:
        m = json.load(f)

    by_proto: dict[str, dict] = defaultdict(
        lambda: {"func_id": None, "func_name": None, "prog_types": []}
    )
    for pt, fids in m.items():
        for fid_s, entry in fids.items():
            proto = entry.get("proto")
            if proto is None:
                continue
            fid = int(fid_s)
            slot = by_proto[proto]
            if slot["func_id"] is None:
                slot["func_id"]   = fid
                slot["func_name"] = name_by_id.get(fid)
            elif slot["func_id"] != fid:
                print(f"warning: {proto} reported for fid {slot['func_id']} "
                      f"and fid {fid} ({pt})", file=sys.stderr)
            slot["prog_types"].append(pt)

    _merge_verdicts(by_proto, name_by_id)

    out = {}
    for proto in sorted(by_proto):
        slot = by_proto[proto]
        slot["prog_types"] = sorted(set(slot["prog_types"]))
        out[proto] = slot

    with open(_OUT, "w") as f:
        json.dump(out, f, indent=2)
        f.write("\n")
    print(f"wrote {_OUT}: {len(out)} protos", file=sys.stderr)
    return 0

if __name__ == "__main__":
    sys.exit(main())
