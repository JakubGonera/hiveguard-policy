#!/usr/bin/env python3
"""Parse bpftrace EV lines from probe.bt and emit two JSON artifacts:

  dispatch_map.json   — depth=1 (outer dispatcher) observations, the
                        authoritative (prog_type -> {func_id -> proto}) map
  dispatch_chain.json — every observation including inner fallbacks

Each EV line has the form:
  EV disp=<sym> d=<int> pt=<int> fid=<int> addr=<hex>

Proto symbol is resolved by exact address match against `kallsyms.snapshot`
(taken in run.sh while we still hold root). Bpftrace's own ksym() rounds to
the nearest preceding kallsyms entry, which is wrong for data symbols.

Usage: resolve.py <events.log> [--kallsyms FILE] [--out-dir DIR]
"""

import argparse
import json
import re
import sys
from collections import defaultdict

# enum bpf_prog_type, kernel UAPI.
PROG_TYPES = {
    0:  "UNSPEC",
    1:  "SOCKET_FILTER",
    2:  "KPROBE",
    3:  "SCHED_CLS",
    4:  "SCHED_ACT",
    5:  "TRACEPOINT",
    6:  "XDP",
    7:  "PERF_EVENT",
    8:  "CGROUP_SKB",
    9:  "CGROUP_SOCK",
    10: "LWT_IN",
    11: "LWT_OUT",
    12: "LWT_XMIT",
    13: "SOCK_OPS",
    14: "SK_SKB",
    15: "CGROUP_DEVICE",
    16: "SK_MSG",
    17: "RAW_TRACEPOINT",
    18: "CGROUP_SOCK_ADDR",
    19: "LWT_SEG6LOCAL",
    20: "LIRC_MODE2",
    21: "SK_REUSEPORT",
    22: "FLOW_DISSECTOR",
    23: "CGROUP_SYSCTL",
    24: "RAW_TRACEPOINT_WRITABLE",
    25: "CGROUP_SOCKOPT",
    26: "TRACING",
    27: "STRUCT_OPS",
    28: "EXT",
    29: "LSM",
    30: "SK_LOOKUP",
    31: "SYSCALL",
    32: "NETFILTER",
}

_LINE = re.compile(
    r"EV\s+disp=(\S+)\s+d=(\d+)\s+pt=(-?\d+)\s+fid=(-?\d+)\s+addr=(0x[0-9a-fA-F]+)"
)

def _load_kallsyms(path: str) -> dict[int, str]:
    """Return {address -> symbol_name} for every `*_proto` data symbol."""
    out: dict[int, str] = {}
    with open(path) as f:
        for line in f:
            parts = line.split(None, 3)
            if len(parts) < 3:
                continue
            addr_s, kind, name = parts[0], parts[1], parts[2].strip()
            if not name.endswith("_proto"):
                continue
            try:
                addr = int(addr_s, 16)
            except ValueError:
                continue
            if addr == 0:
                continue  # kernel zeroes kallsyms when kptr_restrict is set
            out[addr] = name
    return out

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("events")
    ap.add_argument("--kallsyms", default="kallsyms.snapshot")
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()

    try:
        sym = _load_kallsyms(args.kallsyms)
    except FileNotFoundError:
        print(f"resolve: no kallsyms snapshot at {args.kallsyms}; "
              f"proto names will be null", file=sys.stderr)
        sym = {}

    top:   dict[str, dict[str, dict]] = defaultdict(dict)
    chain: list[dict] = []

    with open(args.events) as f:
        for line in f:
            m = _LINE.search(line)
            if not m:
                continue
            disp, depth_s, pt_s, fid_s, addr_s = m.groups()
            depth = int(depth_s)
            pt    = int(pt_s)
            fid   = int(fid_s)
            if fid < 0:
                continue
            addr = int(addr_s, 16)
            pt_name = PROG_TYPES.get(pt, f"UNK_{pt}")
            entry = {
                "disp":  disp,
                "depth": depth,
                "proto": sym.get(addr),
                "addr":  addr_s,
            }
            chain.append({"prog_type": pt_name, "func_id": fid, **entry})
            if depth == 1:
                key = str(fid)
                if key in top[pt_name]:
                    continue
                top[pt_name][key] = entry

    top_sorted = {
        pt: dict(sorted(fids.items(), key=lambda kv: int(kv[0])))
        for pt, fids in sorted(top.items())
    }

    with open(f"{args.out_dir}/dispatch_map.json", "w") as f:
        json.dump(top_sorted, f, indent=2)
        f.write("\n")
    with open(f"{args.out_dir}/dispatch_chain.json", "w") as f:
        json.dump(chain, f, indent=2)
        f.write("\n")

    total = sum(len(v) for v in top_sorted.values())
    print(f"dispatch_map.json: {len(top_sorted)} prog types, "
          f"{total} (prog_type, func_id) bindings", file=sys.stderr)
    print(f"dispatch_chain.json: {len(chain)} raw observations",
          file=sys.stderr)
    return 0

if __name__ == "__main__":
    sys.exit(main())
