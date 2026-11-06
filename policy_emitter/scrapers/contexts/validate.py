#!/usr/bin/env python3
"""Validate ctx_layouts.json against the running kernel's verifier.

For each program type, sweep (offset, size, {read, write, ldsx}) and submit one
tiny program per cell with BPF_PROG_LOAD. The program is never attached or run:
BPF_PROG_LOAD invokes the verifier and returns accept/reject + the verifier log,
which is exactly the oracle the JSON claims to mirror. Needs CAP_BPF (run as root).

Usage:
    sudo python3 validate.py [--prog-type NAME] [--header PATH]
                             [--syscall-nr N] [--verbose]

Exit code is non-zero if any live mismatch is found.
"""

import argparse
import ctypes
import json
import os
import re
import struct
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_JSON = os.path.join(HERE, "ctx_layouts.json")
DEFAULT_HEADER = os.path.normpath(
    os.path.join(HERE, "..", "..", "..", "..", "linux", "include", "uapi", "linux", "bpf.h")
)

NR_BPF = 321  # x86-64; override with --syscall-nr
BPF_PROG_LOAD = 5
BPF_F_SLEEPABLE = 1 << 4

# opcode = class | size | mode  (BPF ISA, see RFC 9669)
LDX = {1: 0x71, 2: 0x69, 4: 0x61, 8: 0x79}          # BPF_LDX|BPF_MEM|sz
LDXSX = {1: 0x91, 2: 0x99, 4: 0x81}                  # BPF_LDX|BPF_MEMSX|sz (no DW)
STX = {1: 0x73, 2: 0x6B, 4: 0x63, 8: 0x7B}          # BPF_STX|BPF_MEM|sz
MOV64_IMM = 0xB7
MOV64_REG = 0xBF                                     # BPF_ALU64|BPF_MOV|BPF_X
ADD64_IMM = 0x07                                     # BPF_ALU64|BPF_ADD|BPF_K
EXIT = 0x95
S16 = 0x7FFF                                          # insn.off is __s16

CTX_REJECT_MARKERS = (
    "invalid bpf_context access",
    "invalid bpf context access",
    "misaligned",
)

# Prog types that need a non-zero expected_attach_type just to load, even though
# none of their fields are attach-guarded. Tried only if attach=0 calibration fails.
FALLBACK_ATTACH = {
    "BPF_PROG_TYPE_SK_LOOKUP": ["BPF_SK_LOOKUP"],
    "BPF_PROG_TYPE_SK_SKB": ["BPF_SK_SKB_STREAM_VERDICT", "BPF_SK_SKB_STREAM_PARSER"],
    "BPF_PROG_TYPE_SK_MSG": ["BPF_SK_MSG_VERDICT"],
    "BPF_PROG_TYPE_FLOW_DISSECTOR": ["BPF_FLOW_DISSECTOR"],
    "BPF_PROG_TYPE_SOCK_OPS": ["BPF_CGROUP_SOCK_OPS"],
    "BPF_PROG_TYPE_LIRC_MODE2": ["BPF_LIRC_MODE2"],
    "BPF_PROG_TYPE_CGROUP_SYSCTL": ["BPF_CGROUP_SYSCTL"],
    "BPF_PROG_TYPE_CGROUP_DEVICE": ["BPF_CGROUP_DEVICE"],
    "BPF_PROG_TYPE_NETFILTER": ["BPF_NETFILTER"],
}

PROG_FLAGS = {"BPF_PROG_TYPE_SYSCALL": BPF_F_SLEEPABLE}


# --------------------------------------------------------------------------
# inputs
# --------------------------------------------------------------------------
def load_json(path):
    with open(path) as f:
        return json.load(f)


def parse_enum(text, enum_name):
    m = re.search(r"enum\s+%s\s*\{(.*?)\}" % enum_name, text, re.S)
    if not m:
        return {}
    body, val, out = m.group(1), 0, {}
    for tok in body.split(","):
        tok = re.sub(r"/\*.*?\*/", "", tok, flags=re.S).strip()
        if not tok:
            continue
        em = re.match(r"([A-Za-z_][A-Za-z0-9_]*)\s*(?:=\s*(0x[0-9a-fA-F]+|\d+))?", tok)
        if not em:
            continue
        if em.group(2) is not None:
            val = int(em.group(2), 0)
        out[em.group(1)] = val
        val += 1
    return out


def load_enums(header):
    with open(header) as f:
        text = f.read()
    return (parse_enum(text, "bpf_prog_type"), parse_enum(text, "bpf_attach_type"))


# --------------------------------------------------------------------------
# expected-access predicate
# --------------------------------------------------------------------------
def _window_ok(row, off, size):
    return row["offset"] <= off and off + size <= row["offset"] + row["size"]


def _dir_active(d, attach_val, attach_enum):
    if d is None:
        return False
    if d.get("offloaded"):  # SW probe path: offload-only access is inactive
        return False
    at = d.get("attach_type")
    if at:
        vals = {attach_enum.get(a) for a in at}
        if attach_val not in vals:
            return False
    # capability gates: we probe privileged, so a granted cap is active.
    return True


def allowed(rows, off, size, mode, attach_val, attach_enum):
    """mode in {'r','w','sx'}."""
    if off % size != 0:
        return False
    if mode == "sx" and size == 8:
        return False
    for r in rows:
        if not _window_ok(r, off, size):
            continue
        # offsetof-style fields (kernel `case offsetof(...)`) allow narrow loads
        # only at the field base; interior bytes fall through to the size-default
        # arm and are rejected. bpf_ctx_range fields stay byte-addressable.
        if r.get("interior", True) is False and off != r["offset"]:
            continue
        d = r["read"] if mode in ("r", "sx") else r["write"]
        if not _dir_active(d, attach_val, attach_enum):
            continue
        if size not in d["access_sizes"]:
            continue
        if mode == "sx" and r.get("sign_extend") is False:
            continue
        return True
    return False


# --------------------------------------------------------------------------
# bpf(2) plumbing
# --------------------------------------------------------------------------
libc = ctypes.CDLL("libc.so.6", use_errno=True)
libc.syscall.restype = ctypes.c_long


def _insn(code, dst=0, src=0, off=0, imm=0):
    return struct.pack("<BBhi", code & 0xFF, ((src & 0xF) << 4) | (dst & 0xF), off, imm)


def _ctx_ptr(off):
    """Insns to address ctx+off as (prefix, load_off, base_reg). insn.off is a
    signed 16-bit field, so large offsets (e.g. the 64K syscall ctx) are folded
    into a base register via constant ctx pointer arithmetic and loaded at 0."""
    if -0x8000 <= off <= S16:
        return b"", off, 1
    return _insn(MOV64_REG, dst=3, src=1) + _insn(ADD64_IMM, dst=3, imm=off), 0, 3


def prog_read(off, size, sx, retval):
    pre, ldoff, base = _ctx_ptr(off)
    code = (LDXSX if sx else LDX)[size]
    return pre + _insn(code, dst=2, src=base, off=ldoff) + _insn(MOV64_IMM, dst=0, imm=retval) + _insn(EXIT)


def prog_write(off, size, retval):
    pre, ldoff, base = _ctx_ptr(off)
    return (
        pre
        + _insn(MOV64_IMM, dst=2, imm=0)
        + _insn(STX[size], dst=base, src=2, off=ldoff)
        + _insn(MOV64_IMM, dst=0, imm=retval)
        + _insn(EXIT)
    )


def prog_canary(retval):
    return _insn(MOV64_IMM, dst=0, imm=retval) + _insn(EXIT)


_LOG = ctypes.create_string_buffer(8192)
_LIC = ctypes.create_string_buffer(b"GPL")


def bpf_load(prog_type, insns, attach=0, flags=0, want_log=True):
    """Return (fd, log). fd<0 means rejected; caller closes fd>=0."""
    insn_buf = ctypes.create_string_buffer(insns, len(insns))
    attr = bytearray(144)
    struct.pack_into("<II", attr, 0, prog_type, len(insns) // 8)
    struct.pack_into("<Q", attr, 8, ctypes.addressof(insn_buf))
    struct.pack_into("<Q", attr, 16, ctypes.addressof(_LIC))
    if want_log:
        struct.pack_into("<II", attr, 24, 1, len(_LOG))
        struct.pack_into("<Q", attr, 32, ctypes.addressof(_LOG))
    struct.pack_into("<I", attr, 44, flags)
    struct.pack_into("<I", attr, 68, attach)
    _LOG[0] = 0
    attr_buf = ctypes.create_string_buffer(bytes(attr), len(attr))
    fd = libc.syscall(
        ctypes.c_long(NR_BPF),
        ctypes.c_long(BPF_PROG_LOAD),
        ctypes.c_void_p(ctypes.addressof(attr_buf)),
        ctypes.c_long(len(attr_buf)),
    )
    log = _LOG.value.decode("utf-8", "replace") if want_log else ""
    return fd, log


def classify(fd, log):
    if fd >= 0:
        os.close(fd)
        return "ALLOW"
    if any(m in log for m in CTX_REJECT_MARKERS):
        return "CTX_REJECT"
    return "NONCTX_REJECT"


def calibrate(prog_type, attach, flags):
    """Find a return value that loads a no-ctx-access prog; None if unloadable."""
    for rv in (0, 1, 2):
        fd, _ = bpf_load(prog_type, prog_canary(rv), attach, flags, want_log=False)
        if fd >= 0:
            os.close(fd)
            return rv
    return None


# --------------------------------------------------------------------------
# live probing
# --------------------------------------------------------------------------
def offsets_for(rows):
    hi = max(r["offset"] + r["size"] for r in rows)
    if hi <= 512:
        return list(range(0, hi + 8))
    pts = {0, 1, 7, 8, 9, hi - 8, hi - 1, hi, hi + 1, hi + 7}
    for r in rows:
        o, s = r["offset"], r["size"]
        pts.update({o - 1, o, o + 1, o + s // 2, o + s - 1, o + s, o + s + 1})
    return sorted(o for o in pts if o >= 0)


def attach_candidates(pt, rows, attach_enum):
    refs = set()
    for r in rows:
        for d in (r["read"], r["write"]):
            if d and d.get("attach_type"):
                refs.update(d["attach_type"])
    cands = [0] + [attach_enum[a] for a in sorted(refs) if a in attach_enum]
    for a in FALLBACK_ATTACH.get(pt, []):
        if a in attach_enum:
            cands.append(attach_enum[a])
    seen, out = set(), []
    for c in cands:
        if c not in seen:
            seen.add(c)
            out.append(c)
    return out


def probe_cells(rows):
    for off in offsets_for(rows):
        for size in (1, 2, 4, 8):
            yield off, size, "r"
            yield off, size, "w"
            if size != 8:
                yield off, size, "sx"


def live_validate(layouts, prog_enum, attach_enum, prog_filter, verbose):
    results = {}
    for pt, rows in layouts.items():
        if prog_filter and pt != prog_filter:
            continue
        if rows is None:
            results[pt] = {"skipped": "null layout (BTF/attach-determined)"}
            continue
        if pt not in prog_enum:
            results[pt] = {"skipped": "unknown prog type"}
            continue
        ptv = prog_enum[pt]
        flags = PROG_FLAGS.get(pt, 0)
        cands = attach_candidates(pt, rows, attach_enum)

        loaded_any = False
        agg = {"ok": 0, "stricter": 0, "looser": 0, "inconclusive": 0,
               "mismatches": [], "attach_tried": [], "attach_loaded": []}
        for attach in cands:
            rv = calibrate(ptv, attach, flags)
            agg["attach_tried"].append(attach)
            if rv is None:
                continue
            loaded_any = True
            agg["attach_loaded"].append(attach)
            for off, size, mode in probe_cells(rows):
                exp = allowed(rows, off, size, mode, attach, attach_enum)
                if mode == "r":
                    insns = prog_read(off, size, False, rv)
                elif mode == "sx":
                    insns = prog_read(off, size, True, rv)
                else:
                    insns = prog_write(off, size, rv)
                fd, log = bpf_load(ptv, insns, attach, flags)
                verdict = classify(fd, log)

                if exp and verdict == "ALLOW":
                    agg["ok"] += 1
                elif not exp and verdict == "CTX_REJECT":
                    agg["ok"] += 1
                elif verdict == "NONCTX_REJECT":
                    agg["inconclusive"] += 1
                elif not exp and verdict == "ALLOW":
                    agg["stricter"] += 1
                    agg["mismatches"].append(
                        (attach, off, size, mode, "JSON rejects, kernel ALLOWS"))
                elif exp and verdict == "CTX_REJECT":
                    agg["looser"] += 1
                    agg["mismatches"].append(
                        (attach, off, size, mode, "JSON allows, kernel REJECTS: " + log.strip()[:80]))
        if not loaded_any:
            results[pt] = {"skipped": f"no loadable attach type (tried {cands})"}
        else:
            results[pt] = agg
        if verbose and isinstance(results[pt], dict) and "ok" in results[pt]:
            r = results[pt]
            print(f"  {pt}: ok={r['ok']} stricter={r['stricter']} "
                  f"looser={r['looser']} inconclusive={r['inconclusive']}")
    return results


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------
def main():
    global NR_BPF
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--json", default=DEFAULT_JSON)
    ap.add_argument("--header", default=DEFAULT_HEADER, help="kernel uapi bpf.h for enums")
    ap.add_argument("--prog-type", help="restrict probing to one BPF_PROG_TYPE_*")
    ap.add_argument("--syscall-nr", type=int, default=NR_BPF)
    ap.add_argument("--dump", help="write every mismatch cell to this JSON file")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()
    NR_BPF = args.syscall_nr

    layouts = load_json(args.json)
    prog_enum, attach_enum = load_enums(args.header)
    if not prog_enum:
        print(f"error: could not parse enums from {args.header}", file=sys.stderr)
        sys.exit(2)

    if os.geteuid() != 0:
        print("error: live probing needs CAP_BPF; re-run with sudo", file=sys.stderr)
        sys.exit(2)

    print("== live validation (BPF_PROG_LOAD probes) ==")
    results = live_validate(layouts, prog_enum, attach_enum, args.prog_type, args.verbose)
    tot = {"ok": 0, "stricter": 0, "looser": 0, "inconclusive": 0}
    for pt, r in sorted(results.items()):
        if "skipped" in r:
            print(f"  - {pt}: SKIPPED ({r['skipped']})")
            continue
        for k in tot:
            tot[k] += r[k]
        flag = "" if not (r["stricter"] or r["looser"]) else "  <-- MISMATCH"
        print(f"  - {pt}: ok={r['ok']} stricter={r['stricter']} "
              f"looser={r['looser']} inconclusive={r['inconclusive']}{flag}")
        for (att, off, size, mode, why) in r["mismatches"][:12]:
            print(f"        attach={att} off={off} size={size} {mode}: {why}")
    print(f"\n  TOTAL ok={tot['ok']} stricter={tot['stricter']} "
          f"looser={tot['looser']} inconclusive={tot['inconclusive']}")
    print("  (looser = JSON permits an access the kernel rejects -- soundness-critical;")
    print("   stricter = JSON rejects an access the kernel permits -- safe but incomplete)")

    if args.dump:
        out = []
        for pt, r in results.items():
            for (att, off, size, mode, why) in r.get("mismatches", []):
                out.append({"prog_type": pt, "attach": att, "offset": off,
                            "size": size, "mode": mode, "detail": why})
        with open(args.dump, "w") as f:
            json.dump(out, f, indent=2)
        print(f"\n  wrote {len(out)} mismatch cells to {args.dump}")

    sys.exit(1 if (tot["stricter"] or tot["looser"]) else 0)


if __name__ == "__main__":
    main()
