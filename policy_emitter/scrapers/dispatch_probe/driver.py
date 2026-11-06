#!/usr/bin/env python3
"""Drive synthetic BPF_PROG_LOAD calls so the verifier exercises every
(prog_type, func_id) helper lookup. The companion probe.bt records what the
dispatcher returned. We don't care if the load succeeds — the kprobe fires
inside bpf_get_helper_proto either way.

Run via run.sh (needs root / CAP_BPF / CAP_SYS_ADMIN).
"""

import ctypes
import errno
import json
import os
import resource
import struct
import sys
import time

# ---- syscall plumbing ------------------------------------------------------

_NR_BPF = {
    "x86_64": 321,
    "aarch64": 280,
    "riscv64": 280,
}.get(os.uname().machine)
if _NR_BPF is None:
    sys.exit(f"unsupported arch: {os.uname().machine}")

_PR_SET_NAME = 15
BPF_PROG_LOAD = 5
BPF_BTF_LOAD  = 18

# BTF binary format constants (include/uapi/linux/btf.h)
_BTF_MAGIC           = 0xEB9F
_BTF_KIND_STRUCT     = 4
_BTF_KIND_FUNC       = 12
_BTF_KIND_FUNC_PROTO = 13
_BTF_FUNC_GLOBAL     = 1

_libc = ctypes.CDLL("libc.so.6", use_errno=True)

def _set_comm(name: bytes):
    # Use prctl so kprobe filter `comm == "proto_drv"` scopes to us only.
    buf = ctypes.create_string_buffer(name[:15] + b"\x00")
    if _libc.prctl(_PR_SET_NAME, ctypes.cast(buf, ctypes.c_void_p), 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "prctl(PR_SET_NAME)")

# ---- bpf_attr (prefix sufficient for PROG_LOAD) ----------------------------

class BpfProgLoadAttr(ctypes.Structure):
    _pack_ = 1
    _fields_ = [
        ("prog_type",            ctypes.c_uint32),
        ("insn_cnt",             ctypes.c_uint32),
        ("insns",                ctypes.c_uint64),
        ("license",              ctypes.c_uint64),
        ("log_level",            ctypes.c_uint32),
        ("log_size",             ctypes.c_uint32),
        ("log_buf",              ctypes.c_uint64),
        ("kern_version",         ctypes.c_uint32),
        ("prog_flags",           ctypes.c_uint32),
        ("prog_name",            ctypes.c_char * 16),
        ("prog_ifindex",         ctypes.c_uint32),
        ("expected_attach_type", ctypes.c_uint32),
        ("prog_btf_fd",          ctypes.c_uint32),
        ("func_info_rec_size",   ctypes.c_uint32),
        ("func_info",            ctypes.c_uint64),
        ("func_info_cnt",        ctypes.c_uint32),
        ("line_info_rec_size",   ctypes.c_uint32),
        ("line_info",            ctypes.c_uint64),
        ("line_info_cnt",        ctypes.c_uint32),
        ("attach_btf_id",        ctypes.c_uint32),
        ("attach_prog_fd",       ctypes.c_uint32),
        ("core_relo_cnt",        ctypes.c_uint32),
        ("fd_array",             ctypes.c_uint64),
        ("core_relos",           ctypes.c_uint64),
        ("core_relo_rec_size",   ctypes.c_uint32),
        ("log_true_size",        ctypes.c_uint32),
        ("prog_token_fd",        ctypes.c_uint32),
        ("fd_array_cnt",         ctypes.c_uint32),
    ]

# Two-instruction body: `call <fid>; exit`. The verifier reaches
# bpf_get_helper_proto before any arg type-checking, so we don't need to set
# up r1..r5 — the dispatcher runs regardless of arg validity.
_BPF_JMP_CALL = 0x85
_BPF_JMP_EXIT = 0x95

def _insns(func_id: int) -> bytes:
    return (
        struct.pack("<BBhi", _BPF_JMP_CALL, 0, 0, func_id) +
        struct.pack("<BBhi", _BPF_JMP_EXIT, 0, 0, 0)
    )

_LICENSE = ctypes.create_string_buffer(b"GPL")
_LICENSE_ADDR = ctypes.cast(_LICENSE, ctypes.c_void_p).value

# enum bpf_attach_type values (include/uapi/linux/bpf.h).
BPF_LSM_MAC    = 27   # the only valid attach for LSM besides BPF_LSM_CGROUP
BPF_TRACE_ITER = 28   # tracing_prog_func_proto only returns the
                      # seq_printf/seq_write/seq_printf_btf protos under it
BPF_F_SLEEPABLE = 1 << 4  # prog_flags; SYSCALL progs must be sleepable

# A prog type's helper set can depend on expected_attach_type: some dispatchers
# (notably tracing_prog_func_proto) return certain protos only under one attach
# type, so we probe each prog type under every attach type that exposes a
# distinct set. The list also satisfies bpf_prog_load_check_attach(), which
# rejects some prog types at attr validation unless expected_attach_type is one
# of their valid values. Values: enum bpf_attach_type, include/uapi/linux/bpf.h.
EXPECTED_ATTACH_TYPES: dict[int, list[int]] = {
    18: [8],               # CGROUP_SOCK_ADDR -> BPF_CGROUP_INET4_BIND
    20: [16],              # LIRC_MODE2       -> BPF_LIRC_MODE2
    25: [21],              # CGROUP_SOCKOPT   -> BPF_CGROUP_GETSOCKOPT
    30: [36],              # SK_LOOKUP        -> BPF_SK_LOOKUP
    32: [45],              # NETFILTER        -> BPF_NETFILTER
    26: [BPF_TRACE_ITER],  # TRACING -> iter: exposes seq_printf/seq_write/...
    29: [BPF_LSM_MAC],     # LSM: anything else dies silently in the verifier's
                           # bpf_check_attach_target attach-type switch
}
_DEFAULT_ATTACH_TYPES = [0]

# enum bpf_prog_type names, used to key the verdict map (must match resolve.py).
PROG_TYPE_NAMES = {
    1:  "SOCKET_FILTER",          2:  "KPROBE",
    3:  "SCHED_CLS",              4:  "SCHED_ACT",
    5:  "TRACEPOINT",             6:  "XDP",
    7:  "PERF_EVENT",             8:  "CGROUP_SKB",
    9:  "CGROUP_SOCK",            10: "LWT_IN",
    11: "LWT_OUT",                12: "LWT_XMIT",
    13: "SOCK_OPS",               14: "SK_SKB",
    15: "CGROUP_DEVICE",          16: "SK_MSG",
    17: "RAW_TRACEPOINT",         18: "CGROUP_SOCK_ADDR",
    19: "LWT_SEG6LOCAL",          20: "LIRC_MODE2",
    21: "SK_REUSEPORT",           22: "FLOW_DISSECTOR",
    23: "CGROUP_SYSCTL",          24: "RAW_TRACEPOINT_WRITABLE",
    25: "CGROUP_SOCKOPT",         26: "TRACING",
    27: "STRUCT_OPS",             28: "EXT",
    29: "LSM",                    30: "SK_LOOKUP",
    31: "SYSCALL",                32: "NETFILTER",
}

# Reused verifier-log buffer. log_level=1 turns the load into an allow/deny
# oracle: get_func_proto returning NULL makes the verifier print "program of
# this type cannot use helper ..." (verifier.c:check_helper_call); once a proto
# is found it proceeds to register checks. This is independent of ftrace, so it
# observes helpers resolved inside dispatchers the kretprobe can't attach to.
_LOG_SIZE     = 1 << 16
_LOG_BUF      = ctypes.create_string_buffer(_LOG_SIZE)
_LOG_BUF_ADDR = ctypes.cast(_LOG_BUF, ctypes.c_void_p).value

_DENY_MARKERS = (b"cannot use helper", b"invalid func")
_REG_MARKERS  = (b"R0", b"R1", b"R2", b"R3", b"R4", b"R5", b"R6", b"R10")

def _classify(loaded: bool, log: bytes) -> str:
    """Map a load outcome to allow / deny / unreached.

    A register reference (R0..R10) can only appear *after* get_func_proto
    returned a non-NULL proto and the verifier started checking the call, so it
    is sound positive evidence of "allowed"; the deny markers are the exact
    NULL-proto / out-of-range strings. Anything else (attach-phase failure,
    empty log) carries no signal about this helper.
    """
    if any(m in log for m in _DENY_MARKERS):
        return "deny"
    if loaded or any(m in log for m in _REG_MARKERS):
        return "allow"
    return "unreached"

# ---- BTF: parser for kernel vmlinux BTF, builder for an in-process BTF
# blob, and BPF_BTF_LOAD wrapper. Needed because STRUCT_OPS demands
# attach_btf_id pointing at a kernel struct, and EXT demands
# attach_btf_id + attach_prog_fd pointing into a *loaded* target program's
# BTF func_info. These are runtime values: BTF type ids vary per build,
# so we never hardcode them.

def _btf_info(kind: int, vlen: int = 0, kflag: int = 0) -> int:
    return (kflag << 31) | (kind << 24) | (vlen & 0xFFFF)

def _find_btf_type_id(path: str, name: str,
                      want_kind: int = _BTF_KIND_STRUCT) -> int | None:
    """Walk a BTF blob and return the 1-indexed type id of a `want_kind` type
    whose name matches `name`, or None if absent."""
    try:
        with open(path, "rb") as f:
            data = f.read()
    except (FileNotFoundError, PermissionError):
        return None
    if len(data) < 24:
        return None
    magic, version, _, hdr_len, type_off, type_len, str_off, str_len = (
        struct.unpack_from("<HBBIIIII", data, 0))
    if magic != _BTF_MAGIC or version != 1:
        return None
    types = data[hdr_len + type_off : hdr_len + type_off + type_len]
    strs  = data[hdr_len + str_off  : hdr_len + str_off + str_len]

    # Trailing bytes per kind after the 12-byte btf_type header.
    def _extra(kind: int, vlen: int) -> int:
        # Sizes from struct btf_member/btf_enum/btf_param/etc. in btf.h.
        if kind in (4, 5):   return vlen * 12   # STRUCT / UNION
        if kind == 6:        return vlen * 8    # ENUM
        if kind == 19:       return vlen * 12   # ENUM64
        if kind == 13:       return vlen * 8    # FUNC_PROTO
        if kind == 15:       return vlen * 12   # DATASEC
        if kind == 1:        return 4           # INT
        if kind == 3:        return 12          # ARRAY
        if kind in (14, 17): return 4           # VAR, DECL_TAG
        return 0

    type_id, pos = 0, 0
    while pos + 12 <= len(types):
        type_id += 1
        name_off, info, _ = struct.unpack_from("<III", types, pos)
        kind = (info >> 24) & 0x1F
        vlen = info & 0xFFFF
        pos += 12 + _extra(kind, vlen)
        if kind != want_kind:
            continue
        if name_off >= len(strs):
            continue
        end = strs.find(b"\x00", name_off)
        if end < 0:
            continue
        if strs[name_off:end].decode("ascii", errors="replace") == name:
            return type_id
    return None

def _build_minimal_btf() -> bytes:
    """Build a BTF blob describing `int f(struct __sk_buff *skb)`.

    Why this specific signature: when a target prog is loaded with
    func_info, the verifier runs `btf_is_prog_ctx_type` against its main
    function's signature to decide whether func_info_aux[0] is "reliable".
    EXT later rejects the load with "Cannot replace static functions" if
    that flag was set to unreliable. The check (kernel/bpf/btf.c:6115)
    requires the arg to be a pointer to a *STRUCT* whose name matches the
    target prog_type's canonical ctx — for SOCKET_FILTER that's
    `__sk_buff`. The struct may be empty: the kernel matches by name only
    (comment at btf.c:6172).
    """
    # Strings — offsets used as name_off in types below.
    #  0:  "",  1: "int",  5: "__sk_buff",  15: "skb",  19: "f"
    strings = b"\x00int\x00__sk_buff\x00skb\x00f\x00"

    types  = b""
    # Type 1: INT 'int' — size=4, encoding=signed, 32 bits
    types += struct.pack("<III", 1, _btf_info(1, 0), 4)         # KIND_INT
    types += struct.pack("<I", (1 << 24) | 32)                  # signed|32
    # Type 2: STRUCT '__sk_buff' — empty body (vlen=0, size=0) is sufficient
    types += struct.pack("<III", 5, _btf_info(_BTF_KIND_STRUCT, 0), 0)
    # Type 3: PTR -> type 2
    types += struct.pack("<III", 0, _btf_info(2, 0), 2)         # KIND_PTR
    # Type 4: FUNC_PROTO returning int (type 1), 1 param of type 3
    types += struct.pack("<III", 0, _btf_info(_BTF_KIND_FUNC_PROTO, 1), 1)
    types += struct.pack("<II", 15, 3)                          # param name="skb"
    # Type 5: FUNC global 'f' with proto=type 4
    types += struct.pack("<III", 19, _btf_info(_BTF_KIND_FUNC, _BTF_FUNC_GLOBAL), 4)

    header = struct.pack("<HBBIIIII",
                         _BTF_MAGIC, 1, 0,
                         24,            # hdr_len
                         0,             # type_off
                         len(types),    # type_len
                         len(types),    # str_off
                         len(strings))  # str_len
    return header + types + strings

class BpfBtfLoadAttr(ctypes.Structure):
    _pack_ = 1
    _fields_ = [
        ("btf",               ctypes.c_uint64),
        ("btf_log_buf",       ctypes.c_uint64),
        ("btf_size",          ctypes.c_uint32),
        ("btf_log_size",      ctypes.c_uint32),
        ("btf_log_level",     ctypes.c_uint32),
        ("btf_log_true_size", ctypes.c_uint32),
        ("btf_flags",         ctypes.c_uint32),
        ("btf_token_fd",      ctypes.c_uint32),
    ]

def _btf_load(blob: bytes) -> int:
    buf = ctypes.create_string_buffer(blob, len(blob))
    attr = BpfBtfLoadAttr()
    attr.btf      = ctypes.cast(buf, ctypes.c_void_p).value
    attr.btf_size = len(blob)
    fd = _libc.syscall(_NR_BPF, BPF_BTF_LOAD,
                       ctypes.byref(attr), ctypes.sizeof(attr))
    if fd < 0:
        raise OSError(ctypes.get_errno(), "BPF_BTF_LOAD")
    return fd

def _load_ext_target(btf_fd: int) -> int:
    """Load a minimal SOCKET_FILTER program annotated with func_info so it
    can serve as an EXT freplace target. Body: `mov r0, 0; exit`."""
    body = (struct.pack("<BBhi", 0xb7, 0, 0, 0) +   # mov64 r0, 0
            struct.pack("<BBhi", 0x95, 0, 0, 0))    # exit
    body_buf = ctypes.create_string_buffer(body, len(body))
    # One func_info record: insn_off=0 maps to BTF type id 5 (our FUNC).
    fi = struct.pack("<II", 0, 5)
    fi_buf = ctypes.create_string_buffer(fi, len(fi))
    attr = BpfProgLoadAttr()
    attr.prog_type          = 1   # SOCKET_FILTER
    attr.insn_cnt           = 2
    attr.insns              = ctypes.cast(body_buf, ctypes.c_void_p).value
    attr.license            = _LICENSE_ADDR
    attr.prog_btf_fd        = btf_fd
    attr.func_info_rec_size = 8
    attr.func_info          = ctypes.cast(fi_buf, ctypes.c_void_p).value
    attr.func_info_cnt      = 1
    fd = _libc.syscall(_NR_BPF, BPF_PROG_LOAD,
                       ctypes.byref(attr), ctypes.sizeof(attr))
    if fd < 0:
        raise OSError(ctypes.get_errno(), "BPF_PROG_LOAD (EXT target)")
    return fd

# Populated at startup. If lookup/build fails, the corresponding prog_type
# silently skips back to the pre-fix EINVAL behaviour for that single type.
_STRUCT_OPS_BTF_ID: int = 0   # set by main(), 0 == "no value found"
_EXT_ATTACH_BTF_ID: int = 0
_EXT_ATTACH_PROG_FD: int = 0
_EXT_BTF_FD: int = 0          # kept open for the whole run; used as prog_btf_fd
# Module-level holders so the underlying ctypes buffers outlive _try_load.
_EXT_FUNC_INFO_BUF = None     # ctypes buffer: array of struct bpf_func_info
_EXT_FUNC_INFO_PTR = 0        # address of _EXT_FUNC_INFO_BUF
_TRACE_ITER_BTF_ID: int = 0   # FUNC id of a bpf_iter_* target; needed so a
                              # TRACING/iter load passes check_attach_btf_id and
                              # reaches the helper check (0 == "no value found").
_LSM_HOOK_BTF_ID: int = 0     # FUNC id of a bpf_lsm_* hook, same role for LSM.

def _attach_btf_id_for(prog_type: int, attach_type: int) -> int:
    if prog_type == 26 and attach_type == BPF_TRACE_ITER:
        return _TRACE_ITER_BTF_ID
    if prog_type == 29 and attach_type == BPF_LSM_MAC:
        return _LSM_HOOK_BTF_ID
    return 0

# (pt, at) pairs that cannot pass check_attach_btf_id without a target id.
_NEEDS_ATTACH_BTF_ID = {(26, BPF_TRACE_ITER), (29, BPF_LSM_MAC)}

def _try_load(prog_type: int, func_id: int, expected_attach_type: int,
              attach_btf_id: int = 0) -> tuple[int, str]:
    """Issue one BPF_PROG_LOAD with log capture.

    Returns (0 or -errno, verdict) where verdict is "allow" / "deny" /
    "unreached" per _classify().
    """
    body = _insns(func_id)
    buf  = ctypes.create_string_buffer(body, len(body))
    attr = BpfProgLoadAttr()
    attr.prog_type            = prog_type
    attr.insn_cnt             = 2
    attr.insns                = ctypes.cast(buf, ctypes.c_void_p).value
    attr.license              = _LICENSE_ADDR
    attr.expected_attach_type = expected_attach_type
    attr.log_level            = 1
    attr.log_size             = _LOG_SIZE
    attr.log_buf              = _LOG_BUF_ADDR
    if prog_type == 31:  # SYSCALL: "Syscall programs can only be sleepable"
        attr.prog_flags = BPF_F_SLEEPABLE
    _LOG_BUF[0] = 0
    if prog_type == 27 and _STRUCT_OPS_BTF_ID:        # STRUCT_OPS
        attr.attach_btf_id = _STRUCT_OPS_BTF_ID
    elif prog_type == 28 and _EXT_ATTACH_PROG_FD:     # EXT
        # The EXT prog itself must carry BTF + func_info whose FUNC signature
        # matches the target's (kernel/bpf/btf.c:btf_check_type_match).
        attr.attach_btf_id      = _EXT_ATTACH_BTF_ID
        attr.attach_prog_fd     = _EXT_ATTACH_PROG_FD
        attr.prog_btf_fd        = _EXT_BTF_FD
        attr.func_info_rec_size = 8
        attr.func_info          = _EXT_FUNC_INFO_PTR
        attr.func_info_cnt      = 1
    elif attach_btf_id:
        attr.attach_btf_id = attach_btf_id
    fd = _libc.syscall(_NR_BPF, BPF_PROG_LOAD,
                       ctypes.byref(attr), ctypes.sizeof(attr))
    err = 0 if fd >= 0 else -ctypes.get_errno()
    if fd >= 0:
        os.close(fd)
    return err, _classify(fd >= 0, ctypes.string_at(_LOG_BUF_ADDR))

# ---- coverage --------------------------------------------------------------

# enum bpf_prog_type currently extends to BPF_PROG_TYPE_NETFILTER (32) on
# kernel 6.17. Iterating past the maximum is wasted syscalls.
PROG_TYPES = range(1, 33)

# __BPF_FUNC_MAX_ID grows over time; iterate well past it so we catch every
# valid id and let the dispatcher's own range check filter the rest.
FUNC_IDS = range(0, 240)

def main() -> int:
    global _STRUCT_OPS_BTF_ID, _EXT_ATTACH_BTF_ID, _EXT_ATTACH_PROG_FD
    global _EXT_BTF_FD, _EXT_FUNC_INFO_BUF, _EXT_FUNC_INFO_PTR
    global _TRACE_ITER_BTF_ID, _LSM_HOOK_BTF_ID

    if os.geteuid() != 0:
        sys.exit("driver: must run as root (CAP_BPF / CAP_SYS_ADMIN)")

    _set_comm(b"proto_drv")

    # Modern kernels use memcg, but bump MEMLOCK anyway for older kernels
    # the user might run this against.
    try:
        resource.setrlimit(resource.RLIMIT_MEMLOCK,
                           (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
    except (ValueError, OSError):
        pass

    # STRUCT_OPS (pt=27) needs attach_btf_id of a kernel struct. tcp_congestion_ops
    # is registered on every kernel with CONFIG_INET, so it's a safe default.
    _STRUCT_OPS_BTF_ID = _find_btf_type_id(
        "/sys/kernel/btf/vmlinux", "tcp_congestion_ops") or 0
    if _STRUCT_OPS_BTF_ID == 0:
        print("driver: warning: tcp_congestion_ops BTF id not found; "
              "STRUCT_OPS loads will continue to fail at attr validation",
              file=sys.stderr)
    else:
        print(f"driver: STRUCT_OPS attach_btf_id = {_STRUCT_OPS_BTF_ID} "
              f"(tcp_congestion_ops in vmlinux BTF)", file=sys.stderr)

    # TRACING/iter (pt=26, expected_attach_type=BPF_TRACE_ITER) must point
    # attach_btf_id at a registered bpf_iter_* target FUNC, else the load fails
    # in check_attach_btf_id before any helper lookup. Any registered iterator
    # works; bpf_map/task exist on every kernel with CONFIG_BPF_SYSCALL.
    _TRACE_ITER_BTF_ID = (
        _find_btf_type_id("/sys/kernel/btf/vmlinux", "bpf_iter_bpf_map",
                          _BTF_KIND_FUNC)
        or _find_btf_type_id("/sys/kernel/btf/vmlinux", "bpf_iter_task",
                             _BTF_KIND_FUNC)
        or 0
    )
    if _TRACE_ITER_BTF_ID == 0:
        print("driver: warning: no bpf_iter_* FUNC in vmlinux BTF; TRACING/iter "
              "helpers (seq_printf, seq_write, ...) will stay uncaptured",
              file=sys.stderr)
    else:
        print(f"driver: TRACING iter attach_btf_id = {_TRACE_ITER_BTF_ID} "
              f"(bpf_iter_* in vmlinux BTF)", file=sys.stderr)

    # LSM (pt=29) likewise needs attach_btf_id of a bpf_lsm_* hook to pass
    # check_attach_btf_id (bpf_lsm_verify_prog); any hook works.
    _LSM_HOOK_BTF_ID = _find_btf_type_id(
        "/sys/kernel/btf/vmlinux", "bpf_lsm_bprm_check_security",
        _BTF_KIND_FUNC) or 0
    if _LSM_HOOK_BTF_ID == 0:
        print("driver: warning: bpf_lsm_bprm_check_security FUNC not in vmlinux "
              "BTF; LSM verdicts will stay uncaptured", file=sys.stderr)
    else:
        print(f"driver: LSM attach_btf_id = {_LSM_HOOK_BTF_ID} "
              f"(bpf_lsm_bprm_check_security in vmlinux BTF)", file=sys.stderr)

    # EXT (pt=28) needs (a) a target program with BTF func_info and matching
    # signature, and (b) the EXT prog itself to carry BTF + func_info whose
    # FUNC signature matches the target's (kernel/bpf/btf.c:btf_check_type_match
    # rejects loads otherwise with "Program extension requires BTF"). We
    # reuse the same minimal BTF + func_info on both sides.
    try:
        _EXT_BTF_FD         = _btf_load(_build_minimal_btf())
        _EXT_ATTACH_PROG_FD = _load_ext_target(_EXT_BTF_FD)
        _EXT_ATTACH_BTF_ID  = 5   # the FUNC type id in our minimal BTF
        # func_info shared between target and EXT loads.
        fi = struct.pack("<II", 0, _EXT_ATTACH_BTF_ID)
        _EXT_FUNC_INFO_BUF = ctypes.create_string_buffer(fi, len(fi))
        _EXT_FUNC_INFO_PTR = ctypes.cast(_EXT_FUNC_INFO_BUF,
                                         ctypes.c_void_p).value
        print(f"driver: EXT target prog fd={_EXT_ATTACH_PROG_FD}, "
              f"btf fd={_EXT_BTF_FD}, attach_btf_id={_EXT_ATTACH_BTF_ID}",
              file=sys.stderr)
    except OSError as e:
        print(f"driver: warning: failed to set up EXT ({e}); "
              "EXT loads will continue to fail at attr validation",
              file=sys.stderr)

    # Per-prog-type stats. errno classes:
    #   0           load succeeded (verifier passed)
    #   -22 EINVAL  rejected (verifier ran -> "bad arg" / unknown helper / etc.)
    #               or pre-verifier rejection — indistinguishable without log
    #   -524 ENOTSUPP / -95 EOPNOTSUPP   prog_type not configured in kernel
    #   -1   EPERM  capability check failed
    # The verifier rejects most of our minimal "call <fid>; exit" bodies with
    # EINVAL *after* it has looked up the proto. That's exactly what we want
    # for capture — load failure is fine, lookup observation is what matters.
    stats: dict[int, dict[int, int]] = {}
    # pt name -> {func_id: allowed?} for every load that reached the helper
    # check. This is the ftrace-independent signal that fills helpers resolved
    # inside dispatchers the kretprobe can't attach to.
    verdicts: dict[str, dict[str, bool]] = {}
    n = 0
    for pt in PROG_TYPES:
        counts: dict[int, int] = {}
        at_list = EXPECTED_ATTACH_TYPES.get(pt, _DEFAULT_ATTACH_TYPES)
        pt_verdicts: dict[str, bool] = {}
        for fid in FUNC_IDS:
            allowed = reached = False
            for at in at_list:
                if (pt, at) in _NEEDS_ATTACH_BTF_ID and not _attach_btf_id_for(pt, at):
                    continue
                err, verdict = _try_load(pt, fid, at, _attach_btf_id_for(pt, at))
                counts[err] = counts.get(err, 0) + 1
                n += 1
                if verdict == "allow":
                    allowed = reached = True
                elif verdict == "deny":
                    reached = True
            if reached:
                pt_verdicts[str(fid)] = allowed
        stats[pt] = counts
        if pt_verdicts:
            verdicts[PROG_TYPE_NAMES.get(pt, f"UNK_{pt}")] = pt_verdicts

    with open("dispatch_verdicts.json", "w") as f:
        json.dump(verdicts, f, indent=2)
        f.write("\n")
    reached_n = sum(len(v) for v in verdicts.values())
    print(f"driver: wrote dispatch_verdicts.json "
          f"({reached_n} reached (prog_type, func_id) verdicts)", file=sys.stderr)

    print(f"driver: issued {n} load attempts", file=sys.stderr)
    print("driver: per-prog-type errno distribution (errno -> count):",
          file=sys.stderr)
    for pt, counts in stats.items():
        line = ", ".join(f"{e}:{c}" for e, c in sorted(counts.items()))
        print(f"  pt={pt:>3}  {line}", file=sys.stderr)

    # Give bpftrace a beat to drain its perf buffer.
    time.sleep(0.5)
    return 0

if __name__ == "__main__":
    sys.exit(main())
