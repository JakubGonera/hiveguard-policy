#!/usr/bin/env bash
# Capture (prog_type, func_id) -> proto dispatch from the running kernel.
# Requires root: bpftrace needs to attach kprobes, and the driver needs
# CAP_BPF/CAP_SYS_ADMIN to issue BPF_PROG_LOAD.

set -u
cd "$(dirname "$0")"

if [ "$EUID" -ne 0 ]; then
    echo "run.sh: re-exec under sudo" >&2
    # $0 was relative to the caller's cwd; we've since cd'd into the script's
    # own directory, so re-exec via an absolute path ($PWD is now that dir).
    exec sudo -E "$PWD/$(basename "$0")" "$@"
fi

EVENTS="${EVENTS:-events.log}"
OUT="${OUT:-dispatch_map.json}"

echo "[0/4] snapshotting kallsyms and regenerating probe.bt"
# Snapshot while we hold root; resolve.py uses exact-address match for proto
# symbols (bpftrace's ksym rounds to nearest, which is wrong for data syms).
cp /proc/kallsyms kallsyms.snapshot
# Regenerate probe.bt from the candidate list, filtered against the kernel's
# own list of ftrace-traceable functions, so untraceable dispatchers don't
# trip bpftrace 0.20's "Code not generated" abort.
python3 gen_probe.py --out probe.bt

echo "[1/4] starting probe -> $EVENTS"
bpftrace probe.bt > "$EVENTS" &
BT_PID=$!
cleanup() {
    kill -INT "$BT_PID" 2>/dev/null || true
    wait "$BT_PID" 2>/dev/null || true
}
trap cleanup EXIT

# Wait for the probe to actually attach. bpftrace prints "# probe attached"
# from its BEGIN block once kprobes are armed.
for _ in $(seq 1 50); do
    if grep -q "probe attached" "$EVENTS" 2>/dev/null; then break; fi
    sleep 0.1
done

echo "[2/4] driving loads"
python3 driver.py

# Let perf-buffer flush before tearing the probe down.
sleep 1

echo "[3/4] stopping probe"
kill -INT "$BT_PID" 2>/dev/null || true
wait "$BT_PID" 2>/dev/null || true
trap - EXIT

echo "[4/4] resolving -> dispatch_map.json + dispatch_chain.json"
python3 resolve.py "$EVENTS"

events=$(grep -c '^EV ' "$EVENTS" || true)
echo "done: $events raw events"
