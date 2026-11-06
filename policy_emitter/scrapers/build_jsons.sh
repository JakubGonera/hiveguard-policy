#!/usr/bin/env bash
# Regenerate the input JSONs consumed by the policy emitter.
#
# Everything here describes the *vendored* kernel, not the one this host boots,
# so `just linux-build` must have run first. Five of the six inputs read the
# built image directly and need no root:
#
#   docs_helper_callers.json       --- web scrape, kernel-independent
#   helper_map_compat.json         --- kernel source scrape
#   pkt_changing.json              --- kernel source scrape
#   kernel_proto_descriptors.json  --- drgn over the built vmlinux's .rodata
#   kfunc_descriptors.json         --- kernel source + the image's .BTF
#   struct_ops_descriptors.json    --- kernel source + the image's .BTF
#
# The fifth, probed_proto_callers.json, observes which proto each program type's
# get_func_proto() dispatch returns. No static image records that, so it has to
# run against a booted vendored kernel: `just scrape-dispatch` does it in the VM.
#
# Usage: ./build_jsons.sh [LINUX_SRC] [VMLINUX]
#   LINUX_SRC: the vendored kernel source tree (default: the in-repo checkout).
#   VMLINUX:   the built image (default: the newest .vm/linux-build/<arch>).

set -eu
cd "$(dirname "$0")"

SRC_INPUT="${1:-../../linux}"
if [ ! -d "$SRC_INPUT" ]; then
    echo "error: kernel source not found: $SRC_INPUT" >&2
    echo "       pass the vendored kernel source tree as the first argument" >&2
    exit 1
fi
LINUX_SRC=$(cd "$SRC_INPUT" && pwd)

VMLINUX_ARG=()
if [ "$#" -ge 2 ]; then
    VMLINUX_ARG=(--vmlinux "$2")
fi

UV=$(command -v uv)

echo "[1/4] docs scrape -> docs_helper_callers.json"
"$UV" run prog_helpers_scraper.py

echo "[2/4] source scrapes -> helper_map_compat.json, pkt_changing.json"
"$UV" run map_compat_scraper.py "$LINUX_SRC"
"$UV" run pkt_changing_scraper.py "$LINUX_SRC"

echo "[3/4] helper protos -> kernel_proto_descriptors.json"
"$UV" run helper_proto_scraper.py "$LINUX_SRC" "${VMLINUX_ARG[@]}"

echo "[4/4] kfunc + struct_ops descriptors"
"$UV" run kfunc_descriptor_scraper.py "$LINUX_SRC" "${VMLINUX_ARG[@]}"
"$UV" run struct_ops_scraper.py "$LINUX_SRC" "${VMLINUX_ARG[@]}"

echo
echo "note: probed_proto_callers.json is not regenerated here; it needs a booted"
echo "      vendored kernel. Run 'just scrape-dispatch' for it."
echo
echo "ready in $(pwd):"
ls -lh docs_helper_callers.json helper_map_compat.json pkt_changing.json kernel_proto_descriptors.json \
       kfunc_descriptors.json struct_ops_descriptors.json
