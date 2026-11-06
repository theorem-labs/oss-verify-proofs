#!/bin/bash
# libdiginet/fuzz_transport IMAGE-B (fuzz_transport.asan-ubsan) core relocation: libdiginet/fuzz_decode's image-B core
# route (its provenance/evidence/core-B/METHOD.md, run.sh) with this unit's pins; donor libreac/fuzz_decode's released
# lib/B (recipes 88154566652a, normalised by mkdon.sh).
#
#   run.sh <workdir> [extra port_core args]     then apply-B.sh
#
#   REL  port_core d9e0589898fd (the port_core release registry's tools/pg-reloc/d9e0589898fd/; best available, NOT of record: its four
#        compensating checks apply to every output)
#   DON  mkdon.sh 88154566652a fuzz_decode B $DONROOT ; DON=$DONROOT/proofs/libreac/fuzz_decode/lib
#   P    libreac's pinned image tree (bin/fuzz_decode, unstripped/fuzz_decode)
#   T    libdiginet's fuzz_transport image tree (result/bin/fuzz_transport, result/unstripped/fuzz_transport)
#   LIB  proofs/libdiginet/fuzz_transport/lib of the branch before the run
#   TPIN_B / TTWIN_B / TPIN_A  the target's asan-ubsan pin, its twin, the asan pin (sha256 prefixes; default: the
#        re-pinned build 41113a03c82f / e217cb0a84f1 / e89be137db17)
set -uo pipefail
WORK=${1:?usage: run.sh <workdir> [extra port_core args]}; shift
HERE=$(cd "$(dirname "$0")" && pwd)
: "${REL:?set REL}" "${DON:?set DON}" "${LIB:?set LIB}" "${P:?set P}" "${T:?set T}"
TPIN_B=${TPIN_B:-41113a03c82f}; TTWIN_B=${TTWIN_B:-e217cb0a84f1}; TPIN_A=${TPIN_A:-e89be137db17}
pin() { [ "$(sha256sum "$1" | cut -c1-12)" = "$2" ] || { echo "run.sh: pin mismatch: $1 is not $2" >&2; exit 5; }; }
pin "$P/bin/fuzz_decode/fuzz_decode.asan-ubsan" 5d05689fd5b1
pin "$P/unstripped/fuzz_decode/fuzz_decode.asan-ubsan" 6744989bb2e6
pin "$P/bin/fuzz_decode/fuzz_decode.asan" 5973b76807d8
pin "$T/result/bin/fuzz_transport/fuzz_transport.asan-ubsan" "$TPIN_B"
pin "$T/result/unstripped/fuzz_transport/fuzz_transport.asan-ubsan" "$TTWIN_B"
pin "$T/result/bin/fuzz_transport/fuzz_transport.asan" "$TPIN_A"
PC_SHA=${PC_SHA:-d9e0589898fd}   # port_core tag: d9e0589898fd, or 83f5203d2a2f (the libreac owner 21:47Z, at a unit boundary)
pin "$REL/port_core.py" "$PC_SHA"
NS=()
while read -r f; do [ -n "$f" ] && NS+=(--no-stage "$f"); done < "$HERE/no-stage-B.txt"
OV=(); [ -f "$HERE/overrides-B.tsv" ] && OV=(--override "$HERE/overrides-B.tsv")
PA=()
for p in "$HERE"/B-*.patch; do [ -e "$p" ] && PA+=(--patch "$p"); done
[ "${PATCHES:-1}" = 0 ] && PA=()
[ "${OVERRIDES:-1}" = 0 ] && OV=()
PL=(); [ -f "$HERE/placement-B.tsv" ] && PL=(--placement "$HERE/placement-B.tsv")
python3 "$REL/port_core.py" \
  --src-lib "$DON" \
  --src-mod OssFuzzTheorems.Proofs.libreac.fuzz_decode.lib \
  --src-images OssFuzzTheorems.libreac.fuzz_decode.images \
  --old-elf "$P/bin/fuzz_decode/fuzz_decode.asan-ubsan" \
  --old-syms "$HERE/libreac-fuzz_decode.asan-ubsan.syms.txt" \
  --old-prog 800b0:823c8 \
  --target-lib "$LIB" \
  --target-mod OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib \
  --target-images OssFuzzTheorems.libdiginet.fuzz_transport.images \
  --target-name libdiginet/fuzz_transport \
  --target-elf "$T/result/bin/fuzz_transport/fuzz_transport.asan-ubsan" \
  --target-syms "$T/result/unstripped/fuzz_transport/fuzz_transport.asan-ubsan" \
  --files "$HERE/files-B-core.txt" \
  "${NS[@]}" \
  --remap-images --reusable-dir B --kernel-dir Reusable "${PL[@]}" \
  --rename TfibB=TransportB --rename TfibSyms=TransportSyms --rename TfibB_syms=TransportB_syms --rename TfibB_ok=TransportB_ok \
  --kernel-image "$P/bin/fuzz_decode/fuzz_decode.asan" \
  --known-elf "$T/result/bin/fuzz_transport/fuzz_transport.asan" \
  --known-elf "$P/bin/fuzz_decode/fuzz_decode.asan" \
  "${OV[@]}" \
  "${PA[@]}" \
  --work "$WORK" "$@"
