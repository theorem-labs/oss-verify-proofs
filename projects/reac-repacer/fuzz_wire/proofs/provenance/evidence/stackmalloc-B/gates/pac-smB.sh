#!/bin/bash
# pac-smB.sh <src dir> <dst dir> <out prefix> [extra checker args]
# port_addr_check 45b78aaa48c3 (versions/45b78aaa48c3.SHA256SUMS sha256 d0f4d698fd8e) over the donor text vs the ported
# text: src = run.sh's stage/ (the donor files at their target paths, module paths changed), dst = the unit lib (or a
# planted copy); --paired-only reads only the five files of this record. Both images with their unstripped twins (no
# symbol recovery), the flags of core-B's gates/pac-B.sh plus --fail-on-flags.
set -uo pipefail
SRC=$1 DST=$2 OUT=$3; shift 3
: "${P:?set P to libreac's pinned image tree}" "${R:?set R to reac-repacer's pinned image tree}"
CK=${CK:?set CK to port_addr_check.py of version 45b78aaa48c3}
DONORS=${DONORS:?set DONORS to the symbolised donor image tree port_addr_check --donors-from reads}
[ "$(sha256sum "$CK" | cut -c1-12)" = 45b78aaa48c3 ] || { echo "pac-smB: $CK is not 45b78aaa48c3" >&2; exit 2; }
mkdir -p "$OUT.cache"
python3 "$CK" --src "$SRC" --dst "$DST" \
  --src-image "B=$P/bin/fuzz_grant/fuzz_grant.asan-ubsan:$P/unstripped/fuzz_grant/fuzz_grant.asan-ubsan" \
  --dst-image "B=$R/result/bin/fuzz_wire/fuzz_wire.asan-ubsan:$R/result/unstripped/fuzz_wire/fuzz_wire.asan-ubsan" \
  --donors-from "$DONORS" --paired-only --fail-on-flags --out "$OUT.tsv" --summary --cache "$OUT.cache" "$@" > "$OUT.log" 2>&1
rc=$?
echo "checker port_addr_check 45b78aaa48c3 rc=$rc" >> "$OUT.log"
python3 "$CK" --list-flag-classes >> "$OUT.log" 2>&1
exit $rc
