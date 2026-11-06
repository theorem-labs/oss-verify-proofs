#!/bin/bash
# pac-B.sh <checker sha12> <src dir (stage)> <dst dir (stage-out or a planted copy)> <out prefix> [extra checker args]
# Runs the frozen port_addr_check over the donor text vs the relocated text, both images with their unstripped twins
# (no symbol recovery needed), the same flags port_core's gate uses (--paired-only --summary --donors-from DONORS).
# The checker is CKDIR/port_addr_check.py.frozen-<sha12>, else CKDIR/versions/<sha12>/port_addr_check.py.
set -uo pipefail
SHA=$1 SRC=$2 DST=$3 OUT=$4; shift 4
: "${P:?set P to libreac's pinned image tree}" "${R:?set R to reac-repacer's pinned image tree}"
AO=${CKDIR:?set CKDIR to the port_addr_check directory (port_addr_check.py.frozen-<sha12> or versions/<sha12>/)}
DONORS=${DONORS:?set DONORS to the symbolised donor image tree port_addr_check --donors-from reads}
CK=$AO/port_addr_check.py.frozen-$SHA
[ -f "$CK" ] || CK=$AO/versions/$SHA/port_addr_check.py
mkdir -p "$OUT.cache"
python3 "$CK" --src "$SRC" --dst "$DST" \
  --src-image "A=$P/bin/fuzz_grant/fuzz_grant.asan-ubsan:$P/unstripped/fuzz_grant/fuzz_grant.asan-ubsan" \
  --dst-image "A=$R/result/bin/fuzz_uci/fuzz_uci.asan-ubsan:$R/result/unstripped/fuzz_uci/fuzz_uci.asan-ubsan" \
  --donors-from "$DONORS" --paired-only --out "$OUT.tsv" --summary --cache "$OUT.cache" "$@" > "$OUT.log" 2>&1
rc=$?
echo "checker $CK rc=$rc (sha256 $(sha256sum "$CK" | cut -c1-12))" >> "$OUT.log"
python3 "$CK" --list-flag-classes >> "$OUT.log" 2>&1
exit $rc
