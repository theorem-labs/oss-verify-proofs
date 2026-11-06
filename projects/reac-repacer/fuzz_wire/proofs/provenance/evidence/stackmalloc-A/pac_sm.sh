#!/bin/bash
# pac_sm.sh OUT SRC DST -- port_addr_check 45b78aaa48c3 (the read-only copy, verified against its SHA256SUMS first) on
# the stack_malloc files: SRC = port_core's stage/ (fuzz_grant's text at the target paths), DST = a tree holding the
# committed A/Rt/StackMalloc0.v, StackMalloc0Tbl.v, AF0r.v, AF0s.v and Reusable/YF0v.v, each image with its unstripped
# twin (no symbol recovery), --paired-only, a private cache. Writes OUT/pac.tsv, OUT/pac.log.
set -uo pipefail
OUT=${1:?usage: pac_sm.sh OUT SRC DST}; SRC=${2:?}; DST=${3:?}
# env: PAC (the extracted port_addr_check 45b78aaa48c3 directory, beside its 45b78aaa48c3.SHA256SUMS), PG (libreac's
# result directory: bin/ and unstripped/fuzz_grant), R (reac-repacer's result directory: bin/ and unstripped/fuzz_wire)
V=${PAC:?set PAC to the port_addr_check 45b78aaa48c3 directory}; PG=${PG:?set PG}; R=${R:?set R}
[ "$(basename "$V")" = 45b78aaa48c3 ] || { echo "pac_sm: PAC is not a 45b78aaa48c3 directory"; exit 2; }
(cd "$V" && sha256sum -c --quiet ../45b78aaa48c3.SHA256SUMS) || { echo "pac_sm: 45b78aaa48c3 fails its SHA256SUMS"; exit 2; }
mkdir -p "$OUT"; rm -rf "$OUT/cache"
systemd-run --user --wait --pipe -q -p MemoryMax=4G -p WorkingDirectory="$PWD" python3 "$V/port_addr_check.py" --src "$SRC" --dst "$DST" \
  --src-image "A=$PG/bin/fuzz_grant/fuzz_grant.asan:$PG/unstripped/fuzz_grant/fuzz_grant.asan" \
  --dst-image "A=$R/bin/fuzz_wire/fuzz_wire.asan:$R/unstripped/fuzz_wire/fuzz_wire.asan" \
  --paired-only --out "$OUT/pac.tsv" --summary --cache "$OUT/cache" > "$OUT/pac.log" 2>&1
echo "pac_sm: rc=$? ($(($(wc -l < "$OUT/pac.tsv") - 1)) rows)"
