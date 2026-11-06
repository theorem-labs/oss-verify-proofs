#!/bin/sh
# libdiginet/fuzz_transport image-A core relocation on the NEW asan pin e89be137db17 (row TCA): fuzz_frame's run.sh
# (run.sh, sha256 437d65e84649; internal record) with only the pins, the names and the per-image values
# changed. Same donor (fuzz_grant's released lib, recipes 25e3d17bdb50, normalised), same file list (core-files.txt of
# the release minus YI0j, YO08), same --no-stage start-up layer (generated for the unit's own image by row T3r).
#   run-transport.sh <workdir> ; NOPATCH=1 runs without the four --patch files (to re-cut them against this stage-out)
set -eu
WORK=${1:?usage: run-transport.sh <workdir>}
HERE=$(cd "$(dirname "$0")" && pwd)
: "${REL:?set REL to the extracted port_core release}"
: "${DON:?set DON to the normalised grant lib}"
: "${PG:?set PG to the directory of fuzz_grant's ORIGINAL images}"
: "${P:?set P to the directory of fuzz_transport's images (result/bin/ and unstripped/)}"
: "${EV:?set EV to this run's evidence directory (overrides, patches, lists, hdrform.py, reusable-local.py)}"
: "${SYMS:?set SYMS to fuzz_grant.asan.syms.txt (pin b46268790c46)}"
: "${LIB:?set LIB to proofs/libdiginet/fuzz_transport/lib}"
: "${GRANTB:?set GRANTB to a directory holding B/YA09.v and B/YA0e.v of fuzz_grant's released lib, recipes 4f87de75d67}"
pin() { [ "$(sha256sum "$1" | cut -c1-12)" = "$2" ] || { echo "run: pin mismatch: $1 is not $2" >&2; exit 5; }; }
pin "$PG/bin/fuzz_grant/fuzz_grant.asan" c2c7559b29bd
pin "$P/result/bin/fuzz_transport/fuzz_transport.asan" e89be137db17
pin "$P/unstripped/fuzz_transport/fuzz_transport.asan" 86efc3a80314
pin "$P/result/bin/fuzz_transport/fuzz_transport.asan-ubsan" 41113a03c82f
pin "$SYMS" b46268790c46
NS=""
while read -r f; do [ -n "$f" ] && NS="$NS --no-stage $f"; done < "$EV/not-relocated-startup-layer.txt"
PATCHES=""
if [ -z "${NOPATCH:-}" ]; then
  for p in zero-shadow-forallb cell-lookup ad1q-shape imgtop-alias dead-arm-ad1g bss-zero-range g-ACfn g-AD1w g-AD1m g-AD1p g-AD1q g-AD1r g-AD2f afet-cost; do PATCHES="$PATCHES --patch $EV/$p.patch"; done
fi
set +e
# shellcheck disable=SC2086
python3 "$REL/port_core.py" \
  --src-lib    "$DON" \
  --src-rev    25e3d17bdb50 \
  --src-mod    OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib \
  --src-images OssFuzzTheorems.libreac.fuzz_grant.images \
  --old-elf    "$PG/bin/fuzz_grant/fuzz_grant.asan" \
  --old-syms   "$SYMS" \
  --old-prog   806b0:857dc \
  --target-lib    "$LIB" \
  --target-mod    OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib \
  --target-images OssFuzzTheorems.libdiginet.fuzz_transport.images \
  --target-name   libdiginet/fuzz_transport \
  --target-elf    "$P/result/bin/fuzz_transport/fuzz_transport.asan" \
  --target-syms   "$P/unstripped/fuzz_transport/fuzz_transport.asan" \
  --files      "$EV/core-files-transport.txt" \
  $NS \
  --rename GrantB=TransportB --rename GrantSyms=TransportSyms \
  --rename GrantB_syms=TransportB_syms --rename GrantB_ok=TransportB_ok \
  --override "$EV/overrides.tsv" \
  $PATCHES \
  --known-elf "$P/result/bin/fuzz_transport/fuzz_transport.asan-ubsan" \
  --reusable-dir Reusable --kernel-dir Reusable \
  --work "$WORK"
status=$?
set -e
[ -n "${NOPATCH:-}" ] && { echo "run: NOPATCH run, port_core status $status"; exit "$status"; }
python3 "$EV/hdrcheck.py" "$WORK/stage-out" "$DON" > "$WORK/hdrcheck.log" || { echo "run: hdrcheck refused (log WORK/hdrcheck.log)"; exit 4; }
echo "run: $(tail -n 1 "$WORK/hdrcheck.log")"
python3 "$EV/reusable-local.py" "$WORK/stage-out" "$GRANTB" || exit 6
exit "$status"
