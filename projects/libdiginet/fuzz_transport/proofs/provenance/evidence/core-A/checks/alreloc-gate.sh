#!/bin/bash
# alreloc-gate.sh WORK LIB OUT: the alreloc a5c53bb2bed4 cross-check of the libdiginet/fuzz_transport image-A core as ONE
# command over a port_core run directory. Kind: measurement; it proves no function. The steps (each as recorded in
# ALRELOC-CROSSCHECK.md, beside the scripts it calls):
#   1. alreloc-xcheck.sh WORK LIB OUT             the record run: every numeral position paired and decided against the
#                                                 images (exit 1 = port_core WRONG rows listed, 3 = UNDECIDED only)
#   2. alreloc-xcheck-control.sh WORK LIB OUT     the planted control (8 plants; exit 0 = each caught, no other row changed)
#   3. SWEEP="80 1", then SWEEP="120 2"           the seeded sweeps (value + 8 at N positions the record run decided right)
#   4. alreloc_record.py WORK LIB OUT             the generated tables -> OUT/record-tables.md
# Each step's output goes to OUT/<step>.log with its exit status and wall time. Exit 0 when the control (2) exits 0 and both
# sweeps catch every plant; the record run's own status is written to OUT/alreloc-gate.txt and read by hand (its WRONG rows
# are decided in the record), not failed on. Environment: as alreloc-xcheck.sh (the same defaults).
set -uo pipefail
[ $# -eq 3 ] || { echo "usage: alreloc-gate.sh WORK LIB OUT" >&2; exit 2; }
WORK=$1 LIB=$2 OUT=$3
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT" && OUT=$(cd "$OUT" && pwd)
export PYTHONDONTWRITEBYTECODE=1
step() { local n=$1; shift; local t0; t0=$(date +%s); "$@" > "$OUT/$n.log" 2>&1; local rc=$?
  echo "$n rc=$rc $(( $(date +%s) - t0 ))s" | tee -a "$OUT/$n.log" >> "$OUT/alreloc-gate.txt"; return $rc; }
: > "$OUT/alreloc-gate.txt"
step xcheck bash "$HERE/alreloc-xcheck.sh" "$WORK" "$LIB" "$OUT"
XRC=$?
[ "$XRC" = 0 ] || [ "$XRC" = 1 ] || [ "$XRC" = 3 ] || { echo "alreloc-gate: the record run failed (rc $XRC, OUT/xcheck.log)" >&2; exit 2; }
step control bash "$HERE/alreloc-xcheck-control.sh" "$WORK" "$LIB" "$OUT"
CRC=$?
step sweep env SWEEP="80 1" bash "$HERE/alreloc-xcheck-control.sh" "$WORK" "$LIB" "$OUT"
step sweep2 env SWEEP="120 2" bash "$HERE/alreloc-xcheck-control.sh" "$WORK" "$LIB" "$OUT"
step record sh -c 'python3 "$1/alreloc_record.py" "$2" "$3" "$4" > "$4/record-tables.md"' - "$HERE" "$WORK" "$LIB" "$OUT"
SW=0
for s in sweep sweep2; do
  awk '/^controls: / { if ($2 != $4) bad = 1; seen = 1 } END { exit (seen && !bad) ? 0 : 1 }' "$OUT/$s.log" || SW=1
done
{ echo "record run rc=$XRC (1 = WRONG rows listed, read by hand in the record)"; grep -h '^controls: ' "$OUT/control.log" "$OUT/sweep.log" "$OUT/sweep2.log"; } >> "$OUT/alreloc-gate.txt"
cat "$OUT/alreloc-gate.txt"
[ "$CRC" = 0 ] && [ "$SW" = 0 ]
