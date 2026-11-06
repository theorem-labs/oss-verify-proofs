#!/bin/bash
# run-all.sh WORK LIB OUT: every check of the TCA value lane (libdiginet/fuzz_transport image-A core relocation, asan pin
# e89be137db17) on one port_core run directory, each with its planted control. proves no function (kind: measurement).
#   1 by-value check          decval-A.sh     -> OUT/decval/decval.txt
#     1b section-bound cells  secbounds.py    -> OUT/secbounds.txt (the 22 tfib_<section>_lo / _hi cells vs the pin's headers)
#     1c stated memory values cellvals.py     -> OUT/cellvals.txt (val_mem / lit / CVal chunks / const lookups vs image bytes)
#   2 atable, core side       atable-A.sh     -> OUT/atable/atable.txt
#   3 .got words (GOT[0] in)  gotwords-A.sh   -> OUT/gotwords.txt, OUT/gotwords-control.txt
#   4 compensating checks     compcheck-A.sh  -> OUT/compcheck.txt, OUT/compcheck-control.txt
#   5 symbol + offset sweep   symoff-A.sh     -> OUT/symoff.txt, OUT/symoff-control.txt (reads OUT/decval)
#   6 roundconst-gate v2      roundconst-A.sh -> OUT/roundconst/roundconst.txt
# The result and control lines of all six go to OUT/RESULTS.txt. Read-only for WORK and LIB. Exit 1 when any step exits
# non-zero. DECIDED (the rows decided by hand, compcheck-decided.tsv) defaults to records/ beside this script, else
# ../records/ (the layout of the committed evidence slice); compcheck-A.sh refuses to run without it.
set -uo pipefail
[ $# -eq 3 ] || { echo "usage: run-all.sh WORK LIB OUT" >&2; exit 2; }
mkdir -p "$3" || exit 2
WORK=$(readlink -f "$1") LIB=$(readlink -f "$2") OUT=$(readlink -f "$3")
HERE=$(dirname "$(readlink -f "$0")")
if [ -z "${DECIDED:-}" ]; then
  DECIDED=$HERE/records/compcheck-decided.tsv; [ -f "$DECIDED" ] || DECIDED=$HERE/../records/compcheck-decided.tsv
fi
[ -f "$DECIDED" ] || { echo "run-all: no compcheck-decided.tsv (set DECIDED)" >&2; exit 2; }
export DECIDED=$(readlink -f "$DECIDED")
step() { local n=$1; shift; echo "== $n: $*" >> "$OUT/run-all.log"; "$@" >> "$OUT/run-all.log" 2>&1; echo "== $n rc=$?" >> "$OUT/run-all.log"; }
: > "$OUT/run-all.log"
step 1 bash "$HERE/decval-A.sh" "$WORK" "$LIB" "$OUT/decval"
step 1b env PYTHONDONTWRITEBYTECODE=1 python3 "$HERE/secbounds.py" "$WORK" "$LIB" "$OUT"
step 1c env PYTHONDONTWRITEBYTECODE=1 python3 "$HERE/cellvals.py" "$WORK" "$LIB" "$OUT"
step 2 bash "$HERE/atable-A.sh" "$WORK" "$LIB" "$OUT/atable"
step 3 bash "$HERE/gotwords-A.sh" "$WORK" "$LIB" "$OUT"
step 4 bash "$HERE/compcheck-A.sh" "$WORK" "$LIB" "$OUT"
step 5 bash "$HERE/symoff-A.sh" "$WORK" "$LIB" "$OUT"
step 6 bash "$HERE/roundconst-A.sh" "$WORK" "$LIB" "$OUT/roundconst"
{
  echo "# run-all.sh $WORK $LIB $OUT ($(date -u +%FT%TZ))"
  echo "# stage-out tree: $(cd "$WORK/stage-out" && find A Reusable -name '*.v' | LC_ALL=C sort | xargs sha256sum | sha256sum | cut -c1-12) ($(cd "$WORK/stage-out" && find A Reusable -name '*.v' | wc -l) files); stage tree: $(cd "$WORK/stage" && find A Reusable -name '*.v' | LC_ALL=C sort | xargs sha256sum | sha256sum | cut -c1-12)"
  echo "# scripts: $(cd "$HERE" && sha256sum decval.py decval_extra.py decval_hand.py decval-A.sh secbounds.py cellvals.py atable-A.sh gotwords.py gotwords-A.sh compcheck.py compcheck-A.sh symoff.py symoff-A.sh rclane.py roundconst-A.sh run-all.sh | awk '{printf "%s %s; ", $2, substr($1, 1, 12)}')compcheck-decided.tsv $(sha256sum < "$DECIDED" | cut -c1-12)"
  echo "## 1 by-value"; grep -E '^(result|plant|relocated files|classes)' "$OUT/decval/decval.txt"
  echo "## 1b section-bound cells"; grep -E '^(result|control|KNOWN|DIFF|NO-SECTION)' "$OUT/secbounds.txt"
  echo "## 1c stated memory values"; grep -E '^(result|control|FINDING)' "$OUT/cellvals.txt"
  echo "## 2 atable"; grep -E '^(donor|ab1w|rows|1ce9|plant-row|plant-tab)' "$OUT/atable/atable.txt"; tail -n 1 "$OUT/atable/atable.txt"
  echo "## 3 .got words"; grep -E '^(E\.|A\.|B\.|C\.|D\.|result|FINDING)' "$OUT/gotwords.txt"; grep '^control' "$OUT/gotwords-control.txt"
  echo "## 4 compensating checks"; grep -E '^(\(|result|FINDING|CANDIDATE)' "$OUT/compcheck.txt"; grep '^control' "$OUT/compcheck-control.txt"
  echo "## 5 symbol + offset"; grep -E '^(  [A-Z]|result|FINDING)' "$OUT/symoff.txt"; grep '^control' "$OUT/symoff-control.txt"
  echo "## 6 roundconst-gate v2"; grep -E '^(# r|# probe|# low|# plant|#   [A-Z]|control|rclane)' "$OUT/roundconst/roundconst.txt"
  echo "non-SAME rows (read by hand, records/roundconst-read.txt): $(grep -c '^NON-SAME' "$OUT/roundconst/roundconst.txt")"
  echo "## step return codes"; grep -E '^== [0-9]+[a-z]? rc=' "$OUT/run-all.log"
} > "$OUT/RESULTS.txt"
cat "$OUT/RESULTS.txt"
! grep -qE '^== [0-9]+[a-z]? rc=[1-9]' "$OUT/run-all.log" || { echo "run-all: a step failed (OUT/run-all.log)" >&2; exit 1; }
# every one of the eight sections must show its control as PASS, and no line of RESULTS.txt may end in FAIL
awk '/^## [0-9]/ { s = $2 } /: PASS$/ && s != "" { ok[s] = 1 } /: FAIL$|: FAIL / { bad = 1 }
     END { n = split("1 1b 1c 2 3 4 5 6", want, " "); for (i = 1; i <= n; i++) if (!(want[i] in ok)) { print "run-all: section " want[i] " shows no PASS control" > "/dev/stderr"; bad = 1 }
           exit bad }' "$OUT/RESULTS.txt" || exit 1
