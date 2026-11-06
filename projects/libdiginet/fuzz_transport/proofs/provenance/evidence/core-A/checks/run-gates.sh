#!/bin/bash
# run-gates.sh WORK LIB OUT: every gate and check of the libdiginet/fuzz_transport image-A core relocation (row TCA) over
# ONE port_core run directory, each as its own single command over WORK LIB OUT/<gate>. Kind: measurement; it proves no
# function. Read-only for WORK and LIB.
#   pac      gates/flag-gate-A.sh   gate (a): port_addr_check 0d24592683b6, triage of every flagged row, 3 controls
#   codeptr  gates/codeptr-A.sh     gate (b): codeptr 12348302dfd2 through start-up set 2026-10-30d, its plants
#   values   checks/run-all.sh      gate (c) and the value lane: by-value check, section cells, stated memory values,
#                                   atable core side, .got words, the four compensating checks, symbol + offset sweep,
#                                   roundconst-gate v2, each with its plant
#   v10      checks/v10-gate.py     gate (d): global_settings v10 439f8e3bd463 and its plant
#   yh03     checks/yh03-gate.py    gate (e): yh03check fb3bfbc1eea8 (v6.4) on LIB's two YH03 files, its plants, and the
#                                   cells v6.4 does not judge, read by content
#   alreloc  checks/alreloc-gate.sh the alreloc a5c53bb2bed4 cross-check, its control and two sweeps
#   hyp      checks/hypvalues.sh    every value in a hypothesis position, derived; its plants
#   ghunks   checks/ghunks-A.sh     the 7 G patches: undone and re-applied on stage-out, the hull and the region counts
#                                   measured (measure_gcut.py), and its two controls
# The gates run in parallel (GATES_SERIAL=1 runs them one after the other; ONLY="pac values" runs those alone). EV (the
# run's own inputs: overrides.tsv, the patches, not-relocated-startup-layer.txt) defaults to the directory above this one,
# the evidence slice. The tools the gates take by directory are extracted once from the hub HUB at TOOLS_REF (the tool
# registry; its README.md sha256 05596ed48d98, internal record) into OUT/tools and passed as SET (start-up set 2026-10-30d), AT1CE9
# (atable 1ce98fbad397), RC (roundconst-gate 32b39f3b34e9), GS (global_settings 439f8e3bd463), YH03CHECK (yh03check
# fb3bfbc1eea8); each gate checks their sha256. Every other input (images, the donor lib, PINS
# for yh03) is each gate's own environment, passed through. OUT/run-gates.txt gets, per gate, the command, its exit status
# and wall time; OUT/<gate>.log the gate's output. Exit 0 when every gate exits 0 (alreloc-gate.sh does not fail on its
# record run's WRONG rows, which its record decides by hand; flag-gate-A.sh exits 0 only when the triage explains every row).
set -uo pipefail
[ $# -eq 3 ] || { echo "usage: run-gates.sh WORK LIB OUT" >&2; exit 2; }
WORK=$(readlink -f "$1") LIB=$(readlink -f "$2")
mkdir -p "$3" || exit 2
OUT=$(readlink -f "$3")
HERE=$(cd "$(dirname "$0")" && pwd)
GATES=$(cd "$HERE/../gates" && pwd)
export EV=${EV:-$(cd "$HERE/.." && pwd)}
export PYTHONDONTWRITEBYTECODE=1
export HUB=${HUB:?set HUB to the hub repository} TOOLS_REF=${TOOLS_REF:-91ef630666824d85906ae28a461aec2ae1e9653d}
T=$OUT/tools
for d in startup-set/2026-10-30d atable/1ce98fbad397 roundconst-gate/32b39f3b34e9 global_settings/439f8e3bd463 \
         yh03check/fb3bfbc1eea8; do
  [ -d "$T/$d" ] || { mkdir -p "$T" && git -C "$HUB" archive "$TOOLS_REF" "tools/$d" | tar -x -C "$T" --strip-components=1; } \
    || { echo "run-gates: cannot extract tools/$d from $HUB at $TOOLS_REF" >&2; exit 2; }
done
export SET=${SET:-$T/startup-set/2026-10-30d} AT1CE9=${AT1CE9:-$T/atable/1ce98fbad397/atable.py}
export RC=${RC:-$T/roundconst-gate/32b39f3b34e9} GS=${GS:-$T/global_settings/439f8e3bd463}
export YH03CHECK=${YH03CHECK:-$T/yh03check/fb3bfbc1eea8}
{ echo "# run-gates.sh $WORK $LIB $OUT ($(date -u +%FT%TZ)); ONLY=${ONLY:-all}"
  echo "# env: EV=$EV HUB=$HUB TOOLS_REF=$TOOLS_REF SET=$SET AT1CE9=$AT1CE9 RC=$RC GS=$GS YH03CHECK=$YH03CHECK PINS=${PINS:-}"
  echo "# scripts: $(cd "$HERE/.." && sha256sum gates/* checks/* | awk '{printf "%s %s; ", $2, substr($1, 1, 12)}')"
} >> "$OUT/run-gates.txt"
gate() { local n=$1; shift; local t0; t0=$(date +%s); "$@" "$WORK" "$LIB" "$OUT/$n" > "$OUT/$n.log" 2>&1; local rc=$?
  echo "$n rc=$rc $(( $(date +%s) - t0 ))s: $* WORK LIB OUT/$n" >> "$OUT/run-gates.txt"; }
run() { case " ${ONLY:-$1} " in *" $1 "*) ;; *) return 0;; esac
  if [ -n "${GATES_SERIAL:-}" ]; then gate "$@"; else gate "$@" & fi; }
run pac bash "$GATES/flag-gate-A.sh"
run codeptr bash "$GATES/codeptr-A.sh"
run values bash "$HERE/run-all.sh"
run v10 python3 "$HERE/v10-gate.py"
run yh03 python3 "$HERE/yh03-gate.py"
run alreloc bash "$HERE/alreloc-gate.sh"
run hyp bash "$HERE/hypvalues.sh"
run ghunks bash "$HERE/ghunks-A.sh"
wait
cat "$OUT/run-gates.txt"
! grep -qE '^[a-z0-9]+ rc=[1-9]' "$OUT/run-gates.txt"
