#!/usr/bin/env bash
# Planted controls (2)-(4) of the v2 by-value gate on plugin-hostd/fuzz_command.
# Step 1: port_addr_check 3d2eee813cce (through the run wrapper pac.sh) on every plant copy and on the unplanted base
#         copy, each restricted to the planted file; donor tree c8557374ad2e:proofs/cgif/cgif_file_fuzzer/lib.
# Step 2: v2 (roundconst.py 32b39f3b34e9) and v1 (roundconst.py 8ad299147f2e) with --all-verdicts on each base and plant.
# Usage: run_plants.sh PAC_WRAPPER RUNS_DIR IMGDIR      (two heavy processes at a time)
set -u
PAC=${1:?pac.sh}; RUNS=${2:?runs dir}; I=${3:?imgdir}
cd "$(dirname "$0")"
H=$PWD
CG=c8557374ad2e:proofs/cgif/cgif_file_fuzzer/lib
SA="A=$I/cgif.A.pin:$I/cgif.A.twin"; TA="A=$I/cmd.A.pin:$I/cmd.A.twin"
SB="B=$I/cgif.B.pin:$I/cgif.B.twin"; TB="B=$I/cmd.B.pin:$I/cmd.B.twin"
# NAME  SIDE  FILE  DIR
JOBS=(
  "RCv2-A-base-AB13 A AB13.v plants/base-A/A"   "RCv2-A-c2a A AB13.v plants/A-c2a/A"
  "RCv2-A-base-AB1h A AB1h.v plants/base-A/A"   "RCv2-A-c2b A AB1h.v plants/A-c2b/A"
  "RCv2-A-base-AB01 A AB01.v plants/base-A/A"   "RCv2-A-c3w A AB01.v plants/A-c3w/A"
  "RCv2-A-c3t A AB01.v plants/A-c3t/A"          "RCv2-A-base-AD1k A AD1k.v plants/base-A/A"
  "RCv2-A-c3w2 A AD1k.v plants/A-c3w2/A"        "RCv2-A-base-AF0m A AF0m.v plants/base-A/A"
  "RCv2-A-c4 A AF0m.v plants/A-c4/A"            "RCv2-B-base-YB13 B YB13.v plants/base-B/B"
  "RCv2-B-c2a B YB13.v plants/B-c2a/B"          "RCv2-B-base-YB01 B YB01.v plants/base-B/B"
  "RCv2-B-c3w B YB01.v plants/B-c3w/B"          "RCv2-B-base-YF0m B YF0m.v plants/base-B/B"
  "RCv2-B-c4 B YF0m.v plants/B-c4/B"
)
pac() { # NAME SIDE FILE DIR
  local n=$1 s=$2 f=$3 d=$4
  if [ "$s" = A ]; then "$PAC" "$n" "$CG/A" "$H/$d" "$SA" "$TA" --include "$f" --dst-include "$f"
  else "$PAC" "$n" "$CG" "$H/$d" "$SB" "$TB" --include "$f" --dst-include "$f"; fi
  mkdir -p controls/pac; cp "$RUNS/$n/summary.out" "controls/pac/$n.summary.out"; cp "$RUNS/$n/rc" "controls/pac/$n.rc"
  gzip -c "$RUNS/$n/full.tsv" > "controls/pac/$n.full.tsv.gz"
}
i=0
for j in "${JOBS[@]}"; do
  set -- $j
  [ -s "controls/pac/$1.full.tsv.gz" ] && continue          # finished in an earlier invocation
  rm -rf "$RUNS/$1"
  pac $j &
  i=$((i + 1)); [ $((i % ${PAR:-2})) = 0 ] && wait
done
wait
gate() { # NAME SIDE
  local n=$1 s=$2 ds ts d1 t1
  if [ "$s" = A ]; then ds=$SA; ts=$TA; d1="A=$I/cgif.A.pin"; t1="A=$I/cmd.A.pin"
  else ds=$SB; ts=$TB; d1="B=$I/cgif.B.pin"; t1="B=$I/cmd.B.pin"; fi
  python3 tool/roundconst.py "controls/pac/$n.full.tsv.gz" "$ds" "$ts" "controls/v2/$n" --all-verdicts > "controls/v2/$n.summary" 2>&1
  python3 tool/v1/roundconst.py "controls/pac/$n.full.tsv.gz" "$d1" "$t1" "controls/v1/$n" --all-verdicts > "controls/v1/$n.summary" 2>&1
}
mkdir -p controls/v2 controls/v1
i=0
for j in "${JOBS[@]}"; do
  set -- $j
  gate "$1" "$2" &
  i=$((i + 1)); [ $((i % ${PAR:-2})) = 0 ] && wait
done
wait
echo DONE
