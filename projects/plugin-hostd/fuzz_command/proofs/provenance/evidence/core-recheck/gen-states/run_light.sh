#!/bin/sh
# run_light.sh ROOT GEN_TRACES OUT -- the function-row tables and the trace universes, both images (a few seconds each).
#   ROOT as in run_states.sh; GEN_TRACES = the unit lane's gen_traces.py (sha256 59966c883510, needs resolve_code.py
#   beside it and rvelf.py, sha256 23152d9ca11c); OUT receives the tables.
# The shadow offset passed to rule_ab1w.py (--so) is the value rule_states.py measured in A/AB01.v and B/YB01.v at
# __asan_shadow_memory_dynamic_address (0x7fff8000 in both; see the *.summary.txt "SO" field).
R=$1; GT=$2; O=$3; H=$(cd "$(dirname "$0")" && pwd)
T=$R/tree/cmd/proofs/plugin-hostd/fuzz_command/lib
C=$R/tree/cgif/proofs/cgif/cgif_file_fuzzer/lib
mkdir -p "$O"
# gen_traces on our pinned images; --ipc = the return address of the second GetCurrentPc call of each interceptor
# (rule_acej.py re-measures and checks it)
python3 "$GT" "$R/img/cmd.A.pin" "$R/img/cmd.A.twin" --ipc malloc=0x58c20 --ipc free=0x58ac0 > "$O/gen.A.all.v"
python3 "$GT" "$R/img/cmd.B.pin" "$R/img/cmd.B.twin" --ipc malloc=0x58c6c --ipc free=0x58b0c > "$O/gen.B.all.v"
for X in "A A/ACej.v lib/A/ACej.v RA ACej A/ACej.v" "B B/YCej.v lib/B/YCej.v RB YCej YCej.v"; do
  set -- $X
  python3 "$H/rule_acej.py" --file "$T/$2" --rel "$3" --gen "$O/gen.$1.all.v" --pin "$R/img/cmd.$1.pin" \
    --twin "$R/img/cmd.$1.twin" --kit "$H/kit" --donor-file "$C/$6" --donor-pin "$R/img/cgif.$1.pin" \
    --donor-twin "$R/img/cgif.$1.twin" --rows "$R/triage/$4.gen.tsv" --out-rows "$O/$5.rows.tsv" \
    --out-check "$O/$5.check.tsv" --out-ctl "$O/$5.ctl.tsv" > "$O/$5.summary.txt"
done
for X in "A A/AB1w.v lib/A/AB1w.v A/AB1w.v RA AB1w" "B B/YB1w.v lib/B/YB1w.v YB1w.v RB YB1w"; do
  set -- $X
  python3 "$H/rule_ab1w.py" --file "$T/$2" --rel "$3" --pin "$R/img/cmd.$1.pin" --twin "$R/img/cmd.$1.twin" \
    --kit "$H/kit" --donor-file "$C/$4" --donor-pin "$R/img/cgif.$1.pin" --donor-twin "$R/img/cgif.$1.twin" \
    --rows "$R/triage/$5.gen.tsv" --out-rows "$O/$6.rows.tsv" --out-defs "$O/$6.defs.tsv" --out-ctl "$O/$6.ctl.tsv" \
    --so 0x7fff8000 > "$O/$6.summary.txt"
done
