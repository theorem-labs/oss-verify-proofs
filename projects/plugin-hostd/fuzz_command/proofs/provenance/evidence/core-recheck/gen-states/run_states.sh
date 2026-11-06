#!/bin/sh
# run_states.sh ROOT OUT -- rule_states.py over the four start-up state files of the unit, both images.
#   ROOT holds tree/cmd (ours, series head a3c671fb9bb), tree/cgif (donor c8557374ad2e), img/ (the pinned images and
#   twins by role), triage/R{A,B}.gen.tsv (the gate's generated-file rows); OUT receives the tables and NAME.rc.
# Each file is judged against its own image (ours A: fuzz_command.asan c0661b96b5bd + twin 68db792d5fa7; ours B:
# fuzz_command.asan-ubsan bbe55d24d096 + twin 658cefbe806b) and compared, name-keyed, with the donor's same file in
# the donor's own image (cgif_file_fuzzer.asan 7093581aab04 + twin 488e39500746; .asan-ubsan 1c29845fe605 + ce511d541cda).
R=$1; O=$2; H=$(cd "$(dirname "$0")" && pwd)
T=$R/tree/cmd/proofs/plugin-hostd/fuzz_command/lib
C=$R/tree/cgif/proofs/cgif/cgif_file_fuzzer/lib
mkdir -p "$O"
run() {  # FILE REL DONORFILE IMG(A|B) RUN NAME
  python3 "$H/rule_states.py" --file "$1" --rel "$2" --pin "$R/img/cmd.$4.pin" --twin "$R/img/cmd.$4.twin" \
    --kit "$H/kit" --donor-file "$3" --donor-pin "$R/img/cgif.$4.pin" --donor-twin "$R/img/cgif.$4.twin" \
    --rows "$R/triage/$5.gen.tsv" --out-rows "$O/$6.rows.tsv" --out-nums "$O/$6.nums.tsv" --out-ctl "$O/$6.ctl.tsv" \
    > "$O/$6.summary.txt" 2> "$O/$6.err"
  echo $? > "$O/$6.rc"
}
run "$T/A/AB03.v" lib/A/AB03.v "$C/A/AB03.v" A RA AB03 &
run "$T/B/YB03.v" lib/B/YB03.v "$C/YB03.v" B RB YB03 &
run "$T/A/AB01.v" lib/A/AB01.v "$C/A/AB01.v" A RA AB01 &
run "$T/B/YB01.v" lib/B/YB01.v "$C/YB01.v" B RB YB01 &
wait
cat "$O"/*.rc
