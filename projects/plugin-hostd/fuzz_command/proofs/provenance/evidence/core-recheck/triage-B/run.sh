#!/usr/bin/env bash
# run.sh WORK -- WORK is the work area of the re-check (layout: WORK/tree/{cmd,cgif}/proofs/..., WORK/img/*,
# WORK/runs/{RB,RAB}/full.tsv, WORK/triage/{base_triage.py,RB.open.tsv,flag-classes.txt,gen-B.txt}, this folder at
# WORK/out/triage-B). Recomputes the RAB open set with base_triage.py, then runs triage.py.
set -eu
P=${1:?usage: run.sh WORK}
D=$P/out/triage-B
cd "$D"
python3 "$P/triage/base_triage.py" "$P/runs/RAB/full.tsv" "$P/tree/cmd/proofs/plugin-hostd/fuzz_command/lib/B" \
  "$P/triage/flag-classes.txt" "$P/triage/gen-B.txt" "$D/RAB" > "$D/RAB.base_triage.out"
rm -f "$D/RAB.gen.tsv"
python3 triage.py --lib "$P/tree/cmd/proofs/plugin-hostd/fuzz_command/lib" \
  --cgif-lib "$P/tree/cgif/proofs/cgif/cgif_file_fuzzer/lib" \
  --img-b "$P/img/cmd.B.pin" "$P/img/cmd.B.twin" --img-a "$P/img/cmd.A.pin" "$P/img/cmd.A.twin" \
  --img-cgif-b "$P/img/cgif.B.pin" "$P/img/cgif.B.twin" \
  --rb-open "$P/triage/RB.open.tsv" --rab-full "$P/runs/RAB/full.tsv" --rab-open "$D/RAB.open.tsv" --out "$D" > "$D/triage.out"
