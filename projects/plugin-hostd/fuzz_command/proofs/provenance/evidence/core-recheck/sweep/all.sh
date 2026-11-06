#!/usr/bin/env bash
# The whole sweep: rows (run.sh), then the triage of every non-SAME row, for the runs and for the controls.
set -eu
cd "$(dirname "$0")"
bash run.sh
python3 triage.py --out mismatches.tsv --adjacent adjacent.tsv > work/triage.out
python3 triage.py --rows work/ctl/rows.tsv --out work/ctl/mismatches.tsv --adjacent work/ctl/adjacent.tsv \
  > work/ctl/triage.out
