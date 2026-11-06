#!/usr/bin/env bash
# Re-run the false-equal check from a cold start.
# Usage: run.sh BASE
#   BASE = the copy root that holds tree/{cmd,cgif}/proofs/..., img/{cgif,cmd}.{A,B}.{pin,twin},
#          runs/{RA,RB,RU}/full.tsv and out/false-equal/img/{cgif,cmd}.P.{pin,twin}.
# Writes rows.tsv, counts.txt and controls.txt beside this script. Needs python3 + pyelftools.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
python3 feq_check.py --base "$1" --out rows.tsv > counts.txt
python3 feq_controls.py --base "$1" --out controls.txt
sha256sum feq_lib.py feq_check.py feq_roles.py feq_controls.py rows.tsv controls.txt | cut -c1-12,65-
