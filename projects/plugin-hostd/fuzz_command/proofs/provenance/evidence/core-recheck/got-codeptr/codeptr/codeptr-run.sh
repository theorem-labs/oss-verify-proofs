#!/usr/bin/env bash
# codeptr 12348302dfd2 (the version of record) on fuzz_command's start-up / table files, both images: every literal
# checked against the unit's own image (code = instruction start, data = in a section) and stale-checked against
# cgif_file_fuzzer's image, PAIRED with the donor's own version of each file (--stale-dir). No --same and no
# --not-address declaration: every flag is triaged by hand with a measurement (codeptr-triage.tsv).
# Then cplimit.py re-judges the literals codeptr passes without comparing names (registered limits H12 / H13).
#
# Run from a directory that holds:
#   tool/   codeptr.py (sha256 12348302dfd2) + pautrlen/ (absint 5acaf718a245, base d3f7ec3c6fa4, compose 7bf620a82573,
#           names eb031db5a107, rvdis acc3b31392a5; byte-equal to tools/startup-set/2026-10-30d/pautrlen/)
#   ours/   proofs/plugin-hostd/fuzz_command at the series head
#   cgif/   proofs/cgif/cgif_file_fuzzer at c8557374ad2e
#   img/    cmd.A.pin (fuzz_command.asan c0661b96b5bd) cmd.A.twin (68db792d5fa7) cmd.B.pin (fuzz_command.asan-ubsan
#           bbe55d24d096) cmd.B.twin (658cefbe806b) cgif.A.pin (7093581aab04) cgif.A.twin (488e39500746)
#           cgif.B.pin (1c29845fe605) cgif.B.twin (ce511d541cda)
# Usage: bash codeptr-run.sh [OUTDIR [SIDES]]   (SIDES "A B" by default; writes OUTDIR/codeptr-{A,B}.out and
#        OUTDIR/cplimit-{A,B}.tsv)
set -u
OUT=${1:-.}
HERE=$(cd "$(dirname "$0")" && pwd)
[ "$(sha256sum < tool/codeptr.py | cut -c1-12)" = 12348302dfd2 ] || { echo "tool/codeptr.py is not 12348302dfd2"; exit 2; }
for f in img/cmd.A.pin img/cmd.A.twin img/cmd.B.pin img/cmd.B.twin img/cgif.A.pin img/cgif.A.twin img/cgif.B.pin img/cgif.B.twin; do
  [ -f "$f" ] || { echo "missing $f"; exit 2; }
done
FILES="AB01 AB03 AB05 AB12 AB1h AB1k AB1w ACej AD1k AD2i AD2j AE3i AF0m"
for side in ${2:-A B}; do
  args=()
  for f in $FILES; do
    if [ $side = A ]; then args+=("ours/lib/A/$f.v"); else args+=("ours/lib/B/Y${f#A}.v"); fi
  done
  python3 tool/codeptr.py --image img/cmd.$side.pin --names img/cmd.$side.twin \
    --stale-image img/cgif.$side.pin --stale-names img/cgif.$side.twin --stale-dir cgif/lib "${args[@]}" \
    > "$OUT/codeptr-$side.out" 2>&1
  echo "rc=$?" >> "$OUT/codeptr-$side.out"
  python3 "$HERE/cplimit.py" --tool tool --image img/cmd.$side.pin --names img/cmd.$side.twin \
    --stale-image img/cgif.$side.pin --stale-names img/cgif.$side.twin --stale-dir cgif/lib "${args[@]}" \
    > "$OUT/cplimit-$side.tsv" 2>&1
  echo "# rc=$?" >> "$OUT/cplimit-$side.tsv"
done
