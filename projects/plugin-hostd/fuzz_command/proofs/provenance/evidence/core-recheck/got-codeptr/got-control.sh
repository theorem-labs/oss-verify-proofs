#!/usr/bin/env bash
# got-control.sh - the known-answer control of gotcheck.py on the planted copies of the value gate's control.
# The plants (plants.tsv) moved two .got cells to the next GOT word, the class the gate passes as SAME-SYMBOL-ROUNDED:
#   A  ACeg.v:21  A_GOT_uar 0xa6448 -> 0xa6450      B  YCeg.v:22  A_GOT_uar 0xa5fb0 <- 0xa5fa8
# gotcheck.py must FLAG both planted cells in the plant copies and must NOT flag them in the base copies; the rows
# that are not OK in a plant copy and OK in its base copy must be exactly the planted .got cells.
# Usage: bash got-control.sh PLANTDIR RUNSDIR IMGDIR OUTDIR
#   PLANTDIR holds A-base A-plant B-base B-plant; RUNSDIR holds the gate runs PA-base PA-plant PB-base PB-plant
#   (full.tsv each); IMGDIR holds cmd.{A,B}.{pin,twin} and cgif.{A,B}.{pin,twin}.
set -u
P=$1; R=$2; I=$3; O=$4
HERE=$(cd "$(dirname "$0")" && pwd)
fail=0
for side in A B; do
  for v in base plant; do
    python3 "$HERE/gotcheck.py" --side-dir $side="$P/$side-$v" --relto "$P" \
      --img A="$I/cmd.A.pin:$I/cmd.A.twin" --img B="$I/cmd.B.pin:$I/cmd.B.twin" \
      --donor-img A="$I/cgif.A.pin:$I/cgif.A.twin" --donor-img B="$I/cgif.B.pin:$I/cgif.B.twin" \
      --gate $side="$R/P$side-$v/full.tsv" --out "$O/got-$side-$v.tsv" --perturb > "$O/got-$side-$v.out" 2>&1
    echo "gotcheck $side-$v rc=$?: $(awk '/numerals inside/' "$O/got-$side-$v.out")"
  done
  # rows not OK in the plant copy whose partner in the base copy (same file, line and ordinal on the line) is OK
  awk -F'\t' -v side=$side 'FNR == 1 {next}
    FILENAME ~ /base/ {sub(/^[AB]-base\//, "", $1); k = $1 ":" $2; base[k ":" nb[k]++] = $8; next}
    {f = $1; sub(/^[AB]-plant\//, "", f); k = f ":" $2; o = np[k]++
     if ($8 != "OK" && base[k ":" o] == "OK") print side "\t" f ":" $2 "\t" $3 "\t" $4 "\t" $8 "\t" $18 "\t" $14}' \
    "$O/got-$side-base.tsv" "$O/got-$side-plant.tsv" > "$O/got-$side-newflags.tsv"
  echo "== $side: rows not OK in the plant copy, OK in the base copy:"; sed 's/^/  /' "$O/got-$side-newflags.tsv"
  echo "== $side: the planted cell in the base copy:"
  awk -F'\t' -v side=$side 'FNR > 1 && (($1 ~ /ACeg.v$/ && $2 == 21) || ($1 ~ /YCeg.v$/ && $2 == 22))' "$O/got-$side-base.tsv" | cut -f1-8 | sed 's/^/  /'
done
grep -q $'^A\tACeg.v:21\t0xa6450' "$O/got-A-newflags.tsv" || { echo "FAIL: A plant ACeg.v:21 0xa6450 not flagged"; fail=1; }
grep -q $'^B\tYCeg.v:22\t0xa5fb0' "$O/got-B-newflags.tsv" || { echo "FAIL: B plant YCeg.v:22 0xa5fb0 not flagged"; fail=1; }
n=$(cat "$O/got-A-newflags.tsv" "$O/got-B-newflags.tsv" | wc -l)
[ "$n" -eq 2 ] || { echo "FAIL: $n new flags, want exactly the 2 planted .got cells"; fail=1; }
for side in A B; do
  awk -F'\t' 'FNR > 1 && (($1 ~ /ACeg.v$/ && $2 == 21) || ($1 ~ /YCeg.v$/ && $2 == 22)) && $8 != "OK" {bad = 1} END {exit bad}' "$O/got-$side-base.tsv" \
    || { echo "FAIL: the base copy flags the unplanted cell ($side)"; fail=1; }
done
[ $fail -eq 0 ] && echo "got-control: PASS (both planted .got cells flagged; the base copies accept them; no other new flag)" || echo "got-control: FAILED"
exit $fail
