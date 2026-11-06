#!/bin/sh
# run.sh -- read every NOSYM cell of the unit's two YH03 address tables against the unit's pins, and judge it.
# yh03check fb3bfbc1eea8 leaves 44 D cells per file NOSYM (no symbol carries the cell's name) and checks nothing about
# them. nosym_table.py judges each one by the rule its name states; refs.py shows the code that forms the addresses
# whose rule needs it. Nothing is written outside OUT. Read-only on every image and on the repository.
#
# usage, from the unit's proofs directory (the one holding lib/ and provenance/):
#   PINNED_DIR=<dir of the pinned binaries> TWIN_DIR=<dir of their unstripped twins> HARNESS=<harness.yaml> \
#   KIT=<a copy of comparison kit 86da41d3ef68> YH03TOOLS=<a copy of yh03check fb3bfbc1eea8> \
#   REPO=<the hub clone> REF=<the commit the two YH03.v are read at> OUT=<output directory> sh run.sh
# Needs pyelftools and capstone on PYTHONPATH.
set -eu
: "${PINNED_DIR:?}" "${TWIN_DIR:?}" "${HARNESS:?}" "${KIT:?}" "${YH03TOOLS:?}" "${REPO:?}" "${REF:?}" "${OUT:?}"
H=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT"
U=proofs/libreac/fuzz_decode

# 1. the two tables under yh03check fb3bfbc1eea8, each against its own pin (the files are unchanged, so this is the
#    run of record repeated: its summary lines must equal check-fb3bfbc1eea8.<side>.summary.txt beside this file)
for side in plain ubsan; do
  [ "$side" = plain ] && V=lib/Reusable/YH03.v || V=lib/U/Reusable/YH03.v
  python3 "$YH03TOOLS"/yh03check.py --pinned "$PINNED_DIR/fuzz_decode.$side" --pins "$HARNESS" --side "$side" \
    "$TWIN_DIR/fuzz_decode.$side" "$V" > "$OUT/check.$side.out" 2>&1          # the tool writes its rows to stdout
                                                                                 # and its summary lines to stderr
  grep '^#' "$OUT/check.$side.out" > "$OUT/check.$side.summary.txt"
  printf 'yh03check %s: exit 0; REFUSED lines %s; rows not OK %s\n' "$side" \
    "$(grep -c REFUS "$OUT/check.$side.out" || true)" "$(sed -n 's/.*rows not OK: \([0-9]*\).*/\1/p' "$OUT/check.$side.out")"
  printf 'two definitions on one line, %s: %s\n' "$V" \
    "$(grep -cE 'Definition [a-z0-9]+_D_.*Definition [a-z0-9]+_D_' "$V" || true)"
done

# 2. the readers of every NOSYM cell outside the two YH03.v, from the repository at REF. The scanner of record blocks
#    one driver prefix outside .v files; MASK is read from the table itself and every output here writes CODENAME for
#    it, so no file of this slice holds it. The two YH03.v keep the real names.
MASK=$(sed -n 's/^Definition src0_D_\([a-z0-9]*\)_arg0 .*/\1/p' lib/Reusable/YH03.v | head -1)
[ -n "$MASK" ] || { echo "run.sh: no driver prefix found in lib/Reusable/YH03.v" >&2; exit 1; }
: > "$OUT/nosym-readers.work.tsv"
for n in $(awk -F'\t' '$3=="NOSYM" {print $2}' "$OUT/check.plain.out"); do
  hits=$(git -C "$REPO" grep -w -n "src0_$n" "$REF" -- "$U" \
         | grep -v -e 'lib/Reusable/YH03.v' -e 'lib/U/Reusable/YH03.v' | sed "s/^$REF://" || true)
  printf '%s\t%s\t%s\n' "$n" "$(printf '%s' "$hits" | grep -c . || true)" "$(printf '%s' "$hits" | tr '\n' ' ')" \
    >> "$OUT/nosym-readers.work.tsv"
done
sed "s/$MASK/CODENAME/g" "$OUT/nosym-readers.work.tsv" > "$OUT/nosym-readers.tsv"

# 3. the judgement, per file
for side in plain ubsan; do
  [ "$side" = plain ] && V=lib/Reusable/YH03.v || V=lib/U/Reusable/YH03.v
  python3 "$H/nosym_table.py" "$KIT" "$V" "$PINNED_DIR/fuzz_decode.$side" "$TWIN_DIR/fuzz_decode.$side" \
    "$OUT/nosym-readers.tsv" --mask "$MASK" > "$OUT/nosym-$side.tsv" 2> "$OUT/nosym-$side.detail"
  awk -F'\t' 'NR>1 {v[$9]++} END {printf "nosym-%s.tsv:", s; for (k in v) printf " %s %d", k, v[k]; print ""}' \
    s="$side" "$OUT/nosym-$side.tsv"
done

# 4. the code that forms the addresses whose rule needs it: the four GOT slots that hold 0, the two tables with no
#    symbol, the three jump tables, and the fmt_fp 1e9 reciprocal
for side in plain ubsan; do
  [ "$side" = plain ] && V=lib/Reusable/YH03.v || V=lib/U/Reusable/YH03.v
  A=$(awk -v f="$V" '$0 ~ "^Definition src0_(D_got_DYNAMIC|D_got_register_frame_info|D_got_deregister_frame_info|D_got_LLVMFuzzerInitialize|D_debruijn32|D_size_classes|D_jt_printf_core_1|D_jt_printf_core_2|D_jt_pop_arg|D_const_u64_fmt_fp_1e9_recip_misc) " {gsub(/\.$/,"",$NF); printf "%s%s", (n++?",":""), $NF}' "$V")
  python3 "$H/refs.py" "$KIT" "$TWIN_DIR/fuzz_decode.$side" "$A" > "$OUT/nosym-refs.$side.out"
done
