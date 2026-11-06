#!/usr/bin/env bash
# run.sh REPO PIN_A OUTDIR -- re-run the scripts of this directory against a checkout and image A, and compare each
# output with the file shipped here. Exit status 0 only when every comparison matches.
#   REPO    root of a checkout that holds proofs/libreac/fuzz_disco
#   PIN_A   image A, the released fuzz_disco.asan (sha256 5e39150dd8104df9...)
#   OUTDIR  directory for the outputs (created when absent)
# Environment: PYTHON (default python3), with pyelftools.
#
# 1. gen_globals_cells.py on image A -> globals-cells-disco-asan.txt (image top read from lib/Reusable/YImgTop.v).
# 2. check_globals_in_af0m.py: every DESC / SHADOW / ZERO line of that table, and every row of
#    af0m-runtime-cells.tsv, is in lib/A/AF0m.v; then a planted control (one DESC value changed) must fail.
# 3. cellcheck.py on lib/A/AF0m.v and on a planted control (one file-backed cell changed) -> cellcheck-record.txt.
set -u
export PYTHONDONTWRITEBYTECODE=1
[ $# -eq 3 ] || { echo "usage: $0 REPO PIN_A OUTDIR" >&2; exit 2; }
HERE=$(cd "$(dirname "$0")" && pwd)
U="$1/proofs/libreac/fuzz_disco"
PIN=$2
OUT=$3
PY=${PYTHON:-python3}
AF0M="$U/lib/A/AF0m.v"
mkdir -p "$OUT/stage" "$OUT/control/stage" || exit 2
fail=0
same() { if cmp "$1" "$2"; then echo "cmp OK   $3"; else echo "cmp FAIL $3"; fail=1; fi; }
sha() { sha256sum < "$1" | cut -d' ' -f1; }
OLD_CELL='z8 (ANum 0xa4dc0) 0x20f80  ;'
NEW_CELL='z8 (ANum 0xa4dc0) 0x20f81  ;'
plant() {  # plant SRC DST: SRC with OLD_CELL changed to NEW_CELL; prints the number of differing bytes
    sed "s/^z8 (ANum 0xa4dc0) 0x20f80  ;\$/z8 (ANum 0xa4dc0) 0x20f81  ;/" "$1" > "$2"
    cmp -l "$1" "$2" | wc -l
}

echo "image A sha256 $(sha "$PIN")"
echo "lib/A/AF0m.v sha256 $(sha "$AF0M")"

# 1. globals table
TOP=$(sed -n 's/^Definition IMG_TOP : Z := \(0x[0-9a-f]*\)\.$/\1/p' "$U/lib/Reusable/YImgTop.v")
[ -n "$TOP" ] || { echo "FAIL no IMG_TOP in lib/Reusable/YImgTop.v"; exit 1; }
echo "image top from lib/Reusable/YImgTop.v: $TOP"
"$PY" "$HERE/gen_globals_cells.py" "$PIN" --img-top "$TOP" --img-top-name YImgTop.IMG_TOP \
    > "$OUT/globals-cells-disco-asan.txt" || fail=1
same "$OUT/globals-cells-disco-asan.txt" "$HERE/globals-cells-disco-asan.txt" \
    "globals-cells-disco-asan.txt (gen_globals_cells.py on image A) = shipped table"

# 2. the table and the runtime rows are in AF0m.v; planted control
"$PY" "$HERE/check_globals_in_af0m.py" "$OUT/globals-cells-disco-asan.txt" "$AF0M" "$HERE/af0m-runtime-cells.tsv" \
    && echo "check OK   globals table and runtime rows present in lib/A/AF0m.v" \
    || { echo "check FAIL globals table or runtime rows"; fail=1; }
nd=$(plant "$OUT/globals-cells-disco-asan.txt" "$OUT/control/globals-cells.planted.txt")
"$PY" "$HERE/check_globals_in_af0m.py" "$OUT/control/globals-cells.planted.txt" "$AF0M" > "$OUT/control/check.out"
rc=$?
if [ "$nd" -eq 1 ] && [ $rc -ne 0 ] && [ "$(sed -n 's/^\(MISSING DESC\).*/\1/p' "$OUT/control/check.out" | wc -l)" -eq 1 ]; then
    echo "control OK table with '$OLD_CELL' changed to '$NEW_CELL' ($nd byte): rc $rc, 1 MISSING DESC line"
else
    echo "control FAIL table plant: $nd byte(s) changed, rc $rc"; cat "$OUT/control/check.out"; fail=1
fi

# 3. cellcheck record
cp "$AF0M" "$OUT/stage/AF0m.v"
nd=$(plant "$OUT/stage/AF0m.v" "$OUT/control/stage/AF0m.v")
"$PY" "$HERE/cellcheck.py" "$OUT/stage" "$PIN" > "$OUT/cc1.out" 2> "$OUT/cc1.err"; rc1=$?
"$PY" "$HERE/cellcheck.py" "$OUT/control/stage" "$PIN" > "$OUT/cc2.out" 2> "$OUT/cc2.err"; rc2=$?
{
    echo "# cellcheck.py record: the file-backed zN (ANum A) V cells of lib/A/AF0m.v (proofs/libreac/fuzz_disco)"
    echo "# against image A. Written by af0m/run.sh. Each run shows cellcheck.py's stdout (mismatch rows: file, line,"
    echo "# addr, n, written, image), then its stderr (the count), then its exit status."
    echo "tool  cellcheck.py sha256 $(sha "$HERE/cellcheck.py")"
    echo "image A (fuzz_disco.asan) sha256 $(sha "$PIN")"
    echo "## run 1: the shipped file"
    echo "input lib/A/AF0m.v sha256 $(sha "$OUT/stage/AF0m.v")"
    cat "$OUT/cc1.out" "$OUT/cc1.err"
    echo "rc $rc1"
    echo "## run 2: planted control: run 1's file with '$OLD_CELL' changed to '$NEW_CELL' ($nd byte differs)"
    echo "input AF0m.v (control) sha256 $(sha "$OUT/control/stage/AF0m.v")"
    cat "$OUT/cc2.out" "$OUT/cc2.err"
    echo "rc $rc2"
} > "$OUT/cellcheck-record.txt"
if [ $rc1 -eq 0 ] && [ $rc2 -ne 0 ] && [ "$nd" -eq 1 ]; then
    echo "cellcheck OK   shipped file rc $rc1, planted control rc $rc2"
else
    echo "cellcheck FAIL shipped file rc $rc1, planted control rc $rc2, $nd byte(s) planted"; fail=1
fi
same "$OUT/cellcheck-record.txt" "$HERE/cellcheck-record.txt" "cellcheck-record.txt (written by this run) = shipped record"

[ $fail -eq 0 ] && echo "af0m: ALL MATCH" || echo "af0m: FAILED"
exit $fail
