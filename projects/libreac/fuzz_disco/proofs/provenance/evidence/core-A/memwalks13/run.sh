#!/bin/bash
# Re-derive the 13 runtime memcpy / memset walk files of libreac/fuzz_disco image A
# (proofs/libreac/fuzz_disco/lib/A/{AE2q,AE2r,AE6l,AE6m,AE6n,AE6o,AE6p,AE6q,AE6r,AE6s,AE6t,AE6u,AE6v}.v) and the
# tables of their relocation run with tool/port_core.py (port_core tag abfd17f8b3d2, every input an argument), check
# only (no --apply), with the override row and the patch of inputs/. Then compare:
#   - each stage-out file with the shipped file: every line but line 4 byte-equal (cmp); line 4, the provenance
#     comment, exactly the tool's form in stage-out and exactly the release's form in the shipped file (below);
#   - check.tsv, fixed.tsv, decimals.tsv, overrides.tsv of the run with tables/ (cmp);
#   - port_core's exit status 0 (every gate of the run passes, the symbol gate included).
# Exit 0 only when all of them hold.
#
# usage: run.sh REPO A_PIN B_PIN CGIF_ASAN CGIF_ASAN_UBSAN GATE_SCRIPT GATE_DONORS GATE_CACHE OUTDIR [port_core options]
#   REPO             checkout root with proofs/cgif/cgif_file_fuzzer/lib (the donor text) and
#                    proofs/libreac/fuzz_disco/lib (the target lib and the shipped files)
#   A_PIN            fuzz_disco.asan, the target image (sha256 5e39150dd810...)
#   B_PIN            fuzz_disco.asan-ubsan, the unit's other image (--known-elf; sha256 cee6f04ad3d4...)
#   CGIF_ASAN        cgif_file_fuzzer.asan, the donor image (sha256 7093581aab04...)
#   CGIF_ASAN_UBSAN  cgif_file_fuzzer.asan-ubsan, the donor's other image (--twin-image; sha256 1c29845fe605...)
#   GATE_SCRIPT      port_addr_check.py tag 5033540ba83b, the symbol gate (sha256 5033540ba83b...), in its tag
#                    directory (scan_literals.py beside it)
#   GATE_DONORS      the symbol gate's --donors-from directory
#   GATE_CACHE       a directory of the symbol gate's recoveries of stripped images (<image sha16>.<donors
#                    sha16>.v*.json): port_core copies them into the run's private gate cache (--gate-cache)
#   OUTDIR           a new or empty directory: port_core's --work
set -u
export PYTHONDONTWRITEBYTECODE=1
if [ $# -lt 9 ]; then
    sed -n '12,25p' "$0" >&2
    exit 2
fi
REPO=$1 A_PIN=$2 B_PIN=$3 CGIF_ASAN=$4 CGIF_ASAN_UBSAN=$5 GATE_SCRIPT=$6 GATE_DONORS=$7 GATE_CACHE=$8 OUT=$9
shift 9
[ -d "$GATE_CACHE" ] || { echo "run.sh: GATE_CACHE $GATE_CACHE is not a directory"; exit 2; }
HERE=$(cd "$(dirname "$0")" && pwd)
SRC_LIB=$REPO/proofs/cgif/cgif_file_fuzzer/lib
TARGET_LIB=$REPO/proofs/libreac/fuzz_disco/lib
TWIN_TXT=$HERE/../twin/fuzz_disco.asan.twin.txt
OLD_SYMS=$HERE/../inputs/cgif_file_fuzzer.asan.syms.txt
fail=0

check_sha() {  # FILE PREFIX
    local got
    got=$(sha256sum "$1" | cut -d' ' -f1)
    case $got in
        "$2"*) echo "sha256 ok   $got  $(basename "$1")" ;;
        *) echo "sha256 FAIL $got  $1 (want $2...)"; fail=1 ;;
    esac
}
check_sha "$A_PIN" 5e39150dd8104df969eb360f9cc29c4f92fe12326afd23783a679e4fb4809f46
check_sha "$B_PIN" cee6f04ad3d4928e242405689ae058bb9e8b6533000c90bde984a2f0d5ff5146
check_sha "$CGIF_ASAN" 7093581aab040cfd94ed56f83bf44a37e6ec3c34db39cc57bf467e2949e870f0
check_sha "$CGIF_ASAN_UBSAN" 1c29845fe6058de6e1dbf3f6ec6abd566ea612d76b65ea5435d7ff77c63e08ef
check_sha "$GATE_SCRIPT" 5033540ba83bdad174e9b1aa3cc21ffeda3469736e4dd0390f58db9008890546
[ "$fail" = 0 ] || { echo "run.sh: an input is not the pinned file"; exit 1; }
if [ -e "$OUT" ] && [ -n "$(ls -A "$OUT")" ]; then
    echo "run.sh: OUTDIR $OUT is not empty"; exit 2
fi
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)

nice python3 "$HERE/tool/port_core.py" \
  --src-lib  "$SRC_LIB" \
  --old-elf  "$CGIF_ASAN" \
  --old-prog 80490:86bcc \
  --old-syms "$OLD_SYMS" \
  --twin-image "$CGIF_ASAN_UBSAN" \
  --target-lib    "$TARGET_LIB" \
  --target-mod    OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib \
  --target-images OssFuzzTheorems.libreac.fuzz_disco.images \
  --target-name   libreac/fuzz_disco \
  --target-elf    "$A_PIN" \
  --target-syms   "$TWIN_TXT" \
  --known-elf     "$B_PIN" \
  --reusable-dir  Reusable \
  --gate-script   "$GATE_SCRIPT" \
  --gate-donors   "$GATE_DONORS" \
  --gate-cache    "$GATE_CACHE" \
  --files    "$HERE/inputs/files13.txt" \
  --override "$HERE/inputs/overrides-abfd17f8b3d2.tsv" \
  --patch    "$HERE/inputs/patch-abfd17f8b3d2.diff" \
  --work "$OUT" "$@" 2> "$OUT/port_core.err"
rc=$?
grep -h '^port_core: symbol gate' "$OUT/port_core.err"
if [ "$rc" = 0 ]; then echo "port_core exit 0"; else echo "port_core exit $rc FAIL (see $OUT/port_core.err)"; fail=1; fi

# Line 4 is the provenance comment. port_core writes
#   (* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/F (donor image sha256 H), with
#      its module paths changed[ and its addresses moved to libreac/fuzz_disco's ASan build]. *)
# (the last clause only when a numeral of F moved); the shipped file holds the release's line in its place:
#   (* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/F, with its module paths
#      changed and its addresses moved to libreac/fuzz_disco's ASan build. *)
donor12=$(sha256sum "$CGIF_ASAN" | cut -c1-12)
pre="(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/"
moved=" and its addresses moved to libreac/fuzz_disco's ASan build"
while read -r f; do
    a=$OUT/stage-out/$f b=$TARGET_LIB/$f
    if ! cmp -s <(sed 4d "$a") <(sed 4d "$b"); then
        echo "FAIL $f: lines other than 4 differ: $(cmp <(sed 4d "$a") <(sed 4d "$b") 2>&1)"; fail=1; continue
    fi
    l4=$(sed -n 4p "$a") s4=$(sed -n 4p "$b")
    ship="$pre$f, with its module paths changed$moved. *)"
    if cmp -s "$a" "$b"; then
        echo "ok   $f: $(wc -l < "$b") lines; cmp-equal"
    elif [ "$s4" = "$ship" ] && [ "$l4" = "$pre$f (donor image sha256 $donor12), with its module paths changed$moved. *)" ]; then
        echo "ok   $f: $(wc -l < "$b") lines; every line but 4 cmp-equal; line 4: tool form (addresses moved), release form"
    elif [ "$s4" = "$ship" ] && [ "$l4" = "$pre$f (donor image sha256 $donor12), with its module paths changed. *)" ]; then
        echo "ok   $f: $(wc -l < "$b") lines; every line but 4 cmp-equal; line 4: tool form (no address moved), release form"
    else
        echo "FAIL $f: line 4"; echo "  tool:    $l4"; echo "  shipped: $s4"; fail=1
    fi
done < <(grep -v '^#' "$HERE/inputs/files13.txt")
for t in check.tsv fixed.tsv decimals.tsv overrides.tsv; do
    if cmp "$OUT/$t" "$HERE/tables/$t"; then echo "ok   $t: cmp-equal to tables/$t"; else echo "FAIL $t"; fail=1; fi
done
if [ "$fail" = 0 ]; then echo "run.sh: ALL MATCH"; else echo "run.sh: MISMATCH"; fi
exit $fail
