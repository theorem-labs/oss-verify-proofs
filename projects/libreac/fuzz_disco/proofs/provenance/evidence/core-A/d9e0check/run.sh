#!/bin/bash
# Check run of port_core d9e0589898fd (the best available port_core tag; NOT of record: 57 silent wrong rows on the
# relocation plant set) on the SAME inputs as the re-runnable relocation run of ../memwalks13/ (port_core
# abfd17f8b3d2 with inputs/overrides-abfd17f8b3d2.tsv and inputs/patch-abfd17f8b3d2.diff), check only (no --apply).
# Then:
#   1. classify.py: compare each of the 13 stage-out files of this run by sha256 with the abfd17f8b3d2 stage-out and
#      with the shipped file; classify each file that differs (provenance-only / patched / VALUE) -> classes.tsv;
#   2. checks.py: the four checks every d9e0589898fd output needs -> checks.txt;
#   3. cmp both with the shipped copies in this directory.
# Exit 0 only when port_core exits 0, both outputs are cmp-equal to the shipped copies and no file is VALUE.
#
# usage: run.sh REPO A_PIN B_PIN CGIF_ASAN CGIF_ASAN_UBSAN A_TWIN D9E0_DIR GATE_DONORS GATE_CACHE ABFD_WORK OUTDIR
#   REPO             checkout root with proofs/cgif/cgif_file_fuzzer/lib and proofs/libreac/fuzz_disco/lib
#   A_PIN            fuzz_disco.asan, the target image (sha256 5e39150dd810...)
#   B_PIN            fuzz_disco.asan-ubsan (--known-elf; sha256 cee6f04ad3d4...)
#   CGIF_ASAN        cgif_file_fuzzer.asan, the donor image (sha256 7093581aab04...)
#   CGIF_ASAN_UBSAN  cgif_file_fuzzer.asan-ubsan (--twin-image; sha256 1c29845fe605...)
#   A_TWIN           the unstripped twin of A_PIN (--target-syms; sha256 b8aac6eee6a6..., the twin that
#                    ../twin/fuzz_disco.asan.twin.txt is extracted from)
#   D9E0_DIR         the port_core tag directory d9e0589898fd (port_core.py sha256 d9e0589898fd..., with its
#                    modules and gate/port_addr_check.py); it is copied into OUTDIR and run from the copy
#   GATE_DONORS      the symbol gate's --donors-from directory (as ../memwalks13/run.sh)
#   GATE_CACHE       the symbol gate's directory of recoveries of stripped images (<image sha16>.<donors
#                    sha16>.v*.json) under the directory name port_core d9e0589898fd reads beside its gate script
#                    (the name is fixed in the tool): it is copied, with its name, into the tag copy's gate/
#   ABFD_WORK        the --work directory of a ../memwalks13/run.sh run (its stage-out/ is compared)
#   OUTDIR           a new or empty directory
set -u
export PYTHONDONTWRITEBYTECODE=1
if [ $# -ne 11 ]; then
    echo "usage: run.sh REPO A_PIN B_PIN CGIF_ASAN CGIF_ASAN_UBSAN A_TWIN D9E0_DIR GATE_DONORS GATE_CACHE ABFD_WORK OUTDIR" >&2
    exit 2
fi
REPO=$1 A_PIN=$2 B_PIN=$3 CGIF_ASAN=$4 CGIF_ASAN_UBSAN=$5 A_TWIN=$6 D9E0_DIR=$7 GATE_DONORS=$8 GATE_CACHE=$9
ABFD_WORK=${10} OUT=${11}
HERE=$(cd "$(dirname "$0")" && pwd)
fail=0
check_sha() {  # FILE SHA256
    local got
    got=$(sha256sum "$1" | cut -d' ' -f1)
    if [ "$got" = "$2" ]; then echo "sha256 ok   $got  $(basename "$1")"; else echo "sha256 FAIL $got  $1 (want $2)"; fail=1; fi
}
check_sha "$A_PIN" 5e39150dd8104df969eb360f9cc29c4f92fe12326afd23783a679e4fb4809f46
check_sha "$B_PIN" cee6f04ad3d4928e242405689ae058bb9e8b6533000c90bde984a2f0d5ff5146
check_sha "$CGIF_ASAN" 7093581aab040cfd94ed56f83bf44a37e6ec3c34db39cc57bf467e2949e870f0
check_sha "$CGIF_ASAN_UBSAN" 1c29845fe6058de6e1dbf3f6ec6abd566ea612d76b65ea5435d7ff77c63e08ef
check_sha "$A_TWIN" b8aac6eee6a62fef29b9e9a7df6154c2cda9a8f0252cbae45ad85bcc91135b6e
check_sha "$D9E0_DIR/port_core.py" d9e0589898fd12f83fd76e086a3d7ddf3d1a43a7008dd59a73f442bff30388aa
[ "$fail" = 0 ] || { echo "run.sh: an input is not the pinned file"; exit 1; }
[ -d "$GATE_CACHE" ] || { echo "run.sh: GATE_CACHE $GATE_CACHE is not a directory"; exit 2; }
[ -d "$ABFD_WORK/stage-out" ] || { echo "run.sh: ABFD_WORK $ABFD_WORK has no stage-out/"; exit 2; }
if [ -e "$OUT" ] && [ -n "$(ls -A "$OUT")" ]; then echo "run.sh: OUTDIR $OUT is not empty"; exit 2; fi
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
cp -r "$D9E0_DIR" "$OUT/tool"
cp -r "$GATE_CACHE" "$OUT/tool/gate/"
MW=$HERE/../memwalks13

# the arguments of ../memwalks13/run.sh, with the twin ELF for --target-syms and the tag's own symbol gate
nice python3 "$OUT/tool/port_core.py" \
  --src-lib  "$REPO/proofs/cgif/cgif_file_fuzzer/lib" \
  --old-elf  "$CGIF_ASAN" \
  --old-prog 80490:86bcc \
  --old-syms "$HERE/../inputs/cgif_file_fuzzer.asan.syms.txt" \
  --twin-image "$CGIF_ASAN_UBSAN" \
  --target-lib    "$REPO/proofs/libreac/fuzz_disco/lib" \
  --target-mod    OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib \
  --target-images OssFuzzTheorems.libreac.fuzz_disco.images \
  --target-name   libreac/fuzz_disco \
  --target-elf    "$A_PIN" \
  --target-syms   "$A_TWIN" \
  --known-elf     "$B_PIN" \
  --reusable-dir  Reusable \
  --gate-script   "$OUT/tool/gate/port_addr_check.py" \
  --gate-donors   "$GATE_DONORS" \
  --files    "$MW/inputs/files13.txt" \
  --override "$MW/inputs/overrides-abfd17f8b3d2.tsv" \
  --patch    "$MW/inputs/patch-abfd17f8b3d2.diff" \
  --work "$OUT/work" 2> "$OUT/port_core.err"
rc=$?
grep -h '^port_core: symbol gate' "$OUT/port_core.err"
if [ "$rc" = 0 ]; then echo "port_core exit 0"; else echo "port_core exit $rc FAIL (see $OUT/port_core.err)"; fail=1; fi

python3 "$HERE/classify.py" "$MW/inputs/files13.txt" "$ABFD_WORK/stage-out" "$OUT/work/stage-out" \
    "$REPO/proofs/libreac/fuzz_disco/lib" "$OUT/classes.tsv" || fail=1
python3 "$HERE/checks.py" "$OUT/work" "$CGIF_ASAN" "$HERE/../inputs/cgif_file_fuzzer.asan.syms.txt" "$A_PIN" "$A_TWIN" \
    "$OUT/checks.txt" || fail=1
for t in classes.tsv checks.txt; do
    if cmp "$OUT/$t" "$HERE/$t"; then echo "ok   $t: cmp-equal to d9e0check/$t"; else echo "FAIL $t"; fail=1; fi
done
if [ "$fail" = 0 ]; then echo "d9e0check: ALL MATCH"; else echo "d9e0check: MISMATCH"; fi
exit $fail
