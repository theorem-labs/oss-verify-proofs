#!/bin/sh
# run.sh -- the exposure scans of cmpkit 86da41d3ef68 (tools/cmpkit/86da41d3ef68 at the tools commit 98e50c029045; kit id
# = first 12 hex of sha256(SHA256SUMS)) on every alloc-reloc record made on cmpkit 4bbd3a74be89 (paths relative to
# provenance/evidence/kit-rerun/, the directory above this one):
#   A/kit-rerun-4bbd3a74be89/ (7 pairs, donor twin C : decode A twin)       -> A/kit-rerun-4bbd3a74be89.scans-86da41d3ef68.log
#   B/fncmp.cmpkit-4bbd3a74be89.log (8 functions, S and T : decode B twin) -> B/fncmp.cmpkit-4bbd3a74be89.scans-86da41d3ef68.log
#   cmpkit-4bbd3a74be89/settled.tsv (3 settled rows, S:E and T:E)          -> cmpkit-4bbd3a74be89/settled.scans-86da41d3ef68.log
#   the twin proofs                                                         -> cmpkit-86da41d3ef68/twins.log
#   the lui trace of the B record (the KIT LIMIT: luiscan follows addi / load / store / jalr only, so `memfed 0` is not
#   proof): the A record's own luitrace.py over the 8 functions, T : E and S : E, and the TryMemCpy words
#                                                                           -> B/luitrace-*-86da41d3ef68.out
#   every `lui-const` in the 86da41d3ef68 outputs of the three records (registry notice: a `lui-const (dataflow)` row
#   is no evidence when the lui value meets a register-register or logical ALU op)
#                                                                           -> cmpkit-86da41d3ef68/luiconst-search.out
# Per record: luiscan.py 9ae61e4a0e01 (rule 8 exposure) on every image of the record, ambiscan.py 9f61b4cee422 (by-name
# compares that hit a duplicated name) on the record's files, and, as a control, the record's compares under
# strictcmp3.py 65688e94214a with diffcheck.py (old against new: verdict, counts, accepted and differing targets).
# usage (KIT and IMG may be relative; the records name only kit/, img/ and kit-rerun/ paths):
#   KIT=<dir holding exactly the nine kit files> IMG=<dir holding bin/ and unstripped/> sh run.sh
# IMG/unstripped: cgif_file_fuzzer.asan-ubsan (donor twin), cgif_file_fuzzer.asan-ubsan.symtwin (provenance/alloc-reloc/
# B/tools/symtwin.py), fuzz_decode.asan, fuzz_decode.asan-ubsan (libreac twins); IMG/bin: cgif_file_fuzzer.asan-ubsan (the
# donor pin; written by ../cmpkit-4bbd3a74be89/pinback.py from the symtwin), fuzz_decode.asan, fuzz_decode.asan-ubsan
# (libreac pins). Needs pyelftools and capstone on PYTHONPATH.
set -eu
: "${KIT:?}" "${IMG:?}"
H=$(cd "$(dirname "$0")" && pwd)
R=$(dirname "$H")
KITA=$(cd "$KIT" && pwd); IMGA=$(cd "$IMG" && pwd)
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
export PYTHONDONTWRITEBYTECODE=1
FILES='ambiscan.py bytecmp-1480ca2faea0.py closure_strict3.py drvcmp.py jtcheck.py luiscan.py paircl.py repin_check.py strictcmp3.py'
[ "$(ls "$KITA" | tr '\n' ' ')" = "$FILES " ] || { echo "run.sh: $KIT does not hold exactly the nine kit files" >&2; exit 1; }
(cd "$KITA" && sha256sum $FILES) > "$T/sums"
KITID=$(sha256sum < "$T/sums" | cut -c1-12)
[ "$KITID" = 86da41d3ef68 ] || { echo "run.sh: kit id $KITID, want 86da41d3ef68" >&2; exit 1; }
[ "$(sha256sum < "$IMGA/bin/cgif_file_fuzzer.asan-ubsan" | cut -c1-64)" = 1c29845fe6058de6e1dbf3f6ec6abd566ea612d76b65ea5435d7ff77c63e08ef ] \
  || { echo "run.sh: IMG/bin/cgif_file_fuzzer.asan-ubsan is not the donor pin 1c29845fe605" >&2; exit 1; }
ln -s "$KITA" "$T/kit"; ln -s "$IMGA" "$T/img"
mkdir -p "$T/kit-rerun/A" "$T/kit-rerun/B" "$T/kit-rerun/cmpkit-4bbd3a74be89"
cp -R "$R/A/kit-rerun-4bbd3a74be89" "$T/kit-rerun/A/"
cp "$R/B/fncmp.cmpkit-4bbd3a74be89.log" "$T/kit-rerun/B/"
cp "$R/cmpkit-4bbd3a74be89/settled.tsv" "$T/kit-rerun/cmpkit-4bbd3a74be89/"
cp "$H/diffcheck.py" "$H/window.py" "$T/"
cd "$T"
VERS=$(python3 -c 'import sys, elftools, capstone; print("python %s, pyelftools %s, capstone %s" % (sys.version.split()[0], elftools.__version__, capstone.__version__))')
SUMS=$(sed 's/^\(............\)[0-9a-f]*  /\1 /' sums | tr '\n' ';' | sed 's/;$//;s/;/, /g')
SELF="run.sh $(sha256sum < "$H/run.sh" | cut -c1-12), diffcheck.py $(sha256sum < "$H/diffcheck.py" | cut -c1-12), window.py $(sha256sum < "$H/window.py" | cut -c1-12)"
U=img/unstripped; P=img/bin
C=$U/cgif_file_fuzzer.asan-ubsan; S=$U/cgif_file_fuzzer.asan-ubsan.symtwin; DA=$U/fuzz_decode.asan; DB=$U/fuzz_decode.asan-ubsan
ALLOC=_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb
POISON=_ZN6__asan12PoisonShadowEmmh
FA="$ALLOC,_ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm,_ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEEE6RefillEPNS7_8PerClassEPS6_m,$POISON,_ZN11__sanitizer13internal_mmapEPvmiiiy,_ZN11__sanitizer13StackDepotPutENS_10StackTraceE,memset"
FB="$FA,_ZN11__sanitizer9TryMemCpyEPvPKvm"

hdr() {  # hdr TITLE
  echo "# $1"
  echo "# cmpkit $KITID (tools/cmpkit/86da41d3ef68 at the tools commit 98e50c029045): $SUMS"
  echo "# $VERS; provenance/evidence/kit-rerun/cmpkit-86da41d3ef68/$SELF; twin proofs: kit-rerun/cmpkit-86da41d3ef68/twins.log"
}
run() {  # run TITLE COMMAND...: the command line, then its output; a nonzero exit is printed, not fatal
  echo "## $1"; shift
  echo "\$ $*"
  set +e; "$@"; rc=$?; set -e
  [ $rc -eq 0 ] || echo "(exit $rc)"
}
runto() {  # runto FILE TITLE COMMAND...: as run, the output also kept in FILE
  f=$1; shift; echo "## $1"; shift
  echo "\$ $*"
  set +e; "$@" > "$f"; rc=$?; set -e
  cat "$f"; [ $rc -eq 0 ] || echo "(exit $rc)"
}
same() {  # same A B: IDENTICAL when the two files are byte-identical
  if cmp -s "$1" "$2"; then echo IDENTICAL; else echo DIFFERENT; fi
}

{ hdr "twin proofs: each pin against its unstripped twin (drvcmp.py twins)"
  run "drvcmp.py twins" python3 kit/drvcmp.py twins $P/cgif_file_fuzzer.asan-ubsan $C $P/cgif_file_fuzzer.asan-ubsan $S \
      $P/fuzz_decode.asan $DA $P/fuzz_decode.asan-ubsan $DB
} > "$H/twins.log"

A=kit-rerun/A/kit-rerun-4bbd3a74be89
AOUT15=$(cd "$A" && ls out | grep -v -e '86da41d3ef68' -e 'scans-kitsha' -e '^luitrace-' | sed 's#^#'"$A"'/out/#' | tr '\n' ' ')
{ hdr "scans of cmpkit 86da41d3ef68 on the A record $A/ (the 7 pairs C:A of out/run-strictcmp2.out)"
  runto lui.A "luiscan, the 7 functions, both images" python3 kit/luiscan.py --all --fns "$FA" $C $DA
  echo "## the ROW and TOTAL lines above against $A/out/luiscan-86da41d3ef68.out (the record's own scan; its '#' image lines name the images by token)"
  grep -v '^#' lui.A > lui.A.rows; grep -v '^#' "$A/out/luiscan-86da41d3ef68.out" > lui.R.rows; same lui.A.rows lui.R.rows
  runto amb.A "ambiscan, the 15 files of out/ the record's own scan read" python3 kit/ambiscan.py $C $DA $AOUT15
  echo "## the TOTAL line above against $A/out/ambiscan-86da41d3ef68.out (the record's own scan)"
  grep '^TOTAL' amb.A > amb.A.total; grep '^TOTAL' "$A/out/ambiscan-86da41d3ef68.out" > amb.R.total; same amb.A.total amb.R.total
  run "ambiscan, every file of the record directory" python3 kit/ambiscan.py $C $DA $A
  runto s3.A "control: the 7 pairs under strictcmp3" python3 kit/strictcmp3.py cmp "$FA" C=$C A=$DA C:A
  run "control: old record (out/run-strictcmp2.out) against strictcmp3" python3 diffcheck.py "$A/out/run-strictcmp2.out" s3.A
} > "$R/A/kit-rerun-4bbd3a74be89.scans-86da41d3ef68.log" 2>&1

B=kit-rerun/B/fncmp.cmpkit-4bbd3a74be89.log
{ hdr "scans of cmpkit 86da41d3ef68 on the B record $B (the 8 functions, pairs S:E and T:E)"
  run "luiscan, the 8 functions, the three images" python3 kit/luiscan.py --all --fns "$FB" $S $C $DB
  run "ambiscan, S : E" python3 kit/ambiscan.py $S $DB $B
  run "ambiscan, T : E" python3 kit/ambiscan.py $C $DB $B
  runto s3.B "control: the 8 functions under strictcmp3" python3 kit/strictcmp3.py cmp "$FB" S=$S T=$C E=$DB S:E,T:E
  run "control: old record against strictcmp3" python3 diffcheck.py "$B" s3.B
} > "$R/B/fncmp.cmpkit-4bbd3a74be89.scans-86da41d3ef68.log" 2>&1

ST=kit-rerun/cmpkit-4bbd3a74be89/settled.tsv
{ hdr "scans of cmpkit 86da41d3ef68 on the settled rows $ST (Allocate +0xdc S:E and T:E, PoisonShadow +0x48c S:E)"
  run "luiscan, the 2 functions, the three images" python3 kit/luiscan.py --all --fns "$ALLOC,$POISON" $S $C $DB
  run "ambiscan, S : E" python3 kit/ambiscan.py $S $DB $ST
  run "ambiscan, T : E" python3 kit/ambiscan.py $C $DB $ST
  runto s3.S "control: the 2 functions under strictcmp3" python3 kit/strictcmp3.py cmp "$ALLOC,$POISON" S=$S T=$C E=$DB S:E,T:E
  run "control: settled rows against strictcmp3's differing targets" python3 diffcheck.py "$ST" s3.S
} > "$R/cmpkit-4bbd3a74be89/settled.scans-86da41d3ef68.log" 2>&1

LT=kit-rerun/A/kit-rerun-4bbd3a74be89/luitrace.py
LTSHA="$LT sha256 $(sha256sum < "$LT" | cut -c1-12)"
for pr in "T $C" "S $S"; do
  set -- $pr
  { hdr "lui trace of the B record, pair $1 : E ($LTSHA, the A record's own tool; 8 functions)"
    run "luitrace.py pair" python3 "$LT" pair "$2" $DB "$FB"
  } > "$R/B/luitrace-pair-$1E-86da41d3ef68.out" 2>&1
done
{ hdr "TryMemCpy, the one lui function of the B record that the A record does not compare: every word, both images"
  run "window.py" python3 window.py kit _ZN11__sanitizer9TryMemCpyEPvPKvm $C $DB
} > "$R/B/luitrace-TryMemCpy-86da41d3ef68.out" 2>&1
{ hdr "the lui trace of the B record against the A record's own trace"
  echo "## the ROW lines of B/luitrace-pair-TE-86da41d3ef68.out less TryMemCpy, against the ROW lines of $LT's record out/luitrace-pair-86da41d3ef68.out"
  grep '^ROW' "$R/B/luitrace-pair-TE-86da41d3ef68.out" | grep -v 'TryMemCpy' > rows.TE
  grep '^ROW' kit-rerun/A/kit-rerun-4bbd3a74be89/out/luitrace-pair-86da41d3ef68.out > rows.CA
  same rows.TE rows.CA
  echo "## B/luitrace-pair-SE-86da41d3ef68.out against B/luitrace-pair-TE-86da41d3ef68.out, lines not starting with '#' or '\$ ' (they name the images)"
  grep -v -e '^#' -e '^\$ ' "$R/B/luitrace-pair-SE-86da41d3ef68.out" > lt.SE; grep -v -e '^#' -e '^\$ ' "$R/B/luitrace-pair-TE-86da41d3ef68.out" > lt.TE
  same lt.SE lt.TE
} > "$R/B/luitrace-compare-86da41d3ef68.out" 2>&1

LCF="kit-rerun/A/kit-rerun-4bbd3a74be89.scans-86da41d3ef68.log kit-rerun/B/fncmp.cmpkit-4bbd3a74be89.scans-86da41d3ef68.log kit-rerun/cmpkit-4bbd3a74be89/settled.scans-86da41d3ef68.log kit-rerun/A/kit-rerun-4bbd3a74be89/out/strictcmp3-cmp-86da41d3ef68.out kit-rerun/A/kit-rerun-4bbd3a74be89/out/luiscan-86da41d3ef68.out kit-rerun/A/kit-rerun-4bbd3a74be89/out/luitrace-pair-86da41d3ef68.out kit-rerun/B/luitrace-pair-TE-86da41d3ef68.out kit-rerun/B/luitrace-pair-SE-86da41d3ef68.out"
for f in A/kit-rerun-4bbd3a74be89.scans-86da41d3ef68.log B/fncmp.cmpkit-4bbd3a74be89.scans-86da41d3ef68.log \
  cmpkit-4bbd3a74be89/settled.scans-86da41d3ef68.log B/luitrace-pair-TE-86da41d3ef68.out B/luitrace-pair-SE-86da41d3ef68.out; do
  cp "$R/$f" "kit-rerun/$f"
done
{ hdr "every lui-const in the cmpkit 86da41d3ef68 outputs of the A, B and settled records"
  echo "## strictcmp3 prints a lui target the dataflow settles as a constant as \`lui-const (dataflow)\`; luiscan counts them in its luiconst column"
  run "grep -c -F lui-const, per file" grep -c -F lui-const $LCF
  run "luiscan TOTAL lines (luiconst column)" grep -h '^TOTAL' kit-rerun/A/kit-rerun-4bbd3a74be89.scans-86da41d3ef68.log \
      kit-rerun/B/fncmp.cmpkit-4bbd3a74be89.scans-86da41d3ef68.log kit-rerun/cmpkit-4bbd3a74be89/settled.scans-86da41d3ef68.log \
      kit-rerun/A/kit-rerun-4bbd3a74be89/out/luiscan-86da41d3ef68.out
} > "$H/luiconst-search.out" 2>&1
grep -h -e '^TOTAL' -e '^IDENTICAL' -e '^DIFFERENT' "$R/A/kit-rerun-4bbd3a74be89.scans-86da41d3ef68.log" \
  "$R/B/fncmp.cmpkit-4bbd3a74be89.scans-86da41d3ef68.log" "$R/cmpkit-4bbd3a74be89/settled.scans-86da41d3ef68.log" \
  "$R/B/luitrace-compare-86da41d3ef68.out" "$R/B/luitrace-pair-TE-86da41d3ef68.out" | cut -c1-160
grep -h -e ':' "$H/luiconst-search.out" | grep -v '^#' | cut -c1-160
