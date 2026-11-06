#!/bin/sh
# run.sh -- re-run of the image-B alloc-reloc same-code record on the comparison kit cmpkit 4bbd3a74be89
# (tools/cmpkit/4bbd3a74be89 at the tools commit 3c3e62ee2786; kit id = first 12 hex of sha256(SHA256SUMS)).
# Paths below are relative to provenance/evidence/kit-rerun/, the directory above this one.
#   provenance/alloc-reloc/B/fncmp.tsv (bytecmp 8ed351b56fbe), fncmp-d7ef.tsv, fncmp-475f.tsv, fncmp-7daa.tsv
#   (provenance/alloc-reloc/B/versions.txt:18-33; OLDB below, in the series tree, not in the released tree):
#     the 8 (cgif donor function, decode B function) pairs          -> B/fncmp.cmpkit-4bbd3a74be89.log
#   every kit difference with its measurement                       -> cmpkit-4bbd3a74be89/settled.tsv
#   pin rebuild and twin proofs                                     -> cmpkit-4bbd3a74be89/twins.log
# The image-A records (provenance/alloc-reloc/A/fpaudit) are re-run in A/kit-rerun-4bbd3a74be89/.
# Two donor twins: S, the input the record names (cgif_file_fuzzer.asan-ubsan.symtwin: provenance/alloc-reloc/B/tools/
# symtwin.py of the donor pin and the port_addr_check cache 1c29845fe6058de6.978e0a064c5a4c6e.v4.json; a recovered
# symtab, no STT_FILE or STT_TLS symbol), and T, the unstripped twin of the donor build (the twin
# A/kit-rerun-4bbd3a74be89 uses), as a cross-check.
# usage (from a directory where KIT and IMG are relative paths, so the records name no host path):
#   KIT=<dir holding exactly the seven kit files> IMG=<dir holding bin/ and unstripped/> [OLDB=<dir of the old tables>] sh run.sh
# IMG/unstripped: cgif_file_fuzzer.asan-ubsan.symtwin, cgif_file_fuzzer.asan-ubsan (donor twin), fuzz_decode.asan-ubsan
# (libreac unstripped twin); IMG/bin: fuzz_decode.asan-ubsan (libreac pin). IMG/bin/cgif_file_fuzzer.asan-ubsan (the
# donor pin) is written here by pinback.py. Needs pyelftools and capstone on PYTHONPATH.
set -eu
: "${KIT:?}" "${IMG:?}"
H=$(cd "$(dirname "$0")" && pwd)
R=$(dirname "$H")
OLDB=${OLDB:-$R/../../alloc-reloc/B}
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
export PYTHONDONTWRITEBYTECODE=1
PY=python3
FILES='bytecmp-1480ca2faea0.py closure_strict2.py drvcmp.py jtcheck.py paircl.py repin_check-4c05cadaeba3.py strictcmp2.py'
[ "$(ls "$KIT" | tr '\n' ' ')" = "$FILES " ] || { echo "run.sh: $KIT does not hold exactly the seven kit files" >&2; exit 1; }
(cd "$KIT" && sha256sum $FILES) > "$T/sums"
KITID=$(sha256sum < "$T/sums" | cut -c1-12)
[ "$KITID" = 4bbd3a74be89 ] || { echo "run.sh: kit id $KITID, want 4bbd3a74be89" >&2; exit 1; }
VERS=$($PY -c 'import sys, elftools, capstone; print("python %s, pyelftools %s, capstone %s" % (sys.version.split()[0], elftools.__version__, capstone.__version__))')
SELF="run.sh $(sha256sum < "$0" | cut -c1-12), kitsum.py $(sha256sum < "$H/kitsum.py" | cut -c1-12), settle.py $(sha256sum < "$H/settle.py" | cut -c1-12), pinback.py $(sha256sum < "$H/pinback.py" | cut -c1-12)"

U=$IMG/unstripped; B=$IMG/bin
SYMTWIN=$U/cgif_file_fuzzer.asan-ubsan.symtwin
TWIN=$U/cgif_file_fuzzer.asan-ubsan
$PY "$H/pinback.py" "$SYMTWIN" "$B/cgif_file_fuzzer.asan-ubsan" > "$T/pinback"
[ "$(sha256sum < "$B/cgif_file_fuzzer.asan-ubsan" | cut -c1-64)" = 1c29845fe6058de6e1dbf3f6ec6abd566ea612d76b65ea5435d7ff77c63e08ef ] \
  || { echo "run.sh: rebuilt pin is not the donor pin of record 1c29845fe605" >&2; exit 1; }
$PY "$KIT/drvcmp.py" twins "$B/cgif_file_fuzzer.asan-ubsan" "$SYMTWIN" "$B/cgif_file_fuzzer.asan-ubsan" "$TWIN" \
  "$B/fuzz_decode.asan-ubsan" "$U/fuzz_decode.asan-ubsan" > "$T/twins"
{
  echo "# cmpkit $KITID: $(sed 's/^\(............\)[0-9a-f]*  /\1 /' "$T/sums" | tr '\n' ';' | sed 's/;$//;s/;/, /g')"
  echo "# $VERS; $SELF"
  echo "# python3 pinback.py $SYMTWIN $B/cgif_file_fuzzer.asan-ubsan"
  cat "$T/pinback"
  echo "# python3 \$KIT/drvcmp.py twins (KIT=$KIT) PIN TWIN ...: the donor pin rebuilt above with both donor twins, and the decode B pin"
  cat "$T/twins"
} > "$H/twins.log"

FB='_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb,_ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm,_ZN6__asan12PoisonShadowEmmh,_ZN11__sanitizer13internal_mmapEPvmiiiy,_ZN11__sanitizer9TryMemCpyEPvPKvm,_ZN11__sanitizer13StackDepotPutENS_10StackTraceE,memset,_ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEEE6RefillEPNS7_8PerClassEPS6_m'
$PY "$KIT/strictcmp2.py" cmp "$FB" S="$SYMTWIN" E="$U/fuzz_decode.asan-ubsan" S:E > "$T/S.tsv"
$PY "$KIT/strictcmp2.py" cmp "$FB" T="$TWIN" E="$U/fuzz_decode.asan-ubsan" T:E > "$T/T.tsv"
$PY "$H/settle.py" "$KIT" "$T/S.tsv" > "$T/S.settled"
$PY "$H/settle.py" "$KIT" "$T/T.tsv" > "$T/T.settled"
{ cat "$T/S.settled"; sed 1d "$T/T.settled"; } > "$H/settled.tsv"
OLD="8ed351b56fbe=$OLDB/fncmp.tsv:cgif_addr:decode_addr:verdict d7efcb08d3a4=$OLDB/fncmp-d7ef.tsv:cgif_addr:decode_addr:verdict 475ff6314d3c=$OLDB/fncmp-475f.tsv:cgif_addr:decode_addr:verdict 7daa0e2a03d9=$OLDB/fncmp-7daa.tsv:cgif_addr:decode_addr:verdict"
$PY "$H/kitsum.py" "$T/S.tsv" "$H/settled.tsv" $OLD > "$T/S.sum"
$PY "$H/kitsum.py" "$T/T.tsv" "$H/settled.tsv" $OLD > "$T/T.sum"
{
  echo "# re-run of provenance/alloc-reloc/B/ fncmp.tsv (bytecmp 8ed351b56fbe), fncmp-d7ef.tsv (d7efcb08d3a4), fncmp-475f.tsv (475ff6314d3c) and fncmp-7daa.tsv (7daa0e2a03d9) on cmpkit 4bbd3a74be89: the same 8 donor / decode B functions"
  echo "# cmpkit $KITID (tools/cmpkit/4bbd3a74be89 at the tools commit 3c3e62ee2786): strictcmp2.py 16982e3ef42b (the one compare), drvcmp.py 4d70e90bc1fa, repin_check-4c05cadaeba3.py 4c05cadaeba3, bytecmp-1480ca2faea0.py 1480ca2faea0; $VERS"
  echo "# twins and the donor pin rebuild: cmpkit-4bbd3a74be89/twins.log; each kit difference with its measurement: cmpkit-4bbd3a74be89/settled.tsv"
  echo "# commands (provenance/evidence/kit-rerun/cmpkit-4bbd3a74be89/run.sh; $SELF), the 8 names of provenance/alloc-reloc/B/tools/fncmp.py:"
  echo "#   python3 \$KIT/strictcmp2.py cmp <names> S=$SYMTWIN E=$U/fuzz_decode.asan-ubsan S:E   (the record's donor input)"
  echo "#   python3 \$KIT/strictcmp2.py cmp <names> T=$TWIN E=$U/fuzz_decode.asan-ubsan T:E   (cross-check: the donor's unstripped twin)"
  echo "## S:E strictcmp2.py cmp output"
  cat "$T/S.tsv"
  echo "## S:E kit verdict, settled verdict and old verdicts per pair (kitsum.py)"
  cat "$T/S.sum"
  echo "## T:E strictcmp2.py cmp output"
  cat "$T/T.tsv"
  echo "## T:E kit verdict, settled verdict and old verdicts per pair (kitsum.py)"
  cat "$T/T.sum"
} > "$R/B/fncmp.cmpkit-4bbd3a74be89.log"
tail -n 1 "$T/S.sum" "$T/T.sum"
