#!/bin/sh
# luicomb-run.sh -- the KNOWN FAIL-OPEN check of cmpkit 86da41d3ef68: two lui values combined by add / sub / sh*add
# into one load / store / jalr / AMO base are not compared as an address by strictcmp3 rule 8. luicomb.py finds that
# shape in every function the three records compare; plantlui.py plants it, as the positive control.
#   the 8 compared functions, in the 4 images of the records -> cmpkit-86da41d3ef68/luicomb-86da41d3ef68.out
#   the planted control                                      -> cmpkit-86da41d3ef68/luicomb-control-86da41d3ef68.out
# What the records conclude from it is in kit-rerun/LUI-COMBINED.md.
# usage (KIT and IMG may be relative; the outputs then name only kit/ and img/ paths):
#   KIT=<dir holding exactly the nine kit files> IMG=<dir holding unstripped/> sh luicomb-run.sh
# IMG/unstripped: cgif_file_fuzzer.asan-ubsan, cgif_file_fuzzer.asan-ubsan.symtwin, fuzz_decode.asan,
# fuzz_decode.asan-ubsan. Needs pyelftools and capstone on PYTHONPATH.
set -eu
: "${KIT:?}" "${IMG:?}"
H=$(cd "$(dirname "$0")" && pwd)
R=$(dirname "$H")
KITA=$(cd "$KIT" && pwd); IMGA=$(cd "$IMG" && pwd)
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
export PYTHONDONTWRITEBYTECODE=1
ln -s "$KITA" "$T/kit"; ln -s "$IMGA" "$T/img"
cp "$H/luicomb.py" "$H/plantlui.py" "$T/"
cd "$T"
VERS=$(python3 -c 'import sys, elftools, capstone; print("python %s, pyelftools %s, capstone %s" % (sys.version.split()[0], elftools.__version__, capstone.__version__))')
KITID=$( (cd kit && sha256sum $(ls) ) | sha256sum | cut -c1-12)
SELF="luicomb.py $(sha256sum < luicomb.py | cut -c1-12), plantlui.py $(sha256sum < plantlui.py | cut -c1-12), luicomb-run.sh $(sha256sum < "$H/luicomb-run.sh" | cut -c1-12)"
U=img/unstripped
ALLOC=_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb
FB="$ALLOC,_ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm,_ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEEE6RefillEPNS7_8PerClassEPS6_m,_ZN6__asan12PoisonShadowEmmh,_ZN11__sanitizer13internal_mmapEPvmiiiy,_ZN11__sanitizer13StackDepotPutENS_10StackTraceE,memset,_ZN11__sanitizer9TryMemCpyEPvPKvm"
hdr() {
  echo "# $1"
  echo "# cmpkit $KITID; $VERS; $SELF"
}
{ hdr "lui + lui -> one base: the 8 functions the records compare, in all 4 images (donor twin, symtwin, decode A twin, decode B twin)"
  python3 luicomb.py kit "$FB" $U/cgif_file_fuzzer.asan-ubsan $U/cgif_file_fuzzer.asan-ubsan.symtwin \
    $U/fuzz_decode.asan $U/fuzz_decode.asan-ubsan
} > "$H/luicomb-86da41d3ef68.out" 2>&1
{ hdr "positive control: the shape planted in a copy, and the same function in the image of record"
  echo "\$ python3 plantlui.py kit $U/fuzz_decode.asan memset control.elf"
  python3 plantlui.py kit $U/fuzz_decode.asan memset control.elf
  echo "\$ python3 luicomb.py kit memset control.elf        (the planted copy: the site must be reported, with its address)"
  python3 luicomb.py kit memset control.elf
  echo "\$ python3 luicomb.py kit memset $U/fuzz_decode.asan   (the image of record: no such site)"
  python3 luicomb.py kit memset $U/fuzz_decode.asan
} > "$H/luicomb-control-86da41d3ef68.out" 2>&1
grep -h -e '^TOTAL' -e '^SITE' "$H/luicomb-86da41d3ef68.out" | awk '{print}' | sed -n '1,4p;$p'
grep -c '^SITE' "$H/luicomb-86da41d3ef68.out" | sed 's/^/SITE rows: /'
