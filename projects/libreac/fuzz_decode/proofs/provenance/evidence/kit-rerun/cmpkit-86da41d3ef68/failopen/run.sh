#!/bin/sh
# run.sh -- the KNOWN FAIL-OPEN shapes (a)-(h) of cmpkit 86da41d3ef68 on every function the kit-rerun records compare,
# by hand pass (failopen.py) over GNU objdump listings, with a planted control per shape (plant.py).
#   A record, 7 pairs, donor twin C : decode A twin                 -> failopen-CA.out
#   B record, 8 functions, donor twin T : decode B twin E           -> failopen-TE.out
#   B record, 8 functions, symtwin S : decode B twin E              -> failopen-SE.out
#   (the settled rows lie in Allocate T:E / S:E and PoisonShadow S:E, inside these two runs)
#   the planted controls, side 1 C, side 2 decode A, in memset      -> controls.out
# What the records conclude from it is in kit-rerun/FAILOPEN-SHAPES.md.
# Runs INSIDE the toolchain image ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c8
# 1a599ffcb20616576a9c668abd8b0a7b (riscv64-alpine-linux-musl-objdump, python3; nothing else is needed):
#   docker run --rm --network none -v <IMG>:/img:ro -v <this dir>:/w -w /w <image> env IMG=/img sh run.sh
# IMG holds the four unstripped twins: cgif_file_fuzzer.asan-ubsan, cgif_file_fuzzer.asan-ubsan.symtwin,
# fuzz_decode.asan, fuzz_decode.asan-ubsan. Each sha256 is checked before use. The outputs name only img/ paths.
set -eu
: "${IMG:?}"
H=$(cd "$(dirname "$0")" && pwd)
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
export PYTHONDONTWRITEBYTECODE=1
OD=riscv64-alpine-linux-musl-objdump
C=cgif_file_fuzzer.asan-ubsan; S=cgif_file_fuzzer.asan-ubsan.symtwin; DA=fuzz_decode.asan; DB=fuzz_decode.asan-ubsan
for p in "$C ce511d541cdabbe3c8df3f672dc517e8b5a7edd37b280a7483043b438de0adf7" \
         "$S 3f110c1db582567aa8b745a910f641e51b80b8aa84dbd5bc5478c823ca0783f4" \
         "$DA 4cb0a852e8262acb5ed0fa075a6bee7b1a25192189b168e777c760a4bfd65ae2" \
         "$DB 6744989bb2e66ffa4fb48e042ecedff4a3b4ba2301f43c1217e76fd1b090d0a4"; do
  set -- $p
  [ "$(sha256sum < "$IMG/$1" | cut -c1-64)" = "$2" ] || { echo "run.sh: IMG/$1 is not sha256 $2" >&2; exit 1; }
done
ln -s "$(cd "$IMG" && pwd)" "$T/img"
cp "$H/failopen.py" "$H/plant.py" "$T/"
cd "$T"
mkdir lst ctl
ALLOC=_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb
FA="$ALLOC _ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm _ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEEE6RefillEPNS7_8PerClassEPS6_m _ZN6__asan12PoisonShadowEmmh _ZN11__sanitizer13internal_mmapEPvmiiiy _ZN11__sanitizer13StackDepotPutENS_10StackTraceE memset"
FB="$FA _ZN11__sanitizer9TryMemCpyEPvPKvm"
VERS="$($OD --version | sed -n 1p); python $(python3 -c 'import sys; print(sys.version.split()[0])')"
SELF="failopen.py $(sha256sum < failopen.py | cut -c1-12), plant.py $(sha256sum < plant.py | cut -c1-12), run.sh $(sha256sum < "$H/run.sh" | cut -c1-12)"
hdr() {
  echo "# $1"
  echo "# kit of record: cmpkit 86da41d3ef68 (its KNOWN FAIL-OPENS are what this checks; the kit is not run here)"
  echo "# hand pass: $SELF; $VERS; listings: $OD -d -M no-aliases --disassemble=FN, and the same bytes as -b binary"
}
listing() {  # listing DIR ELF FN...: the ELF listing of each FN and the plain-binary listing of its bytes
  d=$1; e=$2; shift 2
  b=$(basename "$e")
  : > "$d/$b.lst"; : > "$d/$b.raw"
  for f in "$@"; do
    $OD -d -M no-aliases --disassemble="$f" "$e" >> "$d/$b.lst"
    a=$(python3 failopen.py bytes "$e" "$f" "$d/$b.bin")
    $OD -D -b binary -m riscv:rv64 -M no-aliases --adjust-vma="$a" "$d/$b.bin" >> "$d/$b.raw"
  done
}
for i in $C $S $DA $DB; do listing lst img/$i $FB; done
side() { echo "$1=img/$2=lst/$2.lst=lst/$2.raw"; }
{ hdr "A record: the 7 pairs, donor twin C : decode A twin"
  python3 failopen.py pair "$(echo $FA | tr ' ' ,)" "$(side C $C)" "$(side A $DA)"
} > "$H/failopen-CA.out" 2>&1
{ hdr "B record: the 8 functions, donor twin T : decode B twin E (settled rows: Allocate +0xdc)"
  python3 failopen.py pair "$(echo $FB | tr ' ' ,)" "$(side T $C)" "$(side E $DB)"
} > "$H/failopen-TE.out" 2>&1
{ hdr "B record: the 8 functions, symtwin S : decode B twin E (settled rows: Allocate +0xdc, PoisonShadow +0x48c)"
  python3 failopen.py pair "$(echo $FB | tr ' ' ,)" "$(side S $S)" "$(side E $DB)"
} > "$H/failopen-SE.out" 2>&1
{ hdr "planted controls: one per shape, side 1 a copy of C, side 2 a copy of decode A, planted at memset+0"
  echo "\$ python3 plant.py img/$C img/$DA memset ctl"
  python3 plant.py img/$C img/$DA memset ctl | tee ctl/PLANTS
  TAB=$(printf '\t')
  for p in $(cut -f2,3 ctl/PLANTS | grep -v '^#' | tr '\t' _); do
    listing ctl ctl/$p.1 memset
    listing ctl ctl/$p.2 memset
    python3 failopen.py pair memset "1=ctl/$p.1=ctl/$p.1.lst=ctl/$p.1.raw" "2=ctl/$p.2=ctl/$p.2.lst=ctl/$p.2.raw" \
      > ctl/$p.out 2>&1
    off=$(grep "^PLANT$TAB${p%_*}$TAB${p##*_}$TAB" ctl/PLANTS | cut -f4)
    n=$(( $(printf '%d' "${off#+}") / 4 + 2 ))
    echo "## $p: the planted words as objdump lists them in the ELF (side 1, then side 2), then the planted site"
    for s in 1 2; do
      grep -E '^ +[0-9a-f]+:' ctl/$p.$s.lst | sed -n "1,${n}p"
      if grep -E '^ +[0-9a-f]+:' ctl/$p.$s.lst | sed -n "1,${n}p" | grep -q '\.insn'; then
        echo "  (side $s, the same bytes in the plain-binary listing, which decodes the .insn parcels:)"
        grep -E '^ +[0-9a-f]+:' ctl/$p.$s.raw | sed -n "1,${n}p"
      fi
    done
    grep -E '^# [12]: ' ctl/$p.out
    grep "^SITE${TAB}memset$TAB$off$TAB" ctl/$p.out
  done
  echo "\$ python3 plant.py check ctl/PLANTS ctl"
  python3 plant.py check ctl/PLANTS ctl || true
} > "$H/controls.out" 2>&1
grep -h -e '^GRAND' "$H/failopen-CA.out" "$H/failopen-TE.out" "$H/failopen-SE.out"
grep -h -e '^controls PASS' -e 'FAIL$' "$H/controls.out"
