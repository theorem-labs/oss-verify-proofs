#!/usr/bin/env bash
# Re-runs every measurement of RECORD.md (read-only on all inputs), then writes the committed slice commit/.
# Version of record: cmpkit 4bbd3a74be89 (strictcmp2 the one compare; closure_strict2 by name; paircl against the
# stripped grant pin; jtcheck 824905e26211; drvcmp twins).
# Earlier versions of record are kept, each in its own directory: va88c2822a0f2/, v9cbc3553c09e/, v7daa0e2a03d9/
# (each holds its own tools, outputs and run.sh).
# env.sh (not committed) sets the image paths: UCI_S / UCI_U = fuzz_uci B pin and unstripped twin, GR_S / GR_U =
# fuzz_grant B pin and twin, ID_S / ID_U = fuzz_identity B pin and twin.
set -euo pipefail
cd "$(dirname "$0")"
HERE=$(pwd)
source ./env.sh
TOOLS=$HERE/tools
P=$HERE/planted
R=__interceptor_trampoline_malloc,___interceptor_malloc,__interceptor_trampoline_free,___interceptor_free
JT=$(paste -sd, "$HERE/jtcheck-members.txt")

sha256sum "$UCI_S" "$UCI_U" "$GR_S" "$GR_U" "$ID_S" "$ID_U" > images.sha256
python3 "$TOOLS/drvcmp.py" twins "$UCI_S" "$UCI_U" "$GR_S" "$GR_U" "$ID_S" "$ID_U" > twins.out
for k in UCI_U GR_U ID_U; do echo "== $k"; python3 "$TOOLS/syms.py" "${!k}" "$R,__interceptor_malloc,__interceptor_free"; done > roots-syms.out
# planted copies of grant B, one changed word each (RECORD.md "Controls"):
#   call:     ___interceptor_malloc 0x530b0+0x130 (file 0x421e0): jal __asan::asan_malloc -> jal __sanitizer_get_allocated_begin
#   rodata:   __intscan 0x95c04+0x4c8 (file 0x850cc): addi s5,a1,1944 -> 1120, re-points `table` to `all_mask`
#   debruijn: a copy of GRANT_B_TWIN alone; one byte of the 64-byte De Bruijn ctz table at vaddr 0x10432 (file 0x432)
#             changed from 0x0e to 0x0f (settlement control)
mkdir -p "$P"
for k in call rodata; do cp "$GR_S" "$P/grantB-S-$k.elf"; cp "$GR_U" "$P/grantB-U-$k.elf"; done
cp "$GR_U" "$P/grantB-U-debruijn.elf"
chmod u+w "$P"/*.elf
for f in grantB-S-call grantB-U-call; do printf '\xef\xf0\x9d\xcd' | dd of="$P/$f.elf" bs=1 seek=$((0x421e0)) conv=notrunc status=none; done
for f in grantB-S-rodata grantB-U-rodata; do printf '\x93\x8a\x05\x46' | dd of="$P/$f.elf" bs=1 seek=$((0x850cc)) conv=notrunc status=none; done
printf '\x0f' | dd of="$P/grantB-U-debruijn.elf" bs=1 seek=$((0x432)) conv=notrunc status=none
(cd "$P" && sha256sum *.elf > planted.sha256
 for f in *.elf; do case $f in *-S-*) o=$GR_S;; *-U-debruijn.elf) o=$GR_U;; *) o=$GR_U;; esac; echo "$f: $(cmp -l "$f" "$o" | tr '\n' ' ' || true)"; done > planted.cmp)

(cd "$TOOLS" && sha256sum *.py) > "$HERE/tools.sha256"
cd "$TOOLS"
# the kit's four measurements against grant and identity
python3 strictcmp2.py cmp "$R" U="$UCI_U" G="$GR_U" I="$ID_U" U:G,U:I > "$HERE/roots.tsv" &
python3 closure_strict2.py "$UCI_U" "$GR_U" "$R" > "$HERE/closure-uci-grant.out" &
python3 closure_strict2.py "$UCI_U" "$ID_U" "$R" > "$HERE/closure-uci-identity.out" &
python3 paircl.py "$UCI_U" "$GR_S" ___interceptor_malloc 0x530b0 "$GR_U" > "$HERE/paircl-malloc-grant.out" &
python3 paircl.py "$UCI_U" "$GR_S" ___interceptor_free 0x52ee0 "$GR_U" > "$HERE/paircl-free-grant.out" &
python3 paircl.py "$UCI_U" "$GR_S" __interceptor_trampoline_malloc 0x52edc "$GR_U" > "$HERE/paircl-tmalloc-grant.out" &
python3 paircl.py "$UCI_U" "$GR_S" __interceptor_trampoline_free 0x52ed8 "$GR_U" > "$HERE/paircl-tfree-grant.out" &
python3 jtcheck.py "$UCI_U" "$GR_U" "$JT" > "$HERE/jtcheck-uci-grant.out" &
python3 jtcheck.py "$UCI_U" "$ID_U" "$JT" > "$HERE/ctl-jtcheck-uci-identity.out" &
wait
# plants: each must be caught by the kit (paircl / closure / jtcheck / strictcmp2 as appropriate)
python3 strictcmp2.py cmp "$R" U="$UCI_U" P="$P/grantB-U-call.elf" U:P > "$HERE/ctl-planted-call-roots.tsv" &
python3 closure_strict2.py "$UCI_U" "$P/grantB-U-call.elf" ___interceptor_malloc > "$HERE/ctl-planted-call-closure.out" &
python3 jtcheck.py "$UCI_U" "$P/grantB-U-call.elf" ___interceptor_malloc > "$HERE/ctl-planted-call-jtcheck.out" &
python3 paircl.py "$UCI_U" "$P/grantB-S-call.elf" ___interceptor_malloc 0x530b0 "$P/grantB-U-call.elf" > "$HERE/ctl-planted-call-paircl.out" &
python3 strictcmp2.py cmp __intscan U="$UCI_U" P="$P/grantB-U-rodata.elf" U:P > "$HERE/ctl-planted-rodata-intscan.tsv" &
python3 jtcheck.py "$UCI_U" "$P/grantB-U-rodata.elf" __intscan > "$HERE/ctl-planted-rodata-jtcheck.out" &
python3 closure_strict2.py "$UCI_U" "$P/grantB-U-rodata.elf" ___interceptor_malloc > "$HERE/ctl-planted-rodata-closure.out" &
python3 paircl.py "$UCI_U" "$P/grantB-S-rodata.elf" ___interceptor_malloc 0x530b0 "$P/grantB-U-rodata.elf" > "$HERE/ctl-planted-rodata-paircl.out" &
wait
# the acceptance measurement: one row per kit `other` member, with the full target list from tcmp
python3 otherrows.py "$UCI_U" "$HERE/closure-uci-grant.out" "$HERE/paircl-malloc-grant.out" ___interceptor_malloc > "$HERE/other-rows.txt"
python3 settle.py "$UCI_U" "$GR_U" "$(cat "$HERE/other-rows.txt")" > "$HERE/settle.tsv"
python3 escape.py "$UCI_U" "$GR_U" "$HERE/settle.tsv"
python3 dupcheck.py "$UCI_U" "$GR_U" "$R" "$(cat "$HERE/other-rows.txt"),$JT,__intscan" > "$HERE/dupcheck.tsv"
# settlement control: planted vs untouched De Bruijn copy on Allocate+0xdc
RA=_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb
python3 settle.py "$UCI_U" "$P/grantB-U-debruijn.elf" "$RA" > "$HERE/ctl-settle-debruijn-planted.tsv"
python3 settle.py "$UCI_U" "$GR_U" "$RA" > "$HERE/ctl-settle-debruijn-untouched.tsv"
# ACCEPTANCES.tsv: kit verdict first, then settle rows (unchanged)
python3 mkaccept.py "$HERE/ACCEPTANCES.tsv" 'fuzz_uci B' "$HERE/closure-uci-grant.out" "$HERE/paircl-malloc-grant.out" "$HERE/settle.tsv" "$HERE/dupcheck.tsv" "$HERE/ctl-settle-debruijn-planted.tsv" "$HERE/ctl-settle-debruijn-untouched.tsv" 4bbd3a74be89
rm -rf "$TOOLS/__pycache__"
# the committed slice: raw outputs with every image path rewritten to its token (scrub_out.py refuses any leftover)
cd "$HERE"
python3 tools/scrub_out.py . --tooldir tools --tooldir v7daa0e2a03d9/tools --tooldir v9cbc3553c09e/tools --tooldir va88c2822a0f2/tools \
  --img UCI_B_PIN "$UCI_S" 'fuzz_uci.asan-ubsan, the pinned image: index/binaries.tsv:7521' \
  --img UCI_B_TWIN "$UCI_U" 'fuzz_uci.asan-ubsan, the unstripped twin of UCI_B_PIN (PT_LOAD equal: twins.out)' \
  --img GRANT_B_PIN "$GR_S" 'fuzz_grant.asan-ubsan, the pinned image: index/binaries.tsv:5591' \
  --img GRANT_B_TWIN "$GR_U" 'fuzz_grant.asan-ubsan, the unstripped twin of GRANT_B_PIN (PT_LOAD equal: twins.out)' \
  --img IDENT_B_PIN "$ID_S" 'fuzz_identity.asan-ubsan, the pinned image: index/binaries.tsv:5595' \
  --img IDENT_B_TWIN "$ID_U" 'fuzz_identity.asan-ubsan, the unstripped twin of IDENT_B_PIN (PT_LOAD equal: twins.out)' \
  --img GRANT_B_PIN_PLANTED_CALL "$P/grantB-S-call.elf" 'copy of GRANT_B_PIN with one call re-pointed at file offset 0x421e0 (planted/planted.cmp)' \
  --img GRANT_B_TWIN_PLANTED_CALL "$P/grantB-U-call.elf" 'copy of GRANT_B_TWIN with one call re-pointed at file offset 0x421e0 (planted/planted.cmp)' \
  --img GRANT_B_PIN_PLANTED_RODATA "$P/grantB-S-rodata.elf" 'copy of GRANT_B_PIN with one .rodata address re-pointed at file offset 0x850cc (planted/planted.cmp)' \
  --img GRANT_B_TWIN_PLANTED_RODATA "$P/grantB-U-rodata.elf" 'copy of GRANT_B_TWIN with one .rodata address re-pointed at file offset 0x850cc (planted/planted.cmp)' \
  --img GRANT_B_TWIN_PLANTED_DEBRUIJN "$P/grantB-U-debruijn.elf" 'copy of GRANT_B_TWIN with one byte of the De Bruijn ctz table at file offset 0x432 changed from 0x0e to 0x0f (planted/planted.cmp)'
echo done
