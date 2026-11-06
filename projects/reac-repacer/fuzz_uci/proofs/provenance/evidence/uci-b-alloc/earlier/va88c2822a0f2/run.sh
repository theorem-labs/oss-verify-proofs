#!/usr/bin/env bash
# Re-runs every measurement of RECORD.md (read-only on all inputs), then writes the committed slice commit/.
#   ./run.sh                                    version of record: tools/ (bytecmp 1480ca2faea0 + repin_check e5487165abb8,
#                                               with the fail-closed target rule also in jtcheck.py and paircl.py)
#   ./run.sh v9cbc3553c09e/tools v9cbc3553c09e   the previous run (repin_check 9cbc3553c09e; jtcheck / paircl unchanged)
#   ./run.sh v7daa0e2a03d9/tools v7daa0e2a03d9   the first run (bytecmp 7daa0e2a03d9)
# env.sh (not committed) sets the image paths: UCI_S / UCI_U = fuzz_uci B pin and unstripped twin, GR_S / GR_U =
# fuzz_grant B pin and twin, ID_S / ID_U = fuzz_identity B pin and twin.
set -euo pipefail
cd "$(dirname "$0")"
HERE=$(pwd)
source ./env.sh
TOOLS=$(cd "${1:-tools}" && pwd)
OUT=$(cd "${2:-.}" && pwd)
P=$HERE/planted
R=__interceptor_trampoline_malloc,___interceptor_malloc,__interceptor_trampoline_free,___interceptor_free
JT=$(paste -sd, "$OUT/jtcheck-members.txt")

# shared by all versions: image hashes, twin check, root symbols, planted copies
sha256sum "$UCI_S" "$UCI_U" "$GR_S" "$GR_U" "$ID_S" "$ID_U" > images.sha256
python3 "$TOOLS/drvcmp.py" twins "$UCI_S" "$UCI_U" "$GR_S" "$GR_U" "$ID_S" "$ID_U" > twins.out
for k in UCI_U GR_U ID_U; do echo "== $k"; python3 "$TOOLS/syms.py" "${!k}" "$R,__interceptor_malloc,__interceptor_free"; done > roots-syms.out
# planted copies of grant B, one changed word each (offsets and words: RECORD.md, "Controls"):
#   deep:   __asan::Allocator::Allocate 0x31bc8+0x38 (file 0x20c00): addi s1,a5,0 -> addi s1,a5,1
#   root:   ___interceptor_malloc 0x530b0+0x28 (file 0x420d8): addi s2,ra,0 -> addi s2,ra,1
#   call:   ___interceptor_malloc 0x530b0+0x130 (file 0x421e0): jal __asan::asan_malloc (0x31b6c) ->
#           jal __sanitizer_get_allocated_begin (0x32eb8), a different named function of the same size (92 bytes)
#   rodata: __intscan 0x95c04+0x4c8 (file 0x850cc): addi s5,a1,1944 -> 1120, which re-points the address of `table`
#           (0x22860, 257 bytes) to `all_mask` (0x22528, 8 bytes); both start with the same 8 bytes ff..ff
mkdir -p "$P"
for k in deep root call rodata; do cp "$GR_S" "$P/grantB-S-$k.elf"; cp "$GR_U" "$P/grantB-U-$k.elf"; done
chmod u+w "$P"/*.elf
for f in grantB-S-deep grantB-U-deep; do printf '\x93\x84\x17\x00' | dd of="$P/$f.elf" bs=1 seek=$((0x20c00)) conv=notrunc status=none; done
for f in grantB-S-root grantB-U-root; do printf '\x13\x89\x10\x00' | dd of="$P/$f.elf" bs=1 seek=$((0x420d8)) conv=notrunc status=none; done
for f in grantB-S-call grantB-U-call; do printf '\xef\xf0\x9d\xcd' | dd of="$P/$f.elf" bs=1 seek=$((0x421e0)) conv=notrunc status=none; done
for f in grantB-S-rodata grantB-U-rodata; do printf '\x93\x8a\x05\x46' | dd of="$P/$f.elf" bs=1 seek=$((0x850cc)) conv=notrunc status=none; done
(cd "$P" && sha256sum *.elf > planted.sha256
 for f in *.elf; do case $f in *-S-*) o=$GR_S;; *) o=$GR_U;; esac; echo "$f: $(cmp -l "$f" "$o" | tr '\n' ' ' || true)"; done > planted.cmp)

(cd "$TOOLS" && sha256sum *.py) > "$OUT/tools.sha256"
cd "$TOOLS"
python3 drvcmp.py cmp "$R" U="$UCI_U" G="$GR_U" I="$ID_U" U:G,U:I > "$OUT/roots.tsv" &
python3 closure.py "$UCI_U" "$GR_U" "$R" > "$OUT/closure-uci-grant.out" &
python3 closure.py "$UCI_U" "$ID_U" "$R" > "$OUT/closure-uci-identity.out" &
python3 paircl.py "$UCI_U" "$GR_S" ___interceptor_malloc 0x530b0 "$GR_U" > "$OUT/paircl-malloc-grant.out" &
python3 paircl.py "$UCI_U" "$GR_S" ___interceptor_free 0x52ee0 "$GR_U" > "$OUT/paircl-free-grant.out" &
python3 paircl.py "$UCI_U" "$GR_S" __interceptor_trampoline_malloc 0x52edc "$GR_U" > "$OUT/paircl-tmalloc-grant.out" &
python3 paircl.py "$UCI_U" "$GR_S" __interceptor_trampoline_free 0x52ed8 "$GR_U" > "$OUT/paircl-tfree-grant.out" &
wait
python3 pairtable.py "$UCI_U" "$GR_S" "$GR_U" ___interceptor_malloc 0x530b0 "$OUT/pairs-malloc-grant.tsv" > "$OUT/pairtable-malloc-grant.out" &
python3 pairtable.py "$UCI_U" "$GR_S" "$GR_U" ___interceptor_free 0x52ee0 "$OUT/pairs-free-grant.tsv" > "$OUT/pairtable-free-grant.out" &
python3 pairtable.py "$UCI_U" "$GR_S" "$GR_U" __interceptor_trampoline_malloc 0x52edc "$OUT/pairs-tmalloc-grant.tsv" > "$OUT/pairtable-tmalloc-grant.out" &
python3 pairtable.py "$UCI_U" "$GR_S" "$GR_U" __interceptor_trampoline_free 0x52ed8 "$OUT/pairs-tfree-grant.tsv" > "$OUT/pairtable-tfree-grant.out" &
python3 jtcheck.py "$UCI_U" "$GR_U" "$JT" > "$OUT/jtcheck-uci-grant.out" &
python3 cietable.py "$UCI_U" "$GR_U" "$ID_U" > "$OUT/cietable.out" &
wait
# controls
python3 pairtable.py "$UCI_U" "$ID_S" "$ID_U" ___interceptor_malloc 0x52de8 "$OUT/ctl-pairs-malloc-identity.tsv" > "$OUT/ctl-pairtable-malloc-identity.out" &
python3 pairtable.py "$UCI_U" "$ID_S" "$ID_U" ___interceptor_free 0x52c18 "$OUT/ctl-pairs-free-identity.tsv" > "$OUT/ctl-pairtable-free-identity.out" &
python3 jtcheck.py "$UCI_U" "$ID_U" "$JT" > "$OUT/ctl-jtcheck-uci-identity.out" &
python3 closure.py "$UCI_U" "$P/grantB-U-deep.elf" ___interceptor_malloc > "$OUT/ctl-planted-deep-closure.out" &
python3 pairtable.py "$UCI_U" "$P/grantB-S-deep.elf" "$P/grantB-U-deep.elf" ___interceptor_malloc 0x530b0 "$OUT/ctl-planted-deep-pairs.tsv" > "$OUT/ctl-planted-deep-pairtable.out" &
python3 drvcmp.py cmp "$R" U="$UCI_U" P="$P/grantB-U-root.elf" U:P > "$OUT/ctl-planted-root-roots.tsv" &
python3 pairtable.py "$UCI_U" "$P/grantB-S-root.elf" "$P/grantB-U-root.elf" ___interceptor_malloc 0x530b0 "$OUT/ctl-planted-root-pairs.tsv" > "$OUT/ctl-planted-root-pairtable.out" &
wait
python3 drvcmp.py cmp "$R" U="$UCI_U" P="$P/grantB-U-call.elf" U:P > "$OUT/ctl-planted-call-roots.tsv" &
python3 closure.py "$UCI_U" "$P/grantB-U-call.elf" ___interceptor_malloc > "$OUT/ctl-planted-call-closure.out" &
python3 jtcheck.py "$UCI_U" "$P/grantB-U-call.elf" ___interceptor_malloc > "$OUT/ctl-planted-call-jtcheck.out" &
python3 pairtable.py "$UCI_U" "$P/grantB-S-call.elf" "$P/grantB-U-call.elf" ___interceptor_malloc 0x530b0 "$OUT/ctl-planted-call-pairs.tsv" > "$OUT/ctl-planted-call-pairtable.out" &
python3 drvcmp.py cmp __intscan U="$UCI_U" P="$P/grantB-U-rodata.elf" U:P > "$OUT/ctl-planted-rodata-intscan.tsv" &
python3 jtcheck.py "$UCI_U" "$P/grantB-U-rodata.elf" __intscan > "$OUT/ctl-planted-rodata-jtcheck.out" &
python3 closure.py "$UCI_U" "$P/grantB-U-rodata.elf" ___interceptor_malloc > "$OUT/ctl-planted-rodata-closure.out" &
python3 pairtable.py "$UCI_U" "$P/grantB-S-rodata.elf" "$P/grantB-U-rodata.elf" ___interceptor_malloc 0x530b0 "$OUT/ctl-planted-rodata-pairs.tsv" > "$OUT/ctl-planted-rodata-pairtable.out" &
wait
rm -rf "$TOOLS/__pycache__"
# the committed slice: raw outputs with every image path rewritten to its token (scrub_out.py refuses any leftover)
cd "$HERE"
python3 tools/scrub_out.py . --tooldir tools --tooldir v9cbc3553c09e/tools --tooldir v7daa0e2a03d9/tools \
  --img UCI_B_PIN "$UCI_S" 'fuzz_uci.asan-ubsan, the pinned image: index/binaries.tsv:7521' \
  --img UCI_B_TWIN "$UCI_U" 'fuzz_uci.asan-ubsan, the unstripped twin of UCI_B_PIN (PT_LOAD equal: twins.out)' \
  --img GRANT_B_PIN "$GR_S" 'fuzz_grant.asan-ubsan, the pinned image: index/binaries.tsv:5591' \
  --img GRANT_B_TWIN "$GR_U" 'fuzz_grant.asan-ubsan, the unstripped twin of GRANT_B_PIN (PT_LOAD equal: twins.out)' \
  --img IDENT_B_PIN "$ID_S" 'fuzz_identity.asan-ubsan, the pinned image: index/binaries.tsv:5595' \
  --img IDENT_B_TWIN "$ID_U" 'fuzz_identity.asan-ubsan, the unstripped twin of IDENT_B_PIN (PT_LOAD equal: twins.out)' \
  --img GRANT_B_PIN_PLANTED_DEEP "$P/grantB-S-deep.elf" 'copy of GRANT_B_PIN with one word changed at file offset 0x20c00 (planted/planted.cmp)' \
  --img GRANT_B_TWIN_PLANTED_DEEP "$P/grantB-U-deep.elf" 'copy of GRANT_B_TWIN with one word changed at file offset 0x20c00 (planted/planted.cmp)' \
  --img GRANT_B_PIN_PLANTED_ROOT "$P/grantB-S-root.elf" 'copy of GRANT_B_PIN with one word changed at file offset 0x420d8 (planted/planted.cmp)' \
  --img GRANT_B_TWIN_PLANTED_ROOT "$P/grantB-U-root.elf" 'copy of GRANT_B_TWIN with one word changed at file offset 0x420d8 (planted/planted.cmp)' \
  --img GRANT_B_PIN_PLANTED_CALL "$P/grantB-S-call.elf" 'copy of GRANT_B_PIN with one call re-pointed at file offset 0x421e0 (planted/planted.cmp)' \
  --img GRANT_B_TWIN_PLANTED_CALL "$P/grantB-U-call.elf" 'copy of GRANT_B_TWIN with one call re-pointed at file offset 0x421e0 (planted/planted.cmp)' \
  --img GRANT_B_PIN_PLANTED_RODATA "$P/grantB-S-rodata.elf" 'copy of GRANT_B_PIN with one .rodata address re-pointed at file offset 0x850cc (planted/planted.cmp)' \
  --img GRANT_B_TWIN_PLANTED_RODATA "$P/grantB-U-rodata.elf" 'copy of GRANT_B_TWIN with one .rodata address re-pointed at file offset 0x850cc (planted/planted.cmp)'
echo done
