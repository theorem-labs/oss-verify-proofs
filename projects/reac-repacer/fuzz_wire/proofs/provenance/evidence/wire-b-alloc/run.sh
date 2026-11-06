#!/usr/bin/env bash
# Re-runs every measurement of RECORD.md (read-only on all inputs), then writes the committed slice commit/.
# Version of record: cmpkit 86da41d3ef68 (strictcmp3 the one compare; closure_strict3 by name; paircl 926a9a88afcd
# against the stripped grant pin; repin_check e6883477399d; drvcmp 4d70e90bc1fa; bytecmp 1480ca2faea0; and the kit's
# two exposure scans luiscan 9ae61e4a0e01 and ambiscan 9f61b4cee422), with jtcheck 226254f48c97 (tools/jtcheck.py, from
# the original sha256 226254f48c97; tools/DIFFS.md), the jtcheck of record for table verdicts, in place of the kit's jtcheck 8b0ea3862423, plus this record's
# HAND TRACES of every lui value of every compared function (luitrace.py, over the CITE table cite.tsv that cite_gen.py
# reads from the pinned compiler-rt source), every base of the compared set named as its full address (basescan.py),
# and the plants the hand traces must catch or refuse (plants.py: (a) and (c) caught, (b) refused).
# tools/gates.py writes the unit gates last: one verdict file per gate, with its evidence and its two controls.
# The 8 kit files and the jtcheck 226254f48c97 copy in tools/ are kitscrub.py's copies (host paths out of the comments, a host-path constant read from
# the environment instead (bytecmp lines 182, 183, with the `os` import at line 13; repin_check lines 16-21), a session's
# citation dropped with its claim kept and the kit's plain word `lane` reworded or dropped (CITE), every other
# session name written as its role and every time of day dropped by rolenames.py (`the unit owner's ruling`),
# jtcheck.py's README labels and counts set to its package's README and controls, or dropped where no README item
# covers the sentence (JT_WORDS), and
# the kit's sha pins, with the docstring words on what they name, set to the copies; kitscrub.py's docstring lists each
# change, and tools/DIFFS.md gives each diff with its code compare). Earlier versions of record are kept in earlier/ (RECORD.md says which, and which of them
# has a run.sh of its own), each with its own tools and outputs, as its own run wrote them except the rewrites earlier/SCRUB.tsv lists: the role rewrite,
# the dropped times of day, the forbidden-word loader, the sha256 pin repair and the DIFFS.md note
# (tools/earlierscrub.py); every other byte under earlier/ is its own text as it ran.
# env.sh (not committed) sets UNIT (fuzz_uci, fuzz_wire or fuzz_egress), the image paths -- X_S / X_U = the unit's
# image-B pin and unstripped twin, GR_S / GR_U = fuzz_grant B pin and twin, ID_S / ID_U = fuzz_identity B pin and
# twin --, ROSTER_TSV, the session roster whose names the writers refuse (the name shapes are refused always),
# SCRUB_FORBIDDEN, a file outside the slice with the text the writers refuse or rewrite, and NAMES_DIR and ROSTER_TXT,
# a directory of agent-name lists and the tool registry's roster.txt, whose names the writers also refuse or rewrite.
# SCRUB_FORBIDDEN, NAMES_DIR and ROSTER_TXT are required: the writers stop without them (tools/rolenames.py, which
# every writer loads, stops at its import when NAMES_DIR or ROSTER_TXT is unset or names nothing).
set -euo pipefail
cd "$(dirname "$0")"
HERE=$(pwd)
source ./env.sh
TOOLS=$HERE/tools
P=$HERE/planted
R=__interceptor_trampoline_malloc,___interceptor_malloc,__interceptor_trampoline_free,___interceptor_free
JT=$(paste -sd, "$HERE/jtcheck-members.txt")
case "$UNIT" in
  fuzz_uci) K=UCI; IDX=7521;; fuzz_wire) K=WIRE; IDX=7525;; fuzz_egress) K=EGRESS; IDX=7513;;
  *) echo "unknown UNIT $UNIT" >&2; exit 1;;
esac

sha256sum "$X_S" "$X_U" "$GR_S" "$GR_U" "$ID_S" "$ID_U" > images.sha256
python3 "$TOOLS/drvcmp.py" twins "$X_S" "$X_U" "$GR_S" "$GR_U" "$ID_S" "$ID_U" > twins.out
for k in X_U GR_U ID_U; do echo "== $k"; python3 "$TOOLS/syms.py" "${!k}" "$R,__interceptor_malloc,__interceptor_free"; done > roots-syms.out
# planted copies of grant B, one changed word each (RECORD.md "Controls"); the same offsets in every unit, since grant B
# is the same image:
#   call:     ___interceptor_malloc 0x530b0+0x130 (file 0x421e0): jal __asan::asan_malloc -> jal __sanitizer_get_allocated_begin
#   rodata:   __intscan 0x95c04+0x4c8 (file 0x850cc): addi s5,a1,1944 -> 1120, re-points `table` to `all_mask`
#   debruijn: one byte of the 64-byte De Bruijn ctz table at vaddr 0x10432 (file 0x432), 0x0e -> 0x0f
mkdir -p "$P"
rm -f "$P"/*.elf "$P"/*.out
for k in call rodata; do cp "$GR_S" "$P/grantB-S-$k.elf"; cp "$GR_U" "$P/grantB-U-$k.elf"; done
cp "$GR_U" "$P/grantB-U-debruijn.elf"
chmod u+w "$P"/*.elf
for f in grantB-S-call grantB-U-call; do printf '\xef\xf0\x9d\xcd' | dd of="$P/$f.elf" bs=1 seek=$((0x421e0)) conv=notrunc status=none; done
for f in grantB-S-rodata grantB-U-rodata; do printf '\x93\x8a\x05\x46' | dd of="$P/$f.elf" bs=1 seek=$((0x850cc)) conv=notrunc status=none; done
printf '\x0f' | dd of="$P/grantB-U-debruijn.elf" bs=1 seek=$((0x432)) conv=notrunc status=none

(cd "$TOOLS" && sha256sum *.py) > "$HERE/tools.sha256"
(cd "$HERE" && sha256sum cite.tsv cite-extra.tsv) > "$HERE/cite.sha256"     # cite.tsv: cite_gen.py over compiler-rt-20.1.8.src.tar.xz (RECORD.md)
cd "$TOOLS"
# the kit's measurements against grant B and against identity B (paircl's --targets-out is relative to tools/, so its
# header names the file without a host path)
python3 strictcmp3.py cmp "$R" U="$X_U" G="$GR_U" I="$ID_U" U:G,U:I > "$HERE/roots.tsv" &
python3 closure_strict3.py "$X_U" "$GR_U" "$R" > "$HERE/closure-grant.out" &
python3 closure_strict3.py "$X_U" "$ID_U" "$R" > "$HERE/closure-identity.out" &
python3 paircl.py "$X_U" "$GR_S" ___interceptor_malloc 0x530b0 "$GR_U" --full --targets-out "../paircl-targets-malloc-grant.tsv" > "$HERE/paircl-malloc-grant.out" &
python3 paircl.py "$X_U" "$GR_S" ___interceptor_free 0x52ee0 "$GR_U" --full --targets-out "../paircl-targets-free-grant.tsv" > "$HERE/paircl-free-grant.out" &
python3 paircl.py "$X_U" "$GR_S" __interceptor_trampoline_malloc 0x52edc "$GR_U" --full --targets-out "../paircl-targets-tmalloc-grant.tsv" > "$HERE/paircl-tmalloc-grant.out" &
python3 paircl.py "$X_U" "$GR_S" __interceptor_trampoline_free 0x52ed8 "$GR_U" --full --targets-out "../paircl-targets-tfree-grant.tsv" > "$HERE/paircl-tfree-grant.out" &
python3 jtcheck.py "$X_U" "$GR_U" "$JT" > "$HERE/jtcheck-grant.out" &
python3 jtcheck.py "$X_U" "$ID_U" "$JT" > "$HERE/ctl-jtcheck-identity.out" &
wait
# the kit plants: each must be caught (strictcmp3 / closure_strict3 / jtcheck / paircl)
python3 strictcmp3.py cmp "$R" U="$X_U" P="$P/grantB-U-call.elf" U:P > "$HERE/ctl-planted-call-roots.tsv" &
python3 closure_strict3.py "$X_U" "$P/grantB-U-call.elf" ___interceptor_malloc > "$HERE/ctl-planted-call-closure.out" &
python3 jtcheck.py "$X_U" "$P/grantB-U-call.elf" ___interceptor_malloc > "$HERE/ctl-planted-call-jtcheck.out" &
python3 paircl.py "$X_U" "$P/grantB-S-call.elf" ___interceptor_malloc 0x530b0 "$P/grantB-U-call.elf" --targets-out "../ctl-planted-call-paircl-targets.tsv" > "$HERE/ctl-planted-call-paircl.out" &
python3 strictcmp3.py cmp __intscan U="$X_U" P="$P/grantB-U-rodata.elf" U:P > "$HERE/ctl-planted-rodata-intscan.tsv" &
python3 jtcheck.py "$X_U" "$P/grantB-U-rodata.elf" __intscan > "$HERE/ctl-planted-rodata-jtcheck.out" &
python3 closure_strict3.py "$X_U" "$P/grantB-U-rodata.elf" ___interceptor_malloc > "$HERE/ctl-planted-rodata-closure.out" &
python3 paircl.py "$X_U" "$P/grantB-S-rodata.elf" ___interceptor_malloc 0x530b0 "$P/grantB-U-rodata.elf" --targets-out "../ctl-planted-rodata-paircl-targets.tsv" > "$HERE/ctl-planted-rodata-paircl.out" &
wait
# the kit's two exposure scans: rule 8 (lui) per function, and the by-name compares that hit a duplicated name
python3 luiscan.py --all "$X_U" "$GR_U" > "$HERE/luiscan.tsv"
python3 luirows.py "$X_U" "$GR_U" "$HERE/luiscan.tsv" "$R" > "$HERE/luirows.tsv"
# the hand traces of every lui value of every compared function, and the three plants of plants.py: (a) and (c) must
# be caught (DIFFERS), (b) refused
python3 luitrace.py "$X_U" "$GR_U" "$R" "$HERE/cite.tsv" > "$HERE/luitrace.tsv"
python3 plants.py "$X_U" "$GR_U" "$P" "$R" "$HERE/cite.tsv" "$HERE/luitrace.tsv" > "$HERE/plants.out"
# the acceptance measurement: one row per kit `other` member, with the full target list from tcmp
python3 otherrows.py "$X_U" "$HERE/closure-grant.out" "$HERE/paircl-malloc-grant.out" ___interceptor_malloc > "$HERE/other-rows.txt"
python3 settle.py "$X_U" "$GR_U" "$(cat "$HERE/other-rows.txt")" > "$HERE/settle.tsv"
# the tables jtcheck 226254f48c97 refuses (the REFUSED rows of settle.tsv: no proof), each settled by hand under this
# record's rule (entries, dispatch, and the bound by a CFG walk, each on both images: handtable.py, parts (1)-(3));
# part (4), a non-writer's read of the settlement, is not a tool's: RECORD.md states it with each settlement
HT=$(awk -F'\t' '$1 == "ACCEPT" && $7 == "REFUSED" {print $2 "@+" $3}' "$HERE/settle.tsv" | paste -sd, -)
if [ -n "$HT" ]; then python3 handtable.py "$X_U" "$GR_U" "$HT" > "$HERE/handtable.out"; else : > "$HERE/handtable.out"; fi
# shape (h) of the unit owner's ruling: every load / store / AMO / jalr base of the compared set, lui or not, named as its full
# address in X and Y (the 4 roots first, in full); an address no symbol covers is compared by its bytes or settled by
# jtcheck 226254f48c97's table rule, with the settle.tsv row cited
python3 basescan.py "$X_U" "$GR_U" "$R" "$HERE/settle.tsv" > "$HERE/basescan.tsv"
# the escaping empty strings: whole-image scan of the fields they are stored into, then the escape settlement
python3 objscan.py "$X_U" "$GR_U" "$HERE/settle.tsv" "$HERE/fieldscan.tsv"
python3 escape.py "$X_U" "$GR_U" "$HERE/settle.tsv" "$HERE/fieldscan.tsv"
python3 dupcheck.py "$X_U" "$GR_U" "$R" "$(cat "$HERE/other-rows.txt"),$JT,__intscan" > "$HERE/dupcheck.tsv"
# settlement controls: planted vs untouched De Bruijn copy on Allocate+0xdc; and the dispatch size: VSNPrintf's
# dispatch `slli t3,a7,2` at +0x1b8 (4-byte entries) set to `slli t3,a7,3` in a copy of X, whose table settle.py must
# then read with 8-byte entries or not settle (gates.py, plants gate)
RA=_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb
python3 settle.py "$X_U" "$P/grantB-U-debruijn.elf" "$RA" > "$HERE/ctl-settle-debruijn-planted.tsv"
python3 settle.py "$X_U" "$GR_U" "$RA" > "$HERE/ctl-settle-debruijn-untouched.tsv"
RV=_ZN11__sanitizer9VSNPrintfEPciPKcPv
python3 - "$X_U" "$P/unitB-U-slli3.elf" "$RV" 0x1b8 <<'EOF'
import sys
from elftools.elf.elffile import ELFFile
src, dst, name, off = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4], 16)
e = ELFFile(open(src, 'rb'))
s = [x for x in e.get_section_by_name('.symtab').iter_symbols() if x.name == name]
a = s[0]['st_value'] + off
fo = [a - g['p_vaddr'] + g['p_offset'] for g in e.iter_segments()
      if g['p_type'] == 'PT_LOAD' and g['p_vaddr'] <= a < g['p_vaddr'] + g['p_filesz']]
b = bytearray(open(src, 'rb').read()); w = int.from_bytes(b[fo[0]:fo[0] + 4], 'little')
if len(s) != 1 or len(fo) != 1 or w & 0xfc00707f != 0x1013 or (w >> 20) & 0x3f != 2:
    raise SystemExit('run.sh: %s+%#x is not one 4-byte `slli rd, rs, 2`' % (name, off))
b[fo[0]:fo[0] + 4] = (w + (1 << 20)).to_bytes(4, 'little')
open(dst, 'wb').write(b)
EOF
python3 settle.py "$P/unitB-U-slli3.elf" "$GR_U" "$RV" > "$HERE/ctl-settle-slli3-planted.tsv"
# five hand-settlement controls (gates.py, plants gate, each on its own reason): the first four are copies of X with one
# word of parseCIE changed, the fifth (slot) a copy of GRANT_B_TWIN with one slot of parseCIE's table changed. bound and
# zarm test the bound rule (a walk of the CFG, the dispatch's arms included, not address order), jump the dispatch
# rule, entries and slot the entries rule:
#   bound:   +0x278 `addi a0,a0,1` (in an arm that loops back to the guard, after the guard in address order) set to
#            `addi s5,zero,10`, a second definition of the limit that only a walk of the CFG finds: handtable.py must
#            read NOT SETTLED because the bound differs between X and Y;
#   zarm:    +0x28c `sb s7,0x31(s0)` (the 'z' arm, reached only through the dispatch) set to `addi s5,zero,60`, a
#            larger second limit: handtable.py must not settle it (the walk takes it, and the 48th slot runs off the
#            table);
#   jump:    +0x248 `sb s7,48(s0)` set to `j +0x1c`, a jump into the dispatch block at +0x264: handtable.py must refuse
#            it (that block word gains a second predecessor);
#   entries: the limit `addi s5,zero,46` at +0x234 set to `addi s5,zero,47`: the 48th slot is the next table's first,
#            so handtable.py must refuse it by its entries;
#   slot:    in a copy of GRANT_B_TWIN, parseCIE's table slot 3 (vaddr 0x213a4, the `O` entry, -> parseCIE+0x24c)
#            re-pointed to parseCIE+0x270 (the `L` entry's slot bytes): handtable.py must read DIFFERS.
RC=_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE8parseCIEERS1_mPNS2_8CIE_InfoE
plant_word() {   # SRC DST FUNCTION OFFSET OLD_WORD NEW_WORD: copy SRC to DST with one 4-byte word of FUNCTION changed
python3 - "$@" <<'EOF'
import sys
from elftools.elf.elffile import ELFFile
src, dst, name, off, old, new = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4], 16), int(sys.argv[5], 16), int(sys.argv[6], 16)
e = ELFFile(open(src, 'rb'))
s = [x for x in e.get_section_by_name('.symtab').iter_symbols() if x.name == name]
a = s[0]['st_value'] + off
fo = [a - g['p_vaddr'] + g['p_offset'] for g in e.iter_segments()
      if g['p_type'] == 'PT_LOAD' and g['p_vaddr'] <= a < g['p_vaddr'] + g['p_filesz']]
b = bytearray(open(src, 'rb').read()); w = int.from_bytes(b[fo[0]:fo[0] + 4], 'little')
if len(s) != 1 or len(fo) != 1 or w != old:
    raise SystemExit('run.sh: %s+%#x is not one word %08x' % (name, off, old))
b[fo[0]:fo[0] + 4] = new.to_bytes(4, 'little')
open(dst, 'wb').write(b)
EOF
}
plant_word "$X_U" "$P/unitB-U-ciearm.elf" "$RC" 0x278 00150513 00a00a93
python3 handtable.py "$P/unitB-U-ciearm.elf" "$GR_U" "$RC@+0x23c" > "$HERE/ctl-handtable-bound.out"
plant_word "$X_U" "$P/unitB-U-cielimit.elf" "$RC" 0x234 02e00a93 02f00a93
python3 handtable.py "$P/unitB-U-cielimit.elf" "$GR_U" "$RC@+0x23c" > "$HERE/ctl-handtable-entries.out"
plant_word "$X_U" "$P/unitB-U-ciezarm.elf" "$RC" 0x28c 037408a3 03c00a93
python3 handtable.py "$P/unitB-U-ciezarm.elf" "$GR_U" "$RC@+0x23c" > "$HERE/ctl-handtable-zarm.out"
plant_word "$X_U" "$P/unitB-U-ciejump.elf" "$RC" 0x248 03740823 01c0006f
python3 handtable.py "$P/unitB-U-ciejump.elf" "$GR_U" "$RC@+0x23c" > "$HERE/ctl-handtable-jump.out"
python3 - "$GR_U" "$P/grantB-U-cieslot.elf" 0x213a4 24600600 48600600 <<'EOF'
import sys
from elftools.elf.elffile import ELFFile
src, dst, a, old, new = sys.argv[1], sys.argv[2], int(sys.argv[3], 16), bytes.fromhex(sys.argv[4]), bytes.fromhex(sys.argv[5])
e = ELFFile(open(src, 'rb'))
fo = [a - g['p_vaddr'] + g['p_offset'] for g in e.iter_segments()
      if g['p_type'] == 'PT_LOAD' and g['p_vaddr'] <= a < g['p_vaddr'] + g['p_filesz']]
b = bytearray(open(src, 'rb').read())
if len(fo) != 1 or bytes(b[fo[0]:fo[0] + 4]) != old:
    raise SystemExit('run.sh: %#x does not hold the slot bytes %s' % (a, old.hex()))
b[fo[0]:fo[0] + 4] = new
open(dst, 'wb').write(b)
EOF
python3 handtable.py "$X_U" "$P/grantB-U-cieslot.elf" "$RC@+0x23c" > "$HERE/ctl-handtable-slot.out"
# ACCEPTANCES.tsv: kit verdict first, then the settle rows, then one LUI row per lui-in-section target, then the plants
python3 mkaccept.py "$HERE/ACCEPTANCES.tsv" "$UNIT B" "$HERE/closure-grant.out" "$HERE/paircl-malloc-grant.out" \
  "$HERE/settle.tsv" "$HERE/dupcheck.tsv" "$HERE/ctl-settle-debruijn-planted.tsv" "$HERE/ctl-settle-debruijn-untouched.tsv" \
  86da41d3ef68 "$HERE/luirows.tsv" "$HERE/luitrace.tsv" "$HERE/plants.out"
# ambiscan over every output this run wrote: did any by-name compare take a duplicated name?
python3 ambiscan.py "$X_U" "$GR_U" "$HERE/roots.tsv" "$HERE/closure-grant.out" "$HERE/closure-identity.out" \
  "$HERE"/paircl-*-grant.out "$HERE/jtcheck-grant.out" "$HERE"/ctl-*.out "$HERE"/ctl-*.tsv "$HERE/settle.tsv" \
  "$HERE/luitrace.tsv" "$HERE/luirows.tsv" "$HERE/ACCEPTANCES.tsv" > "$HERE/ambiscan.out"
(cd "$P" && sha256sum *.elf > planted.sha256
 for f in *.elf; do case $f in *-S-*) o=$GR_S;; plant-a-X.elf|plant-b-X.elf|plant-c-X.elf|unitB-U-*.elf) o=$X_U;; *) o=$GR_U;; esac
   echo "$f: $(cmp -l "$f" "$o" | tr '\n' ' ' || true)"; done > planted.cmp)
rm -rf "$TOOLS/__pycache__"
# the unit gates, read from the outputs above: one verdict file per gate (gate-kit.txt, gate-lui.txt, gate-base.txt,
# gate-plants.txt), each ending in its `GATE <unit>-b-alloc-<gate> VERDICT: ...` line, plus gate-controls.txt, the
# two negative controls gates.py runs on copies before it writes a verdict. GATE_HEAD (env.sh) is the head the
# verdict names (gates.py reads it first, else the git HEAD of this directory's worktree).
python3 "$TOOLS/gates.py" "$HERE" "$UNIT"
# the committed slice: raw outputs with every image path rewritten to its token, and every path of a file of this
# directory (paircl names its --targets-out file) to the file's name (scrub_out.py refuses any leftover); earlier/,
# each prior version as its own run wrote it except the rewrites earlier/SCRUB.tsv lists, is copied verbatim and
# checked the same way
cd "$HERE"
python3 tools/scrub_out.py . --tooldir tools --here . --verbatim earlier \
  --img ${K}_B_PIN "$X_S" "$UNIT.asan-ubsan, the pinned image: index/binaries.tsv:$IDX" \
  --img ${K}_B_TWIN "$X_U" "$UNIT.asan-ubsan, the unstripped twin of ${K}_B_PIN (PT_LOAD equal: twins.out)" \
  --img GRANT_B_PIN "$GR_S" 'fuzz_grant.asan-ubsan, the pinned image: index/binaries.tsv:5591' \
  --img GRANT_B_TWIN "$GR_U" 'fuzz_grant.asan-ubsan, the unstripped twin of GRANT_B_PIN (PT_LOAD equal: twins.out)' \
  --img IDENT_B_PIN "$ID_S" 'fuzz_identity.asan-ubsan, the pinned image: index/binaries.tsv:5595' \
  --img IDENT_B_TWIN "$ID_U" 'fuzz_identity.asan-ubsan, the unstripped twin of IDENT_B_PIN (PT_LOAD equal: twins.out)' \
  --img GRANT_B_PIN_PLANTED_CALL "$P/grantB-S-call.elf" 'copy of GRANT_B_PIN with one call re-pointed at file offset 0x421e0 (planted/planted.cmp)' \
  --img GRANT_B_TWIN_PLANTED_CALL "$P/grantB-U-call.elf" 'copy of GRANT_B_TWIN with one call re-pointed at file offset 0x421e0 (planted/planted.cmp)' \
  --img GRANT_B_PIN_PLANTED_RODATA "$P/grantB-S-rodata.elf" 'copy of GRANT_B_PIN with one .rodata address re-pointed at file offset 0x850cc (planted/planted.cmp)' \
  --img GRANT_B_TWIN_PLANTED_RODATA "$P/grantB-U-rodata.elf" 'copy of GRANT_B_TWIN with one .rodata address re-pointed at file offset 0x850cc (planted/planted.cmp)' \
  --img GRANT_B_TWIN_PLANTED_DEBRUIJN "$P/grantB-U-debruijn.elf" 'copy of GRANT_B_TWIN with one byte of the De Bruijn ctz table at file offset 0x432 changed from 0x0e to 0x0f (planted/planted.cmp)' \
  --img ${K}_B_TWIN_PLANTED_SLLI3 "$P/unitB-U-slli3.elf" "copy of ${K}_B_TWIN with the dispatch \`slli t3,a7,2\` of VSNPrintf+0x1b8 set to \`slli t3,a7,3\` (planted/planted.cmp)" \
  --img ${K}_B_TWIN_PLANTED_CIELIMIT "$P/unitB-U-cielimit.elf" "copy of ${K}_B_TWIN with parseCIE's table limit \`addi s5,zero,46\` at +0x234 set to \`addi s5,zero,47\` (planted/planted.cmp)" \
  --img ${K}_B_TWIN_PLANTED_CIEARM "$P/unitB-U-ciearm.elf" "copy of ${K}_B_TWIN with parseCIE's \`addi a0,a0,1\` at +0x278 set to \`addi s5,zero,10\`, a second definition of the table limit (planted/planted.cmp)" \
  --img ${K}_B_TWIN_PLANTED_CIEZARM "$P/unitB-U-ciezarm.elf" "copy of ${K}_B_TWIN with parseCIE's \`sb s7,0x31(s0)\` at +0x28c set to \`addi s5,zero,60\`, a second definition of the table limit in a jump-table arm (planted/planted.cmp)" \
  --img ${K}_B_TWIN_PLANTED_CIEJUMP "$P/unitB-U-ciejump.elf" "copy of ${K}_B_TWIN with parseCIE's \`sb s7,48(s0)\` at +0x248 set to \`j +0x1c\`, a jump into the dispatch block (planted/planted.cmp)" \
  --img GRANT_B_TWIN_PLANTED_CIESLOT "$P/grantB-U-cieslot.elf" "copy of GRANT_B_TWIN with parseCIE's table slot 3 at vaddr 0x213a4 re-pointed to the target of slot 0 (planted/planted.cmp)" \
  --img ${K}_B_TWIN_PLANTED_ADD "$P/plant-a-X.elf" "copy of ${K}_B_TWIN with the four words of plant (a) (planted/planted.cmp)" \
  --img GRANT_B_TWIN_PLANTED_ADD "$P/plant-a-Y.elf" 'copy of GRANT_B_TWIN with the same four words of plant (a) (planted/planted.cmp)' \
  --img ${K}_B_TWIN_PLANTED_UPTR "$P/plant-b-X.elf" "copy of ${K}_B_TWIN with the one re-pointed call of plant (b) (planted/planted.cmp)" \
  --img ${K}_B_TWIN_PLANTED_DIVU "$P/plant-c-X.elf" "copy of ${K}_B_TWIN with the five words of plant (c) (planted/planted.cmp)" \
  --img GRANT_B_TWIN_PLANTED_DIVU "$P/plant-c-Y.elf" 'copy of GRANT_B_TWIN with the same five words of plant (c) (planted/planted.cmp)' \
  --img GRANT_B_TWIN_PLANTED_UPTR "$P/plant-b-Y.elf" 'copy of GRANT_B_TWIN with the same call of plant (b) re-pointed to its own copy of that function (planted/planted.cmp)'
echo done
