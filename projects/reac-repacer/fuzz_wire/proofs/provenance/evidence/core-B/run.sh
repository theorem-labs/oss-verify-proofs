#!/bin/bash
# Reproduce reac-repacer/fuzz_wire's IMAGE-B (fuzz_wire.asan-ubsan) core relocation. The route is fuzz_uci's
# (proofs/reac-repacer/fuzz_uci/provenance/evidence/core-B/METHOD.md); this file names what differs for fuzz_wire.
#
#   run.sh <workdir> [--apply]     then, in this order (GATES.md section 0): apply-B.sh (the apply rule; on the composed
#                                  library the consumer side's step 2, provenance/evidence/depot-B, then replaces 125 of
#                                  the 372 files), icpt-memmove.py (YE34), yd1j-x2.py (YD1j), kernel-depot-B.py (YC5d
#                                  YCbp YCbq YCe5), yb1w-rows.py (YB1w), yb1w_clause2_lockB.py then yb1w-drop-unread.py
#                                  (YB1w: the cells no file reads that are false by name or unverifiable by symtab), then
#                                  yb1w_clause2_v4.py then yb1w-drop-unread.py again (the cells name rule v4 adds), then
#                                  yb1w_clause2_v5.py then yb1w-drop-unread.py again (the cells v5.2 adds), then
#                                  yb1w-side-stack-note.py (YB1w: the donor's side-stack note, GATES.md section 13)
#
# Inputs (each named by sha; nothing is read from a host path the tree does not name):
#   REL    port_core 7a74e72920e6, the tool of record (pg-tools commit b25bb893cdb, tools/pg-reloc/7a74e72920e6;
#          registered at tools registry commit 94d243257b5). Its B mode names lib.B.YImgTop, so no post-step does, and
#          its renames leave the donor's leading licence-notice block as the donor has it.
#   DON    fuzz_grant's RELEASED image-B lib, origin/ossv/recipes 4f87de75d67, normalised by mkdon.sh beside this file
#            HUB=<clone> mkdon.sh 4f87de75d67 fuzz_grant B $DONROOT ; DON=$DONROOT/proofs/libreac/fuzz_grant/lib
#   SYMS   fuzz_grant.asan-ubsan.syms.txt beside this file (mksyms.py over the donor's unstripped twin, sha256
#          5a5ee7c02b4e; the same file as fuzz_uci's image-B core uses)
#   P, R   the pinned image trees: P holds libreac's fuzz_grant (asan-ubsan fde52226dc48), R reac-repacer's result/
#          (fuzz_wire.asan-ubsan af4534831a45, unstripped twin 51eb4bef2425; fuzz_wire.asan 2f8f8697cd4f)
#   LIB    the target lib proofs/reac-repacer/fuzz_wire/lib of this branch without its image-B core files: the wire
#          trunk with image A's core and the image-B start-up layer merged in. Every shared kernel file is KEPT from
#          it (lib/Reusable is image A's), the 19 start-up files of no-stage-B.txt are never staged, and the
#          zero-shadow / CZONE rules read the unit's own B/YF0m.v from it.
# What differs from fuzz_uci's image-B run (measured on fuzz_wire.asan-ubsan's own .symtab; files-B-core.txt):
#   - fuzz_wire links __interceptor_trampoline_bcmp / bcmp / real_bcmp, so the bcmp walks YE2s / YE2z stay in the list;
#     it links no __asan_memset, so the memset walks YE2r YE6t YE6u YE6v leave it, as for fuzz_uci.
#   - fuzz_wire registers no ASan global (no asan_globals section): TFIB_BSS is read as the start of .bss
#     (measure-B.py; on the donor that is __stop_asan_globals, the control).
#   - renames GrantB GrantSyms GrantB_syms GrantB_ok -> WireB WireSyms WireB_syms WireB_ok.
# --old-prog 80a3c:86640 is the donor's (see fuzz_uci's run.sh for its rule and control).
set -uo pipefail
WORK=${1:?usage: run.sh <workdir> [extra port_core args, e.g. --apply]}; shift
HERE=$(cd "$(dirname "$0")" && pwd)
: "${REL:?set REL to the extracted tools/pg-reloc/7a74e72920e6}"
: "${DON:?set DON to the normalised donor lib (mkdon.sh)}"
: "${LIB:?set LIB to proofs/reac-repacer/fuzz_wire/lib}"
: "${P:?set P to libreac's pinned image tree (bin/fuzz_grant, unstripped/fuzz_grant)}"
: "${R:?set R to reac-repacer's pinned image tree (result/bin/fuzz_wire, result/unstripped/fuzz_wire)}"
NS=()
while read -r f; do [ -n "$f" ] && NS+=(--no-stage "$f"); done < "$HERE/no-stage-B.txt"
python3 "$REL/port_core.py" \
  --src-lib "$DON" \
  --src-mod OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib \
  --src-images OssFuzzTheorems.libreac.fuzz_grant.images \
  --old-elf "$P/bin/fuzz_grant/fuzz_grant.asan-ubsan" \
  --old-syms "$HERE/fuzz_grant.asan-ubsan.syms.txt" \
  --old-prog 80a3c:86640 \
  --target-lib "$LIB" \
  --target-mod OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib \
  --target-images OssFuzzTheorems.reac_repacer.fuzz_wire.images \
  --target-name reac-repacer/fuzz_wire \
  --target-elf "$R/result/bin/fuzz_wire/fuzz_wire.asan-ubsan" \
  --target-syms "$R/result/unstripped/fuzz_wire/fuzz_wire.asan-ubsan" \
  --files "$HERE/files-B-core.txt" \
  "${NS[@]}" \
  --rename GrantB=WireB --rename GrantSyms=WireSyms --rename GrantB_syms=WireB_syms --rename GrantB_ok=WireB_ok \
  --remap-images --reusable-dir B --kernel-dir Reusable \
  --kernel-image "$P/bin/fuzz_grant/fuzz_grant.asan" \
  --known-elf "$R/result/bin/fuzz_wire/fuzz_wire.asan" \
  --known-elf "$P/bin/fuzz_grant/fuzz_grant.asan" \
  --override "$HERE/overrides-B.tsv" \
  --patch "$HERE/B-zero-shadow-forallb.patch" \
  --patch "$HERE/B-cell-lookup.patch" \
  --patch "$HERE/B-ad1q-shape.patch" \
  --work "$WORK" "$@"
