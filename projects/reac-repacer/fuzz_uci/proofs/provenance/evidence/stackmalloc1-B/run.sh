#!/bin/bash
# Reproduce reac-repacer/fuzz_uci's IMAGE-B class-1 __asan_stack_malloc_1 contract relocation (lib/B/Rt/YF0r.v,
# lib/B/Rt/YF0s.v and the shared lib/Reusable/YF0v.v they Require).
#
#   run.sh <workdir> [extra port_core args]      then apply-sm1.sh (copy, nothing overwritten), header-sm1.py (comments only)
#                                                and header-sm1-restore.py LIB HUB (comments only: the corrected header rule)
#
# The route is core-B's (../core-B/METHOD.md, ../core-B/run.sh); only the file list, the overrides and the patch differ:
#   overrides-sm1.tsv  one value no rule decides (measure-sm1.py)
#   B-fs-ranges.patch  YF0r.v's code table without fuzz_grant's __asan_stack_malloc_0 / _2 / _4 ranges (fuzz_uci links
#                      class 1 only; the class-1 code calls none of them: BYTECMP.md)
# Inputs (each named by sha):
#   REL    port_core 0e4e065eab9f: git archive 7f0e4b05267 tools/pg-reloc/0e4e065eab9f
#   DON    fuzz_grant's RELEASED lib at origin/ossv/recipes 4f87de75d67, normalised by ../core-B/mkdon.sh:
#            mkdon.sh 4f87de75d67 fuzz_grant B $DONROOT ; DON=$DONROOT/proofs/libreac/fuzz_grant/lib
#          (lib/B/Rt/YF0r.v and YF0s.v are Rt/YF0r.v and Rt/YF0s.v there, lib/Reusable/YF0v.v is YF0v.v)
#   SYMS   ../core-B/fuzz_grant.asan-ubsan.syms.txt (mksyms.py over the donor's unstripped twin, sha256 5a5ee7c02b4e)
#   P, R   the pinned image trees: P holds libreac's fuzz_grant (asan-ubsan fde52226dc48, asan c2c7559b29bd), R holds
#          reac-repacer's result/ (fuzz_uci.asan-ubsan a1b86e424add = harness.yaml, twin 8d07ffcf5948; fuzz_uci.asan
#          6ea017c24525)
#   LIB    proofs/reac-repacer/fuzz_uci/lib of this branch WITHOUT the three files: image A's core, the image-B start-up
#          layer and the image-B core (lib/B, 389 files). Every module the three files Require except YF0v is KEPT from it.
# Flags as core-B: --old-prog 80a3c:86640, the rename set, image-B mode, the start-up files --no-stage'd.
set -uo pipefail
WORK=${1:?usage: run.sh <workdir> [extra port_core args]}; shift
HERE=$(cd "$(dirname "$0")" && pwd)
CORE=$HERE/../core-B
: "${REL:?set REL to the extracted tools/pg-reloc/0e4e065eab9f}"
: "${DON:?set DON to the normalised donor lib (core-B/mkdon.sh)}"
: "${LIB:?set LIB to proofs/reac-repacer/fuzz_uci/lib}"
: "${P:?set P to libreac's pinned image tree (bin/fuzz_grant)}"
: "${R:?set R to reac-repacer's pinned image tree (result/bin/fuzz_uci, result/unstripped/fuzz_uci)}"
NS=()
while read -r f; do [ -n "$f" ] && NS+=(--no-stage "$f"); done < "$CORE/no-stage-B.txt"
python3 "$REL/port_core.py" \
  --src-lib "$DON" \
  --src-mod OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib \
  --src-images OssFuzzTheorems.libreac.fuzz_grant.images \
  --old-elf "$P/bin/fuzz_grant/fuzz_grant.asan-ubsan" \
  --old-syms "$CORE/fuzz_grant.asan-ubsan.syms.txt" \
  --old-prog 80a3c:86640 \
  --target-lib "$LIB" \
  --target-mod OssFuzzTheorems.Proofs.reac_repacer.fuzz_uci.lib \
  --target-images OssFuzzTheorems.reac_repacer.fuzz_uci.images \
  --target-name reac-repacer/fuzz_uci \
  --target-elf "$R/result/bin/fuzz_uci/fuzz_uci.asan-ubsan" \
  --target-syms "$R/result/unstripped/fuzz_uci/fuzz_uci.asan-ubsan" \
  --files "$HERE/files-sm1.txt" \
  "${NS[@]}" \
  --rename GrantB=UciB --rename GrantSyms=UciSyms --rename GrantB_syms=UciB_syms --rename GrantB_ok=UciB_ok \
  --remap-images --reusable-dir B --kernel-dir Reusable \
  --kernel-image "$P/bin/fuzz_grant/fuzz_grant.asan" \
  --known-elf "$R/result/bin/fuzz_uci/fuzz_uci.asan" \
  --known-elf "$P/bin/fuzz_grant/fuzz_grant.asan" \
  --override "$HERE/overrides-sm1.tsv" \
  --patch "$HERE/B-fs-ranges.patch" \
  --work "$WORK" "$@"
