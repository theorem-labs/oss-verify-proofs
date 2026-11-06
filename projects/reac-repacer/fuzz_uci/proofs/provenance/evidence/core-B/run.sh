#!/bin/bash
# Reproduce reac-repacer/fuzz_uci's IMAGE-B (fuzz_uci.asan-ubsan) core relocation.
#
#   run.sh <workdir> [--apply]     then apply-B.sh (the apply rule) and
#                                  imgtop-require.py fuzz_uci <lib> applied.txt (B files Require B's own YImgTop)
#
# Inputs (each named by sha; nothing is read from a host path the tree does not name):
#   REL    port_core 0e4e065eab9f: git archive 7f0e4b05267 tools/pg-reloc/0e4e065eab9f
#   DON    the donor = fuzz_grant's RELEASED image-B lib, origin/ossv/recipes 4f87de75d67, normalised by mkdon.sh beside
#          this file (lib/B over lib/Reusable at the lib root, module text ...fuzz_grant.lib.{Reusable,B} -> ...fuzz_grant.lib):
#            mkdon.sh 4f87de75d67 fuzz_grant B $DONROOT ; DON=$DONROOT/proofs/libreac/fuzz_grant/lib
#          Chosen over fuzz_identity's released lib/ReusableB (70952e1c8c9) by a measured dry run of both on the same target
#          lib (README.md): grant refused 67 / staged 369 per-image files, identity refused 60 + 3 partner-left FAIL rows /
#          staged 395 (26 kernel files grant keeps shared with image A, whose donor is grant); grant's names are image A's.
#   SYMS   fuzz_grant.asan-ubsan.syms.txt beside this file: mksyms.py over the donor's unstripped twin (sha256 5a5ee7c02b4e;
#          pin fde52226dc48); the same script reproduces decode-core's fuzz_grant.asan.syms.txt (body) byte for byte (control)
#   P, R   the pinned image trees of the pipeline (bin/<unit>/ and result/unstripped/<unit>/): P holds libreac's fuzz_grant
#          (asan-ubsan fde52226dc48, asan c2c7559b29bd), R holds reac-repacer's result/ (fuzz_uci.asan-ubsan a1b86e424add =
#          harness.yaml, unstripped twin 8d07ffcf5948; fuzz_uci.asan 6ea017c24525)
#   LIB    the target lib proofs/reac-repacer/fuzz_uci/lib of this branch before the run: the trunk 147218220547 with image
#          A's core (a8fc5eedae69) and the image-B start-up layer (883082ed41ea) merged in (merge 5a77a109158). Every shared
#          kernel file is KEPT from it (lib/Reusable is image A's), the 19 start-up files of no-stage-B.txt are never
#          staged, and the zero-shadow / CZONE rules read the unit's own B/YF0m.v from it. This run writes lib/B core
#          files only.
#   SLOTS  (optional) a --slots directory; not used by the run of record (LIB holds the start-up layer)
# Flags: --old-prog 80a3c:86640 = LLVMFuzzerTestOneInput .. end of the last program function before __wrap_getenv of
# fuzz_grant.asan-ubsan (the same rule gives grant asan's 806b0:857dc of decode-core and of image A: control).
set -uo pipefail
WORK=${1:?usage: run.sh <workdir> [extra port_core args, e.g. --apply]}; shift
HERE=$(cd "$(dirname "$0")" && pwd)
: "${REL:?set REL to the extracted tools/pg-reloc/0e4e065eab9f}"
: "${DON:?set DON to the normalised donor lib (mkdon.sh)}"
: "${LIB:?set LIB to proofs/reac-repacer/fuzz_uci/lib}"
SL=(); [ -n "${SLOTS:-}" ] && SL=(--slots "$SLOTS")
: "${P:?set P to libreac's pinned image tree (bin/fuzz_grant, unstripped/fuzz_grant)}"
: "${R:?set R to reac-repacer's pinned image tree (result/bin/fuzz_uci, result/unstripped/fuzz_uci)}"
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
  --target-mod OssFuzzTheorems.Proofs.reac_repacer.fuzz_uci.lib \
  --target-images OssFuzzTheorems.reac_repacer.fuzz_uci.images \
  --target-name reac-repacer/fuzz_uci \
  --target-elf "$R/result/bin/fuzz_uci/fuzz_uci.asan-ubsan" \
  --target-syms "$R/result/unstripped/fuzz_uci/fuzz_uci.asan-ubsan" \
  --files "$HERE/files-B-core.txt" \
  "${NS[@]}" \
  --rename GrantB=UciB --rename GrantSyms=UciSyms --rename GrantB_syms=UciB_syms --rename GrantB_ok=UciB_ok \
  --remap-images --reusable-dir B --kernel-dir Reusable \
  --kernel-image "$P/bin/fuzz_grant/fuzz_grant.asan" \
  --known-elf "$R/result/bin/fuzz_uci/fuzz_uci.asan" \
  --known-elf "$P/bin/fuzz_grant/fuzz_grant.asan" \
  --override "$HERE/overrides-B.tsv" \
  --patch "$HERE/B-zero-shadow-forallb.patch" \
  --patch "$HERE/B-cell-lookup.patch" \
  --patch "$HERE/B-ad1q-shape.patch" \
  "${SL[@]}" \
  --work "$WORK" "$@"
