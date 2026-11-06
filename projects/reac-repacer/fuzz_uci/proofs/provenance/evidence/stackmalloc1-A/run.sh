#!/bin/bash
# Reproduce reac-repacer/fuzz_uci's IMAGE-A class-1 __asan_stack_malloc_1 contract relocation (lib/A/Rt/AF0r.v,
# lib/A/Rt/AF0s.v and the shared lib/Reusable/YF0v.v they Require).
#
#   run.sh <workdir> [extra port_core args]      then apply-sm1.sh (copy, nothing overwritten) and header-sm1.py (comments only)
#
# The route is core-A's (../core-A/run.sh), the image-B record's (../stackmalloc1-B/run.sh) with image B -> image A; only
# the file list and the patch differ from core-A, and no value needs an --override (measure-sm1.py: the image-B
# record's one override, the low-shadow bound, is a donor value here that holds on fuzz_uci.asan unchanged):
#   A-fs-ranges.patch  AF0r.v's code table without fuzz_grant's __asan_stack_malloc_0 / _2 / _4 ranges (fuzz_uci links
#                      class 1 only; the class-1 code calls none of them: BYTECMP.md)
#   YF0v-lia.patch     YF0v.v shadow_apart's last step `nia` -> `lia` (the text rules forbid nia; the goal is linear once
#                      the divisions by 8 are rewritten)
# Inputs (each named by sha):
#   REL    port_core 0e4e065eab9f: git archive 7f0e4b05267 tools/pg-reloc/0e4e065eab9f
#   DON    fuzz_grant's RELEASED lib at origin/ossv/recipes 4f87de75d67, normalised by mkdon-sm1.sh (core-A's rule):
#            mkdon-sm1.sh 4f87de75d67 $DONROOT ; DON=$DONROOT/proofs/libreac/fuzz_grant/lib
#          (lib/A/Rt/AF0r.v and AF0s.v keep their paths there, lib/Reusable/YF0v.v is YF0v.v; the three blobs are the
#          same at 25e3d17bdb50, core-A's donor commit)
#   SYMS   ../../core-reloc/A/fuzz_grant.asan.syms.txt (core-A's --old-syms, sha256 b46268790c46)
#   P, R   the pinned image trees: P holds libreac's fuzz_grant (asan c2c7559b29bd, its twin 57c26f993615), R holds
#          reac-repacer's result/ (fuzz_uci.asan 6ea017c24525 = harness.yaml, twin 56822e263d76; fuzz_uci.asan-ubsan
#          a1b86e424add)
#   LIB    proofs/reac-repacer/fuzz_uci/lib of this branch WITHOUT the three files: image A's core and start-up layer.
#          Every module the three files Require except YF0v is KEPT from it.
# Flags as core-A: --old-prog 806b0:857dc, the rename set, --reusable-dir Reusable --kernel-dir Reusable, the start-up
# files --no-stage'd.
set -uo pipefail
WORK=${1:?usage: run.sh <workdir> [extra port_core args]}; shift
HERE=$(cd "$(dirname "$0")" && pwd)
CORE=$HERE/../core-A
: "${REL:?set REL to the extracted tools/pg-reloc/0e4e065eab9f}"
: "${DON:?set DON to the normalised donor lib (mkdon-sm1.sh)}"
: "${LIB:?set LIB to proofs/reac-repacer/fuzz_uci/lib}"
: "${P:?set P to libreac's pinned image tree (bin/fuzz_grant)}"
: "${R:?set R to reac-repacer's pinned image tree (result/bin/fuzz_uci, result/unstripped/fuzz_uci)}"
SYMS=$HERE/../../core-reloc/A/fuzz_grant.asan.syms.txt
pin() { [ "$(sha256sum "$1" | cut -c1-12)" = "$2" ] || { echo "run.sh: pin mismatch: $1 is not $2" >&2; exit 5; }; }
pin "$P/bin/fuzz_grant/fuzz_grant.asan" c2c7559b29bd
pin "$R/result/bin/fuzz_uci/fuzz_uci.asan" 6ea017c24525
pin "$R/result/unstripped/fuzz_uci/fuzz_uci.asan" 56822e263d76
pin "$R/result/bin/fuzz_uci/fuzz_uci.asan-ubsan" a1b86e424add
pin "$SYMS" b46268790c46
NS=()
while read -r f; do [ -n "$f" ] && NS+=(--no-stage "$f"); done < "$CORE/not-relocated-startup-layer.txt"
python3 "$REL/port_core.py" \
  --src-lib "$DON" \
  --src-mod OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib \
  --src-images OssFuzzTheorems.libreac.fuzz_grant.images \
  --old-elf "$P/bin/fuzz_grant/fuzz_grant.asan" \
  --old-syms "$SYMS" \
  --old-prog 806b0:857dc \
  --target-lib "$LIB" \
  --target-mod OssFuzzTheorems.Proofs.reac_repacer.fuzz_uci.lib \
  --target-images OssFuzzTheorems.reac_repacer.fuzz_uci.images \
  --target-name reac-repacer/fuzz_uci \
  --target-elf "$R/result/bin/fuzz_uci/fuzz_uci.asan" \
  --target-syms "$R/result/unstripped/fuzz_uci/fuzz_uci.asan" \
  --files "$HERE/files-sm1.txt" \
  "${NS[@]}" \
  --rename GrantB=UciB --rename GrantSyms=UciSyms --rename GrantB_syms=UciB_syms --rename GrantB_ok=UciB_ok \
  --known-elf "$R/result/bin/fuzz_uci/fuzz_uci.asan-ubsan" \
  --reusable-dir Reusable --kernel-dir Reusable \
  --patch "$HERE/A-fs-ranges.patch" \
  --patch "$HERE/YF0v-lia.patch" \
  --work "$WORK" "$@"
