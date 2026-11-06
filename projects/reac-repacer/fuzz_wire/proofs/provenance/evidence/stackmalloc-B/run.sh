#!/bin/bash
# Reproduce reac-repacer/fuzz_wire's IMAGE-B __asan_stack_malloc_0 / _1 contract relocation: lib/B/Rt/StackMalloc0.v,
# lib/B/Rt/StackMalloc0Tbl.v, lib/B/Rt/YF0r.v, lib/B/Rt/YF0s.v and the shared lib/Reusable/YF0v.v they Require.
#
#   run.sh <workdir> [extra port_core args]      then apply-smB.sh <workdir> <LIB> (copy, nothing overwritten, licence
#                                                lines removed)
#
# The flags are those of the unit's image-B core run of record (../core-B/run.sh); what differs:
#   --files       files-smB.txt (the donor Rt paths and YF0v.v), instead of core-B's files-B-core.txt
#   --override    overrides-smB.tsv (values no port_core rule decides; each measured by role in numerals-smB.tsv)
#   --patch       B-smB.patch (YF0r.v's code table without the rows of the classes fuzz_wire does not link)
#   core-B's own --override / --patch rows name core files only, so they are not passed.
#   OVERRIDES=0 / PATCHES=0 in the environment leave the overrides / the patch out (the first run, whose refusals
#   and outputs the numeral table reads).
# Inputs (each named by sha256):
#   REL    port_core 0e4e065eab9f (port_core.py sha256 0e4e065eab9f9a67): git archive 7f0e4b05267 tools/pg-reloc/0e4e065eab9f
#          (resolve_code.py 81803218fe79, gen_traces.py a78026af1ae2, adapted.patch 27bb43cc1436)
#   DON    fuzz_grant's RELEASED lib at recipes 4f87de75d67, normalised by ../core-B/mkdon.sh (as core-B):
#            mkdon.sh 4f87de75d67 fuzz_grant B $DONROOT ; DON=$DONROOT/proofs/libreac/fuzz_grant/lib
#   SYMS   ../core-B/fuzz_grant.asan-ubsan.syms.txt (the donor's unstripped twin 5a5ee7c02b4e)
#   P, R   the pinned image trees: P holds libreac's fuzz_grant (bin/fuzz_grant/fuzz_grant.asan-ubsan fde52226dc48,
#          bin/fuzz_grant/fuzz_grant.asan c2c7559b29bd), R holds reac-repacer's result/ (bin/fuzz_wire/fuzz_wire.asan-ubsan
#          af4534831a45 = harness.yaml, unstripped/fuzz_wire/fuzz_wire.asan-ubsan 51eb4bef2425, bin/fuzz_wire/fuzz_wire.asan
#          2f8f8697cd4f)
#   LIB    the unit's lib (projects/reac-repacer/fuzz_wire/proofs/lib) WITHOUT the five files: every module they Require
#          except YF0v is KEPT from it.
set -uo pipefail
WORK=${1:?usage: run.sh <workdir> [extra port_core args]}; shift
HERE=$(cd "$(dirname "$0")" && pwd)
CORE=$HERE/../core-B
: "${REL:?set REL to the extracted tools/pg-reloc/0e4e065eab9f}"
: "${DON:?set DON to the normalised donor lib (core-B/mkdon.sh)}"
: "${LIB:?set LIB to the unit lib}"
: "${P:?set P to libreac's pinned image tree (bin/fuzz_grant)}"
: "${R:?set R to reac-repacer's pinned image tree (result/bin/fuzz_wire, result/unstripped/fuzz_wire)}"
NS=()
while read -r f; do [ -n "$f" ] && NS+=(--no-stage "$f"); done < "$CORE/no-stage-B.txt"
EXTRA=()
[ "${OVERRIDES:-1}" = 0 ] || EXTRA+=(--override "$HERE/overrides-smB.tsv")
[ "${PATCHES:-1}" = 0 ] || EXTRA+=(--patch "$HERE/B-smB.patch")
python3 "$REL/port_core.py" \
  --src-lib "$DON" \
  --src-mod OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib \
  --src-images OssFuzzTheorems.libreac.fuzz_grant.images \
  --old-elf "$P/bin/fuzz_grant/fuzz_grant.asan-ubsan" \
  --old-syms "$CORE/fuzz_grant.asan-ubsan.syms.txt" \
  --old-prog 80a3c:86640 \
  --target-lib "$LIB" \
  --target-mod OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib \
  --target-images OssFuzzTheorems.reac_repacer.fuzz_wire.images \
  --target-name reac-repacer/fuzz_wire \
  --target-elf "$R/result/bin/fuzz_wire/fuzz_wire.asan-ubsan" \
  --target-syms "$R/result/unstripped/fuzz_wire/fuzz_wire.asan-ubsan" \
  --files "$HERE/files-smB.txt" \
  "${NS[@]}" \
  --rename GrantB=WireB --rename GrantSyms=WireSyms --rename GrantB_syms=WireB_syms --rename GrantB_ok=WireB_ok \
  --remap-images --reusable-dir B --kernel-dir Reusable \
  --kernel-image "$P/bin/fuzz_grant/fuzz_grant.asan" \
  --known-elf "$R/result/bin/fuzz_wire/fuzz_wire.asan" \
  --known-elf "$P/bin/fuzz_grant/fuzz_grant.asan" \
  "${EXTRA[@]}" \
  --work "$WORK" "$@"
