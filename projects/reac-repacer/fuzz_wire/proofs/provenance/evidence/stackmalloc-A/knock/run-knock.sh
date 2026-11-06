#!/bin/sh
# The knock run of reac-repacer/fuzz_wire's image-A core (its flags unchanged), used here for ONE file: knock-files.txt
# names A/AF0s.v, fuzz_knock's released class-1 fake-stack contract, relocated onto fuzz_wire.asan only so that
# depot_classify.py --consumer can compare it with this relocation's A/Rt/AF0s.v (numerals on the same image). The
# run's output is read, never applied: its required.tsv names knock-only Requires (A.AWalkFw0, A.AF0r).
#
#   run-knock.sh <workdir>
#
#   REL  port_core release 0e4e065eab9f (as run.sh)
#   DONK libreac/fuzz_knock's released lib at the release commit 88154566652a in repository layout, NORMALISED as the grant
#        donor: Reusable/* (files and the R/, Z/ directories) moved to the lib root and the module text
#        ...fuzz_knock.lib.Reusable -> ...fuzz_knock.lib in every .v (lib/AU is not read)
#   PK   the libreac result directory: bin/fuzz_knock/fuzz_knock.asan, sha256 61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118
#        (= the release's projects/libreac/fuzz_knock/harness.yaml), its unstripped twin sha256 fff563b309575a57ef583abcb12d652ce77bc65f8952edd8dd93464602cbea25
#   P    the reac-repacer result directory (as run.sh)
#   LIB  the unit's lib with this relocation's files (A/Rt/StackMalloc0.v, StackMalloc0Tbl.v, AF0r.v, AF0s.v)
# --old-prog 7eed0:7f6bc: fuzz_knock's own code, LLVMFuzzerTestOneInput up to __wrap_getenv (the rule of run.sh's
# 806b0:857dc for fuzz_grant). fuzz_knock.asan.syms.txt: mk_old_syms.py. Renames: knock's cgif record names Tfib* -> Wire*.
set -eu
WORK=${1:?usage: run-knock.sh <workdir>}
HERE=$(cd "$(dirname "$0")" && pwd)
: "${REL:?set REL to the extracted tools/pg-reloc/0e4e065eab9f}"
: "${DONK:?set DONK to the normalised knock lib}"
: "${PK:?set PK to the libreac result directory}"
: "${P:?set P to the reac-repacer result directory}"
: "${LIB:?set LIB to proofs/reac-repacer/fuzz_wire/lib}"
OV=""; [ -f "$HERE/overrides-knock.tsv" ] && OV="--override $HERE/overrides-knock.tsv"
PA=""; for p in "$HERE"/patches-knock/*.patch; do [ -f "$p" ] && PA="$PA --patch $p"; done
set +e
# shellcheck disable=SC2086
python3 "$REL/port_core.py" \
  --src-lib    "$DONK" \
  --src-mod    OssFuzzTheorems.Proofs.libreac.fuzz_knock.lib \
  --src-images OssFuzzTheorems.libreac.fuzz_knock.images \
  --old-elf    "$PK/bin/fuzz_knock/fuzz_knock.asan" \
  --old-syms   "$HERE/fuzz_knock.asan.syms.txt" \
  --old-prog   7eed0:7f6bc \
  --target-lib    "$LIB" \
  --target-mod    OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib \
  --target-images OssFuzzTheorems.reac_repacer.fuzz_wire.images \
  --target-name   reac-repacer/fuzz_wire \
  --target-elf    "$P/bin/fuzz_wire/fuzz_wire.asan" \
  --target-syms   "$P/unstripped/fuzz_wire/fuzz_wire.asan" \
  --files      "$HERE/knock-files.txt" \
  --rename TfibB=WireB --rename TfibSyms=WireSyms \
  --rename TfibB_syms=WireB_syms --rename TfibB_ok=WireB_ok \
  $OV $PA \
  --known-elf "$P/bin/fuzz_wire/fuzz_wire.asan-ubsan" \
  --reusable-dir Reusable --kernel-dir Reusable \
  --work "$WORK"
status=$?
set -e
exit "$status"
