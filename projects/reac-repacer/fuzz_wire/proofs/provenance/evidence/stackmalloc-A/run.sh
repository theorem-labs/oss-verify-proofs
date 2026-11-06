#!/bin/sh
# Relocate fuzz_grant's released fake-stack contracts (lib/A/Rt: StackMalloc0.v, StackMalloc0Tbl.v, AF0r.v, AF0s.v, and
# the shared lib/Reusable/YF0v.v that StackMalloc0.v and AF0s.v Require, which the unit's lib/Reusable lacked) onto
# reac-repacer/fuzz_wire's image A with port_core 0e4e065eab9f: the flags of image A's core run, with --files =
# files.txt and one patch:
#   A-fs-ranges.patch  AF0r.v's code table without fuzz_grant's __asan_stack_malloc_2 / _4 rows (port_core refuses
#                      them, code-no-counterpart: fuzz_wire.asan links classes 0 and 1 only)
#
#   run.sh <workdir> [extra port_core flags]      then sm_apply.py <workdir> <the unit's lib> <list>
#
#   REL  port_core 0e4e065eab9f: `git archive 7f0e4b05267 tools/pg-reloc/0e4e065eab9f`
#   DON  fuzz_grant's released lib at the release commit 4f87de75d67 in repository layout, normalised as the core
#        run's: Reusable/* moved to the lib root, module text ...fuzz_grant.lib.Reusable -> ...fuzz_grant.lib (the 5
#        files' blobs are the same at 98c99a85e4)
#   PG   the libreac result directory (bin/fuzz_grant/fuzz_grant.asan sha256 c2c7559b29bd)
#   P    the reac-repacer result directory (bin/fuzz_wire/fuzz_wire.asan 2f8f8697cd4f, unstripped twin d2f662a22962,
#        bin/fuzz_wire/fuzz_wire.asan-ubsan af4534831a45)
#   LIB  the unit's lib (projects/reac-repacer/fuzz_wire/proofs/lib) at the base commit a3f9509d24de, without the 5 files
# Beside this script: files.txt, A-fs-ranges.patch, fuzz_grant.asan.syms.txt (the core run's --old-syms, sha256
# ed0cf498789c) and not-relocated-startup-layer.txt (the core run's --no-stage list, sha256 0f4837905d40).
set -eu
WORK=${1:?usage: run.sh <workdir> [flags]}; shift
HERE=$(cd "$(dirname "$0")" && pwd)
: "${REL:?}"; : "${DON:?}"; : "${PG:?}"; : "${P:?}"; : "${LIB:?}"
pin() { [ "$(sha256sum < "$1" | cut -c1-12)" = "$2" ] || { echo "run.sh: pin mismatch: $1 is not $2" >&2; exit 5; }; }
pin "$REL/port_core.py" 0e4e065eab9f
pin "$PG/bin/fuzz_grant/fuzz_grant.asan" c2c7559b29bd
pin "$P/bin/fuzz_wire/fuzz_wire.asan" 2f8f8697cd4f
pin "$P/unstripped/fuzz_wire/fuzz_wire.asan" d2f662a22962
pin "$P/bin/fuzz_wire/fuzz_wire.asan-ubsan" af4534831a45
pin "$HERE/fuzz_grant.asan.syms.txt" ed0cf498789c
pin "$HERE/not-relocated-startup-layer.txt" 0f4837905d40
NS=""
while read -r f; do [ -n "$f" ] && NS="$NS --no-stage $f"; done < "$HERE/not-relocated-startup-layer.txt"
set +e
# shellcheck disable=SC2086
python3 "$REL/port_core.py" \
  --src-lib    "$DON" \
  --src-mod    OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib \
  --src-images OssFuzzTheorems.libreac.fuzz_grant.images \
  --old-elf    "$PG/bin/fuzz_grant/fuzz_grant.asan" \
  --old-syms   "$HERE/fuzz_grant.asan.syms.txt" \
  --old-prog   806b0:857dc \
  --target-lib    "$LIB" \
  --target-mod    OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib \
  --target-images OssFuzzTheorems.reac_repacer.fuzz_wire.images \
  --target-name   reac-repacer/fuzz_wire \
  --target-elf    "$P/bin/fuzz_wire/fuzz_wire.asan" \
  --target-syms   "$P/unstripped/fuzz_wire/fuzz_wire.asan" \
  --files      "$HERE/files.txt" \
  $NS \
  --rename GrantB=WireB --rename GrantSyms=WireSyms \
  --rename GrantB_syms=WireB_syms --rename GrantB_ok=WireB_ok \
  --known-elf "$P/bin/fuzz_wire/fuzz_wire.asan-ubsan" \
  --reusable-dir Reusable --kernel-dir Reusable \
  --patch "$HERE/A-fs-ranges.patch" \
  --work "$WORK" "$@"
status=$?
set -e
exit "$status"
