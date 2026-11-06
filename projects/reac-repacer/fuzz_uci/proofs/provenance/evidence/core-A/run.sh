#!/bin/sh
# Reproduce reac-repacer/fuzz_uci's image-A core relocation, byte for byte, header rule included.
#
#   run.sh <workdir>
#
# The method is libreac/fuzz_decode's (its core at commit 1148f2311f8, provenance/core-reloc/A/run.sh): the DONOR is
# fuzz_grant's RELEASED lib (fuzz_uci's driver and runtime are grant's), not cgif's. Agreed by the unit owner after
# measuring both on the same trunk with the same tool: cgif donor 218 refused values / 236 rows, grant donor 100
# refused / 101 value rows.
#
#   REL  port_core release 0e4e065eab9f: git -C <hub> archive 7f0e4b05267 tools/pg-reloc/0e4e065eab9f | tar -x -C X
#        (versions.txt beside this file: port_core / resolve_code / gen_traces / adapted.patch / symbol gate shas)
#   DON  fuzz_grant's released lib at origin/ossv/recipes 25e3d17bdb50, NORMALISED as decode's run.sh does (Reusable/*
#        moved to the lib root, module text ...fuzz_grant.lib.Reusable -> ...fuzz_grant.lib), in repository layout:
#          mkdir -p $D/proofs/libreac/fuzz_grant/lib && git -C <hub> archive 25e3d17bdb50 proofs/libreac/fuzz_grant/lib \
#            | tar -x -C $D/proofs/libreac/fuzz_grant/lib --strip-components=4
#          cd $D/proofs/libreac/fuzz_grant/lib && mv Reusable/* . && rmdir Reusable && find . -name '*.v' -print0 | xargs -0 \
#            perl -pi -e 's/OssFuzzTheorems\.Proofs\.libreac\.fuzz_grant\.lib\.Reusable/OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib/g'
#        DON=$D/proofs/libreac/fuzz_grant/lib
#   PG   directory of fuzz_grant's ORIGINAL images: bin/fuzz_grant/fuzz_grant.asan (pin sha256 c2c7559b29bd)
#   P    directory of fuzz_uci's ORIGINAL images (the reac-repacer build's result/): bin/fuzz_uci/fuzz_uci.asan (pin
#        sha256 6ea017c24525), unstripped/fuzz_uci/fuzz_uci.asan (pin 56822e263d76), bin/fuzz_uci/fuzz_uci.asan-ubsan
#        (pin a1b86e424add)
#   SYMS fuzz_grant.asan's symbols (default: provenance/core-reloc/A/fuzz_grant.asan.syms.txt, pin b46268790c46,
#        libreac/fuzz_decode's file)
#   LIB  the unit's lib (proofs/reac-repacer/fuzz_uci/lib) holding the trunk (TRUNK-SEED.md), the files taken by path
#        (taken-by-path.txt) and the start-up layer (not-relocated-startup-layer.txt: generated, provenance/startup-gen/A).
#
# port_core ends with status 3 for ONE row, `rename-new-undeclared` (UciSyms "declared by none, staged or kept"): UciSyms
# is declared by LIB's A/AF0m.v, a start-up-layer file this run does not stage, and the check reads only staged and kept
# non-A files. So --apply is not used; the staged files of WORK/stage-out go into LIB by --apply's own rule (A/ files
# always, a non-A file only when LIB lacks it).
# The two patches zero-shadow-forallb.patch and cell-lookup.patch are libreac/fuzz_decode's (its core at commit
# 1148f2311f8), re-cut against this run's stage-out (AFjy's context bound 0x5f6000 -> fuzz_uci's 0x5f4000): the
# Tfib_zero_shadow case splits become forallb checks (fuzz_uci has 3 ranges, grant 15), and the AFim / AFin const-cell
# lookups by index become cell_lookup_In. ad1q-shape.patch gives A/AD1q.v fuzz_uci's own lib_shape instance.
#
# Header rule: after port_core, header_rule.py (beside this file) rewrites the comments of every staged file in
# WORK/stage-out: the donor's and port_core's dated `Modified by Theorem Labs, <date>:` notices lose their date, and an
# absolute path to a repository file becomes repository-relative. It changes no text outside comments and refuses
# (status 4) if a comment still names a host path, an agent, a date or a lane branch. The run's status is port_core's.
set -eu
WORK=${1:?usage: run.sh <workdir>}
HERE=$(cd "$(dirname "$0")" && pwd)
: "${REL:?set REL to the extracted tools/pg-reloc/0e4e065eab9f}"
: "${DON:?set DON to the normalised grant lib}"
: "${PG:?set PG to the directory of fuzz_grant's ORIGINAL images}"
: "${P:?set P to the directory of fuzz_uci's ORIGINAL images (result/)}"
: "${SYMS:=$HERE/../../core-reloc/A/fuzz_grant.asan.syms.txt}"
: "${LIB:?set LIB to proofs/reac-repacer/fuzz_uci/lib}"
pin() { [ "$(sha256sum "$1" | cut -c1-12)" = "$2" ] || { echo "run.sh: pin mismatch: $1 is not $2" >&2; exit 5; }; }
pin "$PG/bin/fuzz_grant/fuzz_grant.asan" c2c7559b29bd
pin "$P/bin/fuzz_uci/fuzz_uci.asan" 6ea017c24525
pin "$P/unstripped/fuzz_uci/fuzz_uci.asan" 56822e263d76
pin "$P/bin/fuzz_uci/fuzz_uci.asan-ubsan" a1b86e424add
pin "$SYMS" b46268790c46
NS=""
while read -r f; do [ -n "$f" ] && NS="$NS --no-stage $f"; done < "$HERE/not-relocated-startup-layer.txt"
set +e
# shellcheck disable=SC2086
python3 "$REL/port_core.py" \
  --src-lib    "$DON" \
  --src-mod    OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib \
  --src-images OssFuzzTheorems.libreac.fuzz_grant.images \
  --old-elf    "$PG/bin/fuzz_grant/fuzz_grant.asan" \
  --old-syms   "$SYMS" \
  --old-prog   806b0:857dc \
  --target-lib    "$LIB" \
  --target-mod    OssFuzzTheorems.Proofs.reac_repacer.fuzz_uci.lib \
  --target-images OssFuzzTheorems.reac_repacer.fuzz_uci.images \
  --target-name   reac-repacer/fuzz_uci \
  --target-elf    "$P/bin/fuzz_uci/fuzz_uci.asan" \
  --target-syms   "$P/unstripped/fuzz_uci/fuzz_uci.asan" \
  --files      "$HERE/core-files-uci.txt" \
  $NS \
  --rename GrantB=UciB --rename GrantSyms=UciSyms \
  --rename GrantB_syms=UciB_syms --rename GrantB_ok=UciB_ok \
  --override "$HERE/overrides.tsv" \
  --patch    "$HERE/zero-shadow-forallb.patch" \
  --patch    "$HERE/cell-lookup.patch" \
  --patch    "$HERE/ad1q-shape.patch" \
  --known-elf "$P/bin/fuzz_uci/fuzz_uci.asan-ubsan" \
  --reusable-dir Reusable --kernel-dir Reusable \
  --work "$WORK"
status=$?
set -e
python3 "$HERE/header_rule.py" "$WORK/stage-out" || exit 4
exit "$status"
