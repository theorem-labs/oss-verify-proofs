#!/bin/bash
# controls/run-controls-rel.sh -- re-runs the kit 86da41d3ef68's negctl.py and suite.py as run-controls.sh does, with every
# input under a relative name, so that negctl.out and planted.sha256 name no host directory. usage: run-controls-rel.sh RUN_DIR
#   RUN_DIR  holds the inputs under the relative names below (each is checked by sha256); the kit copies, the planted
#            copies and the outputs go there too. RERUN-RELATIVE.md tells what each input is.
set -euo pipefail
[ $# -eq 1 ] || { sed -n '2,5p' "$0"; exit 2; }
export PYTHONDONTWRITEBYTECODE=1
HUB="${HUB:-$(git rev-parse --show-toplevel)}"
cd "$1"; C="$(pwd)"
sha256sum -c --strict <<'EOF'
78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd  bin/fuzz_ctrl/fuzz_ctrl.asan
ee07e2c38d942e2b8934937ada9746fb6e66942335ac0a2693c398a3f0c65338  bin/fuzz_ctrl/fuzz_ctrl.asan-ubsan
04ef57cccba30736e8e7bbacaa27832e18b470f7e6235ca6a1cd77cbf4531fb2  src1/fuzz_lock/fuzz_lock.plain
56822e263d767986a76ec862cbfbee7571b0e64df2413ad18d7201205a7563fb  src1/fuzz_uci/fuzz_uci.asan
bf96847dbf1b9ab1e827610a8f10d6fff77e1406f7b1819547fd3763c6250522  src1/fuzz_uci/fuzz_uci.plain
d2f662a229626fd402f1018631498190e800834bad837fa4027204b79088b128  src1/fuzz_wire/fuzz_wire.asan
4cb0a852e8262acb5ed0fa075a6bee7b1a25192189b168e777c760a4bfd65ae2  src2/fuzz_decode/fuzz_decode.asan
18a5c8eae19bb74fbc117c13e83c703c4c6c96007627c4d957601805c6ef78fa  src2/fuzz_decode/fuzz_decode.plain
c90d4fa54d43160baf62e5aa387211a798dddbad13d2619d85acbf37aee0c175  src3/fuzz_preset/fuzz_preset.asan-ubsan
3b5e1a099b535acf2c4e81d857fed63daaf3cf5e758d7fe50834a6bd419c3c58  src4/fuzz_preset/fuzz_preset.asan-ubsan
67d7e481d74edac58be0e018835f577491192d461b4a35bd4109dc4ab0494fd5  src5/fuzz_frame/fuzz_frame.asan
EOF
mkdir kitrun oldkit xchk e548 driver
git -C "$HUB" archive 98e50c029045 tools/cmpkit/86da41d3ef68 | tar -x -C kitrun --strip-components=3
git -C "$HUB" archive 3c3e62ee278 tools/cmpkit/4bbd3a74be89 | tar -x -C oldkit --strip-components=3
git -C "$HUB" archive f69e6d74ebe tools/repin_check/e5487165abb8/repin_check.py | tar -x -C e548 --strip-components=3
(cd kitrun && sha256sum -c SHA256SUMS) && (cd oldkit && sha256sum -c SHA256SUMS)
echo 'e5487165abb8dfb7a39518a418fc24a0e815cea74918943bafbf35667c70ed11  e548/repin_check.py' | sha256sum -c --strict
cp -a oldkit/. xchk/ && cp kitrun/controls/xchk/jtcheck_strict2.py xchk/   # the cross-check jtcheck
# The drivers: the kit's controls/negctl.py and controls/suite.py (not members of the kit's SHA256SUMS). In the copies,
# each host path constant is a relative name and each lane name (in comments and in three plant labels) is <agent>;
# suite.py keeps OUT and PLANTED_DIR relative, and KIT stays absolute, because the tools run with their own directory
# as cwd. negctl-rel.py and suite-rel.py beside this script are these copies, byte for byte (the sha256s below).
K=kitrun/controls
LANE=(-e 's#\bh-[a-z0-9][a-z0-9-]*[a-z0-9]#<agent>#g' -e 's#([a-z]-[a-z]* 15:19Z)#(<agent> 15:19Z)#')
sed -e "s#^S = '[^']*'\$#S = 'driver'#" -e "s#^E548 = '[^']*'\$#E548 = 'e548/repin_check.py'#" "${LANE[@]}" \
    $K/negctl.py > $K/negctl-rel.py
sed -e 's#^KIT, OUT, PL = (os.path.abspath(x) for x in sys.argv\[1:4\])$#KIT, OUT, PL = os.path.abspath(sys.argv[1]), sys.argv[2], sys.argv[3]#' \
    -e "s#^R = '[^']*'\$#R = 'src1'#" \
    -e "s#^E548 = '[^']*'\$#E548 = 'e548/repin_check.py'#" \
    -e "s#^CU = '[^']*'; #CU = 'bin/fuzz_ctrl'; #" \
    -e "s#^\\(WA, DA = R + '/fuzz_wire/fuzz_wire.asan', \\)'[^']*'\$#\\1'src2/fuzz_decode/fuzz_decode.asan'#" \
    -e "s#^PO = '[^']*'\$#PO = 'src4/fuzz_preset/fuzz_preset.asan-ubsan'#" \
    -e "s#^PN = '[^']*'\$#PN = 'src3/fuzz_preset/fuzz_preset.asan-ubsan'#" \
    "${LANE[@]}" $K/suite.py > $K/suite-rel.py
n1=$(diff $K/negctl.py $K/negctl-rel.py | grep -c '^>' || true); n2=$(diff $K/suite.py $K/suite-rel.py | grep -c '^>' || true)
[ "$n1 $n2" = '3 21' ] || { echo "the driver substitution changed $n1 / $n2 lines, not 3 / 21" >&2; exit 1; }
sha256sum -c --strict <<'EOF'
287d2110aff0ad195b4470f98e53e40f85b88264be2e29a40a9fe939c40c3c8f  kitrun/controls/negctl-rel.py
a7f357899752b6bfc2a2a27dc4d27c69361b33c7eee251ff4827485e22822a2a  kitrun/controls/suite-rel.py
EOF
echo 'FA=src5/fuzz_frame/fuzz_frame.asan; DA=src2/fuzz_decode/fuzz_decode.asan; DP=src2/fuzz_decode/fuzz_decode.plain' > driver/env.sh
# a tool runs with its own directory as cwd: there each relative name leads to the same file as in RUN_DIR
for d in kitrun oldkit xchk; do for n in bin src1 src2 src3 src4 planted suite-out; do ln -s ../$n $d/$n; done; done
python3 $K/negctl-rel.py kitrun > negctl.out
SUITE_OLD_KIT="$C/oldkit" SUITE_XCHK_JT="$C/xchk/jtcheck_strict2.py" python3 $K/suite-rel.py kitrun suite-out planted "${JOBS:-16}"
