#!/bin/bash
# run_af0mB.sh -- reac-repacer/fuzz_wire image B (asan-ubsan): YF0m.v (lib/B), the twin of the fuzz_uci image-B run's
# tools/af0mB/run_af0mB.sh. rule 24: proves no function (kind: start-up facts). Run with env.sh sourced (every path is
# one of its variables).
# Tools: the start-up set of record, the start-up tool set at commit dbb5a97ad14 ($FT; af0m 238598b380f1,
# atable 42e18a7eef50, hsform a6de3be38c53), run with that directory's frozen-run.sh and an absolute bundle path.
# Base route (fuzz_decode B's relocownB.py route): port_core 0e4e065eab9f's image-B relocation of cgif's YF0m.v onto
# fuzz_wire.asan-ubsan (lib/B layout; logs/port_core.B.log) = base.YF0m.v; its Tfib_owned_static, which port_core leaves
# at cgif's numbers, re-derived by NAME by relocownWireB.py (= decode B's relocownB.py with wire paths and its n = 0
# branch) = base.patched.YF0m.v. af0m then regenerates every list and constant from the image and the 50 hand-off states.
# fuzz_wire registers 0 ASan globals (no asan_globals section): af0m takes its own n = 0 branch (no descriptor slot, no
# descriptor const_shadow cell, no owned descriptor array; Tfib_zero_shadow cited through YImgTop).
# Decisions (each with its reason):
#   --refused-drop 0x9ffd8 0x9ffc8  REAL(fclose) / REAL(fopen) = &fclose / &fopen: fuzz_wire links neither (twin nm has
#                                  no fclose / fopen / real_fclose / real_fopen); as fuzz_uci B
#   --refused-drop 0x20e23..0x20e27 cgif's global-1 redzone bytes: fuzz_wire has no global
#   (the 24 refused descriptor-word rows of cgif's 3 descriptors) af0m's descriptor slots: none for n = 0
#   --add 0x9d1c0/4 0x1323dc/4 0x13234c/4  decode B's --add list of record mapped by name (addsWB.py): asan instance+0x28,
#                                  common_flags_dont_use+0xb4 / +0x24 (the fuzz_uci runs' three cells, same order)
#   --add 0x10328/8                 decode B's SECTION row .rodata+0x58 (8fe3388ee3388ee3): fuzz_wire holds the same bytes
#                                  at the same offset, once, read by its own program code (rp_frame_channels+0x24)
#   --add 0x9a578/8                 __interception::real_strlen (twin nm 0x9a578 .data), holding musl strlen 0x921f8: the
#                                  fuzz_uci runs' REAL(strlen) row twin (pins.py stamp --pair needs A == B REAL rows);
#                                  real_memchr 0x9a5a0 and real_bcmp 0x9a598 are base rows already
set -uo pipefail
. "$W/env.sh"   # W is exported by env.sh; this brings scrub and every path variable
H=$W/tools/af0mB
L=$W/logs/af0m
mkdir -p $H/ctl $L
FAILED=
rc() { echo "$1 rc=$2"; [ "$2" = 0 ] || FAILED="$FAILED [$1]"; }

echo "=== 1 af0m CONTROL: cgif's own YF0m as base + cgif's released 50 B states (YB01 in log form) ==="
python3 $H/ab01log_B.py $DLIBC/YB01.v $LT/cgifB.YB01.log
grep -v '^#' $S/syms/cgif_file_fuzzer.asan-ubsan.nm > $LT/cgifB.recovered.nm   # a file: tr0.py re-reads it
cd $LT
$FR3 af0m.py --base $DLIBC/YF0m.v --log $LT/cgifB.YB01.log --image $CB --no-pin-owned-ro --names none \
  --out $H/ctl/YF0m.cgif.nonames.v 2>&1 | scrub > $H/ctl/control.nonames.log; rc "control (--names none)" ${PIPESTATUS[0]}
cmp $H/ctl/YF0m.cgif.nonames.v $DLIBC/YF0m.v && echo "CONTROL cgif B (--names none): BYTE-EQUAL" || { echo "CONTROL cgif B: DIFFERS"; FAILED="$FAILED [control]"; }
$FR3 af0m.py --base $DLIBC/YF0m.v --log $LT/cgifB.YB01.log --image $CB --no-pin-owned-ro \
  --names $LT/cgifB.recovered.nm --out $H/ctl/YF0m.cgif.names.v 2>&1 | scrub > $H/ctl/control.names.log
rc "control (--names cgif recovered nm)" ${PIPESTATUS[0]}
cmp $H/ctl/YF0m.cgif.names.v $DLIBC/YF0m.v && echo "CONTROL cgif B (cgif nm, TFIB_TR0 / TFIB_HASH derived): BYTE-EQUAL" || echo "CONTROL cgif B (names): DIFFERS (reported)"

echo "=== 2 base: port_core stage-out B/YF0m.v, Tfib_owned_static re-derived by name ==="
cp $LT/pcB/stage-out/B/YF0m.v $H/base.YF0m.v
(cd $H && python3 $H/relocownWireB.py 2>&1 | scrub > $L/relocownWireB.log); rc relocownWireB ${PIPESTATUS[0]}
grep -E '^(rows|IDENTITY|CONTAINMENT|relocownWireB)' $L/relocownWireB.log
(cd $H && python3 $H/addsWB.py $H/base.patched.YF0m.v 2>&1 | scrub > $L/addsWB.log); rc addsWB $?; grep '^ADD' $L/addsWB.log

echo "=== 3 provisional YB12 for --ab12 (atable 42e18a7eef50; its text does not depend on --cells) ==="
$FR3 atable.py $UB $UBs --side B --prefix $NS_D --donor-image $CB --donor-atable $DLIBC/YB12.v \
  --cells $H/base.patched.YF0m.v --header $W/tools/hdr.YB12.txt > $H/YB12.prov.v 2> >(scrub > $L/YB12.prov.log); rc "atable (provisional)" $?

echo "=== 4 af0m on fuzz_wire B ==="
MOD="copied from proofs/cgif/cgif_file_fuzzer/lib/YF0m.v (commit 25e3d17bdb50) through port_core 0e4e065eab9f's image-B relocation onto reac-repacer/fuzz_wire's asan-ubsan build (lib/B layout), its Tfib_owned_static re-derived by name from fuzz_wire.asan-ubsan (fuzz_decode B's relocownB.py rule: 37 donor rows, 33 keyed, 4 regenerated, 0 dropped; the asan_globals bounds .got pair keyed to the slots asan.module_ctor loads), then generated by af0m.py (sha256 238598b380f1, the start-up tool set at commit dbb5a97ad14) from fuzz_wire.asan-ubsan and the 50 hand-off states of its pass-2 start-up collector run (= lib/B/YB01.v): the image registers 0 ASan globals, so no descriptor slot, no descriptor const_shadow cell and no owned descriptor array; REAL(fclose) / REAL(fopen) dropped (not linked); --add cells decode B's list mapped by name, .rodata+0x58 and REAL(strlen)"
$FR3 af0m.py --base $H/base.patched.YF0m.v --log $W/logs/pass2.B.log --image $UB --twin $UBs --names $WK/nm/wireB.nmS.txt \
  --ab12 $H/YB12.prov.v --plan $WK/raw/YB05.v --universe $WK/gen/YCej.universe.json \
  --tmpl-image $CB --tmpl-af0m $DLIBC/YF0m.v \
  --refused-drop 0x9ffd8 --refused-drop 0x9ffc8 \
  --refused-drop 0x20e23 --refused-drop 0x20e24 --refused-drop 0x20e25 --refused-drop 0x20e26 --refused-drop 0x20e27 \
  --add 0x9d1c0/4 --add 0x1323dc/4 --add 0x13234c/4 --add 0x10328/8 --add 0x9a578/8 \
  --modified "$MOD" --out $WK/raw/YF0m.v 2>&1 | scrub > $L/af0m.wireB.log; rc "af0m fuzz_wire B" ${PIPESTATUS[0]}
grep -v '^frozen-run' $L/af0m.wireB.log | grep -v 'slot: refused donor descriptor word' || true
sha256sum $WK/raw/YF0m.v | scrub
[ -z "$FAILED" ] || { echo "FAILED:$FAILED"; exit 1; }
echo "YF0m generated"
