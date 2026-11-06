#!/bin/bash
# run_af0mB.sh -- reac-repacer/fuzz_uci image B (asan-ubsan): YF0m.v (lib/B), the B twin of the image-A
# uci-sg/start/af0m/run_af0m.sh. rule 24: proves no function (kind: start-up facts).
# Tools: the corrected start-up set of record, commit dbb5a97ad14 (af0m 238598b380f1,
# atable 42e18a7eef50; run with that directory's frozen-run.sh and an absolute bundle path). The first
# generation ran on commit 8cd71d3a4bb's earlier set (af0m 238598b380f1, atable 2d236e51ad70).
# Base route (the brief's "decode B's relocownB.py route"): port_core 0e4e065eab9f's image-B relocation of cgif's
# YF0m.v onto fuzz_uci.asan-ubsan (lib/B layout; logs/port_core.B.log) = base.YF0m.v; its Tfib_owned_static, which
# port_core leaves at cgif's numbers, re-derived by NAME by relocownUciB.py (= decode B's relocownB.py with uci paths)
# = base.patched.YF0m.v. af0m then regenerates every list and constant from the image and the 50 hand-off states.
# Decisions (each with its reason):
#   --refused-map 0x9ee98=0x97da0  cgif's .got slot holding &asan_globals (port_core got-word-unresolved): fuzz_uci's .got
#                                  slot holding its asan_globals start 0x9b9d0 is 0x97da0 (relocownUciB owned[21], keyed
#                                  POINTER asan_globals+0 / one-past end; base row 0x97da8 = 0x9ba10 beside it)
#   --refused-drop 0x9ff40          REAL(bcmp) = &bcmp: fuzz_uci.asan-ubsan defines neither bcmp nor real_bcmp (twin nm),
#                                  as a9's image-A --refused-drop 0x9e590 (NOTES D2)
#   --refused-drop 0x9ffd8 0x9ffc8  REAL(fclose) / REAL(fopen) = &fclose / &fopen: fuzz_uci links neither (port_core
#                                  deleted FF_got_fclose / FF_got_fopen with their uses in YE2k; grant's AF0m has neither row)
#   --refused-drop 0x20e23..0x20e27 cgif's global-1 redzone bytes: fuzz_uci has one global; its redzone tail
#                                  (0x20ca8, 0x18) is owned and pinned by af0m's default rule
#   (the 23 other refused rows)     cgif's 3 descriptors' words: af0m's descriptor slots (8 take fuzz_uci's 1 descriptor)
#   --add 0x9bac0/4 0x130cdc/4 0x130c4c/4   decode B's --add list of record mapped by name (addsB.py; a9's image-A
#                                  adds are the same three cells: asan instance+0x28, common_flags_dont_use+0xb4 / +0x24)
#   --add 0x20ca8/8 0x20cb0/8 0x20cb8/8     MARGIN_MAX's redzone tail pins (= 0, image bytes), passed in the order af0m's
#                                  pin pass wrote them in the first generation (rows 213-215), so the later --add cannot push
#                                  them down; the pin pass then appends nothing (a9's image-A rule, run_af0m.sh:29-33)
#   --add 0x98e28/8                 __interception::real_strlen (twin nm 0x98e28 size 8 .data), holding musl strlen 0x90aa8
#                                  (twin nm `strlen`; the pin's word at 0x98e28): the strlen wrapper walk reads it;
#                                  image A's AF0m carries the A twin 0x98d20 = 0x909a0,
#                                  and `pins.py stamp --pair` refuses REAL rows A != B without it. Row 216, the last;
#                                  rows 0..215 keep the first generation's indices.
set -euo pipefail
: "${UCIB_UB:?source the lane env file first (env.example.sh names every variable)}"
H=$W/tools/af0mB
mkdir -p $H/ctl $W/logs/af0m
cd $H
FAILED=
rc() { echo "$1 rc=$2"; [ "$2" = 0 ] || FAILED="$FAILED [$1]"; }

echo "=== 1 af0m CONTROL: cgif's own YF0m as base + cgif's released 50 B states (YB01 in log form) ==="
set +e
python3 $H/ab01log_B.py $DLIBC/YB01.v $LT/cgifB.YB01.log
grep -v '^#' $S/syms/cgif_file_fuzzer.asan-ubsan.nm > $LT/cgifB.recovered.nm   # a file: tr0.py re-reads it
cd /tmp
$FR3 af0m.py --base $DLIBC/YF0m.v --log $LT/cgifB.YB01.log --image $CB --no-pin-owned-ro --names none \
  --out $H/ctl/YF0m.cgif.nonames.v > $H/ctl/control.nonames.log 2>&1; rc "control (--names none)" $?
cmp $H/ctl/YF0m.cgif.nonames.v $DLIBC/YF0m.v && echo "CONTROL cgif B (--names none): BYTE-EQUAL" || { echo "CONTROL cgif B: DIFFERS"; FAILED="$FAILED [control]"; }
$FR3 af0m.py --base $DLIBC/YF0m.v --log $LT/cgifB.YB01.log --image $CB --no-pin-owned-ro \
  --names $LT/cgifB.recovered.nm --out $H/ctl/YF0m.cgif.names.v > $H/ctl/control.names.log 2>&1
rc "control (--names cgif recovered nm)" $?
cmp $H/ctl/YF0m.cgif.names.v $DLIBC/YF0m.v && echo "CONTROL cgif B (cgif nm, TFIB_TR0 / TFIB_HASH derived): BYTE-EQUAL" || echo "CONTROL cgif B (names): DIFFERS (reported)"
set -e
cd $H

echo "=== 2 base: port_core stage-out B/YF0m.v, Tfib_owned_static re-derived by name ==="
cp $LT/pcB/stage-out/B/YF0m.v $H/base.YF0m.v
python3 $H/relocownUciB.py > $W/logs/af0m/relocownUciB.log 2>&1; rc relocownUciB $?
grep -E '^(rows|IDENTITY|CONTAINMENT)' $W/logs/af0m/relocownUciB.log
python3 $H/addsB.py $H/base.patched.YF0m.v > $W/logs/af0m/addsB.log 2>&1; rc addsB $?; tail -1 $W/logs/af0m/addsB.log

echo "=== 3 provisional YB12 for --ab12 (atable 42e18a7eef50; its text does not depend on --cells) ==="
cd /tmp
$FR3 atable.py $UB $UBs --side B --prefix $NS_D --donor-image $CB --donor-atable $DLIBC/YB12.v \
  --cells $H/base.patched.YF0m.v --header $W/tools/hdr.YB12.txt > $H/YB12.prov.v 2> $W/logs/af0m/YB12.prov.log; rc "atable (provisional)" $?

echo "=== 4 af0m on fuzz_uci B ==="
MOD="copied from proofs/cgif/cgif_file_fuzzer/lib/YF0m.v (commit 25e3d17bdb50) through port_core 0e4e065eab9f's image-B relocation onto reac-repacer/fuzz_uci's asan-ubsan build (lib/B layout), its Tfib_owned_static re-derived by name from fuzz_uci.asan-ubsan (fuzz_decode B's relocownB.py rule: 37 donor rows, 33 keyed, 4 regenerated, 0 dropped), then generated by af0m.py (frozen 238598b380f1, start-up tool set of commit dbb5a97ad14) from fuzz_uci.asan-ubsan and the 50 hand-off states of its pass-2 start-up collector run (= lib/B/YB01.v): the 1 asan_globals descriptor at 0x9b9d0 (MARGIN_MAX, all 8 fields; the 16 other descriptor-word slots of cgif's 3 descriptors hold duplicates so no index moves), its redzone and metadata shadow, the zero-shadow ranges, the redzone tail (0x20ca8, 0x18) owned and pinned, TFIB_TR0 / TFIB_HASH from tr0.py on this image, DRV_TRACES from lib/B/YCej's universe; REAL(bcmp) / REAL(fopen) / REAL(fclose) and cgif's second global's redzone bytes dropped (fuzz_uci has none), three runtime cells added by name (fuzz_decode B's list of record), and REAL(strlen) (the strlen wrapper walk reads it; image A carries its twin)."
$FR3 af0m.py --base $H/base.patched.YF0m.v --log $W/logs/pass2.B.log --image $UB --twin $UBs --names $WK/nm/uciB.nmS.txt \
  --ab12 $H/YB12.prov.v --plan $WK/raw/YB05.v --universe $WK/gen/YCej.universe.json \
  --tmpl-image $CB --tmpl-af0m $DLIBC/YF0m.v \
  --refused-map 0x9ee98=0x97da0 --refused-drop 0x9ff40 --refused-drop 0x9ffd8 --refused-drop 0x9ffc8 \
  --refused-drop 0x20e23 --refused-drop 0x20e24 --refused-drop 0x20e25 --refused-drop 0x20e26 --refused-drop 0x20e27 \
  --add 0x9bac0/4 --add 0x130cdc/4 --add 0x130c4c/4 \
  --add 0x20ca8/8 --add 0x20cb0/8 --add 0x20cb8/8 --add 0x98e28/8 \
  --modified "$MOD" --out $WK/raw/YF0m.v > $W/logs/af0m/af0m.uciB.log 2>&1; rc "af0m fuzz_uci B" $?
grep -v '^frozen-run' $W/logs/af0m/af0m.uciB.log | grep -v 'slot: refused donor descriptor word' || true
cd $H
sha256sum $WK/raw/YF0m.v
[ -z "$FAILED" ] || { echo "FAILED:$FAILED"; exit 1; }
echo "YF0m generated"
