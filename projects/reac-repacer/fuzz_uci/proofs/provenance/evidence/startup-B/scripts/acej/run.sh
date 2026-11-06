#!/bin/sh
# fuzz_uci image B (asan-ubsan): lib/B/YCej.v, the allocation-trace universe, and YCej.universe.json (af0m's
# --universe input). Image B twin of the image-A run (uci-sg/acej/run.sh, sha256 a573ce23a396),
# which is fuzz_decode's method (commit 1148f2311f82,
# proofs/libreac/fuzz_decode/provenance/startup-gen/A/acej); the json step is fuzz_decode B's
# (7eb81ddb186 proofs/libreac/fuzz_decode/provenance/startup-gen/B/acej/ycej_json.py). rule 24: no function proved;
# no statement or contract text.
# Differences from a9's run.sh (each also in REPORT.md): image B's inputs (image, ipc, return addresses, planted pcs,
# header); cgif's released lib/YCej.v as a second emitter control; fuzz_grant B's release (commit
# 4f87de75d67 lib/B/YCej.v, YF0m.v) as a second tool / checker / members / reloc control; fuzz_decode B's committed
# lib/B/YCej.v (7eb81ddb186) as a third checker control; the lib/B namespace gate (nsB.py --grant-twin YCej) with a
# negative control; YCej.universe.json and af0m's DRV_TRACES derivation from it, each with a control and the latter
# with a negative control; the controls run before the gates they control; a wall time on every gate line.
#
#   run.sh WORK    WORK must not exist or be empty. Every generated file and log goes under WORK; nothing else is
#                  written. Each check prints "GATE <name> rc=<n> wall=<s>s" (or "NEG <name> rc=<n> ...", which must
#                  be nonzero); exit status 0 iff all pass. If out/YCej.v exists next to this script, WORK/YCej.v must
#                  equal it (same for the json), and the same against the lane's work/gen/ copies if they exist.
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
WORK=${1:?usage: run.sh WORK}
if [ -e "$WORK" ] && [ -n "$(ls -A "$WORK")" ]; then echo "run.sh: $WORK is not empty" >&2; exit 2; fi
mkdir -p "$WORK/logs" "$WORK/src" "$WORK/neg"
WORK=$(cd "$WORK" && pwd)
cd "$WORK"
export PYTHONDONTWRITEBYTECODE=1
LANE=${UCIB_W:?source the lane env file first (env.example.sh names every variable)}
export PYTHONPATH=$LANE/pylib                     # pyelftools 0.33 + capstone 5.0.7 (this host has no binutils)
PY=python3
HUB=${UCIB_OVPI:?}
TOOLS=$LANE/tools/pg-reloc/0e4e065eab9f           # = commit 7f0e4b05267 tools/pg-reloc/0e4e065eab9f (step 0)
NSB=$LANE/tools/nsB.py                            # lib/B namespace gate (port_core 0e4e's rename_text)
YG=${UCIB_YGDIR:?}   # shared kernel YG00 / YG01 (read-only): port_core 0e4e's Reusable stage-out
AF0M=${UCIB_FROZEN:?}/af0m.py   # frozen 238598b380f1 (cited)
BUN=$LANE/bundle/startup-set-8cd71d3a4bb.tsv      # commit 8cd71d3a4bb, the start-up bundle of record
GEN=$LANE/work/gen
U=${UCIB_UROOT:?}   # the reac-repacer build result root (bin/, unstripped/)
L=${UCIB_LROOT:?}   # the libreac build result root (bin/, unstripped/)
UBIN=$U/bin/fuzz_uci/fuzz_uci.asan-ubsan
USYM=$U/unstripped/fuzz_uci/fuzz_uci.asan-ubsan
GBIN=$L/bin/fuzz_grant/fuzz_grant.asan
GSYM=$L/unstripped/fuzz_grant/fuzz_grant.asan
GBBIN=$L/bin/fuzz_grant/fuzz_grant.asan-ubsan
GBSYM=$L/unstripped/fuzz_grant/fuzz_grant.asan-ubsan
DBIN=$L/bin/fuzz_decode/fuzz_decode.asan
DSYM=$L/unstripped/fuzz_decode/fuzz_decode.asan
DBBIN=$L/bin/fuzz_decode/fuzz_decode.asan-ubsan
DBSYM=$L/unstripped/fuzz_decode/fuzz_decode.asan-ubsan
X=_ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE3addEmmmm
MOD=OssFuzzTheorems.Proofs.reac_repacer.fuzz_uci.lib.Reusable
REQ="From $MOD Require Import YG00 YG01."
GMOD=OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib.Reusable
GREQ="From $GMOD Require Import YG00 YG01."
# fuzz_uci image B's measured inputs (T0.4-uci-image.md item 2, lines 94 and 96), each re-checked in step 5
UIPC="--ipc malloc=0x51a24 --ipc free=0x518c4"
URA="--expect-ra main=0x86544 --expect-ra target_alloc_init=0x7efa8 --expect-ra target_alloc_count=0x7efcc
     --expect-ra target_run=0x7efbc --expect-ra emit_printf=0x7f1f4 --expect-ra LLVMFuzzerTestOneInput=0x7f1e4
     --expect-ra check_no_overread=0x7f478 --expect-ra check_value=0x7f488 --expect-ra check_clamp=0x7f508"
UCTX="--a-ctx main=0x86544 --a-ctx target_alloc_init=0x7efa8 --a-ctx target_alloc_count=0x7efcc
      --a-ctx target_run=0x7efbc --a-ctx emit_printf=0x7f1f4 --a-ctx LLVMFuzzerTestOneInput=0x7f1e4"
UDRV='[[0x51a24; 0x7ee9c]; [0x51a24; 0x7eef0]; [0x51a24; 0x7f17c]; [0x51a24]; [0x518c4; 0x7ef14]; [0x518c4; 0x7f044]; [0x518c4; 0x7f210]; [0x518c4]]'
XU="$PY $HERE/xcheck_pcs.py --bin $UBIN --syms $USYM $UIPC --exclude $X"

now() { date +%s.%N; }
dt() { awk -v a="$1" -v b="$2" 'BEGIN { printf "%.1f", b - a }'; }
gate() {
  n=$1; shift
  t0=$(now)
  set +e; "$@" > "logs/$n.txt" 2>&1; rc=$?; set -e
  w=$(dt "$t0" "$(now)")
  cat "logs/$n.txt"
  echo "GATE $n rc=$rc wall=${w}s" | tee -a logs/gates.txt
  [ "$rc" -eq 0 ] || { echo "run.sh: gate $n failed" >&2; exit 1; }
}
neg() {
  n=$1; shift
  t0=$(now)
  set +e; "$@" > "logs/$n.txt" 2>&1; rc=$?; set -e
  w=$(dt "$t0" "$(now)")
  awk '/^planted|^FAIL|^XCHECK|^  failed| BAD | MISS | XTRA |DIFFERS|^nsB rc|^DRV /' "logs/$n.txt"
  echo "NEG $n rc=$rc wall=${w}s (must be nonzero)" | tee -a logs/gates.txt
  [ "$rc" -ne 0 ] || { echo "run.sh: negative control $n was not caught" >&2; exit 1; }
}

echo "=== 0. pins: the images, the tools of record, the Requires; the released references from the hub"
gate pins sha256sum -c "$HERE/pins.sha256"
gate bundle awk -F '\t' '$1 == "af0m.py" { print FILENAME ": " $0; f = ($2 == "238598b380f1") } END { exit !f }' "$BUN"
gate refs sh -c "
  git -C $HUB show 25e3d17bdb50:proofs/cgif/cgif_file_fuzzer/lib/YCej.v > src/cgif_YCej.v &&
  git -C $HUB show 25e3d17bdb50:proofs/cgif/cgif_file_fuzzer/lib/A/ACej.v > src/cgif_ACej.v &&
  git -C $HUB show 25e3d17bdb50:proofs/libreac/fuzz_grant/lib/A/ACej.v > src/grant_ACej.v &&
  git -C $HUB show 25e3d17bdb50:proofs/libreac/fuzz_grant/lib/A/AF0m.v > src/grant_AF0m.v &&
  git -C $HUB show 25e3d17bdb50:proofs/libreac/fuzz_grant/lib/Reusable/YG00.v > src/grant_YG00.v &&
  git -C $HUB show 25e3d17bdb50:proofs/libreac/fuzz_grant/lib/Reusable/YG01.v > src/grant_YG01.v &&
  git -C $HUB show 4f87de75d67:proofs/libreac/fuzz_grant/lib/B/YCej.v > src/grantB_YCej.v &&
  git -C $HUB show 4f87de75d67:proofs/libreac/fuzz_grant/lib/B/YF0m.v > src/grantB_YF0m.v &&
  git -C $HUB show 1148f2311f82:proofs/libreac/fuzz_decode/lib/A/ACej.v > src/decode_ACej.v &&
  git -C $HUB show 7eb81ddb186:proofs/libreac/fuzz_decode/lib/B/YCej.v > src/decodeB_YCej.v &&
  git -C $HUB show 7eb81ddb186:proofs/libreac/fuzz_decode/lib/B/YF0m.v > src/decodeB_YF0m.v &&
  git -C $HUB show 7eb81ddb186:proofs/libreac/fuzz_decode/provenance/startup-gen/B/acej/YCej.universe.json > src/decodeB_YCej.universe.json &&
  git -C $HUB show 7f0e4b05267:tools/pg-reloc/0e4e065eab9f/gen_traces.py > src/gen_traces.hub.py &&
  git -C $HUB show 7f0e4b05267:tools/pg-reloc/0e4e065eab9f/resolve_code.py > src/resolve_code.hub.py &&
  git -C $HUB show 1148f2311f82:proofs/libreac/fuzz_decode/provenance/startup-gen/A/acej/acej.py > src/decode_acej.hub.py &&
  git -C $HUB show 7eb81ddb186:proofs/libreac/fuzz_decode/provenance/startup-gen/B/acej/ycej_json.py > src/decodeB_ycej_json.hub.py &&
  test \"\$(git -C $HUB rev-parse 4f87de75d67:proofs/libreac/fuzz_grant/lib/Reusable/YG00.v 4f87de75d67:proofs/libreac/fuzz_grant/lib/Reusable/YG01.v)\" = \"\$(git -C $HUB rev-parse 25e3d17bdb50:proofs/libreac/fuzz_grant/lib/Reusable/YG00.v 25e3d17bdb50:proofs/libreac/fuzz_grant/lib/Reusable/YG01.v)\" &&
  (cd src && sha256sum -c $HERE/refs.sha256) &&
  cmp src/gen_traces.hub.py $TOOLS/gen_traces.py && cmp src/resolve_code.hub.py $TOOLS/resolve_code.py &&
  cmp src/decode_acej.hub.py $HERE/acej.py && cmp src/decodeB_ycej_json.hub.py $HERE/ycej_json.py &&
  echo 'gen_traces.py and resolve_code.py = tag 0e4e065eab9f of commit 7f0e4b05267; acej.py = the fuzz_decode emitter (1148f2311f82); ycej_json.py = the fuzz_decode B copy (7eb81ddb186); grant YG00 / YG01 blobs equal at 25e3d17bdb50 and 4f87de75d67'"

echo "=== 1. CONTROL: acej.py re-emits cgif's released lib/YCej.v (image B) and lib/A/ACej.v byte for byte"
gate control_cgif_B $PY "$HERE/acej.py" --control src/cgif_YCej.v
gate control_cgif_A $PY "$HERE/acej.py" --control src/cgif_ACej.v

echo "=== 2. CONTROL: gen_traces.py + acej.py on fuzz_grant's images reproduce grant's released Tfib_universe"
gate gen_grant sh -c "$PY $TOOLS/gen_traces.py $GBIN $GSYM --ipc malloc=0x52dec --ipc free=0x52c8c \
  --fp LLVMFuzzerTestOneInput=0x805ac --exclude $X > grant.v.txt 2> logs/gen_grant.stderr &&
  cat grant.v.txt && test ! -s logs/gen_grant.stderr && echo 'gen_traces stderr: empty'"
gate emit_grant sh -c "head -n 4 src/grant_ACej.v > grant_header.txt &&
  $PY $HERE/acej.py --data grant.v.txt --header grant_header.txt --require '$GREQ' -o grant_ACej.gen.v"
gate control_grant $PY "$HERE/compare_control.py" same grant_ACej.gen.v src/grant_ACej.v
gate gen_grantB sh -c "$PY $TOOLS/gen_traces.py $GBBIN $GBSYM --ipc malloc=0x53178 --ipc free=0x53018 \
  --fp LLVMFuzzerTestOneInput=0x80938 --exclude $X > grantB.v.txt 2> logs/gen_grantB.stderr &&
  cat grantB.v.txt && test ! -s logs/gen_grantB.stderr && echo 'gen_traces stderr: empty'"
gate emit_grantB sh -c "sed -n '/^From Stdlib/q;p' src/grantB_YCej.v > grantB_header.txt &&
  $PY $HERE/acej.py --data grantB.v.txt --header grantB_header.txt --require '$GREQ' -o grantB_YCej.gen.v"
gate control_grantB $PY "$HERE/compare_control.py" same grantB_YCej.gen.v src/grantB_YCej.v

echo "=== 3. CONTROL: the checker on fuzz_grant's (A, B) and fuzz_decode's (A, B) released / committed units"
gate xcheck_grant $PY "$HERE/xcheck_pcs.py" --bin "$GBIN" --syms "$GSYM" --acej src/grant_ACej.v \
  --ipc malloc=0x52dec --ipc free=0x52c8c --exclude $X \
  --expect-ra main=0x8bb14 --expect-ra target_alloc_init=0x80370 --expect-ra target_alloc_count=0x80394 \
  --expect-ra target_run=0x80384 --expect-ra emit_printf=0x805bc --expect-ra LLVMFuzzerTestOneInput=0x805ac
gate xcheck_grantB $PY "$HERE/xcheck_pcs.py" --bin "$GBBIN" --syms "$GBSYM" --acej src/grantB_YCej.v \
  --ipc malloc=0x53178 --ipc free=0x53018 --exclude $X \
  --expect-ra main=0x8c978 --expect-ra target_alloc_init=0x806fc --expect-ra target_alloc_count=0x80720 \
  --expect-ra target_run=0x80710 --expect-ra emit_printf=0x80948 --expect-ra LLVMFuzzerTestOneInput=0x80938
gate xcheck_decode $PY "$HERE/xcheck_pcs.py" --bin "$DBIN" --syms "$DSYM" --acej src/decode_ACej.v \
  --ipc malloc=0x52204 --ipc free=0x520a4 --ipc calloc=0x52438 --exclude $X \
  --name-map TRACES_check_round_trip_override=check_round_trip --name-map CTX_check_round_trip_stmt=check_round_trip
gate xcheck_decodeB $PY "$HERE/xcheck_pcs.py" --bin "$DBBIN" --syms "$DBSYM" --acej src/decodeB_YCej.v \
  --ipc malloc=0x52250 --ipc free=0x520f0 --ipc calloc=0x52484 --exclude $X \
  --name-map TRACES_check_round_trip_override=check_round_trip --expect-ra LLVMFuzzerTestOneInput=0x7ffac

echo "=== 4. gen_traces.py on fuzz_uci.asan-ubsan (image B); emit YCej (fuzz_decode's emitter; no --overrides, no --drop-def)"
gate gen_B sh -c "$PY $TOOLS/gen_traces.py $UBIN $USYM $UIPC --exclude $X > B.v.txt 2> logs/gen_B.stderr &&
  cat B.v.txt && test ! -s logs/gen_B.stderr && echo 'gen_traces stderr: empty'"
gate emit_B $PY "$HERE/acej.py" --data B.v.txt --header "$HERE/header-B.txt" --require "$REQ" -o YCej.gen.v
echo "--- lib/B namespace gate (nsB.py, port_core 0e4e's rename_text, grant B layout 4f87de75d67); its control first"
neg neg_ns sh -c "sed 's/^From $MOD Require Import YG00 YG01\.\$/From OssFuzzTheorems.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YG00 YG01./' YCej.gen.v > neg/ns.v &&
  ! cmp -s YCej.gen.v neg/ns.v && echo 'planted Require dir lib.Reusable -> lib.B: neg/ns.v' &&
  cd $UCIB_LT && { $PY $NSB $WORK/neg/ns.v $WORK/neg/ns.out.v --grant-twin YCej; rc=\$?; echo \"nsB rc=\$rc (3 = refused)\"; [ \$rc -eq 3 ]; } && exit 3; exit 0"
gate ns sh -c "cd $UCIB_LT && $PY $NSB $WORK/YCej.gen.v $WORK/YCej.v --grant-twin YCej"
gate ns_same sh -c "cmp YCej.gen.v YCej.v && echo 'nsB output = acej output byte for byte (already in the lib/B namespace)'"

echo "=== 5. NEGATIVE controls: one wrong pc planted at every occurrence; the checker must fail each"
neg neg_tail sh -c "$PY $HERE/plant.py YCej.v neg/tail.v 0x7f478 0x7f47c && $XU --acej neg/tail.v"
neg neg_ipc sh -c "$PY $HERE/plant.py YCej.v neg/ipc.v 0x518c4 0x518a8 &&
  $PY $HERE/xcheck_pcs.py --bin $UBIN --syms $USYM --ipc malloc=0x51a24 --ipc free=0x518a8 --exclude $X --acej neg/ipc.v"
neg neg_site sh -c "$PY $HERE/plant.py YCej.v neg/site.v 0x7f5bc 0x7f5b8 && $XU --acej neg/site.v"
echo "--- every pc of image B's YCej.v against the image (independent of gen_traces)"
gate xcheck_B $XU --acej YCej.v $URA --fn check_no_overread

echo "=== 6. members: what fuzz_uci's core asks of YCej (controls: the same check on grant's A and B releases); universe_ok; form"
gate members_grant $PY "$HERE/check_members.py" src/grant_ACej.v --yg00 src/grant_YG00.v --yg01 src/grant_YG01.v \
  --module $GMOD --drv-from src/grant_AF0m.v
gate members_grantB $PY "$HERE/check_members.py" src/grantB_YCej.v --yg00 src/grant_YG00.v --yg01 src/grant_YG01.v \
  --module $GMOD --drv-from src/grantB_YF0m.v
gate members_B $PY "$HERE/check_members.py" YCej.v --yg00 "$YG/YG00.v" --yg01 "$YG/YG01.v" --module $MOD \
  --drv "$UDRV" --row 'TRACES_check_no_overread=[0x518c4; 0x7f478]'

echo "=== 7. fuzz_uci B's driver rows and driver CTX values = fuzz_grant's released A (and B) ones at the same function offsets"
gate reloc $PY "$HERE/compare_control.py" reloc --a YCej.v --a-syms "$USYM" --b src/grant_ACej.v --b-syms "$GSYM" \
  --fn main --fn target_run $UCTX
gate reloc_grantB $PY "$HERE/compare_control.py" reloc --a YCej.v --a-syms "$USYM" --b src/grantB_YCej.v --b-syms "$GBSYM" \
  --fn main --fn target_run $UCTX

echo "=== 8. YCej.universe.json (fuzz_decode B's ycej_json.py); control: decode B's committed YCej.v re-emits its committed json"
gate json_control sh -c "$PY $HERE/ycej_json.py src/decodeB_YCej.v decodeB.universe.json &&
  cmp decodeB.universe.json src/decodeB_YCej.universe.json && echo 'CONTROL json: BYTE-EQUAL to 7eb81ddb186 provenance/startup-gen/B/acej/YCej.universe.json'"
gate json_B $PY "$HERE/ycej_json.py" YCej.v YCej.universe.json

echo "=== 9. af0m 238598b380f1's DRV_TRACES derivation from the json (its own code lines); control on decode B; negative"
gate drv_control $PY "$HERE/drv_check.py" src/decodeB_YCej.universe.json --af0m "$AF0M" --af0m-sha 238598b380f1 \
  --expect-from src/decodeB_YF0m.v --same-order
neg neg_drv $PY "$HERE/drv_check.py" YCej.universe.json --af0m "$AF0M" --af0m-sha 238598b380f1 \
  --expect "$(echo "$UDRV" | sed 's/0x7f17c/0x7f178/')"
gate drv_B $PY "$HERE/drv_check.py" YCej.universe.json --af0m "$AF0M" --af0m-sha 238598b380f1 --expect "$UDRV"

echo "=== 10. outputs"
(cd "$HERE" && sha256sum run.sh acej.py xcheck_pcs.py check_members.py compare_control.py plant.py ycej_json.py \
  drv_check.py header-B.txt pins.sha256 refs.sha256) > logs/sha256.txt
sha256sum YCej.v YCej.universe.json YCej.gen.v B.v.txt grant.v.txt grant_ACej.gen.v grantB.v.txt grantB_YCej.gen.v \
  >> logs/sha256.txt
cat logs/sha256.txt
if [ -f "$HERE/out/YCej.v" ]; then
  gate reproduce sh -c "cmp YCej.v $HERE/out/YCej.v && cmp YCej.universe.json $HERE/out/YCej.universe.json &&
    echo 'YCej.v and YCej.universe.json = out/ byte for byte'"
fi
if [ -f "$GEN/YCej.v" ]; then
  gate reproduce_gen sh -c "cmp YCej.v $GEN/YCej.v && cmp YCej.universe.json $GEN/YCej.universe.json &&
    echo 'YCej.v and YCej.universe.json = work/gen/ byte for byte'"
fi
echo "ALL GATES PASS"
