#!/bin/sh
# reac-repacer/fuzz_wire image B (asan-ubsan): lib/B/YCej.v, the allocation-trace universe, and YCej.universe.json
# (af0m's --universe input). Image-B twin of the fuzz_uci image-B run (its run.sh (sha256 7ce2eb0de04b) is not in the
# published tree; a later version, with its host paths read from the environment, is reac-repacer/fuzz_uci's released
# provenance/evidence/startup-B/scripts/acej/run.sh at recipes commit 0295462466b2), which is fuzz_decode's image-A
# method with fuzz_decode B's json step, ycej_json.py (sha256 c96a25b5daf9, not in the published tree). rule 24: no function proved;
# no statement or contract text.
# Differences from the fuzz_uci run (each also in REPORT.md): fuzz_wire image B's inputs (image, ipc, return
# addresses, planted pcs, header); fuzz_wire has no tail-call row, so the first negative control plants a wrong
# return address at a harness site (neg_ra); members uses fuzz_wire's own port_core B stage-out YG00 / YG01; the
# namespace gate is nsW.py; the start-up tool set is the start-up tool set of record, by sha256 (af0m 238598b380f1; not in the published tree); the helper
# copies are checked against the fuzz_uci commit; every host path comes from env.sh, every kept log is scrubbed, and
# hdrcheck gates (each with a negative control first) run on the outputs, this script and the logs.
#
#   . env.sh && sh run.sh WORK
#                  WORK must not exist or be empty. Every generated file and log goes under WORK; nothing else is
#                  written. WORK/logs holds the scrubbed logs (the ones to keep); WORK/raw the unscrubbed ones. Each
#                  check prints "GATE <name> rc=<n> wall=<s>s" (or "NEG <name> rc=<n> ...", which must be nonzero);
#                  exit status 0 iff all pass. If out/YCej.v exists next to this script, WORK/YCej.v must equal it
#                  (same for the json), and the same against the lane's work/gen/ copies if they exist.
set -eu
: "${W:?run.sh: source env.sh first (W is unset)}"
. "$W/env.sh"                                     # paths and the scrub filter
: "${LR:?run.sh: env.sh sets no LR}"
HERE=$(cd "$(dirname "$0")" && pwd)
WORK=${1:?usage: run.sh WORK}
if [ -e "$WORK" ] && [ -n "$(ls -A "$WORK")" ]; then echo "run.sh: $WORK is not empty" >&2; exit 2; fi
mkdir -p "$WORK/logs" "$WORK/raw" "$WORK/src" "$WORK/neg"
WORK=$(cd "$WORK" && pwd)
cd "$WORK"
export PYTHONDONTWRITEBYTECODE=1                  # PYTHONPATH (pyelftools 0.33 + capstone 5.0.7) comes from env.sh
PY=python3
TOOLS=$W/tools/pg-reloc/0e4e065eab9f              # gen_traces.py / resolve_code.py = commit 7f0e4b05267 (gate refs)
NSW=$W/tools/nsW.py                               # lib/B namespace gate (port_core 0e4e's rename_text)
HDR=$W/tools/hdrcheck.py                          # the header rule's text check
YG=$LT/pcB/stage-out/Reusable                     # fuzz_wire's port_core B stage-out: YG00 / YG01 (read-only)
AF0M=$FT/af0m.py                                  # start-up set of record, by sha256; not in the published tree
BUN=${FR3##* }                                    # that set's tsv (the last word of env.sh's FR3)
GEN=$WK/gen
UBIN=$UB
USYM=$UBs
GBIN=$LR/bin/fuzz_grant/fuzz_grant.asan
GSYM=$LR/unstripped/fuzz_grant/fuzz_grant.asan
GBBIN=$LR/bin/fuzz_grant/fuzz_grant.asan-ubsan
GBSYM=$LR/unstripped/fuzz_grant/fuzz_grant.asan-ubsan
DBIN=$LR/bin/fuzz_decode/fuzz_decode.asan
DSYM=$LR/unstripped/fuzz_decode/fuzz_decode.asan
DBBIN=$LR/bin/fuzz_decode/fuzz_decode.asan-ubsan
DBSYM=$LR/unstripped/fuzz_decode/fuzz_decode.asan-ubsan
X=_ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE3addEmmmm
MOD=$NS_U.Reusable
REQ="From $MOD Require Import YG00 YG01."
GMOD=OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib.Reusable
GREQ="From $GMOD Require Import YG00 YG01."
UCIC=883082ed41ea                                 # the fuzz_uci image-B commit whose helper copies this run uses
UCID=proofs/reac-repacer/fuzz_uci/provenance/startup-gen/B/acej
HELPERS="acej.py xcheck_pcs.py check_members.py compare_control.py drv_check.py ycej_json.py plant.py"
# fuzz_wire image B's measured inputs. ipc: the LONG-arm GetCurrentPc returns of ___interceptor_malloc /
# ___interceptor_free (xcheck section 2). Return addresses: each function's one call in the twin (xcheck section 7;
# main's = the jalr s2 in libc_start_main_stage2). DRV: TRACES_main ++ TRACES_target_run ++ [[ipc]] in fuzz_grant
# AF0m.v's form (rows grouped by ipc, malloc first). Each value is re-checked by a gate below.
UIPC="--ipc malloc=0x52334 --ipc free=0x521d4"
URA="--expect-ra main=0x87c90 --expect-ra target_alloc_init=0x7f8b8 --expect-ra target_alloc_count=0x7f8dc
     --expect-ra target_run=0x7f8cc --expect-ra emit_printf=0x7fb04 --expect-ra LLVMFuzzerTestOneInput=0x7faf4
     --expect-ra check_copy=0x7fd34 --expect-ra check_forward=0x7fcb8 --expect-ra check_ret=0x7fcc4
     --expect-ra check_downstream=0x7fcd0 --expect-ra check_meter=0x7fcdc --expect-ra check_counter=0x7fce8
     --expect-ra check_width=0x7fcf0"
UCTX="--a-ctx main=0x87c90 --a-ctx target_alloc_init=0x7f8b8 --a-ctx target_alloc_count=0x7f8dc
      --a-ctx target_run=0x7f8cc --a-ctx emit_printf=0x7fb04 --a-ctx LLVMFuzzerTestOneInput=0x7faf4"
UDRV='[[0x52334; 0x7f7ac]; [0x52334; 0x7f800]; [0x52334; 0x7fa8c]; [0x52334]; [0x521d4; 0x7f824]; [0x521d4; 0x7f954]; [0x521d4; 0x7fb20]; [0x521d4]]'
XU="$PY $HERE/xcheck_pcs.py --bin $UBIN --syms $USYM $UIPC --exclude $X"

now() { date +%s.%N; }
dt() { awk -v a="$1" -v b="$2" 'BEGIN { printf "%.1f", b - a }'; }
gate() {
  n=$1; shift
  t0=$(now)
  set +e; "$@" > "raw/$n.txt" 2>&1; rc=$?; set -e
  w=$(dt "$t0" "$(now)")
  scrub < "raw/$n.txt" > "logs/$n.txt"
  cat "logs/$n.txt"
  echo "GATE $n rc=$rc wall=${w}s" | tee -a logs/gates.txt
  [ "$rc" -eq 0 ] || { echo "run.sh: gate $n failed" >&2; exit 1; }
}
neg() {
  n=$1; shift
  t0=$(now)
  set +e; "$@" > "raw/$n.txt" 2>&1; rc=$?; set -e
  w=$(dt "$t0" "$(now)")
  scrub < "raw/$n.txt" > "logs/$n.txt"
  awk '/^planted|^FAIL|^XCHECK|^  failed| BAD | MISS | XTRA |DIFFERS|^nsW rc|^DRV |^hdrcheck:/' "logs/$n.txt"
  echo "NEG $n rc=$rc wall=${w}s (must be nonzero)" | tee -a logs/gates.txt
  [ "$rc" -ne 0 ] || { echo "run.sh: negative control $n was not caught" >&2; exit 1; }
}
stderr_log() { scrub < "raw/$1.stderr" > "logs/$1.stderr"; }
# pins.sha256 names each file by an env.sh expression ($UB, $LR/...); print that text, never the expanded path.
pins_check() {
  bad=0
  while read -r h p; do
    eval "f=$p"
    if [ "$(sha256sum < "$f" | awk '{ print $1 }')" = "$h" ]; then echo "$p: OK"; else echo "$p: FAILED"; bad=1; fi
  done < "$HERE/pins.sha256"
  return $bad
}

echo "=== 0. pins: the images, the tools of record, the core's YG00 / YG01; the released references from the hub"
gate pins pins_check
gate bundle awk -F '\t' '$1 == "af0m.py" { print "start-up set tsv (commit dbb5a97ad14): " $0; f = ($2 == "238598b380f1") } END { exit !f }' "$BUN"
SETD=$(basename "$BUN" .tsv); SETD=${SETD#startup-set-}
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
  git -C $HUB show dbb5a97ad14:tools/startup-set/$SETD/af0m.py > src/set_af0m.hub.py &&
  git -C $HUB show dbb5a97ad14:tools/startup-set/$SETD/startup-set-$SETD.tsv > src/set_tsv.hub.tsv &&
  test \"\$(git -C $HUB rev-parse 4f87de75d67:proofs/libreac/fuzz_grant/lib/Reusable/YG00.v 4f87de75d67:proofs/libreac/fuzz_grant/lib/Reusable/YG01.v)\" = \"\$(git -C $HUB rev-parse 25e3d17bdb50:proofs/libreac/fuzz_grant/lib/Reusable/YG00.v 25e3d17bdb50:proofs/libreac/fuzz_grant/lib/Reusable/YG01.v)\" &&
  (cd src && sha256sum -c $HERE/refs.sha256) &&
  cmp src/gen_traces.hub.py $TOOLS/gen_traces.py && cmp src/resolve_code.hub.py $TOOLS/resolve_code.py &&
  cmp src/decode_acej.hub.py $HERE/acej.py && cmp src/decodeB_ycej_json.hub.py $HERE/ycej_json.py &&
  cmp src/set_af0m.hub.py $AF0M && cmp src/set_tsv.hub.tsv $BUN &&
  echo 'gen_traces.py and resolve_code.py = tools/pg-reloc/0e4e065eab9f at commit 7f0e4b05267; acej.py = the fuzz_decode emitter (1148f2311f82); ycej_json.py = the fuzz_decode B copy (7eb81ddb186); af0m.py and the set tsv = tools/startup-set at commit dbb5a97ad14; grant YG00 / YG01 blobs equal at 25e3d17bdb50 and 4f87de75d67'"
gate helpers sh -c "for f in $HELPERS; do git -C $HUB show $UCIC:$UCID/\$f > src/uci_\$f && cmp src/uci_\$f $HERE/\$f &&
  echo \"\$f = $UCIC:$UCID/\$f sha256 \$(sha256sum < $HERE/\$f | cut -c1-64)\" || exit 1; done"

echo "=== 1. CONTROL: acej.py re-emits cgif's released lib/YCej.v (image B) and lib/A/ACej.v byte for byte"
gate control_cgif_B $PY "$HERE/acej.py" --control src/cgif_YCej.v
gate control_cgif_A $PY "$HERE/acej.py" --control src/cgif_ACej.v

echo "=== 2. CONTROL: gen_traces.py + acej.py on fuzz_grant's images reproduce grant's released Tfib_universe"
gate gen_grant sh -c "$PY $TOOLS/gen_traces.py $GBIN $GSYM --ipc malloc=0x52dec --ipc free=0x52c8c \
  --fp LLVMFuzzerTestOneInput=0x805ac --exclude $X > grant.v.txt 2> raw/gen_grant.stderr &&
  cat grant.v.txt && test ! -s raw/gen_grant.stderr && echo 'gen_traces stderr: empty'"
stderr_log gen_grant
gate emit_grant sh -c "head -n 4 src/grant_ACej.v > grant_header.txt &&
  $PY $HERE/acej.py --data grant.v.txt --header grant_header.txt --require '$GREQ' -o grant_ACej.gen.v"
gate control_grant $PY "$HERE/compare_control.py" same grant_ACej.gen.v src/grant_ACej.v
gate gen_grantB sh -c "$PY $TOOLS/gen_traces.py $GBBIN $GBSYM --ipc malloc=0x53178 --ipc free=0x53018 \
  --fp LLVMFuzzerTestOneInput=0x80938 --exclude $X > grantB.v.txt 2> raw/gen_grantB.stderr &&
  cat grantB.v.txt && test ! -s raw/gen_grantB.stderr && echo 'gen_traces stderr: empty'"
stderr_log gen_grantB
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

echo "=== 4. gen_traces.py on fuzz_wire.asan-ubsan (image B); emit YCej (fuzz_decode's emitter; no --overrides, no --drop-def)"
gate gen_B sh -c "$PY $TOOLS/gen_traces.py $UBIN $USYM $UIPC --exclude $X > B.v.txt 2> raw/gen_B.stderr &&
  cat B.v.txt && test ! -s raw/gen_B.stderr && echo 'gen_traces stderr: empty'"
stderr_log gen_B
gate emit_B $PY "$HERE/acej.py" --data B.v.txt --header "$HERE/header-B.txt" --require "$REQ" -o YCej.gen.v
echo "--- lib/B namespace gate (nsW.py, port_core 0e4e's rename_text, grant B layout 4f87de75d67); its control first"
neg neg_ns sh -c "sed 's/^From $MOD Require Import YG00 YG01\.\$/From $NS_U.B Require Import YG00 YG01./' YCej.gen.v > neg/ns.v &&
  ! cmp -s YCej.gen.v neg/ns.v && echo 'planted Require dir lib.Reusable -> lib.B: neg/ns.v' &&
  cd $LT && { $PY $NSW $WORK/neg/ns.v $WORK/neg/ns.out.v --grant-twin YCej; rc=\$?; echo \"nsW rc=\$rc (3 = refused)\"; [ \$rc -eq 3 ]; } && exit 3; exit 0"
gate ns sh -c "cd $LT && $PY $NSW $WORK/YCej.gen.v $WORK/YCej.v --grant-twin YCej"
gate ns_same sh -c "cmp YCej.gen.v YCej.v && echo 'nsW output = acej output byte for byte (already in the lib/B namespace, no dated notice)'"

echo "=== 5. NEGATIVE controls: one wrong pc planted at every occurrence; the checker must fail each"
neg neg_ra sh -c "$PY $HERE/plant.py YCej.v neg/ra.v 0x80c9c 0x80ca0 && $XU --acej neg/ra.v"
neg neg_ipc sh -c "$PY $HERE/plant.py YCej.v neg/ipc.v 0x521d4 0x521b8 &&
  $PY $HERE/xcheck_pcs.py --bin $UBIN --syms $USYM --ipc malloc=0x52334 --ipc free=0x521b8 --exclude $X --acej neg/ipc.v"
neg neg_site sh -c "$PY $HERE/plant.py YCej.v neg/site.v 0x7fd08 0x7fd04 && $XU --acej neg/site.v"
echo "--- every pc of image B's YCej.v against the image (independent of gen_traces)"
gate xcheck_B $XU --acej YCej.v $URA --fn LLVMFuzzerTestOneInput --fn check_copy

echo "=== 6. members: what fuzz_wire's core asks of YCej (controls: the same check on grant's A and B releases); universe_ok; form"
gate members_grant $PY "$HERE/check_members.py" src/grant_ACej.v --yg00 src/grant_YG00.v --yg01 src/grant_YG01.v \
  --module $GMOD --drv-from src/grant_AF0m.v
gate members_grantB $PY "$HERE/check_members.py" src/grantB_YCej.v --yg00 src/grant_YG00.v --yg01 src/grant_YG01.v \
  --module $GMOD --drv-from src/grantB_YF0m.v
gate members_B $PY "$HERE/check_members.py" YCej.v --yg00 "$YG/YG00.v" --yg01 "$YG/YG01.v" --module $MOD \
  --drv "$UDRV" --row 'TRACES_check_copy=[0x52334; 0x80b0c]' --row 'TRACES_check_copy=[0x521d4; 0x80c9c]' \
  --row 'TRACES_LLVMFuzzerTestOneInput=[0x52334; 0x7fc80]'

echo "=== 7. fuzz_wire B's driver rows and driver CTX values = fuzz_grant's released A (and B) ones at the same function offsets"
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
  --expect "$(echo "$UDRV" | sed 's/0x7fa8c/0x7fa88/')"
gate drv_B $PY "$HERE/drv_check.py" YCej.universe.json --af0m "$AF0M" --af0m-sha 238598b380f1 --expect "$UDRV"

echo "=== 10. the header rule on the outputs and this script (hdrcheck; control first: a planted host path)"
neg neg_hdr sh -c "{ cat YCej.v; echo '(* planted: $LT *)'; } > neg/hdr.v && $PY $HDR neg/hdr.v"
gate hdr $PY "$HDR" YCej.v YCej.universe.json "$HERE/header-B.txt" "$HERE/run.sh"

echo "=== 11. outputs"
(cd "$HERE" && sha256sum run.sh $HELPERS header-B.txt pins.sha256 refs.sha256) > logs/sha256.txt
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
gate hdr_logs sh -c "$PY $HDR logs/*.txt logs/*.stderr"
echo "ALL GATES PASS"
