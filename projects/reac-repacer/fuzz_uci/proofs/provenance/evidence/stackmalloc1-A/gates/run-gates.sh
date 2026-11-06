#!/bin/bash
# run-gates.sh <gatedir>: every gate of this slice over the three committed files, each control beside its run; raw
# outputs to <gatedir> (records-sm1.py turns them into ../records/). The cb build (gate 5) runs on the build VM: GATES.md.
# The image-B record's gates/run-gates.sh with image B -> image A, the flag gate on port_addr_check efa19b81e92b of record
# (e165063a0081 beside it), and two planted pointers (a code and a data pointer) for the flag gate.
# Environment (each tool named by sha; nothing here depends on a host path the tree names):
#   P, R      the pinned image trees (run.sh)            WORK  run.sh's work dir (stage/ = the renamed donor text)
#   LIB       proofs/reac-repacer/fuzz_uci/lib            CORE  proofs/reac-repacer/fuzz_uci
#   DON       the normalised donor lib (mkdon-sm1.sh)     DONREL  `git archive 4f87de75d67` of the 3 released donor files
#   CKDIR     the directory holding versions/<sha12>/port_addr_check.py (efa19b81e92b, e165063a0081)
#   SET       the start-up tool set 2026-10-30 of record (its frozen-run.sh, codeptr 12348302dfd2,
#             keyset f050b43e480e, atable 42e18a7eef50)
#   GS        global_settings.py 439f8e3bd463 (v10)       YH03  yh03check.py ca63d81d7725
set -uo pipefail
GD=${1:?usage: run-gates.sh <gatedir>}
H=$(cd "$(dirname "$0")" && pwd); SM=$H/..
GB=$P/bin/fuzz_grant/fuzz_grant.asan; GT=$P/unstripped/fuzz_grant/fuzz_grant.asan
UB=$R/result/bin/fuzz_uci/fuzz_uci.asan; UT=$R/result/unstripped/fuzz_uci/fuzz_uci.asan
F3="A/Rt/AF0r.v A/Rt/AF0s.v Reusable/YF0v.v"
mkdir -p "$GD"; FIN=$GD/final; rm -rf "$FIN" "$GD"/plant-*
for f in $F3; do mkdir -p "$FIN/$(dirname "$f")"; cp "$LIB/$f" "$FIN/$f"; done
# plant <name> <file> <old> <new>: a copy of the three files with one value planted (exactly one occurrence)
plant() { local d=$GD/plant-$1; cp -r "$FIN" "$d"; python3 - "$d/$2" "$3" "$4" <<'EOF' || exit 9
import sys; p, o, n = sys.argv[1:]; t = open(p).read(); assert t.count(o) == 1, (p, o); open(p, 'w').write(t.replace(o, n))
EOF
}
plant loop A/Rt/AF0r.v 'Definition FS_LOOP : Z := 0x3c24c.' 'Definition FS_LOOP : Z := 0x3cfac.'
plant tsd A/Rt/AF0r.v 'Definition TSD : Z := 0x5f3338.' 'Definition TSD : Z := 0x5f8e78.'
plant entry A/Rt/AF0r.v 'Definition FS_ENTRY : Z := 0x3c1b8.' 'Definition FS_ENTRY : Z := 0x3cf18.'
plant rtoff A/Rt/AF0r.v '(0x60904, 2%nat)' '(0x60908, 2%nat)'
plant rtcnt A/Rt/AF0r.v '(0x68358, 140%nat)' '(0x68358, 141%nat)'
plant v10 A/Rt/AF0s.v 'Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).' \
  'Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).'

echo "== 0 bytecmp of every walked body (+ 6 planted controls)"
python3 "$SM/bytecmp.py" "$GT" "$UT" > "$GD/bytecmp.out"; echo "rc=$?" >> "$GD/bytecmp.out"
python3 "$SM/bytecmp.py" --no-addi0 "$GT" "$UT" > "$GD/bytecmp-b-tool.out"; echo "rc=$?" >> "$GD/bytecmp-b-tool.out"
# 1-3 planted instruction words; 4 the module id of the TLS index pair in the .got cell stack_malloc_1 +0x18 names;
# 5 that cell pointed at __asan_stack_malloc_1 (the resolve branch); 6 a byte in the 64-byte window after the empty
# string RegisterCommonFlags names at 0x13e5f (the NUL cut alone reads it as one zero byte, the same in both images)
k=0; for p in "--plant 0x3c24c:00e668b3" "--plant 0x3c280:02c1f0ef" "--plant 0x58454:00050413" \
  "--plant-data 0x97d00:02" "--plant-data 0x97d00:b8c1030000000000" "--plant 0x13e5f:48002800"; do k=$((k + 1))
  python3 "$SM/bytecmp.py" $p "$GT" "$UT" > "$GD/bytecmp-plant$k.out"; echo "rc=$?" >> "$GD/bytecmp-plant$k.out"; done
python3 "$SM/sites.py" "$UT" > "$GD/sites-target.out"; echo "rc=$?" >> "$GD/sites-target.out"
python3 "$SM/sites.py" "$GT" > "$GD/sites-donor.out"; echo "rc=$?" >> "$GD/sites-donor.out"

echo "== 1 flag gate: port_addr_check efa19b81e92b (of record) and e165063a0081 --fail-on-flags (+ 2 planted pointers)"
for ck in efa19b81e92b e165063a0081; do
  for t in rec loop tsd; do d=$FIN; [ "$t" = rec ] || d=$GD/plant-$t
    bash "$H/pac-sm1.sh" "$ck" "$WORK/stage" "$d" "$GD/$ck-$t" --fail-on-flags
    python3 "$H/triage-sm1.py" "$GD/$ck-$t.tsv" "$GD/$ck-$t.triage.tsv" > "$GD/$ck-$t.triage.out"; echo "rc=$?" >> "$GD/$ck-$t.triage.out"
  done
done

echo "== 2a codeptr 12348302dfd2 (base, declared, donor baseline, planted FS_ENTRY with and without the declarations)"
fr() { bash "$SET/frozen-run.sh" "$SET/startup-set-2026-10-30.tsv" "$@"; }
NA=(); while IFS=$'\t' read -r v why; do case "$v" in ''|'#'*) continue;; esac; NA+=(--not-address "$v=$why"); done < "$H/codeptr-notaddr-sm1.tsv"
sf() { local d=$1 a=(); for f in $F3; do a+=(--stale-file "$d/$f=$WORK/stage/$f"); done; echo "${a[@]}"; }
cp1() { local d=$1; shift; fr codeptr.py --image "$UB" --names "$UT" --stale-image "$GB" --stale-names "$GT" $(sf "$d") "$@" $(for f in $F3; do echo "$d/$f"; done); }
cp1 "$FIN" > "$GD/codeptr-base.out" 2>&1; echo "rc=$?" >> "$GD/codeptr-base.out"
cp1 "$FIN" "${NA[@]}" > "$GD/codeptr-declared.out" 2>&1; echo "rc=$?" >> "$GD/codeptr-declared.out"
fr codeptr.py --image "$GB" --names "$GT" $(for f in $F3; do echo "$WORK/stage/$f"; done) > "$GD/codeptr-donor.out" 2>&1; echo "rc=$?" >> "$GD/codeptr-donor.out"
cp1 "$GD/plant-entry" > "$GD/codeptr-plant.out" 2>&1; echo "rc=$?" >> "$GD/codeptr-plant.out"
cp1 "$GD/plant-entry" "${NA[@]}" > "$GD/codeptr-plant-declared.out" 2>&1; echo "rc=$?" >> "$GD/codeptr-plant-declared.out"

echo "== 2b in place of atable: keyset classes / check, and the keyed range-table check of fs_ranges (+ 2 plants)"
for x in "uciA $UB $UT" "grantA $GB $GT"; do set -- $x; fr keyset.py classes --image "$2" --twin "$3" > "$GD/keyset-classes-$1.out" 2>&1; echo "rc=$?" >> "$GD/keyset-classes-$1.out"; done
fr keyset.py check --image "$UB" --twin "$UT" $(for f in $F3; do echo "$FIN/$f"; done) > "$GD/keyset-check-uciA.out" 2>&1; echo "rc=$?" >> "$GD/keyset-check-uciA.out"
for x in "rec $FIN" "plant-offset $GD/plant-rtoff" "plant-count $GD/plant-rtcnt"; do set -- $x
  python3 "$H/rangetab-sm1.py" "$WORK/stage/A/Rt/AF0r.v" "$2/A/Rt/AF0r.v" "$GT" "$UT" > "$GD/rangetab-$1.out" 2>&1; echo "rc=$?" >> "$GD/rangetab-$1.out"; done

echo "== 2c the by-value check (record with the declaration, without it, and a planted donor value)"
DECL="0x109000:Definition FS_FROFF :=kFakeFramesOff + (1 << kStackSizeLog) = 0x9000 + 0x100000, the model's fake-frame offset of class 1 (frame_addr_cid, Qed in this file), not an image address"
python3 "$H/decval-sm1.py" --out "$GD/decval.tsv" --review "$GD/decval-review.tsv" --declare "$DECL" > "$GD/decval.out" 2>&1; echo "rc=$?" >> "$GD/decval.out"
python3 "$H/decval-sm1.py" > "$GD/decval-undeclared.out" 2>&1; echo "rc=$?" >> "$GD/decval-undeclared.out"
TC=$GD/ctlcore; rm -rf "$TC"; mkdir -p "$TC/provenance/evidence/stackmalloc1-A"; cp -r "$CORE/lib" "$TC/lib"
cp "$SM/applied.txt" "$TC/provenance/evidence/stackmalloc1-A/"; cp "$GD/plant-entry/A/Rt/AF0r.v" "$TC/lib/A/Rt/AF0r.v"
python3 "$H/decval-sm1.py" --core "$TC" --declare "$DECL" > "$GD/decval-control.out" 2>&1; echo "rc=$?" >> "$GD/decval-control.out"; rm -rf "$TC"

echo "== 3 v10 (global_settings 439f8e3bd463): the files, fuzz_grant's released counterparts, and a planted global flag"
(cd "$GD" && python3 "$GS" "$FIN" $F3 > v10-uciA.out 2>&1; echo "rc=$?" >> v10-uciA.out)
(cd "$GD" && python3 "$GS" "$DONREL" proofs/libreac/fuzz_grant/lib/A/Rt/AF0r.v proofs/libreac/fuzz_grant/lib/A/Rt/AF0s.v proofs/libreac/fuzz_grant/lib/Reusable/YF0v.v > v10-grant-counterparts.out 2>&1; echo "rc=$?" >> v10-grant-counterparts.out)
(cd "$GD" && python3 "$GS" "$GD/plant-v10" $F3 > v10-plant.out 2>&1; echo "rc=$?" >> v10-plant.out)

echo "== 4 yh03check ca63d81d7725: the files (no src0_ row: N/A) and its two known-answer controls"
python3 "$YH03" "$UT" $(for f in $F3; do echo "$FIN/$f"; done) > "$GD/yh03check.out" 2>&1; echo "rc=$?" >> "$GD/yh03check.out"
printf 'Definition src0_A___asan_stack_malloc_1 : Z := 0x3c1b8.\nDefinition src0_E___asan_stack_malloc_1 : Z := 0x3c348.\n' > "$GD/ok.YH03.v"
printf 'Definition src0_A___asan_stack_malloc_1 : Z := 0x3c1bc.\nDefinition src0_E___asan_stack_malloc_1 : Z := 0x3c348.\n' > "$GD/bad.YH03.v"
for t in ok bad; do python3 "$YH03" "$UT" "$GD/$t.YH03.v" > "$GD/yh03check-control-$t.out" 2>&1; echo "rc=$?" >> "$GD/yh03check-control-$t.out"; done
echo "run-gates: done ($GD)"
