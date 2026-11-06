set -euo pipefail
usage='step2.sh <out dir, must not exist> [LIB to lay lib/B into]
  env: UNIT HUB TREE A_CORE A_GRANT A_KNOCK S1 REL P R TWIN [CZONE] [A_EVIDENCE] [FILES2]'
OUT=${1:?$usage}; LAY=${2:-}
HERE=$(cd "$(dirname "$0")" && pwd)
: "${UNIT:?$usage}" "${HUB:?$usage}" "${TREE:?$usage}" "${A_CORE:?$usage}" "${A_GRANT:?$usage}" "${A_KNOCK:?$usage}" "${S1:?$usage}"
: "${REL:?$usage}" "${P:?$usage}" "${R:?$usage}" "${TWIN:?$usage}"
. "$HERE/unit_root.sh"
U=$(unit_root "$TREE")
M=OssFuzzTheorems.Proofs.reac_repacer.$UNIT.lib
K=proofs/libreac/fuzz_knock/lib  # fuzz_knock's released text at 88154566652a, a commit of the earlier layout
E=${A_EVIDENCE:-$(unit_root "$A_CORE")/provenance/evidence/depot}
[ ! -e "$OUT" ] || { echo "step2: $OUT exists" >&2; exit 2; }
mkdir -p "$OUT/tree" "$OUT/gbflat" "$OUT/gb/B" "$OUT/knock" "$OUT/kb/B" "$OUT/kb/Reusable" "$OUT/cc" "$OUT/a" "$OUT/lib/B" "$OUT/glue/lib/B"
git -C "$HUB" archive "$TREE" "$U/lib/B" | tar -x -C "$OUT/tree"
git -C "$HUB" archive 88154566652a "$K/AU" "$K/Reusable" | tar -x -C "$OUT/knock"
for f in consumer-classes.tsv takes.tsv knock-files.txt flag-before-r26.tsv flag-baseline-655d9c-unstubbed.tsv; do
  git -C "$HUB" show "$A_CORE:$E/$f" > "$OUT/a/$f"
done
if [ -n "${FILES2:-}" ]; then cp "$FILES2" "$OUT/files2.txt"; else
  sed -n 's|^A/\(.*\)$|\1|p' "$OUT/a/knock-files.txt" | grep -vx 'AB1w.v' | sed 's/^A\(.*\)$/Y\1/; s/^YWalkFw0\.v$/AWalkFw0.v/' > "$OUT/files2.txt"
fi
python3 "$HERE/zify_flag_sets.py" "$OUT/a/flag-before-r26.tsv" "$OUT/a/flag-baseline-655d9c-unstubbed.tsv" > "$OUT/zify-flag-sets.txt"
PIN=$(git -C "$HUB" show "$TREE:projects/reac-repacer/$UNIT/harness.yaml" | python3 -c "import sys, yaml; print(yaml.safe_load(sys.stdin)['builds']['asan-ubsan']['sha256'])")
python3 "$HERE/mk_glue_ad3d.py" --image B --unit-mod "$M" "$OUT/knock/$K/AU/YF0r.v" "$OUT/glue/lib/B/YD3dEnv.v" | tee "$OUT/mk-glue-B.log"
python3 "$HERE/mk_yd3d_patch.py" "$S1/work/stage-out/B/YD3d.v" > "$OUT/yd3d-env.patch"
python3 "$HERE/derive_overrides_knockB.py" ${CZONE:+--czone "$CZONE"} --files "$OUT/files2.txt" "$UNIT" "$R" "$P" \
  "$S1/donB-knock/proofs/libreac/fuzz_knock/lib" "$PIN" "$TWIN" > "$OUT/overrides-knockB.tsv" 2> "$OUT/overrides-knockB-roles.tsv"
echo "step2: $(wc -l < "$OUT/files2.txt") files to relocate, $(wc -l < "$OUT/overrides-knockB.tsv") override rows"
RUN=step2-$(basename "$OUT")
ADD_B="$OUT/glue/lib/B/YD3dEnv.v" UNIT="$UNIT" REL="$REL" P="$P" R="$R" bash "$HERE/reloc.sh" "$S1" "$RUN" "$OUT/files2.txt" \
  --override "$OUT/overrides-knockB.tsv" --patch "$OUT/yd3d-env.patch" > "$OUT/reloc.log" 2>&1
grep -e '^reloc' -e 'values have no rule' -e '^port_core: staged' "$OUT/reloc.log" | cut -c1-200
MAIN=$S1/$RUN/work/stage-out
: > "$OUT/consumers.txt"; : > "$OUT/closure.txt"
while read -r f; do
  if [ ! -e "$OUT/tree/$U/lib/B/$f" ]; then echo "$f" >> "$OUT/closure.txt"; continue; fi
  echo "$f" >> "$OUT/consumers.txt"
  cp "$OUT/tree/$U/lib/B/$f" "$OUT/gbflat/$f"; cp "$OUT/tree/$U/lib/B/$f" "$OUT/gb/B/$f"; cp "$MAIN/B/$f" "$OUT/kb/B/$f"
done < "$OUT/files2.txt"
mapfile -t CONS < "$OUT/consumers.txt"
echo "step2: ${#CONS[@]} consumer files, $(wc -l < "$OUT/closure.txt") knock-only files"
python3 "$HERE/depot_classify.py" --consumer "$U/lib/B/" knock-relocated:B/ --sub B "$OUT/gbflat" "$OUT/kb" "$OUT/cc" "${CONS[@]}" > "$OUT/consumer-classes-B.tsv"
tail -1 "$OUT/consumer-classes-B.tsv"
python3 "$HERE/consumer_classify.py" "$OUT/gbflat" "$OUT/kb/B" "${CONS[@]}" > "$OUT/consumer-residue-B.txt"
git -C "$HUB" ls-tree --name-only "$TREE" "$U/lib/A/" | sed -n 's|.*/\(.*\)\.v$|\1|p' > "$OUT/amods.txt"
AMODS=$OUT/amods.txt ROWS_ARGS=$OUT/rows.args python3 "$HERE/map_rows.py" "$A_GRANT" "$A_KNOCK" \
  "$OUT/a/consumer-classes.tsv" "$OUT/a/takes.tsv" "$HERE/a-merges.tsv" "$OUT/gb" "$OUT/kb" "$OUT/consumer-classes-B.tsv" \
  "${CONS[@]}" > "$OUT/rows-B.tsv"
mapfile -t ROWS < "$OUT/rows.args"
python3 "$HERE/depot_apply.py" --consumer --sub B --lib-repo "$U/lib" "$OUT/gb" "$OUT/kb" "$OUT/consumer-classes-B.tsv" \
  "$OUT/applied" --imgtop-unfold "${ROWS[@]}" > "$OUT/consumer-apply-B.log"
for f in "${CONS[@]}"; do cp "$OUT/applied/$f" "$OUT/lib/B/$f"; done
mapfile -t CLO < <(grep -vx 'AWalkFw0.v' "$OUT/closure.txt")
for f in "${CLO[@]}"; do cp "$MAIN/B/$f" "$OUT/lib/B/$f"; done
python3 "$HERE/closure_glue.py" "${CLO[@]/#/$OUT/lib/B/}" > "$OUT/closure-glue-B.log"
tail -1 "$OUT/closure-glue-B.log"
python3 "$HERE/closure_awalk.py" --image B "${CLO[@]/#/$OUT/lib/B/}" > "$OUT/closure-awalk-B.log"
tail -1 "$OUT/closure-awalk-B.log"
python3 "$HERE/notice_split.py" "$OUT/lib/B/YD3i.v" "$OUT/lib/B/YD3j.v" "$OUT/lib/B/YD3k.v" > "$OUT/notice-split-B.log"
cat "$OUT/notice-split-B.log"
python3 "$HERE/ad1g_guard.py" "$OUT/lib/B/YD1g.v" > "$OUT/ad1g-guard-B.log"
head -1 "$OUT/ad1g-guard-B.log"
python3 "$HERE/tail_generalize.py" --image B "$OUT/lib/B" > "$OUT/tail-generalize-B.log"
tail -1 "$OUT/tail-generalize-B.log"
python3 "$HERE/d1w_close.py" --image B "$OUT/lib" > "$OUT/d1w-close-B.log"
tail -1 "$OUT/d1w-close-B.log"
read -r -a E6 <<< "$(sed -n 's/^E6 //p' "$OUT/zify-flag-sets.txt")"
read -r -a E7 <<< "$(sed -n 's/^E7 //p' "$OUT/zify-flag-sets.txt")"
for f in "${E6[@]}" "${E7[@]}"; do
  y=Y${f#A}
  [ -e "$OUT/lib/B/$y" ] || cp "$OUT/tree/$U/lib/B/$y" "$OUT/lib/B/$y"
done
python3 "$HERE/zify_flag.py" --image B "$OUT/lib" "${E6[@]}" > "$OUT/zify-flag-false-B.log"
python3 "$HERE/zify_flag.py" --image B --e7 "$OUT/lib" "${E7[@]}" > "$OUT/zify-flag-true-B.log"
tail -1 "$OUT/zify-flag-false-B.log"; tail -1 "$OUT/zify-flag-true-B.log"
cp "$OUT/glue/lib/B/YD3dEnv.v" "$OUT/lib/B/YD3dEnv.v"
set +e
python3 "$HERE/leak_gate.py" --exceptions "$HERE/leak-gate-exceptions.tsv" "$OUT/gbflat" "$OUT/lib/B" "${CONS[@]}" > "$OUT/leak-gate-B.tsv"
lg=$?
set -e
echo "step2: leak_gate rc=$lg; $(tail -1 "$OUT/leak-gate-B.tsv")"
[ "$lg" -eq 0 ] || { echo "step2: STOP: the leak gate fails (a LINEAGE hit no exception row clears, or a stale row); nothing is laid" >&2; exit 1; }
grep -l 'port_core_refused' "$OUT/lib/B/"*.v > "$OUT/refused-left.txt" || true
echo "step2: files with port_core_refused markers: $(wc -l < "$OUT/refused-left.txt"); lib/B files written: $(ls "$OUT/lib/B" | wc -l)"
if [ -n "$LAY" ]; then
  cp "$OUT/lib/B/"*.v "$LAY/B/"
  echo "step2: laid $(ls "$OUT/lib/B" | wc -l) files into $LAY/B"
fi
