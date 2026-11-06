#!/bin/bash
# codeptr-B.sh <workdir> <outdir>: the start-up set's codeptr checker (codeptr.py sha256 12348302dfd2e419748b...), run
# from the set's directory (SET=, BUNDLE= its bundle file) through the set's
# frozen-run.sh, over every staged image-B core file, plus two controls:
#   donor   the donor's own text (stage/B) on the donor's own image, no stale check: the tool's baseline on accepted text
#   plant   a copy of stage-out/B/YE3m.v whose STDOUT_BUFA is put back to the donor's 0x5f9020 (above uci's top 0x5f4000):
#           must be a finding (stale / outside) in exactly that file
#   base    stage-out/B/*.v on fuzz_uci.asan-ubsan with --stale-image grant B and --stale-dir stage (each file's donor text)
set -uo pipefail
WORK=$1 OUT=$2
SS=${SET:?set SET to the start-up set directory that holds frozen-run.sh and codeptr.py sha256 12348302dfd2}
BUNDLE=${BUNDLE:-startup-set-2026-10-30.tsv}
: "${P:?set P to libreac's pinned image tree}" "${R:?set R to reac-repacer's pinned image tree}"
GB=$P/bin/fuzz_grant/fuzz_grant.asan-ubsan; GT=$P/unstripped/fuzz_grant/fuzz_grant.asan-ubsan
UB=$R/result/bin/fuzz_uci/fuzz_uci.asan-ubsan; UT=$R/result/unstripped/fuzz_uci/fuzz_uci.asan-ubsan
mkdir -p "$OUT/plant/B"
fr() { bash "$SS/frozen-run.sh" "$SS/$BUNDLE" codeptr.py "$@"; }
fr --image "$GB" --names "$GT" "$WORK"/stage/B/*.v > "$OUT/donor.out" 2>&1; echo "rc=$?" >> "$OUT/donor.out"
sed 's/^Definition STDOUT_BUFA : Z := 0x5f27a0\./Definition STDOUT_BUFA : Z := 0x5f9020./' "$WORK/stage-out/B/YE3m.v" > "$OUT/plant/B/YE3m.v"
diff "$WORK/stage-out/B/YE3m.v" "$OUT/plant/B/YE3m.v" > "$OUT/plant.diff"
fr --image "$UB" --names "$UT" --stale-image "$GB" --stale-names "$GT" --stale-dir "$WORK/stage" "$OUT/plant/B/YE3m.v" > "$OUT/plant.out" 2>&1; echo "rc=$?" >> "$OUT/plant.out"
fr --image "$UB" --names "$UT" --stale-image "$GB" --stale-names "$GT" --stale-dir "$WORK/stage" "$WORK"/stage-out/B/*.v > "$OUT/base.out" 2>&1; echo "rc=$?" >> "$OUT/base.out"
#   declared  base again with every non-address of codeptr-notaddr.tsv declared (--not-address VALUE=REASON); the plant
#             must still be a finding under the same declarations (they exempt numbers, not the planted donor address)
NA=()
while IFS=$'\t' read -r v why; do case "$v" in ''|'#'*) continue;; esac; NA+=(--not-address "$v=$why"); done < "$(dirname "$0")/codeptr-notaddr.tsv"
fr --image "$UB" --names "$UT" --stale-image "$GB" --stale-names "$GT" --stale-dir "$WORK/stage" "${NA[@]}" "$WORK"/stage-out/B/*.v > "$OUT/declared.out" 2>&1; echo "rc=$?" >> "$OUT/declared.out"
cp "$WORK"/stage-out/B/*.v "$OUT/plant/B/" && sed -i 's/^Definition STDOUT_BUFA : Z := 0x5f27a0\./Definition STDOUT_BUFA : Z := 0x5f9020./' "$OUT/plant/B/YE3m.v"
fr --image "$UB" --names "$UT" --stale-image "$GB" --stale-names "$GT" --stale-dir "$WORK/stage" "${NA[@]}" "$OUT"/plant/B/*.v > "$OUT/plant-declared.out" 2>&1; echo "rc=$?" >> "$OUT/plant-declared.out"
for f in donor plant base declared plant-declared; do printf '%s: ' "$f"; tail -n 3 "$OUT/$f.out" | tr '\n' ' '; echo; done
