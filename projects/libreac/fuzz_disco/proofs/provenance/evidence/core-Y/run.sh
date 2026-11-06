#!/bin/sh
# Re-runs every script of the core-Y evidence slice and compares each output with the shipped bytes. Run from this directory.
# Inputs (variables; no host path is written in this file):
#   PIN         fuzz_disco.asan-ubsan, the released image-B pin,  sha256 cee6f04ad3d4928e242405689ae058bb9e8b6533000c90bde984a2f0d5ff5146
#   TWIN        its unstripped twin (never shipped),            sha256 ead714913acd1e81...
#   REPO        a checkout of this repository at a commit that holds this slice
#   OLD_PIN, KERNEL_PIN, KNOWN_PIN, OLD_TWIN   the Y5 donor and helper images (see y5-g8g7 below)
#   OUT         an empty scratch directory outside the tree (its path must not contain "proofs/")
#   LOG         optional: the collector's pass-2 log (sha256 8331d9ec8f44...); when set, the Y6 value table is re-extracted
#   D9E0        optional: the files of port_core tag d9e0589898fd; when set, y5-d9e0/command.sh dry-runs that tag on the
#               Y5 inputs and re-derives the classification and check tables (y5-d9e0/classify.tsv, checks.tsv)
# Needs python3 with pyelftools and capstone.
set -eu
export PYTHONDONTWRITEBYTECODE=1
case "$OUT" in *proofs/*) echo "OUT must not contain proofs/" >&2; exit 2;; esac
mkdir -p "$OUT"
# the symbol extract of the image-B build
python3 extract/extract_symbols.py --twin "$TWIN" --pin "$PIN" --out "$OUT/symbols-asan-ubsan.tsv"
cmp "$OUT/symbols-asan-ubsan.tsv" extract/symbols-asan-ubsan.tsv
# Y8: lib/Reusable/YB1w.v
python3 y8-yb1w/gen_b1w_own.py --pin "$PIN" --symbols extract/symbols-asan-ubsan.tsv \
	--table y8-yb1w/YB1w-da397ed671d.v --out "$OUT/YB1w.v" \
	--old y8-yb1w/YB1w-8de90eafc69a.v --musl-lo 0x8f6b0 --musl-hi 0x9f248
cmp "$OUT/YB1w.v" "$REPO/proofs/libreac/fuzz_disco/lib/Reusable/YB1w.v"
# Y9: the two values of lib/Reusable/YImgTop.v
python3 y9-imgtop/img_hull.py --pin "$PIN" > "$OUT/img_hull.txt"
sed -nE 's/^Definition (IMG_LO|IMG_TOP) : Z := (0x[0-9a-f]+)\.$/\1 \2/p' \
	"$REPO/proofs/libreac/fuzz_disco/lib/Reusable/YImgTop.v" > "$OUT/YImgTop.values"
cmp "$OUT/img_hull.txt" "$OUT/YImgTop.values"
# Y6: lib/Reusable/YF0m.v
python3 y6-yf0m/yf0m_regen.py --image "$PIN" --symbols extract/symbols-asan-ubsan.tsv \
  --binaries "$REPO/index/binaries.tsv" --imgtop "$REPO/proofs/libreac/fuzz_disco/lib/Reusable/YImgTop.v" \
  --stage y6-yf0m/YF0m.stage.v --base y6-yf0m/yf0m_base.v --values y6-yf0m/pass2-values.tsv --out "$OUT/YF0m.v"
cmp "$OUT/YF0m.v" "$REPO/proofs/libreac/fuzz_disco/lib/Reusable/YF0m.v"
if [ -n "${LOG:-}" ]; then
  python3 y6-yf0m/extract_pass2.py --log "$LOG" --image "$PIN" --cells y6-yf0m/pass2-values.tsv --out "$OUT/pass2-values.tsv"
  cmp "$OUT/pass2-values.tsv" y6-yf0m/pass2-values.tsv
fi
# Y5: the 18 relocated files of lib/Reusable (donor: the released cgif tree cbd08981406; target lib: 54fe7cb842c)
WORK="$OUT/y5"
sha256sum -c - <<EOF
cee6f04ad3d4928e242405689ae058bb9e8b6533000c90bde984a2f0d5ff5146  $PIN
1c29845fe6058de6e1dbf3f6ec6abd566ea612d76b65ea5435d7ff77c63e08ef  $OLD_PIN
7093581aab040cfd94ed56f83bf44a37e6ec3c34db39cc57bf467e2949e870f0  $KERNEL_PIN
5e39150dd8104df969eb360f9cc29c4f92fe12326afd23783a679e4fb4809f46  $KNOWN_PIN
ce511d541cdabbe3c8df3f672dc517e8b5a7edd37b280a7483043b438de0adf7  $OLD_TWIN
EOF
mkdir -p "$WORK/donor" "$WORK/target"
python3 extract/extract_symbols.py --twin "$OLD_TWIN" --pin "$OLD_PIN" --out "$WORK/symbols-cgif-asan-ubsan.tsv"
cmp "$WORK/symbols-cgif-asan-ubsan.tsv" y5-g8g7/symbols-cgif-asan-ubsan.tsv
git -C "$REPO" archive cbd08981406 proofs/cgif/cgif_file_fuzzer/lib | tar -x -C "$WORK/donor"
git -C "$REPO" archive 54fe7cb842c proofs/libreac/fuzz_disco/lib | tar -x -C "$WORK/target"
python3 y5-g8g7/port_core.py --kit-dir kit \
  --src-lib "$WORK/donor/proofs/cgif/cgif_file_fuzzer/lib" \
  --old-elf "$OLD_PIN" --old-prog 804c0:86e40 \
  --old-syms y5-g8g7/symbols-cgif-asan-ubsan.tsv \
  --target-lib "$WORK/target/proofs/libreac/fuzz_disco/lib" \
  --target-mod OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib \
  --target-images OssFuzzTheorems.libreac.fuzz_disco.images \
  --target-name libreac/fuzz_disco \
  --target-elf "$PIN" --target-syms extract/symbols-asan-ubsan.tsv \
  --files y5-g8g7/files.txt \
  --work "$WORK/run" \
  --reusable-dir Reusable \
  --remap-images \
  --kernel-image "$KERNEL_PIN" \
  --known-elf "$KNOWN_PIN" \
  --rename tfib_A_musl_memcmp=tfib_A_memcmp_libc \
  --rename tfib_A_musl_memset=tfib_A_memset_libc \
  --override y5-g8g7/overrides.tsv \
  --no-gate
for f in YE2s YE3b YE6z YE70 YE2z YE2q YE2r YE6l YE6m YE6n YE6o YE6p YE6q YE6r YE6s YE6t YE6u YE6v; do
  cmp "$WORK/run/stage-out/Reusable/$f.v" "$REPO/proofs/libreac/fuzz_disco/lib/Reusable/$f.v"
done
if [ -n "${D9E0:-}" ]; then
  D9E0="$D9E0" WORK="$WORK" sh y5-d9e0/command.sh
fi
echo "core-Y: every re-run output equals the shipped bytes"
