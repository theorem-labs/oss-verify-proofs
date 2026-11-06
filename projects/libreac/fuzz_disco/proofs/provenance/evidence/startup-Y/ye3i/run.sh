#!/usr/bin/env bash
# startup-Y/ye3i: re-derive lib/Reusable/YE3i.v of libreac/fuzz_disco (IMG_RO_LO, IMG_RO_HI, img_ro_chunks) from the
# image B pin, the shipped YF0m (its Tfib_owned_static ranges) and the released donor YE3i (all other text).
#   TREE   a checkout of the series base (the repository root)
#   IMG_B  the image B pin, fuzz_disco.asan-ubsan (index/binaries.tsv row libreac fuzz_disco asan-ubsan)
#   OUT    where to write (default: ./out)
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
HERE="$(cd "$(dirname "$0")" && pwd)"
: "${TREE:?set TREE}" "${IMG_B:?set IMG_B}"
OUT="${OUT:-./out}"; mkdir -p "$OUT"
DONOR="$TREE/proofs/cgif/cgif_file_fuzzer/lib"
SHIP="$TREE/proofs/libreac/fuzz_disco/lib/Reusable"
# the one Modified line ae3i.py adds is the shipped file's own fourth line
note="$(sed -n 4p "$SHIP/YE3i.v" | sed -e 's/^(\* Modified by Theorem Labs, 2026-10: //' -e 's/ \*)$//')"
python3 "$HERE/ae3i.py" --tmpl "$DONOR/YE3i.v" --owned "$SHIP/YF0m.v" --image "$IMG_B" --out "$OUT/YE3i.v" \
  --ns OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib=OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib.Reusable \
  --modified "$note"
cmp "$OUT/YE3i.v" "$SHIP/YE3i.v"
echo "ye3i: YE3i.v reproduced byte for byte"
