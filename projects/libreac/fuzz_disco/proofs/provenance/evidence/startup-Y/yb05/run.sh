#!/usr/bin/env bash
# startup-Y/yb05: re-derive lib/Reusable/YB05.v of libreac/fuzz_disco (the image B start-up plan) and remap.B.tsv (the
# per-value table of its address step) from the released donor files and the two image B pins, then compare.
#   TREE    a checkout of the series base (the repository root)
#   IMG_B   the image B pin, fuzz_disco.asan-ubsan (index/binaries.tsv row libreac fuzz_disco asan-ubsan)
#   CGIF_B  the donor's image B pin, cgif_file_fuzzer.asan-ubsan (index/binaries.tsv row cgif cgif_file_fuzzer asan-ubsan)
#   OUT     where to write (default: ./out)
# Needs python3 with capstone and pyelftools (itabranges.py decodes the executable sections of IMG_B).
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
HERE="$(cd "$(dirname "$0")" && pwd)"
: "${TREE:?set TREE}" "${IMG_B:?set IMG_B}" "${CGIF_B:?set CGIF_B}"
OUT="${OUT:-./out}"; mkdir -p "$OUT"
DONOR="$TREE/proofs/cgif/cgif_file_fuzzer/lib"
SHIP="$TREE/proofs/libreac/fuzz_disco/lib/Reusable"
# 0. each image must be the one its index/binaries.tsv row names (project, harness, build -> sha256)
pin() {
  want="$(awk -F'\t' -v p="$2" -v h="$3" -v b="$4" '$1 == p && $2 == h && $3 == b { print $8 }' "$TREE/index/binaries.tsv")"
  [ -n "$want" ] && [ "$(sha256sum < "$1" | cut -c1-64)" = "$want" ] \
    || { echo "yb05: $1 is not the $2 $3 $4 image of index/binaries.tsv" >&2; exit 1; }
}
pin "$IMG_B" libreac fuzz_disco asan-ubsan
pin "$CGIF_B" cgif cgif_file_fuzzer asan-ubsan
# 1. the address map, donor image B -> image B
python3 "$HERE/kit/elf_symbols.py" "$CGIF_B" "$IMG_B" -o "$OUT/map.json" --summary "$OUT/map.summary.txt"
# 2. move every address-like number of the donor's YB05.v, YB1k.v and YF0m.v (one call: the report covers all three)
python3 "$HERE/kit/numeral_map.py" --map "$OUT/map.json" --report "$OUT/remap.B.tsv" --rewrite "$OUT/reloc" \
  "$DONOR/YB05.v" "$DONOR/YB1k.v" "$DONOR/YF0m.v" > "$OUT/numeral_map.summary.txt"
cmp "$OUT/remap.B.tsv" "$HERE/remap.B.tsv"
# 3. the plan's tail: 46 PX XMemset / PRun pairs before every final PRun [main] (main is 0x80b1c on image B; 46 is the
#    count the collector's probe measured)
cp "$OUT/reloc/YB05.v" "$OUT/YB05.plan.v"
python3 "$HERE/plantail.py" insert --plan "$OUT/YB05.plan.v" --main 0x80b1c --count 46
# 4. the plan's ranges: one range per executable section of image B (--rule text; the donor plan gives the name)
python3 "$HERE/itabranges.py" --new "$IMG_B" --rule text --plan "$DONOR/YB05.v" --out-plan "$OUT/YB05.plan.v"
# 5. the unit's module paths and its one Modified line (the note is the shipped file's own fourth line)
note="$(sed -n 4p "$SHIP/YB05.v" | sed -e 's/^(\* Modified by Theorem Labs, 2026-10: //' -e 's/ \*)$//')"
python3 "$HERE/to_disco.py" "$OUT/YB05.plan.v" "$OUT/YB05.v" "$note"
cmp "$OUT/YB05.v" "$SHIP/YB05.v"
# 6. YB1k.v, from the same call as step 2: the shipped file is the step-2 output with the unit's module paths (no
#    Modified line) and ONE value set by hand, line 66 F_020 0x65000 -> 0x65afc, the review row "YB1k.v 66 47" of
#    remap.B.tsv. These two changes are applied here to show that they are the only differences.
sed -e 's/OssFuzzTheorems\.Proofs\.cgif\.cgif_file_fuzzer\.lib\([. ]\)/OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib.Reusable\1/g' \
  -e '66s/0x65000/0x65afc/' "$OUT/reloc/YB1k.v" > "$OUT/YB1k.v"
cmp "$OUT/YB1k.v" "$SHIP/YB1k.v"
echo "yb05: remap.B.tsv and YB05.v reproduced byte for byte; YB1k.v differs from the address step only by its module paths and F_020"
