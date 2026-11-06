#!/usr/bin/env bash
# startup-Y/yb12: re-derive lib/Reusable/YB12.v of libreac/fuzz_disco (the image descriptor of image B) with atable.py
# from the image B pin, the twin's symbol extract (twin_syms.B.tsv), the donor image B and the donor's released YB12.v.
#   TREE    a checkout of the series base (the repository root)
#   IMG_B   the image B pin, fuzz_disco.asan-ubsan (index/binaries.tsv row libreac fuzz_disco asan-ubsan)
#   CGIF_B  the donor image B, cgif_file_fuzzer.asan-ubsan (index/binaries.tsv row cgif cgif_file_fuzzer asan-ubsan)
#   OUT     where to write (default: ./out)
#   TWIN_B  optional: the unstripped twin of IMG_B; when given, twin_syms.B.tsv is re-extracted from it first
#   REPO    optional: a git repository that holds commit 7bae547bef80; when given, the output is also compared with
#           that commit's YB12.v (the tool's recorded output)
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
HERE="$(cd "$(dirname "$0")" && pwd)"
: "${TREE:?set TREE}" "${IMG_B:?set IMG_B}" "${CGIF_B:?set CGIF_B}"
OUT="${OUT:-./out}"; mkdir -p "$OUT"
SYMS="$HERE/twin_syms.B.tsv"
if [ -n "${TWIN_B:-}" ]; then
  python3 "$HERE/extract_twin_syms.py" "$IMG_B" "$TWIN_B" "$OUT/twin_syms.B.tsv"
  cmp "$OUT/twin_syms.B.tsv" "$SYMS"
fi
SHIP="$TREE/proofs/libreac/fuzz_disco/lib/Reusable/YB12.v"
# 1. the header input: the provenance comment, lines 1-7 of the shipped file (the tool writes them verbatim)
sed -n 1,7p "$SHIP" > "$OUT/hdr_disco.v"
# 2. the descriptor
python3 "$HERE/atable.py" --side B --prefix OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib --reusable .Reusable \
  --img-names YImgTop.IMG_LO,YImgTop.IMG_TOP --donor-image "$CGIF_B" \
  --donor-atable "$TREE/proofs/cgif/cgif_file_fuzzer/lib/YB12.v" --header "$OUT/hdr_disco.v" \
  "$IMG_B" "$SYMS" > "$OUT/YB12.v"
# 3. the shipped file is this output plus one hand edit (commit a34e82e078a1): header line 8 added and
#    TFIB_TEXT_N 112697 -> 112841. Undo that edit on the shipped file and compare.
sed -e 8d -e 's/^Definition TFIB_TEXT_N : nat := 112841\.$/Definition TFIB_TEXT_N : nat := 112697./' "$SHIP" \
  | cmp - "$OUT/YB12.v"
if [ -n "${REPO:-}" ]; then
  git -C "$REPO" show 7bae547bef80:proofs/libreac/fuzz_disco/lib/Reusable/YB12.v | cmp - "$OUT/YB12.v"
fi
echo "yb12: YB12.v reproduced byte for byte up to the hand edit of TFIB_TEXT_N (112697 -> 112841) and header line 8"
