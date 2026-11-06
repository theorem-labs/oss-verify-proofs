#!/usr/bin/env bash
# evidence/startup-Y: re-derive every generated image-B start-up file, one subdirectory at a time, and compare each
# result byte for byte with the shipped file (each subdirectory's run.sh does its own cmp and stops on a difference).
#   TREE    a checkout of the series base (the repository root)
#   IMG_B   the image B pin, fuzz_disco.asan-ubsan (index/binaries.tsv row libreac fuzz_disco asan-ubsan)
#   TWIN_B  the unstripped twin of IMG_B (the same build with symbols; never shipped)
#   CGIF_B  the donor's image B pin, cgif_file_fuzzer.asan-ubsan (index/binaries.tsv row cgif cgif_file_fuzzer asan-ubsan)
#   OUT     where to write (default: ./out); each subdirectory writes OUT/<subdirectory>/
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
HERE="$(cd "$(dirname "$0")" && pwd)"
: "${TREE:?set TREE}" "${IMG_B:?set IMG_B}" "${TWIN_B:?set TWIN_B}" "${CGIF_B:?set CGIF_B}"
OUT="${OUT:-./out}"
for d in collector yb05 yb12 ad2 ye3i ycej yb1v; do
  [ -x "$HERE/$d/run.sh" ] || continue
  echo "== $d"
  TREE="$TREE" IMG_B="$IMG_B" TWIN_B="$TWIN_B" CGIF_B="$CGIF_B" OUT="$OUT/$d" bash "$HERE/$d/run.sh"
done
