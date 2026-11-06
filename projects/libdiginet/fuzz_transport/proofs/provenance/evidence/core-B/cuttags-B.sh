#!/bin/bash
# cuttags-B.sh <workdir> <LIB0> <MODEL_TAGS> <OUT.patch> [RECORDS_DIR]: B-model-tags.patch for libdiginet/fuzz_transport's
# image-B core.
#
# The image-A core's commit 0ece7baefb1 ran model_tags.py e1cb9c4fb27f (the tool registry's tools/model-tags/
# e1cb9c4fb27f/) on the unit: the 14 allocator-model labels of lib/Reusable/YG00.v (201364 .. 469488) became the tags
# 1..14 in the shared lib/Reusable files and in image A's twins. The image-B twins this run stages restate the same
# labels, so they must carry the tags too. This script runs the same tool, unchanged, on a unit tree made of LIB0 (the
# unit's lib before that commit: lib/Reusable/YG00.v still holds the labels, which the tool reads its map from) with
# the run's stage-out applied by apply-B.sh (beside this script) and the two driver files, and writes the diff of
# every lib/B file the tool rewrote as a --patch against stage-out (paths B/<f>.v, 3 lines of context). The files of
# lib/A and lib/Reusable the tool rewrites are not in the patch: the target lib already holds them in that form
# (the script checks each against LIB, when LIB is set, and stops on a difference).
#   workdir     a port_core run directory (stage-out/ is read)
#   LIB0        a lib directory before the model_tags commit (lib/Reusable/YG00.v with the labels)
#   MODEL_TAGS  model_tags.py e1cb9c4fb27f (its sha256 is checked)
#   RECORDS_DIR (optional) where the tool's --check and run output are written (model-tags-B.check.txt, .run.txt)
set -euo pipefail
WORK=$1 LIB0=$2 MT=$3 OUT=$4 REC=${5:-}
HERE=$(cd "$(dirname "$0")" && pwd)
[ "$(sha256sum "$MT" | cut -c1-12)" = e1cb9c4fb27f ] || { echo "cuttags-B: $MT is not model_tags.py e1cb9c4fb27f" >&2; exit 5; }
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
U=proofs/libdiginet/fuzz_transport
mkdir -p "$TMP/$U" && cp -a "$LIB0" "$TMP/$U/lib"
bash "$HERE/apply-B.sh" "$WORK" "$TMP/$U/lib" "$TMP/applied.txt" > /dev/null
cp "$HERE/TransportDrvGB.v" "$HERE/TransportDriverB.v" "$TMP/$U/lib/B/"
(cd "$TMP" && git init -q && git add -A && git -c user.email=x@x -c user.name=x commit -qm base)
(cd "$TMP" && python3 "$MT" --check "$U") > "$TMP/check.txt"
(cd "$TMP" && python3 "$MT" "$U") > "$TMP/run.txt"
left=$(cd "$TMP" && { git grep -n -w -E '201364|201376|202260|209280|210276|212388|213516|219184|221048|222820|391236|449860|460508|469488' -- ":(glob)$U/**/*.v" ":(glob,exclude)$U/**/provenance/**" || true; } | wc -l)
[ "$left" = 0 ] || { echo "cuttags-B: $left label occurrences left" >&2; exit 4; }
: > "$OUT"
for f in $(cd "$TMP" && git diff --name-only -- "$U/lib" | LC_ALL=C sort); do
  r=${f#$U/lib/}
  case $r in
    B/*) diff -u --label "$r" --label "$r" "$WORK/stage-out/$r" "$TMP/$f" >> "$OUT" || true ;;
    *) if [ -n "${LIB:-}" ]; then cmp -s "$TMP/$f" "$LIB/$r" || { echo "cuttags-B: $r differs from LIB's" >&2; exit 6; }; fi ;;
  esac
done
if [ -n "$REC" ]; then cp "$TMP/check.txt" "$REC/model-tags-B.check.txt"; cp "$TMP/run.txt" "$REC/model-tags-B.run.txt"; fi
echo "$OUT: $(grep -c '^+++ ' "$OUT") files, $(grep -c '^-[^-]' "$OUT") lines replaced"
