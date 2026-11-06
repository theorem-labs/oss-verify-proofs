#!/bin/bash
# cutuntime-B.sh <workdir> <UNIT> <TOOLS> <OUT.patch> <RECORD_DIR>: B-untime.patch for libdiginet/fuzz_transport's
# image-B core.
#
# The image-A core's commit 3b8ca450689 ran `untime --commit libdiginet/fuzz_transport` (tools/publish/untime): rule
# a, the token `timeout 30` of the first arm of lib/A/ACeg.v's shok_auto_with goes, with the timeout-ok marker
# comment on its line; the timed tactic and the fallback arm stay; one row (file, first line, lines, sha256 of the
# marker's text) goes to the unit's clean index provenance/evidence/untime-removed.tsv, and the marker's text to the
# verbatim record, which never ships. The image-B core's B/YCeg.v, relocated from the donor, carries the same arm. This
# script runs the same tool, unchanged, with --commit on a copy of UNIT (proofs/libdiginet/fuzz_transport of the tree
# the run is applied to, as a directory: its lib/B/YCeg.v must be byte-equal to the run's stage-out/B/YCeg.v) and
# writes the tool's change of every lib/B file as a --patch against stage-out (paths B/<f>.v, 3 lines of context).
# It prints the clean-index rows the tool appended (the tree's provenance/evidence/untime-removed.tsv takes them too)
# and writes the tool's --report before and after, and the verbatim record, into RECORD_DIR.
#   workdir   a port_core run directory (stage-out/ is read)
#   UNIT      a directory holding the unit's lib/ and provenance/evidence/ (untime-removed.tsv and the MANIFESTs)
#   TOOLS     a tools/ folder holding publish/untime and oft/ (the publish/t14-untime release)
set -euo pipefail
WORK=$1 UNIT=$2 TOOLS=$3 OUT=$4 REC=$5
U=proofs/libdiginet/fuzz_transport
cmp -s "$UNIT/lib/B/YCeg.v" "$WORK/stage-out/B/YCeg.v" || { echo "cutuntime-B: UNIT's lib/B/YCeg.v is not the run's" >&2; exit 5; }
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
mkdir -p "$TMP/$U" "$REC/verbatim" && cp -a "$UNIT/." "$TMP/$U/"
(cd "$TMP" && git init -q && git add -A && git -c user.email=x@x -c user.name=x commit -qm base)
ut() { (cd "$TMP" && python3 "$TOOLS/publish/untime" --oft "$TOOLS" "$@"); }
ut --report libdiginet/fuzz_transport > "$REC/untime-B.before.txt" 2>&1 || true
ut --commit libdiginet/fuzz_transport --record-dir "$REC/verbatim"
ut --report libdiginet/fuzz_transport > "$REC/untime-B.after.txt" 2>&1
: > "$OUT"
for f in $(cd "$TMP" && git diff --name-only HEAD~1 HEAD -- "$U/lib" | LC_ALL=C sort); do
  r=${f#$U/lib/}
  case $r in
    B/*) diff -u --label "$r" --label "$r" "$WORK/stage-out/$r" "$TMP/$f" >> "$OUT" || true ;;
    *) echo "cutuntime-B: the tool changed $r, outside lib/B" >&2; exit 6 ;;
  esac
done
(cd "$TMP" && git diff HEAD~1 HEAD -- "$U/provenance/evidence/untime-removed.tsv" | sed -n 's/^+\([^+]\)/\1/p')
echo "$OUT: $(grep -c '^+++ ' "$OUT") files"
