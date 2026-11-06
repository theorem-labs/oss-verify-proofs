#!/usr/bin/env bash
# startup-Y/collector: re-derive lib/Reusable/YB03.v and lib/Reusable/YB01.v of libreac/fuzz_disco from the
# collector's printed results (dumps/), the released donor headers and the image B pin.
#   TREE   a checkout of the series base (the repository root)
#   IMG_B  the image B pin, fuzz_disco.asan-ubsan (index/binaries.tsv row libreac fuzz_disco asan-ubsan)
#   OUT    where to write (default: ./out)
#   PASS1_LOG, PASS2_LOG  optional: the collector's build logs; when given, the dumps are re-extracted from them first
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
HERE="$(cd "$(dirname "$0")" && pwd)"
: "${TREE:?set TREE}" "${IMG_B:?set IMG_B}"
OUT="${OUT:-./out}"; mkdir -p "$OUT"
DUMPS="$HERE/dumps"
if [ -n "${PASS1_LOG:-}" ] && [ -n "${PASS2_LOG:-}" ]; then
  DUMPS="$OUT/dumps"; mkdir -p "$DUMPS"
  python3 "$HERE/extract_dumps.py" "$PASS1_LOG" "$DUMPS/pass1.dump" JSDUMP
  python3 "$HERE/extract_dumps.py" --part-bytes 4194304 "$PASS2_LOG" "$DUMPS/pass2.dump" HSDUMPHOLES HSDUMP
  cmp "$DUMPS/pass1.dump" "$HERE/dumps/pass1.dump"
  for p in "$HERE"/dumps/pass2.dump.??; do cmp "$DUMPS/$(basename "$p")" "$p"; done
fi
# the pass-2 extract is shipped in parts under the repository's file-size cap: join them
mkdir -p "$OUT/dumps"; cat "$DUMPS"/pass2.dump.?? > "$OUT/dumps/pass2.dump"
DONOR="$TREE/proofs/cgif/cgif_file_fuzzer/lib"
SHIP="$TREE/proofs/libreac/fuzz_disco/lib/Reusable"
export OSSV_BINARIES_TSV="$TREE/index/binaries.tsv"
T="$HERE/tools"
# 1. the join state and the 50 hand-off states, in the donor's module paths (hsform's pin, KImg and descriptor gates run)
python3 "$T/hsform.py" js "$DUMPS/pass1.dump" "$OUT/YB03.donor.v" --header "$DONOR/YB03.v" --qualify-kinds APC --image "$IMG_B"
python3 "$T/hsform.py" hs "$OUT/dumps/pass2.dump" "$OUT/YB01.donor.v" --header "$DONOR/YB01.v" --nholes 50 --image "$IMG_B" \
  --report-json "$OUT/YB01.v.json"
# 2. the unit's module paths and its one Modified line (the note is the shipped file's own fourth line)
for f in YB03 YB01; do
  note="$(sed -n 4p "$SHIP/$f.v" | sed -e 's/^(\* Modified by Theorem Labs, 2026-10: //' -e 's/ \*)$//')"
  python3 "$T/to_disco.py" "$OUT/$f.donor.v" "$OUT/$f.v" "$note"
done
# 3. byte equality with the shipped files and with the recorded per-hole table
cmp "$OUT/YB03.v" "$SHIP/YB03.v"; cmp "$OUT/YB01.v" "$SHIP/YB01.v"; cmp "$OUT/YB01.v.json" "$HERE/YB01.v.json"
echo "collector: YB03.v, YB01.v and YB01.v.json reproduced byte for byte"
