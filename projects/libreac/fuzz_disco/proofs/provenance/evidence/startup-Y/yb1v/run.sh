#!/usr/bin/env bash
# startup-Y/yb1v: re-derive lib/Reusable/YB1v.v of libreac/fuzz_disco (the musl and exit-guard decode windows) from its
# four window values, then derive the same four values from the image B pin's .text and two symbols of its twin.
#   TREE    a checkout of the series base (the repository root)
#   IMG_B   the image B pin, fuzz_disco.asan-ubsan (index/binaries.tsv row libreac fuzz_disco asan-ubsan)
#   TWIN_B  optional: the pin's unstripped twin; when given, the symbol extract is made again from it first and compared
#   OUT     where to write (default: ./out)
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
HERE="$(cd "$(dirname "$0")" && pwd)"
: "${TREE:?set TREE}" "${IMG_B:?set IMG_B}"
OUT="${OUT:-./out}"; mkdir -p "$OUT"
SHIP="$TREE/proofs/libreac/fuzz_disco/lib/Reusable"
# 1. the four values of record, read by hand from the image's symbols and sections: sysconf (the first musl function),
#    the 4-byte slots from it to the end of .text, oft_exit_guard, its four instructions
MUSL_START=0x8f6b0 MUSL_COUNT=16102 GUARD_START=0x80f44 GUARD_COUNT=4
python3 "$HERE/gen_y.py" "$OUT" "$MUSL_START" "$MUSL_COUNT" "$GUARD_START" "$GUARD_COUNT"
cmp "$OUT/YB1v.v" "$SHIP/YB1v.v"
# 2. the same four values by rule, from the pin's .text section and words and the twin's symbols sysconf / oft_exit_guard
SYMS="$HERE/fuzz_disco.asan-ubsan.yb1v-syms.txt"
if [ -n "${TWIN_B:-}" ]; then
  SYMS="$OUT/fuzz_disco.asan-ubsan.yb1v-syms.txt"
  python3 "$HERE/extract_syms.py" "$TWIN_B" "$IMG_B" "$SYMS" sysconf oft_exit_guard
  cmp "$SYMS" "$HERE/fuzz_disco.asan-ubsan.yb1v-syms.txt"
fi
derived="$(python3 "$HERE/derive_yb1v.py" "$SYMS" "$IMG_B" sysconf oft_exit_guard)"
if [ "$derived" != "$MUSL_START $MUSL_COUNT $GUARD_START $GUARD_COUNT" ]; then
  echo "yb1v: derived values ($derived) differ from the values of record" >&2; exit 1
fi
echo "yb1v: YB1v.v reproduced byte for byte; the four values derived by rule are the values of record ($derived)"
