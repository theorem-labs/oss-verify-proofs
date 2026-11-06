#!/usr/bin/env bash
# startup-Y/ycej: re-derive the generated trace lists of lib/Reusable/YCej.v of libreac/fuzz_disco (ycej.gen.v) from the
# image B pin's .text and the function symbols of its unstripped twin (fuzz_disco.asan-ubsan.syms.txt).
#   IMG_B   the image B pin, fuzz_disco.asan-ubsan (index/binaries.tsv row libreac fuzz_disco asan-ubsan)
#   TWIN_B  optional: the pin's unstripped twin; when given, the symbol extract is made again from it first and compared
#   OUT     where to write (default: ./out)
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
HERE="$(cd "$(dirname "$0")" && pwd)"
: "${IMG_B:?set IMG_B}"
OUT="${OUT:-./out}"; mkdir -p "$OUT"
SYMS="$HERE/fuzz_disco.asan-ubsan.syms.txt"
if [ -n "${TWIN_B:-}" ]; then
  SYMS="$OUT/fuzz_disco.asan-ubsan.syms.txt"
  python3 "$HERE/extract_syms.py" "$TWIN_B" "$IMG_B" "$SYMS"
  cmp "$SYMS" "$HERE/fuzz_disco.asan-ubsan.syms.txt"
fi
# gen_traces.py names the image file in its first output line; the run of record read the pin under the name fuzz_disco
mkdir -p "$OUT/img"; ln -sfn "$(readlink -f "$IMG_B")" "$OUT/img/fuzz_disco"
# --ipc: the pc each interceptor records (the return address of its GetCurrentPc call); --fp: LLVMFuzzerTestOneInput
# keeps its frame pointer and its caller's call returns to 0x80eb8; --exclude: the libunwind FDE cache's two calls are
# the runtime's error path, not a healthy run
python3 "$HERE/gen_traces.py" "$OUT/img/fuzz_disco" "$SYMS" --ipc malloc=0x536f8 --ipc free=0x53598 \
  --fp LLVMFuzzerTestOneInput=0x80eb8 --exclude _ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE3addEmmmm \
  > "$OUT/ycej.gen.v"
cmp "$OUT/ycej.gen.v" "$HERE/ycej.gen.v"
echo "ycej: ycej.gen.v reproduced byte for byte"
