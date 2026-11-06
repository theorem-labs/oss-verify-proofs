#!/bin/sh
# Control of palist.py's image-B form: on libreac/fuzz_decode's pinned fuzz_decode.asan-ubsan (the asan-ubsan pin of
# projects/libreac/fuzz_decode/harness.yaml) and its unstripped twin, with that unit's released names, the renderer
# must give fuzz_decode's released lib/B/Prog/DecodeBSyms.v, DecodeBAddr.v and DecodeBList.v (origin/ossv/recipes
# 88154566652a) byte for byte. The released files' sha256 are below.
# Usage: control.sh IMAGE UNSTRIPPED_TWIN OUTDIR
set -eu
pin=5d05689fd5b196976890b91e68c113953d385775b9d811ef98c712b2cac7d4a9
have=$(sha256sum < "$1" | cut -c1-64)
[ "$have" = "$pin" ] || { echo "control.sh: $1 is sha256 $have, not the pin $pin" >&2; exit 1; }
here=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$3"
python3 "$here/palist.py" "$1" "$2" \
  --first LLVMFuzzerTestOneInput --end __wrap_getenv \
  --extra __asan_shadow_memory_dynamic_address __asan_option_detect_stack_use_after_return \
  --pre OssFuzzTheorems.Proofs.libreac.fuzz_decode.lib.B.Prog \
  --pre-pa OssFuzzTheorems.Proofs.libreac.fuzz_decode.lib.A.Prog --img fuzz_decode.asan-ubsan \
  --project libreac --unit decodeb --ty dbsym --cp DB_ --mod-syms DecodeBSyms \
  --outdir "$3" --out DecodeBSyms.v DecodeBAddr.v DecodeBList.v
cd "$3"
sha256sum -c <<'EOF'
0c2805f933b970ff3612270e10edbd55265b8fe142566a27b3ba6bd168213395  DecodeBSyms.v
9251153ab63e99f01fd3831747f9c9df465d94528fc345c0de8d72584acb0aef  DecodeBAddr.v
e34cda42d89491ab42dd644b8db8a5f86689464741dddc029653b75cbaee656c  DecodeBList.v
EOF
