#!/usr/bin/env bash
# Interceptor inventory of uci, egress and wire image B, then the committed slice commit/. env.sh (not committed) sets
# the paths of the unstripped twins: UCI_U, EGRESS_U, WIRE_U.
set -euo pipefail
cd "$(dirname "$0")"
source ./env.sh
(cd tools && sha256sum *.py) > tools.sha256
sha256sum "$UCI_U" "$EGRESS_U" "$WIRE_U" > images.sha256
python3 tools/inventory.py fuzz_uci "$UCI_U" inventory-uci.tsv > summary-uci.out &
python3 tools/inventory.py fuzz_egress "$EGRESS_U" inventory-egress.tsv > summary-egress.out &
python3 tools/inventory.py fuzz_wire "$WIRE_U" inventory-wire.tsv > summary-wire.out &
wait
rm -rf tools/__pycache__
# the committed slice: raw outputs with every image path rewritten to its token (scrub_out.py refuses any leftover)
python3 tools/scrub_out.py . --tooldir tools \
  --img UCI_B_TWIN "$UCI_U" 'fuzz_uci.asan-ubsan, the unstripped twin of the pinned image of index/binaries.tsv:7521' \
  --img EGRESS_B_TWIN "$EGRESS_U" 'fuzz_egress.asan-ubsan, the unstripped twin of the pinned image of index/binaries.tsv:7513' \
  --img WIRE_B_TWIN "$WIRE_U" 'fuzz_wire.asan-ubsan, the unstripped twin of the pinned image of index/binaries.tsv:7525'
echo done
