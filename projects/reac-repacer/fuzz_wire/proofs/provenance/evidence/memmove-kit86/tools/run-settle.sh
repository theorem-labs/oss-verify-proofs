#!/bin/sh
# Settle every target the kit leaves unsettled, on one or both images.
#   usage: WIRE=<dir of fuzz_wire.*.unstripped> PCAPU=<dir of the fuzz_pcap twins> PCAPP=<dir of the fuzz_pcap pins> \
#          run-settle.sh [asan|asan-ubsan ...]
# It expects, beside it: a fresh copy of cmpkit 86da41d3ef68 in ./kit, the kit outputs of this record in ./rec
# (closure-<image>.txt, paircl-<image>.txt, paircl-targets-<image>.tsv, jtcheck-<image>.txt) and ./tools.
cd "$(dirname "$0")/.." || exit 1
export PYTHONDONTWRITEBYTECODE=1
: "${WIRE:?set WIRE}" "${PCAPU:?set PCAPU}" "${PCAPP:?set PCAPP}"
mkdir -p out
for t in ${*:-asan asan-ubsan}; do
  python3 tools/settle3.py kit "$WIRE/fuzz_wire.$t.unstripped" "$PCAPP/fuzz_pcap.$t" "$PCAPU/fuzz_pcap.$t" \
    rec/closure-$t.txt rec/paircl-$t.txt rec/paircl-targets-$t.tsv rec/jtcheck-$t.txt tools/luiclass.tsv \
    out/settle-$t > out/settle-$t-summary.txt &
done
wait
for t in ${*:-asan asan-ubsan}; do echo "== $t"; cat out/settle-$t-summary.txt; done
