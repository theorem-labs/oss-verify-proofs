#!/bin/sh
# Regenerates lib/A/Prog/DgnTransportSyms.v, DgnTransportAddr.v and DgnTransportList.v of this unit from
# fuzz_transport.asan (the asan pin of projects/libdiginet/fuzz_transport/harness.yaml) and its unstripped twin, with
# palist.py (needs pyelftools).
# Usage: run.sh IMAGE UNSTRIPPED_TWIN
set -eu
pin=e89be137db17b720e0310addc2dcc601998945478a9102e6a9850b0566106350
have=$(sha256sum < "$1" | cut -c1-64)
[ "$have" = "$pin" ] || { echo "run.sh: $1 is sha256 $have, not the pin $pin" >&2; exit 1; }
here=$(cd "$(dirname "$0")" && pwd)
python3 "$here/palist.py" "$1" "$2" \
  --first LLVMFuzzerTestOneInput --end __wrap_getenv \
  --extra __asan_shadow_memory_dynamic_address __asan_option_detect_stack_use_after_return \
  --pre OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib.A.Prog --img fuzz_transport.asan --project libdiginet \
  --unit transport --ty tsym --cp TS_ --mod-syms DgnTransportSyms \
  --outdir "$here/../../../../lib/A/Prog" --out DgnTransportSyms.v DgnTransportAddr.v DgnTransportList.v
