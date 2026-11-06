#!/bin/sh
# Regenerates lib/B/Prog/DgnTransportBSyms.v, DgnTransportBAddr.v and DgnTransportBList.v of this unit from
# fuzz_transport.asan-ubsan (the asan-ubsan pin of projects/libdiginet/fuzz_transport/harness.yaml) and its unstripped
# twin, with palist.py (needs pyelftools). Image B's form: the listing modules are lib.B.Prog's and PaTable is the
# image-generic one of lib.A.Prog (--pre-pa), as in fuzz_decode's released lib/B/Prog/DecodeBAddr.v and DecodeBList.v.
# Usage: run.sh IMAGE UNSTRIPPED_TWIN (the twin used: sha256 e217cb0a84f1e1810805155304b281a259ef83a85f50efcf0c65b40697bfa4dc;
# names only, palist.py checks that its listed words equal the image's). Outputs' sha256: SHA256SUMS (from the unit dir:
# sha256sum -c provenance/evidence/prog-gen/B/SHA256SUMS). Control of the image-B form: control.sh. --pinned: the three files'
# headers name the image as 'the pinned fuzz_transport.asan-ubsan image (sha256 41113a03c82f)'.
set -eu
pin=41113a03c82fde8282db830ab5f4fbe376e392a38d22670b8cb8c9f02969ece4
have=$(sha256sum < "$1" | cut -c1-64)
[ "$have" = "$pin" ] || { echo "run.sh: $1 is sha256 $have, not the pin $pin" >&2; exit 1; }
here=$(cd "$(dirname "$0")" && pwd)
python3 "$here/palist.py" "$1" "$2" \
  --first LLVMFuzzerTestOneInput --end __wrap_getenv \
  --extra __asan_shadow_memory_dynamic_address __asan_option_detect_stack_use_after_return \
  --pre OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib.B.Prog \
  --pre-pa OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib.A.Prog --img fuzz_transport.asan-ubsan --pinned \
  --project libdiginet --unit transportb --ty tbsym --cp TB_ --mod-syms DgnTransportBSyms \
  --outdir "$here/../../../../lib/B/Prog" --out DgnTransportBSyms.v DgnTransportBAddr.v DgnTransportBList.v
