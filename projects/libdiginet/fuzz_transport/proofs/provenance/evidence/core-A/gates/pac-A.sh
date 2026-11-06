#!/bin/bash
# pac-A.sh <src dir (stage)> <dst dir (stage-out or a planted copy)> <out prefix> [extra checker args]
# Gate (a) runner of the libdiginet/fuzz_transport image-A core relocation (row TCA): the versioned
# port_addr_check over the donor text vs the relocated text, both images with their unstripped twins (no symbol
# recovery needed), the flags port_core's gate uses (--paired-only --summary --donors-from DONORS), one default pass,
# --fail-on-flags. libdiginet/fuzz_decode's gates/pac-A.sh (sha256 e6f5f0468baa; internal record) with the pins,
# the image paths and the argument list changed (the checker sha is SHA, default 205a90fd19b8, the version of record
# after 08:00Z; its own donor-recovery cache is OUT.cache, passed as --cache).
# Every input is pinned by sha256 (12 hex); a mismatch exits 5 before the checker runs.
# Environment (no host path is written here; each image is taken from the named directory unless given itself):
#   CKDIR    port_addr_check directory; the checker is CKDIR/versions/<SHA>/port_addr_check.py
#   SHA      checker sha12 (205a90fd19b8)
#   PG       fuzz_grant's image tree (bin/, unstripped/): SRC_IMG SRC_TWIN fuzz_grant.asan c2c7559b29bd + twin 57c26f993615
#   TIMG     fuzz_transport's image dir (stripped/, unstripped/): DST_IMG DST_TWIN fuzz_transport.asan e89be137db17 + twin
#            86efc3a80314
#   DONORS   the symbolised donor tree --donors-from reads (port_core's DONORS, as D9)
# The image key is A on both sides (a build letter: A = asan), so no --image-build is needed.
set -uo pipefail
[ $# -ge 3 ] || { echo "usage: pac-A.sh SRC DST OUTPREFIX [checker args]" >&2; exit 2; }
SRC=$1 DST=$2 OUT=$3; shift 3
SHA=${SHA:-205a90fd19b8}
CKDIR=${CKDIR:?set CKDIR to the port_addr_check directory (versions/<sha12>/ under it)}
SRC_IMG=${SRC_IMG:-${PG:?set PG to the fuzz_grant image tree}/bin/fuzz_grant/fuzz_grant.asan}
SRC_TWIN=${SRC_TWIN:-$PG/unstripped/fuzz_grant/fuzz_grant.asan}
DST_IMG=${DST_IMG:-${TIMG:?set TIMG to the fuzz_transport image dir}/stripped/fuzz_transport.asan}
DST_TWIN=${DST_TWIN:-$TIMG/unstripped/fuzz_transport.asan}
DONORS=${DONORS:?set DONORS to the symbolised donor tree port_addr_check --donors-from reads}
CK=$CKDIR/versions/$SHA/port_addr_check.py
pin() { local h; h=$(sha256sum "$1" 2>/dev/null | cut -c1-12); [ "$h" = "$2" ] || { echo "pac-A: pin mismatch: $1 is ${h:-absent}, not $2" >&2; exit 5; }; }
pin "$CK" "$SHA"
# the checker's helpers (scan_literals.py, inputs_used.py, insn-targets/, identity-quotients/) against the version's own
# list CKDIR/versions/<SHA>.SHA256SUMS
SUMS=$CKDIR/versions/$SHA.SHA256SUMS
[ -f "$SUMS" ] || { echo "pac-A: no $SUMS" >&2; exit 5; }
SUMSOUT=$(cd "$CKDIR/versions/$SHA" && sha256sum -c "$SUMS" 2>&1) || { echo "pac-A: $SUMS does not hold: $SUMSOUT" >&2; exit 5; }
pin "$SRC_IMG" c2c7559b29bd
pin "$SRC_TWIN" 57c26f993615
pin "$DST_IMG" e89be137db17
pin "$DST_TWIN" 86efc3a80314
mkdir -p "$OUT.cache"
PYTHONDONTWRITEBYTECODE=1 python3 "$CK" --src "$SRC" --dst "$DST" \
  --src-image "A=$SRC_IMG:$SRC_TWIN" \
  --dst-image "A=$DST_IMG:$DST_TWIN" \
  --donors-from "$DONORS" --paired-only --out "$OUT.tsv" --summary --cache "$OUT.cache" --fail-on-flags "$@" \
  > "$OUT.log" 2>&1
rc=$?
echo "checker $CK rc=$rc (sha256 $(sha256sum "$CK" | cut -c1-12))" >> "$OUT.log"
echo "checker files: $(echo "$SUMSOUT" | grep -c ': OK$') of $(grep -c . "$SUMS") in versions/$SHA.SHA256SUMS OK" >> "$OUT.log"
PYTHONDONTWRITEBYTECODE=1 python3 "$CK" --list-flag-classes >> "$OUT.log" 2>&1
exit $rc
