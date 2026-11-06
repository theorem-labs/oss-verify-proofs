#!/bin/sh
# Reruns every measurement of this slice and rewrites its tables and MANIFEST.md (needs pyelftools).
#   IMG_A / TWIN_A  fuzz_uci.asan pin and its unstripped twin
#   IMG_B / TWIN_B  fuzz_uci.asan-ubsan pin and its unstripped twin
#   LOG             the cb build log of record of lib/B/UciBClose.vo (for records/)
# (env.example.sh names them). Checks each image against its pin first.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
chk() { have=$(sha256sum < "$1" | cut -c1-64); [ "$have" = "$2" ] || { echo "run.sh: $1 is $have, not $2" >&2; exit 1; }; }
chk "$IMG_A" 6ea017c24525e6946fa06dc7e3075459ad2c5146d59af49873bf3c51a46e885d
chk "$TWIN_A" 56822e263d767986a76ec862cbfbee7571b0e64df2413ad18d7201205a7563fb
chk "$IMG_B" a1b86e424adde6f65d345459822690a6c21e9e606446b91b4ad25e9f3ef6e7fc
chk "$TWIN_B" 8d07ffcf594874884207465cc34ff9f3b1062f21f6d9b3622e0771fa76490b16
mkdir -p "$here/tables" "$here/records"
python3 "$here/scripts/dis_rv64.py" "$IMG_A" "$TWIN_A" "$here/tables" A
python3 "$here/scripts/dis_rv64.py" "$IMG_B" "$TWIN_B" "$here/tables" B
python3 "$here/scripts/cells.py" "$IMG_A" "$TWIN_A" > "$here/tables/cells-A.txt"
python3 "$here/scripts/cells.py" "$IMG_B" "$TWIN_B" > "$here/tables/cells-B.txt"
python3 "$here/scripts/mk_record.py" "$LOG" "$here"
python3 "$here/scripts/mk_slice_manifest.py" "$here"
