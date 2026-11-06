#!/usr/bin/env bash
# Roundconst gate v2 (roundconst.py sha256 32b39f3b34e9) on the full TSVs of the value gate (port_addr_check
# 3d2eee813cce): RA (donor lib/A -> unit lib/A, key A), RB (donor lib/Y*.v -> unit lib/B, key B), RU (donor lib/Y*.v
# -> unit lib/Reusable, key B), and the donor-on-donor controls CA, CB. Images keyed with their unstripped twins.
# Usage: run_main.sh IMGDIR   (IMGDIR holds cgif.{A,B}.{pin,twin} and cmd.{A,B}.{pin,twin}; in/ holds the gzip'd TSVs)
# At most two gate processes run at once.
set -eu
I=${1:?IMGDIR}
cd "$(dirname "$0")"
G=tool/roundconst.py
[ "$(sha256sum < $G | cut -c1-12)" = 32b39f3b34e9 ] || { echo "roundconst.py is not 32b39f3b34e9" >&2; exit 2; }
DA="A=$I/cgif.A.pin:$I/cgif.A.twin"; TA="A=$I/cmd.A.pin:$I/cmd.A.twin"
DB="B=$I/cgif.B.pin:$I/cgif.B.twin"; TB="B=$I/cmd.B.pin:$I/cmd.B.twin"
run() { # NAME TSV DSPEC TSPEC [flags]
  local n=$1 t=$2 d=$3 s=$4; shift 4
  python3 $G "$t" "$d" "$s" "$n" "$@" > "$n.summary" 2> "$n.stderr"; echo "$n rc=$?" >> rc.log
}
mkdir -p main controls
: > rc.log
run main/rc-A in/RA.full.tsv.gz "$DA" "$TA" &
run main/mv-A in/RA.full.tsv.gz "$DA" "$TA" --moved &
wait
run main/rc-B in/RB.full.tsv.gz "$DB" "$TB" &
run main/mv-B in/RB.full.tsv.gz "$DB" "$TB" --moved &
wait
run main/rc-U in/RU.full.tsv.gz "$DB" "$TB" &
run main/mv-U in/RU.full.tsv.gz "$DB" "$TB" --moved &
wait
# control (1): donor-on-donor, the donor image on both sides (normal and --moved)
run controls/c1-CA in/CA.full.tsv.gz "$DA" "$DA" &
run controls/c1-CB in/CB.full.tsv.gz "$DB" "$DB" &
wait
run controls/c1-CA-mv in/CA.full.tsv.gz "$DA" "$DA" --moved &
run controls/c1-CB-mv in/CB.full.tsv.gz "$DB" "$DB" --moved &
wait
cat rc.log
