#!/usr/bin/env bash
# One port_addr_check run of the core-recheck gate re-run, on the build VM.
# Usage: run_gate.sh NAME VER SRC DST SRCIMG DSTIMG [extra args...]
#   NAME   run directory name under $RUN
#   VER    expected sha256 prefix (12 hex) of port_addr_check.py in $PAC/$VER
# Writes $RUN/NAME/{full.tsv,summary.out,stderr.txt,rc}. Full output (every row),
# --paired-only, --fail-on-flags, as the record's gate runs did. The trees are the
# local `git archive` extracts of the two checked commits ($TREE/donor, $TREE/ours),
# the images the pinned copies in $IMG, the donor set $BIN.
set -u
name=$1; ver=$2; src=$3; dst=$4; si=$5; di=$6; shift 6
T=$PAC/$ver
[ "$(sha256sum < "$T/port_addr_check.py" | cut -c1-12)" = "$ver" ] || { echo "not $ver" >&2; exit 2; }
d=$RUN/$name
mkdir -p "$d" || exit 2
cd "$d" || exit 2
mkdir -p cache
start=$(date -u +%FT%TZ)
python3 "$T/port_addr_check.py" --src "$src" --dst "$dst" \
  --src-image "$si" --dst-image "$di" --donors-from "$BIN" --cache cache \
  --paired-only --summary --fail-on-flags --out full.tsv "$@" > summary.out 2> stderr.txt
rc=$?
echo "rc=$rc start=$start end=$(date -u +%FT%TZ)" > rc
cat rc
