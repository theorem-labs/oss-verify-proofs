#!/usr/bin/env bash
# One port_addr_check 3d2eee813cce run. Usage: pac.sh NAME SRC DST SRCIMG DSTIMG [extra args...]
# Writes runs/NAME/{full.tsv,summary.out,stderr.txt,rc}. Full output (every row), --paired-only, --fail-on-flags.
# On the build VM (no git checkout there) a REF:PATH argument of the two checked commits is read from the local
# `git archive` extract of that commit ($W/tree/...), and the donor images from $BIN (a byte copy
# of the pinned donor set, checked against its SHA256SUMS).
set -u
name=$1; src=$2; dst=$3; si=$4; di=$5; shift 5
T=$PAC
[ "$(sha256sum < $T/port_addr_check.py | cut -c1-12)" = 3d2eee813cce ] || { echo "not 3d2eee813cce" >&2; exit 2; }
GIT=(--git $HUB); DON=$BIN
if [ ! -d $HUB ]; then
  GIT=(); DON=$BIN
  loc() { case "$1" in
      c8557374ad2e:*) echo "$DONOR/${1#c8557374ad2e:}" ;;
      a3c671fb9bb:*) echo "$OURS/${1#a3c671fb9bb:}" ;;
      *:*) [ -e "$1" ] && echo "$1" || { echo "pac.sh: no local extract for $1" >&2; exit 2; } ;;
      *) echo "$1" ;; esac; }
  src=$(loc "$src") || exit 2; dst=$(loc "$dst") || exit 2
fi
case "$name" in /*) d=$name ;; *) d=$RUN/$name ;; esac
mkdir -p "$d"; cd "$d" || exit 2
[ -d cache ] || cp -r $RUN/test/cache cache
start=$(date -u +%FT%TZ)
python3 $T/port_addr_check.py "${GIT[@]}" --src "$src" --dst "$dst" \
  --src-image "$si" --dst-image "$di" --donors-from "$DON" --cache cache \
  --paired-only --summary --fail-on-flags --out full.tsv "$@" > summary.out 2> stderr.txt
rc=$?
echo "rc=$rc start=$start end=$(date -u +%FT%TZ)" > rc
