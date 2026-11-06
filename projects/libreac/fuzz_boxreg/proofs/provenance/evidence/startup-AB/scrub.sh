#!/bin/bash
# The four cleaned copies of start-up inputs that stay outside git, written by scrub.py beside this file. In each, the
# scanner flags only bytes that the tool reading the file does not read:
#   startup-A/inputs/AF0m.v.prev and startup-B/inputs/YF0m.v1base.prev, startup-B/inputs/YF0m.v.prev: line 5, the
#     notice comment of the af0m run that wrote the file. gen_ad1k.py reads --owned only through gen_ad2.owned_static
#     and its zero_shadow (the `Definition <x>_owned_static` and `Definition <x>_zero_shadow` bodies); ae3i.py reads it
#     only from `Definition Tfib_owned_static` to the next `].`.
#   startup-A/inputs/fuzz_boxreg.asan.compose.json: the value of its "img" member (the image's path when the composer
#     ran). universe.py reads only its "results", "ipc" and "ctxs" members.
# Each copy's record (startup-A/scrub/, startup-B/scrub/) is its diff from the original with the removed text shown
# only as <redacted>. Each run.sh that reads a copy was run on the original and on the copy, and its outputs were
# byte-identical (the copy's row in its slice's README.md).
#
# Environment: SCANNER = the name and path scanner of record; REPO = this checkout; AF0M_V_PREV, YF0M_V1BASE_PREV,
# YF0M_V_PREV, COMPOSE_A = the originals (each checked against its sha256 below by scrub.py).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
: "${SCANNER:?}" "${REPO:?}" "${AF0M_V_PREV:?}" "${YF0M_V1BASE_PREV:?}" "${YF0M_V_PREV:?}" "${COMPOSE_A:?}"
EV=proofs/libreac/fuzz_boxreg/provenance/evidence
s() { python3 -B "$HERE/scrub.py" --scanner "$SCANNER" --repo "$REPO" "$@"; }
s --orig-sha256 f2a61027cb7496dfe51f2ba64433b825ed6b4cd08a4abf1276a22ec2b22bcac4 "$AF0M_V_PREV" \
  $EV/startup-A/inputs/AF0m.v.prev $EV/startup-A/scrub/AF0m.v.prev.diff line:5
s --orig-sha256 ded187c73ca93ef17c68975874c28b01f4edceaf36c8087463aaa0f8efe9dee6 "$YF0M_V1BASE_PREV" \
  $EV/startup-B/inputs/YF0m.v1base.prev $EV/startup-B/scrub/YF0m.v1base.prev.diff line:5
s --orig-sha256 6a8225b73169fdc6bdf9fcaa956389a097c7537f8d90a71cf42f808f1c05e7e4 "$YF0M_V_PREV" \
  $EV/startup-B/inputs/YF0m.v.prev $EV/startup-B/scrub/YF0m.v.prev.diff line:5
s --orig-sha256 d6e2a5d74f39a33e1eedfab696767b1002169c20d7d5a71087f93b4dd55fc5a3 "$COMPOSE_A" \
  $EV/startup-A/inputs/fuzz_boxreg.asan.compose.json $EV/startup-A/scrub/fuzz_boxreg.asan.compose.json.diff json-str:img
