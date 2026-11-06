#!/bin/bash
# mkdon-sm1.sh <rev> <out>: fuzz_grant's RELEASED lib at <rev>, normalised as core-A's run.sh says (its DON): Reusable/*
# moved to the lib root, module text ...fuzz_grant.lib.Reusable -> ...fuzz_grant.lib. Prints DON.
#   HUB=<clone of the proofs repository> mkdon-sm1.sh 4f87de75d67 <out>
set -euo pipefail
REV=$1 OUT=$2
HUB=${HUB:?set HUB to a clone of the proofs repository holding <rev>}
D=$OUT/proofs/libreac/fuzz_grant/lib
rm -rf "$OUT"; mkdir -p "$D"
git -C "$HUB" archive "$REV" proofs/libreac/fuzz_grant/lib | tar -x -C "$D" --strip-components=4
cd "$D"
mv Reusable/* .
rmdir Reusable
find . -name '*.v' -print0 | xargs -0 perl -pi -e \
  's/OssFuzzTheorems\.Proofs\.libreac\.fuzz_grant\.lib\.Reusable/OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib/g'
echo "$D"
