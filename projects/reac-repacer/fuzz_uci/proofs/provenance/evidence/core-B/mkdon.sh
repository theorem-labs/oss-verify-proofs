#!/bin/bash
# Normalise a RELEASED unit lib into the image-B donor shape port_core's core-files-Y.txt names:
# root = lib root + Reusable/* (shared / image-A kernel) overlaid by the unit's image-B dir (B/ or ReusableB/),
# module text ...<unit>.lib.Reusable / .lib.<bdir> -> ...<unit>.lib (decode-core run.sh's normalisation, extended to B).
#   HUB=<clone of the proofs repository> mkdon.sh <rev> <unit> <bdir> <out>      e.g. mkdon.sh 4f87de75d67 fuzz_grant B <out>
set -euo pipefail
REV=$1 UNIT=$2 BDIR=$3 OUT=$4
HUB=${HUB:?set HUB to a clone of the proofs repository holding <rev>}
rm -rf "$OUT"; mkdir -p "$OUT"
git -C "$HUB" archive "$REV" "proofs/libreac/$UNIT/lib" | tar -x -C "$OUT"
D=$OUT/proofs/libreac/$UNIT/lib
cd "$D"
nR=$(find Reusable -name '*.v' | wc -l); nB=$(find "$BDIR" -name '*.v' | wc -l)
both=$(comm -12 <(cd Reusable && find . -name '*.v' | sort) <(cd "$BDIR" && find . -name '*.v' | sort) | wc -l)
cp -a Reusable/. .
cp -a "$BDIR"/. .
rm -rf Reusable "$BDIR"
find . -name '*.v' -print0 | xargs -0 sed -i \
  -e "s/OssFuzzTheorems\.Proofs\.libreac\.$UNIT\.lib\.Reusable\b/OssFuzzTheorems.Proofs.libreac.$UNIT.lib/g" \
  -e "s/OssFuzzTheorems\.Proofs\.libreac\.$UNIT\.lib\.$BDIR\b/OssFuzzTheorems.Proofs.libreac.$UNIT.lib/g"
echo "$UNIT@$REV: Reusable $nR .v, $BDIR $nB .v, in both $both (B text wins); root .v now $(ls *.v | wc -l); A/ $(ls A | wc -l)"
echo "left module refs to lib.Reusable / lib.$BDIR: $(grep -rlE "lib\.(Reusable|$BDIR)\b" --include='*.v' . | wc -l)"
