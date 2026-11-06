#!/usr/bin/env bash
# The record's planted controls PA / PB (gate/plants.tsv, gate/mkplants.py), run under both tool versions.
# The plants are made by the record's own mkplants.py from the same extract of the checked tree.
# $W: the work directory (README.md, "Reproducing"): pac/<version>/, runs/, bin/, img/, tree/, pylib/.
set -u
W=${W:?set W to the work directory}
export PAC=$W/pac
export RUN=$W/runs
export PYTHONPATH=$W/pylib
export BIN=$W/bin
IMG=$W/img
TREE=$W/tree
PLANT=$W/plant
G=$(dirname "$0")/run_gate.sh

python3 "$(dirname "$0")/../../gate/mkplants.py" "$TREE/ours" "$PLANT" || exit 2
echo "plants.tsv sha256 $(sha256sum < "$PLANT/plants.tsv" | cut -c1-12)"

AS="A=$IMG/cgif.A.pin:$IMG/cgif.A.twin"
AD="A=$IMG/cmd.A.pin:$IMG/cmd.A.twin"
BS="B=$IMG/cgif.B.pin:$IMG/cgif.B.twin"
BD="B=$IMG/cmd.B.pin:$IMG/cmd.B.twin"
IA=(--include AB1v.v --include ACeg.v --include AE6k.v --include AE7d.v
    --dst-include AB1v.v --dst-include ACeg.v --dst-include AE6k.v --dst-include AE7d.v)
IB=(--include YB1v.v --include YCeg.v --include YE30.v --include YE7d.v
    --dst-include YB1v.v --dst-include YCeg.v --dst-include YE30.v --dst-include YE7d.v)

for v in 3d2eee813cce 0d24592683b6; do
  for k in base plant; do
    setsid nohup "$G" "PA-$k-${v:0:4}" "$v" "$TREE/donor/A" "$PLANT/A-$k" "$AS" "$AD" "${IA[@]}" \
      > "$RUN/PA-$k-${v:0:4}.log" 2>&1 &
    setsid nohup "$G" "PB-$k-${v:0:4}" "$v" "$TREE/donor" "$PLANT/B-$k" "$BS" "$BD" "${IB[@]}" \
      > "$RUN/PB-$k-${v:0:4}.log" 2>&1 &
  done
done
wait
echo "ALL EIGHT PLANT RUNS ENDED"
for d in "$RUN"/P?-*-????; do
  echo "== ${d##*/}: $(cat "$d/rc" 2>/dev/null)"
  tail -n 1 "$d/stderr.txt" 2>/dev/null
done
