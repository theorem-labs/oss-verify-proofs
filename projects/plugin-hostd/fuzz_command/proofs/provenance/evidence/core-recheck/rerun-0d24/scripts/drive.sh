#!/usr/bin/env bash
# Run the core-recheck RA and RB value gates under both tool versions, in parallel, on the build VM.
# The four runs read the same trees, the same pinned images and the same donor set, so a difference
# between the 3d2e run and the 0d24 run of a gate is the tool's, not the inputs'.
# $W: the work directory (README.md, "Reproducing"): pac/<version>/, runs/, bin/, img/, tree/, pylib/.
set -u
W=${W:?set W to the work directory}
export PAC=$W/pac
export RUN=$W/runs
# pyelftools 0.33 (the tool's one third-party module; the VM has none), copied from the host that staged this run.
export PYTHONPATH=$W/pylib
export BIN=$W/bin
IMG=$W/img
TREE=$W/tree
G=$(dirname "$0")/run_gate.sh

AS="A=$IMG/cgif.A.pin:$IMG/cgif.A.twin"
AD="A=$IMG/cmd.A.pin:$IMG/cmd.A.twin"
BS="B=$IMG/cgif.B.pin:$IMG/cgif.B.twin"
BD="B=$IMG/cmd.B.pin:$IMG/cmd.B.twin"

for v in 3d2eee813cce 0d24592683b6; do
  setsid nohup "$G" "RA-${v:0:4}" "$v" "$TREE/donor/A" "$TREE/ours/A" "$AS" "$AD" \
    --include 'A*.v' --dst-include 'A*.v' > "$RUN/RA-${v:0:4}.log" 2>&1 &
  setsid nohup "$G" "RB-${v:0:4}" "$v" "$TREE/donor"   "$TREE/ours/B" "$BS" "$BD" \
    --include 'Y*.v' --dst-include 'Y*.v' > "$RUN/RB-${v:0:4}.log" 2>&1 &
done
wait
echo "ALL FOUR RUNS ENDED"
for d in "$RUN"/R?-????; do
  echo "== $d: $(cat "$d/rc" 2>/dev/null)"
  tail -n 1 "$d/summary.out" 2>/dev/null
done
