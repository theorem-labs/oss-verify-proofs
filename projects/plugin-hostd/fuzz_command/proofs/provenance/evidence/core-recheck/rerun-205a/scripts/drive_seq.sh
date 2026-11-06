#!/usr/bin/env bash
# The rerun-0d24 commands (its scripts/drive.sh and scripts/drive_plants.sh) on the same inputs, under
# port_addr_check 0d24592683b6 (identity check) and 205a90fd19b8, ONE RUN AT A TIME at nice 19 (the machine's
# page cache is shared). Each run goes through the record's scripts/run_gate.sh, unchanged, which refuses a
# tool whose sha256 does not start with the version asked.
# Usage: drive_seq.sh VERSION [RUN...]   RUN in RA RB PA-base PA-plant PB-base PB-plant (default: all six)
# $W: the work directory: img/ (the eight image copies), tree/donor + tree/ours (git archive extracts),
# plant/ (mkplants.py output), runs/. $PAC: the directory of the tool owner's versioned copies (<sha12>/ each).
# $BIN: the pinned donor binaries (their SHA256SUMS, sha256 c5f896249572).
set -u
W=${W:?set W to the work directory}
export PAC=${PAC:?set PAC to the directory of the versioned tool copies}
export BIN=${BIN:?set BIN to the pinned donor binaries}
export RUN=$W/runs
IMG=$W/img
TREE=$W/tree
PLANT=$W/plant
G=$(dirname "$0")/run_gate.sh
v=$1; shift
runs=("$@"); [ ${#runs[@]} -gt 0 ] || runs=(RA RB PA-base PA-plant PB-base PB-plant)
mkdir -p "$RUN"

AS="A=$IMG/cgif.A.pin:$IMG/cgif.A.twin"
AD="A=$IMG/cmd.A.pin:$IMG/cmd.A.twin"
BS="B=$IMG/cgif.B.pin:$IMG/cgif.B.twin"
BD="B=$IMG/cmd.B.pin:$IMG/cmd.B.twin"
IA=(--include AB1v.v --include ACeg.v --include AE6k.v --include AE7d.v
    --dst-include AB1v.v --dst-include ACeg.v --dst-include AE6k.v --dst-include AE7d.v)
IB=(--include YB1v.v --include YCeg.v --include YE30.v --include YE7d.v
    --dst-include YB1v.v --dst-include YCeg.v --dst-include YE30.v --dst-include YE7d.v)

for r in "${runs[@]}"; do
  n="$r-${v:0:4}"
  case $r in
    RA) a=("$TREE/donor/A" "$TREE/ours/A" "$AS" "$AD" --include 'A*.v' --dst-include 'A*.v') ;;
    RB) a=("$TREE/donor" "$TREE/ours/B" "$BS" "$BD" --include 'Y*.v' --dst-include 'Y*.v') ;;
    PA-base|PA-plant) a=("$TREE/donor/A" "$PLANT/A-${r#PA-}" "$AS" "$AD" "${IA[@]}") ;;
    PB-base|PB-plant) a=("$TREE/donor" "$PLANT/B-${r#PB-}" "$BS" "$BD" "${IB[@]}") ;;
    *) echo "unknown run $r" >&2; exit 2 ;;
  esac
  echo "== $n"
  nice -n 19 "$G" "$n" "$v" "${a[@]}" > "$RUN/$n.log" 2>&1
  cat "$RUN/$n.log"
  tail -n 1 "$RUN/$n/stderr.txt" 2>/dev/null
done
