#!/usr/bin/env bash
# The route of fuzz_wire's ASan __asan_memmove contract, one image per run: libreac/fuzz_pcap's released lib/<IMG>/Rt/
# Memmove{Def,Im,K,Paths,}.v (origin/ossv/recipes 5098883da0b) -> alreloc (frozen a5c53bb2bed4ad03, with the measured
# resolutions asan-resolve-<IMG>.txt) -> adapt_memmove.py (module layout, symbol record, image end, the added notice).
# The donor's notice lines stay byte for byte; the comment scrub of the unit runs later, on the whole unit tree.
# usage: run.sh A|B WORKTREE        Environment: ALRELOC, WIRE_BIN (fuzz_wire pins + twins), PCAP_TWIN (fuzz_pcap's
#        v1.9.0 unstripped twins).
# Layout: this ran on the unit's first layout, proofs/reac-repacer/fuzz_wire/, the only one alreloc a5c53bb2bed4ad03
# reads (it refuses a tree without proofs/<unit>/lib). The unit now sits at projects/reac-repacer/fuzz_wire/proofs/
# with nothing inside it moved, so the files it wrote are the same files at that path.
set -euo pipefail
IMG=$1 WT=$(cd "$2" && pwd)
case "$IMG" in A) BUILD=asan ;; B) BUILD=asan-ubsan ;; *) echo "run.sh: A or B" >&2; exit 2 ;; esac
P=proofs/reac-repacer/fuzz_wire
HERE=$WT/$P/provenance/evidence/memmove-reloc
FILES="$IMG/Rt/MemmoveDef.v $IMG/Rt/MemmoveIm.v $IMG/Rt/MemmoveK.v $IMG/Rt/MemmovePaths.v $IMG/Rt/Memmove.v"
cd "$WT"
python3 "$ALRELOC" --src libreac/fuzz_pcap --ref 5098883da0b --unit reac-repacer/fuzz_wire --build "$BUILD" --wt "$WT" \
  --resolve "$HERE/asan-resolve-$IMG.txt" --unit-elf "$WIRE_BIN/fuzz_wire.$BUILD.unstripped" \
  --pinned-elf "$WIRE_BIN/fuzz_wire.$BUILD" --src-elf "$PCAP_TWIN/fuzz_pcap.$BUILD" $FILES
python3 "$HERE/adapt_memmove.py" "$IMG" "$P/lib"
echo "run.sh: $IMG done"
