#!/bin/bash
# run-knockB.sh <unit> <target lib> <workdir> <file list> [extra port_core args]
# The knock-donor rows of the image-B core (the empty-depot form, the unit owner's one patch set): each file of <file list>
# (Y<x>.v names, the lib/AU twins of the image-A donor map's knock rows) is relocated from fuzz_knock's RELEASED image-B
# text, origin/ossv/recipes 88154566652a proofs/libreac/fuzz_knock/lib/AU over lib/Reusable (mkdon.sh ... fuzz_knock AU),
# onto <unit>.asan-ubsan with port_core 7a74e72920e6 in B mode; shared kernel files are kept from the target lib.
# Donor image fuzz_knock.asan-ubsan (pin f834165f5002, unstripped twin 6b6e06f3c924); --old-prog 7eed0:7f700 by the rule
# LLVMFuzzerTestOneInput .. end of the last program function before __wrap_getenv (control: fuzz_grant asan 806b0:857dc).
# Renames: knock's image-B record names TfibSyms / TfibB* -> <Unit>Syms / <Unit>B*.
set -uo pipefail
UNIT=$1 LIB=$2 WORK=$3 FILES=$4; shift 4
U=$(python3 -c "import sys; u=sys.argv[1].split('_',1)[1]; print(u[0].upper()+u[1:])" "$UNIT")
S=${S:?set S to a scratch dir holding donB-knock: HUB=<clone> mkdon.sh 88154566652a fuzz_knock AU \$S/donB-knock}
REL=${REL:?set REL to the extracted tools/pg-reloc/7a74e72920e6}
P=${P:?set P to the libreac result directory holding bin/fuzz_knock}
R=${R:?set R to the reac-repacer result directory holding bin/ and unstripped/ of the unit}
python3 "$REL/port_core.py" \
  --src-lib "$S/donB-knock/proofs/libreac/fuzz_knock/lib" \
  --src-mod OssFuzzTheorems.Proofs.libreac.fuzz_knock.lib \
  --src-images OssFuzzTheorems.libreac.fuzz_knock.images \
  --old-elf "$P/bin/fuzz_knock/fuzz_knock.asan-ubsan" \
  --old-syms "$(cd "$(dirname "$0")" && pwd)/fuzz_knock.asan-ubsan.syms.txt" \
  --old-prog 7eed0:7f700 \
  --target-lib "$LIB" \
  --target-mod OssFuzzTheorems.Proofs.reac_repacer.$UNIT.lib \
  --target-images OssFuzzTheorems.reac_repacer.$UNIT.images \
  --target-name reac-repacer/$UNIT \
  --target-elf "$R/bin/$UNIT/$UNIT.asan-ubsan" \
  --target-syms "$R/unstripped/$UNIT/$UNIT.asan-ubsan" \
  --files "$FILES" \
  --rename TfibSyms=${U}Syms --rename TfibB=${U}B --rename TfibB_syms=${U}B_syms --rename TfibB_ok=${U}B_ok \
  --rename TfibB_pair=${U}B_pair \
  --remap-images --reusable-dir B --kernel-dir Reusable \
  --kernel-image "$P/bin/fuzz_knock/fuzz_knock.asan" \
  --known-elf "$R/bin/$UNIT/$UNIT.asan" \
  --known-elf "$P/bin/fuzz_knock/fuzz_knock.asan" \
  --work "$WORK" "$@"
