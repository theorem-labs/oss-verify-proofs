#!/usr/bin/env bash
# Extra run: lib/Reusable describes fuzz_command's PLAIN image (Reusable/YH00.v: src0segs := zsegs of images.Plain;
# measured: src0_A_memcpy 0x20510 = memcpy in fuzz_command.plain a20873dc7f0e), while the value gate's RU run of
# record is keyed B. Gate the same RU TSV with the plain images in place of B (the TSV's key column stays `B`):
# donor cgif_file_fuzzer.plain (pin 19dedd1bc682, twin 6ab540c43108), target fuzz_command.plain (pin a20873dc7f0e,
# twin fbe3a48ad296). Normal and --moved.
set -eu
cd "$(dirname "$0")"
[ "$(sha256sum < tool/roundconst.py | cut -c1-12)" = 32b39f3b34e9 ] || { echo "roundconst.py is not 32b39f3b34e9" >&2; exit 2; }
DP="B=img/cgif.P.pin:img/cgif.P.twin"; TP="B=img/cmd.P.pin:img/cmd.P.twin"
mkdir -p main
python3 tool/roundconst.py in/RU.full.tsv.gz "$DP" "$TP" main/rc-UP > main/rc-UP.summary 2> main/rc-UP.stderr &
python3 tool/roundconst.py in/RU.full.tsv.gz "$DP" "$TP" main/mv-UP --moved > main/mv-UP.summary 2> main/mv-UP.stderr &
wait
echo DONE
