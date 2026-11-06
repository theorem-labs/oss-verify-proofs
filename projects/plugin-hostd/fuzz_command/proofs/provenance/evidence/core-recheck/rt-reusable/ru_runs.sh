#!/usr/bin/env bash
# Value-gate run (port_addr_check 3d2eee813cce via pac.sh) of cgif_file_fuzzer's root Y*.v against our lib/Reusable/Y*.v
# with the PLAIN images (key P). Run RU (key B) read these files against the ASan+UBSan images; the files that
# describe the plain build (src0_* names, users state runs over Images.plain) are judged here against their own build.
# Usage: ru_runs.sh RUP | CtlCgifP     (ROOT, WIMG, PAC as in rt_runs.sh)
set -u
ROOT=${ROOT:-$(cd "$(dirname "$0")" && pwd)}
WIMG=${WIMG:-$ROOT/work/img}              # cgif.P.{pin,twin} (pin 19dedd1bc682, twin 6ab540c43108),
                                          # cmd.P.{pin,twin}  (pin a20873dc7f0e, twin fbe3a48ad296)
PAC=${PAC:-$RUN/pac.sh}
REL=../out/rt-reusable/runs
CG=c8557374ad2e:proofs/cgif/cgif_file_fuzzer/lib
CM=a3c671fb9bb:proofs/plugin-hostd/fuzz_command/lib
I_CP="P=$WIMG/cgif.P.pin:$WIMG/cgif.P.twin"; I_MP="P=$WIMG/cmd.P.pin:$WIMG/cmd.P.twin"
for r in "$@"; do
  case $r in
    RUP) $PAC $REL/RUP "$CG" "$CM/Reusable" "$I_CP" "$I_MP" --include 'Y*.v' --dst-include 'Y*.v' ;;
    # donor-on-donor control for the new image pair: cgif's YH03.v with the cgif plain image on both sides
    CtlCgifP) $PAC $REL/CtlCgifP "$CG" "$CG" "$I_CP" "$I_CP" --include 'YH03.v' --dst-include 'YH03.v' ;;
    *) echo "unknown $r" >&2; exit 2 ;;
  esac
  echo "$r $(cat "$ROOT/runs/$r/rc") $(tail -1 "$ROOT/runs/$r/stderr.txt")"
done
