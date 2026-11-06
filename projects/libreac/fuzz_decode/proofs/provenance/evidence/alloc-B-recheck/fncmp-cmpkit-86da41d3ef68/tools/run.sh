#!/bin/bash
# tools/run.sh -- reproduces every out/ and scans/ file of this record from the kit and the four images, in order.
# usage: tools/run.sh KIT_DIR CGIF_B_PIN CGIF_B_TWIN DECODE_B_PIN DECODE_B_TWIN
#   KIT_DIR: the cmpkit 86da41d3ef68 files AS RUN:
#     mkdir kit-asrun && git archive 98e50c029045 tools/cmpkit/86da41d3ef68 | tar -x -C kit-asrun --strip-components=3
# Inputs kept in the record: out/FNLIST8.txt (the 8 paired functions); kit/SHA256SUMS is a copy of the kit's, for reference.
# scans/lui-targets.tsv / scans/luiconst-targets.tsv are REGENERATED here from the closure output. rerun8cmp.py reads the
# 8-function re-run beside the record (../fncmp.cmpkit-4bbd3a74be89.log, ../../cmpkit-4bbd3a74be89/settled.tsv). The kit's
# own controls (its controls/) are run separately (RECORD.md section 11). Progress and timings go to stderr, not to the record.
# The publication scrub xz-compresses out/closure_strict3.out and scans/constbase.tsv. The lui traces and the whole-image
# field scan (objscan.py) each take about 25 minutes.
set -euo pipefail
[ $# -eq 5 ] || { sed -n '2,11p' "$0"; exit 2; }
export PYTHONDONTWRITEBYTECODE=1
export CMPREC="$(cd "$(dirname "$0")/.." && pwd)" CMPKIT="$(cd "$1" && pwd)"
export CGIF_B_PIN="$2" CGIF_B_TWIN="$3" DECODE_B_PIN="$4" DECODE_B_TWIN="$5"
T="$CMPREC/tools"; O="$CMPREC/out"; S="$CMPREC/scans"
mkdir -p "$S"
(cd "$CMPKIT" && sha256sum -c SHA256SUMS)
F=$(paste -sd, "$O/FNLIST8.txt")
python3 "$CMPKIT/drvcmp.py" twins "$CGIF_B_PIN" "$CGIF_B_TWIN" "$DECODE_B_PIN" "$DECODE_B_TWIN" > "$O/twins.out"
python3 "$CMPKIT/strictcmp3.py" cmp "$F" C="$CGIF_B_TWIN" D="$DECODE_B_TWIN" C:D > "$O/strictcmp3-cmp.out"
python3 "$CMPKIT/closure_strict3.py" "$CGIF_B_TWIN" "$DECODE_B_TWIN" "$F" > "$O/closure_strict3.out"
python3 "$T/reported.py"                                   # -> out/closure-reported.txt
python3 "$CMPKIT/jtcheck.py" "$CGIF_B_TWIN" "$DECODE_B_TWIN" "$(cut -f1 "$O/closure-reported.txt" | paste -sd,)" > "$O/jtcheck.out"
python3 "$T/settle.py" "$O/jtcheck.out"                    # -> out/settle.tsv
python3 "$T/fulldiff.py" > "$O/fulldiff.out"               # -> out/fulldiff.tsv
python3 "$T/tables.py" > "$O/tables.out"                   # -> out/tables.tsv
python3 "$CMPKIT/luiscan.py" --all "$CGIF_B_TWIN" "$DECODE_B_TWIN" > "$S/luiscan-all.tsv"
python3 "$T/exposure.py" > "$S/exposure.out"               # -> scans/exposure.tsv
python3 "$T/luitargets.py"                                 # -> scans/lui-targets.tsv, scans/luiconst-targets.tsv
python3 "$T/switchbound.py" > "$O/switchbound.out"         # -> out/switchbound.tsv (the two tables jtcheck refused)
python3 "$T/luitrace.py" > "$S/luitrace.out"               # -> scans/luitrace.tsv (~20 min)
python3 "$T/luitrace.py" "$S/luiconst-targets.tsv" "$S/luitrace-luiconst.tsv" > "$S/luitrace-luiconst.out"
python3 "$T/luiclass.py" > "$S/luiclass.out"               # -> scans/luiclass.tsv (one class per lui row, or NOT CERTIFIED)
python3 "$T/luisummary.py" > /dev/null                     # -> scans/luiclass-summary.md (RECORD.md section 5 tables)
python3 "$T/luilui.py" > "$S/luilui.out"                   # -> scans/luilui.tsv (two lui values in one base)
python3 "$T/constbase.py" > "$S/constbase.out"             # -> scans/constbase.tsv, scans/constbase-summary.md
python3 "$T/nameonly.py" > "$O/nameonly.out"               # -> out/nameonly.tsv (NAME-ONLY acceptances re-measured)
python3 "$T/certify.py"                                    # -> out/certify.tsv, out/certify.out
python3 "$T/objscan.py" > "$O/objscan.summary"             # -> out/objscan.out, out/objscan.tsv (~25 min)
python3 "$T/ptrfollow.py" > /dev/null                      # -> out/ptrfollow.out, out/ptrfollow.tsv
python3 "$T/escape.py" > "$O/escape.out"                   # -> out/escape.tsv
python3 "$T/vreader.py" > "$O/vreader.out"
python3 "$T/cstrcount.py" > "$O/cstrcount.out"
python3 "$T/dupnames.py" > "$O/dupnames.out"
python3 "$T/dupaddr.py" > "$O/dupaddr.out"
P="${PLANTDIR:-$(mktemp -d)}"
PLANTDIR="$P" python3 "$T/plant_ctz.py" | sed "s#$P#<plantdir>#g" > "$O/plant_ctz.out"
PLANTDIR="$P" python3 "$T/plant_luiclass.py" | sed "s#$P#<plantdir>#g" > "$S/plant_luiclass.out"   # controls (a) (b)
PLANTDIR="$P" python3 "$T/plant_luilui.py" | sed "s#$P#<plantdir>#g" > "$S/plant_luilui.out"       # controls (c) (d)
PLANTDIR="$P" python3 "$T/plant_constbase.py" | sed "s#$P#<plantdir>#g" > "$S/plant_constbase.out" # controls (e) (f)
python3 "$T/rerun8cmp.py" > "$O/rerun8cmp.out"            # this record beside the 8-function re-run (../fncmp.cmpkit-*.log)

echo "run.sh: done; outputs in $O and $S"
