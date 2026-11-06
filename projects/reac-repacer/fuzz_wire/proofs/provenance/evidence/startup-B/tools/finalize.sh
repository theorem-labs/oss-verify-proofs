#!/bin/bash
# finalize.sh -- reac-repacer/fuzz_wire image B: the last writer steps over the 19 generated files, re-runnable end to
# end from the donor-namespace outputs (no hand edit anywhere):
#   1. nsW.py raw -> gen for the 18 files a generator writes in the donor namespace ($WK/raw, and the exit-driver lane's
#      out/ for YE23 / YD1y / YE37); YCej comes from its lane already in the lib/B namespace (nsW gate only)
#   2. pins.py 4778073f01be stamp on the files whose generator writes no `(* Read from: ...)` pin line, on a scratch copy
#      that replaces the file only after textguard.py passes it (fail-closed: nsW.py refuses a forbidden token before it
#      writes, and the frozen pins.py's line is checked the same way before the file is replaced)
#   3. hdrcheck.py over the 19 (0 hits required), sha256 list
set -uo pipefail
. "$W/env.sh"
R=$WK/raw; G=$WK/gen; X=$W/sub/exitdrv/out; L=$W/logs/final
mkdir -p $L
FAILED=
rc() { echo "$1 rc=$2"; [ "$2" = 0 ] || FAILED="$FAILED [$1]"; }
cd $LT
ALL="YB01 YB03 YB05 YB12 YB13 YB1h YB1k YB1l YB1m YB1v YCej YD1k YD1y YD2i YD2j YE23 YE37 YE3i YF0m"
for f in $ALL; do
  case $f in
    YCej) src=$W/sub/acej/out/YCej.v ;;
    YE23|YD1y|YE37) src=$X/$f.v ;;
    *) src=$R/$f.v ;;
  esac
  [ -f "$src" ] || { echo "MISSING $f ($src)"; FAILED="$FAILED [missing $f]"; continue; }
  python3 $W/tools/nsW.py "$src" $G/$f.v --grant-twin $f 2>&1 | scrub > $L/nsW.$f.log; rc "nsW $f" ${PIPESTATUS[0]}
  grep -h 'EQUAL\|DIFFERS' $L/nsW.$f.log
done
grep -h 'placement' $L/nsW.YB01.log | sed 's/.*; placement/placement/'
mkdir -p $LT/finalize.stamp
for f in $ALL; do
  grep -q '^(\* Read from: ' $G/$f.v && continue
  cp $G/$f.v $LT/finalize.stamp/$f.v
  $FR3 pins.py stamp $LT/finalize.stamp/$f.v $UB --twin $UBs --ns $NS_U 2>&1 | scrub > $L/stamp.$f.log; r=${PIPESTATUS[0]}
  if [ $r = 0 ]; then
    python3 $W/tools/textguard.py $LT/finalize.stamp/$f.v 2>&1 | scrub | tail -1; [ ${PIPESTATUS[0]} = 0 ] || r=2
  fi
  [ $r = 0 ] && cp $LT/finalize.stamp/$f.v $G/$f.v
  rc "pins stamp $f" $r; grep -h '^(\* Read from' $G/$f.v | cut -c1-120
done
python3 $W/tools/hdrcheck.py $(for f in $ALL; do printf '%s ' $G/$f.v; done) 2>&1 | scrub; rc "hdrcheck 19 files" ${PIPESTATUS[0]}
(cd $G && sha256sum $(for f in $ALL; do printf '%s.v ' $f; done)) | tee $L/SHA256.lib-B.txt
[ -z "$FAILED" ] || { echo "FAILED:$FAILED"; exit 1; }
echo "FINAL SET READY: 19 files"
