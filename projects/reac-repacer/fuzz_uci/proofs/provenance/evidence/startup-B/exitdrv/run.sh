#!/usr/bin/env bash
# run.sh -- regenerate reac-repacer/fuzz_uci image B's exit-certificate files YE23 / YD1y / YE37 from scratch
# (the exit-driver step of the image-B start-up set).  Writes only: this directory, $UCIB_EXITWORK, and
# $WK/gen/{YE23,YD1y,YE37}.v (through nsB.py).  Read-only on every git tree.  Every step: logs/commands.log (rc, wall).
#   1. binmatch cgif B vs uci B (the cited binmatch.py unchanged, ~30 s); its json must equal the pinned copy byte for byte
#   2. gen_exitB.py -> $UCIB_EXITWORK/out/{YE23,YD1y,YE37}.v + numerals.md (cgif namespace; refuses on any failed check)
#   3. 8 negative controls (gen_exitB.py --plant; each must print NEGATIVE CONTROL: CAUGHT and exit 0)
#   4. nsB.py <out> $WK/gen/<f>.v --grant-twin <f> (module paths + record names; gate: Require set == grant B's twin)
set -uo pipefail
: "${UCIB_UB:?source the lane env file first (env.example.sh names every variable)}"
L=${UCIB_EXITDRV:?}
T=${UCIB_EXITWORK:?}
mkdir -p "$T/binmatch" "$T/out" "$L/logs" "$L/out" "$WK/gen"
: > "$L/logs/commands.log"
run() {   # run NAME CMD... ; stdout/stderr already redirected by the caller's CMD wrapper
  local name=$1; shift
  local s e rc
  s=$(date +%s%N); "$@"; rc=$?; e=$(date +%s%N)
  printf '%s\trc=%d\twall=%d.%03ds\t%s\n' "$name" "$rc" $(( (e - s) / 1000000000 )) $(( (e - s) / 1000000 % 1000 )) "$*" \
    >> "$L/logs/commands.log"
  return $rc
}
fail=0
# 0. the asan-ubsan data map (the image address-map tool, sha256 4d51ec1c0069, as port_core 0e4e ran it for the parent
#    run): must reproduce the pinned input byte for byte. The tool is named by role and sha256 and its path comes from
#    UCIB_MAPTOOL (no default), so no tool name or host path is written here.
MAPTOOL=${UCIB_MAPTOOL:-}
[ -n "$MAPTOOL" ] || { echo "run.sh: set UCIB_MAPTOOL to the image address-map tool (sha256 4d51ec1c0069...)" >&2; exit 2; }
run datamap-sha bash -c "echo '4d51ec1c0069a242e4923a4eea37dc66f9f9aa0e4cbfeb0d9c8f8778954b893c  $MAPTOOL' | sha256sum -c --quiet" || fail=1
run datamap bash -c "cd $T && python3 $MAPTOOL $CB $UB -o $T/map.rerun.json --summary $T/map.rerun.txt > $T/datamap.rerun.log 2>&1" || fail=1
run datamap-cmp cmp "$T/map.rerun.json" "$L/inputs/map.cgif2uci.asan-ubsan.json" || fail=1
# 1. binmatch
run binmatch bash -c "cd $T && python3 $L/run_binmatch_uciB.py --other cgif --builds asan-ubsan > $T/binmatch/run.asan-ubsan.log 2>&1" || fail=1
run binmatch-cmp cmp "$T/binmatch/binmatch.cgif.asan-ubsan.json" "$L/binmatch/binmatch.cgif.asan-ubsan.json" || fail=1
# 2. generator
run gen bash -c "cd $T && python3 $L/gen_exitB.py > $L/logs/gen_exitB.out 2>&1" || fail=1
# 3. negative controls (independent; run together)
P=(0xa28d0=0x9b7c8 0x8d824=0x86bf4 d:6265120=6236072 0x9f000=0x9f000 0xa6f60=0x9fde8 0xa00d0=0x98fc8 0xa3b30=0x9c9b8
   0x5d91b8=0x5d2040)
pids=()
for i in "${!P[@]}"; do
  n=$((i + 1))
  run "plant$n" bash -c "cd $T && python3 $L/gen_exitB.py --plant ${P[$i]} > $L/logs/plant$n.out 2>&1" &
  pids+=($!)
done
for p in "${pids[@]}"; do wait "$p" || fail=1; done
# 4. module paths (nsB.py, run from $UCIB_LT)
for f in YE23 YD1y YE37; do
  run "nsB-$f" bash -c "cd $UCIB_LT && python3 $W/tools/nsB.py $T/out/$f.v $WK/gen/$f.v --grant-twin $f > $L/logs/nsB.$f.log 2>&1" || fail=1
done
cp "$T/out/YE23.v" "$T/out/YD1y.v" "$T/out/YE37.v" "$T/out/numerals.md" "$L/out/"
# 5. after nsB: numeral-by-numeral comparison with port_core 0e4e's own relocation (snapshot); trunk Requires
run xcheck_portcore bash -c "python3 $L/xcheck_portcore.py > $L/logs/xcheck_portcore.out 2>&1" || fail=1
run trunk_requires bash -c "python3 $L/trunk_requires.py > $L/logs/trunk_requires.out 2>&1" || fail=1
sha256sum "$WK/gen/YE23.v" "$WK/gen/YD1y.v" "$WK/gen/YE37.v" "$L"/out/* "$L/gen_exitB.py" "$L/run_binmatch_uciB.py" \
  "$L/xcheck_portcore.py" "$L/trunk_requires.py" "$L/run.sh" > "$L/logs/sha256.out"
cat "$L/logs/commands.log"
exit $fail
