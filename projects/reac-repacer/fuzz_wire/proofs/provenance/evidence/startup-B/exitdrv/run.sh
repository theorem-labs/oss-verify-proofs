#!/usr/bin/env bash
# run.sh -- regenerate reac-repacer/fuzz_wire image B's exit-certificate files YE23 / YD1y / YE37 from scratch.
# rule 24: proves no function (kind: start-up facts). Writes only: this directory, $LT/exitdrv/, and
# $WK/gen/{YE23,YD1y,YE37}.v (through nsW.py). Read-only on every git tree. Every step: logs/commands.log (rc, wall).
#   0. the asan-ubsan data map cgif B -> wire B, re-run with the image address-map tool (env.sh's MAPTOOL, sha256
#      4d51ec1c0069); must equal the pinned input byte for byte
#   1. binmatch cgif B vs wire B (the shared binmatch.py unchanged); must equal the pinned json byte for byte
#   2. CONTROL C0: gen_exitW.py --target uci must reproduce the fuzz_uci image-B lane's three files below their headers
#   3. gen_exitW.py -> $LT/exitdrv/out/{YE23,YD1y,YE37}.v + numerals.md (donor namespace; refuses on any failed check)
#   4. 10 negative controls (gen_exitW.py --plant; each must print NEGATIVE CONTROL: CAUGHT and exit 0)
#   5. the --af0m gate against the unit's own YF0m
#   6. nsW.py <out> $WK/gen/<f>.v --grant-twin <f> (module paths + record names; gate: Require set == grant B's twin)
#   7. port_core cross-check, trunk Requires, sha256, header rule (hdrcheck.py) on every output, script and kept log
set -uo pipefail
L=$(cd "$(dirname "$0")" && pwd)
. "$L/../../env.sh"
T=$LT/exitdrv
mkdir -p "$T/binmatch" "$T/out" "$T/inputs" "$T/uciref/unitB" "$T/ref" "$L/logs" "$L/out" "$WK/gen"
: > "$L/logs/commands.log"
fail=0
run() {
  local name=$1; shift
  local s e rc
  s=$(date +%s%N); "$@"; rc=$?; e=$(date +%s%N)
  printf '%s\trc=%d\twall=%d.%03ds\t%s\n' "$name" "$rc" $(( (e - s) / 1000000000 )) $(( (e - s) / 1000000 % 1000 )) \
    "$(echo "$*" | scrub)" >> "$L/logs/commands.log"
  [ $rc = 0 ] || fail=1
  return $rc
}

# ---- snapshot the inputs other lanes own (their live directories are rewritten; every copy is sha256-pinned by the
#      generator, so a changed byte stops the run)
run snapshot bash -c "cp -f '$LT/pcB/map.json' '$T/inputs/map.cgif2wire.asan-ubsan.json' &&
  install -m 644 '$UCI/sub/exitdrv/binmatch/binmatch.cgif.asan-ubsan.json' \
     '$UCI/sub/exitdrv/inputs/map.cgif2uci.asan-ubsan.json' '$UCI/sub/exitdrv/tools/af0m.py' \
     '$UCI/sub/exitdrv/tools/hsform.py' '$T/uciref/' &&
  install -m 644 '$UCI/sub/exitdrv'/inputs/unitB/*.v '$T/uciref/unitB/' &&
  mkdir -p '$T/inputs/unitB' && install -m 644 '$LT/pcB/stage-out/B'/{YE2p,YE3m,YE22,YF0m,YE23,YD1y,YE37}.v \
     '$T/inputs/unitB/'"
# the C0 reference is the fuzz_uci image-B lane's own generator output, copied once into this lane's scratch and
# pinned here; the generator re-checks the same sha256 before it compares bodies.
run c0-ref bash -c "cd '$T/ref' && echo '27f4fa108e0c8c988e91afa9abd3c01e0a5ecda844144a47171d60e7f7c495f3  uciB.YE23.v
9338d848470c79edfd7b5828182fa4269309e9ba20d97069791f66ffe67e6a16  uciB.YD1y.v
5582074bd970c7a52d868a53a3eea6d2d442609d72be8c1a9da29de0f005c6dc  uciB.YE37.v' | sha256sum -c -"

# ---- 0 the data map (the image address-map tool, sha256 4d51ec1c0069, as port_core ran it for the parent lane): must
#      reproduce the pinned input. The tool is named by role and sha256 and its path comes from env.sh's MAPTOOL (no
#      default), so no tool name or host path is written here
[ -n "${MAPTOOL:-}" ] || { echo "run.sh: set MAPTOOL to the image address-map tool (sha256 4d51ec1c0069...)" >&2; exit 2; }
run datamap-sha bash -c "echo '4d51ec1c0069a242e4923a4eea37dc66f9f9aa0e4cbfeb0d9c8f8778954b893c  $MAPTOOL' | sha256sum -c --quiet"
run datamap bash -c "cd '$T' && python3 '$MAPTOOL' '$CB' '$UB' -o '$T/map.rerun.json' --summary '$T/map.rerun.txt' \
  > '$T/datamap.rerun.log' 2>&1"
run datamap-cmp cmp "$T/map.rerun.json" "$T/inputs/map.cgif2wire.asan-ubsan.json"
# ---- 1 binmatch
run binmatch bash -c "cd '$T' && python3 '$L/run_binmatch_wireB.py' --other cgif --builds asan-ubsan \
  > '$T/binmatch/run.asan-ubsan.log' 2>&1"
run binmatch-sha bash -c "echo '27dc4c8c2aeef1a0cdda4f470625f7c2fba64689da807cf5b8682609d85f1c3c  $T/binmatch/binmatch.cgif.asan-ubsan.json' | sha256sum -c -"
# ---- 2 CONTROL C0 first: the same generator must reproduce the fuzz_uci image-B lane's files
run c0-uci bash -c "cd '$T' && python3 '$L/gen_exitW.py' --target uci > '$L/logs/gen_uci.out' 2>&1"
# ---- 3 the wire files
run gen bash -c "cd '$T' && python3 '$L/gen_exitW.py' > '$L/logs/gen_exitW.out' 2>&1"
# ---- 4 negative controls (independent; run together)
P=(0xa28d0=0x9cf20 0x8d824=0x88340 d:6265120=6241960 0x9f000=0x9f000 0xa2ae0=0x9d130 0xa0098=0x9a6e8
   0xa6f60=0xa14e8 0x9ee98=0x994f8 stk=16 flagval=1)
pids=()
for i in "${!P[@]}"; do
  n=$((i + 1))
  run "plant$n" bash -c "cd '$T' && python3 '$L/gen_exitW.py' --plant ${P[$i]} > '$L/logs/plant$n.out' 2>&1" &
  pids+=($!)
done
for p in "${pids[@]}"; do wait "$p" || fail=1; done
for i in "${!P[@]}"; do
  n=$((i + 1))
  grep -q 'NEGATIVE CONTROL: CAUGHT' "$L/logs/plant$n.out" || { echo "plant$n (${P[$i]}) NOT CAUGHT"; fail=1; }
done
# ---- 5 the --af0m gate against the unit's own YF0m
run af0m bash -c "cd '$T' && python3 '$L/gen_exitW.py' --af0m '$WK/raw/YF0m.v' > '$L/logs/gen_af0m.out' 2>&1"
# ---- 6 module paths and record names (nsW.py, run from $LT as the lane contract says)
for f in YE23 YD1y YE37; do
  run "nsW-$f" bash -c "cd '$LT' && python3 '$W/tools/nsW.py' '$T/out/$f.v' '$WK/gen/$f.v' --grant-twin $f \
    > '$L/logs/nsW.$f.log' 2>&1"
done
cp "$T/out"/{YE23,YD1y,YE37}.v "$T/out/numerals.md" "$L/out/"
# every kept log through scrub: a log may name a host path (the --af0m argument, the out/ sha lines)
for f in "$L/logs"/*.out "$L/logs"/*.log; do scrub < "$f" > "$f.scrubbed" && mv "$f.scrubbed" "$f"; done
# ---- 7 cross-checks and the header rule
run xcheck_portcore bash -c "python3 '$L/xcheck_portcore.py' > '$L/logs/xcheck_portcore.out' 2>&1"
run trunk_requires bash -c "python3 '$L/trunk_requires.py' > '$L/logs/trunk_requires.out' 2>&1"
for f in "$L/logs/xcheck_portcore.out" "$L/logs/trunk_requires.out"; do
  scrub < "$f" > "$f.scrubbed" && mv "$f.scrubbed" "$f"
done
run hdrcheck bash -c "python3 '$W/tools/hdrcheck.py' '$WK/gen/YE23.v' '$WK/gen/YD1y.v' '$WK/gen/YE37.v' \
  '$L/out/YE23.v' '$L/out/YD1y.v' '$L/out/YE37.v' '$L/out/numerals.md' '$L/gen_exitW.py' '$L/run_binmatch_wireB.py' \
  '$L/run.sh' '$L/xcheck_portcore.py' '$L/trunk_requires.py' '$L/REPORT.md' '$L/logs'/*.log '$L/logs'/*.out \
  > '$L/logs/hdrcheck.out' 2>&1"
sha256sum "$WK/gen/YE23.v" "$WK/gen/YD1y.v" "$WK/gen/YE37.v" "$L"/out/* "$L/gen_exitW.py" "$L/run_binmatch_wireB.py" \
  "$L/xcheck_portcore.py" "$L/trunk_requires.py" "$L/run.sh" | scrub > "$L/logs/sha256.out"
cat "$L/logs/commands.log"
exit $fail
