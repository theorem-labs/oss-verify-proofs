#!/bin/bash
# ghunks-A.sh WORK LIB OUT: the G patches of the libdiginet/fuzz_transport image-A core (row TCA) checked on a run of
# record. Kind: measurement; it proves no function. Read-only for WORK and LIB. The record of the G patches is
# records/GHUNKS-A-rec3.md (with records/GHUNKS-A.md, its section 3 and 9); its tools are checks/make_gpatches.py,
# check_gpatches.py, asan_globals.py, measure_gcut.py (each called here unchanged).
#   1. undo: the 7 G patches (EV/g-<f>.patch, in reverse of run.sh's order) undone on a copy of WORK/stage-out
#      (`patch -R -p0 -F0`; port_core's provenance line under each notice block only offsets the hunks): rc 0 each.
#      The tree that is left is the text after the run's first 6 patches, with its provenance lines.
#   2. check_gpatches.py on that tree, with --before the 6 first patches of run.sh and PATCHDIR = a copy of the 7 G
#      patches whose stage-g/A/<f>.v is WORK/stage-out's own text without the provenance line: the 6 patches undo and
#      re-apply exactly, each G patch applies with `--dry-run -F0` then for real, and each patched file equals WORK's text;
#      its control (a G patch with one context line altered) must be refused.
#   3. asan_globals.py on fuzz_transport.asan's unstripped twin (TIMG/unstripped/fuzz_transport.asan, sha256
#      86efc3a80314) -> OUT/asan_globals.tsv; measure_gcut.py LIB/A/AD2j.v WORK/stage-out/A/AD2f.v
#      WORK/stage-out/A/AD1x.v OUT/asan_globals.tsv LIB/A/AD1y.v -> OUT/measure_gcut.out. It must give: no DIFFERS line,
#      hull_meets 0, clip_identity true, L_mem_avoids_G true, STDOUT / SOBUF / F_STDERR off the hull.
#   4. control of 3: a copy of LIB/A/AD2j.v with the region that ends nearest below DRV_G_LO made to end 8 bytes into the
#      hull: measure_gcut.py must then give hull_meets 1 and clip_identity false.
# OUT/ghunks.txt is the record (each command, its status, the result lines). Exit 0 when every step and both controls
# answer as above.
set -uo pipefail
[ $# -eq 3 ] || { echo "usage: ghunks-A.sh WORK LIB OUT" >&2; exit 2; }
WORK=$(readlink -f "$1") LIB=$(readlink -f "$2")
mkdir -p "$3" || exit 2
OUT=$(readlink -f "$3")
HERE=$(cd "$(dirname "$0")" && pwd)
EV=${EV:-$(cd "$HERE/.." && pwd)}
TWIN=${TWIN:-${TIMG:?set TIMG to the fuzz_transport image dir}/unstripped/fuzz_transport.asan}
[ "$(sha256sum "$TWIN" | cut -c1-12)" = 86efc3a80314 ] || { echo "ghunks-A: $TWIN is not 86efc3a80314" >&2; exit 2; }
G="ACfn AD1w AD1m AD1p AD1q AD1r AD2f"
FIRST="zero-shadow-forallb cell-lookup ad1q-shape imgtop-alias dead-arm-ad1g bss-zero-range"
REC=$OUT/ghunks.txt
FAIL=0
say() { echo "$*" >> "$REC"; }
s12() { sha256sum "$1" | cut -c1-12; }
: > "$REC"
say "# ghunks-A.sh WORK LIB OUT ($(date -u +%FT%TZ))"
say "# tools: $(cd "$HERE" && sha256sum ghunks-A.sh make_gpatches.py check_gpatches.py asan_globals.py measure_gcut.py | awk '{printf "%s %s; ", $2, substr($1, 1, 12)}')"
say "# inputs: G patches$(for f in $G; do printf ' g-%s %s' "$f" "$(s12 "$EV/g-$f.patch")"; done); LIB/A/AD2j.v $(s12 "$LIB/A/AD2j.v"), AD1y.v $(s12 "$LIB/A/AD1y.v"); WORK/stage-out A/AD2f.v $(s12 "$WORK/stage-out/A/AD2f.v"), A/AD1x.v $(s12 "$WORK/stage-out/A/AD1x.v"); twin 86efc3a80314"
NOPROV='import os, re, sys
prov = re.compile(r"^\(\* Relocated from proofs/\S+ at [0-9a-f]{12} by port_core [0-9a-f]{12} onto \S+ \((plain|ubsan|asan|asan-ubsan)\)\. \*\)$")
src, dst = sys.argv[1], sys.argv[2]
for sub in ("A", "Reusable"):
    os.makedirs(os.path.join(dst, sub), exist_ok=True)
    for f in sorted(os.listdir(os.path.join(src, sub))):
        if f.endswith(".v"):
            lines = open(os.path.join(src, sub, f)).read().split("\n")
            open(os.path.join(dst, sub, f), "w").write("\n".join(l for l in lines if not prov.match(l)))'
# 1. undo the G patches
rm -rf "$OUT/undo" "$OUT/gpd" && mkdir -p "$OUT/undo" && cp -r "$WORK/stage-out/A" "$WORK/stage-out/Reusable" "$OUT/undo/" || exit 2
say "## 1. the 7 G patches undone on a copy of WORK/stage-out, in reverse order"
for f in $(echo $G | tr ' ' '\n' | tac); do
  o=$(cd "$OUT/undo" && patch -R -p0 -F0 --batch < "$EV/g-$f.patch" 2>&1); rc=$?
  say "undo g-$f.patch rc=$rc $(echo "$o" | tr '\n' ' ' | sed 's/ *$//')"
  [ "$rc" = 0 ] || FAIL=1
done
# 2. check_gpatches.py on the 6-patch text
mkdir -p "$OUT/gpd/stage-g/A"
python3 -c "$NOPROV" "$WORK/stage-out" "$OUT/noprov" || exit 2
for f in $G; do cp "$EV/g-$f.patch" "$OUT/gpd/"; cp "$OUT/noprov/A/$f.v" "$OUT/gpd/stage-g/A/$f.v"; done
rm -rf "$OUT/noprov"
say "## 2. check_gpatches.py UNDO-TREE GPD --before <the 6 first patches of run.sh> (stage-g = WORK/stage-out's own text)"
python3 "$HERE/check_gpatches.py" "$OUT/undo" "$OUT/gpd" --before $(for p in $FIRST; do echo "$EV/$p.patch"; done) > "$OUT/check_gpatches.out" 2>&1
rc=$?
sed "s|$EV/||g; s|$OUT/|OUT/|g" "$OUT/check_gpatches.out" >> "$REC"
say "check_gpatches.py rc=$rc"
[ "$rc" = 0 ] || FAIL=1
# 3. the hull and the counts
say "## 3. asan_globals.py TWIN; measure_gcut.py LIB/A/AD2j.v WORK/stage-out/A/AD2f.v WORK/stage-out/A/AD1x.v OUT/asan_globals.tsv LIB/A/AD1y.v"
python3 "$HERE/asan_globals.py" "$TWIN" > "$OUT/asan_globals.tsv" || { say "asan_globals.py failed"; exit 2; }
say "asan_globals.tsv: $(awk '!/^#/ && NF' "$OUT/asan_globals.tsv" | wc -l) descriptors, sha256 $(s12 "$OUT/asan_globals.tsv")"
python3 "$HERE/measure_gcut.py" "$LIB/A/AD2j.v" "$WORK/stage-out/A/AD2f.v" "$WORK/stage-out/A/AD1x.v" "$OUT/asan_globals.tsv" \
  "$LIB/A/AD1y.v" > "$OUT/measure_gcut.out" 2>&1
rc=$?
cat "$OUT/measure_gcut.out" >> "$REC"
say "measure_gcut.py rc=$rc"
want() { awk -F'\t' -v k="$1" -v v="$2" '$1 == k { f = 1; if ($2 != v) bad = 1 } END { exit (f && !bad) ? 0 : 1 }' "$3"; }
ok3=1
[ "$rc" = 0 ] || ok3=0
! awk -F'\t' '$3 ~ /DIFFERS/' "$OUT/measure_gcut.out" | grep -q . || ok3=0
for kv in hull_meets:0 clip_identity:true L_mem_avoids_G:true STDOUT_off_hull:true SOBUF_off_hull:true F_STDERR_off_hull:true; do
  want "${kv%%:*}" "${kv#*:}" "$OUT/measure_gcut.out" || { ok3=0; say "WRONG: ${kv%%:*} is not ${kv#*:}"; }
done
say "measurement: $([ $ok3 = 1 ] && echo PASS || echo FAIL) (no DIFFERS; hull_meets 0; clip_identity, L_mem_avoids_G and the three off-hull rows true)"
[ $ok3 = 1 ] || FAIL=1
# 4. control of 3
python3 - "$LIB/A/AD2j.v" "$OUT/AD2j-plant.v" "$OUT/measure_gcut.out" > "$OUT/plant.txt" <<'PY' || { say "control: the plant did not apply"; exit 2; }
import re, sys
src, dst, mg = sys.argv[1:4]
lo = int(next(l.split('\t')[1] for l in open(mg) if l.startswith('DRV_G_LO\t')), 16)
t = open(src).read()
rx = re.compile(r'(Definition (R_\w+) : region :=\s*mkRegion (?:None|\(Some \d+\)) (-?\d+) )(-?\d+)')
best = None
for m in rx.finditer(t):
    if int(m.group(4)) <= lo and (best is None or int(m.group(4)) > int(best.group(4))):
        best = m
if best is None:
    sys.exit(1)
new = lo + 8
open(dst, 'w').write(t[:best.start(4)] + str(new) + t[best.end(4):])
print(f'{best.group(2)}: end {int(best.group(4)):#x} -> {new:#x} (DRV_G_LO {lo:#x} + 8)')
PY
python3 "$HERE/measure_gcut.py" "$OUT/AD2j-plant.v" "$WORK/stage-out/A/AD2f.v" "$WORK/stage-out/A/AD1x.v" "$OUT/asan_globals.tsv" \
  "$LIB/A/AD1y.v" > "$OUT/measure_gcut-plant.out" 2>&1
pm=$(awk -F'\t' '$1 == "hull_meets" { print $2 }' "$OUT/measure_gcut-plant.out")
pc=$(awk -F'\t' '$1 == "clip_identity" { print $2 }' "$OUT/measure_gcut-plant.out")
c4=$([ "$pm" = 1 ] && [ "$pc" = false ] && echo CAUGHT || echo "NOT CAUGHT")
say "## 4. control: $(cat "$OUT/plant.txt"): hull_meets $pm, clip_identity $pc: $c4"
[ "$c4" = CAUGHT ] || FAIL=1
grep -q '^control (g-ACfn.patch, context line .* altered)	rc=1' "$OUT/check_gpatches.out" && say "check_gpatches control: CAUGHT" \
  || { say "check_gpatches control: NOT CAUGHT"; FAIL=1; }
say "ghunks-A: $([ $FAIL = 0 ] && echo PASS || echo FAILED)"
cat "$REC"
exit $FAIL
