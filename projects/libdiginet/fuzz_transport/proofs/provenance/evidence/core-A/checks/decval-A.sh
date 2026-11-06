#!/bin/bash
# decval-A.sh WORK LIB OUT: the by-value check of the libdiginet/fuzz_transport image-A core relocation (row TCA, asan pin
# e89be137db17), over every numeral of the staged files of a port_core run directory (WORK/stage-out/A/*.v,
# Reusable/*.v) against the donor text WORK/stage. libdiginet/fuzz_decode's checks/decval-A.sh (sha256
# 58524d54aa5f; internal record) with the pins, the trees and the argument list changed. Runs:
#   stage 1  decval.py       -> OUT/A.tsv, OUT/review.tsv, OUT/decval.out
#   stage 2  decval_extra.py -> OUT/A-stage2.tsv, OUT/extra.out
#   by hand  decval_hand.py  -> OUT/hand.tsv, OUT/hand.out: every .got cell and every constant row read from the target
#            ELF, the bytes at each stage-1 DONOR-STALE address and each stage-2 NO TWIN address in both images, and the
#            comment numerals that are donor values (each must sit in the donor's notice block)
#   plant    a copy of stage-out whose A/AB1w.v tfib_at_x_memset is put back to the donor's value (WORK/stage/A/AB1w.v,
#            the address of fuzz_grant's memset): stage 1 on the copy must differ from stage 1 in that row alone, DONOR-STALE
# LIB is the target lib the run used; only its start-up layer is read (each not-relocated file must be LIB's and none
# staged). Env (defaults in decval.py): P, PG, EV. Output: OUT/decval.txt (the result lines of every run).
# Exit 1 when any step (decval.py, decval_extra.py, decval_hand.py, the plant run, the summary) fails: a crashed step leaves
# no result line, so a 0 exit with a missing line cannot happen.
set -uo pipefail
[ $# -eq 3 ] || { echo "usage: decval-A.sh WORK LIB OUT" >&2; exit 2; }
WORK=$1 LIB=$2 OUT=$3
HERE=$(dirname "$(readlink -f "$0")")
EV=${EV:?set EV to the evidence dir of the run (not-relocated-startup-layer.txt)}
[ -f "$WORK/stage-out/A/AB1w.v" ] && [ -f "$WORK/stage/A/AB1w.v" ] || { echo "decval-A: no stage-out/A/AB1w.v or stage/A/AB1w.v in $WORK" >&2; exit 2; }
[ -d "$LIB/A" ] || { echo "decval-A: no A/ in LIB $LIB" >&2; exit 2; }
mkdir -p "$OUT"
rm -f "$OUT/A.tsv" "$OUT/review.tsv" "$OUT/A-stage2.tsv" "$OUT/hand.tsv" "$OUT/plant.tsv"
# the start-up layer: every not-relocated file must be in LIB and absent from stage-out
SU=0 SUL=0 SUS=0
while read -r f; do
  [ -n "$f" ] || continue; SU=$((SU + 1))
  case $f in A/*) l=$LIB/$f; s=$WORK/stage-out/$f ;; *) l=$LIB/Reusable/$f; s=$WORK/stage-out/Reusable/$f ;; esac
  [ -f "$l" ] && SUL=$((SUL + 1)); [ -f "$s" ] && SUS=$((SUS + 1))
done < "$EV/not-relocated-startup-layer.txt"
FAIL=0
py() { local o=$1; shift; PYTHONDONTWRITEBYTECODE=1 python3 "$@" > "$o" 2>&1; local rc=$?; echo "rc=$rc" >> "$o"; [ "$rc" = 0 ] || FAIL=1; }
py "$OUT/decval.out" "$HERE/decval.py" "$WORK" --out "$OUT/A.tsv" --review "$OUT/review.tsv"
py "$OUT/extra.out" "$HERE/decval_extra.py" "$WORK" "$OUT/A.tsv" --out "$OUT/A-stage2.tsv"
py "$OUT/hand.out" "$HERE/decval_hand.py" "$WORK" "$OUT/A-stage2.tsv" --out "$OUT/hand.tsv"
# the plant: the donor's own tfib_at_x_memset written into a copy of the relocated A/AB1w.v; exactly one line changes
RE='^Definition tfib_at_x_memset : Z := \(0x[0-9a-f]*\)\.$'
DV=$(sed -n "s/$RE/\1/p" "$WORK/stage/A/AB1w.v")
[ -n "$DV" ] || { echo "decval-A: no tfib_at_x_memset line in WORK/stage/A/AB1w.v" >&2; exit 2; }
rm -rf "$OUT/plant" && mkdir -p "$OUT/plant" && cp -r "$WORK/stage-out" "$OUT/plant/stage-out" && ln -s "$(readlink -f "$WORK/stage")" "$OUT/plant/stage"
sed "s/$RE/Definition tfib_at_x_memset : Z := $DV./" "$WORK/stage-out/A/AB1w.v" > "$OUT/plant/stage-out/A/AB1w.v"
diff "$WORK/stage-out/A/AB1w.v" "$OUT/plant/stage-out/A/AB1w.v" > "$OUT/plant.diff"
[ "$(grep -c '^>' "$OUT/plant.diff")" = 1 ] || { echo "decval-A: the plant did not change exactly one line" >&2; exit 2; }
py "$OUT/plant.out" "$HERE/decval.py" "$OUT/plant" --out "$OUT/plant.tsv"
rm -rf "$OUT/plant/stage-out"
python3 - "$OUT" "$DV" "$SU" "$SUL" "$SUS" > "$OUT/decval.txt" <<'PY'
import os, re, sys
out, dv, su, sul, sus = sys.argv[1:]
rd = lambda f: open(os.path.join(out, f)).read().splitlines()
pick = lambda f, rx: [l for l in rd(f) if re.match(rx, l)]
print("# start-up layer: %s not-relocated files, %s of them in LIB, %s staged" % (su, sul, sus))
print("# stage 1 (decval.py)")
print("\n".join(pick("decval.out", r"relocated files|target top|fetch/word pairs|tfib_A_/tfib_E_ rows|classes:|DONOR-STALE\t|FETCH-MISMATCH|rc=")))
print("# stage 2 (decval_extra.py)")
print("\n".join(pick("extra.out", r"identical \.rodata|fetch rows|word rows|moved rows|  (OTHER|TARGET|DONOR-STALE) |UNVERIFIED|NO-TWIN|tfib table|sweep |rc=")))
print("# by hand (decval_hand.py: the target ELF read)")
print("\n".join(pick("hand.out", r"\.got rows|\.got cell values|GOT-|constant rows|CONST-CHANGED|DONOR-STALE\t|SAME-8\t|NO-TWIN\t|stage-2 NO TWIN|COMMENT-DONOR-VALUE|comment numerals|rc=")))
# the result: each stage-1 DONOR-STALE row is decided by its bytes (the same 16 bytes at the address in both images) or as a
# constant unchanged from the donor text; each stage-2 NO TWIN row by its 8 bytes; any other stays open
hand = {(r[1], r[2]): r[0] for r in (l.split("\t") for l in rd("hand.tsv")[1:])}
left = []
for l in pick("hand.out", r"DONOR-STALE\t"):
    f, row = l.split("\t")[1], l.split("\t")
    m = re.match(r"target (\w+) .*; donor (\w+) ", row[3])
    loc = tuple(f.rsplit(":", 1))
    if not ((m and m.group(1) == m.group(2) and "SHARED by bytes" in row[3]) or hand.get(loc) == "CONST-UNCHANGED"):
        left.append(f)
n1 = len(pick("hand.out", r"DONOR-STALE\t"))
nt = [l.split("\t")[1] for l in pick("hand.out", r"(SAME-8|NO-TWIN)\t")]
ntl = [l.split("\t")[1] for l in pick("hand.out", r"NO-TWIN\t")]
gd = pick("hand.out", r"GOT-(DIFF|STATED-DIFF)\t")
cc = pick("hand.out", r"CONST-CHANGED\t")
cd = pick("hand.out", r"COMMENT-DONOR-VALUE\t")
print("result: stage 1 DONOR-STALE %d; decided by bytes or as an unchanged constant %d; DONOR-STALE after the look by hand %d%s" % (
    n1, n1 - len(left), len(left), (": " + " ".join(left)) if left else ""))
print("result: stage 2 NO TWIN %d; decided by the 8 bytes at the address %d; open %d%s" % (
    len(nt), len(nt) - len(ntl), len(ntl), (": " + " ".join(ntl)) if ntl else ""))
print("result: .got rows wrong %d; constant rows changed %d; comment donor values outside the notice block %d" % (len(gd), len(cc), len(cd)))
# the control
a = {tuple(l.split("\t")[:2]): l for l in rd("A.tsv")[1:]}
b = {tuple(l.split("\t")[:2]): l for l in rd("plant.tsv")[1:]}
diff = sorted(k for k in set(a) | set(b) if a.get(k) != b.get(k))
row = b.get(diff[0], "").split("\t") if len(diff) == 1 else []
ok = len(diff) == 1 and diff[0][0] == "A/AB1w.v" and row[2] == dv and row[4] == "DONOR-STALE"
cnt = lambda f: sum(1 for l in rd(f)[1:] if l.split("\t")[4] == "DONOR-STALE")
print("# control")
print("plant: A/AB1w.v tfib_at_x_memset -> %s (the donor's); stage-1 DONOR-STALE %d -> %d; changed rows %d%s: %s" % (
    dv, cnt("A.tsv"), cnt("plant.tsv"), len(diff), (" (" + "\t".join(row[:6]) + ")") if row else "", "PASS" if ok else "FAIL"))
PY
SUMRC=$?
cat "$OUT/decval.txt"
[ "$SUMRC" = 0 ] && [ "$FAIL" = 0 ] || { echo "decval-A: a step failed (summary rc $SUMRC; step rc lines in OUT/*.out)" >&2; exit 1; }
