#!/bin/bash
# gotwords-A.sh WORK LIB OUT: item 3 of the TCA value lane (the .got words the core states, GOT[0] included), and its
# planted control. Runs gotwords.py on the run, then on a copy of WORK/stage-out with three plants:
#   G1 A/AFii.v R_got: the .got cell 0xa4d18 (holds __stack_chk_guard) -> 0xa4d20, the next cell (holds __environ)
#   G2 A/AB1w.v tfib_got_lo: GOT[0] 0xa4030 -> 0xa4038, GOT[1] (also a zero word: the registry's silent GOT[0] class)
#   G3 A/AD1j.v A_canary: the value the .got cell 0xa4d18 holds, 6372144 (0x613b30) -> the donor's 6257424 (0x5f7b10)
# Each plant must give at least one finding on its own line, and no finding may fall outside the planted lines; exit 1
# when the control is not PASS. The plant directory is PL (P names the image tree that decval.py reads).
set -uo pipefail
[ $# -eq 3 ] || { echo "usage: gotwords-A.sh WORK LIB OUT" >&2; exit 2; }
WORK=$1 LIB=$2 OUT=$3
HERE=$(dirname "$(readlink -f "$0")")
mkdir -p "$OUT"
py() { local o=$1; shift; PYTHONDONTWRITEBYTECODE=1 python3 "$@" > "$o" 2>&1; echo "rc=$?" >> "$o"; }
py "$OUT/gotwords.out" "$HERE/gotwords.py" "$WORK" "$LIB" "$OUT"
PL=$OUT/gotwords-plant
rm -rf "$PL" && mkdir -p "$PL" && cp -r "$WORK/stage-out" "$PL/stage-out" && ln -s "$(readlink -f "$WORK/stage")" "$PL/stage" \
  && ln -s "$(readlink -f "$WORK/check.tsv")" "$PL/check.tsv"
python3 - "$WORK/stage-out" "$PL/stage-out" > "$PL/plants.txt" <<'PY' || { echo "gotwords-A: a plant did not apply" >&2; exit 2; }
import re, sys
src, dst = sys.argv[1:]
for f, key, old, new, why in (("A/AFii.v", "R_got", "0xa4d18", "0xa4d20", "G1: the next .got cell"),
                              ("A/AB1w.v", "tfib_got_lo", "0xa4030", "0xa4038", "G2: GOT[0] -> GOT[1]"),
                              ("A/AD1j.v", "A_canary", "6372144", "6257424", "G3: the held value put back to the donor's")):
    L = open("%s/%s" % (src, f)).read().split("\n")
    rx = re.compile(r"(%s\b[^;]{0,60}?)(?<![A-Za-z0-9_])%s(?![A-Za-z0-9_])" % (re.escape(key), old))
    i = next(i for i, l in enumerate(L) if rx.search(l))
    L[i] = rx.sub(lambda m: m.group(1) + new, L[i], count=1)
    open("%s/%s" % (dst, f), "w").write("\n".join(L))
    print("%s\t%d\t%s\t%s\t%s" % (f, i + 1, old, new, why))
PY
py "$PL/gotwords.out" "$HERE/gotwords.py" "$PL" "$LIB" "$PL" --tag plant
rm -rf "$PL/stage-out"
python3 - "$OUT" > "$OUT/gotwords-control.txt" <<'PY'
import os, sys
out = sys.argv[1]
pl = [l.split("\t") for l in open(os.path.join(out, "gotwords-plant", "plants.txt")).read().splitlines()]
txt = open(os.path.join(out, "gotwords-plant", "gotwords-plant.txt")).read().splitlines()
fi = [l.split("\t") for l in txt if l.startswith("FINDING")]
base = {l.split("\t")[3] for l in open(os.path.join(out, "gotwords.txt")).read().splitlines() if l.startswith("FINDING")}
planted = {"%s:%s" % (p[0], p[1]) for p in pl}
# part C quotes check.tsv's (donor) line number, one above the stage-out line
at = lambda x: x[3] if x[1] != "C" else "%s:%d" % (x[3].split(":")[0], int(x[3].split(":")[1]) + 1)
new = [x for x in fi if x[3] not in base]
hit = {p: [x[1] + " " + x[2] for x in new if at(x) == p] for p in sorted(planted)}
stray = [x for x in new if at(x) not in planted]
d0 = [l for l in txt if l.startswith("D. ")]
ok = all(hit.values()) and not stray
for p in pl:
    print("plant %s:%s %s -> %s (%s): caught by %s" % (p[0], p[1], p[2], p[3], p[4], hit["%s:%s" % (p[0], p[1])] or "NOTHING"))
print("  " + (d0[0] if d0 else "no D line"))
print("control: %d planted line(s), each caught: %s; findings outside the planted lines: %d: %s" % (
    len(planted), all(hit.values()), len(stray), "PASS" if ok else "FAIL"))
PY
grep -v '^   cell' "$OUT/gotwords.txt"; cat "$OUT/gotwords-control.txt"
grep -q ': PASS$' "$OUT/gotwords-control.txt" || { echo "gotwords-A: the planted control is not PASS (OUT/gotwords-control.txt)" >&2; exit 1; }
