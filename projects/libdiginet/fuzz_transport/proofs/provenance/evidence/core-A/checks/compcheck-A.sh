#!/bin/bash
# compcheck-A.sh WORK LIB OUT: item 4 of the TCA value lane, the four compensating checks of port_core d9e0589898fd's
# registry entry (compcheck.py), on the run and on a planted copy. The run takes the rows decided by hand on the dry run
# (records/compcheck-decided.tsv, beside this script; DECIDED overrides the path): a row at the same place with the same
# written value takes that decision, every other row stays open. Plants, each in one copy of WORK/stage-out:
#   P1 A/AFia.v   the PT_LOAD3 page span 5705728 -> the donor's 5619712 (a kept image-derived count)       part a1 / a2
#   P2 A/AE34.v   the code range (0x44a08, 156%nat) -> (0x44a0c, 156%nat) (a start moved by 4)            part a1b
#   P3 A/AB1w.v   tfib_got_lo GOT[0] 0xa4030 -> 0xa4038 (GOT[1])                                          part b
#   P4 A/AE2v.v   the shadow window bound 0x7fffb300 -> the donor's 0x7fffb2e8 (a kept shadow address)    part c1 / c1w
#   P5 A/AFev.v   the divisor of `change (65536 / 8)` -> 16 (a moved divisor)                             part c2
#   P6 Reusable/YG0f.v kNodesBlockSize 0x100000 -> 0x107ec0 (a model constant moved by symbol)          part c4
#   P7 A/AB1w.v   the tfib_A_ / tfib_E_sysconf row renamed away (a drop of a function the target links)   part d
#   P8 A/AB15.v   the arithmetic constant 16843009 (0x1010101) -> 16843010                               part c3 (c2)
# Each plant must add at least one FINDING / CANDIDATE on its own line, and the copy may add none elsewhere. Exit 1 when the
# control is not PASS. The plant directory is PL (P names the image tree that decval.py reads).
set -uo pipefail
[ $# -eq 3 ] || { echo "usage: compcheck-A.sh WORK LIB OUT" >&2; exit 2; }
WORK=$1 LIB=$2 OUT=$3
HERE=$(dirname "$(readlink -f "$0")")
if [ -z "${DECIDED:-}" ]; then
  DECIDED=$HERE/records/compcheck-decided.tsv; [ -f "$DECIDED" ] || DECIDED=$HERE/../records/compcheck-decided.tsv
fi
[ -f "$DECIDED" ] || { echo "compcheck-A: no compcheck-decided.tsv (set DECIDED): without it every row decided by hand is open" >&2; exit 2; }
mkdir -p "$OUT"
py() { local o=$1; shift; PYTHONDONTWRITEBYTECODE=1 python3 "$@" > "$o" 2>&1; echo "rc=$?" >> "$o"; }
DA=(--decided "$DECIDED")
py "$OUT/compcheck.out" "$HERE/compcheck.py" "$WORK" "$LIB" "$OUT" "${DA[@]}"
PL=$OUT/compcheck-plant
rm -rf "$PL" && mkdir -p "$PL" && cp -r "$WORK/stage-out" "$PL/stage-out" && ln -s "$(readlink -f "$WORK/stage")" "$PL/stage"
for f in check.tsv geometry.tsv decimals.tsv no-twin.tsv; do [ -f "$WORK/$f" ] && ln -s "$(readlink -f "$WORK/$f")" "$PL/$f"; done
python3 - "$WORK/stage-out" "$PL/stage-out" > "$PL/plants.txt" <<'PY' || { echo "compcheck-A: a plant did not apply" >&2; exit 2; }
import re, sys
src, dst = sys.argv[1:]
plants = (("A/AFia.v", r"\b5705728\b", "5619712", "P1 a kept PT_LOAD3 page span"),
          ("A/AE34.v", r"\(0x44a08, 156%nat\)", "(0x44a0c, 156%nat)", "P2 a code range start moved by 4"),
          ("A/AB1w.v", r"(Definition tfib_got_lo : Z := )0xa4030", r"\g<1>0xa4038", "P3 GOT[0] -> GOT[1]"),
          ("A/AE2v.v", r"\b0x7fffb300\b", "0x7fffb2e8", "P4 a kept donor shadow address"),
          ("A/AFev.v", r"change \(65536 / 8\)", "change (65536 / 16)", "P5 a moved divisor"),
          ("Reusable/YG0f.v", r"(Definition kNodesBlockSize : Z := )0x100000", r"\g<1>0x107ec0", "P6 a moved model constant"),
          ("A/AB1w.v", r"Definition tfib_A_sysconf : Z := (0x[0-9a-f]+)\.  Definition tfib_E_sysconf : Z := ",
           r"Definition tfib_A_sysconf_gone : Z := \g<1>.  Definition tfib_E_sysconf_gone : Z := ", "P7 the row of a function the target links dropped"),
          ("A/AB15.v", r"\b16843009\b", "16843010", "P8 a moved arithmetic constant"))
files = {}
for f, rx, new, why in plants:
    if f not in files:
        files[f] = open("%s/%s" % (src, f)).read().split("\n")
    L = files[f]
    i = next(i for i, l in enumerate(L) if re.search(rx, l))
    m = re.search(rx, L[i])
    print("%s\t%d\t%s\t%s\t%s" % (f, i + 1, m.group(0)[:60], m.expand(new)[:60], why))
    L[i] = re.sub(rx, new, L[i], count=1)
for f, L in files.items():
    open("%s/%s" % (dst, f), "w").write("\n".join(L))
PY
py "$PL/compcheck.out" "$HERE/compcheck.py" "$PL" "$LIB" "$PL" --tag plant "${DA[@]}"
rm -rf "$PL/stage-out"
python3 - "$OUT" > "$OUT/compcheck-control.txt" <<'PY'
import os, sys
out = sys.argv[1]
pl = [l.split("\t") for l in open(os.path.join(out, "compcheck-plant", "plants.txt")).read().splitlines()]
open_ = lambda p: {(r[0], r[2], r[4]) for r in (l.split("\t") for l in open(p).read().splitlines()[1:]) if r[1] in ("FINDING", "CANDIDATE", "AMBIGUOUS")}
base = open_(os.path.join(out, "compcheck.tsv"))
plant = open_(os.path.join(out, "compcheck-plant", "compcheck-plant.tsv"))
new = sorted(plant - base)
# the line of a plant; (d) names the file, not a line
def hits(p):
    f, ln = p[0], int(p[1])
    return [x for x in new if x[1].split(" ")[0] == "%s:%d" % (f, ln) or (p[4].startswith("P7") and x[0] == "d" and x[1] == f)]
ok = True
used = set()
for p in pl:
    h = hits(p)
    used |= set(h)
    ok &= bool(h)
    print("plant %s:%s %s -> %s (%s): caught by %s" % (p[0], p[1], p[2], p[3], p[4], ["%s %s %s" % x for x in h] or "NOTHING"))
stray = [x for x in new if x not in used]
print("control: %d plant(s), each caught: %s; new open rows elsewhere: %d%s: %s" % (
    len(pl), ok, len(stray), (" " + str(stray[:5])) if stray else "", "PASS" if ok and not stray else "FAIL"))
PY
grep -v -P '^(CANDIDATE|FINDING)\t' "$OUT/compcheck.txt"; cat "$OUT/compcheck-control.txt"
grep -q ': PASS$' "$OUT/compcheck-control.txt" || { echo "compcheck-A: the planted control is not PASS (OUT/compcheck-control.txt)" >&2; exit 1; }
