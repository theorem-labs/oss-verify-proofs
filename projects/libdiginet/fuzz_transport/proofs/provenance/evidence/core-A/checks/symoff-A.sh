#!/bin/bash
# symoff-A.sh WORK LIB OUT: item 5 of the TCA value lane, the symbol + offset sweep (symoff.py) on the run, and its planted
# control. Needs OUT/decval/A-stage2.tsv (decval-A.sh WORK LIB OUT/decval; run-all.sh runs it first).
#   run    symoff.py WORK LIB OUT -> OUT/symoff.tsv, OUT/symoff.txt
#   plant  a copy of WORK/stage-out with two values written the wrong way (the registry's two shapes):
#          P1 the first 0x13c4a0 (__sanitizer::PageSizeCached) of A/AFeq.v -> 0xa4070, the .got word that HOLDS it;
#          P2 the first 0xa9648 (__asan::instance+0x2b0) of A/AD2l.v -> the donor value 0xa1788 moved by the .data / .got
#             address delta 0x7820 (0xa8fa8) instead of by its symbol;
#          decval.py + decval_extra.py + symoff.py on the copy must report exactly these two rows: P1 GOT, P2 OTHER-SYM.
#          Exit 1 when the control is not PASS. The plant directory is PL (P names the image tree that decval.py reads).
set -uo pipefail
[ $# -eq 3 ] || { echo "usage: symoff-A.sh WORK LIB OUT" >&2; exit 2; }
WORK=$1 LIB=$2 OUT=$3
HERE=$(dirname "$(readlink -f "$0")")
[ -f "$OUT/decval/A-stage2.tsv" ] || { echo "symoff-A: no $OUT/decval/A-stage2.tsv (run decval-A.sh WORK LIB OUT/decval first)" >&2; exit 2; }
py() { local o=$1; shift; PYTHONDONTWRITEBYTECODE=1 python3 "$@" > "$o" 2>&1; echo "rc=$?" >> "$o"; }
py "$OUT/symoff.out" "$HERE/symoff.py" "$WORK" "$LIB" "$OUT"
PL=$OUT/symoff-plant
rm -rf "$PL" && mkdir -p "$PL" && cp -r "$WORK/stage-out" "$PL/stage-out" && ln -s "$(readlink -f "$WORK/stage")" "$PL/stage"
python3 - "$WORK/stage-out" "$PL/stage-out" > "$PL/plants.txt" <<'PY' || { echo "symoff-A: a plant did not apply" >&2; exit 2; }
import re, sys
src, dst = sys.argv[1:]
for f, old, new, why in (("A/AFeq.v", "0x13c4a0", "0xa4070", "P1: the .got word holding __sanitizer::PageSizeCached"),
                         ("A/AD2l.v", "0xa9648", "%#x" % (0xa1788 + 0x7820), "P2: donor 0xa1788 moved by the address delta 0x7820")):
    L = open("%s/%s" % (src, f)).read().split("\n")
    rx = re.compile(r"(?<![A-Za-z0-9_])%s(?![A-Za-z0-9_])" % old)
    i = next(i for i, l in enumerate(L) if rx.search(l))
    L[i] = rx.sub(new, L[i], count=1)
    open("%s/%s" % (dst, f), "w").write("\n".join(L))
    print("%s\t%d\t%s\t%s\t%s" % (f, i + 1, old, new, why))
PY
py "$PL/decval.out" "$HERE/decval.py" "$PL" --out "$PL/A.tsv"
py "$PL/extra.out" "$HERE/decval_extra.py" "$PL" "$PL/A.tsv" --out "$PL/A-stage2.tsv"
py "$PL/symoff.out" "$HERE/symoff.py" "$PL" "$LIB" "$PL" --tsv "$PL/A-stage2.tsv" --tag plant
rm -rf "$PL/stage-out"
python3 - "$OUT" > "$OUT/symoff-control.txt" <<'PY'
import os, sys
out = sys.argv[1]
pl = [l.split("\t") for l in open(os.path.join(out, "symoff-plant", "plants.txt")).read().splitlines()]
fi = [l.split("\t") for l in open(os.path.join(out, "symoff-plant", "symoff-plant.txt")).read().splitlines() if l.startswith("FINDING")]
base = [l for l in open(os.path.join(out, "symoff.txt")).read().splitlines() if l.startswith("FINDING")]
want = {("%s:%s" % (p[0], p[1]), p[3]): k for p, k in zip(pl, ("GOT", "OTHER-SYM"))}
got = {(x[2], x[3].split(" -> ")[1]): x[1] for x in fi}
new = {k: v for k, v in got.items() if not any(b.split("\t")[2] == k[0] for b in base)}
ok = new == want
for p in pl:
    print("plant %s:%s %s -> %s (%s)" % tuple(p[:4] + [p[4]]))
for x in fi:
    print("  " + "\t".join(x))
print("control: the planted copy adds %d finding(s) %s, want %s: %s" % (len(new), sorted(new.items()), sorted(want.items()), "PASS" if ok else "FAIL"))
PY
cat "$OUT/symoff.txt" "$OUT/symoff-control.txt"
grep -q ': PASS$' "$OUT/symoff-control.txt" || { echo "symoff-A: the planted control is not PASS (OUT/symoff-control.txt)" >&2; exit 1; }
