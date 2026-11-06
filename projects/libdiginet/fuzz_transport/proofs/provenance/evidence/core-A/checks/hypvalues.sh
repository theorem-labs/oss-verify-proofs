#!/bin/bash
# hypvalues.sh WORK LIB OUT: hypothesis-position value audit of the libdiginet/fuzz_transport image-A core (row
# TCA). proves no function (kind: measurement). Read-only for WORK, LIB and the images; writes only under OUT.
#   1  hyplist.py WORK OUT          every numeral in a hypothesis position of WORK/stage-out, paired with WORK/stage
#   2  hypderive.py WORK LIB OUT    every DIFFERS value derived from the target image / the unit's definitions; SAME values
#                                   that name a donor image value; memory facts against the image bytes
#   3  control: a copy of WORK/stage-out with four planted values; steps 1-2 on the copy must report exactly these rows:
#      P1 A/AFek.v (aN, mkAF 1 4097 0) -> mkAF 1 4000 0   a narrowed atom range (SAME -> listed DIFFERS)
#      P2 A/AFk6.v (rSHA, mkAF 0x5cf050 ..) -> 0x5cf058   a relocated atom range narrowed (DIFFERS, derived WRONG)
#      P3 A/AD1o.v rom_seg1 0x31000 -> 0x30000            the donor's image bound kept (SAME, KEPT-IMAGE)
#      P4 A/AFii.v R_scj lit4 0x217c4 0x71800 -> 0x71804  a memory fact against the image (DIFFERS, CONTENT WRONG)
set -uo pipefail
[ $# -eq 3 ] || { echo "usage: hypvalues.sh WORK LIB OUT" >&2; exit 2; }
WORK=$(readlink -f "$1") LIB=$(readlink -f "$2") OUT=$3
HERE=$(dirname "$(readlink -f "$0")")
mkdir -p "$OUT"
OUT=$(readlink -f "$OUT")
export PYTHONDONTWRITEBYTECODE=1
treesha() { (cd "$1" && find . -name '*.v' -type f -print0 | sort -z | xargs -0 sha256sum | sha256sum | cut -c1-12); }
{
  echo "# hypvalues.sh $WORK $LIB $OUT  ($(date -u +%FT%TZ))"
  echo "tools: $(cd "$HERE" && sha256sum hypvalues.sh hyplist.py coqhyp.py hypderive.py imgs.py | awk '{printf "%s %s, ", $2, substr($1,1,12)}')"
  echo "inputs: WORK/stage-out tree $(treesha "$WORK/stage-out") ($(find "$WORK/stage-out" -name '*.v' | wc -l) files), WORK/stage tree $(treesha "$WORK/stage") ($(find "$WORK/stage" -name '*.v' | wc -l) files), LIB/A/AD2j.v $(sha256sum "$LIB/A/AD2j.v" | cut -c1-12), WORK/versions.txt port_core $(awk '$1=="port_core.py"{print substr($2,1,12)}' "$WORK/versions.txt" 2>/dev/null)"
} > "$OUT/RESULT.txt"
python3 "$HERE/hyplist.py" "$WORK" "$OUT" > "$OUT/hyplist.out" 2>&1 || { cat "$OUT/hyplist.out"; exit 1; }
python3 "$HERE/hypderive.py" "$WORK" "$LIB" "$OUT" > "$OUT/hypderive.out" 2>&1 || { cat "$OUT/hypderive.out"; exit 1; }
# control
P=$OUT/plant
rm -rf "$P" && mkdir -p "$P" && cp -r "$WORK/stage-out" "$P/stage-out" && ln -s "$WORK/stage" "$P/stage"
python3 - "$WORK/stage-out" "$P/stage-out" > "$P/plants.txt" <<'PY' || { echo "hypvalues: a plant did not apply" >&2; exit 2; }
import sys
src, dst = sys.argv[1:]
plants = [("P1", "A/AFek.v", "(aN, mkAF 1 4097 0)", "(aN, mkAF 1 4000 0)", "4000", "DIFFERS", None),
          ("P2", "A/AFk6.v", "(rSHA, mkAF 0x5cf050 kHighMemBeg 12)", "(rSHA, mkAF 0x5cf058 kHighMemBeg 12)", "0x5cf058", "DIFFERS", "WRONG"),
          ("P3", "A/AD1o.v", "0x10000 <= a < 0x31000 -> in_ro_tfa a", "0x10000 <= a < 0x30000 -> in_ro_tfa a", "0x30000", "SAME", "KEPT-IMAGE"),
          ("P4", "A/AFii.v", "lit4 0x217c4 0x71800", "lit4 0x217c4 0x71804", "0x71804", "DIFFERS", "WRONG")]
for tag, f, old, new, val, dec, ver in plants:
    L = open("%s/%s" % (src, f)).read().split("\n")
    hit = [i for i, l in enumerate(L) if old in l]
    if len(hit) != 1:
        raise SystemExit("plant %s: %d hits" % (tag, len(hit)))
    L[hit[0]] = L[hit[0]].replace(old, new, 1)
    open("%s/%s" % (dst, f), "w").write("\n".join(L))
    print("\t".join((tag, f, str(hit[0] + 1), old, new, val, dec, ver or "-")))
PY
python3 "$HERE/hyplist.py" "$P" "$OUT" --tag plant > "$P/hyplist.out" 2>&1 || { cat "$P/hyplist.out"; exit 1; }
python3 "$HERE/hypderive.py" "$P" "$LIB" "$OUT" --tag plant > "$P/hypderive.out" 2>&1 || { cat "$P/hypderive.out"; exit 1; }
rm -rf "$P/stage-out"
python3 - "$OUT" > "$OUT/control.txt" <<'PY'
import csv, os, sys
out = sys.argv[1]
def rows(name):
    return list(csv.DictReader(open(os.path.join(out, name)), delimiter="\t"))
def key(r):
    return (r["file"], r["line"], r["col"], r["written"], r["decision"])
plants = [l.split("\t") for l in open(os.path.join(out, "plant", "plants.txt")).read().splitlines()]
base, pl = rows("hyplist.tsv"), rows("hyplist-plant.tsv")
bk = {key(r) for r in base}
new = [r for r in pl if key(r) not in bk]
dbase = {(r["file:line"], r["written"], r["verdict"]) for r in rows("differs.tsv")}
dpl = [r for r in rows("differs-plant.tsv") if (r["file:line"], r["written"], r["verdict"]) not in dbase]
kbase = {(r["file:line"], r["value"], r["decision"]) for r in rows("kept.tsv")}
kpl = [r for r in rows("kept-plant.tsv") if (r["file:line"], r["value"], r["decision"]) not in kbase and r["decision"] == "KEPT-IMAGE"]
cbase = {(r["file:line"], r["value"], r["verdict"]) for r in rows("content.tsv")}
cpl = [r for r in rows("content-plant.tsv") if (r["file:line"], r["value"], r["verdict"]) not in cbase and r["verdict"] == "WRONG"]
ok = True
for tag, f, ln, old, newt, val, dec, ver in plants:
    lst = [r for r in new if r["file"] == f and r["line"] == ln and r["written"] == val and r["decision"] == dec]
    if ver == "WRONG":
        got = [r for r in dpl if r["file:line"] == "%s:%s" % (f, ln) and r["written"] == val and r["verdict"] == "WRONG"]
    elif ver == "KEPT-IMAGE":
        got = [r for r in kpl if r["file:line"] == "%s:%s" % (f, ln) and r["value"] == val]
    else:
        got = [True]
        info = [r for r in rows("differs-plant.tsv") if r["file:line"] == "%s:%s" % (f, ln) and r["written"] == val]
    caught = len(lst) == 1 and len(got) >= 1
    ok &= caught
    print("%s %s:%s %s -> %s: listed %s %s; derived %s: %s" % (tag, f, ln, old, newt, dec, "yes (%s, %s)" % (lst[0]["class"], lst[0]["ctor"] or "-") if lst else "NO",
                                                         ver, "caught" if caught else "MISSED"))
    if got and got[0] is not True:
        g = got[0]
        print("    %s" % "  ".join("%s=%s" % (k, g[k]) for k in g if k in ("verdict", "decision", "rule", "right", "target_value"))[:400])
    elif ver == "-" and info:
        print("    hypderive on the row: verdict=%s rule=%s (%s)" % (info[0]["verdict"], info[0]["rule"], info[0]["derivation"][:200]))
extra = [r for r in new if not any(r["file"] == p[1] and r["line"] == p[2] and r["written"] == p[5] for p in plants)]
extra_d = [r for r in dpl if not any(r["file:line"] == "%s:%s" % (p[1], p[2]) for p in plants)]
print("rows new in the planted copy: hyplist %d (outside the plants %d), derived WRONG %d (outside %d), KEPT-IMAGE %d, CONTENT WRONG %d" % (
    len(new), len(extra), len(dpl), len(extra_d), len(kpl), len(cpl)))
ok &= not extra and not extra_d
print("control: %s" % ("PASS" if ok else "FAIL"))
PY
{
  echo "## hyplist"; cat "$OUT/hyplist.txt"
  echo "## hypderive"; cat "$OUT/hypvalues.txt"
  echo "## control"; cat "$OUT/plant/plants.txt"; cat "$OUT/control.txt"
} >> "$OUT/RESULT.txt"
sed -n '1,12p' "$OUT/RESULT.txt"; grep -E '^(listed|DIFFERS rows|SAME rows|CONTENT|control)' "$OUT/RESULT.txt"
grep -q '^control: PASS$' "$OUT/control.txt" || { echo "hypvalues: the planted control is not PASS (OUT/control.txt)" >&2; exit 1; }
