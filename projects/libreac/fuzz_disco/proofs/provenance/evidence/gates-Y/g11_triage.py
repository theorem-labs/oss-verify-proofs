#!/usr/bin/env python3
"""g11_triage.py -- every row port_addr_check 205a90fd19b8 changes against 0d24592683b6 on one tree, and every row
205a90fd19b8 flags that g1_triage.py leaves untriaged, each triaged by a measured rule.

Usage: g11_triage.py --run NAME:OLD.tsv:NEW.tsv:G1OLD.tsv:G1NEW.tsv [--run ...] --pac-old OLD_TOOL.py \\
                     --pac-new NEW_TOOL.py --lib SERIES_LIB --cgif-lib CGIF_LIB --pin K=PIN --twin K=TWIN \\
                     --cgif-pin K=PIN --cgif-twin K=TWIN --out OUT.tsv

OLD.tsv / NEW.tsv are the --out tables of 0d24592683b6 and 205a90fd19b8 with the same arguments on the same tree
(G11-address-check-205a.md gives the commands); G1OLD.tsv / G1NEW.tsv are g1_triage.py's output on them. SERIES_LIB is
proofs/libreac/fuzz_disco/lib at the series tree the two runs read, CGIF_LIB proofs/cgif/cgif_file_fuzzer/lib at the
donor commit. --pin / --cgif-pin take fuzz_disco's and cgif's pins for the keys A, B, P, U (their PT_LOADs are
measured); --twin takes fuzz_disco's unstripped twins A, B, P and --cgif-twin cgif's twin P (the rules of
g10_triage.py read them). The flagged classes are read from both tools (`--list-flag-classes`) and must be equal.

Method. A row's key is (src_file, src_line, dst_file, dst_line, sentence, idx, kind, src_value, dst_value) with its
occurrence number; the two tables must hold the same keys. Part `diff`: a row DIFFERS when any column differs; a
differing row whose verdict is the same is NOTE-ONLY; a row whose verdict moved gets the FIRST rule that holds: the
rules of g10_triage.py (in its order), then the rules below (in RULES order). A row that is DIFFERENT-SYMBOL or
UNMEASURED-NAME in OLD.tsv and SAME-SYMBOL in NEW.tsv gets no rule (205a90fd19b8's name-variant rule can pass a cell
that names another function; such a row keeps the old verdict until it is read by hand) and is counted. Part
`flagged`: a row of NEW.tsv that g1_triage.py leaves UNTRIAGED and whose verdict did not move gets the first rule of
g10_triage.py that holds for it. A row no rule takes is UNTRIAGED. Exit 0 only when no row is UNTRIAGED.

Image quantities (measured on the pin of the row's image, and on cgif's pin of the same key): seg<i>.lo / seg<i>.hi
= PT_LOAD i's address rounded down / its end (p_vaddr + p_memsz) rounded up to 4096, seg<i>.size = hi - lo,
load<i>.lo = p_vaddr, load<i>.memhi = p_vaddr + p_memsz, image.top = the last segment's hi, image.span = image.top -
seg0.lo (PT_LOADs counted from 0).

Output: one row per row, per run: run, part, old_verdict, new_verdict, image, where (port file:line), sentence, idx,
src_value, dst_value, rule, detail.
"""
import argparse
import collections
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from g1_triage import Img  # noqa: E402
import g10_triage  # noqa: E402

RULES = collections.OrderedDict([
    ("NOTE-ONLY", "the verdict is unchanged; only the note or reading text differs (the detail gives the note text "
                  "removed and added)"),
    ("SAME-G1-RULE", "both verdicts are findings and g1_triage.py gives the row the same rule and the same measured "
                     "detail on both tables: only the finding's class name moved"),
    ("TARGET-GEOMETRY", "the new verdict flags a size that CHANGED from the donor's value, but 0d24592683b6 read it as "
                        "the image quantity `size <q>`: measured, the port's value is q of the row's fuzz_disco pin and "
                        "the donor's value is q of cgif's pin, so the port holds the target's own quantity and the "
                        "donor value the new verdict expects is cgif's"),
    ("UNCHANGED-PASS", "both verdicts are passes and the value is the same on both sides; 0d24592683b6 read it as the "
                       "image quantity named first in its reading, and that quantity of the row's fuzz_disco pin is this "
                       "value (measured), or as ROUND-CONSTANT-SAME (itself a size-or-bound reading); 205a90fd19b8 reads "
                       "it as a size in the slot the detail names. The detail gives the numeral's role read from its "
                       "line and cgif's value of the same quantity"),
    ("UNTRIAGED", "no rule took the row"),
])

# The numeral's role, read from its line: (value, role, pattern); the first entry for the row's value whose pattern
# matches the text within 50 characters of the numeral (as written, decimal or hex) names it. These say what the rows
# of UNCHANGED-PASS are; the rule itself rests on the measurement above.
ROLES = [
    (65536, "64 KiB stack window below the stack pointer", r"(usp|sp0|sp_window_lo|ew E 0\)) - 65536|-\s?65536 <=|"
                                                           r"= -65536|65536 \+ o(ff)?\b|eSp1? \+ 65536|stk <= 65536|"
                                                           r"usp \+ 65536"),
    (65536, "GIF code-table / palette modulus 2^16", r"\(2 \* L\) mod 65536|\* 2\) mod 65536|\* 3\) mod 65536"),
    (65536, "64 KiB size threshold (a large mapping's shadow, a batch halving loop)", r"65536 \* UNIT|"
                                                                                      r"65536 <= CNTv LEN"),
    (65536, "64 KiB chunk stride", r"65536 \* Z\.of_nat j\b"),
    (65536, "input buffer capacity of the read loop (64 KiB, doubling)", r"65536 <= cap|cap\w* = 65536|cap0|"
                                                                          r"cap mod 65536|<=\? 65536\)|cap = 2 \^ e|"
                                                                          r"2 \* 65536\) with 131072"),
    (65536, "read / write chunk length bound (64 KiB)", r"<=? (want|n|w|cnt) <= 65536|RS_LO \+ 65536|\bn <= 65536|"
                                                        r"SLit 65536|a \+ 65536\b|a 65536 = true|< 65536 -> in_img"),
    (65536, "allocator model bound (record count, size class, redzone)", r"10248 <= 65536|65536 - 10240|65536 < n|"
                                                                           r"\d => 65536|RZ <= 65536|NDv <= 65536"),
    (65536, "image base: PT_LOAD 0's address", r"\b0x10000\b|(?<!- )\b65536 <=\?? ?(a|x)\b"),
    (65536, "64 KiB alignment modulus", r"mod 65536\b|q\w* \* 65536\b"),
    (65536, "2^16 factor of a positional weight (bytes, half-words, 2^32 split)", r"\* 65536\b(?! /)|"
                                                                                  r"\b65536 \* [\w(]|"
                                                                                  r"/ 65536\) mod 256|256 \* 65536"),
    (65536, "shadow scale: 65536 / 8 = 8192 shadow bytes per 64 KiB", r"65536 / 8\b"),
    (65536, "16-bit value range bound", r"< 65536\b"),
    (131072, "seg0 of image B: x - 65536 < 131072", r"x - 65536\) <\? 131072"),
    (131072, "128 KiB mmap length of the pointer-array commit, and the region it maps", r"QSv \+ 131072|"
                                                                                        r"QSv mod 131072|"
                                                                                        r"q \* 131072|SLit 131072|"
                                                                                        r"eager_used mdV \+ 131072"),
    (131072, "input capacity doubling 2 * 131072", r"2 \* 131072|67108864 <=\? 131072"),
    (131072, "128 KiB request / buffer length bound", r"\+ 131072 <=|131072 <= (len|dlen)|<= 131072\b|"
                                                      r"a \+ 131072\)"),
    (196608, "seg1 of image B starts at 196608: [196608, 196608 + 458752)", r"196608 <=\? x|196608 \+ 458752"),
    (5619712, "seg3 of image B: x - 663552 < 5619712", r"x - 663552\) <\? 5619712"),
    (1048576, "hash bucket bound 2^20", r"bkt < 1048576"),
]


def role_of(line, v):
    wins = [line[max(0, m.start() - 50):m.end() + 50] for p in (r"\b%d\b" % v, r"\b0x0*%x\b" % v)
            for m in re.finditer(p, line)]
    return next((r for x, r, p in ROLES if x == v and any(re.search(p, w) for w in wins)), None)


def ival(s):
    try:
        return int(s, 0)
    except (TypeError, ValueError):
        return None


class Geo:
    """PT_LOAD quantities of one image."""

    def __init__(self, img):
        self.q = {}
        segs = [(va, ms) for va, fs, ms, *_ in img.segs]
        for i, (va, ms) in enumerate(segs):
            lo, hi = va & ~0xFFF, (va + ms + 0xFFF) & ~0xFFF
            self.q.update({"seg%d.lo" % i: lo, "seg%d.hi" % i: hi, "seg%d.size" % i: hi - lo,
                           "load%d.lo" % i: va, "load%d.memhi" % i: va + ms})
        self.q["image.top"] = self.q["seg%d.hi" % (len(segs) - 1)]
        self.q["image.span"] = self.q["image.top"] - self.q["seg0.lo"]


QTOK = re.compile(r"\b(seg\d+\.(?:lo|hi|size)|load\d+\.(?:lo|memhi)|image\.(?:top|span))\b")


def g1_index(path):
    """g1_triage.py output: (image, where, sentence, idx, src_value, dst_value) -> [(verdict, rule, detail)]."""
    out = collections.defaultdict(list)
    for r in open(path).read().split("\n")[1:]:
        if r:
            c = r.split("\t")
            out[(c[1], c[3], c[4], c[5], c[6], c[7])].append((c[0], c[8], c[9]))
    return out


def snippet(line, v):
    for p in (r"\b%d\b" % v, r"\b0x0*%x\b" % v):
        m = re.search(p, line)
        if m:
            return line[max(0, m.start() - 40):m.end() + 30].strip()
    return line.strip()[:70]


def move_rule(o, n, H, c, geo, cgeo, g1o, g1n, grp):
    d = dict(zip(H, n))
    ov, nv = o[H.index("verdict")], d["verdict"]
    rd = g10_triage.rule_of(d, ov, c)
    if rd:
        return rd
    sent = re.sub(r" / sentence \d+$", "", d["sentence"])[:60]
    k = (d["image"], "%s:%s" % (d["dst_file"], d["dst_line"]), sent, d["idx"], d["src_value"], d["dst_value"])
    dv, sv, img = ival(d["dst_value"]), ival(d["src_value"]), d["image"]
    old_res = o[H.index("dst_res")]
    # SAME-G1-RULE
    if grp(ov) == grp(nv) == "FLAG" and len(g1o.get(k, [])) == 1 and len(g1n.get(k, [])) == 1:
        (vo, ro, do), (vn, rn, dn) = g1o[k][0], g1n[k][0]
        if vo == ov and vn == nv and ro == rn and do == dn and rn not in ("UNTRIAGED",) and not rn.startswith("DEFECT"):
            return "SAME-G1-RULE", "g1_triage.py on both tables: %s: %s" % (rn, dn)
    # TARGET-GEOMETRY
    m = re.match(r"size (\S+);", old_res)
    if nv == "NON-ADDRESS-CHANGED" and ov == "SAME-GEOMETRY" and m and img in geo and img in cgeo:
        q = m.group(1)
        if geo[img].q.get(q) == dv and cgeo[img].q.get(q) == sv:
            return "TARGET-GEOMETRY", ("%s of the image %s pin = %#x = the port's value; cgif's %s = %#x = the donor's "
                                       "value (PT_LOADs measured); 205a90fd19b8 expects the donor's" %
                                       (q, img, dv, q, sv))
    # UNCHANGED-PASS
    if grp(ov) == grp(nv) == "OK" and dv is not None and dv == sv and img in geo:
        line = c.lines(c.lib, d["dst_file"])[int(d["dst_line"]) - 1]
        role = role_of(line, dv)
        slot = re.search(r"a size in an? ([\w-]+) slot", d["note"])
        toks = QTOK.findall(old_res)
        why = None
        if toks and geo[img].q.get(toks[0]) == dv:
            cq = cgeo[img].q.get(toks[0])
            why = "%s of the image %s pin = %#x (cgif's %s = %#x%s)" % (
                toks[0], img, dv, toks[0], cq, "" if cq == dv else ": there the numeral is not that quantity")
        elif ov == "ROUND-CONSTANT-SAME":
            why = "0d24592683b6: ROUND-CONSTANT-SAME (a size or a loose bound)"
        if why and role:
            return "UNCHANGED-PASS", "%s; 205a90fd19b8: size in a %s slot; role: %s; text: %s" % (
                why, slot.group(1) if slot else "?", role, snippet(line, dv))
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", action="append", required=True)
    for k in ("pac-old", "pac-new", "lib", "cgif-lib", "out"):
        ap.add_argument("--" + k, required=True)
    for k in ("pin", "twin", "cgif-pin", "cgif-twin"):
        ap.add_argument("--" + k, action="append", required=True)
    a = ap.parse_args()
    fl = [set(subprocess.run([sys.executable, p, "--list-flag-classes"], capture_output=True, text=True,
                             check=True).stdout.split()) for p in (a.pac_old, a.pac_new)]
    if fl[0] != fl[1]:
        sys.exit("g11_triage: the two tools list different flag classes")
    flags = fl[1]
    grp = lambda v: "FLAG" if v in flags else ("UNMEASURED" if v.startswith("UNMEASURED") or v.endswith("UNMEASURED")
                                               else "OK")
    a.pac = a.pac_new
    c = g10_triage.Ctx(a)
    kv = lambda xs: dict(x.split("=", 1) for x in xs)
    geo = {k: Geo(c.pin[k]) for k in c.pin}
    cgeo = {k: Geo(Img(v)) for k, v in kv(a.cgif_pin).items()}
    out, bad = [], 0
    for spec in a.run:
        name, old, new, g1old, g1new = spec.split(":")
        ho, O = g10_triage.table(old)
        hn, N = g10_triage.table(new)
        if ho != hn or set(O) != set(N):
            sys.exit("g11_triage: %s: the two tables do not hold the same rows (header or keys differ)" % name)
        H = hn
        iv = H.index("verdict")
        g1o, g1n = g1_index(g1old), g1_index(g1new)
        cnt, moves, covered = collections.Counter(), collections.Counter(), set()
        ndiff = named = 0

        def emit(part, ov, d, rule, det):
            cnt[(part, rule)] += 1
            out.append("\t".join([name, part, ov, d["verdict"], d["image"], "%s:%s" % (d["dst_file"], d["dst_line"]),
                                  re.sub(r" / sentence \d+$", "", d["sentence"])[:60], d["idx"], d["src_value"],
                                  d["dst_value"], rule, det.replace("\t", " ")]))

        for k in O:
            o, n = O[k], N[k]
            if o == n:
                continue
            ndiff += 1
            d = dict(zip(H, n))
            ov = o[iv]
            if ov == d["verdict"]:
                emit("diff", ov, d, "NOTE-ONLY", g10_triage.note_change(o[H.index("note")], d["note"]))
                continue
            moves[(grp(ov), grp(d["verdict"]))] += 1
            if ov in ("DIFFERENT-SYMBOL", "UNMEASURED-NAME") and d["verdict"] == "SAME-SYMBOL":
                # 205a90fd19b8's variant-spelling rule can read a cell naming another function SAME-SYMBOL: such a
                # row keeps the old verdict until it is read by hand, so no rule here passes it
                named += 1
                rd = None
            else:
                rd = move_rule(o, n, H, c, geo, cgeo, g1o, g1n, grp)
            rule, det = rd if rd else ("UNTRIAGED", "")
            bad += rule == "UNTRIAGED"
            covered.add(k)
            emit("diff", ov, d, rule, det)
        # part flagged: rows g1_triage.py leaves UNTRIAGED in NEW whose verdict did not move
        g1u = collections.Counter(kk for kk, vs in g1n.items() for v, r, _ in vs if r == "UNTRIAGED")
        nflag = 0
        for k in N:
            n = N[k]
            d = dict(zip(H, n))
            sent = re.sub(r" / sentence \d+$", "", d["sentence"])[:60]
            gk = (d["image"], "%s:%s" % (d["dst_file"], d["dst_line"]), sent, d["idx"], d["src_value"], d["dst_value"])
            if n[iv] not in flags or not g1u.get(gk):
                continue
            g1u[gk] -= 1
            if k in covered:
                continue
            nflag += 1
            rd = g10_triage.rule_of(d, "", c)
            rule, det = rd if rd else ("UNTRIAGED", "")
            bad += rule == "UNTRIAGED"
            emit("flagged", n[iv], d, rule, det)
        left = sum(v for v in g1u.values() if v > 0)
        bad += left
        print("# %s: %d rows each; %d differ; verdict moves %d (%s); DIFFERENT-SYMBOL or UNMEASURED-NAME -> "
              "SAME-SYMBOL: %d; flagged rows g1_triage.py leaves untriaged and the diff does not cover: %d; g1 rows "
              "not found in NEW: %d" %
              (name, len(N), ndiff, sum(moves.values()),
               ", ".join("%s->%s %d" % (x, y, m) for (x, y), m in sorted(moves.items())), named, nflag, left),
              file=sys.stderr)
        for (part, r), m in sorted(cnt.items()):
            print("  %-8s %-20s %4d" % (part, r, m), file=sys.stderr)
    with open(a.out, "w") as fo:
        fo.write("\t".join(["run", "part", "old_verdict", "new_verdict", "image", "where", "sentence", "idx",
                            "src_value", "dst_value", "rule", "detail"]) + "\n")
        fo.write("\n".join(out) + "\n")
    for r in out:
        if "\tUNTRIAGED\t" in r:
            print("UNTRIAGED\t" + r, file=sys.stderr)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
