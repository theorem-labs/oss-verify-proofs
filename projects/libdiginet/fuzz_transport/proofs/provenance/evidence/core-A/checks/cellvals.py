#!/usr/bin/env python3
"""cellvals.py WORK LIB OUT: every memory value the relocated core states at an image address (`val_mem .. A n V`,
`lit1 / lit2 / lit4 / lit8 / flit8 A V`, `mkChunk A (CVal n (SLit V))`, `tfib_const_lookup .. A n V`; n in 1, 2, 4, 8) read
in the target image: at a file-backed address the n bytes the stripped pin holds there must be V (little-endian); a
.bss address holds no image bytes (a runtime value) and is counted apart. Comment lines are left out. Built-in planted
control: the same check with the first file-backed statement's value plus one must report exactly that statement.
Read-only. Output: OUT/cellvals.txt, OUT/cellvals.tsv.
"""
import collections
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import decval as DV  # noqa: E402
from symoff import Res, lab  # noqa: E402

N = r"(0x[0-9a-fA-F]+|\d+)"
PATS = [
    ("val_mem", re.compile(r"val_mem\b[^;]*?\s" + N + r"\s+([1248])\s+" + N + r"\b"), (0, 1, 2)),
    ("lit", re.compile(r"\bf?lit([1248])\s+(0x[0-9a-fA-F]+)\s+" + N + r"\b"), (1, 0, 2)),
    ("chunk", re.compile(r"mkChunk\s+(0x[0-9a-fA-F]+)\s+\(CVal\s+([1248])\s+\(SLit\s+" + N + r"\)\)"), (0, 1, 2)),
    ("lookup", re.compile(r"tfib_const_lookup\s+\S+\s+\S+\s+\S+\s+\S+\s+\(w_H W\)\s+\S+\s+(0x[0-9a-fA-F]+)\s+([1248])\s+" + N + r"\b"), (0, 1, 2)),
]


def statements(cfg):
    for t, dp in DV.file_list(cfg):
        depth = 0
        for j, line in enumerate(open(os.path.join(cfg["core"], t)).read().splitlines()):
            incom = depth > 0
            depth = max(0, depth + line.count("(*") - line.count("*)"))
            if incom or DV.role(line) == "comment":
                continue
            for k, rx, (ia, iz, iv) in PATS:
                for m in rx.finditer(line):
                    g = m.groups()
                    yield t, j + 1, k, DV.val(g[ia]), int(g[iz]), DV.val(g[iv])


def judge(TR, a, n, v):
    if not 0x10000 <= a < TR.top:
        return "NOT-IMAGE", None
    fb = any(lo <= a and a + n <= lo + len(d) for lo, m, d in TR.loads)
    got = int.from_bytes(TR.rd(a, n), "little")
    v &= (1 << (8 * n)) - 1
    if not fb:
        return "NOBITS", got
    return ("SAME" if got == v else "DIFF"), got


def main():
    work, lib, out = sys.argv[1:4]
    cfg = DV.setup([work])
    TR = Res(cfg["tgt_syms"], cfg["tgt_bytes"])
    st = list(statements(cfg))
    rows, cnt = [], collections.Counter()
    for t, ln, k, a, n, v in st:
        dec, got = judge(TR, a, n, v)
        cnt[(k, dec)] += 1
        rows.append((dec, "%s:%d" % (t, ln), k, "%#x" % a, str(n), "%#x" % v, "%#x" % got if got is not None else "-", lab(TR.resolve(a))))
    with open(os.path.join(out, "cellvals.tsv"), "w") as f:
        f.write("decision\tat\tform\taddress\tbytes\tstated\timage\tsymbol\n")
        for r in rows:
            f.write("\t".join(r) + "\n")
    bad = [r for r in rows if r[0] == "DIFF"]
    lines = ["# cellvals.py: %d stated memory values at image addresses in stage-out, read in %s" % (len(st), os.path.basename(cfg["tgt_bytes"]))]
    lines.append("  " + ", ".join("%s %s %d" % (k, d, c) for (k, d), c in sorted(cnt.items())))
    for r in bad:
        lines.append("FINDING\t" + "\t".join(r))
    lines.append("result: file-backed statements %d: SAME %d, DIFF %d; .bss statements (runtime values, no image bytes) %d" % (
        sum(1 for r in rows if r[0] in ("SAME", "DIFF")), sum(1 for r in rows if r[0] == "SAME"), len(bad), sum(1 for r in rows if r[0] == "NOBITS")))
    fb = next((x for x in st if judge(TR, x[3], x[4], x[5])[0] == "SAME"), None)
    if fb:
        t, ln, k, a, n, v = fb
        fi = st.index(fb)
        pl = [judge(TR, a2, n2, v2 + 1 if i == fi else v2)[0] for i, (t2, ln2, k2, a2, n2, v2) in enumerate(st)]
        nd = sum(1 for d in pl if d == "DIFF")
        lines.append("control: %s:%d %s %#x %d: stated %#x -> %#x: DIFF %d -> %d: %s" % (
            t, ln, k, a, n, v, v + 1, len(bad), nd, "PASS" if nd == len(bad) + 1 else "FAIL"))
    open(os.path.join(out, "cellvals.txt"), "w").write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
