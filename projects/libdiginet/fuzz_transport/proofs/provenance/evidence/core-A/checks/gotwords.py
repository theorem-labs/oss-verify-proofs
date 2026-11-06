#!/usr/bin/env python3
"""gotwords.py WORK LIB OUT [--tag NAME]: item 3 of the TCA value lane, the .got words the relocated image-A core states,
read by CONTENT in both images (D9's records/GOT-WORDS.md method, with every numeral of the core in the scan, not only
check.tsv's rows). Read-only. proves no function (kind: measurement).

Neither image has a PT_DYNAMIC segment, a .dynamic section or a .rela.dyn section (measured and printed below), so every
.got word is the 8 bytes the static link wrote; those bytes are read from the stripped image of record and named by the
unstripped twin's .symtab (the smallest sized symbol holding the value, or the label / end at it; a value below 0x10000
is compared as a value: 0, 1, the TLS offset 0x10).

  A. every numeral of WORK/stage-out/{A,Reusable}/*.v whose value lies in the target's .got [lo, hi): the cell must be
     8-byte aligned and its aligned donor token (WORK/stage, numerals masked, decval.py's alignment) a donor .got cell at
     the same offset from .got's start; the target word and the donor word must hold the same symbol + offset (or the
     same value). A comment numeral is listed apart (port_core edits no comment).
  B. every value the text states for a .got cell (`lit8 A V`, `mkChunk A (CVal 8 (SLit V))`, `val_mem .. A 8 V`): V must
     be the 8 bytes the target holds at A.
  C. check.tsv's got-word rows (old donor cell -> new target cell: same content by symbol) and got-value rows (a value a
     donor .got cell holds -> the value the twin target cell holds: new must be exactly that word, and the twin of old).
  D. GOT[0] (registry check OK-GOT0): every numeral equal to the target .got start names GOT[0]; the value must be the
     target's own .got start and the word there 0 (no .dynamic) or .dynamic's address; the donor's likewise.
  E. the whole .got, word by word: target word k and donor word k hold the same symbol + offset (or value).
Output: OUT/gotwords[-TAG].tsv (one row per checked numeral / row), OUT/gotwords[-TAG].txt (result lines).
"""
import collections
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import decval as DV  # noqa: E402
from symoff import Res, lab, same_obj  # noqa: E402
from elftools.elf.elffile import ELFFile  # noqa: E402

STATED = [
    re.compile(r"\blit8\s+(0x[0-9a-fA-F]+)\s+(0x[0-9a-fA-F]+|\d+)"),
    re.compile(r"mkChunk\s+(0x[0-9a-fA-F]+)\s+\(CVal 8 \(SLit (0x[0-9a-fA-F]+|\d+)\)\)"),
    re.compile(r"val_mem\b[^;]*?\s(0x[0-9a-fA-F]+)\s+8\s+(0x[0-9a-fA-F]+|\d+)"),
]


def name(R, w):
    return lab(R.resolve(w)) if w >= 0x10000 else "value %#x" % w


def dyninfo(path):
    e = ELFFile(open(path, "rb"))
    return ("PT_DYNAMIC %d, .dynamic %s, .rela.dyn %s, .got.plt %s" % (
        sum(1 for s in e.iter_segments() if s["p_type"] == "PT_DYNAMIC"),
        "yes" if e.get_section_by_name(".dynamic") else "none", "yes" if e.get_section_by_name(".rela.dyn") else "none",
        "yes" if e.get_section_by_name(".got.plt") else "none"),
        e.get_section_by_name(".dynamic"))


def main():
    a = sys.argv[1:]
    if len(a) < 3:
        sys.exit("usage: gotwords.py WORK LIB OUT [--tag NAME]")
    work, lib, out = a[:3]
    tag = ("-" + a[a.index("--tag") + 1]) if "--tag" in a else ""
    cfg = DV.setup([work])
    TR, DR = Res(cfg["tgt_syms"], cfg["tgt_bytes"]), Res(cfg["don_syms"], cfg["don_bytes"])
    (tlo, tsz), (dlo, dsz) = [[(x, z) for n, x, z in R.secs if n == ".got"][0] for R in (TR, DR)]
    rows, lines, bad = [], [], collections.Counter()
    tdyn, tds = dyninfo(cfg["tgt_syms"])
    ddyn, dds = dyninfo(cfg["don_syms"])
    lines.append("# images: target %s .got [%#x, %#x) (%d words): %s; donor %s .got [%#x, %#x) (%d words): %s" % (
        os.path.basename(cfg["tgt_bytes"]), tlo, tlo + tsz, tsz // 8, tdyn, os.path.basename(cfg["don_bytes"]), dlo,
        dlo + dsz, dsz // 8, ddyn))

    # ---- E. the whole .got, word by word
    ediff = []
    for k in range(0, min(tsz, dsz), 8):
        tw, dw = TR.q(tlo + k), DR.q(dlo + k)
        if not same_obj(DR, dw, TR, tw):
            ediff.append("%#x" % k)
    lines.append("E. whole .got: %d words, %d hold a different symbol + offset (or value) at the same offset%s" % (
        min(tsz, dsz) // 8, len(ediff), (": " + " ".join(ediff[:20])) if ediff else ""))
    bad["E"] += len(ediff)

    # ---- A. every numeral of the core in the target .got
    rel = DV.file_list(cfg)
    ast, cells = collections.Counter(), collections.defaultdict(lambda: [0, ""])
    for t, dp in rel:
        d, c, pr = DV.align(dp, os.path.join(cfg["core"], t))
        depth = 0
        for j, line in enumerate(c):
            incom = depth > 0
            depth = max(0, depth + line.count("(*") - line.count("*)"))
            tk = DV.toks(line)
            dtk = DV.toks(d[pr[j]]) if j in pr else None
            for i, s in enumerate(tk):
                v = DV.val(s)
                if not tlo <= v < tlo + tsz:
                    continue
                dt = dtk[i] if dtk is not None and len(dtk) == len(tk) else None
                com = incom or DV.role(line) == "comment"
                tw = TR.q(v - v % 8)
                if dt is None:
                    dec, ev = "GOT-NO-DONOR-TOKEN", "no aligned donor token"
                else:
                    dv = DV.val(dt)
                    if not dlo <= dv < dlo + dsz:
                        dec, ev = "GOT-DIFF", "donor token %s is not a donor .got cell" % dt
                    else:
                        dw = DR.q(dv - dv % 8)
                        same = same_obj(DR, dw, TR, tw)
                        okoff = v % 8 == 0 and dv % 8 == 0 and v - tlo == dv - dlo
                        dec = "GOT-SAME" if same and okoff else "GOT-DIFF"
                        ev = "target %#x (.got+%#x) holds %#x = %s; donor %#x (.got+%#x) holds %#x = %s" % (
                            v, v - tlo, tw, name(TR, tw), dv, dv - dlo, dw, name(DR, dw))
                if com:
                    dec = "COMMENT-" + dec
                ast[dec] += 1
                if dec == "GOT-SAME":
                    cells[v][0] += 1
                    cells[v][1] = name(TR, tw)
                elif not com:
                    bad["A"] += 1
                rows.append(("A", dec, "%s:%d" % (t, j + 1), dt or "-", s, ev))
    lines.append("A. core numerals in the target .got: %d %s; %d distinct cells" % (sum(ast.values()), dict(ast), len(cells)))
    for v in sorted(cells):
        lines.append("   cell %#x (.got+%#x) holds %s  x%d" % (v, v - tlo, cells[v][1], cells[v][0]))

    # ---- B. stated cell values
    bst = collections.Counter()
    for t, dp in rel:
        for j, line in enumerate(open(os.path.join(cfg["core"], t)).read().splitlines()):
            for rx in STATED:
                for m in rx.finditer(line):
                    ad, sv = int(m.group(1), 16), DV.val(m.group(2))
                    if not tlo <= ad < tlo + tsz:
                        continue
                    ok = TR.q(ad) == sv
                    bst["stated value = the cell's 8 bytes" if ok else "STATED VALUE DIFFERS"] += 1
                    rows.append(("B", "STATED-SAME" if ok else "STATED-DIFF", "%s:%d" % (t, j + 1), "-", "%#x" % sv,
                                 "cell %#x: the target holds %#x = %s" % (ad, TR.q(ad), name(TR, TR.q(ad)))))
                    bad["B"] += 0 if ok else 1
    lines.append("B. .got cell values the text states (lit8 / mkChunk CVal 8 / val_mem 8): %d %s" % (sum(bst.values()), dict(bst)))

    # ---- C. check.tsv's got-word / got-value rows (line = the donor's; stage-out holds the written value one line lower)
    cst = collections.Counter()
    ck = os.path.join(work, "check.tsv")
    ckrows = [l.rstrip("\n").split("\t") for l in open(ck).read().splitlines()[1:]] if os.path.exists(ck) else []
    if not ckrows:
        lines.append("C. no check.tsv in %s: part C not run" % work)
    so = {}
    for r in ckrows:
        if not r[4].startswith(("got-word", "got-value")):
            continue
        if r[0] not in so:
            so[r[0]] = open(os.path.join(cfg["core"], r[0])).read().splitlines()
        L = so[r[0]]
        ln = int(r[1])
        present = any(0 < k <= len(L) and int(r[3], 16) in {DV.val(x) for x in DV.toks(L[k - 1])} for k in (ln + 1, ln))
        old, new = int(r[2], 16), int(r[3], 16)
        if r[4].startswith("got-word"):
            ok = (dlo <= old < dlo + dsz and tlo <= new < tlo + tsz and old - dlo == new - tlo
                  and same_obj(DR, DR.q(old), TR, TR.q(new)))
            ev = "donor cell %#x holds %s; target cell %#x holds %s" % (old, name(DR, DR.q(old)), new, name(TR, TR.q(new)))
            kind = "got-word"
        else:
            cell = int(re.search(r"held by GOT (0x[0-9a-f]+)", r[4]).group(1), 16)
            tcell = cell - dlo + tlo
            ok = DR.q(cell) == old and TR.q(tcell) == new and same_obj(DR, old, TR, new)
            ev = "donor cell %#x holds %#x = %s; its twin cell %#x holds %#x = %s; written %#x" % (
                cell, DR.q(cell), name(DR, DR.q(cell)), tcell, TR.q(tcell), name(TR, TR.q(tcell)), new)
            kind = "got-value"
        ev += "; stage-out %s line %d / %d holds the written value: %s" % (r[0], ln + 1, ln, present)
        ok = ok and present
        cst[(kind, ok)] += 1
        bad["C"] += 0 if ok else 1
        rows.append(("C", "%s %s" % (kind, "SAME" if ok else "DIFF"), "%s:%s" % (r[0], r[1]), r[2], r[3], ev))
    lines.append("C. check.tsv rows: " + ", ".join("%s %s %d" % (k, "SAME" if o else "DIFF", c) for (k, o), c in sorted(cst.items())))

    # ---- D. GOT[0] (OK-GOT0)
    def got0(R, lo, ds):
        w = R.q(lo)
        want = ds["sh_addr"] if ds is not None else 0
        return w, want, w == want
    tw0, twant, tok = got0(TR, tlo, tds)
    dw0, dwant, dok = got0(DR, dlo, dds)
    g0 = [x for x in rows if x[0] == "A" and DV.val(x[4]) == tlo]
    g0ok = all(x[1].endswith("GOT-SAME") for x in g0)
    lines.append("D. OK-GOT0: target GOT[0] = .got start %#x, its word %#x (OK-GOT0 wants %#x: %s); donor GOT[0] = %#x, word %#x "
                 "(wants %#x: %s); core numerals naming GOT[0] (= %#x): %d (%s), each GOT-SAME: %s" % (
                     tlo, tw0, twant, "OK" if tok else "BAD", dlo, dw0, dwant, "OK" if dok else "BAD", tlo, len(g0),
                     " ".join(x[2] for x in g0), g0ok))
    bad["D"] += (0 if tok and dok and g0ok else 1)
    for x in rows:
        if x[1] in ("GOT-DIFF", "GOT-NO-DONOR-TOKEN", "STATED-DIFF") or x[1].endswith("DIFF"):
            lines.append("FINDING\t%s\t%s\t%s\t%s -> %s\t%s" % (x[0], x[1], x[2], x[3], x[4], x[5]))
    lines.append("result: .got words wrong: %d (A %d, B %d, C %d, D %d, E %d)" % (
        sum(bad.values()), bad["A"], bad["B"], bad["C"], bad["D"], bad["E"]))
    with open(os.path.join(out, "gotwords%s.tsv" % tag), "w") as f:
        f.write("part\tdecision\tat\tdonor\twritten\tevidence\n")
        for x in rows:
            f.write("\t".join(x) + "\n")
    open(os.path.join(out, "gotwords%s.txt" % tag), "w").write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
