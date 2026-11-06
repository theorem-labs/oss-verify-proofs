#!/usr/bin/env python3
"""hyplist.py WORK OUT [--tag NAME]: list every numeral in a HYPOTHESIS position of WORK/stage-out (coqhyp.py's rules)
and pair it with the same position in WORK/stage (the donor text). proves no function (kind: measurement). Read-only.

Rule def-in-hyp (all depths): an identifier named in a section-hyp / record-field / inductive / lemma-premise / fact-ctor /
state-spec position is
resolved to its Definition / Let / Notation: in the same file first, else in the stage-out file of the module the use
qualifies (M.name) or of a module the file Requires directly; a name with more than one such definer is followed into
every one of them (counted). The numerals of that definition are listed, in the DEFINING file (column ctor: the depth and
the file that names it), and the identifiers of that definition are followed the same way (depth + 1).

Pairing: the registered provenance line '(* Relocated from ... *)' is dropped from the stage-out file (stage-out line =
stage line + 1 below it); the two line lists are aligned with difflib (autojunk off). Lines of an 'equal' block pair one
to one. Inside a 'replace' block the tokens of both sides (comments and strings removed, numerals normalised to NUM) are
aligned: numerals >= 0x10000 are normalised to NUM (smaller ones keep their text); a NUM whose context (4 tokens before
and 2 after; then the 4 before alone) occurs once on each side pairs with that donor NUM; the rest pair by difflib (numerals of an equal or
same-length replace run, by position). A numeral with no partner is NEW.
Decision: SAME = the written token is byte-equal to the paired donor token; DIFFERS otherwise (DIFFERS-FORM when the two
tokens denote the same number, e.g. hex against decimal); NEW = no donor position.

Output: OUT/hyplist[-TAG].tsv  file line col class keyword name ctor written donor_at donor decision
        OUT/hyplist[-TAG].txt  counts by class and decision, the census of numerals not listed.
"""
import collections
import difflib
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import coqhyp  # noqa: E402

PROV = "(* Relocated from"
CLASSES = ["section-hyp", "record-field", "inductive", "lemma-premise", "fact-ctor", "state-spec", "def-in-hyp"]
REQ = re.compile(r"Require\s+(?:Import\s+|Export\s+)?([A-Za-z0-9_ .']+?)\s*\.(?:\s|$)")


def numval(s):
    s = s.replace("_", "")
    return int(s, 16) if s[:2].lower() == "0x" else int(s)


def tree_files(root):
    out = []
    for d, _, fs in os.walk(root):
        for f in fs:
            if f.endswith(".v"):
                out.append(os.path.relpath(os.path.join(d, f), root))
    return sorted(out)


def pair_file(st_text, so_text, so_toks):
    """(line, col) of every stage-out numeral -> (donor line, donor text) or None."""
    so_lines = so_text.split("\n")
    pk = [i for i, l in enumerate(so_lines) if l.startswith(PROV)]
    if len(pk) != 1:
        raise SystemExit("provenance line count %d" % len(pk))
    pk = pk[0]
    b_orig = [i + 1 for i in range(len(so_lines)) if i != pk]          # b index -> stage-out line number
    b_lines = [l for i, l in enumerate(so_lines) if i != pk]
    a_lines = st_text.split("\n")
    a_tok = collections.defaultdict(list)
    for t in coqhyp.lex(st_text):
        a_tok[t[2]].append(t)
    b_tok = collections.defaultdict(list)
    for t in so_toks:
        b_tok[t[2]].append(t)
    pairs = {}
    sm = difflib.SequenceMatcher(None, a_lines, b_lines, autojunk=False)
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == "equal":
            for di in range(i2 - i1):
                ta, tb = a_tok[i1 + di + 1], b_tok[b_orig[j1 + di]]
                if len(ta) != len(tb):
                    _pair_tokens(ta, tb, pairs)     # same text, other token split (a multi-line comment edge)
                    continue
                for x, y in zip(ta, tb):
                    if y[0] == "num":
                        pairs[(y[2], y[3])] = (x[2], x[1]) if x[0] == "num" else None
            continue
        ta = [t for ln in range(i1 + 1, i2 + 1) for t in a_tok[ln]]
        tb = [t for j in range(j1, j2) for t in b_tok[b_orig[j]]]
        _pair_tokens(ta, tb, pairs)
    for t in so_toks:
        if t[0] == "num":
            pairs.setdefault((t[2], t[3]), None)
    return pairs


def _norm(t):
    """numerals >= 0x10000 (image values, which the relocation moves) align as NUM; smaller numerals keep their text, so
    an inserted list entry does not shift the pairing of the entries after it."""
    if t[0] != "num":
        return t[1]
    try:
        return "NUM" if numval(t[1]) >= 0x10000 else t[1]
    except ValueError:
        return t[1]


def _ctx(n, k):
    return (tuple(n[max(0, k - 4):k]), tuple(n[k + 1:k + 3]))


def _pair_tokens(ta, tb, pairs):
    """first, a NUM whose context (4 tokens before and 2 after, normalised; then the 4 tokens before alone) occurs exactly
    once on each side pairs with that donor NUM; then difflib pairs the rest (numerals of equal or same-length replace runs,
    by position)."""
    na = [_norm(t) for t in ta]
    nb = [_norm(t) for t in tb]
    done, used = set(), set()
    for ctx in (_ctx, lambda n, k: _ctx(n, k)[0]):
        ca = collections.defaultdict(list)
        cb = collections.defaultdict(list)
        for k, x in enumerate(na):
            if x == "NUM" and k not in used:
                ca[ctx(na, k)].append(k)
        for k, x in enumerate(nb):
            if x == "NUM" and (tb[k][2], tb[k][3]) not in done:
                cb[ctx(nb, k)].append(k)
        for c, ks in cb.items():
            if len(ks) == 1 and len(ca.get(c, [])) == 1:
                x, y = ta[ca[c][0]], tb[ks[0]]
                pairs[(y[2], y[3])] = (x[2], x[1])
                done.add((y[2], y[3]))
                used.add(ca[c][0])
    used_at = {(ta[k][2], ta[k][3]) for k in used}
    sm = difflib.SequenceMatcher(None, na, nb, autojunk=False)
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op in ("equal", "replace") and i2 - i1 == j2 - j1:
            for x, y in zip(ta[i1:i2], tb[j1:j2]):
                if y[0] == "num" and (y[2], y[3]) not in done:
                    pairs[(y[2], y[3])] = (x[2], x[1]) if x[0] == "num" and (x[2], x[3]) not in used_at else None
        else:
            for y in tb[j1:j2]:
                if y[0] == "num" and (y[2], y[3]) not in done:
                    pairs[(y[2], y[3])] = None


def decide(written, donor):
    if donor is None:
        return "NEW"
    if written == donor:
        return "SAME"
    try:
        if numval(written) == numval(donor):
            return "DIFFERS-FORM"
    except ValueError:
        pass
    return "DIFFERS"


def requires(text):
    mods = set()
    for m in REQ.finditer(text):
        for x in m.group(1).split():
            mods.add(x.split(".")[-1])
    return mods


def main():
    args = sys.argv[1:]
    tag = ""
    if "--tag" in args:
        k = args.index("--tag")
        tag = "-" + args[k + 1]
        del args[k:k + 2]
    if len(args) != 2:
        raise SystemExit("usage: hyplist.py WORK OUT [--tag NAME]")
    work, out = args
    so_root, st_root = os.path.join(work, "stage-out"), os.path.join(work, "stage")
    files = tree_files(so_root)
    st_files = set(tree_files(st_root))
    missing = [f for f in files if f not in st_files]
    if missing:
        raise SystemExit("no donor file for %s" % missing)
    os.makedirs(out, exist_ok=True)
    mod2file = {os.path.basename(f)[:-2]: f for f in files}
    per = {}
    cen = collections.Counter()
    for f in files:
        so_text = open(os.path.join(so_root, f)).read()
        toks = coqhyp.lex(so_text)
        rows, census, used, defs, add, places = coqhyp.classify(toks)
        quals = {t[1].rsplit(".", 1)[0].split(".")[-1] + "." + t[1].rsplit(".", 1)[1]
                 for t in toks if t[0] == "id" and "." in t[1]}
        per[f] = dict(text=so_text, toks=toks, rows=rows, used=used, defs=defs, add=add, places=places, req=requires(so_text),
                      quals=quals)
        cen.update(census)
    # def-in-hyp: every definition a hypothesis position names, and every definition those name (all depths)
    unresolved = collections.Counter()

    def resolve(f, nm):
        P = per[f]
        if nm in P["defs"]:
            return [f]
        cands = [m for m in P["req"] if m in mod2file and nm in per[mod2file[m]]["defs"]]
        cands += [q.split(".")[0] for q in P["quals"] if q.split(".")[1] == nm and q.split(".")[0] in mod2file
                  and nm in per[mod2file[q.split(".")[0]]]["defs"] and q.split(".")[0] not in cands]
        if len(cands) > 1:
            unresolved[nm] += 1
        return [mod2file[c] for c in cands]

    frontier = [(f, nm, f, 1) for f in files for nm in sorted(per[f]["used"])]
    seen = set()
    depth = collections.Counter()
    while frontier:
        nxt = []
        for f, nm, via, d in frontier:
            for g in resolve(f, nm):
                if (g, nm) in seen:
                    continue
                seen.add((g, nm))
                for s in per[g]["defs"][nm]:
                    kw = coqhyp.head(s)[0]
                    for t in s:
                        if t[0] == "num":
                            n0 = len(per[g]["rows"])
                            per[g]["add"](t, "def-in-hyp", kw, nm, "depth %d, named in %s" % (d, via))
                            depth[d] += len(per[g]["rows"]) - n0
                        elif t[0] == "id":
                            nxt.append((g, t[1].split(".")[-1], g, d + 1))
        frontier = nxt
    tsv = open(os.path.join(out, "hyplist%s.tsv" % tag), "w")
    tsv.write("file\tline\tcol\tclass\tkeyword\tname\tctor\twritten\tdonor_at\tdonor\tdecision\n")
    cnt = collections.Counter()
    ucnt = collections.Counter()
    unl = open(os.path.join(out, "unlisted-differs%s.tsv" % tag), "w")
    unl.write("file\tline\tcol\tplace\tkeyword\tname\twritten\tdonor_at\tdonor\tdecision\n")
    for f in files:
        P = per[f]
        st_text = open(os.path.join(st_root, f)).read()
        pairs = pair_file(st_text, P["text"], P["toks"])
        listed_keys = {(r[0][2], r[0][3]) for r in P["rows"]}
        for t in P["toks"]:
            if t[0] != "num" or (t[2], t[3]) in listed_keys:
                continue
            p = pairs.get((t[2], t[3]))
            dl, dv = (p if p else (None, None))
            dec = decide(t[1], dv)
            pl = P["places"].get((t[2], t[3]), ("definition", "?", ""))
            ucnt[(pl[0], dec)] += 1
            if dec != "SAME":
                unl.write("\t".join(map(str, (f, t[2], t[3] + 1, pl[0], pl[1], pl[2], t[1],
                                               ("%s:%s" % (f, dl)) if dl else "-", dv if dv else "-", dec))) + "\n")
        for t, cls, kw, name, extra in sorted(P["rows"], key=lambda r: (r[0][2], r[0][3])):
            p = pairs.get((t[2], t[3]))
            dl, dv = (p if p else (None, None))
            dec = decide(t[1], dv)
            cnt[(cls, dec)] += 1
            cnt[("ALL", dec)] += 1
            tsv.write("\t".join(map(str, (f, t[2], t[3] + 1, cls, kw, name, extra, t[1],
                                          ("%s:%s" % (f, dl)) if dl else "-", dv if dv else "-", dec))) + "\n")
    tsv.close()
    unl.close()
    total = sum(1 for f in files for t in per[f]["toks"] if t[0] == "num")
    with open(os.path.join(out, "hyplist%s.txt" % tag), "w") as o:
        o.write("hyplist.py %s: %d stage-out files paired with %d stage files; %d numerals outside comments and strings\n"
                % (work, len(files), len(st_files), total))
        decs = ["SAME", "DIFFERS", "DIFFERS-FORM", "NEW"]
        o.write("class\t" + "\t".join(decs) + "\ttotal\n")
        for cls in CLASSES + ["ALL"]:
            o.write(cls + "\t" + "\t".join(str(cnt[(cls, d)]) for d in decs) + "\t%d\n" % sum(cnt[(cls, d)] for d in decs))
        listed = sum(cnt[("ALL", d)] for d in decs)
        rest = total - listed - cen["in-proof"] - cen["conclusion"] - cen["other"]
        o.write("not listed (census): in proof bodies %d, in lemma conclusions %d, in other vernacular %d, in other "
                "definitions and computed (Eval) states %d; listed + not listed = %d of %d\n"
                % (cen["in-proof"], cen["conclusion"], cen["other"], rest,
                   listed + cen["in-proof"] + cen["conclusion"] + cen["other"] + rest, total))
        o.write("not listed, by place and decision: " + ", ".join("%s %s %d" % (k[0], k[1], v) for k, v in sorted(ucnt.items()))
                + " (rows not SAME: unlisted-differs%s.tsv)\n" % tag)
        o.write("def-in-hyp rows by depth: " + ", ".join("%d: %d" % kv for kv in sorted(depth.items())) + "\n")
        o.write("names used in a hypothesis position with more than one definer (all followed): %d %s\n"
                % (len(unresolved), " ".join(sorted(unresolved))[:2000]))
    print(open(os.path.join(out, "hyplist%s.txt" % tag)).read(), end="")


if __name__ == "__main__":
    main()
