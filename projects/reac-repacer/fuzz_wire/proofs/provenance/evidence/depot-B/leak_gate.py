#!/usr/bin/env python3
"""leak_gate.py [--exceptions TSV] GRANT_A APPLIED_A FILE... -- the leak-watch GATE on the consumer hunk map (the unit owner's condition (2)).

GRANT_A/<F>: the unit's relocated grant text of a consumer; APPLIED_A/<F>: the same file after depot_apply.py. Every
token difference grant -> applied (comments removed, module paths mapped) is one residue piece of a TAKEN hunk. A piece
that names the empty-depot form (depot_classify.DEPOTNAME / GROW) is depot; a piece of punctuation only is restructuring;
every other piece is listed as 'depot-induced restructuring (for review)'. Then each piece is scanned for the known
LINEAGE tokens of the knock release: an `unfold` of YImgTop.IMG_LO / IMG_TOP (IMG_TOP as a Definition), EV_MAX / 8192 /
11776, 2 ^ 31, kFreeArrayOffset, an AF0m row index (nth_error_In Tfib_const_abs N), prim_committed_bound, a stack-class
literal (cid = N, pc_stack_malloc). Every LINEAGE token of a piece is a hit unless a row of the --exceptions table (file,
applied line, token, a needle the applied piece contains, reason) clears it. The gate PASSES (exit 0) iff no hit is
left AND every exception row cleared a hit (a row no hit uses is stale and fails the gate); else exit 1.
Prints a TSV: file, line (applied), kind, lineage hit, grant tokens, applied tokens; then the counts."""
import difflib, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import depot_classify as dc  # noqa: E402

LINEAGE = re.compile(r'unfold [^<]*?YImgTop\.IMG_(?:LO|TOP)|\bEV_MAX\b|\b8192\b|\b11776\b|2 \^ 31|kFreeArrayOffset|'
                     r'nth_error_In Tfib_const_abs \d+|prim_committed_bound\w*|\bcid = \d|pc_stack_malloc')


def load_exceptions(path):
    """rows (file, line, token, needle, reason): a LINEAGE hit is cleared only by a row whose file, applied line and
    token are the hit's and whose needle occurs in the applied piece"""
    rows = []
    for k, l in enumerate(open(path).read().split('\n')):
        if k == 0 or not l.strip() or l.startswith('#'):
            continue
        f, ln, tok, needle, why = l.split('\t')
        rows.append((f, int(ln), tok, needle, why))
    return rows


def main():
    args = sys.argv[1:]
    exc = []
    if args[:1] == ['--exceptions']:
        exc, args = load_exceptions(args[1]), args[2:]
    ga, aa = args[:2]
    used = set()
    print('file\tline\tkind\tlineage\tgrant\tapplied')
    n = {'depot': 0, 'punctuation': 0, 'review': 0, 'lineage': 0, 'excepted': 0}
    for f in args[2:]:
        g = dc.tokens(open(os.path.join(ga, f)).read())
        a = dc.tokens(open(os.path.join(aa, f)).read())
        for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, [x for x, _ in g], [x for x, _ in a], autojunk=False).get_opcodes():
            if tag == 'equal':
                continue
            gs = ' '.join(x for x, _ in g[i1:i2])
            as_ = ' '.join(x for x, _ in a[j1:j2])
            txt = gs + ' || ' + as_
            ln = a[j1][1] if j1 < len(a) else a[-1][1]
            if dc.DEPOTNAME.search(txt) or dc.GROW.search(txt):
                kind = 'depot'
            elif all(x in dc.PUNCT for x, _ in g[i1:i2] + a[j1:j2]):
                kind = 'punctuation'
            else:
                kind = 'review'
            n[kind] += 1
            # every LINEAGE token of the piece must be cleared by its own exception row, else it is a hit
            marks = []
            for m in LINEAGE.finditer(as_):
                hit = [r for r in exc if r[0] == f and r[1] == ln and r[2] == m.group(0) and r[3] in as_]
                if hit:
                    used.update(hit)
                    n['excepted'] += 1
                    marks.append(m.group(0) + ' (excepted)')
                else:
                    n['lineage'] += 1
                    marks.append(m.group(0))
            print('%s\t%d\t%s\t%s\t%s\t%s' % (f, ln, kind, '; '.join(marks) or '-', gs[:300], as_[:300]))
    stale = [r for r in exc if r not in used]
    for r in stale:
        print('# exception row not used by any hit (stale): %s:%d %s' % (r[0], r[1], r[2]))
    print('# pieces: depot %d, punctuation %d, depot-induced restructuring for review %d; LINEAGE hits %d; excepted %d; '
          'stale exception rows %d' % (n['depot'], n['punctuation'], n['review'], n['lineage'], n['excepted'], len(stale)))
    sys.exit(1 if n['lineage'] or stale else 0)


if __name__ == '__main__':
    main()
