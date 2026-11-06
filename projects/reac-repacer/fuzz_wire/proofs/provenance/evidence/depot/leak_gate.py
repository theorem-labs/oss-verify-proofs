#!/usr/bin/env python3
"""leak_gate.py GRANT_A APPLIED_A FILE... -- the leak-watch GATE on the consumer hunk map (the unit owner's condition (2)).

GRANT_A/<F>: the unit's relocated grant text of a consumer; APPLIED_A/<F>: the same file after depot_apply.py. Every
token difference grant -> applied (comments removed, module paths mapped) is one residue piece of a TAKEN hunk. A piece
that names the empty-depot form (depot_classify.DEPOTNAME / GROW) is depot; a piece of punctuation only is restructuring;
every other piece is listed as 'depot-induced restructuring (for review)'. Then each piece is scanned for the known
LINEAGE tokens of the knock release: an `unfold` of YImgTop.IMG_LO / IMG_TOP (IMG_TOP as a Definition), EV_MAX / 8192 /
11776, 2 ^ 31, kFreeArrayOffset, an AF0m row index (nth_error_In Tfib_const_abs N), prim_committed_bound, a stack-class
literal (cid = N, pc_stack_malloc). A lineage hit left after the split rules FAILS the gate (exit 1).
Prints a TSV: file, line (applied), kind, lineage hit, grant tokens, applied tokens; then the counts.

The grant-term rule (the unit owner's ruling, for the NUMERAL lineage tokens 8192 and 11776): a numeral hit counts as
LINEAGE only if GRANT_A's file of the same name does NOT carry the same numeral in the same TERM. The TERM of a numeral
is the numeral and the two tokens directly before it in the file's token stream (for `MSv / 8 + 8192`, the term is
`8 + 8192`). The term match is EXACT, token for token, after the gate's existing normalisation (depot_classify.tokens:
comments removed, module paths, image and record names masked); nothing else is normalised. A numeral hit whose term
GRANT_A's file carries is a grant-lineage number, not knock's EV_MAX, and is counted apart (`numeral hits in a grant
term`). Every other LINEAGE token is unchanged by this rule.
`leak_gate.py --test` runs the rule's tests: the same term in grant clears the hit; a knock-only EV_MAX term and a term
that grant carries the numeral in DIFFERENTLY both still fail."""
import difflib, os, re, sys, tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import depot_classify as dc  # noqa: E402

LINEAGE = re.compile(r'unfold [^<]*?YImgTop\.IMG_(?:LO|TOP)|\bEV_MAX\b|\b8192\b|\b11776\b|2 \^ 31|kFreeArrayOffset|'
                     r'nth_error_In Tfib_const_abs \d+|prim_committed_bound\w*|\bcid = \d|pc_stack_malloc')
NUMERALS = re.compile(r'\b(?:8192|11776)\b')   # the numeral LINEAGE tokens the grant-term rule applies to
OTHER = re.compile(r'unfold [^<]*?YImgTop\.IMG_(?:LO|TOP)|\bEV_MAX\b|2 \^ 31|kFreeArrayOffset|'
                   r'nth_error_In Tfib_const_abs \d+|prim_committed_bound\w*|\bcid = \d|pc_stack_malloc')


def term(toks, k):
    """the TERM of the numeral at token index k: it and the two tokens before it"""
    return tuple(x for x, _ in toks[max(0, k - 2):k + 1])


def gate(ga, aa, files, out=print):
    """the gate on GRANT_A / APPLIED_A for FILES; returns the counts"""
    out('file\tline\tkind\tlineage\tgrant\tapplied')
    n = {'depot': 0, 'punctuation': 0, 'review': 0, 'lineage': 0, 'grant-term': 0}
    for f in files:
        g = dc.tokens(open(os.path.join(ga, f)).read())
        a = dc.tokens(open(os.path.join(aa, f)).read())
        gterms = {term(g, k) for k, (x, _) in enumerate(g) if NUMERALS.search(x)}
        for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, [x for x, _ in g], [x for x, _ in a], autojunk=False).get_opcodes():
            if tag == 'equal':
                continue
            gs = ' '.join(x for x, _ in g[i1:i2])
            as_ = ' '.join(x for x, _ in a[j1:j2])
            txt = gs + ' || ' + as_
            ln = a[j1][1] if j1 < len(a) else a[-1][1]
            other = OTHER.search(as_)
            nums = [k for k in range(j1, j2) if NUMERALS.search(a[k][0])]
            left = [k for k in nums if term(a, k) not in gterms]
            n['grant-term'] += len(nums) - len(left)
            lin = other.group(0) if other else (a[left[0]][0] if left else None)
            if dc.DEPOTNAME.search(txt) or dc.GROW.search(txt):
                kind = 'depot'
            elif all(x in dc.PUNCT for x, _ in g[i1:i2] + a[j1:j2]):
                kind = 'punctuation'
            else:
                kind = 'review'
            n[kind] += 1
            if lin:
                n['lineage'] += 1
            out('%s\t%d\t%s\t%s\t%s\t%s' % (f, ln, kind, lin or '-', gs[:300], as_[:300]))
    out('# pieces: depot %d, punctuation %d, depot-induced restructuring for review %d; LINEAGE hits %d; numeral hits in a '
        'grant term %d' % (n['depot'], n['punctuation'], n['review'], n['lineage'], n['grant-term']))
    return n


def selftest():
    cases = [  # (name, grant text, applied text, expected LINEAGE hits)
        ('the same term in grant clears the hit',
         'Definition a := slackS (MSv + (MSv / 8 + 8192)).\n',
         'Definition a := FPP_site (MSv + MSv / 8 + 8192).\n', 0),
        ('a planted knock-only EV_MAX term still fails',
         'Definition b := fun y => y < 11776.\n',
         'Definition b := fun y => y < 8192.\n', 1),
        ('grant carries the numeral in a different term: still fails',
         'Definition c := fun z => z * 8192.\nDefinition d := fun w => w.\n',
         'Definition c := fun z => z * 2.\nDefinition d := fun w => w + 8192.\n', 1),
    ]
    bad = 0
    for name, gt, at, want in cases:
        d = tempfile.mkdtemp()
        for sub, t in (('g', gt), ('a', at)):
            os.makedirs(os.path.join(d, sub))
            open(os.path.join(d, sub, 'T.v'), 'w').write(t)
        got = gate(os.path.join(d, 'g'), os.path.join(d, 'a'), ['T.v'], out=lambda s: None)['lineage']
        ok = (got > 0) == (want > 0)
        bad += not ok
        print('leak_gate --test: %s: LINEAGE hits %d (%s)' % (name, got, 'ok' if ok else 'WRONG'))
    print('leak_gate --test: %d of %d case(s) as expected' % (len(cases) - bad, len(cases)))
    return bad


def main():
    if sys.argv[1:] == ['--test']:
        sys.exit(1 if selftest() else 0)
    n = gate(sys.argv[1], sys.argv[2], sys.argv[3:])
    sys.exit(1 if n['lineage'] else 0)


if __name__ == '__main__':
    main()
