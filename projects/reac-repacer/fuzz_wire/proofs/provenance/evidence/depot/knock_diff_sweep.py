#!/usr/bin/env python3
"""knock_diff_sweep.py GRANT_A KNOCK_A KNOCK_FILES OUT.tsv -- every lib/A file the knock run does NOT carry
(not in KNOCK_FILES) whose knock release text differs from grant's release text beyond the module paths, the
AB1v -> AWalkFw0 rename, numerals and the YImgTop lineage: those files may need knock's text because a callee's
statement changed with the depot form (as A/AFfs.v did: knock passes HND to afree_mid). Line-level diff of the
comment-stripped texts, then a token diff inside each changed line hunk. One row per file: ops, depot-named ops, the
first two ops."""
import difflib, os, re, sys
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from depot_classify import norm_lines  # noqa: E402

NUM = re.compile(r"^(?:0 ?x[0-9a-f]+|x[0-9a-f]+|\d+)$")
DEP = re.compile(r"depot|HND|st_depot|KnBlock|DZONE|layout_grow|put_effect|nb_ext|sb_ext|StackDepot|TwoLevel|StackStore|DPOST")
TOK = re.compile(r"[\w'.]+|[^\s\w]")


def one(args):
    g, k, f = args
    norm = lambda l, u: re.sub(r'\.lib\.Reusable\b', '.lib', re.sub(u, 'X', l))
    gl = [norm(l, 'fuzz_grant') for _, l in norm_lines(open(os.path.join(g, f)).read())]
    kl = [norm(l, 'fuzz_knock') for _, l in norm_lines(open(os.path.join(k, f)).read())]
    if gl == kl:
        return None
    ops = []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, gl, kl, autojunk=False).get_opcodes():
        if tag == 'equal':
            continue
        a = TOK.findall(' '.join(gl[i1:i2]))
        b = TOK.findall(' '.join(kl[j1:j2]))
        for t2, a1, a2, b1, b2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
            if t2 == 'equal':
                continue
            ga, kb = a[a1:a2], b[b1:b2]
            if all(NUM.match(x) for x in ga + kb):
                continue
            gs, ks = ' '.join(ga), ' '.join(kb)
            if (gs, ks) == ('AB1v', 'AWalkFw0') or ('YImgTop' in ks and not DEP.search(ks)) or ('YImgTop' in gs and not DEP.search(gs)):
                continue
            ops.append((t2, gs[:100], ks[:160]))
    if not ops:
        return None
    return (f, len(ops), sum(1 for o in ops if DEP.search(o[1] + ' ' + o[2])), ops[:2])


def main():
    g, k, kfiles, out = sys.argv[1:5]
    kf = {l.strip() for l in open(kfiles) if l.strip()}
    todo = [(g, k, f) for f in sorted(os.listdir(g)) if f.endswith('.v') and 'A/' + f not in kf and os.path.exists(os.path.join(k, f))]
    with Pool(16) as p:
        res = [r for r in p.map(one, todo) if r]
    with open(out, 'w') as o:
        o.write('file\tops\tdepot-named ops\tfirst ops\n')
        for r in res:
            o.write('A/%s\t%d\t%d\t%s\n' % (r[0], r[1], r[2], ' || '.join('%s grant[%s] -> knock[%s]' % x for x in r[3])))
    print('knock_diff_sweep: %d files compared, %d differ' % (len(todo), len(res)))


if __name__ == '__main__':
    main()
