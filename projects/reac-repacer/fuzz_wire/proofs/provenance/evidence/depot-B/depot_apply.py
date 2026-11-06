#!/usr/bin/env python3
"""depot_apply.py [--consumer [--sub B] [--lib-repo proofs/P/U/lib]] GRANT_REL KNOCK_REL CLASSES.tsv OUT_DIR [--take FILE:HUNK ...] -- the empty-depot switch of
libreac/fuzz_knock's released kernel, taken into fuzz_grant's released kernel text hunk by hunk.

GRANT_REL / KNOCK_REL: the two released libs in repository layout (proofs/libreac/fuzz_grant/lib at commit
4f87de75d67, proofs/libreac/fuzz_knock/lib at 88154566652a). CLASSES.tsv: depot_classify.py's table. For every file it
names, the line hunks are recomputed exactly as depot_classify.py numbers them (comment-stripped lines, difflib), and a
hunk is TAKEN when its class is depot or layout-grow, or when it is named by --take FILE:HUNK (an 'other' hunk a ruling
admits), or by --merge FILE:HUNK:OLD=NEW (a hunk mixing a depot change with a grant-lineage name: knock's lines with
the one occurrence of OLD written back as grant's NEW), or by --glue FILE:HUNK:OLD=>NEW (a taken hunk whose knock text
needs one line of glue that this file's kept grant text forces: OLD, occurring once in knock's lines, becomes NEW);
every other hunk keeps grant's text. --imgtop-unfold applies imgtop_rule.py to the knock lines of every taken hunk.
--merge / --glue OLD=NEW#N: OLD must occur exactly N times (default 1). A taken hunk replaces grant's lines of the hunk by knock's (an insertion
lands after grant's preceding line and carries knock's comment lines just above it), with knock's module paths written
as grant's. No notice line is added (the hunk table and this run's log are the record). OUT_DIR/<F> is the new text in grant's
form (module paths ...libreac.fuzz_grant.lib.Reusable), so a unit maps it like any grant file; OUT_DIR/depot.patch is the
unified diff (repo paths) of all files. Prints per file the hunks taken and kept.
--consumer: lib/A consumers (GRANT_REL/A/<F> the unit's relocated grant text, KNOCK_REL/A/<F> knock's text relocated
onto the unit's image by port_core): the same hunk rule; the output is the unit's file itself."""
import difflib, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from depot_classify import norm_lines  # noqa: E402
from imgtop_rule import strip_imgtop_unfold  # noqa: E402

KMOD = re.compile(r'OssFuzzTheorems\.Proofs\.libreac\.fuzz_knock\.lib')
GREPO = 'proofs/libreac/fuzz_grant/lib/Reusable/'


def main():
    args = sys.argv[1:]
    sub, consumer, librepo = 'Reusable', False, 'proofs/reac-repacer/fuzz_wire/lib'
    if args and args[0] == '--consumer':
        sub, consumer, args = 'A', True, args[1:]
        if args[:1] == ['--sub']:
            sub, args = args[1], args[2:]
        if args[:1] == ['--lib-repo']:
            librepo, args = args[1], args[2:]
    grel, krel, tsv, out = args[:4]
    take_extra, merge, glue, expect = set(), {}, {}, {}
    imgtop = False
    args = args[4:]
    while args:
        if args[0] == '--take':
            f, h = args[1].split(':')
            take_extra.add((f, int(h)))
            args = args[2:]
        elif args[0] == '--imgtop-unfold':
            imgtop = True
            args = args[1:]
            continue
        elif args[0] in ('--merge', '--glue'):
            f, h, spec_ = args[1].split(':', 2)
            cnt_ = 1
            mm = re.match(r'^(.*)#(\d+)$', spec_)
            if mm:
                spec_, cnt_ = mm.group(1), int(mm.group(2))
            old, new = spec_.split('=>') if args[0] == '--glue' else spec_.split('=')
            expect[(f, int(h), old)] = cnt_
            (merge if args[0] == '--merge' else glue).setdefault((f, int(h)), []).append((old, new))
            args = args[2:]
        else:
            sys.exit('depot_apply: unknown argument %s' % args[0])
    cls = {}
    for line in open(tsv).read().splitlines()[1:]:
        p = line.split('\t')
        if len(p) >= 7 and p[1].isdigit():
            cls[(p[0], int(p[1]))] = p[2]
    files = sorted({f for f, _ in cls})
    os.makedirs(out, exist_ok=True)
    patch = []
    for f in files:
        gp = os.path.join(grel, sub, f)
        kp = os.path.join(krel, sub, f)
        gt, kt = open(gp).read(), open(kp).read()
        G, K = gt.split('\n'), kt.split('\n')
        gl, kl = norm_lines(gt), norm_lines(kt)
        ops = [o for o in difflib.SequenceMatcher(None, [l for _, l in gl], [l for _, l in kl], autojunk=False).get_opcodes()
               if o[0] != 'equal']
        edits, taken, kept, merged, glued, imgtop_hits = [], [], [], [], [], []
        for h, (tag, i1, i2, j1, j2) in enumerate(ops, 1):
            c = cls.get((f, h))
            if c is None:
                sys.exit('depot_apply: %s hunk %d is not in the table (the table is stale)' % (f, h))
            if not (c in ('depot', 'layout-grow') or (f, h) in take_extra or (f, h) in merge or (f, h) in glue):
                kept.append(h)
                continue
            taken.append(h)
            subs = merge.get((f, h), []) + glue.get((f, h), [])
            if merge.get((f, h)):
                merged.append('%d (%s)' % (h, ', '.join('%s -> %s' % s for s in merge[(f, h)])))
            if glue.get((f, h)):
                glued.append('%d (%s)' % (h, ', '.join('`%s` -> `%s`' % s for s in glue[(f, h)])))
            if i1 == i2:                                  # insertion after grant's line gl[i1-1]
                at = gl[i1 - 1][0] if i1 else 0
                k0 = (kl[j1 - 1][0] + 1) if j1 else 1      # with knock's comment / blank lines above the first line
                new = K[k0 - 1:kl[j2 - 1][0]]
                lo, hi = at, at                           # replace G[at:at] (0-based slice after line `at`)
            else:
                lo, hi = gl[i1][0] - 1, gl[i2 - 1][0]
                new = K[kl[j1][0] - 1:kl[j2 - 1][0]] if j1 < j2 else []
            for old_, new_ in subs:
                want = expect.get((f, h, old_), 1)
                if sum(x.count(old_) for x in new) != want:
                    sys.exit('depot_apply: --merge / --glue %s:%d: %s does not occur exactly %d time(s) in knock\'s lines'
                             % (f, h, old_, want))
                new = [x.replace(old_, new_) for x in new]
            if imgtop:
                joined, k_ = strip_imgtop_unfold('\n'.join(new))   # an `unfold` list may span lines
                if k_:
                    new = joined.split('\n')
                    imgtop_hits.append('%d (%d)' % (h, k_))
            edits.append((lo, hi, new))
        res = list(G)
        for a, b, new in sorted(edits, key=lambda e: (e[0], e[1]), reverse=True):
            res[a:b] = [KMOD.sub('OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib', x) for x in new]
        # no notice is written (stream lead's ruling: no lane writes a `Modified by` line; the hunk table, the merges, the
        # takes and the splits listed in the log are the record of what changed)
        if merged or glued or imgtop_hits:
            print('%s: merges %s; glue %s; YImgTop unfold splits %s' % (f, '; '.join(merged) or '-', '; '.join(glued) or '-',
                                                                       '; '.join(imgtop_hits) or '-'))
        txt = '\n'.join(res)
        open(os.path.join(out, f), 'w').write(txt)
        rp = ('%s/%s/' % (librepo, sub) if consumer else GREPO) + f
        patch += difflib.unified_diff(gt.splitlines(True), txt.splitlines(True), rp, rp, n=3)
        print('%s: %d hunks: taken %d, kept %d (%s)' % (f, len(ops), len(taken), len(kept), ' '.join(map(str, kept)) or '-'))
    open(os.path.join(out, 'depot.patch'), 'w').write(''.join(patch))


if __name__ == '__main__':
    main()
