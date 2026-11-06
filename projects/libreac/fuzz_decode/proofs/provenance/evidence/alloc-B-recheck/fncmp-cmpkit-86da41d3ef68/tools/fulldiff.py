#!/usr/bin/env python3
"""fulldiff.py -- the FULL differing-target list of every closure member the closure script REPORTED, from the kit's own
tcmp (strictcmp3), never from printed output. Functions: out/closure-reported.txt (name, X address; Allocator::Allocate,
the one reported root, is among them). Each is compared BY ADDRESS: X = its address in the cgif-B twin, Y = the closure's
own counterpart (member() / ycounterpart(): the FUNC with the same qualified name). Every diff entry is then:
  - kind `lui-in-section` (a lui-built absolute value inside a section, rule 8): settlement LUI, settled per target by
    the lui trace (tools/luitrace.py, scans/luitrace.tsv) and its class (RECORD.md 4g);
  - kind `unmeasured` / `one-side` / `unreadable`: LISTED with its kind (none expected);
  - any other kind: settled by settle.measure() at those addresses.
Writes out/fulldiff.tsv (one row per diff entry) and prints the counts. usage: fulldiff.py"""
import collections, importlib.util, os, sys
TOOLS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLS)
import common
ALLOC = '_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb'


def main():
    g = common.closure_globals([ALLOC])
    X, Y, I, tcmp, member, ycp = g['X'], g['Y'], g['I'], g['tcmp'], g['member'], g['ycounterpart']
    sp = importlib.util.spec_from_file_location('settle', os.path.join(TOOLS, 'settle.py'))
    st = importlib.util.module_from_spec(sp); sp.loader.exec_module(st)
    C, D = st.sc.Img(common.CGIF_B_TWIN), st.sc.Img(common.DECODE_B_TWIN)
    fns = []
    for l in open(os.path.join(common.OUT, common.REPORTED)):
        if not l.strip():
            continue
        n0, ax = l.rstrip('\n').split('\t')
        a = int(ax, 16)
        n, z, q = member(a)
        assert n == n0, (n, n0)
        ys, err = ycp(n, q)
        assert not err and ys[1] == z, (n, err)
        fns.append((n, a, z, ys[0]))
    rows, per, kinds, settled = [], {}, collections.Counter(), collections.Counter()
    for n, a, z, y in fns:
        v, c, t3, diff = tcmp(I, 'X', a, 'Y', y, z, [])
        per[n] = len(diff)
        for off, r1, r2, kind, info in diff:
            kinds[kind] += 1
            o = int(off, 16)
            if kind in ('unmeasured', 'one-side', 'unreadable'):
                s, why, tc, td = 'LISTED-' + kind.upper(), '%s %s' % (r1, r2), None, None
            elif kind == 'lui-in-section':
                s, why = 'LUI', '%s | %s (settled by the lui trace)' % (r1, r2)
                tc = td = None
            else:
                s, why, tc, td = st.measure(C, D, n, o, (a, z), (y, z))
            settled[s] += 1
            rows.append((n, '%#x' % a, '%#x' % y, off, kind, s, '%#x' % tc if tc else '-', '%#x' % td if td else '-',
                         str(why)[:300]))
    with open(os.path.join(common.OUT, 'fulldiff.tsv'), 'w') as f:
        f.write('function\tX addr\tY addr\tword\tkit kind\tsettlement\tX target\tY target\tmeasurement\n')
        for r in rows:
            f.write('\t'.join(r) + '\n')
    print('functions %d; differing targets in tcmp (full) %d' % (len(fns), sum(per.values())))
    print('kit kinds:', dict(sorted(kinds.items())))
    print('settlement:', dict(sorted(settled.items())))
    for r in rows:
        if r[5] == 'DIFFERS' or r[5].startswith('LISTED'):
            print('  %s %s %s %s %s' % (r[0][:60], r[3], r[4], r[5], r[8][:160]))


if __name__ == '__main__':
    main()
