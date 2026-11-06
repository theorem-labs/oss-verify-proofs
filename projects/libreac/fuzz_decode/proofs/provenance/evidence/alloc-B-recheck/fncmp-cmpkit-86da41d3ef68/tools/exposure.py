#!/usr/bin/env python3
"""exposure.py -- joins the exposure scan of cmpkit 86da41d3ef68 (luiscan.py 9ae61e4a0e01 --all over both images,
scans/luiscan-all.tsv) with every function this record compared: the 8 functions of section 1 and every member of their
call closure (786; the closure script's own callees() / member() / ycounterpart(), so each member is the X address
the closure compared and the Y copy it paired). Per member: the luiscan row of its X address in the cgif-B twin and of
its Y counterpart in the decode-B twin, and EXPOSED when `exposure` > 0 in either (rule 8 of strictcmp3: a lui-built
absolute value that the earlier compare strictcmp2 compared raw). Writes scans/exposure.tsv; prints the counts and every
EXPOSED member.
usage: exposure.py"""
import collections, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common

LUI = os.path.join(common.HERE, 'scans', 'luiscan-all.tsv')
COLS = ['luis', 'insec', 'inload', 'memfed', 'memfed_out', 'luiconst', 'unmeasured', 'exposure']


def main():
    fns = [l.strip() for l in open(os.path.join(common.OUT, 'FNLIST8.txt')) if l.strip()]
    g = common.closure_globals(fns)
    X, Y, starts, callees, member, ycp = g['X'], g['Y'], g['starts'], g['callees'], g['member'], g['ycounterpart']
    seen = set()
    for r in fns:
        s = X.fsym(r)
        work = [s[0]]; seen.add(s[0])
        while work:
            a = work.pop()
            c, _ = callees(a, starts[a][0][1])
            for t in c:
                if t not in seen:
                    seen.add(t); work.append(t)
    rows = collections.defaultdict(dict)                 # image basename -> addr -> row
    for l in open(LUI):
        c = l.rstrip('\n').split('\t')
        if c[0] == 'ROW' and c[3] != 'addr':
            rows[c[1]][int(c[3], 16)] = dict(zip(COLS, (int(x) for x in c[5:13])), name=c[2], size=int(c[4]))
    xi, yi = os.path.basename(common.CGIF_B_TWIN), os.path.basename(common.DECODE_B_TWIN)
    out, exposed = [], []
    for a in sorted(seen):
        n, z, q = member(a)
        ys, err = ycp(n, q) if q else (None, 'AMBIGUOUS-NAME-in-X')
        rx = rows[xi].get(a)
        ry = rows[yi].get(ys[0]) if ys else None
        ex = (rx['exposure'] if rx else -1, ry['exposure'] if ry else -1)
        flag = 'EXPOSED' if max(ex) > 0 else ('no-row' if min(ex) < 0 else 'exposure 0 in both')
        rec = (q or n, '%#x' % a, '%#x' % ys[0] if ys else (err or '-'), str(z),
               ' '.join('%s=%d' % (k, rx[k]) for k in COLS) if rx else '-',
               ' '.join('%s=%d' % (k, ry[k]) for k in COLS) if ry else '-', flag)
        out.append(rec)
        if flag != 'exposure 0 in both':
            exposed.append(rec)
    with open(os.path.join(common.HERE, 'scans', 'exposure.tsv'), 'w') as f:
        f.write('member (qualified)\tX addr (cgif B)\tY addr (decode B)\tsize\tluiscan X\tluiscan Y\tresult\n')
        for r in out:
            f.write('\t'.join(r) + '\n')
    c = collections.Counter(r[6] for r in out)
    print('closure members %d (the 8 roots included): %s' % (len(out), dict(c)))
    for r in exposed:
        print('  %s X %s Y %s | X %s | Y %s' % (r[0][:90], r[1], r[2], r[4], r[5]))


if __name__ == '__main__':
    main()
