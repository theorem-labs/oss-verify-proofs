#!/usr/bin/env python3
"""dupaddr.py -- BY-ADDRESS check of every closure member whose name has more than one symtab entry (dupnames.py).
For each such member at X address a:
  - callers: every closure member whose code calls a (the closure script's own callees(), i.e. the jal / auipc+jalr target);
  - the Y copy the CODE calls: for each caller, its Y counterpart (the closure's member() / ycounterpart(), by
    qualified name), then that Y caller's callees() restricted to the copies of the same name;
  - the Y copy the closure chose (qualified name name{STT_FILE});
  - the by-address compare: the kit's own tcmp(I, 'X', a, 'Y', y, size, fb) on the code-called pair.
Also tallies the whole union closure by the kit's own per-member rules (EQUAL / EQUAL-mod-pcrel all targets
equal / other). usage: dupaddr.py"""
import collections, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common
HERE = common.HERE
X_ELF, Y_ELF = common.CGIF_B_TWIN, common.DECODE_B_TWIN
FNS = [l.strip() for l in open(os.path.join(HERE, 'out', 'FNLIST8.txt')) if l.strip()]


def callees_in(dc, IMG, st, a, z):
    """the closure script's callees(), on image IMG with FUNC starts st (the same code, X and starts replaced)"""
    b = dc.frd(IMG, a, z); out = set()
    if b is None:
        return out
    w = dc.bc_words(b); t = dc._g['targets'](a, b)
    for i, (o, x, n) in enumerate(w):
        if n != 4:
            continue
        op = x & 0x7f
        if op in (0x6f, 0x67) and i in t:
            tg = t[i][1]
            if IMG.sec(tg) == '.got':
                c8 = dc.frd(IMG, tg, 8); tg = int.from_bytes(c8, 'little') if c8 else -1
            if tg in st and not (a <= tg < a + z):
                out.add(tg)
    return out


def main():
    g = common.closure_globals(FNS)
    X, Y, starts, callees, member, ycp, tcmp, I = g['X'], g['Y'], g['starts'], g['callees'], g['member'], \
        g['ycounterpart'], g['tcmp'], g['I']
    # Y-side starts (address -> [(name, size)]) for Y callees()
    ystarts = collections.defaultdict(list)
    for n, l in Y.byname.items():
        for v, z, t in l:
            if t == 'STT_FUNC' and z > 0:
                ystarts[v].append((n, z))
    seen, calls = set(), collections.defaultdict(set)
    for r in FNS:
        s = X.fsym(r)
        work = [s[0]]; seen.add(s[0])
        while work:
            a = work.pop()
            c, _ = callees(a, starts[a][0][1])
            for t in c:
                calls[t].add(a)
                if t not in seen:
                    seen.add(t); work.append(t)
    tally, other = collections.Counter(), []
    dup_rows = []
    for a in sorted(seen):
        n, z, q = member(a)
        if q is None:
            tally['AMBIGUOUS-NAME-in-X'] += 1; other.append((n, a, 'AMBIGUOUS-NAME-in-X')); continue
        ys, err = ycp(n, q)
        if err:
            tally[err.split(' ')[0]] += 1; other.append((n, a, err)); continue
        if ys[1] != z:
            tally['SIZE'] += 1; other.append((n, a, 'SIZE')); continue
        fb = []
        v, cc, t3, diff = tcmp(I, 'X', a, 'Y', ys[0], z, fb)
        k = g['dc'].verdict(v, diff)                       # the kit's combined verdict (words and targets)
        tally[k] += 1
        if n in g['dupx'] or len([1 for vv, zz, tt in Y.byname.get(n, []) if tt == 'STT_FUNC' and zz > 0]) > 1:
            ycopies = {vv for vv, zz, tt in Y.byname[n] if tt == 'STT_FUNC' and zz > 0}
            called = set()
            for c in sorted(calls[a]):
                cn, cz, cq = member(c)
                cy, cerr = ycp(cn, cq) if cq else (None, 'AMBIGUOUS')
                if cerr:
                    called.add('caller %s %s' % (cn[:40], cerr)); continue
                yt = callees_in(g['dc'], Y, ystarts, cy[0], cy[1])
                called.add((cn, '%#x' % c, '%#x' % cy[0], tuple('%#x' % t for t in sorted(t for t in yt if t in ycopies))))
            dup_rows.append((n, q, a, ys[0], k, called))
    print('union closure: %d members; %s' % (len(seen), dict(tally)))
    for n, a, e in other:
        print('  other: %s @%#x %s' % (n[:70], a, e))
    for n, q, a, y, k, called in dup_rows:
        print('DUP %s\tX %#x\tY(by qualified name) %#x\tverdict %s' % (q, a, y, k))
        for c in sorted(called, key=str):
            print('    called from %s' % (c,))


if __name__ == '__main__':
    main()
