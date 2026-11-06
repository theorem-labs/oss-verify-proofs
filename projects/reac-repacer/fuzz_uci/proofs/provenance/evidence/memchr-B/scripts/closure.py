#!/usr/bin/env python3
"""closure.py -- for each root function, its call closure in image X (direct jal / auipc+jalr call and tail-call
targets that start a FUNC symbol, followed transitively; register-indirect calls are counted, not followed), and a
same-name byte compare of every closure member against image Y with drvcmp.py's tcmp (bytecmp 7daa0e2a03d9 + repin_check
9cbc3553c09e target pass). Read-only.
usage: closure.py X_ELF Y_ELF root1,root2,...      prints one summary row per root and every member that is not
EQUAL / EQUAL-mod-pcrel-with-all-targets-equal."""
import sys, os
import importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('drvcmp', os.path.join(HERE, 'drvcmp.py'))
dc = importlib.util.module_from_spec(spec); spec.loader.exec_module(dc)
Img, targets, bc_words, tcmp = dc.Img, dc._g['targets'], dc.bc_words, dc.tcmp
X, Y = Img(sys.argv[1]), Img(sys.argv[2])
I = {'X': X, 'Y': Y}
roots = sys.argv[3].split(',')
starts = {}
for v, z, n, t in X.syms:
    if t == 'STT_FUNC' and z > 0:
        starts.setdefault(v, []).append((n, z))
dupx = {n for n, l in X.byname.items() if len([e for e in l if e[2] == 'STT_FUNC' and e[1] > 0]) > 1}
def callees(a, z):
    b = X.rd(a, z); w = bc_words(b); t = targets(a, b); out = set(); ind = 0
    for i, (o, x, n) in enumerate(w):
        if n != 4: continue
        op = x & 0x7f; rd = (x >> 7) & 31
        if op in (0x6f, 0x67) and i in t:
            tg = t[i][1]
            if X.sec(tg) == '.got':
                tg = int.from_bytes(X.rd(tg, 8), 'little')
            if tg in starts and not (a <= tg < a + z):
                out.add(tg)
        elif op == 0x67 and rd != 0:
            ind += 1
    return out, ind
cache = {}
for r in roots:
    s = X.fsym(r)
    if not s:
        print('%s\tABSENT in X' % r); continue
    seen = {s[0]}; work = [s[0]]; ind = 0
    while work:
        a = work.pop()
        z = starts[a][0][1]
        c, k = callees(a, z); ind += k
        for t in c:
            if t not in seen:
                seen.add(t); work.append(t)
    rows = {'EQUAL': 0, 'EQUAL-mod-pcrel': 0}; bad = []
    for a in sorted(seen):
        n, z = starts[a][0]
        if n not in cache:
            ys = Y.fsym(n)
            if not ys: cache[n] = ('ABSENT-in-Y', None)
            elif ys[1] != z: cache[n] = ('SIZE %d vs %d' % (z, ys[1]), None)
            else:
                v, cc, t3, diff = tcmp(I, 'X', a, 'Y', ys[0], z)
                cache[n] = (v + (' target-differ' if diff else ''), diff)
        v = cache[n][0]
        if v in rows: rows[v] += 1
        else: bad.append((n, hex(a), v, (cache[n][1] or [])[:2], 'DUP-NAME' if n in dupx else ''))
    print('%s\tclosure %d functions (register-indirect call sites inside: %d)\tEQUAL %d\tEQUAL-mod-pcrel(all targets equal) %d\tother %d'
          % (r, len(seen), ind, rows['EQUAL'], rows['EQUAL-mod-pcrel'], len(bad)))
    for b in bad:
        print('   %s @%s: %s %s %s' % b)
