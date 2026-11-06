#!/usr/bin/env python3
"""closure_strict2.py -- closure_strict.py 16537c22e6bc with the fixes of its review (REVIEW.md):
 - loads strictcmp2.py (strictcmp2's target pass; C-string rule ON by default, STRICT_LITERAL=1 turns it off);
 - every closure member is compared once per X ADDRESS (no verdict cache by bare function name), and its Y counterpart is
   found by symbol identity: the FUNC with the same qualified name (strictcmp2.qname: the name, or name{STT_FILE} when
   several symbols carry it). A member name that is ambiguous in X, or absent / ambiguous in Y, is reported, never
   replaced by the first symbol of that name;
 - every value / full-bytes / C-string acceptance of every member is printed: ACCEPT lines, and one strictcmp2 CSTR row
   per C-string acceptance (CSTR, function, pair, word offset, addr1, addr2, length, hex, repr);
 - function bytes that are not file-backed give strictcmp2's verdict UNREADABLE.
Original docstring: for each root function, its call closure in image X (direct jal / auipc+jalr call and tail-call
targets that start a FUNC symbol, followed transitively; register-indirect calls are counted, not followed), and a
same-name byte compare of every closure member against image Y. Read-only.
usage: [STRICT_LITERAL=1] closure_strict2.py X_ELF Y_ELF root1,root2,...   one summary row per root, then every member that
       is not EQUAL / EQUAL-mod-pcrel-with-all-targets-equal, then the acceptances."""
import sys, os
import importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('strictcmp2', os.path.join(HERE, 'strictcmp2.py'))
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
    b = dc.frd(X, a, z); out = set(); ind = 0
    if b is None: return out, ind
    w = bc_words(b); t = targets(a, b)
    for i, (o, x, n) in enumerate(w):
        if n != 4: continue
        op = x & 0x7f; rd = (x >> 7) & 31
        if op in (0x6f, 0x67) and i in t:
            tg = t[i][1]
            if X.sec(tg) == '.got':
                c8 = dc.frd(X, tg, 8); tg = int.from_bytes(c8, 'little') if c8 else -1
            if tg in starts and not (a <= tg < a + z):
                out.add(tg)
        elif op == 0x67 and rd != 0:
            ind += 1
    return out, ind

def member(a):
    """(name, size, qualified name or None): a name at a that is not duplicated, else the first name"""
    l = sorted(starts[a])
    n, z = next(((n, z) for n, z in l if n not in dupx), l[0])
    return n, z, dc.qname(X, n, a)

def ycounterpart(n, q):
    c = sorted({(v, z) for v, z, t in Y.byname.get(n, []) if t == 'STT_FUNC' and z > 0 and dc.qname(Y, n, v) == q})
    return (c[0], None) if len(c) == 1 else (None, 'ABSENT-in-Y' if not c else 'AMBIGUOUS-in-Y %s' % [hex(v) for v, z in c])

cache = {}
for r in roots:
    s = X.fsym(r)
    if not s:
        print('%s\tABSENT in X' % r); continue
    if r in dupx:
        print('%s\tAMBIGUOUS root name in X %s' % (r, [hex(v) for v, z, t in X.byname[r] if t == 'STT_FUNC' and z > 0])); continue
    seen = {s[0]}; work = [s[0]]; ind = 0
    while work:
        a = work.pop()
        z = starts[a][0][1]
        c, k = callees(a, z); ind += k
        for t in c:
            if t not in seen:
                seen.add(t); work.append(t)
    rows = {'EQUAL': 0, 'EQUAL-mod-pcrel': 0}; bad = []; accs = []
    for a in sorted(seen):
        n, z, q = member(a)
        if a not in cache:
            if q is None: cache[a] = ('AMBIGUOUS-NAME-in-X', None, [], None)
            else:
                ys, err = ycounterpart(n, q)
                if err: cache[a] = (err, None, [], None)
                elif ys[1] != z: cache[a] = ('SIZE %d vs %d' % (z, ys[1]), None, [], ys[0])
                else:
                    fb = []
                    v, cc, t3, diff = tcmp(I, 'X', a, 'Y', ys[0], z, fb)
                    cache[a] = (v + (' target-differ' if diff else ''), diff, fb, ys[0])
        v, diff, fb, ya = cache[a]
        if v in rows: rows[v] += 1
        else: bad.append((q or n, hex(a), v, (diff or [])[:2], 'DUP-NAME' if n in dupx else ''))
        if fb: accs.append((q or n, a, ya, fb))
    print('%s\tclosure %d functions (register-indirect call sites inside: %d)\tEQUAL %d\tEQUAL-mod-pcrel(all targets equal) %d'
          '\tother %d\tmembers with value / full-bytes / C-string acceptances %d'
          % (r, len(seen), ind, rows['EQUAL'], rows['EQUAL-mod-pcrel'], len(bad), len(accs)))
    for b in bad:
        print('   %s @%s: %s %s %s' % b)
    for n, a, ya, fb in accs:
        t = dc.fb_text(fb)
        if t: print('   ACCEPT %s @%#x/%#x: %s' % (n, a, ya, t))
        for row in dc.cstr_rows(n, 'X:Y', fb): print(row)
