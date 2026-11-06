#!/usr/bin/env python3
"""dupcheck.py -- duplicate-name check for every function a record compares BY NAME. Read-only.

For each name it counts the .symtab entries carrying exactly that name (elftools, every symbol type) in X and in Y.
Names checked: the roots and extra names given on the command line (strictcmp2 cmp, settle.py and jtcheck look these up by
name), and every member of the by-name closure that closure_strict2 builds from the roots (it is rebuilt here the same
way: jal / auipc+jalr / .got call targets in X).
For a name with more than one entry in X or Y, it compares the copy the code calls, BY ADDRESS: the X copy is the
closure member's address; the Y copy is the target of the same call word in Y's counterpart of an X caller (the caller's
own Y address is found the same way, back to the root). The kit's tcmp gives the by-address verdict; the by-name verdict
is the one closure_strict2 computes (its Y copy: the one with the same name{STT_FILE}). One row per name; for a duplicated
name, one row per X copy in the closure, with both verdicts and both Y addresses.
usage: dupcheck.py X_ELF Y_ELF ROOT1,ROOT2,... [EXTRA1,EXTRA2,...]"""
import os, sys, collections, importlib.util
from elftools.elf.elffile import ELFFile
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('strictcmp2', os.path.join(HERE, 'strictcmp2.py'))
dc = importlib.util.module_from_spec(spec); spec.loader.exec_module(dc)
Img, targets, bc_words, tcmp = dc.Img, dc._g['targets'], dc.bc_words, dc.tcmp
xp, yp = sys.argv[1], sys.argv[2]
roots = sys.argv[3].split(',')
extra = [n for n in (sys.argv[4].split(',') if len(sys.argv) > 4 and sys.argv[4] else []) if n]
X, Y = Img(xp), Img(yp)
I = {'X': X, 'Y': Y}

def counts(p):
    c = collections.Counter(); f = collections.Counter()
    for s in ELFFile(open(p, 'rb')).get_section_by_name('.symtab').iter_symbols():
        if not s.name: continue
        c[s.name] += 1
        if s['st_info']['type'] == 'STT_FUNC' and s['st_size'] > 0: f[s.name] += 1
    return c, f
cx, fx = counts(xp); cy, fy = counts(yp)

def starts_of(Im):
    st = {}
    for v, z, n, t in Im.syms:
        if t == 'STT_FUNC' and z > 0: st.setdefault(v, []).append((n, z))
    return st
SX, SY = starts_of(X), starts_of(Y)
dupx = {n for n, l in X.byname.items() if len([e for e in l if e[2] == 'STT_FUNC' and e[1] > 0]) > 1}

def calls(Im, st, a, z):
    """{word index: callee start} for the jal / auipc+jalr / .got calls of the function at a (closure_strict2's rule)"""
    b = dc.frd(Im, a, z); out = {}
    if b is None: return out
    w = bc_words(b); t = targets(a, b)
    for i, (o, x, n) in enumerate(w):
        if n != 4: continue
        op = x & 0x7f
        if op in (0x6f, 0x67) and i in t:
            tg = t[i][1]
            if Im.sec(tg) == '.got':
                c8 = dc.frd(Im, tg, 8); tg = int.from_bytes(c8, 'little') if c8 else -1
            if tg in st and not (a <= tg < a + z): out[i] = tg
    return out

def member(a):
    l = sorted(SX[a]); n, z = next(((n, z) for n, z in l if n not in dupx), l[0])
    return n, z, dc.qname(X, n, a)

def ycounterpart(n, q):
    c = sorted({(v, z) for v, z, t in Y.byname.get(n, []) if t == 'STT_FUNC' and z > 0 and dc.qname(Y, n, v) == q})
    return c[0] if len(c) == 1 else None

def verdict(a, ya, z):
    if ya is None: return 'no Y copy'
    zy = next((zz for n, zz in SY.get(ya, [])), None)
    if zy != z: return 'SIZE %s vs %s' % (z, zy)
    v, c, t3, diff = tcmp(I, 'X', a, 'Y', ya, z)
    return v + (' target-differ %d' % len(diff) if diff else '')

print('# X sha256 %s; Y sha256 %s; roots %s' % (dc.sha(xp)[:12], dc.sha(yp)[:12], ','.join(roots)))
print('name\tused as\tX entries (FUNC sized)\tY entries (FUNC sized)\tX copy\tY copy by name\tby-name verdict\tY copy the code calls (via caller)\tby-address verdict\tsame')
members = {}; parents = collections.defaultdict(list)
for r in roots:
    s = X.fsym(r)
    if not s: print('%s\troot\tABSENT in X' % r); continue
    seen = {s[0]}; work = [s[0]]
    while work:
        a = work.pop(); z = SX[a][0][1]
        for i, t in calls(X, SX, a, z).items():
            parents[t].append((a, i))
            if t not in seen: seen.add(t); work.append(t)
    for a in seen: members.setdefault(a, set()).add(r)
# Y address of each closure member, following the code: root by name (roots are checked unique below), then callees
yaddr = {}
for r in roots:
    s, sy = X.fsym(r), Y.fsym(r)
    if s and sy: yaddr[s[0]] = sy[0]
changed = True
while changed:
    changed = False
    for a in members:
        if a in yaddr: continue
        for p, i in parents[a]:
            if p in yaddr:
                zp = SX[p][0][1]; ty = calls(Y, SY, yaddr[p], zp).get(i)
                if ty is not None: yaddr[a] = ty; changed = True; break
ambiguous = 0; rows = []
def emit(n, use, a, z, q):
    global ambiguous
    nx, ny = cx.get(n, 0), cy.get(n, 0)
    dup = nx > 1 or ny > 1
    yn = ycounterpart(n, q) if q else None
    yn_a = yn[0] if yn else None
    vn = verdict(a, yn_a, z) if not dup or yn else ('AMBIGUOUS-NAME (closure_strict2 reports it, never EQUAL)' if q is None or yn is None else '')
    ya = yaddr.get(a)
    va = verdict(a, ya, z) if dup else '-'
    if dup: ambiguous += 1
    rows.append('%s\t%s\t%d (%d)\t%d (%d)\t%#x\t%s\t%s\t%s\t%s\t%s' % (
        q or n, use, nx, fx.get(n, 0), ny, fy.get(n, 0), a, hex(yn_a) if yn_a else '-', vn,
        hex(ya) if dup and ya else '-', va, ('yes' if (yn_a == ya and vn == va) else 'NO') if dup else '-'))
for a in sorted(members):
    n, z, q = member(a)
    for nn, zz in SX[a]:
        emit(nn, 'closure member' + (' (root)' if nn in roots else ''), a, zz, dc.qname(X, nn, a))
for n in extra:
    s = X.fsym(n)
    if not s: rows.append('%s\textra\tABSENT in X' % n); continue
    if s[0] in members: continue
    emit(n, 'extra (not in the closure)', s[0], s[1], dc.qname(X, n, s[0]))
print('\n'.join(rows))
print('# names compared by name: %d; with more than one .symtab entry in X or Y: %d' % (len(rows), ambiguous))
