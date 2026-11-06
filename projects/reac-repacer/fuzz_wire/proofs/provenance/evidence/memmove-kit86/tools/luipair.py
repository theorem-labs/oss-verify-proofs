#!/usr/bin/env python3
"""luipair.py -- the kit 86da41d3ef68 FAIL-OPEN #3 check (registry 91ef6306668): TWO lui values combined by
add / sub / sh{1,2,3}add into ONE load / store / jalr / AMO base are not compared as an address by strictcmp3 (each lui
is judged alone, so `lui; lui; add; ld` on two different objects can read EQUAL-mod-pcrel with exposure 0).

For every compared function pair (the closure members and the paircl pairs of this record) whose luiscan `luis` count is
>= 2 in either image, this runs luitrace's expression dataflow over the X function and reports every memory / jump base
whose value holds TWO OR MORE lui words. For each such site the combined target is computed on BOTH images (each lui
and each immediate taken from that image's own words) and named by the kit's naming (strictcmp3.qres / atname):
`EQUAL` only when both sides name the same symbol + offset.
usage: luipair.py KITDIR X_ELF Y_PIN Y_TWIN CLOSURE_OUT PAIRCL_TSV OUT"""
import sys, os, re, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import luitrace as LT

kit, xe, ype, yte, clf, pct, out = sys.argv[1:8]
s3 = LT.load_kit(kit)
from elftools.elf.elffile import ELFFile
X, YT, YP = s3.Img(xe), s3.Img(yte), s3.Img(yte)
segs = [(g['p_vaddr'], g['p_filesz'], g['p_memsz'], g.data()) for g in ELFFile(open(ype, 'rb')).iter_segments()
        if g['p_type'] == 'PT_LOAD']
YP.segs = [(v, fz, d) for v, fz, mz, d in segs]

starts = {}
for v, z, n, t in X.syms:
    if t == 'STT_FUNC' and z > 0: starts.setdefault(v, []).append((n, z))
dupx = {n for n, l in X.byname.items() if len([e for e in l if e[2] == 'STT_FUNC' and e[1] > 0]) > 1}


def member(a):
    l = sorted(starts[a]); n, z = next(((n, z) for n, z in l if n not in dupx), l[0])
    return n, z, s3.qname(X, n, a)


# the compare set: every closure member (by X address, Y by qualified name in the twin) and every paircl pair
# the closure is walked here exactly as closure_strict3 walks it (direct jal / auipc+jalr / .got call targets that
# start a sized FUNC, transitively); the closure output is read only for its member count
pairs = collections.OrderedDict()
targets, bc_words = s3._g['targets'], s3.bc_words


def callees(a, z):
    b = s3.frd(X, a, z); outc = set()
    if b is None: return outc
    w = bc_words(b); t = targets(a, b)
    for i, (o, x, n) in enumerate(w):
        if n != 4: continue
        op = x & 0x7f
        if op in (0x6f, 0x67) and i in t:
            tg = t[i][1]
            if X.sec(tg) == '.got':
                c8 = s3.frd(X, tg, 8); tg = int.from_bytes(c8, 'little') if c8 else -1
            if tg in starts and not (a <= tg < a + z): outc.add(tg)
    return outc


root = s3.fcopies(X, '__asan_memmove')[0]
seen = {root[0]}; work = [root[0]]
while work:
    a = work.pop(); z = starts[a][0][1]
    for t in callees(a, z):
        if t not in seen: seen.add(t); work.append(t)
for a in sorted(seen):
    n, z, q = member(a)
    c = sorted({(v, zz) for v, zz, t in YT.byname.get(n, []) if t == 'STT_FUNC' and zz > 0 and s3.qname(YT, n, v) == q})
    if len(c) == 1 and c[0][1] == z: pairs[('closure', a)] = (q or n, a, c[0][0], z, 'twin')
# the paircl pair set, walked exactly as paircl.py walks it (paircl.py:72-96 without the compare): the i-th pc-relative
# target of X is paired with the i-th of Y; a pair whose X target starts a sized FUNC is followed
ya0 = int(os.environ.get('YROOT', '0'), 16)
if ya0:
    pair = {root[0]: ya0}; rev = {ya0: root[0]}; work = [root[0]]
    while work:
        xa = work.pop(); yb = pair[xa]; z = starts[xa][0][1]
        bx, by = s3.frd(X, xa, z), s3.frd(YP, yb, z)
        if bx is None or by is None: continue
        tx, ty = targets(xa, bx), targets(yb, by)
        for i in sorted(set(tx) & set(ty)):
            ax, ay = tx[i][1], ty[i][1]
            if X.sec(ax) == YP.sec(ay) == '.got':
                cx, cy = s3.frd(X, ax, 8), s3.frd(YP, ay, 8)
                if cx is None or cy is None: continue
                ax, ay = int.from_bytes(cx, 'little'), int.from_bytes(cy, 'little')
            if ax in starts and ax not in pair and ay not in rev and not (xa <= ax < xa + z):
                pair[ax] = ay; rev[ay] = ax; work.append(ax)
    for xa, ya in pair.items():
        pairs[('paircl', xa)] = (member(xa)[2] or member(xa)[0], xa, ya, starts[xa][0][1], 'pin')
ntsv = len({ln.split('\t')[1] for ln in open(pct).read().splitlines()[1:]})

def precise_luis(e, w):
    """the lui words an expression holds EXACTLY (a widened node 'T' is not a precise hold)"""
    t = e[0]
    if t == 'L': return {e[1]} if w[e[1]][1] & 0x7f == 0x37 else set()
    if t == 'op': return precise_luis(e[2], w) | precise_luis(e[3], w)
    return set()


rows = []; nfun = 0; nmulti = 0; widened = []; npairs = 0; luidiff = []
for key, (nm, xa, ya, z, which) in pairs.items():
    IY = YT if which == 'twin' else YP
    bx, by = s3.frd(X, xa, z), s3.frd(IY, ya, z)
    if bx is None or by is None: continue
    wx = bc_words(bx)
    wy = bc_words(by)
    nl = sum(1 for o, x, n in wx if n == 4 and x & 0x7f == 0x37 and (x >> 7) & 31)
    npairs += 1
    if len(wx) == len(wy):
        d = [hex(o) for (o, x, n), (oy, y, ny) in zip(wx, wy) if n == 4 and x & 0x7f == 0x37 and x != y]
        if d: luidiff.append((which, nm, hex(xa), ','.join(d)))
    else: luidiff.append((which, nm, hex(xa), 'word count differs'))
    if nl < 2: continue
    nfun += 1
    FX, FY = LT.Fn(s3, bx, xa), LT.Fn(s3, by, ya)
    if FX.parcels:
        rows.append((which, nm, hex(xa), '-', 'SKIP', 'the function holds 2-byte parcels: rule 8 does not follow registers through them (kit `unmeasured`)'))
        continue
    FX.run()
    for i, (o, x, n) in enumerate(wx):
        s = FX.ins[i]
        if s is None: continue
        for q, role, imm in FX.reads(i):
            if role != 'BASE': continue
            for e in s.get(q, frozenset()):
                ls = LT.luis_of(e)
                prec = precise_luis(e, wx)          # L leaves the expression holds exactly (not through a widening)
                wide = {j for j in ls if wx[j][1] & 0x7f == 0x37} - prec
                if len(prec) < 2:
                    if len(prec | wide) >= 2:
                        widened.append((which, nm, hex(xa), hex(o), 'auipc base' if LT.has_auipc(e) else 'no auipc leaf'))
                    continue
                nmulti += 1
                vx, vy = LT.evaluate(e, FX.w, xa), LT.evaluate(e, FY.w, ya)
                if vx is not None and vy is not None:
                    # every leaf is a lui / auipc / immediate: the base is an ABSOLUTE address; compare it by name
                    ax, ay = (vx + imm) & LT.M64, (vy + LT.rd_list_imm(FY.reads(i), q)) & LT.M64
                    nx, ny = LT.name(s3, X, ax), LT.name(s3, IY, ay)
                    v = 'ABS-EQUAL' if nx == ny and not nx.startswith('(') and nx != '?' else 'ABS-DIFFERS'
                    rows.append((which, nm, hex(xa), hex(o), v, '%s + %d -> X %#x=%s | Y %#x=%s' % (LT.show(e, wx), imm, ax, nx, ay, ny)))
                    continue
                # an unknown leaf (a load, an argument, a call result): the lui values are a DISPLACEMENT on it
                auipc = LT.has_auipc(e)
                eqwords = all(wx[j][1] == FY.w[j][1] for j in ls)
                v = 'DISP-AUIPC' if auipc else ('DISP-EQUAL-WORDS' if eqwords else 'DISP-WORD-DIFFERS')
                rows.append((which, nm, hex(xa), hex(o), v, '%s + %d; unknown leaves: %s; lui / immediate words equal in X and Y: %s'
                             % (LT.show(e, wx), imm, ', '.join(sorted({LT.show(u, wx) for u in LT.leaves_unknown(e)})), eqwords)))
with open(out, 'w') as f:
    f.write('# luipair (kit FAIL-OPEN #3): X %s, Y twin %s, Y pin %s; compared function pairs with >= 2 lui words: %d;\n'
            '# memory / jump bases holding two or more lui values: %d\n' % (s3.sha(xe)[:12], s3.sha(yte)[:12], s3.sha(ype)[:12], nfun, nmulti))
    f.write('# function pairs compared here: %d; pairs in which ANY lui word differs between X and Y: %d %s\n'
            % (npairs, len(luidiff), luidiff if luidiff else ''))
    f.write('# bases whose value holds two or more lui values only through a WIDENED node (the dataflow joined several\n'
            '# values into one, so the lui set is an over-approximation; each row says whether the base is auipc-derived): %d\n' % len(set(widened)))
    for r in sorted(set(widened)): f.write('WIDENED\t%s\t%s\t%s\t%s\t%s\n' % r)
    f.write('run\tfunction\tX fn\tword offset\tverdict\tdetail\n')
    for r in rows: f.write('\t'.join(r) + '\n')
print('# luipair: %d pairs compared, lui words differ in %d of them; %d pairs with >= 2 luis; %d bases hold two or more '
      'lui values exactly (%s); %d more only through a widened node'
      % (npairs, len(luidiff), nfun, nmulti, dict(collections.Counter(r[4] for r in rows)) or 'none', len(set(widened))))
