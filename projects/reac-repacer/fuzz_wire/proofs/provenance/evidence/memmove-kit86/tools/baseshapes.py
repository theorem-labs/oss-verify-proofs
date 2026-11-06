#!/usr/bin/env python3
"""baseshapes.py -- the kit 86da41d3ef68 known fail-opens (registry 7f2e3c70626): an EQUAL / EQUAL-mod-pcrel verdict is
not evidence where an address value reaches a load / store / jalr / AMO base through a shape the kit's target rule does
not compare. This scans EVERY compared function pair of the record (the closure members and the paircl pairs, walked as
closure_strict3 and paircl walk them) and reports, per memory / jump base, which of these shapes built it and what the
combined target is on BOTH images, named by the kit's naming (symbol + offset):

  (a) IMM        the load / store immediate: the target is the base VALUE + imm, computed as one address
  (b) ADDI       an addi / addiw chain on the value
  (c) LOGICAL    ori / xori / slli (and the other logical / shift ops) on the value
  (d) SPILL-FP   the value went through a frame slot (followed), or through an FP register or a CSR (NOT followed:
                 such a leaf makes the base RUNTIME, which this scan reports and never settles)
  (e) JT-ARM     the word is in a jump-table arm no decoded edge reaches (it is analysed with every value live at the
                 function's indirect jumps, as the kit's lui_scan does)
  (f) INFN-CALL  the base's value passed through a call this scan could not resolve to a sized FUNC (an in-function
                 callee, a register-indirect call): such a value is RUNTIME here
  (g) C.LUI      a compressed lui (the function holds 2-byte parcels; rule 8 does not follow registers through them)
  (h) NO-LUI     the constant part is built WITHOUT a lui: an auipc, or arithmetic on immediates only

Verdicts per base: ADDRESS-EQUAL / ADDRESS-DIFFERS (every leaf known: the full address, both images),
TERM-EQUAL / TERM-DIFFERS (an object address plus a runtime term: its constant part, both images), RUNTIME (no
constant part: a pointer from an argument, a load or a call), UNNAMED (an address neither image names).
A DIFFERS verdict is a REAL difference.
usage: baseshapes.py KITDIR X_ELF Y_PIN Y_TWIN YROOT OUT"""
import sys, os, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import luitrace as LT

kit, xe, ype, yte, yroot, out = sys.argv[1:7]
s3 = LT.load_kit(kit)
from elftools.elf.elffile import ELFFile
X, YT, YP = s3.Img(xe), s3.Img(yte), s3.Img(yte)
segs = [(g['p_vaddr'], g['p_filesz'], g['p_memsz'], g.data()) for g in ELFFile(open(ype, 'rb')).iter_segments()
        if g['p_type'] == 'PT_LOAD']
YP.segs = [(v, fz, d) for v, fz, mz, d in segs]
targets, bc_words = s3._g['targets'], s3.bc_words

starts = {}
for v, z, n, t in X.syms:
    if t == 'STT_FUNC' and z > 0: starts.setdefault(v, []).append((n, z))
dupx = {n for n, l in X.byname.items() if len([e for e in l if e[2] == 'STT_FUNC' and e[1] > 0]) > 1}


def member(a):
    l = sorted(starts[a]); n, z = next(((n, z) for n, z in l if n not in dupx), l[0])
    return s3.qname(X, n, a) or n, z


def callees(a, z):
    b = s3.frd(X, a, z); o = set()
    if b is None: return o
    w = bc_words(b); t = targets(a, b)
    for i, (off, x, n) in enumerate(w):
        if n == 4 and (x & 0x7f) in (0x6f, 0x67) and i in t:
            tg = t[i][1]
            if X.sec(tg) == '.got':
                c8 = s3.frd(X, tg, 8); tg = int.from_bytes(c8, 'little') if c8 else -1
            if tg in starts and not (a <= tg < a + z): o.add(tg)
    return o


root = s3.fcopies(X, '__asan_memmove')[0]
seen = {root[0]}; work = [root[0]]
while work:
    a = work.pop()
    for t in callees(a, starts[a][0][1]):
        if t not in seen: seen.add(t); work.append(t)
pairs = collections.OrderedDict()
for a in sorted(seen):
    nm, z = member(a)
    c = sorted({(v, zz) for v, zz, t in YT.byname.get(nm.split('{')[0], []) if t == 'STT_FUNC' and zz > 0
                and s3.qname(YT, nm.split('{')[0], v) == s3.qname(X, nm.split('{')[0], a)})
    if len(c) == 1 and c[0][1] == z: pairs[('closure', a)] = (nm, a, c[0][0], z, YT)
ya0 = int(yroot, 16)
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
    pairs[('paircl', xa)] = (member(xa)[0], xa, ya, starts[xa][0][1], YP)

LOGICAL_OPS = ('and', 'or', 'xor', 'sll', 'srl', 'sra', 'andn', 'orn', 'xnor', 'slli', 'srli', 'srai', 'andi', 'ori',
               'xori', 'slliw', 'srliw', 'sraiw', 'sllw', 'srlw', 'sraw', 'mul', 'mulw', 'div', 'divu', 'rem', 'remu')


def ops_in(e, acc):
    if e[0] == 'op':
        acc.add(e[1]); ops_in(e[2], acc); ops_in(e[3], acc)
    return acc


def is_clui(x, n):
    return n == 2 and (x & 3) == 1 and ((x >> 13) & 7) == 3 and ((x >> 7) & 31) not in (0, 2)


rows = []; shape = collections.Counter(); verdicts = collections.Counter(); nfun = 0; nbase = 0; clui = 0; parcelfn = 0
for key, (nm, xa, ya, z, IY) in pairs.items():
    run = key[0]
    bx, by = s3.frd(X, xa, z), s3.frd(IY, ya, z)
    if bx is None or by is None: continue
    nfun += 1
    wx = bc_words(bx)
    nc = sum(1 for o, x, n in wx if is_clui(x, n))
    if any(n == 2 for o, x, n in wx):
        parcelfn += 1; clui += nc
        rows.append((run, nm, hex(xa), '-', 'C.LUI' if nc else 'PARCELS', 'RUNTIME',
                     'the function holds %d 2-byte parcel(s) (%d of them c.lui): rule 8 and this trace do not follow '
                     'registers through them; every lui row of such a function is NOT CERTIFIED' % (sum(1 for o, x, n in wx if n == 2), nc)))
        shape['(g) C.LUI'] += 1
        continue
    FX, FY = LT.Fn(s3, bx, xa), LT.Fn(s3, by, ya)
    try:
        FX.run()
    except LT.NoFixpoint as e:
        rows.append((run, nm, hex(xa), '-', 'NOT-ANALYSED', 'RUNTIME', str(e) + ': every base of this function is left unsettled here'))
        shape['(not analysed: no fixpoint)'] += 1
        continue
    reach = set(); st = [0]
    while st:
        i = st.pop()
        if i in reach: continue
        reach.add(i)
        st += FX.succ[i]
    for i, (o, x, n) in enumerate(wx):
        s = FX.ins[i]
        if s is None: continue
        for q, role, imm in FX.reads(i):
            if role != 'BASE': continue
            nbase += 1
            es = sorted(s.get(q, frozenset()), key=str)
            if not es: continue
            sh = set()
            if imm: sh.add('(a) IMM')
            if i not in reach: sh.add('(e) JT-ARM')
            vx = vy = None; cpart = []; runt = set(); allknown = True
            for e in es:
                opset = ops_in(e, set())
                if opset & {'add', 'addi', 'addiw', 'sub', 'subw'}: sh.add('(b) ADDI')
                if opset & set(LOGICAL_OPS): sh.add('(c) LOGICAL')
                lv = {LT.show(u, wx) for u in LT.leaves_unknown(e)}
                if any(t.startswith(('fp@', 'csr@')) for t in lv): sh.add('(d) SPILL-FP')
                if any(t.startswith('ret@') for t in lv): sh.add('(f) INFN-CALL')
                if LT.has_auipc(e) and not any(wx[j][1] & 0x7f == 0x37 for j in LT.luis_of(e)): sh.add('(h) NO-LUI')
                cs, us = LT.split_terms(e)
                runt |= {LT.show(u, wx) for sg, u in us}
                if us: allknown = False
                cpart.append((cs, us))
            if 'slot' in str(es): sh.add('(d) SPILL-FP')
            names = set(); det = []
            for (cs, us), e in zip(cpart, es):
                if not cs:
                    names.add('RUNTIME'); continue
                ax = ay = 0; ok = True
                for sg, c in cs:
                    ex, ey = LT.evaluate(c, FX.w, xa), LT.evaluate(c, FY.w, ya)
                    if ex is None or ey is None: ok = False; break
                    ax += sg * ex; ay += sg * ey
                if not ok:
                    names.add('RUNTIME'); continue
                if not LT.has_auipc(e):
                    names.add('OFFSET'); continue   # a lui-only constant is a struct offset, not an address of this
                                                    # image: the lui row's own class settles it, naming it would be
                                                    # reading a number as an address
                ax = (ax + imm) & LT.M64; ay = (ay + LT.rd_list_imm(FY.reads(i), q)) & LT.M64
                nx, ny = LT.name(s3, X, ax), LT.name(s3, IY, ay)
                det.append('%#x=%s | %#x=%s%s' % (ax, nx, ay, ny, '' if not us else ' + runtime term'))
                names.add('EQUAL' if nx == ny and not nx.startswith('(') and nx != '?' else
                          'UNNAMED' if nx == ny else 'DIFFERS')
            v = ('ADDRESS-DIFFERS' if 'DIFFERS' in names else
                 'OFFSET-ON-POINTER' if names and names <= {'OFFSET', 'RUNTIME'} and 'OFFSET' in names else
                 'RUNTIME' if names == {'RUNTIME'} else
                 'UNNAMED' if 'UNNAMED' in names else
                 ('ADDRESS-EQUAL' if allknown else 'TERM-EQUAL'))
            if 'DIFFERS' in names and not allknown: v = 'TERM-DIFFERS'
            verdicts[v] += 1
            for t in sh: shape[t] += 1
            if not sh: shape['(none: a plain lo12 pair or a pointer)'] += 1
            if v in ('ADDRESS-DIFFERS', 'TERM-DIFFERS') or 'DIFFERS' in names:
                rows.append((run, nm, hex(xa), hex(o), '+'.join(sorted(sh)) or '-', v, '; '.join(det)))
            elif v in ('ADDRESS-EQUAL', 'TERM-EQUAL', 'UNNAMED'):
                rows.append((run, nm, hex(xa), hex(o), '+'.join(sorted(sh)) or '-', v,
                             '; '.join(det) + ('; runtime terms: ' + ', '.join(sorted(runt)) if runt else '')))
with open(out, 'w') as f:
    f.write('# baseshapes (kit known fail-opens, registry 7f2e3c70626): X %s, Y twin %s, Y pin %s\n'
            % (s3.sha(xe)[:12], s3.sha(yte)[:12], s3.sha(ype)[:12]))
    f.write('# function pairs scanned %d; memory / jump bases %d; functions with 2-byte parcels %d (c.lui words %d)\n'
            % (nfun, nbase, parcelfn, clui))
    f.write('# shapes: %s\n' % '; '.join('%s %d' % kv for kv in sorted(shape.items())))
    f.write('# verdicts: %s\n' % '; '.join('%s %d' % kv for kv in sorted(verdicts.items())))
    f.write('run\tfunction\tX fn\tword offset\tshapes\tverdict\tdetail\n')
    for r in rows: f.write('\t'.join(r) + '\n')
print('# baseshapes: pairs %d, bases %d, parcel functions %d (c.lui %d)' % (nfun, nbase, parcelfn, clui))
print('# shapes: %s' % dict(shape))
print('# verdicts: %s' % dict(verdicts))
