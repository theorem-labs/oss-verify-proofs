#!/usr/bin/env python3
"""basecalc.py X_ELF Y_ELF JTCHECK_OUT   (KIT=<cmpkit 86da41d3ef68 dir>; read-only)

For every `strictcmp3 lui-in-section` row of jtcheck's output: every load / store / AMO / jalr whose BASE carries the
row's lui-built value (alone or as part of a sum), with the full base address rebuilt on BOTH images.

A forward walk over the same paths as luiuse.py (both sides of each branch, `j` and REL4 jump tables inside the function,
direct callees to depth 16 with the argument values (L ones and known K / A ones), 8-byte stack spills and reloads; a call ends the caller-saved
registers, an ecall a0 / a1) carries a VALUE per register, starting from the values every path from the function's entry gives the registers at
the row's word (pre_state; a call to a function with no ret and no jump out of its body has no fall-through):
 K(c)       a known constant c (li, lui, addi / addiw / add / sub / slli / shNadd of constants)
 A(a)       an image address a known at link time (auipc, plus known constants), `+idx` when a run-time value was added
 U(origin)  a run-time value (a load from memory that is not a constant pointer cell, a function argument, a call's
            result, anything not followed); an 8-byte load from .got / .data.rel.ro / .init_array / .fini_array at a
            known image address gives the cell's file value (cell)
and a flag L: the value was computed with the row's lui value (L values are the ones followed). A value without L that has
been through two or more arithmetic steps is widened to U; a value with L after six steps is widened too (K to U with
L; an image address A keeps its symbol + offset and becomes `+idx`), so loops on the value end. add / sub / addi /
slli / shNadd combine values exactly (K+K, A+K, A-K, A+U = A+idx, U+anything = U); every other operation on an L value
gives U with L.
At a base with an L value:
 IMAGE   A(a): the full address a + the access immediate, named by symbol + offset in each image (the object that
         contains it); EQUAL when both images give the same symbol + offset (`+idx`: the run-time index is added to that
         same symbol + offset in both images)
 ABS     K(c): the lui-built value used as an absolute address (named in each image; should not occur: luiuse.py's
         ADDRESS verdict)
 RUNTIME U: a run-time pointer plus the lui value; the pointer is not an image address (its origin is printed)
 JOIN     the other part is an image address on some path and something else on another (pre_state): not settled
Output: one row per (row, call chain, function, use offset, access kind) with the SET of full addresses (or run-time
origins) on each image; IMAGE EQUAL when the two sets are equal; SUMMARY counts. Exit 1 on an ABS row or an IMAGE row that
DIFFERs."""
import sys, os, re, importlib.util, collections
KIT = os.environ['KIT']
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('luiuse', os.path.join(HERE, 'luiuse.py'))
argv = sys.argv; sys.argv = [argv[0], argv[1], argv[2], os.devnull]
L = importlib.util.module_from_spec(spec); spec.loader.exec_module(L)
s3 = L.s3; sx = L.sx; M64 = 2 ** 64

def W(v):
    """widening: a value not computed with the lui value that has been through 2 or more arithmetic steps becomes U
    (loop counters / walking pointers would otherwise give unboundedly many states)"""
    if not v[2] and v[0] in ('K', 'A') and v[3] >= 2: return ('U', 'widened', False, 0)
    if v[2] and v[0] == 'K' and v[3] >= 6: return ('U', 'widened (loop on the lui value)', True, 0)
    if v[2] and v[0] == 'A' and v[3] >= 6: return ('A', (v[1][0], True), True, 6)
    return v

def comb(op, a, b):
    """a, b: (kind, data, L, g); op 'add' / 'sub'"""
    return W(_comb(op, a, b))

def _comb(op, a, b):
    la = a[2] or b[2]; g = max(a[3], b[3]) + 1
    for p, q in ((a, b), (b, a)):        # an L image address already widened absorbs further constants (`+idx`)
        if p[0] == 'A' and p[2] and p[3] >= 6 and p[1][1] and q[0] in ('K', 'U'): return ('A', p[1], True, 6)
    if a[0] == 'K' and b[0] == 'K': return ('K', (a[1] + b[1] if op == 'add' else a[1] - b[1]) % M64, la, g)
    if a[0] == 'A' and b[0] == 'K': return ('A', ((a[1][0] + b[1] if op == 'add' else a[1][0] - b[1]) % M64, a[1][1]), la, g)
    if a[0] == 'K' and b[0] == 'A' and op == 'add': return ('A', ((b[1][0] + a[1]) % M64, b[1][1]), la, g)
    if a[0] == 'A' and b[0] == 'U' and op == 'add': return ('A', (a[1][0], True), la, g)
    if a[0] == 'U' and b[0] == 'A' and op == 'add': return ('A', (b[1][0], True), la, g)
    if 'J' in (a[0], b[0]): return ('J', 'an image address on some path into the row word', la, 0)
    org = a[1] if a[0] == 'U' else b[1] if b[0] == 'U' else 'A%sA' % ('+' if op == 'add' else '-')
    return ('U', org, la, 0)

def name(I, a):
    for v, z, nm, t in I.syms:
        if z > 0 and v <= a < v + z: return '%s+%#x' % (nm, a - v)
    sec = next((nm for nm, v, z in I.secs if v <= a < v + z), None)
    return '(%s)%#x' % (sec, a) if sec else '%#x(no section)' % a

CONST_CELLS = ('.got', '.got.plt', '.data.rel.ro', '.init_array', '.fini_array')
def cell(M, b, imm, f3):
    """the value of an 8-byte load from a constant pointer cell: base b an image address (no run-time index) in .got /
    .data.rel.ro / .init_array / .fini_array (filled at link time in these static images); the file's 8 bytes there, an
    image address when they fall in a section, else a constant. Anything else: None (a run-time value)"""
    if b[0] != 'A' or b[1][1] or f3 != 3 or M.I is None: return None
    a = (b[1][0] + imm) % M64
    sec = next((nm for nm, v, z in M.I.secs if v <= a < v + z), None)
    if sec not in CONST_CELLS: return None
    raw = s3.frd(M.I, a, 8)
    if raw is None: return None
    v = int.from_bytes(raw, 'little')
    insec = any(s <= v < s + z for nm, s, z in M.I.secs)
    return ('A', (v, False), b[2], 0) if insec else ('K', v, b[2], 0)

NORET = {}
def noreturn(M, ta):
    """a callee that cannot return: no `ret`, no indirect jump and no jump out of it (a tail call) in its body, and
    every call it makes ... (only the local test: its own words). Its call site then has no fall-through edge."""
    if ta in NORET: return NORET[ta]
    if ta not in M.funcs: NORET[ta] = False; return False
    w, at = M.words(ta); r = w is not None and not any(n == 2 for o, x, n in w)
    if r:
        for o, x, n in w:
            op = x & 0x7f
            if op == 0x67 and (x >> 7) & 31 == 0: r = False; break
            if op == 0x6f and (x >> 7) & 31 == 0:
                t = o + sx(((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11 | ((x >> 21) & 0x3ff) << 1, 21)
                if t not in at: r = False; break
    NORET[ta] = r; return r

def pre_state(M, fa, i0):
    """the image addresses (A) and constants (K) the registers hold at word i0 on EVERY path from the function's entry
    (a forward dataflow; values that differ between paths, or that a path does not set, are dropped = run-time U)"""
    f = M.funcs[fa]; w, at = M.words(fa)
    succ = [list(s) for s in s3._succ(w)]
    for q, (o, x, n) in enumerate(w):
        if n == 4 and x & 0x7f == 0x67 and (x >> 7) & 31 == 0 and not s3._isret(x):
            succ[q] = succ[q] + [at[t] for t in (L.jtable(M, fa, w, q) or [])]
        if n == 4 and x & 0x7f == 0x6f and (x >> 7) & 31 == 1:
            t = o + sx(((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11 | ((x >> 21) & 0x3ff) << 1, 21)
            if noreturn(M, f[0] + t): succ[q] = [s for s in succ[q] if s != q + 1]
    def step(q, s):
        o, x, n = w[q]; out = dict(s)
        if n != 4: return {}
        op = x & 0x7f; rd = (x >> 7) & 31; rs1 = (x >> 15) & 31; rs2 = (x >> 20) & 31; f3 = (x >> 12) & 7
        def V(r): return ('K', 0, False, 0) if r == 0 else s.get(r, ('U', '', False, 0))
        if op == 0x37: out[rd] = ('K', (sx(x >> 12, 20) << 12) % M64, False, 0)
        elif op == 0x17: out[rd] = ('A', ((f[0] + o + (sx(x >> 12, 20) << 12)) % M64, False), False, 0)
        elif op in (0x13, 0x1b) and f3 == 0:
            r = comb('add', V(rs1), ('K', sx(x >> 20, 12) % M64, False, 0))
            if op == 0x1b: r = ('K', sx(r[1] & 0xffffffff, 32) % M64, False, r[3]) if r[0] == 'K' else ('U', '', False, 0)
            out[rd] = r
        elif op == 0x33 and f3 == 0 and (x >> 25) in (0, 0x20): out[rd] = comb('add' if (x >> 25) == 0 else 'sub', V(rs1), V(rs2))
        elif op == 0x03:
            k = ('S', sx(x >> 20, 12))
            r = s.get(k) if rs1 == 2 and f3 == 3 else cell(M, V(rs1), sx(x >> 20, 12), f3)
            if r: out[rd] = r
            else: out.pop(rd, None)
        elif op == 0x23 and rs1 == 2:
            k = ('S', sx(((x >> 25) << 5) | ((x >> 7) & 31), 12))
            if f3 == 3 and V(rs2)[0] in ('K', 'A'): out[k] = V(rs2)
            else: out.pop(k, None)
        elif L.wrd(x) is not None: out.pop(L.wrd(x), None)
        if L.wrd(x) == 2:
            for k in [k for k in out if isinstance(k, tuple)]: out.pop(k)
        if op in (0x6f, 0x67) and rd:
            for r in L.CS: out.pop(r, None)
        if op == 0x73 and f3 == 0: out.pop(10, None); out.pop(11, None)
        out.pop(0, None)
        return {r: v for r, v in out.items() if v[0] in ('K', 'A', 'J')}
    ins = [None] * len(w); ins[0] = {}; work = [0]
    while work:
        q = work.pop(); o = step(q, ins[q])
        for t in succ[q]:
            if ins[t] is None: new = dict(o)
            else:
                new = {}
                for r in set(ins[t]) | set(o):
                    a, b = ins[t].get(r), o.get(r)
                    if a == b: new[r] = a
                    elif 'A' in (a or ('U',))[0] + (b or ('U',))[0] or (a and a[0] == 'J') or (b and b[0] == 'J'):
                        new[r] = ('J', 'an image address on some path into the row word', False, 0)
            if new != ins[t]: ins[t] = new; work.append(t)
    return ins[i0] or {}

def walk(M, fa, j0, init, depth, sites, chain):
    f = M.funcs[fa]; w, at = M.words(fa); nm = f[2]
    rets = {}
    if w is None or any(n == 2 for o, x, n in w):
        sites.append((chain, nm, -1, 'NOT-MEASURED', 'function with a 2-byte parcel or unreadable', None)); return rets
    work = [(j0, frozenset(init.items()))]; seen = set()
    while work:
        j, st = work.pop()
        while True:
            if j >= len(w) or not any(v[2] for _, v in st) or (j, st) in seen: break
            seen.add((j, st))
            if len(seen) > 300000: sites.append((chain, nm, -1, 'NOT-MEASURED', 'path budget', None)); return rets
            o, x, n = w[j]; op = x & 0x7f; rd = (x >> 7) & 31; rs1 = (x >> 15) & 31; rs2 = (x >> 20) & 31; f3 = (x >> 12) & 7
            reg = dict(st); out = dict(reg); nxt = j + 1
            def V(r): return ('K', 0, False, 0) if r == 0 else reg.get(r, ('U', 'r%d: no constant / image address on this path in %s' % (r, nm[:40]), False, 0))
            def base(r, imm, kind):
                v = V(r)
                if not v[2]: return
                if v[0] == 'K': sites.append((chain, nm, o, 'ABS', kind, (v[1] + imm) % M64))
                elif v[0] == 'A': sites.append((chain, nm, o, 'IMAGE', kind, ((v[1][0] + imm) % M64, v[1][1])))
                elif v[0] == 'J': sites.append((chain, nm, o, 'JOIN', kind, v[1]))
                else: sites.append((chain, nm, o, 'RUNTIME', kind, v[1]))
            def call(toff):
                ta = f[0] + toff; args = {r: V(r) for r in range(10, 18) if V(r)[2] or V(r)[0] in ('K', 'A')}
                if not any(v[2] for v in args.values()): return {}
                if ta not in M.funcs or depth >= 16:
                    sites.append((chain, nm, o, 'NOT-MEASURED', 'L argument into %s' % (M.funcs[ta][2] if ta in M.funcs else hex(ta)), None)); return {}
                key = (ta, frozenset(args.items()))
                if key in M.busy: return {}
                M.busy.add(key)
                r = walk(M, ta, 0, args, depth + 1, sites, chain + ('%s+%#x' % (nm[:40], o),))
                M.busy.discard(key); return r
            if op == 0x63:
                t = o + sx(((x >> 31) & 1) << 12 | ((x >> 7) & 1) << 11 | ((x >> 25) & 0x3f) << 5 | ((x >> 8) & 0xf) << 1, 13)
                if t in at: work.append((at[t], st))
            elif op == 0x6f:
                t = o + sx(((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11 | ((x >> 21) & 0x3ff) << 1, 21)
                if rd == 0 and t in at: nxt = at[t]
                elif rd == 0:
                    rets.update(call(t)); break
                else:
                    back = call(t)
                    for r in L.CS: out.pop(r, None)
                    for r, v in back.items(): out[r] = v
            elif op == 0x67:
                base(rs1, sx(x >> 20, 12), 'jalr')
                if rd == 0 and rs1 == 1 and (x >> 20) == 0:
                    for r in (10, 11):
                        if V(r)[2]: rets[r] = V(r)
                    break
                tg = L.jtable(M, fa, w, j) if rd == 0 else None
                if tg is not None:
                    for t in tg: work.append((at[t], st))
                    break
                if rd == 0: break
                for r in L.CS: out.pop(r, None)
            elif op in (0x03, 0x07):
                base(rs1, sx(x >> 20, 12), 'load')
                if op == 0x03:
                    k = ('S', sx(x >> 20, 12))
                    if rs1 == 2 and f3 == 3 and k in reg: out[rd] = reg[k]
                    else: out[rd] = cell(M, V(rs1), sx(x >> 20, 12), f3) or ('U', 'load at %s+%#x' % (nm[:40], o), False, 0)
            elif op in (0x23, 0x27):
                base(rs1, sx(((x >> 25) << 5) | ((x >> 7) & 31), 12), 'store')
                if rs1 == 2:
                    k = ('S', sx(((x >> 25) << 5) | ((x >> 7) & 31), 12))
                    if op == 0x23 and f3 == 3 and (V(rs2)[2] or V(rs2)[0] in ('K', 'A')): out[k] = V(rs2)
                    else: out.pop(k, None)
            elif op == 0x2f:
                base(rs1, 0, 'amo'); out[rd] = ('U', 'amo result', False, 0)
            elif op == 0x37: out[rd] = ('K', (sx(x >> 12, 20) << 12) % M64, False, 0)
            elif op == 0x17: out[rd] = ('A', ((f[0] + o + (sx(x >> 12, 20) << 12)) % M64, False), False, 0)
            elif op in (0x13, 0x1b):
                a = V(rs1); imm = sx(x >> 20, 12)
                if f3 == 0:
                    r = comb('add', a, ('K', imm % M64, False, 0))
                    if op == 0x1b and r[0] == 'K': r = ('K', sx(r[1] & 0xffffffff, 32) % M64, r[2], r[3])
                    elif op == 0x1b and r[0] != 'K': r = ('U', 'addiw', r[2], 0)
                    out[rd] = r
                elif f3 == 1 and op == 0x13:
                    out[rd] = W(('K', (a[1] << (imm & 63)) % M64, a[2], a[3] + 1)) if a[0] == 'K' else ('U', 'shift', a[2], 0)
                else:
                    out[rd] = ('U', 'opimm%d at %s+%#x' % (f3, nm[:40], o), a[2], 0)
            elif op in (0x33, 0x3b):
                a, b = V(rs1), V(rs2); f7 = x >> 25
                if op == 0x33 and f3 == 0 and f7 in (0, 0x20): out[rd] = comb('add' if f7 == 0 else 'sub', a, b)
                elif op == 0x33 and f7 == 0x10 and f3 in (2, 4, 6):     # shNadd
                    sh = ('K', (a[1] << (f3 // 2)) % M64, a[2], a[3]) if a[0] == 'K' else ('U', 'shift', a[2], 0)
                    out[rd] = comb('add', sh, b)
                elif op == 0x33 and f3 == 1 and f7 == 0 and b[0] == 'K' and a[0] == 'K':
                    out[rd] = W(('K', (a[1] << (b[1] & 63)) % M64, a[2] or b[2], max(a[3], b[3]) + 1))
                else: out[rd] = ('U', 'op at %s+%#x' % (nm[:40], o), a[2] or b[2], 0)
            elif op == 0x73:
                if f3 == 0: out.pop(10, None); out.pop(11, None)
            else:
                if L.wrd(x) is not None: out.pop(L.wrd(x), None)
            if L.wrd(x) == 2:
                for k in [k for k in out if isinstance(k, tuple)]: out.pop(k)
            out.pop(0, None)
            st = frozenset((k, v) for k, v in out.items() if v[2] or v[0] in ('K', 'A')); j = nxt
    return rets

def main():
    X, Y = L.Image(argv[1]), L.Image(argv[2])
    rows = []; fn = None
    for l in open(argv[3]):
        m = re.match(r'^(\S+)\tX 0x', l)
        if m: fn = m.group(1); continue
        m = re.match(r'^   DIFF \+(0x[0-9a-f]+) strictcmp3 lui-in-section: ', l)
        if m: rows.append((fn, int(m.group(1), 16)))
    print('row\tfunction+use\tkind\tverdict\tX\tY')
    cnt = collections.Counter(); bad = 0
    for fname, off in rows:
        res = []
        for M in (X, Y):
            c = s3.fcopies(M.I, fname); fa = c[0][0]; w, at = M.words(fa); i0 = at[off]; x0 = w[i0][1]
            # the row's value, as luiuse.py computes it
            val, us, d = L.row(M, fname, off)
            sites = []
            init = dict(pre_state(M, fa, i0)); init[(x0 >> 7) & 31] = ('K', val % M64, True, 0)
            walk(M, fa, i0 + 1, init, 0, sites, ())
            res.append(sorted(set(sites), key=lambda s: (s[0], s[1], s[2], s[3], s[4])))
        def group(M, ss):
            g = collections.defaultdict(set)
            for s in ss:
                if s[3] == 'IMAGE': d = name(M.I, s[5][0]) + (' +idx' if s[5][1] else '')
                elif s[3] == 'ABS': d = name(M.I, s[5])
                elif s[3] == 'RUNTIME': d = s[5]
                else: d = s[4]
                g[s[:5]].add(d)
            return g
        gx, gy = group(X, res[0]), group(Y, res[1])
        for key in sorted(set(gx) | set(gy), key=str):
            kind = key[3]; dx, dy = sorted(gx.get(key, ())), sorted(gy.get(key, ()))
            if key not in gx or key not in gy: v = 'DISAGREE'; bad += 1
            elif kind == 'IMAGE': v = 'IMAGE EQUAL' if dx == dy else 'IMAGE DIFFER'; bad += v == 'IMAGE DIFFER'
            elif kind == 'ABS': v = 'ABS'; bad += 1
            elif kind == 'RUNTIME': v = 'RUNTIME'
            else: v = kind; bad += 1
            cnt[v] += 1
            print('%s+%#x\t%s%s+%#x\t%s\t%s\t%s\t%s' % (fname[:50], off, (' > '.join(key[0]) + ' > ') if key[0] else '', key[1][:50], key[2], key[4], v, ' ; '.join(dx), ' ; '.join(dy)))
    print('SUMMARY rows %d sites %s' % (len(rows), dict(cnt)))
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
