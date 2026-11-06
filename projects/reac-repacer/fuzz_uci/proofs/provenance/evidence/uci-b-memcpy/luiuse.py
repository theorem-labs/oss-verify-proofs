#!/usr/bin/env python3
"""luiuse.py X_ELF Y_ELF JTCHECK_OUT   (KIT=<cmpkit 86da41d3ef68 dir>; read-only)

The by-dataflow use trace for every `strictcmp3 lui-in-section` DIFF row of jtcheck's output (function, word offset):
on BOTH images, the value the word builds (a lui's own value, or lui + the addi / addiw immediate) and EVERY use of that
value and of everything computed from it, on every path of the function and, through direct calls, of its callees.

Tracking: a forward walk over every path (both sides of each branch, `j` inside the function). A register holds
 PURE   the value, or a value computed from it and known constants only (addi / addiw / logical / shift / mul / div /
        add / sub whose other operand is PURE, x0, or a register set by li / lui / arithmetic on constants);
 MIXED  a value computed by add / sub / logical / mul from a PURE or MIXED register and a register that holds no known
        constant (an offset or mask applied to something else).
A register stops being tracked when a word writes that INTEGER register (bytecmp 1480ca2faea0's WRITES_RD /
FP_WRITES_XRD), at a call for the caller-saved registers (a callee that returns a PURE a0 / a1 gives it back), at an
ecall for a0 / a1. An 8-byte store of a tracked register to sp+K makes slot K tracked, an `ld _, K(sp)` reloads it,
any other store to sp+K clears it, any write of sp clears every slot; an `addi _, sp, imm` while a slot is tracked
is a HAND row (the stack address escapes).
Calls: a DIRECT call (jal, rd = ra) or tail call (jal x0 out of the function) to a sized FUNC with a PURE value in a0-a7
is followed into the callee with those registers PURE (depth <= 8; a recursion
already in progress adds nothing). Everything the trace cannot follow is a HAND row, listed with what it is:
 data      a PURE value stored (the field it lands in is read elsewhere)
 ret       a PURE a0 / a1 at a return of the row's own function (the caller's use is elsewhere)
 indirect  a PURE value in a0-a7 at an indirect call / jump (jalr other than ret) that is not an in-function REL4
           jump table (jtable: such a table's entries are all followed, with the state at the jr)
 syscall   a PURE value in a0-a7 at an ecall
 deep      a PURE argument at the depth limit, or into a callee that is not measured (2-byte parcel, no symbol)
Verdict per row: ADDRESS if a PURE value is ever the base of a load / store / AMO / jalr (an absolute address);
otherwise NUMBER if there is no HAND row, NUMBER+HAND if there are (each HAND row needs the reason in the record).
X and Y must give the same verdict, the same value and the same use list."""
import sys, os, re, importlib.util, collections
KIT = os.environ['KIT']
spec = importlib.util.spec_from_file_location('strictcmp3', os.path.join(KIT, 'strictcmp3.py'))
s3 = importlib.util.module_from_spec(spec); spec.loader.exec_module(s3)
CS = set(s3._bc['CALLER_SAVED']); WR = s3._bc['WRITES_RD']; FPX = s3._bc['FP_WRITES_XRD']
MAXD = 8
LOGIC_R = {(0x33, 4, 0), (0x33, 6, 0), (0x33, 7, 0), (0x33, 1, 0), (0x33, 5, 0), (0x33, 5, 0x20), (0x33, 2, 0), (0x33, 3, 0),
           (0x3b, 1, 0), (0x3b, 5, 0), (0x3b, 5, 0x20)}

def sx(v, b): return v - (1 << b) if v & (1 << (b - 1)) else v
def wrd(x):
    op = x & 0x7f; rd = (x >> 7) & 31
    if rd and (op in WR or (op == 0x53 and (x >> 27) in FPX)): return rd
    return None

class Image:
    def __init__(self, path):
        self.I = s3.Img(path); self.cache = {}; self.memo = {}; self.busy = set()
        self.funcs = {}
        for v, z, nm, t in self.I.syms:
            if t == 'STT_FUNC' and z > 0: self.funcs.setdefault(v, (v, z, nm))
    def words(self, v):
        if v not in self.cache:
            f = self.funcs[v]; b = s3.frd(self.I, f[0], f[1])
            w = s3.bc_words(b) if b is not None else None
            self.cache[v] = (w, {o: j for j, (o, x, n) in enumerate(w)} if w else None)
        return self.cache[v]

CALLEE_SAVED = {2, 8, 9} | set(range(18, 28))
def bound_const(w, m, rK):
    """K if register rK holds the constant K at word m on every path, else None: on every path from the entry to word m
    (decoded edges, plus an edge from every indirect jump to every word no decoded edge reaches) the last word that
    writes rK is `addi rK, zero, K`, with one K over all paths; a call counts as a write of a caller-saved rK, and the
    entry value counts as unknown."""
    if any(n == 2 for o, x, n in w) or rK in (0, 2): return None
    succ = [list(s) for s in s3._succ(w)]
    preds = {t for s in succ for t in s}
    roots = [q for q in range(1, len(w)) if q not in preds]
    for q, (o, x, n) in enumerate(w):
        if x & 0x7f == 0x67 and (x >> 7) & 31 == 0 and not s3._isret(x): succ[q] = succ[q] + roots
    cs = rK not in CALLEE_SAVED
    def after(q, last):
        x = w[q][1]; op = x & 0x7f
        if op == 0x13 and (x >> 12) & 7 == 0 and (x >> 15) & 31 == 0 and (x >> 7) & 31 == rK: return ('K', sx(x >> 20, 12))
        if wrd(x) == rK: return ('OTHER',)
        if cs and op in (0x6f, 0x67) and (x >> 7) & 31: return ('OTHER',)
        return last
    at_m = set(); seen = {(0, ('ENTRY',))}; stack = [(0, ('ENTRY',))]
    while stack:
        q, last = stack.pop()
        if q == m: at_m.add(last); continue
        nl = after(q, last)
        for t in succ[q]:
            if (t, nl) not in seen: seen.add((t, nl)); stack.append((t, nl))
    if len(at_m) == 1 and next(iter(at_m))[0] == 'K': return next(iter(at_m))[1]
    return None

def jtable(M, fa, w, j):
    """the in-function targets of a REL4 jump table dispatched by the `jr rT` at word j, else None. Shape (every
    register checked, nothing written in between): `bltu rK, rI` with rK = K on every path (bound_const) .. `slli rI, rI, 2`
    .. `add rA, rI, rB` .. `lw rE, 0(rA)` .. `add rT, rE, rB` .. `jr rT`, rB = auipc + addi (table address B, set before
    and unchanged up to the second add); n = K + 1 entries, each target B + sx32(entry), every one inside the function."""
    def d(i):
        x = w[i][1]; return x & 0x7f, (x >> 7) & 31, (x >> 12) & 7, (x >> 15) & 31, (x >> 20) & 31, x >> 25, sx(x >> 20, 12)
    def back(i, pred, lim=24):
        for k in range(i - 1, max(-1, i - lim), -1):
            if w[k][2] != 4: return None
            if pred(d(k)): return k
        return None
    def clean(r, a, b):   # register r not written by words a+1 .. b-1
        return all(w[k][2] == 4 and wrd(w[k][1]) != r for k in range(a + 1, b))
    rT = d(j)[3]
    k1 = back(j, lambda t: t[1] == rT)
    if k1 is None: return None
    op, rd, f3, a, b, f7, _ = d(k1)
    if not (op == 0x33 and f3 == 0 and f7 == 0): return None
    k2 = back(k1, lambda t: t[1] in (a, b))
    if k2 is None: return None
    op2, rE, f32, rA, _, _, imm2 = d(k2)
    if not (op2 == 0x03 and f32 == 2 and imm2 == 0): return None
    rB = b if rE == a else a
    k3 = back(k2, lambda t: t[1] == rA)
    if k3 is None: return None
    op3, _, f33, a3, b3, f73, _ = d(k3)
    if not (op3 == 0x33 and f33 == 0 and f73 == 0 and rB in (a3, b3)): return None
    rI = b3 if a3 == rB else a3
    k4 = back(k3, lambda t: t[1] == rI)
    if k4 is None: return None
    op4, _, f34, a4, _, _, imm4 = d(k4)
    if not (op4 == 0x13 and f34 == 1 and a4 == rI and (imm4 & 63) == 2): return None
    k5 = back(k4, lambda t: t[0] == 0x63 and t[2] == 6 and t[4] == rI)
    if k5 is None or not clean(rI, k5, k4): return None
    K = bound_const(w, k5, d(k5)[3])
    if K is None: return None
    k7 = back(k3, lambda t: t[1] == rB, 40)
    if k7 is None: return None
    op7, _, f37, a7, _, _, lo = d(k7)
    if not (op7 == 0x13 and f37 == 0): return None
    k8 = back(k7, lambda t: t[1] == a7)
    if k8 is None or d(k8)[0] != 0x17: return None
    if not clean(rB, k7, k1): return None   # B is read by the two adds; later writes of rB do not matter
    B = fa + w[k8][0] + (sx(w[k8][1] >> 12, 20) << 12) + lo
    n = K + 1; raw = s3.frd(M.I, B, 4 * n)
    if raw is None: return None
    at = {o for o, x, nn in w}; out = []
    for e in range(n):
        t = B + sx(int.from_bytes(raw[4 * e:4 * e + 4], 'little'), 32) - fa
        if t not in at: return None
        out.append(t)
    return out

def walk(M, fa, j0, init, depth, top, chain=()):
    """-> (uses set, PURE return registers). uses: (function, offset, class, detail)"""
    f = M.funcs[fa]; w, at = M.words(fa); name = f[2]
    uses = set(); rets = set()
    if w is None or any(n == 2 for o, x, n in w):
        uses.add((name, -1, 'deep', 'callee not measured (2-byte parcel or unreadable)')); return uses, rets
    work = [(j0, frozenset(init.items()))]; seen = set()
    while work:
        j, st = work.pop()
        while True:
            if j >= len(w) or not any(v in ('PURE', 'MIXED') for _, v in st) or (j, st) in seen: break
            seen.add((j, st))
            if len(seen) > 200000: uses.add((name, -1, 'deep', 'path budget')); return uses, rets
            o, x, n = w[j]; op = x & 0x7f; rd = (x >> 7) & 31; rs1 = (x >> 15) & 31; rs2 = (x >> 20) & 31; f3 = (x >> 12) & 7
            reg = dict(st)
            def cls(r): return reg.get(r) if reg.get(r) in ('PURE', 'MIXED') else None
            def pc(r): return r == 0 or reg.get(r) in ('PURE', 'CONST')
            def isc(r): return r == 0 or reg.get(r) == 'CONST'
            nxt = j + 1; out = dict(reg); U = lambda c, d: uses.add((name, o, c, d + ((' via ' + ' > '.join(chain)) if c in ('data', 'syscall', 'indirect', 'deep') and chain else '')))
            def call(target_off, tail):
                pure = frozenset(r for r in range(10, 18) if reg.get(r) == 'PURE')
                ta = f[0] + target_off
                back = set()
                if pure:
                    if ta not in M.funcs or depth >= MAXD:
                        U('deep', 'PURE %s into %s' % (sorted(pure), M.funcs[ta][2] if ta in M.funcs else hex(ta)))
                    else:
                        key = (ta, pure)
                        if key in M.busy: su, sr = set(), set()
                        else:
                            M.busy.add(key)
                            su, sr = walk(M, ta, 0, {r: 'PURE' for r in pure}, depth + 1, False,
                                          chain + ('%s+%#x(%s)' % (name[:50], o, ','.join('a%d' % (r - 10) for r in sorted(pure))),))
                            M.busy.discard(key)
                        uses.update(su); back = sr
                return back
            if op == 0x63:
                for r in (rs1, rs2):
                    if cls(r): U('logic', 'branch %s' % cls(r))
                t = o + sx(((x >> 31) & 1) << 12 | ((x >> 7) & 1) << 11 | ((x >> 25) & 0x3f) << 5 | ((x >> 8) & 0xf) << 1, 13)
                if t in at: work.append((at[t], st))
            elif op == 0x6f:
                t = o + sx(((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11 | ((x >> 21) & 0x3ff) << 1, 21)
                if rd == 0 and t in at: nxt = at[t]
                elif rd == 0:                       # tail call: the callee's returns are this function's
                    for r in call(t, True):
                        if top: U('ret', 'a%d PURE (tail call)' % (r - 10))
                        rets.add(r)
                    break
                else:
                    back = call(t, False)
                    for r in CS: out.pop(r, None)
                    for r in back: out[r] = 'PURE'
            elif op == 0x67:
                if cls(rs1): U('base', 'jalr %s' % cls(rs1))
                if rd == 0 and rs1 == 1 and (x >> 20) == 0:      # ret
                    for r in (10, 11):
                        if reg.get(r) == 'PURE':
                            rets.add(r)
                            if top: U('ret', 'a%d PURE' % (r - 10))
                    break
                tgts = jtable(M, fa, w, j) if rd == 0 else None
                if tgts is not None:                      # an in-function REL4 jump table: follow every entry
                    for t in tgts: work.append((at[t], st))
                    break
                for r in range(10, 18):
                    if reg.get(r) == 'PURE': U('indirect', 'a%d PURE at jalr' % (r - 10))
                if rd == 0: break
                for r in CS: out.pop(r, None)
            elif op in (0x03, 0x07):
                if cls(rs1): U('base', 'load %s' % cls(rs1))
                if op == 0x03:
                    out.pop(rd, None)
                    if rs1 == 2 and f3 == 3 and ('S', sx(x >> 20, 12)) in reg:      # reload of a spilled copy
                        out[rd] = reg[('S', sx(x >> 20, 12))]
            elif op in (0x23, 0x27):
                if cls(rs1): U('base', 'store %s' % cls(rs1))
                if op == 0x23 and reg.get(rs2) == 'PURE': U('data', 'store%d PURE' % (1 << f3))
                if rs1 == 2:
                    k = ('S', sx(((x >> 25) << 5) | ((x >> 7) & 31), 12))
                    if op == 0x23 and f3 == 3 and cls(rs2): out[k] = cls(rs2)
                    else: out.pop(k, None)
            elif op == 0x2f:
                if cls(rs1): U('base', 'amo %s' % cls(rs1))
                if reg.get(rs2) == 'PURE': U('data', 'amo PURE')
                out.pop(rd, None)
            elif op in (0x13, 0x1b):
                if cls(rs1):
                    U('logic' if f3 else 'arith', 'opimm%d %s' % (f3, cls(rs1))); out[rd] = cls(rs1)
                elif isc(rs1) and f3 == 0: out[rd] = 'CONST'
                else: out.pop(rd, None)
            elif op in (0x33, 0x3b):
                a, b = cls(rs1), cls(rs2)
                if a or b:
                    f7 = x >> 25
                    kind = 'logic' if (op, f3, f7) in LOGIC_R else 'arith'
                    U(kind, '%s %s,%s' % ('muldiv' if f7 == 1 else 'op', reg.get(rs1), reg.get(rs2)))
                    out[rd] = 'PURE' if pc(rs1) and pc(rs2) else 'MIXED'
                elif isc(rs1) and isc(rs2): out[rd] = 'CONST'
                else: out.pop(rd, None)
            elif op == 0x37: out[rd] = 'CONST'
            elif op == 0x17: out.pop(rd, None)
            elif op == 0x73:
                if f3 == 0:
                    for r in range(10, 18):
                        if reg.get(r) == 'PURE': U('syscall', 'a%d PURE at ecall' % (r - 10))
                    out.pop(10, None); out.pop(11, None)
                elif cls(rs1): U('other', 'csr %s' % cls(rs1))
            else:
                if cls(rs1) or cls(rs2): U('other', 'op%#x %s' % (op, cls(rs1) or cls(rs2)))
                if wrd(x) is not None: out.pop(wrd(x), None)
            if any(isinstance(k, tuple) for k in reg):
                if op == 0x13 and f3 == 0 and rs1 == 2 and rd not in (0, 2):
                    U('data', 'stack address sp%+d taken while a spilled copy is tracked' % sx(x >> 20, 12))
                if wrd(x) == 2:
                    for k in [k for k in out if isinstance(k, tuple)]: out.pop(k)
            out.pop(0, None)
            st = frozenset(out.items()); j = nxt
    return uses, rets

def row(M, fname, off):
    c = s3.fcopies(M.I, fname)
    if len(c) != 1: return None, None, 'NOT-MEASURED (name)'
    fa = c[0][0]; w, at = M.words(fa)
    if not w or off not in at: return None, None, 'NOT-MEASURED (word)'
    i0 = at[off]; o0, x0, n0 = w[i0]; op0 = x0 & 0x7f; rd0 = (x0 >> 7) & 31
    if op0 == 0x37: val = sx(x0 >> 12, 20) << 12
    elif op0 in (0x13, 0x1b) and ((x0 >> 12) & 7) == 0:
        rs1 = (x0 >> 15) & 31; val = None
        for j in range(i0 - 1, -1, -1):
            o, x, n = w[j]
            if n == 4 and x & 0x7f == 0x37 and (x >> 7) & 31 == rs1: val = (sx(x >> 12, 20) << 12) + sx(x0 >> 20, 12); break
            if n == 4 and wrd(x) == rs1: break
        if val is not None and op0 == 0x1b: val = sx(val & 0xffffffff, 32)
    else: return None, None, 'NOT-MEASURED (not a lui / addi pair)'
    uses, rets = walk(M, fa, i0 + 1, {rd0: 'PURE'}, 0, True)
    us = sorted(uses, key=lambda u: (u[0], u[1], u[2], u[3]))
    if any(u[2] == 'base' and 'PURE' in u[3] for u in us): v = 'ADDRESS'
    elif any(u[2] in ('data', 'ret', 'indirect', 'syscall', 'deep') for u in us): v = 'NUMBER+HAND'
    else: v = 'NUMBER'
    return val, us, v

def main():
    X, Y = Image(sys.argv[1]), Image(sys.argv[2])
    rows = []; fn = None
    for l in open(sys.argv[3]):
        m = re.match(r'^(\S+)\tX 0x', l)
        if m: fn = m.group(1); continue
        m = re.match(r'^   DIFF \+(0x[0-9a-f]+) strictcmp3 lui-in-section: ', l)
        if m: rows.append((fn, int(m.group(1), 16)))
    print('fn\tword\tvalue\tverdict\tX=Y\thand uses (function+offset class detail)')
    cnt = collections.Counter()
    for fname, off in rows:
        vx, ux, dx = row(X, fname, off); vy, uy, dy = row(Y, fname, off)
        nx = [(u[0], u[2], u[3]) for u in ux] if ux else []; ny = [(u[0], u[2], u[3]) for u in uy] if uy else []
        same = vx == vy and dx == dy and nx == ny
        v = dx if same else 'DISAGREE'
        cnt[v] += 1
        hand = [u for u in (ux or []) if u[2] in ('data', 'ret', 'indirect', 'syscall', 'deep', 'base')]
        print('%s\t+%#x\t%s\t%s\t%s\t%s' % (fname, off, None if vx is None else '%#x' % (vx % 2**64), v, same,
              ' | '.join('%s+%#x %s %s' % (u[0][:60], u[1], u[2], u[3]) for u in hand if u[2] != 'base' or 'PURE' in u[3])))
    print('SUMMARY rows %d %s' % (len(rows), dict(cnt)))
    sys.exit(0 if not (cnt['ADDRESS'] or cnt['DISAGREE'] or any(k.startswith('NOT-MEASURED') for k in cnt)) else 1)


if __name__ == '__main__':
    main()
