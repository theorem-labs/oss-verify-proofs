#!/usr/bin/env python3
"""settle.py X_ELF Y_ELF fn1,fn2,...   (KIT=<cmpkit 86da41d3ef68 dir>; read-only)

Settles, by a NAMED MEASUREMENT, every target that cmpkit 86da41d3ef68's jtcheck.py (8b0ea3862423) leaves UNMEASURED or
calls a DIFF in the listed functions, except its `lui-in-section` rows (luiuse.py takes those). Each target pair (X
address, Y address, the lo12 word that forms it) is re-collected
from jtcheck's own pairing (its same_target is wrapped, nothing else changes), then exactly one measurement applies, chosen
by the instructions that USE the address, decoded on BOTH images; no measurement applies -> the target stays OPEN (exit 1).

 BYTE64     a byte table indexed by a 6-bit value: within 8 words of the lo12 word that forms table base rT, a
            `srli rI, _, 58` (rI <= 63), an `add rA, rT, rI` and a `lbu _, 0(rA)`, with rT / rI / rA not written in
            between. Extent 64 bytes; the 64 file bytes at X and at Y must be equal.
 WORDS(n)   a 4-byte table with a bound: `bltu rK, rJ` with rK = K on every path (bound_const: the last write of rK on
            every path from the entry is `addi rK, zero, K`), rJ <= K, n = K+1; then `slli rI, rJ, 2`, `add rA, rT, rI`
            (rA may be rT), `lw _, 0(rA)` with the loaded value not added back to rT. Extent 4n bytes; equal bytes.
 REL4(n)    the same bound, `lw rV, 0(rA)` (rA not rT) and then `add _, rV, rT` / `add _, rT, rV` (entry = offset from
            the table): each of the n entries resolves to tbl + sx32(entry) on each side, and each pair of resolved
            targets must be the same in-function offset (a jump: `jr` follows) or the same string by CSTRANY's byte
            rule (a value: no jr).
 CSTRANY    an address used as a C string: the bytes from the target up to and including the first NUL, all inside
            the PT_LOAD's file bytes, must be equal on both sides, and the NUL must lie within 256 bytes. Unlike the
            kit's C-string rule it accepts non-printable bytes (ESC of the ANSI colour sequences \\x1b[..m) and the
            empty string; every acceptance is printed with its bytes. Applied only when no table pattern matches, the
            forming word is not a load, and cstr_use passes on BOTH images: on every path through the function from
            the forming word (branches both ways, `j` inside the function, calls continue with the callee-saved
            registers, 8-byte spills to sp slots and their reloads tracked), the address and every copy of it is only
            passed on (call argument, return, jump out), stored as a value, compared, or read by `lbu _, 0(r)`; any
            other load / store on it, arithmetic on it, jump through it or other read refuses (the target stays OPEN).
Output: one row per target: fn, word offset, X, Y, measurement, verdict, detail. Summary last."""
import sys, os, io, contextlib, importlib.util
KIT = os.environ['KIT']
sys.path.insert(0, KIT)
spec = importlib.util.spec_from_file_location('jt', os.path.join(KIT, 'jtcheck.py'))
jt = importlib.util.module_from_spec(spec)
argv = sys.argv; sys.argv = [os.path.join(KIT, 'jtcheck.py')] + argv[1:3] + ['-']
spec.loader.exec_module(jt)
dc = jt.dc
X, Y = jt.X, jt.Y
REC = []; CUR = {}
orig = jt.same_target
def rec(fx, fy, tx, ty, word, nmax=None, blen=None):
    r = orig(fx, fy, tx, ty, word, nmax, blen)
    if r[0] is not True: REC.append((CUR['fn'], tx, ty, r[0], r[1]))
    return r
jt.same_target = rec

def sx(v, b): return v - (1 << b) if v & (1 << (b - 1)) else v
def dec(x):
    return dict(op=x & 0x7f, rd=(x >> 7) & 31, f3=(x >> 12) & 7, rs1=(x >> 15) & 31, rs2=(x >> 20) & 31,
                f7=x >> 25, imm=sx(x >> 20, 12), sh=(x >> 20) & 63)
WRITES_RD, FP_WRITES_XRD = dc._bc['WRITES_RD'], dc._bc['FP_WRITES_XRD']   # bytecmp 1480ca2faea0's integer-rd rule
def writes(d, r):
    """the word writes INTEGER register r (an FP destination with the same number is not r)"""
    return r != 0 and d['rd'] == r and (d['op'] in WRITES_RD or (d['op'] == 0x53 and (d['f7'] >> 2) in FP_WRITES_XRD))

def filebytes(I, a, n):
    g = next(((v, fz, d) for v, fz, d in I.segs if v <= a < v + fz), None)
    if g is None or a + n > g[0] + g[1]: return None
    return g[2][a - g[0]:a - g[0] + n]

def cstr(I, a):
    b = filebytes(I, a, 1)
    if b is None: return None
    out = b''
    while len(out) <= 256:
        c = filebytes(I, a + len(out), 1)
        if c is None: return None
        out += c
        if c == b'\0': return out
    return None

def lo12_words(fn, f, ws, ta):
    """indices of lo12 words whose auipc pair resolves to ta (jtcheck's MUST dataflow)"""
    st_all = dc._g['bc_states'](ws); out = []
    for i, (o, x, n) in enumerate(ws):
        op = x & 0x7f; rs1 = (x >> 15) & 31
        if op not in jt.LO12: continue
        st = st_all[i]; k = st[rs1] if st and rs1 in st else None
        if k is not None and jt.hi_lo(f[0], ws, k, x, op) == ta: out.append(i)
    return out

def byte64(ws, i):
    rT = dec(ws[i][1])['rd']
    if dec(ws[i][1])['op'] != 0x13: return None
    lo, hi = max(0, i - 8), min(len(ws), i + 9)
    for j in range(lo, hi):
        a = dec(ws[j][1])
        if not (a['op'] == 0x33 and a['f3'] == 0 and a['f7'] == 0 and rT in (a['rs1'], a['rs2'])): continue
        if j <= i or any(writes(dec(ws[m][1]), rT) for m in range(i + 1, j)): continue
        rI = a['rs2'] if a['rs1'] == rT else a['rs1']; rA = a['rd']
        s = [m for m in range(lo, j) if dec(ws[m][1])['op'] == 0x13 and dec(ws[m][1])['f3'] == 5 and dec(ws[m][1])['rd'] == rI
             and dec(ws[m][1])['sh'] == 58 and (ws[m][1] >> 26) == 0]
        if not s or any(writes(dec(ws[m][1]), rI) for m in range(s[-1] + 1, j)): continue
        for k in range(j + 1, hi):
            b = dec(ws[k][1])
            if b['op'] == 0x03 and b['f3'] == 4 and b['rs1'] == rA and b['imm'] == 0: return (s[-1], j, k)
            if writes(b, rA): break
    return None

def bound_const(ws, m, rK):
    """K if register rK holds the constant K at word m on every path, else None: on every path from the entry to word m
    (decoded edges, plus an edge from every indirect jump to every word no decoded edge reaches) the last word that
    writes rK is `addi rK, zero, K`, with one K over all paths; a call counts as a write of a caller-saved rK, and the
    entry value counts as unknown."""
    if any(n == 2 for o, x, n in ws): return None
    if rK in (0, 2): return None
    succ = [list(s) for s in dc._succ(ws)]
    preds = {t for s in succ for t in s}
    roots = [q for q in range(1, len(ws)) if q not in preds]
    for q, (o, x, n) in enumerate(ws):
        if x & 0x7f == 0x67 and (x >> 7) & 31 == 0 and not dc._isret(x): succ[q] = succ[q] + roots
    caller_saved = rK not in CALLEE_SAVED
    def after(q, last):
        f = dec(ws[q][1])
        if f['op'] == 0x13 and f['f3'] == 0 and f['rs1'] == 0 and f['rd'] == rK: return ('K', f['imm'])
        if writes(f, rK): return ('OTHER',)
        if caller_saved and f['op'] in (0x6f, 0x67) and f['rd'] != 0: return ('OTHER',)
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

def table4(ws, i):
    """-> (n, kind, lw index, jr?) for the bounded 4-byte table whose base the lo12 word i forms, else None"""
    d = dec(ws[i][1]); rT = d['rd']
    if d['op'] != 0x13: return None
    for j in range(i + 1, min(len(ws), i + 40)):
        a = dec(ws[j][1])
        if not (a['op'] == 0x33 and a['f3'] == 0 and a['f7'] == 0 and rT in (a['rs1'], a['rs2'])):
            if writes(a, rT): return None
            continue
        rI = a['rs2'] if a['rs1'] == rT else a['rs1']; rA = a['rd']
        k = j + 1; b = dec(ws[k][1])
        if not (b['op'] == 0x03 and b['f3'] == 2 and b['rs1'] == rA and b['imm'] == 0): return None
        sl = j - 1; c = dec(ws[sl][1])
        if not (c['op'] == 0x13 and c['f3'] == 1 and c['rd'] == rI and c['sh'] == 2):
            sl = None
            for m in range(j - 1, max(-1, j - 12), -1):
                c = dec(ws[m][1])
                if c['op'] == 0x13 and c['f3'] == 1 and c['rd'] == rI and c['sh'] == 2: sl = m; break
                if writes(c, rI): return None
            if sl is None: return None
        rJ = dec(ws[sl][1])['rs1']          # the index: rI = rJ << 2
        # the bound: `bltu rK, rJ` before the slli (rJ not written in between), rK holding K on every path (bound_const)
        n = None
        for m in range(sl - 1, max(-1, sl - 12), -1):
            e = dec(ws[m][1])
            if e['op'] == 0x63 and e['f3'] == 6 and e['rs2'] == rJ:
                K = bound_const(ws, m, e['rs1'])
                if K is not None: n = K + 1
                break
            if writes(e, rJ): return None
        if n is None: return None
        rV = b['rd']; e = dec(ws[k + 1][1])
        rel = e['op'] == 0x33 and e['f3'] == 0 and e['f7'] == 0 and {e['rs1'], e['rs2']} == {rV, rT}
        if rel and rA == rT: return None   # rT no longer holds the table address: not an offset-from-table entry
        jr = rel and dec(ws[k + 2][1])['op'] == 0x67 and dec(ws[k + 2][1])['rs1'] == e['rd']
        return (n, 'REL4' if rel else 'WORDS', k, jr)
    return None

CALLEE_SAVED = {2, 8, 9} | set(range(18, 28))   # sp, s0-s11: kept across a call

def cstr_use(ws, i):
    """-> None if every use of the address that the lo12 word i forms is a C-string use, on every path through the
    function from i; else the first word that is not. Paths: fall-through, both sides of a branch, `j` (jal x0) inside
    the function; a call (jal / jalr with rd = ra) passes the address on and the path continues after it with only the
    callee-saved registers (sp, s0-s11) still holding it; `ret` (jalr x0, 0(ra)) or a `j` out of the function passes it
    on and ends the path; any other `jalr x0` (an indirect jump) while it is live refuses; an ecall passes it on and
    clears a0 / a1; a path ends when no register and no stack slot holds it. A register is cleared only by a word that
    writes that INTEGER register (bytecmp 1480ca2faea0's WRITES_RD / FP_WRITES_XRD). An `sd` of it to sp+K makes slot K
    a copy, an `ld _, K(sp)` reloads it, an FP reload of slot K refuses, any other store to sp+K clears the slot, `addi
    sp, sp, +N` followed by `ret` releases every slot, any other write of sp while a slot holds it refuses. Allowed:
    passing it on, an 8-byte store of it as a value through a base other than sp / s0 (a pointer field; the stored copy
    is not followed), `mv` (addi _, r, 0; the copy is tracked), a branch compare, `lbu _, 0(r)` (byte 0 is inside the
    compared bytes). Refused: any other load or store with it as base, a narrower store of it, a store of it through
    s0, any arithmetic on it, a jump or call through it, any other instruction reading it, a 2-byte parcel on a path
    (not decoded here)."""
    at = {o: j for j, (o, x, n) in enumerate(ws)}
    end = ws[-1][0] + ws[-1][2]
    work = [(i + 1, frozenset({dec(ws[i][1])['rd']}), frozenset())]; seen = set()
    while work:
        j, regs, slots = work.pop()
        while True:
            if (j, regs, slots) in seen or j >= len(ws) or not (regs or slots): break
            seen.add((j, regs, slots))
            if len(seen) > 50000: return 'path budget exceeded'
            o, x, n = ws[j]
            if n == 2: return '+%#x 2-byte parcel' % o
            d = dec(x); op = d['op']
            if op == 0x63:
                t = o + sx(((x >> 31) & 1) << 12 | ((x >> 7) & 1) << 11 | ((x >> 25) & 0x3f) << 5 | ((x >> 8) & 0xf) << 1, 13)
                if t in at: work.append((at[t], regs, slots))
                elif not (0 <= t < end): pass
                else: return '+%#x branch into the middle of a word' % o
                j += 1; continue
            if op == 0x6f:
                t = jt.jal_target(0, o, x)
                if d['rd'] == 0:
                    if t in at: j = at[t]; continue
                    if 0 <= t < end: return '+%#x jump into the middle of a word' % o
                    break
                regs = frozenset(r for r in regs if r in CALLEE_SAVED); j += 1; continue
            if op == 0x67:
                if d['rs1'] in regs: return '+%#x jumps or calls through it' % o
                if d['rd'] == 0:
                    if d['rs1'] == 1 and d['imm'] == 0: break   # ret: the address is returned / dropped
                    return '+%#x indirect jump while it is live' % o
                regs = frozenset(r for r in regs if r in CALLEE_SAVED); j += 1; continue
            if op == 0x03:
                if d['rs1'] in regs and not (d['f3'] == 4 and d['imm'] == 0): return '+%#x load from it' % o
                if d['rs1'] == 2 and d['f3'] == 3 and d['imm'] in slots:   # reload of a spilled copy
                    regs = (regs | {d['rd']}) if d['rd'] else regs; j += 1; continue
            elif op in (0x23, 0x27):
                if d['rs1'] in regs: return '+%#x store with it as base' % o
                if op == 0x23 and d['rs2'] in regs and d['f3'] != 3: return '+%#x narrow store of it' % o
                if op == 0x23 and d['rs2'] in regs and d['rs1'] == 8: return '+%#x store of it through s0 (frame?)' % o
                if d['rs1'] == 2:
                    s_imm = sx(((x >> 25) << 5) | ((x >> 7) & 31), 12)
                    if op == 0x23 and d['f3'] == 3 and d['rs2'] in regs: slots = slots | {s_imm}
                    else: slots = slots - {s_imm}
            elif op == 0x13 and d['f3'] == 0 and d['imm'] == 0 and d['rs1'] in regs:
                regs = (regs | {d['rd']}) if d['rd'] else regs; j += 1; continue
            elif op in (0x13, 0x1b):
                if d['rs1'] in regs: return '+%#x arithmetic on it' % o
            elif op in (0x37, 0x17):
                pass
            elif d['rs1'] in regs or d['rs2'] in regs:
                return '+%#x opcode %#x reads it' % (o, op)
            if op == 0x07 and d['rs1'] == 2 and d['imm'] in slots: return '+%#x FP reload of a spilled copy' % o
            if op == 0x73 and d['f3'] == 0: regs = regs - {10, 11}   # ecall returns in a0 / a1
            if writes(d, d['rd']):
                if d['rd'] == 2 and slots:
                    if not (op == 0x13 and d['f3'] == 0 and d['rs1'] == 2 and d['imm'] > 0 and epilogue(ws, j)):
                        return '+%#x sp moves while a copy is spilled' % o
                    slots = frozenset()   # `addi sp, sp, +N` right before `ret`: the frame holding the copies is released
                regs = regs - {d['rd']}
            j += 1
    return None

def epilogue(ws, j):
    """the words after j up to the first control transfer are loads off sp and ALU words, and that transfer is `ret`"""
    for k in range(j + 1, min(len(ws), j + 16)):
        o, x, n = ws[k]
        if n == 2: return False
        d = dec(x)
        if d['op'] == 0x67: return d['rd'] == 0 and d['rs1'] == 1 and d['imm'] == 0
        if d['op'] in (0x63, 0x6f, 0x23, 0x27): return False
        if d['op'] == 0x03 and d['rs1'] != 2: return False
    return False

def wsof(I, fn):
    f = jt.fsymq(I, fn); return f, jt.bc_words(dc.frd(I, *f))

for fn in argv[3].split(','):
    CUR['fn'] = fn
    with contextlib.redirect_stdout(io.StringIO()): jt.run(fn)

rows = []; seen = set()
for fn, tx, ty, ok, what in REC:
    fx, wx = wsof(X, fn); fy, wy = wsof(Y, fn)
    for i in lo12_words(fn, fx, wx, tx):
        if (fn, i) in seen: continue
        seen.add((fn, i))
        o = wx[i][0]
        if i not in lo12_words(fn, fy, wy, ty):
            rows.append((fn, o, tx, ty, '-', 'OPEN', 'Y pair does not resolve to the jtcheck Y target')); continue
        bx, by = byte64(wx, i), byte64(wy, i)
        if bx and by and bx == by:
            a, b = filebytes(X, tx, 64), filebytes(Y, ty, 64)
            rows.append((fn, o, tx, ty, 'BYTE64', 'EQUAL' if a is not None and a == b else 'DIFFER',
                         'srli58 +%#x add +%#x lbu +%#x; 64 bytes %s' % (wx[bx[0]][0], wx[bx[1]][0], wx[bx[2]][0], a.hex() if a else None)))
            continue
        t, u = table4(wx, i), table4(wy, i)
        if t and u and t == u:
            n, kind, k, jr = t
            if kind == 'WORDS':
                a, b = filebytes(X, tx, 4 * n), filebytes(Y, ty, 4 * n)
                rows.append((fn, o, tx, ty, 'WORDS(%d)' % n, 'EQUAL' if a is not None and a == b else 'DIFFER',
                             'lw +%#x; %d bytes %s' % (wx[k][0], 4 * n, a.hex() if a else None)))
                continue
            bad = []; det = []
            for e in range(n):
                ex, ey = filebytes(X, tx + 4 * e, 4), filebytes(Y, ty + 4 * e, 4)
                if ex is None or ey is None: bad.append('entry %d unreadable' % e); continue
                ax = tx + sx(int.from_bytes(ex, 'little'), 32); ay = ty + sx(int.from_bytes(ey, 'little'), 32)
                if jr:
                    if ax - fx[0] != ay - fy[0] or not (0 <= ax - fx[0] < fx[1]): bad.append('entry %d +%#x | +%#x' % (e, ax - fx[0], ay - fy[0]))
                    else: det.append('+%#x' % (ax - fx[0]))
                else:
                    sxs, sys_ = cstr(X, ax), cstr(Y, ay)
                    if sxs is None or sxs != sys_: bad.append('entry %d %r | %r' % (e, sxs, sys_))
                    else: det.append(repr(sxs))
            rows.append((fn, o, tx, ty, 'REL4(%d)%s' % (n, ' jump' if jr else ' string'), 'EQUAL' if not bad else 'DIFFER',
                         '; '.join(bad) if bad else ' '.join(det)))
            continue
        ux, uy = cstr_use(wx, i), cstr_use(wy, i)
        if dc.loadwidth(wx[i][1]) is None and ux is None and uy is None:
            a, b = cstr(X, tx), cstr(Y, ty)
            rows.append((fn, o, tx, ty, 'CSTRANY', 'EQUAL' if a is not None and a == b else 'DIFFER', '%r | %r' % (a, b)))
            continue
        rows.append((fn, o, tx, ty, '-', 'OPEN', '%s; use X: %s; use Y: %s' % (what, ux, uy)))
print('fn\tword\tX\tY\tmeasurement\tverdict\tdetail')
for r in rows: print('%s\t+%#x\t%#x\t%#x\t%s\t%s\t%s' % r)
from collections import Counter
c = Counter((r[4].split('(')[0], r[5]) for r in rows)
print('SUMMARY targets %d functions %d %s' % (len(rows), len({r[0] for r in rows}), dict(c)))
sys.exit(0 if all(r[5] == 'EQUAL' for r in rows) else 1)
