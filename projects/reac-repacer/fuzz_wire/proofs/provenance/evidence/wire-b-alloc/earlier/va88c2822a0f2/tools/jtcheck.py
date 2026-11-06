#!/usr/bin/env python3
"""jtcheck.py -- settle the functions drvcmp/closure leave UNMEASURED or 'target-differ' (jump tables). Read-only.

For a same-named, same-size function in images X and Y whose words differ only in immediates (bytecmp's cmp says
UNMEASURED or EQUAL-mod-pcrel):
 1. PAIRS: every lo12 word (addi / loads / stores / jalr) is paired with an auipc writing its rs1 by bytecmp
    1480ca2faea0's MUST dataflow (repin_check e5487165abb8's targets()) or, failing that, with the nearest earlier auipc
    writing rs1 inside the same basic block (no label, branch, jump, ecall or other write of rs1 in between, so every path
    to the word ran that auipc). Labels = branch targets + jal targets inside the function + jump-table entries (3).
 2. Each pair's target on X and on Y is compared: same symbol+offset (repin_check Img.res); a .got cell by the
    symbol+offset it holds. Two different names, or a name on one side only, is a difference with no content compare
    (the target rule of repin_check e5487165abb8). Only when neither side has a symbol: same NUL-terminated string;
    same 8 bytes; else, for a target in .rodata / .data.rel.ro, as a TABLE (3).
 3. TABLE: 8-byte absolute entries read while the X entry points into the X function (jump table: entries compared as
    function-relative offsets, and added to the labels), else 4-byte entries relative to the table base read while the X
    entry points into the X function (relative jump table, same) or into .rodata (string table: compared as strings).
 Steps 1-3 repeat until the label set is stable. A word that differs and cannot be paired is reported UNPAIRED.
usage: jtcheck.py X_ELF Y_ELF fn1,fn2,..."""
import sys, os
import importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('drvcmp', os.path.join(HERE, 'drvcmp.py'))
dc = importlib.util.module_from_spec(spec); spec.loader.exec_module(dc)
Img, targets, bc_words, sx = dc.Img, dc._g['targets'], dc.bc_words, dc._g['sx']
WRITES_RD = dc._bc['WRITES_RD']
X, Y = Img(sys.argv[1]), Img(sys.argv[2])
LO12 = (0x13, 0x03, 0x23, 0x67, 0x07, 0x27)

def cstr(I, a):
    b = I.rd(a, 96) or b''
    return b[:b.find(b'\0')] if b'\0' in b else b

def table(fx, fy, ax, ay, nmax=None):
    """(kind, n, ok, cases) or None. nmax: the entry count the dispatch's bound check gives (None: read while the X
    entry stays a jump target / string)."""
    for size, rel in ((8, False), (4, True)):
        n = 0; ok = True; cases = set(); kind = None
        while n < (nmax or 1024):
            ex = X.rd(ax + size * n, size); ey = Y.rd(ay + size * n, size)
            if ex is None or ey is None: break
            if rel:
                vx = ax + int.from_bytes(ex, 'little', signed=True); vy = ay + int.from_bytes(ey, 'little', signed=True)
            else:
                vx = int.from_bytes(ex, 'little'); vy = int.from_bytes(ey, 'little')
            if fx[0] <= vx < fx[0] + fx[1] and kind in (None, 'jump'):
                kind = 'jump'; cases.add(vx - fx[0])
                if vy - fy[0] != vx - fx[0]: ok = False
            elif rel and X.sec(vx) == '.rodata' and cstr(X, vx) and kind in (None, 'str'):
                kind = 'str'
                if cstr(X, vx) != cstr(Y, vy): ok = False
            elif nmax and not rel and kind in (None, 'ptr') and (ex == ey or not X.res(vx).startswith('(')):
                kind = 'ptr'
                if ex != ey and X.res(vx) != Y.res(vy): ok = False
            else:
                break
            n += 1
        if n and (nmax is None or n == nmax):
            return ('%s%d-%s' % ('rel' if rel else 'abs', size, kind), n, ok, cases)
    return None

def blob(ax, ay, L):
    """L bytes compared as 8-byte words: equal, or both pointers to the same symbol+offset"""
    ok = True
    for k in range(0, L, 8):
        ex = X.rd(ax + k, min(8, L - k)); ey = Y.rd(ay + k, min(8, L - k))
        if ex == ey: continue
        if len(ex) < 8: ok = False; continue
        rx = X.res(int.from_bytes(ex, 'little')); ry = Y.res(int.from_bytes(ey, 'little'))
        if rx != ry or rx.startswith('('): ok = False
    return ok

def same_target(fx, fy, tx, ty, nmax=None, blen=None):
    rx, ry = X.res(tx), Y.res(ty)
    if X.sec(tx) == '.got' and Y.sec(ty) == '.got':
        gx = int.from_bytes(X.rd(tx, 8), 'little'); gy = int.from_bytes(Y.rd(ty, 8), 'little')
        rx, ry = X.res(gx), Y.res(gy)
        return (rx == ry and not rx.startswith('(')), 'got->%s | got->%s' % (rx, ry), None
    if rx == ry and not rx.startswith('('): return True, rx, None
    if not (rx.startswith('(') and ry.startswith('(')): return False, '%s | %s' % (rx, ry), None
    t = table(fx, fy, tx, ty, nmax) if X.sec(tx) in ('.rodata', '.data.rel.ro') else None
    if t and t[1] >= 2: return t[2], 'table %s %d entries%s' % (t[0], t[1], ' (bound check)' if nmax else ''), t
    sxx, syy = cstr(X, tx), cstr(Y, ty)
    if sxx and sxx == syy: return True, 'str %r' % sxx[:24], None
    if blen and X.sec(tx) in ('.rodata', '.data.rel.ro'):
        return blob(tx, ty, blen), 'initializer %d bytes (memcpy length)' % blen, None
    cx, cy = X.rd(tx, 8), Y.rd(ty, 8)
    if cx is not None and cx == cy: return True, 'const %s' % cx.hex(), None
    return False, '%s | %s' % (rx, ry), None

def bound(wx, k):
    """the entry count of a table dispatch: `addi rK, zero, K` then `bltu rK, rI` (n = K+1) or `bgeu rI, rK` (n = K)
    within the 10 words before the table's auipc at k"""
    lo = max(0, k - 10)
    for b in range(k - 1, lo - 1, -1):
        x = wx[b][1]
        if x & 0x7f != 0x63 or ((x >> 12) & 7) not in (6, 7): continue
        f3 = (x >> 12) & 7; r1 = (x >> 15) & 31; r2 = (x >> 20) & 31
        rk = r1 if f3 == 6 else r2
        for a in range(b - 1, lo - 1, -1):
            y = wx[a][1]
            if y & 0x7f == 0x13 and ((y >> 12) & 7) == 0 and ((y >> 15) & 31) == 0 and ((y >> 7) & 31) == rk:
                K = sx(y >> 20, 12)
                return K + 1 if f3 == 6 else K
        return None
    return None

def memcpy_len(wx, i):
    """`addi a2, zero, L` then a jal within the 3 words after word i: the length of the copy it feeds"""
    L = None
    for j in range(i + 1, min(len(wx), i + 4)):
        x = wx[j][1]
        if x & 0x7f == 0x13 and ((x >> 12) & 7) == 0 and ((x >> 15) & 31) == 0 and ((x >> 7) & 31) == 12:
            L = sx(x >> 20, 12)
        if x & 0x7f == 0x6f and ((x >> 7) & 31) == 1:
            return L
    return None

def hi_lo(base, ws, k, w, op):
    ho, hx, _ = ws[k]
    hi = base + ho + sx(hx >> 12, 20) * 4096
    return hi + (sx(((w >> 25) << 5) | ((w >> 7) & 31), 12) if op in (0x23, 0x27) else sx(w >> 20, 12))

def bb_auipc(wx, i, rs1, labels):
    j = i - 1
    while j >= 0:
        if wx[j + 1][0] in labels: return None
        oj, xj, _ = wx[j]; opj = xj & 0x7f; rdj = (xj >> 7) & 31
        if opj in (0x63, 0x6f, 0x67): return None
        if opj == 0x73 and ((xj >> 12) & 7) == 0 and rs1 in (10, 11): return None
        if rdj == rs1 and opj == 0x17: return j
        if rdj == rs1 and (opj in WRITES_RD or opj == 0x2f or (opj == 0x53 and ((xj >> 27) & 31) in (0x14, 0x18, 0x1c))):
            return None
        j -= 1
    return None

def run(fn):
    fx, fy = X.fsym(fn), Y.fsym(fn)
    if not fx or not fy or fx[1] != fy[1]:
        print('%s\tSKIP %s %s' % (fn, fx, fy)); return
    bx, by = X.rd(*fx), Y.rd(*fy)
    wx, wy = bc_words(bx), bc_words(by)
    def mask(op): return 0xfff if op in (0x17, 0x6f) else 0x01fff07f if op in (0x23, 0x27) else 0x000fffff
    shape = [i for i, ((o, x, n), (_, y, _)) in enumerate(zip(wx, wy)) if x != y and (
        (x & 0x7f) != (y & 0x7f) or (x & 0x7f) not in LO12 + (0x17, 0x6f) or (x & mask(x & 0x7f)) != (y & mask(x & 0x7f)))]
    if shape:
        print('%s\tREAL difference (not immediate-only) at %s' % (fn, [hex(wx[i][0]) for i in shape[:6]])); return
    st_all = dc._g['bc_states'](wx)
    base_labels = set()
    for o, x, n in wx:
        op = x & 0x7f
        if op == 0x63:
            base_labels.add(o + sx(((x >> 31) & 1) << 12 | ((x >> 7) & 1) << 11 | ((x >> 25) & 0x3f) << 5 | ((x >> 8) & 0xf) << 1, 13))
        elif op == 0x6f:
            t = o + sx(((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11 | ((x >> 21) & 0x3ff) << 1, 21)
            if 0 <= t < fx[1]: base_labels.add(t)
    cases = set()
    while True:
        labels = base_labels | cases
        pairs = {}; unpaired = []
        for i, ((o, x, n), (_, y, _)) in enumerate(zip(wx, wy)):
            op = x & 0x7f; rs1 = (x >> 15) & 31
            if op not in LO12: continue
            st = st_all[i]
            k = st[rs1] if st and rs1 in st else None
            if k is None: k = bb_auipc(wx, i, rs1, labels)
            if k is None:
                if x != y: unpaired.append('+%#x %08x vs %08x op %#x rs1 x%d' % (o, x, y, op, rs1))
                continue
            pairs[i] = (hi_lo(fx[0], wx, k, x, op), hi_lo(fy[0], wy, k, y, op), k)
        newcases = set(cases); res = []
        for i, (tx, ty, k) in sorted(pairs.items()):
            ok, what, t = same_target(fx, fy, tx, ty, bound(wx, k), memcpy_len(wx, i))
            if t and t[0].endswith('jump'): newcases |= t[3]
            res.append((wx[i][0], ok, what, wx[i][1] != wy[i][1]))
        if newcases == cases: break
        cases = newcases
    bad = [r for r in res if not r[1]]
    tabs = sorted({r[2] for r in res if r[2].startswith('table')})
    print('%s\tX %#x Y %#x size %d\tlo12 pairs %d (in differing words %d)\ttarget differs %d\tunpaired differing words %d\t%s'
          % (fn, fx[0], fy[0], fx[1], len(res), sum(1 for r in res if r[3]), len(bad), len(unpaired), tabs))
    for o, ok, what, d in bad: print('   DIFF +%#x %s' % (o, what))
    for u in unpaired: print('   UNPAIRED ' + u)

for f in sys.argv[3].split(','):
    run(f)
