#!/usr/bin/env python3
"""jtcheck.py -- settle the functions a byte compare leaves UNMEASURED or 'target-differ' (jump tables). Read-only.

Loads the comparison kit beside it, checking each file's sha256:
  strictcmp2.py 5f6c05791a3f  -> `tsame`, the target rule of record (and qres / region / frd / cstr_rows), which loads
  drvcmp.py     89ca4b797ed7  -> class Img = repin_check 4c05cadaeba3 lines 31-80, targets / sx / w_off lines 209-231,
                                 bytecmp 1480ca2faea0 (drvcmp checks those two itself).

For a same-named, same-size function in images X and Y whose words differ only in immediates:
 1. PAIRS: every lo12 word (addi / loads / stores / jalr) is paired with the auipc that wrote its base, by bytecmp's MUST
    dataflow, else - only in a function with no 2-byte parcel - with the nearest earlier auipc in the same basic block.
    UNPAIRED (settles nothing): a differing word that cannot be paired; a word that cannot be paired whose base register
    was last written, in address order, by an auipc, equal or not; an auipc that no pair consumes. A differing word of
    any other shape (a branch, another opcode, a 2-byte parcel) is a REAL difference and stops the function.
 2. EVERY TARGET PAIR - each lo12 pair and each jal - is judged first by strictcmp2's `tsame`, the rule of record:
    qualified names (a duplicated name by its STT_FILE; exact-address names for size-0 / NOTYPE symbols such as
    `dlsym`), a name on one side only or two different names = a difference with no content compare; .got cells by
    what they hold (a pointer by name; a value raw, inside PT_TLS also by its STT_TLS symbol; an address-taken cell as a
    general-dynamic tls_index); unnamed code = a difference; unnamed writable data outside PT_GNU_RELRO = a difference;
    unnamed read-only data by the bytes a load reads, else the C-STRING RULE (the pool owner's option B: bytes before
    the first NUL all printable and that NUL inside the region -> the C string INCLUDING its NUL), else the full region
    to the next FUNC / OBJECT start; every content read on FILE bytes only (never the loader's zero-fill).
 3. ON TOP of tsame, only where it refuses an unnamed .rodata / .data.rel.ro target:
    a. a JUMP TABLE whose entry count the dispatch's bound check gives (or read while the X entry points into the X
       function), every entry the same function-relative offset on both sides -> the same target;
    b. a POINTER TABLE with a bound check, every 8-byte entry equal or naming the same qualified symbol+offset;
    c. an INITIALIZER whose memcpy length is known, every 8-byte word equal or naming the same qualified symbol+offset;
    d. UNMEASURED in place of tsame's 'data-differs' for an address-taken target whose two regions (to the next FUNC /
       OBJECT start) are not equally long: the object's extent is not in the symbol table, so jtcheck cannot say.
 4. A function name that several sized FUNC symbols carry in either image is SKIPped unless given as name{file}.
 OUTPUT: one line per function (lo12 pairs, jal, target differs, target unmeasured, unpaired, C-string acceptances,
 tables), then DIFF / UNMEASURED / UNPAIRED lines, ACCEPT lines for every acceptance that is not a name, and one CSTR
 row per C-string acceptance in strictcmp2's format (function, pair, word offset, addr1, addr2, length, hex, repr).
 Settled = target differs, target unmeasured, unpaired and REAL all 0.
usage: [STRICT_LITERAL=1] jtcheck.py X_ELF Y_ELF fn1,fn2{file},...   (strictcmp2.py, drvcmp.py,
       repin_check-4c05cadaeba3.py, bytecmp-1480ca2faea0.py beside it; X_ELF and Y_ELF carry .symtab)"""
import sys, os, hashlib
import importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
for _f, _want in (('strictcmp2.py', '5f6c05791a3ffcf6d4cd35ddbda03675a3ed9b274a07169e2292a7c36b0d8bbc'),
                  ('drvcmp.py', '89ca4b797ed737e4cfef64016d74febd46965baf758b175b446928f0f212e5c4')):
    _got = hashlib.sha256(open(os.path.join(HERE, _f), 'rb').read()).hexdigest()
    if _got != _want: raise SystemExit('jtcheck.py: %s has sha256 %s, want %s' % (_f, _got, _want))
spec = importlib.util.spec_from_file_location('strictcmp2', os.path.join(HERE, 'strictcmp2.py'))
dc = importlib.util.module_from_spec(spec); spec.loader.exec_module(dc)
Img, bc_words, sx = dc.Img, dc.bc_words, dc._g['sx']
WRITES_RD = dc._bc['WRITES_RD']
X, Y = Img(sys.argv[1]), Img(sys.argv[2])
LO12 = (0x13, 0x03, 0x23, 0x67, 0x07, 0x27)

def qname_ok(vx, vy, ex, ey):
    """an 8-byte table entry / initializer word: equal file bytes, or both addresses (inside a section) of the same
    qualified symbol+offset (never an unnamed one)"""
    if ex == ey: return True
    if len(ex) < 8 or X.sec(vx) is None or Y.sec(vy) is None: return False
    rx, ry = dc.qres(X, vx), dc.qres(Y, vy)
    return rx is not None and rx == ry and not rx.startswith('(')

def table(fx, fy, ax, ay, nmax=None):
    """(kind, n, ok, cases) or None. Jump tables: 8-byte absolute or 4-byte relative entries read while the X entry
    points into the X function (nmax: the bound check's count), compared as function-relative offsets. Pointer tables
    (only with a bound check, and only when the 4-byte relative reading gives no jump table): 8-byte entries by
    qname_ok. File bytes only."""
    ptr = None
    for size, rel in ((8, False), (4, True)):
        n = 0; ok = True; cases = set(); kind = None
        while n < (nmax or 1024):
            ex = dc.frd(X, ax + size * n, size); ey = dc.frd(Y, ay + size * n, size)
            if ex is None or ey is None: break
            if rel:
                vx = ax + int.from_bytes(ex, 'little', signed=True); vy = ay + int.from_bytes(ey, 'little', signed=True)
            else:
                vx = int.from_bytes(ex, 'little'); vy = int.from_bytes(ey, 'little')
            if fx[0] <= vx < fx[0] + fx[1] and kind in (None, 'jump'):
                kind = 'jump'; cases.add(vx - fx[0])
                if vy - fy[0] != vx - fx[0]: ok = False
            elif nmax and not rel and kind in (None, 'ptr') and (ex == ey or X.sec(vx) is not None):
                kind = 'ptr'
                if not qname_ok(vx, vy, ex, ey): ok = False
            else:
                break
            n += 1
        if n and (nmax is None or n == nmax):
            t = ('%s%d-%s' % ('rel' if rel else 'abs', size, kind), n, ok, cases)
            if kind == 'ptr': ptr = t
            elif ptr is None or n >= 2: return t
    return ptr

def blob(ax, ay, L):
    """L bytes as 8-byte words, each by qname_ok; a read past the file bytes is a difference"""
    ok = True
    for k in range(0, L, 8):
        ex = dc.frd(X, ax + k, min(8, L - k)); ey = dc.frd(Y, ay + k, min(8, L - k))
        if ex is None or ey is None or not qname_ok(int.from_bytes(ex, 'little'), int.from_bytes(ey, 'little'), ex, ey):
            ok = False
    return ok

def same_target(fx, fy, tx, ty, word, nmax=None, blen=None):
    """-> (verdict, what, table, acceptance): verdict True / False / None (UNMEASURED). tsame decides first; on top of
    it, for an unnamed .rodata / .data.rel.ro target it refuses: a jump table, a pointer table, an initializer, or
    UNMEASURED when the two regions are not equally long. acceptance = (kind, x, y, info) for anything but a name."""
    ok, kind, rx, ry, info = dc.tsame(X, tx, Y, ty, word)
    unnamed_data = kind in ('full', 'cstr', 'data-differs', 'cstr-differs')
    ro = X.sec(tx) in ('.rodata', '.data.rel.ro')
    t = table(fx, fy, tx, ty, nmax) if unnamed_data and ro else None
    if ok:
        return True, '%s %s' % (kind, rx), t, (None if kind == 'name' else (kind, tx, ty, rx if kind == 'gotval' else info))
    if t and t[1] >= 2 and (t[0].endswith('jump') or t[2]):
        return t[2], 'table %s %d entries%s' % (t[0], t[1], ' (bound check)' if nmax else ''), t, \
            (('table', tx, ty, '%s %d entries' % (t[0], t[1])) if t[2] else None)
    if unnamed_data and ro and blen:
        if blob(tx, ty, blen):
            return True, 'initializer %d bytes (memcpy length)' % blen, t, ('initializer', tx, ty, blen)
    if kind == 'data-differs' and dc.loadwidth(word) is None:
        ra, rb = dc.region(X, tx), dc.region(Y, ty)
        if ra is not None and rb is not None and len(ra) != len(rb):
            return None, 'unnamed %s: region %d | %d bytes to the next FUNC / OBJECT start (extent unknown)' % (
                rx, len(ra), len(rb)), t, None
        if open_string(X, tx) or open_string(Y, ty):
            return None, 'unnamed %s: printable bytes with no NUL before the region or the file bytes end (C-string ' \
                'rule cannot bound it)' % rx, t, None
    return False, '%s: %s | %s' % (kind, rx, ry), t, None

def open_string(I, a):
    """the region at a (to the next FUNC / OBJECT start or the end of a's section) runs past its PT_LOAD's file bytes,
    and the file bytes from a to their end are non-empty, all printable and hold no NUL: a C string whose NUL no file
    holds, so the C-string rule cannot bound it (the kit Img.rd's zero-fill would supply a NUL; jtcheck does not use it)"""
    s = next(((v, z) for nm, v, z in I.secs if v <= a < v + z), None)
    g = next(((v, fz, d) for v, fz, d in I.segs if v <= a < v + fz), None)
    if s is None or g is None: return False
    st = dc._meta(I)['starts']; k = dc.bisect.bisect_right(st, a)
    rend = min(s[0] + s[1], st[k] if k < len(st) else s[0] + s[1])
    if rend <= g[0] + g[1]: return False
    b = g[2][a - g[0]:]
    return bool(b) and b'\0' not in b and all(ch in dc.PRINTABLE for ch in b)

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

def jal_target(base, o, x):
    return base + o + sx(((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11 | ((x >> 21) & 0x3ff) << 1, 21)

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

def fsymq(I, spec):
    """(addr, size) of the sized FUNC named spec (or name{file}); None if absent; 'ambiguous' if several, unqualified.
    An unqualified unique name goes through I.fsym (the same answer: the one sized FUNC of that name)."""
    nm = spec.split('{')[0]
    c = sorted({(v, z) for v, z, t in I.byname.get(nm, []) if t == 'STT_FUNC' and z > 0})
    if '{' in spec: c = [(v, z) for v, z in c if dc.qname(I, nm, v) == spec]
    elif len(c) <= 1: return I.fsym(nm)
    return None if not c else c[0] if len(c) == 1 else 'ambiguous'

def run(fn):
    fx, fy = fsymq(X, fn), fsymq(Y, fn)
    if 'ambiguous' in (fx, fy):
        print('%s\tSKIP AMBIGUOUS: several sized FUNC symbols carry this name (give it as name{file})' % fn); return
    if not fx or not fy or fx[1] != fy[1]:
        print('%s\tSKIP %s %s' % (fn, fx, fy)); return
    bx, by = dc.frd(X, *fx), dc.frd(Y, *fy)
    if bx is None or by is None:
        print('%s\tUNREADABLE (function bytes not all file bytes)' % fn); return
    wx, wy = bc_words(bx), bc_words(by)
    def mask(op): return 0xfff if op in (0x17, 0x6f) else 0x01fff07f if op in (0x23, 0x27) else 0x000fffff
    shape = [i for i, ((o, x, n), (_, y, _)) in enumerate(zip(wx, wy)) if x != y and (
        (x & 0x7f) != (y & 0x7f) or (x & 0x7f) not in LO12 + (0x17, 0x6f) or (x & mask(x & 0x7f)) != (y & mask(x & 0x7f)))]
    if shape:
        print('%s\tREAL difference (not immediate-only) at %s' % (fn, [hex(wx[i][0]) for i in shape[:6]])); return
    st_all = dc._g['bc_states'](wx)
    onreg = dc.auipc_reg_words(wx)
    rvc = any(n == 2 for o, x, n in wx)   # 2-byte parcels are not decoded here: no basic-block pairing then
    base_labels = set()
    for o, x, n in wx:
        op = x & 0x7f
        if op == 0x63:
            base_labels.add(o + sx(((x >> 31) & 1) << 12 | ((x >> 7) & 1) << 11 | ((x >> 25) & 0x3f) << 5 | ((x >> 8) & 0xf) << 1, 13))
        elif op == 0x6f:
            t = jal_target(0, o, x)
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
            if k is None and not rvc: k = bb_auipc(wx, i, rs1, labels)
            if k is None:
                if x != y: unpaired.append('+%#x %08x vs %08x op %#x rs1 x%d' % (o, x, y, op, rs1))
                elif i in onreg: unpaired.append('+%#x %08x (equal) op %#x rs1 x%d: base register last written by an auipc' % (o, x, op, rs1))
                continue
            pairs[i] = (hi_lo(fx[0], wx, k, x, op), hi_lo(fy[0], wy, k, y, op), k)
        newcases = set(cases); res = []; acc = []
        for i, (tx, ty, k) in sorted(pairs.items()):
            ok, what, t, a = same_target(fx, fy, tx, ty, wx[i][1], bound(wx, k), memcpy_len(wx, i))
            if t and t[0].endswith('jump'): newcases |= t[3]
            res.append((wx[i][0], ok, what, wx[i][1] != wy[i][1]))
            if ok and a: acc.append((a[0], hex(wx[i][0]), a[1], a[2], a[3]))
        if newcases == cases: break
        cases = newcases
    used = {k for (tx, ty, k) in pairs.values()}
    for k, (o, x, n) in enumerate(wx):
        if n == 4 and x & 0x7f == 0x17 and (x >> 7) & 31 and k not in used:
            unpaired.append('+%#x %08x vs %08x auipc consumed by no pair' % (o, x, wy[k][1]))
    jres = []
    for i, ((o, x, n), (_, y, _)) in enumerate(zip(wx, wy)):
        if n == 4 and x & 0x7f == 0x6f:
            tx, ty = jal_target(fx[0], o, x), jal_target(fy[0], o, y)
            if fx[0] <= tx < fx[0] + fx[1] or fy[0] <= ty < fy[0] + fy[1]:
                jres.append((o, tx - fx[0] == ty - fy[0], 'jal +%#x | +%#x (in-function)' % (tx - fx[0], ty - fy[0]), x != y))
            else:
                ok, kind, rx, ry, info = dc.tsame(X, tx, Y, ty, x)
                jres.append((o, ok, 'jal %s: %s | %s' % (kind, rx, ry), x != y))
    bad = [r for r in res + jres if r[1] is False]
    unm = [r for r in res if r[1] is None]
    ncs = sum(1 for a in acc if a[0] == 'cstr')
    tabs = sorted({r[2] for r in res if r[2].startswith('table')})
    print('%s\tX %#x Y %#x size %d\tlo12 pairs %d (in differing words %d)\tjal %d (differing %d)\ttarget differs %d\t'
          'target unmeasured %d\tunpaired %d\tC-string acceptances %d\t%s'
          % (fn, fx[0], fy[0], fx[1], len(res), sum(1 for r in res if r[3]), len(jres), sum(1 for r in jres if r[3]),
             len(bad), len(unm), len(unpaired), ncs, tabs))
    for o, ok, what, d in bad: print('   DIFF +%#x %s' % (o, what))
    for o, ok, what, d in unm: print('   UNMEASURED +%#x %s' % (o, what))
    for u in unpaired: print('   UNPAIRED ' + u)
    for k, o, x, y, info in acc:
        if k != 'cstr': print('   ACCEPT %s %s +%s [%#x|%#x] %s' % (fn, k, o, x, y, info))
    for r in dc.cstr_rows(fn, 'X:Y', acc): print(r)

if __name__ == '__main__':
    for f in sys.argv[3].split(','):
        run(f)
