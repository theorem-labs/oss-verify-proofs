#!/usr/bin/env python3
"""settle.py -- a named measurement for each target pair that the comparison kit (cmpkit 86da41d3ef68) reports as
`data-differs` in a by-name function compare. Read-only. It never changes a kit verdict: the kit's row stays as the
kit wrote it; this tool adds one ACCEPT row per target pair with the extent the code reads, the evidence for that
extent (instruction pcs, widths, index bounds, readers), the bytes of that extent in both images, and a verdict.

It loads jtcheck 226254f48c97 (this record's copy, tools/jtcheck.py, which sha-checks and loads strictcmp3.py and
drvcmp.py) from its own directory: strictcmp3's tcmp lists the target pairs; a table's entry size and count are those
jtcheck's own proof gives on both images (luitrace.table_proof2: Flow.prove), and its `table` reads them; its
`copy_len` gives the extent of a memcpy initializer.
The readers are traced in X's function only: the kit has already found X's and Y's functions equal outside these
target words (same size, every other word and every named target the same), so Y's code reads the same way.

Classes, in this order:
  TABLE      the address is indexed (`add`), jtcheck 226254f48c97 PROVES the table's entry size and count on both
             images (the bound on every path of its CFG: luitrace.table_proof2), and its table() reads a jump table
             (each entry the same function-relative offset), a string table (each entry's C string, or equal bytes
             where an entry is not a C string) or a pointer table (each entry the same named symbol+offset, or equal
             bytes) over exactly those entries. One ENTRY row per entry, with its target in both images.
  INDEXED    every use of the address is `add rB, rT, rS` followed by a load `l* rD, off(rB)` of width w in the same
             block, where rS is `srli *, 58` (index 0..63), `andi *, M` (index 0..M), or `slli rI, s` with rI guarded
             by `bltu rK, rI` / `bgeu rI, rK`, rK = `addi rK, zero, K`, on the only path to the load (index 0..K or
             0..K-1). The extent is the bytes from off to the last index's entry end.
  CSTR       every reader of the address reads it as a C string: a `const char *` parameter of the callee (its
             mangled name, or its C prototype: table PARAMS), a `%s` argument of a printf-like callee (the format
             strings that reach the call, read in X and Y), an `lb`/`lbu` inside the string, a pointer compare (no
             read), a register live at a call that does not take it (PARAMS gives the argument count), a stack spill
             and its reloads, or a return value whose callers do one of these (followed 2 levels). The extent is the
             bytes up to and including the first NUL.
  UNSETTLED  anything else, with the reason: the kit row stays `other`.
  REFUSED    in place of UNSETTLED, for an indexed address (`add`) jtcheck 226254f48c97 proves no table shape for and
             no class above settles: NO PROOF, not a difference (tools/handtable.py may settle the table by hand).
usage: settle.py X_ELF Y_ELF FN1,FN2,...    (X_ELF, Y_ELF: unstripped, with .symtab; FN may be name{file})"""
import importlib.util, os, re, runpy, sys, collections

HERE = os.path.dirname(os.path.abspath(__file__))
_argv = sys.argv[:]
sys.argv = [os.path.join(HERE, 'jtcheck.py'), _argv[1], _argv[2], '']
jt = runpy.run_path(os.path.join(HERE, 'jtcheck.py'), run_name='jtcheck_lib')
sys.argv = _argv
dc, X, Y = jt['dc'], jt['X'], jt['Y']
sx, bc_words = jt['sx'], jt['bc_words']
I = {'X': X, 'Y': Y}
_spec = importlib.util.spec_from_file_location('luitrace', os.path.join(HERE, 'luitrace.py'))
lt = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(lt)      # table_proof2: the one table rule
RN = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
      's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
CALLER_SAVED = {1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31}

# callee -> (argument registers it takes, `this` included; indices that are `const char *`;
#            printf-like (format index, first variadic index) or None; evidence)
PARAMS = {
    '_ZN11__sanitizer6PrintfEPKcz': (1, {0}, (0, 1), 'Printf(const char *format, ...): PKcz'),
    '_ZN11__sanitizer6ReportEPKcz': (1, {0}, (0, 1), 'Report(const char *format, ...): PKcz'),
    '_ZN11__sanitizer20InternalScopedString7AppendFEPKcz': (2, {1}, (1, 2),
        'InternalScopedString::AppendF(this, const char *format, ...): member, PKcz'),
    '_ZN11__sanitizer20InternalScopedString6AppendEPKc': (2, {1}, None,
        'InternalScopedString::Append(this, const char *): member, PKc'),
    '_ZN11__sanitizer15internal_strcmpEPKcS1_': (2, {0, 1}, None, 'internal_strcmp(const char *, const char *): PKc S1_=PKc'),
    '_ZN11__sanitizer16internal_strncmpEPKcS1_m': (3, {0, 1}, None,
        'internal_strncmp(const char *, const char *, unsigned long): PKc S1_=PKc m'),
    '_ZN11__sanitizer16internal_strncpyEPcPKcm': (3, {1}, None, 'internal_strncpy(char *, const char *, unsigned long): Pc PKc m'),
    '_ZN6__asan15PrintMemoryByteEPN11__sanitizer20InternalScopedStringEPKchbS4_': (5, {1, 4}, None,
        'PrintMemoryByte(InternalScopedString *, const char *, u8, bool, const char *): PKc h b S4_=PKc'),
    '_ZN6__asan23PrintAddressDescriptionEmmPKc': (3, {2}, None, 'PrintAddressDescription(uptr, uptr, const char *): m m PKc'),
    '_ZN11__sanitizer18SuppressionContext5ParseEPKc': (2, {1}, None, 'SuppressionContext::Parse(this, const char *): member, PKc'),
    '_ZN11__sanitizer10FlagParser11ParseStringEPKcS2_': (3, {1, 2}, None,
        'FlagParser::ParseString(this, const char *, const char *): member, PKc S2_=PKc'),
    '_ZN6__asanL10RZSize2LogEj': (1, set(), None, 'RZSize2Log(u32): j'),
    '_ZN6__asan21GetCurrentThreadStatsEv': (0, set(), None, 'GetCurrentThreadStats(): v'),
    '_ZN6__asan27ReportNewDeleteTypeMismatchEmmmPN11__sanitizer18BufferedStackTraceE': (4, set(), None,
        'ReportNewDeleteTypeMismatch(uptr, uptr, uptr, BufferedStackTrace *): m m m P'),
    '_ZN11__sanitizer15StaticSpinMutex8LockSlowEv': (1, set(), None, 'StaticSpinMutex::LockSlow(this): member, v'),
    '_ZN11__sanitizer10ReportFile17ReopenIfNecessaryEv': (1, set(), None, 'ReportFile::ReopenIfNecessary(this): member, v'),
    '__fstatat': (4, {1}, None, 'C (musl): int __fstatat(int, const char *restrict, struct stat *restrict, int)'),
    'fstatat': (4, {1}, None, 'C (musl): int fstatat(int, const char *restrict, struct stat *restrict, int)'),
    '__lctrans': (2, {0}, None, 'C (musl): const char *__lctrans(const char *, const struct __locale_map *)'),
    '_ZN11__sanitizer18ReportErrorSummaryEPKcPKNS_10StackTraceES1_': (3, {0, 2}, None,
        'ReportErrorSummary(const char *, const StackTrace *, const char *): PKc PKN..E S1_=PKc'),
    '__strftime_l': (5, {2}, None, 'C (musl): size_t __strftime_l(char *restrict, size_t, const char *restrict, const struct tm *restrict, locale_t)'),
    'strftime_l': (5, {2}, None, 'C (musl): size_t strftime_l(char *restrict, size_t, const char *restrict, const struct tm *restrict, locale_t)'),
}

def callee_info(name):
    if not name or not name.endswith('+0x0'): return None, None
    for nm in name[:-4].split('/'):
        if nm in PARAMS: return nm, PARAMS[nm]
    return name[:-4], None

def dec(x):
    op = x & 0x7f; rd = (x >> 7) & 31; f3 = (x >> 12) & 7; rs1 = (x >> 15) & 31; rs2 = (x >> 20) & 31; f7 = x >> 25
    ii = sx(x >> 20, 12); si = sx(((x >> 25) << 5) | ((x >> 7) & 31), 12)
    if op == 0x37: return 'lui', rd, None, None, sx(x >> 12, 20)
    if op == 0x17: return 'auipc', rd, None, None, sx(x >> 12, 20)
    if op == 0x6f:
        return 'jal', rd, None, None, sx(((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11
                                          | ((x >> 21) & 0x3ff) << 1, 21)
    if op == 0x67: return 'jalr', rd, rs1, None, ii
    if op == 0x63:
        return (['beq', 'bne', 'b?', 'b?', 'blt', 'bge', 'bltu', 'bgeu'][f3], None, rs1, rs2,
                sx(((x >> 31) & 1) << 12 | ((x >> 7) & 1) << 11 | ((x >> 25) & 0x3f) << 5 | ((x >> 8) & 0xf) << 1, 13))
    if op == 0x03: return ['lb', 'lh', 'lw', 'ld', 'lbu', 'lhu', 'lwu', 'l?'][f3], rd, rs1, None, ii
    if op == 0x23: return ['sb', 'sh', 'sw', 'sd', 's?', 's?', 's?', 's?'][f3], None, rs1, rs2, si
    if op == 0x13:
        if f3 == 1: return 'slli', rd, rs1, None, (x >> 20) & 63
        if f3 == 5: return ('srai' if (x >> 30) & 1 else 'srli'), rd, rs1, None, (x >> 20) & 63
        return ['addi', 'i?', 'slti', 'sltiu', 'xori', 'i?', 'ori', 'andi'][f3], rd, rs1, None, ii
    if op == 0x33 and f7 != 1:
        return {0: 'sub' if f7 == 0x20 else 'add', 1: 'sll', 2: 'slt', 3: 'sltu', 4: 'xor',
                5: 'sra' if f7 == 0x20 else 'srl', 6: 'or', 7: 'and'}[f3], rd, rs1, rs2, None
    if op == 0x07: return 'fl', rd, rs1, None, ii
    if op == 0x27: return 'fs', None, rs1, rs2, si
    if op in (0x0f, 0x73): return 'op%#x' % op, None, None, None, None
    return 'op%#x' % op, rd, rs1, (rs2 if op in (0x33, 0x3b, 0x2f, 0x53) else None), None

BRANCH = ('beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu')
STORE = ('sb', 'sh', 'sw', 'sd', 'fs')
LOADW = {'lb': 1, 'lbu': 1, 'lh': 2, 'lhu': 2, 'lw': 4, 'lwu': 4, 'ld': 8}

def writes(m, rd):
    return rd not in (None, 0) and m not in STORE and m not in BRANCH

class Fn:
    def __init__(self, Im, a, z):
        self.I, self.a, self.z = Im, a, z
        self.b = dc.frd(Im, a, z); self.w = bc_words(self.b)
        self.idx = {o: i for i, (o, x, n) in enumerate(self.w)}
        self.t = dc.targets(a, self.b)
        self.d = [dec(x) for o, x, n in self.w]
        self.labels = set(); self._preds = None
        for (o, x, n), (m, rd, r1, r2, im) in zip(self.w, self.d):
            if m in BRANCH or (m == 'jal' and 0 <= o + im < z): self.labels.add(o + im)
        # jump-table cases: every in-function entry of a 4-byte relative or 8-byte absolute table at a read-only
        # target of this function; an indirect jump (jalr zero, not a return) may go to any of them
        self.cases = set()
        for k, (kind, ta) in self.t.items():
            if Im.sec(ta) not in ('.rodata', '.data.rel.ro'): continue
            for size, rel in ((4, True), (8, False)):
                e = 0
                while e < 1024:
                    ex = dc.frd(Im, ta + size * e, size)
                    if ex is None: break
                    v = ta + int.from_bytes(ex, 'little', signed=True) if rel else int.from_bytes(ex, 'little')
                    if not (a <= v < a + z) or (v - a) not in self.idx: break
                    self.cases.add(v - a); e += 1
        self.labels |= self.cases
    def succ(self, i):
        o = self.w[i][0]; m, rd, r1, r2, im = self.d[i]
        nxt = [i + 1] if i + 1 < len(self.w) else []
        if m == 'jal':
            if 0 <= o + im < self.z and rd == 0: return [self.idx[o + im]] if o + im in self.idx else []
            return [] if rd == 0 else nxt
        if m == 'jalr':
            if rd == 0 and r1 != 1: return [self.idx[c] for c in sorted(self.cases)]
            return [] if rd == 0 else nxt
        if m in BRANCH: return nxt + ([self.idx[o + im]] if o + im in self.idx else [])
        return nxt
    def preds(self, i):
        if self._preds is None:
            self._preds = collections.defaultdict(list)
            for j in range(len(self.w)):
                for k in self.succ(j): self._preds[k].append(j)
        return self._preds[i]
    def pc(self, i): return '+%#x' % self.w[i][0]

def reaching_writers(F, i, reg, limit=20000):
    """every word that last writes reg on a path into word i; None if a path reaches the function entry first"""
    out = set(); seen = set(); work = list(F.preds(i))
    if not work and i == 0: return None
    while work:
        j = work.pop()
        if j in seen: continue
        seen.add(j)
        if len(seen) > limit: return None
        m, rd, r1, r2, im = F.d[j]
        if writes(m, rd) and rd == reg: out.add(j); continue
        if m in ('jal', 'jalr') and rd == 1 and reg in CALLER_SAVED: return None
        ps = F.preds(j)
        if not ps: return None
        work += ps
    return out or None

def addr_values(F, i, reg, depth=0):
    """the lo12-target words whose address reg holds at word i (through `addi r, s, 0` copies); None if not all known"""
    ws = reaching_writers(F, i, reg)
    if ws is None or depth > 6: return None
    out = set()
    for j in ws:
        m, rd, r1, r2, im = F.d[j]
        if m == 'addi' and j in F.t: out.add(j)
        elif m == 'addi' and im == 0:
            sub = addr_values(F, j, r1, depth + 1)
            if sub is None: return None
            out |= sub
        else: return None
    return out

def conversions(fmt):
    """the argument kinds a printf format consumes, in order: 's' for a %s string, 'n' for anything else"""
    out = []; k = 0; s = fmt.rstrip(b'\0')
    while k < len(s):
        if s[k:k + 1] != b'%': k += 1; continue
        k += 1
        if s[k:k + 1] == b'%': k += 1; continue
        while k < len(s) and s[k:k + 1] in b'-+ #0': k += 1
        if s[k:k + 1] == b'*': out.append('n'); k += 1
        while k < len(s) and s[k:k + 1].isdigit(): k += 1
        if s[k:k + 1] == b'.':
            k += 1
            if s[k:k + 1] == b'*': out.append('n'); k += 1
            while k < len(s) and s[k:k + 1].isdigit(): k += 1
        while k < len(s) and s[k:k + 1] in b'hlzjtL': k += 1
        c = s[k:k + 1]; k += 1
        out.append('s' if c == b's' else 'p' if c == b'p' else 'n')
    return out

def uses(F, start, reg):
    """every use of the value reg holds after word start: (kind, word index, detail)"""
    out = []; seen = set(); slots = set()
    work = [(j, reg) for j in F.succ(start)]
    while work:
        i, r = work.pop()
        if (i, r) in seen: continue
        seen.add((i, r))
        o = F.w[i][0]; m, rd, r1, r2, im = F.d[i]
        stop = False
        if m == 'addi' and r1 == r and im == 0 and rd:
            for j in F.succ(i): work.append((j, rd))
        elif m == 'jal' and not (0 <= o + im < F.z):
            if 10 <= r <= 17:
                nm, p = callee_info(dc.qres(F.I, F.a + o + im))
                if p and not p[2] and r - 10 >= p[0]: out.append(('live', i, (nm, r - 10, p)))
                else: out.append(('arg', i, (nm, r - 10, p)))
            stop = rd == 0 or r in CALLER_SAVED
        elif m == 'jalr':
            if rd == 0 and r1 == 1:
                if r == 10: out.append(('ret', i, None))
                stop = True
            elif rd == 0 and F.cases:
                if r1 == r: out.append(('other', i, 'jr'))      # the address itself is the jump target
            else:
                if 10 <= r <= 17: out.append(('arg', i, ('(register-indirect)', r - 10, None)))
                stop = rd == 0 or r in CALLER_SAVED
        elif m in LOADW and r1 == r: out.append(('load', i, (m, im)))
        elif m in STORE and r2 == r:
            if r1 == 2 and m == 'sd': slots.add(im); out.append(('spill', i, im))
            else: out.append(('store', i, (m, im, RN[r1])))
        elif m == 'add' and r in (r1, r2): out.append(('add', i, (rd, r2 if r1 == r else r1)))
        elif m in BRANCH and r in (r1, r2): out.append(('cmp', i, m))
        elif r in (r1, r2): out.append(('other', i, m))
        if stop or (writes(m, rd) and rd == r): continue
        for j in F.succ(i): work.append((j, r))
    for i in range(len(F.w)):
        m, rd, r1, r2, im = F.d[i]
        if m == 'ld' and r1 == 2 and im in slots and rd:
            out.append(('reload', i, im)); out += uses(F, i, rd)
    return out

_callers = {}
def callers(Im, fa):
    """(caller Fn, word index) of every direct `jal ra` to fa in Im"""
    if id(Im) not in _callers:
        cs = collections.defaultdict(list)
        for v, z, nm, ty in Im.syms:
            if ty != 'STT_FUNC' or z <= 0: continue
            b = dc.frd(Im, v, z)
            if b is None: continue
            for k, (o, x, n) in enumerate(bc_words(b)):
                if n == 4 and x & 0x7f == 0x6f and (x >> 7) & 31 == 1: cs[v + o + dec(x)[4]].append((v, z, k))
        _callers[id(Im)] = cs
    return [(Fn(Im, v, z), k) for v, z, k in sorted(set(_callers[id(Im)].get(fa, [])))]

def string_readers(F, FY, start, reg, slen, depth=0):
    """(ok, evidence, unknown): the value of reg after word start is read only as a C string of slen bytes"""
    ev, unk = [], []
    for kind, i, d in uses(F, start, reg):
        pc = F.pc(i)
        if kind == 'arg':
            nm, k, p = d
            if p is None: unk.append('%s a%d to %s (no recorded prototype)' % (pc, k, nm)); continue
            nargs, strs, pf, why = p
            if k in strs: ev.append('%s a%d -> %s [%s]' % (pc, k, nm, why)); continue
            if pf and k >= pf[1]:
                fw = addr_values(F, i, 10 + pf[0])
                if not fw: unk.append('%s a%d vararg to %s: the format reaching the call is not known' % (pc, k, nm)); continue
                pos = k - pf[1]; bad = []; fms = []
                for j in sorted(fw):
                    fx = dc.cstring(F.I, F.t[j][1]); fy = dc.cstring(FY.I, FY.t[j][1]) if FY else fx
                    cx = conversions(fx) if fx else None; cy = conversions(fy) if fy else None
                    if fx is None or fx != fy or cx != cy: bad.append((F.pc(j), fx, fy)); continue
                    if pos >= len(cx): fms.append('not consumed by %r (%d conversions) (%s)' % (fx, len(cx), F.pc(j)))
                    elif cx[pos] == 's': fms.append('%%s of %r (%s)' % (fx, F.pc(j)))
                    elif cx[pos] == 'p': fms.append('%%p of %r: the pointer value, no byte read (%s)' % (fx, F.pc(j)))
                    else: bad.append((F.pc(j), fx, fy))
                if bad: unk.append('%s a%d vararg #%d to %s: format %s' % (pc, k, pos, nm, bad)); continue
                ev.append('%s a%d -> %s vararg #%d: %s' % (pc, k, nm, pos, ' / '.join(fms))); continue
            unk.append('%s a%d -> %s: not a const char * argument [%s]' % (pc, k, nm, why))
        elif kind == 'live':
            nm, k, p = d; ev.append('%s a%d live at a call to %s, which takes %d argument registers [%s]' % (pc, k, nm, p[0], p[3]))
        elif kind == 'load':
            m, im = d
            if m in ('lb', 'lbu') and 0 <= im < slen: ev.append('%s %s %d(addr): 1 byte inside the string' % (pc, m, im))
            else: unk.append('%s %s %d(addr)' % (pc, m, im))
        elif kind == 'cmp': ev.append('%s %s on the address (pointer compare, reads no byte)' % (pc, d))
        elif kind in ('spill', 'reload'): ev.append('%s %s %d(sp)' % (pc, kind, d))
        elif kind == 'ret':
            if depth >= 2: unk.append('%s returned (callers not followed past 2 levels)' % pc); continue
            cs = callers(F.I, F.a)
            if not cs: unk.append('%s returned; no direct caller' % pc); continue
            for G, k in cs:
                where = '%s returned to %s %s' % (pc, dc.qres(G.I, G.a)[:-4], G.pc(k))
                gq = jt['fsymq'](Y, dc.qres(G.I, G.a)[:-4])
                gy = Fn(Y, *gq) if gq and gq != 'ambiguous' and gq[1] == G.z else None
                ok2, ev2, un2 = string_readers(G, gy, k, 10, slen, depth + 1)
                ev += ['%s: %s' % (where, e) for e in ev2]
                unk += ['%s: %s' % (where, u) for u in un2]
                if not ev2 and not un2: ev.append('%s: result not used' % where)
        else:
            unk.append('%s %s %s' % (pc, kind, d))
    return not unk and bool(ev), ev, unk

def guard_count(F, j, ri):
    """index count from a guard on ri before word j: `bltu rK, ri` -> K+1, `bgeu ri, rK` -> K, rK = addi rK, zero, K;
    the guard's fall-through must be the only way to word j (no label between them, ri not written)"""
    for b in range(j - 1, max(-1, j - 16), -1):
        if F.w[b + 1][0] in F.labels and b + 1 <= j: return None
        mb, rdb, b1, b2, _ = F.d[b]
        if writes(mb, rdb) and rdb == ri: return None
        if mb in ('bltu', 'bgeu') and ri in (b1, b2):
            if (mb == 'bltu' and b2 != ri) or (mb == 'bgeu' and b1 != ri): return None
            rk = b1 if mb == 'bltu' else b2
            ws = reaching_writers(F, b, rk)
            if not ws or len(ws) != 1: return None
            c = ws.pop(); mc, rdc, r1c, _, imc = F.d[c]
            if mc != 'addi' or r1c != 0: return None
            return (imc + 1 if mb == 'bltu' else imc), '%s addi %s,zero,%d; %s %s' % (F.pc(c), RN[rk], imc, F.pc(b), mb)
        if mb in BRANCH or mb in ('jal', 'jalr'): return None
    return None

def indexed(F, start, reg):
    """(lo, hi, evidence): the byte range [lo, hi) the indexed reads cover, or None"""
    us = [u for u in uses(F, start, reg) if u[0] != 'live']
    if not us or any(k != 'add' for k, i, d in us): return None
    lo, hi, ev = None, None, []
    for k, i, (rb, rs) in us:
        ws = reaching_writers(F, i, rs)
        if not ws or len(ws) != 1: return None
        j = ws.pop(); mj, rdj, r1j, _, imj = F.d[j]
        if mj == 'srli' and imj == 58: n, scale, why = 64, 1, '%s srli %s,*,58 (index 0..63)' % (F.pc(j), RN[rs])
        elif mj == 'andi' and 0 <= imj < 4096: n, scale, why = imj + 1, 1, '%s andi %s,*,%d' % (F.pc(j), RN[rs], imj)
        elif mj == 'slli' and imj <= 3:
            g = guard_count(F, j, r1j)
            if not g: return None
            n, scale, why = g[0], 1 << imj, '%s; %s slli %s,%s,%d' % (g[1], F.pc(j), RN[rdj], RN[r1j], imj)
        else: return None
        q = i + 1; hit = None
        while q < len(F.w) and F.w[q][0] not in F.labels:
            mq, rdq, r1q, _, imq = F.d[q]
            if mq in LOADW and r1q == rb: hit = (q, mq, imq); break
            if writes(mq, rdq) and rdq == rb: break
            if mq in BRANCH or mq in ('jal', 'jalr'): break
            q += 1
        if hit is None or n < 1: return None
        q, mq, imq = hit; wd = LOADW[mq]
        a, b = imq, imq + (n - 1) * scale + wd
        lo = a if lo is None else min(lo, a); hi = b if hi is None else max(hi, b)
        ev.append('%s; %s add; %s %s %d(%s) (%d bytes per entry, %d entries)' % (why, F.pc(i), F.pc(q), mq, imq, RN[rb], wd, n))
    return lo, hi, ev

def relstr(F, FY, start, reg, ax, ay):
    """a relative table of string pointers: add rB, rT, rS (rS = slli rI, 2, rI guarded: n entries); lw rE, 0(rB);
    add rP, rT, rE. -> (n, guard evidence, entries, reader evidence, unknown) or None"""
    us = [u for u in uses(F, start, reg) if u[0] != 'live']
    if len(us) != 2 or any(k != 'add' for k, i, d in us): return None
    (k1, i1, (rb, rs)), (k2, i2, (rp, re)) = sorted(us, key=lambda u: u[1])
    ws = reaching_writers(F, i1, rs)
    if not ws or len(ws) != 1: return None
    j = ws.pop(); mj, rdj, r1j, _, imj = F.d[j]
    if mj != 'slli' or imj != 2: return None
    g = guard_count(F, j, r1j)
    ws2 = reaching_writers(F, i2, re)
    if not g or not ws2 or len(ws2) != 1: return None
    q = ws2.pop(); mq, rdq, r1q, _, imq = F.d[q]
    if mq != 'lw' or r1q != rb or imq != 0 or not (i1 < q < i2): return None
    n = g[0]; ents = []
    for e in range(n):
        ex = dc.frd(X, ax + 4 * e, 4); ey = dc.frd(Y, ay + 4 * e, 4)
        if ex is None or ey is None: return None
        vx = ax + int.from_bytes(ex, 'little', signed=True); vy = ay + int.from_bytes(ey, 'little', signed=True)
        sx_, sy_ = dc.frd(X, vx, 4096) or b'', dc.frd(Y, vy, 4096) or b''
        kx, ky = sx_.find(b'\0'), sy_.find(b'\0')
        ents.append((e, ex.hex(), vx, sx_[:kx + 1] if kx >= 0 else None, ey.hex(), vy, sy_[:ky + 1] if ky >= 0 else None))
    lens = [len(e[3]) for e in ents if e[3] is not None]
    ok, ev, unk = string_readers(F, FY, i2, rp, min(lens) if lens else 0)
    why = '%s; %s slli %s,%s,2; %s add; %s lw 0(%s); %s add %s = table + entry' % (
        g[1], F.pc(j), RN[rdj], RN[r1j], F.pc(i1), F.pc(q), RN[rb], F.pc(i2), RN[rp])
    return n, why, ents, ev, unk

def table_entries(fx, fy, ax, ay, kind, n):
    """one row per entry, read as jtcheck's table() read it: a jump case by its function-relative offset, a string
    entry by its C string (jtcheck's own rule for a `str` table), anything else by qname_ok"""
    size = int(kind[3]); rel = kind.startswith('rel'); rows = []
    for e in range(n):
        ex = dc.frd(X, ax + size * e, size); ey = dc.frd(Y, ay + size * e, size)
        if rel: vx = ax + int.from_bytes(ex, 'little', signed=True); vy = ay + int.from_bytes(ey, 'little', signed=True)
        else: vx = int.from_bytes(ex, 'little'); vy = int.from_bytes(ey, 'little')
        if kind.endswith('jump'):
            nx, ny = '%s+%#x' % (dc.qres(X, fx[0])[:-4], vx - fx[0]), '%s+%#x' % (dc.qres(Y, fy[0])[:-4], vy - fy[0])
            same = vx - fx[0] == vy - fy[0]
        elif kind.endswith('str'):
            # the table rule for a `str` table (jtcheck table()): an entry that reads as a C string
            # settles by that string; an entry that is not a C string settles only by equal bytes
            sa, sb = dc.cstring(X, vx), dc.cstring(Y, vy)
            nx = ('C string %r' % sa) if sa is not None else (dc.qres(X, vx) + ' (not a C string)')
            ny = ('C string %r' % sb) if sb is not None else (dc.qres(Y, vy) + ' (not a C string)')
            same = (sa == sb) if sa is not None else (sb is None and ex == ey)
        else:
            nx = dc.qres(X, vx) if X.sec(vx) else 'value ' + ex.hex(); ny = dc.qres(Y, vy) if Y.sec(vy) else 'value ' + ey.hex()
            same = jt['qname_ok'](vx, vy, ex, ey)
        rows.append((e, ex.hex(), vx, nx, ey.hex(), vy, ny, same))
    return rows

def settle(fn, out):
    fx, fy = jt['fsymq'](X, fn), jt['fsymq'](Y, fn)
    if not fx or not fy or 'ambiguous' in (fx, fy) or fx[1] != fy[1]:
        out.append('ROW\t%s\tSKIP %s %s' % (fn, fx, fy)); return
    v, c, cnt, diff = dc.tcmp(I, 'X', fx[0], 'Y', fy[0], fx[1])
    FX, FY = Fn(X, *fx), Fn(Y, *fy)
    states = dc._g['bc_states'](FX.w)
    nset = 0
    for off, ra, rb, kind, info in diff:
        i = FX.idx.get(int(off, 16))
        head = '%s\t%s\t%s' % (fn, off, kind)
        if kind == 'unmeasured' and i is not None and ra.startswith('I/S-type word on an auipc register'):
            # NOT-PCREL: the kit flags the word because, in address order, its base register was last written by an
            # auipc. Measured on the CFG: if no auipc reaches the word in that register, the word is not pc-relative
            # and its bytes must simply be equal.
            mm, rdm, r1m, r2m, imm = FX.d[i]
            ws = reaching_writers(FX, i, r1m) if r1m else None
            wx_, wy_ = FX.w[i][1], FY.w[i][1]
            if ws is not None and not any(FX.d[j][0] == 'auipc' for j in ws):
                ok = wx_ == wy_
                out.append('ACCEPT\t%s\t-\t-\tNOT-PCREL\t%s %s: base %s is written on every path into the word by %s, none an auipc\t4 bytes (the word)\t%08x\t%08x\t%s'
                           % (head, FX.pc(i), mm, RN[r1m], ', '.join('%s %s' % (FX.pc(j), FX.d[j][0]) for j in sorted(ws)),
                              wx_, wy_, 'SETTLED-EQUAL' if ok else 'DIFFERS'))
                nset += ok; continue
        if kind not in ('data-differs', 'cstr-differs') or i is None or i not in FX.t or i not in FY.t:
            out.append('ACCEPT\t%s\t-\t-\tUNSETTLED\tnot an unnamed-data target pair (%s | %s)\t-\t-\t-\tUNSETTLED' % (head, ra, rb)); continue
        tx, ty = FX.t[i][1], FY.t[i][1]
        m, rd, r1, r2, im = FX.d[i]
        loc = '%#x\t%#x' % (tx, ty)
        us = uses(FX, i, rd) if m == 'addi' else []
        # TABLE: jtcheck 226254f48c97's rule: the entry size and count both images PROVE (Flow.prove), and table() reads
        # exactly those entries. An indexed address it does not prove goes on to the other classes; if none settles it,
        # its row is REFUSED: no proof, never a difference.
        refused = None
        ka = states[i].get(r1) if states[i] else None
        if ka is not None and any(u[0] == 'add' for u in us):
            shape = lt.table_proof2(jt, X, FX.w, fx, Y, FY.w, fy, i, tx, ty,
                                    lambda q, n: dc.frd(X, q, n), lambda q, n: dc.frd(Y, q, n))
            t = jt['table'](fx, fy, tx, ty, shape[0], shape[1]) if shape else None
            if t and t[1] >= 2 and (t[0].endswith('jump') or t[2]):
                ents = table_entries(fx, fy, tx, ty, t[0], t[1])
                same = all(e[7] for e in ents) and t[2]
                out.append('ACCEPT\t%s\t%s\tTABLE\tjtcheck table(): %s, %d entries (proven on both images: %s)\t%d bytes\t-\t-\t%s'
                           % (head, loc, t[0], t[1], shape[2], t[1] * int(t[0][3]), 'SETTLED-EQUAL' if same else 'DIFFERS'))
                for e in ents:
                    out.append('ENTRY\t%s\t%s\t%d\tX %s -> %#x %s\tY %s -> %#x %s\t%s'
                               % (fn, off, e[0], e[1], e[2], e[3], e[4], e[5], e[6], 'same' if e[7] else 'DIFFERENT'))
                nset += same; continue
            if shape is None:
                def why(I_, F_, f_, t_):
                    """this image's own answer from 226254: the shape it proves here, or its own refusal reason quoted
                    verbatim (`...`), with what that reason's words name"""
                    p_ = lt.table_proof(jt, I_, F_.w, f_[0], f_[1], i, t_, lambda q, n: dc.frd(I_, q, n))
                    fl = lt._FLOW[(id(I_), f_[0])]
                    if p_ is not None: return 'it proves %d-byte entries, %d of them' % (p_[0], p_[1])
                    if fl.ok: return 'it proves no bound on every path'
                    w_ = fl.why or 'refused'
                    m_ = re.match(r'the store at \+(0x[0-9a-f]+) writes it to memory$', w_)
                    if m_ and int(m_.group(1), 16) in F_.idx:
                        sm, _, s1, s2, si = F_.d[F_.idx[int(m_.group(1), 16)]]
                        return ('`%s`: in its words `it` is a value its value flow cannot rule out as an address inside '
                                'the function, here the %s stored by `%s %s,%d(%s)`; it does not follow that value, so it '
                                'proves no table in that function' % (w_, RN[s2], sm, RN[s2], si, RN[s1]))
                    return '`%s`' % w_
                refused = ('jtcheck 226254f48c97 proves no table shape for the indexed address at %s on both images; its '
                           'own reason, X: %s; Y: %s: no proof, not a difference'
                           % (FX.pc(i), why(X, FX, fx, tx), why(Y, FY, fy, ty)))
        if m != 'addi':
            out.append('ACCEPT\t%s\t%s\tUNSETTLED\tthe target word is %s, not an address\t-\t-\t-\tUNSETTLED' % (head, loc, m)); continue
        # INITIALIZER (jtcheck: memcpy of a constant initializer, each 8-byte word by qname_ok)
        cl = jt['copy_len'](FX.w, i, FX.a); L = cl[0] if cl else None
        cj = next((q for q in range(i + 1, min(len(FX.w), i + 4)) if FX.d[q][0] == 'jal' and FX.d[q][1] == 1), None)
        cn = dc.qres(X, FX.a + FX.w[cj][0] + FX.d[cj][4]) if cj is not None else ''
        if L and rd == 11 and 'memcpy' in cn:
            ok = jt['blob'](tx, ty, L)
            out.append('ACCEPT\t%s\t%s\tINITIALIZER\tjtcheck blob(): %s addi a1 = the address; a2 = %d; %s jal %s (memcpy source a1, %d bytes)\t%d bytes\t%s\t%s\t%s'
                       % (head, loc, FX.pc(i), L, FX.pc(cj), cn, L, L, (dc.frd(X, tx, L) or b'').hex(), (dc.frd(Y, ty, L) or b'').hex(),
                          'SETTLED-EQUAL' if ok else 'DIFFERS'))
            for q in range(0, L, 8):
                ex = dc.frd(X, tx + q, min(8, L - q)) or b''; ey = dc.frd(Y, ty + q, min(8, L - q)) or b''
                vx, vy = int.from_bytes(ex, 'little'), int.from_bytes(ey, 'little')
                nx = dc.qres(X, vx) if len(ex) == 8 and X.sec(vx) else 'value ' + ex.hex()
                ny = dc.qres(Y, vy) if len(ey) == 8 and Y.sec(vy) else 'value ' + ey.hex()
                out.append('ENTRY\t%s\t%s\t+%d\tX %s -> %s\tY %s -> %s\t%s' % (fn, off, q, ex.hex(), nx, ey.hex(), ny,
                           'same' if jt['qname_ok'](vx, vy, ex, ey) else 'DIFFERENT'))
            nset += ok; continue
        # RELSTR
        rs_ = relstr(FX, FY, i, rd, tx, ty)
        if rs_:
            n, why, ents, ev, unk = rs_
            same = all(e[3] is not None and e[3] == e[6] for e in ents)
            verdict = 'DIFFERS' if not same else 'SETTLED-EQUAL' if not unk and ev else 'UNSETTLED'
            cls_ = 'REFUSED' if refused and verdict == 'UNSETTLED' else 'RELSTR'
            out.append('ACCEPT\t%s\t%s\t%s\t%s%s; each entry -> a string read as: %s%s\t%d entries x 4 bytes, each string to its NUL\t-\t-\t%s'
                       % (head, loc, cls_, (refused + '; RELSTR: ') if cls_ == 'REFUSED' else '', why, ' ; '.join(ev) or '-',
                          (' | NOT SHOWN: ' + ' ; '.join(unk)) if unk else '', n, verdict))
            for e in ents:
                out.append('ENTRY\t%s\t%s\t%d\tX %s -> %#x %r\tY %s -> %#x %r\t%s' % (fn, off, e[0], e[1], e[2], e[3], e[4], e[5], e[6],
                           'same' if e[3] is not None and e[3] == e[6] else 'DIFFERENT'))
            nset += verdict == 'SETTLED-EQUAL'; continue
        # INDEXED
        ix = indexed(FX, i, rd)
        if ix:
            lo, hi, ev = ix
            bx, by = dc.frd(X, tx + lo, hi - lo), dc.frd(Y, ty + lo, hi - lo)
            ok = bx is not None and bx == by
            out.append('ACCEPT\t%s\t%s\tINDEXED\t%s\t%d bytes at +%d\t%s\t%s\t%s' % (head, loc, ' ; '.join(ev), hi - lo, lo,
                       bx.hex() if bx else None, by.hex() if by else None, 'SETTLED-EQUAL' if ok else 'DIFFERS'))
            nset += ok; continue
        # CSTR
        rx, ry = dc.frd(X, tx, 4096) or b'', dc.frd(Y, ty, 4096) or b''
        kx, ky = rx.find(b'\0'), ry.find(b'\0')
        if kx < 0 or ky < 0:
            out.append('ACCEPT\t%s\t%s\t%s\t%sno NUL within 4096 file bytes\t-\t-\t-\tUNSETTLED'
                       % (head, loc, 'REFUSED' if refused else 'UNSETTLED', (refused + '; ') if refused else '')); continue
        sxa, sya = rx[:kx + 1], ry[:ky + 1]
        ok, ev, unk = string_readers(FX, FY, i, rd, len(sxa))
        if not ok:
            out.append('ACCEPT\t%s\t%s\t%s\t%sreaders: %s | not shown to read a C string: %s\t%d bytes to the NUL\t%s\t%s\tUNSETTLED'
                       % (head, loc, 'REFUSED' if refused else 'UNSETTLED', (refused + '; ') if refused else '',
                          ' ; '.join(ev) or '-', ' ; '.join(unk) or 'no reader found', len(sxa), sxa.hex(), sya.hex()))
            continue
        same = sxa == sya
        out.append('ACCEPT\t%s\t%s\tCSTR\t%s\t%d bytes (to the NUL)\t%s\t%s\t%s' % (head, loc, ' ; '.join(ev), len(sxa),
                   sxa.hex(), sya.hex(), 'SETTLED-EQUAL' if same else 'DIFFERS'))
        nset += same
    out.append('ROW\t%s\tkit %s with %d target pairs reported\tsettled-equal %d of %d\t%s' % (
        fn, v, len(diff), nset, len(diff), 'ROW SETTLED-EQUAL' if diff and nset == len(diff) else 'ROW NOT SETTLED'))

if __name__ == '__main__':
    print('# X sha256 %s; Y sha256 %s; kit files loaded from the directory of this script' % (
        dc.sha(sys.argv[1])[:12], dc.sha(sys.argv[2])[:12]))
    print('ACCEPT\tfunction\tword\tkit kind\tX target\tY target\tclass\tevidence\textent\tX bytes\tY bytes\tverdict')
    print('ENTRY\tfunction\tword\tentry\tX entry -> target\tY entry -> target\tsame')
    for f in sys.argv[3].split(','):
        out = []; settle(f, out); print('\n'.join(out))
