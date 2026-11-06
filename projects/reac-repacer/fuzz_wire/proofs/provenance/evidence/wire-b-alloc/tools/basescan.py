#!/usr/bin/env python3
"""basescan.py -- shape (h) of the unit owner's ruling: EVERY load / store / AMO / jalr base of the compared functions, lui or not,
named as its FULL address (base value + the instruction's immediate) in X and in Y, and compared. Read-only. Loads
luitrace.py (and through it strictcmp3.py, cmpkit 86da41d3ef68) from its own directory: the compared set, the CFG with
its jump-table and in-function call edges (luitrace.Fn), the decoder and the exact pure-number ALU.

THE BASE VALUE: reaching definitions backwards over the CFG (the edge rules of luitrace.anchor), each definition
evaluated to a symbolic form (anchor, constant):
  auipc (alone, or with its addi / load / store / jalr pair: the kit's own `targets`) -> ('sym', address);
  a load of a .got cell -> ('sym', the address the cell holds); any other load -> ('obj', where it was loaded);
  lui / li -> a number; addi / mv -> the summed immediate; addiw on a number -> sign-extended from 32 bits;
  add / sub / sh1add / sh2add / sh3add / add.uw -> anchor + number (two anchors, or a scaled anchor: unknown); any
  other ALU op -> exact on known numbers, else an unknown NUMBER (an index when added to an anchor); the entry value of
  a0-a7 -> ('obj', parameter), of sp -> ('stack'), of gp -> ('gp': __global_pointer$), of tp -> ('tls'); a0 after a
  direct call -> the callee's own return when every return of the callee is a symbol or a number (callee_return, 3
  calls deep), else ('obj', the callee's return); a loop-carried value -> the forms entering the loop with their
  constants unknown (an index on the same anchor); anything else unknown.
THE NAME of each form (constant + immediate added): sym / number / gp -> the symbol + offset the full address falls in
  (strictcmp3.qres; `absolute 0x..` outside every section); stack -> `sp at entry +N`; tls -> `tp +N`; obj ->
  `<origin> +N`. A form whose constant is unknown keeps only its anchor (`... + an index`).
  An address inside a section that NO symbol covers (qres gives only the section name, or an ambiguous name) is ANON:
  it is shown as `(section)+offset` and never compared by name (the egress re-review, RR1): settle_anon pairs the X and
  Y forms by the word that formed the anchor and compares them by the bytes the instruction reads there, or by jtcheck
  226254f48c97's same_target (a table entry by entry over the shape both images prove, the whole unnamed region...)
  with the settle.tsv row cited.
VERDICT per base, X against Y:
  EQUAL          every form is named by its symbol + offset (or a stack / tp / object anchor) and the X and Y names
                 are the same set;
  EQUAL+INDEX    the same, but a form is anchor + an index (the anchor's name is the same; the index is not named);
  EQUAL+BYTES    an ANON constant address whose bytes (the extent the instruction reads) are equal in X and Y;
  EQUAL+TABLE    an ANON form jtcheck's same_target (or a settle.tsv row) settles;
  DIFFERS        the X and Y names differ (any form), or ANON bytes differ and no table rule settles them;
  NOT CERTIFIED  a form is unknown in X or Y, or an ANON form neither bytes nor a table rule settles (real 0 when the
                 known forms agree).
Output: one ROOTBASE line per base of the 4 roots (every base, in full), then one FN line per compared function
(counts per verdict and per name class), one BASE line per closure base that is not EQUAL, the PRESENT lines (how
often each shape (a)-(h) occurs in the compared set of X and of Y), and TOTAL.
usage: basescan.py X_ELF Y_ELF ROOT1,ROOT2,... [SETTLE_TSV]"""
import collections, importlib.util, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('luitrace', os.path.join(HERE, 'luitrace.py'))
lt = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(lt)
s3 = lt.s3; dec = lt.dec; text = lt.text; M64 = lt.M64; RN = lt.RN

def unk(why): return (('unk', why), None)

def entry(reg):
    if 10 <= reg <= 17: return (('obj', 'parameter %s' % RN[reg]), 0)
    if reg == 2: return (('stack',), 0)
    if reg == 3: return (('gp',), 0)
    if reg == 4: return (('tls',), 0)
    return unk('the entry value of %s' % RN[reg])

def evaluate(F, j, reg, depth, rdep=0):
    """the forms of the value word j writes into reg"""
    o, x, n = F.w[j]; op, rd, f3, r1, r2, f7 = dec(x)
    if j in F.tpc:
        t = F.tpc[j]
        if op == 0x03:
            if F.I.sec(t) == '.got':
                c = s3.frd(F.I, t, 8)
                return {(('sym', int.from_bytes(c, 'little'), ('got', j)), 0)} if c else {unk('an unreadable .got cell')}
            return {(('obj', 'a value loaded from %s' % s3.qres(F.I, t)), 0)}
        return {(('sym', t, ('pair', j)), 0)}
    if op == 0x17: return {(('sym', (F.a + o + (lt.sxv(x >> 12, 20) << 12)) & M64, ('auipc', j)), 0)}
    if op == 0x37: return {(None, (lt.sxv(x >> 12, 20) << 12) & M64)}
    if op in (0x13, 0x1b) and f3 == 0:
        imm = s3._lo12(x)
        base = {(None, 0)} if r1 == 0 else val(F, j, r1, depth + 1, rdep)
        out = set()
        for an, c in base:
            if op == 0x13: out.add((an, None if c is None else (c + imm) & M64))
            elif an is None and c is not None: out.add((None, lt.sxv((c + imm) & 0xffffffff, 32) & M64))
            else: out.add(unk('addiw on an address'))
        return out
    if op in (0x13, 0x1b):
        # slli / srli / srai / andi / ori / xori / slti / sltiu: exact on a known number; on anything else the result is
        # an unknown NUMBER (no anchor): a base made of it alone is UNKNOWN, and added to an anchor it is an index
        return {lt.imm_op(x, an, c) for an, c in ({(None, 0)} if r1 == 0 else val(F, j, r1, depth + 1, rdep))}
    if op in (0x33, 0x3b):
        m = text(x, o).split(' ')[0]
        A = {(None, 0)} if r1 == 0 else val(F, j, r1, depth + 1, rdep)
        B = {(None, 0)} if r2 == 0 else val(F, j, r2, depth + 1, rdep)
        out = set()
        for an, c in lt.combine(A, B, m):
            out.add(unk(an[1]) if an is not None and an[0] == 'ptr' else (an, c))
        return out
    if op == 0x03: return {(('obj', 'a value loaded by `%s` at %s' % (text(x, o), F.pc(j))), 0)}
    if op in (0x6f, 0x67): return {unk('a return address')}
    return {unk('computed by `%s` at %s' % (text(x, o), F.pc(j)))}

_RET = {}
def callee_return(I, ta, rdep):
    """the forms a direct callee at ta returns in a0, when every one of its returns gives a symbol or a number (its own
    returns traced the same way, to 3 calls deep); None otherwise (a parameter, a load, an unknown value, a tail jump)"""
    st = lt.STARTS.get(id(I), {})
    if ta is None or ta not in st or rdep > 3: return None
    key = (id(I), ta)
    if key in _RET: return _RET[key]
    _RET[key] = None                                   # a recursive callee resolves to None
    z = st[ta][0][1]; b = s3.frd(I, ta, z)
    if b is None or any(n == 2 for o, x, n in s3.bc_words(b)): return None
    Fc = lt.Fn(I, ta, z); Fc.vm = {}
    rets = []
    for i, (o, x, n) in enumerate(Fc.w):
        op, rd = x & 0x7f, (x >> 7) & 31
        if s3._isret(x): rets.append(i)
        elif (op == 0x6f and rd == 0 and not 0 <= o + s3._jal_off(x) < len(Fc.b)) or (op == 0x67 and rd == 0 and not Fc.arms):
            return None                                # a tail jump: its target's return is not traced here
    forms = set()
    for i in rets: forms |= val(Fc, i, 10, 0, rdep + 1)
    ok = forms and all(c is not None and (an is None or an[0] == 'sym') for an, c in forms)
    _RET[key] = frozenset(forms) if ok else None
    return _RET[key]

def val(F, k, reg, depth=0, rdep=0):
    """the forms reg may hold at word k (memoized per function); a0 after a direct call is the callee's resolved return
    (callee_return) when it has one"""
    key = (k, reg)
    if key in F.vm: return F.vm[key]
    if depth > 12: return {unk('more than 12 definitions deep')}
    F.vm[key] = {(('loop', key), 0)}               # the value of a loop-carried definition, resolved below
    out = set()
    if reg == 0: out = {(None, 0)}
    else:
        if k == 0: out.add(entry(reg))
        elif not F.pr[k]: out.add(unk('a word no decoded edge reaches'))
        work = [(j, k) for j in F.pr[k]]; vis = set()
        while work:
            j, kk = work.pop()
            if (j, kk) in vis: continue
            vis.add((j, kk))
            o, x, n = F.w[j]; op, rd, f3, r1, r2, f7 = dec(x)
            if op in (0x6f, 0x67) and rd:
                if F.icall.get(j) == kk and kk != j + 1:
                    if reg == rd: out.add(unk('a return address')); continue
                    if j == 0: out.add(entry(reg))
                    work += [(p, j) for p in F.pr[j]]; continue
                if reg in lt.CS:
                    r = callee_return(F.I, F.tgt(j), rdep) if reg == 10 and op == 0x6f else None
                    if r: out |= r
                    else:
                        out.add((('obj', 'the return of %s' % ((F.callee(j) or '?')[:-4] if op == 0x6f else
                                                              'a register-indirect call')), 0) if reg == 10
                                else unk('clobbered by the call at %s' % F.pc(j)))
                    continue
            if s3._writes(x) == reg:
                out |= evaluate(F, j, reg, depth, rdep); continue
            if op == 0x73 and f3 == 0 and reg in (10, 11): out.add(unk('written by the ecall at %s' % F.pc(j))); continue
            if j == 0: out.add(entry(reg))
            elif not F.pr[j]: out.add(unk('a word no decoded edge reaches'))
            work += [(p, j) for p in F.pr[j]]
    # a loop: the forms derived from this value itself (anchor ('loop', key)) widen to the forms that enter the loop with
    # their constants unknown (an index on the same anchor); a number entering it widens to an unknown number
    if any(an is not None and an[0] == 'loop' and an[1] == key for an, c in out):
        base = {(an, c) for an, c in out if not (an is not None and an[0] == 'loop' and an[1] == key)}
        out = base | {(an, None) for an, c in base} if base else {unk('a loop with no value entering it')}
    if len(out) > 16: out = {unk('more than 16 forms')}
    if any(an is not None and an[0] == 'loop' for an, c in out):
        del F.vm[key]                                  # still depends on an enclosing loop being resolved: not cached
    else:
        F.vm[key] = out
    return out

class Namer:
    def __init__(self, I):
        self.I = I
        gp = [v for v, z, n, t in I.syms if n == '__global_pointer$']
        self.gp = gp[0] if len(gp) == 1 else None
        self.tls = sorted((v, z, n) for v, z, n, t in I.syms if t == 'STT_TLS')
    def named(self, a):
        """the symbol + offset of a, `absolute 0x..` outside every section; None when a lies in a section but no single
        symbol covers it (strictcmp3.qres gives the bare section name, or an ambiguous name): such an address is ANON"""
        a &= M64
        if not self.I.sec(a): return 'absolute %#x' % a
        q = s3.qres(self.I, a)
        return None if q is None or q.startswith('(') else q
    def anon(self, a):
        """`(section)+offset` of an address no symbol covers"""
        a &= M64; sec = self.I.sec(a)
        st = [v for n, v, z in self.I.secs if n == sec and v <= a < v + z]
        return '(%s)+%#x' % (sec, a - st[0]) if st else '(%s) %#x' % (sec, a)
    def at(self, a): return self.named(a) or self.anon(a)
    def addr(self, a, key, width):
        """(class, name, payload) of a full address: ADDRESS by symbol, or ANON with a payload the X / Y compare settles"""
        a &= M64; n = self.named(a)
        if n is not None: return ('ADDRESS', n, None)
        return ('ANON', self.anon(a), ('addr', key, a, width))
    def name(self, form, imm, width):
        """(class, name, payload) of one form with the instruction's immediate added; payload None except for ANON"""
        an, c = form
        full = None if c is None else (c + imm) & M64
        if an is None:
            return ('UNKNOWN', 'an unknown number', None) if full is None else self.addr(full, ('number', full), width)
        k = an[0]
        if k == 'unk': return ('UNKNOWN', an[1], None)
        if k == 'loop': return ('UNKNOWN', 'an unresolved loop value', None)
        if k == 'sym':
            w = an[2] if len(an) > 2 else None
            if full is None:
                n = self.named(an[1]); ix = lt.sxv(imm & M64, 64)
                if n is not None: return ('INDEX', '%s + an index %+d' % (n, ix), None)
                return ('ANON', '%s + an index %+d' % (self.anon(an[1]), ix), ('idx', (w, ix), an[1], width))
            return self.addr(an[1] + full, (w, full), width)
        if k == 'gp':
            if self.gp is None: return ('UNKNOWN', 'gp, but no single __global_pointer$ symbol', None)
            if full is None:
                n = self.named(self.gp)
                if n is not None: return ('INDEX', '%s + an index %+d' % (n, lt.sxv(imm & M64, 64)), None)
                return ('UNKNOWN', 'gp + an index, gp covered by no symbol', None)
            return self.addr(self.gp + full, ('gp', full), width)
        if k == 'stack':
            return (('INDEX', 'the stack + an index %+d' % lt.sxv(imm & M64, 64), None) if full is None else
                    ('STACK', 'sp at entry %+d' % lt.sxv(full, 64), None))
        if k == 'tls':
            if full is None: return ('INDEX', 'tp + an index %+d' % lt.sxv(imm & M64, 64), None)
            off = lt.sxv(full, 64)
            sym = [n for v, z, n in self.tls if v <= off < v + max(z, 1)]
            return ('TLS', 'tp %+d%s' % (off, ' (%s)' % '/'.join(sym) if sym else ''), None)
        if k == 'obj':
            return (('INDEX', '%s + an index %+d' % (an[1], lt.sxv(imm & M64, 64)), None) if full is None else
                    ('OBJECT', '%s %+d' % (an[1], lt.sxv(full, 64)), None))
        return ('UNKNOWN', repr(an), None)

def base_of(x):
    """(base register, immediate, kind) of a load / store / AMO / jalr (not a return), else None"""
    op, rd, f3, r1, r2, f7 = dec(x)
    if op in (0x03, 0x07): return r1, s3._lo12(x), 'load'
    if op in (0x23, 0x27): return r1, s3._lo12(x), 'store'
    if op == 0x2f: return r1, 0, 'amo'
    if op == 0x67 and not s3._isret(x): return r1, s3._lo12(x), 'jalr' if rd else 'jump'
    return None

def width_of(x):
    """the number of bytes the instruction reads or writes at its base (a jalr: the 4-byte word it jumps to)"""
    op, f3 = x & 0x7f, (x >> 12) & 7
    if op in (0x03, 0x23): return 1 << (f3 & 3)
    if op in (0x07, 0x27, 0x2f): return 8 if f3 == 3 else 4
    return 4

def one(F, NX, i, r, imm):
    """the (class, name, payload) set of one base, and whether the kit's targets() resolved it (an auipc pair)"""
    o, x, n = F.w[i]; wd = width_of(x)
    if i in F.tpc:                                  # auipc + this word: the kit's own full address (imm included)
        t = F.tpc[i]
        if x & 0x7f == 0x03 and F.I.sec(t) == '.got':
            c = s3.frd(F.I, t, 8)
            if not c: return frozenset({('UNKNOWN', 'an unreadable .got cell', None)}), True
            v = int.from_bytes(c, 'little'); nm = NX.named(v)
            if nm is not None: return frozenset({('ADDRESS', 'the .got cell of %s' % nm, None)}), True
            return frozenset({('ANON', 'the .got cell of %s' % NX.anon(v), ('idx', (('got', i), 0), t, wd))}), True
        return frozenset({NX.addr(t, (('pair', i), 0), wd)}), True
    return frozenset(NX.name(f, imm, wd) for f in val(F, i, r)), False

def verdict(nx, ny):
    """the verdict of the named forms (ANON forms are left to settle_anon)"""
    nx = {(c, n) for c, n, p in nx if c != 'ANON'}; ny = {(c, n) for c, n, p in ny if c != 'ANON'}
    if nx != ny:
        kx = {n for c, n in nx if c != 'UNKNOWN'}; ky = {n for c, n in ny if c != 'UNKNOWN'}
        if any(c == 'UNKNOWN' for c, n in nx | ny) and kx == ky: return 'NOT CERTIFIED'
        return 'DIFFERS'
    if any(c == 'UNKNOWN' for c, n in nx): return 'NOT CERTIFIED'
    if any(c == 'INDEX' for c, n in nx): return 'EQUAL+INDEX'
    return 'EQUAL'

SETTLE = {}                                        # (function, word) -> the settle.tsv ACCEPT row (cross-reference)

def kit_table(FX, FY, j):
    """jtcheck 226254f48c97's judgement of the target pair the auipc pair at word j forms (same_target, with the table
    shape both images prove: luitrace.table_proof2): (True, what) when it settles the pair (a table entry by entry, the
    whole unnamed region, a C string, an initializer...), else (False, what)"""
    if j not in FX.tpc or j not in FY.tpc: return False, 'no auipc pair at the word that forms the anchor'
    jt = lt._jtcheck(); tx, ty = FX.tpc[j], FY.tpc[j]
    def shape():
        return lt.table_proof2(jt, FX.I, FX.w, (FX.a, FX.z), FY.I, FY.w, (FY.a, FY.z), j, tx, ty,
                               lambda q, n, I=FX.I: lt.s3.frd(I, q, n), lambda q, n, I=FY.I: lt.s3.frd(I, q, n))
    ok, what, t, acc = jt['same_target']((FX.a, FX.z), (FY.a, FY.z), tx, ty, FX.w[j][1], shape)
    return ok is True, 'jtcheck same_target at %s: %s' % (FX.pc(j), what)

def settle_anon(qx, FX, FY, nx, ny):
    """X and Y ANON forms (an address in a section that no symbol covers), paired by the word that formed them and their
    offset from it. Each pair settles as BYTES (a constant address: the bytes the instruction reads there are equal in
    X and Y), TABLE (an indexed anchor, or a constant address whose bytes differ: jtcheck 226254f48c97's same_target settles
    the target pair, with the settle.tsv row cited when there is one), or else NOT CERTIFIED (no file bytes to compare,
    or no table rule settles it) / DIFFERS (a pair missing on one side, or constant-address bytes that differ and no
    table rule settles). -> (verdict, evidence)"""
    # paired by (kind, the word that formed the anchor, the offset from it): a constant address and an index into the
    # same object are two different forms, each settled on its own
    ax = {(p[0], p[1]): (n, p) for c, n, p in nx if c == 'ANON'}; ay = {(p[0], p[1]): (n, p) for c, n, p in ny if c == 'ANON'}
    if not ax and not ay: return None, ''
    if set(ax) != set(ay): return 'DIFFERS', 'the unnamed forms do not pair up between X and Y'
    res = []; ev = []
    for key in sorted(ax, key=repr):
        (nxn, px), (nyn, py) = ax[key], ay[key]
        k1 = key[1][0]
        w = k1[1] if isinstance(k1, tuple) and k1[0] in ('pair', 'auipc', 'got') else None
        row = SETTLE.get((qx, '%#x' % FX.w[w][0])) if w is not None else None
        cite = (' [settle.tsv ACCEPT %s %s %s %s]' % (row[1][:60], row[2], row[6], row[-1])) if row else ''
        if px[0] == 'addr':
            bx = s3.frd(FX.I, px[2], px[3]); by = s3.frd(FY.I, py[2], py[3])
            if bx is not None and by is not None and bx == by:
                res.append('BYTES'); ev.append('%s | %s: the %d bytes read there are equal: %s' % (nxn, nyn, px[3], bx.hex())); continue
        ok, what = kit_table(FX, FY, w) if w is not None else (False, 'no auipc word forms it')
        if ok:
            res.append('TABLE'); ev.append('%s | %s: settled by jtcheck 226254f48c97: %s%s' % (nxn, nyn, what, cite)); continue
        if row and row[-1] == 'SETTLED-EQUAL':
            res.append('TABLE'); ev.append('%s | %s: settled by settle.tsv%s (jtcheck alone: %s)' % (nxn, nyn, cite, what)); continue
        if px[0] == 'addr' and bx is not None and by is not None:
            res.append('DIFFERS'); ev.append('%s | %s: the %d bytes differ (%s | %s); %s%s' % (nxn, nyn, px[3], bx.hex(), by.hex(), what, cite))
        else:
            res.append('NOT CERTIFIED'); ev.append('%s | %s: %s; %s%s' % (
                nxn, nyn, 'no file bytes to compare (e.g. .bss)' if px[0] == 'addr' else 'an index into an unnamed object',
                what, cite))
    v = ('DIFFERS' if 'DIFFERS' in res else 'NOT CERTIFIED' if 'NOT CERTIFIED' in res else
         'EQUAL+TABLE' if 'TABLE' in res else 'EQUAL+BYTES')
    return v, ' ;; '.join(ev)

def combine_v(v, va):
    """the named-form verdict v and the ANON verdict va"""
    if va is None: return v
    order = ['DIFFERS', 'NOT CERTIFIED', 'EQUAL+TABLE', 'EQUAL+BYTES', 'EQUAL+INDEX', 'EQUAL']
    return min(v, va, key=order.index)

def fmt(ns): return ' | '.join('%s: %s' % (c, n) for c, n, p in sorted(ns, key=lambda t: (t[0], t[1])))

def present(Im, F, P):
    """count the shapes (a)-(h) that occur in F (one image)"""
    for i, (o, x, n) in enumerate(F.w):
        if n == 2:
            P['g: 2-byte parcels'] += 1
            if (x & 3) == 1 and (x >> 13) & 7 == 3 and (x >> 7) & 31 not in (0, 2): P['g: c.lui'] += 1
            continue
        op, rd, f3, r1, r2, f7 = dec(x)
        if op in (0x03, 0x07, 0x23, 0x27) and s3._lo12(x): P['a: load / store with a nonzero immediate'] += 1
        if op in (0x13, 0x1b) and f3 == 0 and r1 and rd: P['b: addi / addiw with a source register'] += 1
        if op == 0x13 and f3 in (1, 4, 5, 6): P['c: slli / xori / srli / srai / ori'] += 1
        if op in (0x23,) and r1 == 2: P['d: store to sp (a spill slot)'] += 1
        if op == 0x53 and (x >> 27) in (0x1a, 0x1e): P['d: integer -> FP register (fcvt / fmv)'] += 1
        if op == 0x53 and (x >> 27) == 0x1c and f3 == 0: P['d: FP register -> integer (fmv.x)'] += 1
        if op in (0x07, 0x27): P['d: FP load / store'] += 1
        if op == 0x73 and f3 in (1, 2, 3) and r1: P['d: CSR write (csrrw / csrrs / csrrc with rs1 != x0)'] += 1
        if op == 0x73 and f3 in (5, 6, 7) and (x >> 15) & 31: P['d: CSR write by an immediate'] += 1
        if op in (0x03, 0x07, 0x23, 0x27, 0x2f, 0x67) and r1 == 3: P['h: gp-relative base'] += 1
        if op in (0x13,) and f3 == 0 and r1 == 3: P['h: addi from gp'] += 1
        if op in (0x03, 0x07, 0x23, 0x27, 0x2f, 0x67) and r1 == 4: P['h: tp-relative base'] += 1
        if op == 0x33 and 4 in (r1, r2): P['h: add with tp'] += 1
        if op == 0x17: P['h: auipc'] += 1
    if F.jr:
        P['e: indirect jumps (jr, not ret)'] += len(F.jr)
        P['e: jump-table arms found'] += len(F.arms)
        P['e: arms also reached by fall-through or a branch'] += sum(1 for t in F.arms if any(p not in F.jr for p in F.pr[t]))
    P['f: in-function calls'] += len(F.icall)

def main():
    xp, yp, roots = sys.argv[1], sys.argv[2], sys.argv[3].split(',')
    if len(sys.argv) > 4:
        for l in open(sys.argv[4]):
            f = l.rstrip('\n').split('\t')
            if f[0] == 'ACCEPT' and f[1] != 'function': SETTLE[(f[1], f[2])] = f
    X, Y = s3.Img(xp), s3.Img(yp); lt.JTARGS[:] = [xp, yp]
    SX, SY, seen, yof = lt.compared_set(X, Y, roots)
    NX, NY = Namer(X), Namer(Y)
    print('#\tX %s sha256 %s\tY %s sha256 %s\troots %s\tcompared functions %d' % (
        os.path.basename(xp), s3.sha(xp)[:12], os.path.basename(yp), s3.sha(yp)[:12], ','.join(roots), len(seen)))
    print('#\t__global_pointer$ X %s Y %s' % (hex(NX.gp) if NX.gp is not None else '-', hex(NY.gp) if NY.gp is not None else '-'))
    rootaddr = [s3.fcopies(X, r)[0][0] for r in roots]
    order = rootaddr + sorted(a for a in seen if a not in rootaddr)
    tot = collections.Counter(); PX = collections.Counter(); PY = collections.Counter(); cls = collections.Counter()
    for a in order:
        nx, zx = sorted(SX[a])[0]; qx = s3.qname(X, nx, a) or nx; ya = yof.get(a); isroot = a in rootaddr
        if ya is None or SY.get(ya, [(None, -1)])[0][1] != zx:
            print('NOY\t%s\tno Y copy of the same size' % qx); tot['functions without a Y copy'] += 1; continue
        FX, FY = lt.Fn(X, a, zx), lt.Fn(Y, ya, zx)
        FX.vm = {}; FY.vm = {}
        present(X, FX, PX); present(Y, FY, PY)
        if any(n == 2 for o, x, n in FX.w) or any(n == 2 for o, x, n in FY.w):
            print('UNMEASURED\t%s\t2-byte parcels' % qx); tot['functions unmeasured (2-byte parcels)'] += 1; continue
        fc = collections.Counter(); tot['functions'] += 1
        for i, (ox, xx, nn) in enumerate(FX.w):
            bx = base_of(xx)
            if bx is None: continue
            r, imm, kind = bx; by = base_of(FY.w[i][1])
            if by is None or by[0] != r or by[2] != kind or (xx & 0x7f) != (FY.w[i][1] & 0x7f):
                v, kit, anev = 'DIFFERS', False, ''      # not the same kind of base on the same register in Y
                nxs, nys = frozenset({('WORD', '%08x' % xx, None)}), frozenset({('WORD', '%08x' % FY.w[i][1], None)})
            else:
                nxs, kit = one(FX, NX, i, r, imm); nys, _ = one(FY, NY, i, r, by[1])   # each side its own immediate
                va, anev = settle_anon(qx, FX, FY, nxs, nys)
                v = combine_v(verdict(nxs, nys), va)
            fc[v] += 1; tot['bases'] += 1; tot['bases ' + v] += 1
            for c, n, p in nxs: cls[c] += 1
            if anev: tot['bases with an unnamed (ANON) form'] += 1
            if kit: tot['bases the kit resolves (auipc pairs)'] += 1
            line = '%s\t%s\t%s\t`%s`\t%s\t%s\tX: %s\tY: %s%s' % (qx, FX.pc(i), kind, text(xx, ox), v,
                                                                 'kit auipc pair' if kit else 'traced', fmt(nxs), fmt(nys),
                                                                 ('\tunnamed: ' + anev) if anev else '')
            if isroot:
                print('ROOTBASE\t' + line); tot['root bases'] += 1; tot['root bases ' + v] += 1
            elif v != 'EQUAL':
                print('BASE\t' + line)
        print('FN\t%s\t%s\t%s' % (qx, 'root' if isroot else 'closure', '\t'.join('%s %d' % kv for kv in sorted(fc.items()))))
    for k in sorted(set(PX) | set(PY)):
        print('PRESENT\t%s\tX %d\tY %d' % (k, PX.get(k, 0), PY.get(k, 0)))
    print('TOTAL\t%s\t%s' % ('\t'.join('%s %d' % kv for kv in sorted(tot.items())),
                             '\t'.join('names of class %s %d' % kv for kv in sorted(cls.items()))))

if __name__ == '__main__':
    main()
