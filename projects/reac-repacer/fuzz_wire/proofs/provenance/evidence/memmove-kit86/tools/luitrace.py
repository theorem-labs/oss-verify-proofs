#!/usr/bin/env python3
"""luitrace.py -- the hand trace of a lui register, for the rule-8 (lui) rows of cmpkit 86da41d3ef68's strictcmp3.

For one function pair (X, Y; the words already aligned by the kit's bytecmp) and one lui word of it, this follows the
lui's value through EVERY word up to the next write of each register (and stack slot) that holds it, on every path of
the function's control-flow graph (the kit's own successor rule, strictcmp3._succ; a word only an indirect jump reaches
starts with every value live at the function's indirect jumps, as strictcmp3.lui_scan does).

Values are symbolic expressions over these leaves: L<j> (lui word j: imm << 12, the same word in X and Y), A<k> (auipc
word k: pc + imm << 12, each image its own word), constants (addi rd, x0, imm), and UNKNOWN leaves: arg:<reg> (the
register at function entry), ld@<off> (a load's result), ret@<off>:<reg> (a register after a call / ecall at off),
and other writes. The value is carried THROUGH every integer ALU op: addi / addiw / add / sub / sh1add / sh2add /
sh3add / and / or / xor / andi / ori / xori / shifts / mul / div and their 32-bit forms, and through stack spills (a
store of the value to a frame slot and the load of that slot). Every READ of a register that holds a value derived
from the lui is a USE, with its role:
  BASE        rs1 of a load / FP load / store / FP store / jalr / AMO: the full address (base value + imm) is computed
              on BOTH images when every leaf is a lui / auipc / constant, and named by symbol + offset with the kit's
              own naming (strictcmp3.qres, else atname); else the UNKNOWN leaves of the base are printed (the
              pointer the lui value is added to)
  STORE-DATA  the stored register of a store / AMO (not to a tracked frame slot): the store's address is printed
  ARG         a0-a7 at a call (jal / jalr with rd != 0), a tail call (jal x0 out of the function, jalr x0 that is
              not a return) or ecall: the callee is printed (by the kit's targets())
  RET         a0 / a1 at a return
  CMP         a branch operand, or slt / sltu / slti / sltiu (their 0/1 result is not followed)
  OTHER       any other read (csr, an FP move / convert from an integer register)
  THROUGH     an ALU op that writes a derived value into rd (followed further)
A row of the kit is settled from this trace ONLY as the README says: a BASE use by the full address (equal symbol +
offset on both images), every other use by a named class with its citation (tools/luiclass.tsv). This tool computes
and prints; it decides nothing but the full-address equality.
usage: luitrace.py KITDIR X_ELF Y_ELF ROWS [--ypin Y_PIN]
  ROWS: a TSV, one line per lui: tag, function name, X fn address, Y fn address, size, lui word offset (hex)
  --ypin: Y's bytes are taken from this stripped pin (same PT_LOAD layout as Y_ELF, the paircl construction)"""
import sys, os, importlib.util, collections

M64 = (1 << 64) - 1


def load_kit(kit):
    spec = importlib.util.spec_from_file_location('strictcmp3', os.path.join(kit, 'strictcmp3.py'))
    s3 = importlib.util.module_from_spec(spec); spec.loader.exec_module(s3)
    return s3


def sx(v, b):
    v &= (1 << b) - 1
    return v - (1 << b) if v & (1 << (b - 1)) else v


_cs = None


def dis(x, o=0):
    global _cs
    if _cs is None:
        import capstone
        _cs = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)
    r = list(_cs.disasm(x.to_bytes(4, 'little'), o))
    return '%s %s' % (r[0].mnemonic, r[0].op_str) if r else '.word %#010x' % x


RN = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
      's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
CALLER_SAVED = (1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31)
# every integer register a value can be in when control leaves the function or enters a callee. sp / gp / tp (2, 3, 4)
# are the frame and the thread pointers, which this trace follows as such, not as values; x0 is not a register value.
LIVE_REGS = tuple([1] + list(range(5, 32)))
NONARG_REGS = tuple(r for r in LIVE_REGS if not 10 <= r <= 17)
ARGS = tuple(range(10, 18))
MAXSET, MAXDEPTH = 12, 8

# ---- decoding ------------------------------------------------------------------------------------------------------


def fields(x):
    return x & 0x7f, (x >> 7) & 31, (x >> 12) & 7, (x >> 15) & 31, (x >> 20) & 31, x >> 25


def i_imm(x): return sx(x >> 20, 12)


def s_imm(x): return sx(((x >> 25) << 5) | ((x >> 7) & 31), 12)


OPS = {  # (opcode, f3, f7) -> mnemonic for R-type integer ops
    (0x33, 0, 0): 'add', (0x33, 0, 0x20): 'sub', (0x33, 1, 0): 'sll', (0x33, 2, 0): 'slt', (0x33, 3, 0): 'sltu',
    (0x33, 4, 0): 'xor', (0x33, 5, 0): 'srl', (0x33, 5, 0x20): 'sra', (0x33, 6, 0): 'or', (0x33, 7, 0): 'and',
    (0x33, 0, 1): 'mul', (0x33, 1, 1): 'mulh', (0x33, 2, 1): 'mulhsu', (0x33, 3, 1): 'mulhu', (0x33, 4, 1): 'div',
    (0x33, 5, 1): 'divu', (0x33, 6, 1): 'rem', (0x33, 7, 1): 'remu', (0x33, 2, 0x10): 'sh1add', (0x33, 4, 0x10): 'sh2add',
    (0x33, 6, 0x10): 'sh3add', (0x33, 7, 0x20): 'andn', (0x33, 6, 0x20): 'orn', (0x33, 4, 0x20): 'xnor',
    (0x3b, 0, 0): 'addw', (0x3b, 0, 0x20): 'subw', (0x3b, 1, 0): 'sllw', (0x3b, 5, 0): 'srlw', (0x3b, 5, 0x20): 'sraw',
    (0x3b, 0, 1): 'mulw', (0x3b, 4, 1): 'divw', (0x3b, 5, 1): 'divuw', (0x3b, 6, 1): 'remw', (0x3b, 7, 1): 'remuw',
    (0x3b, 0, 4): 'add.uw', (0x3b, 2, 0x10): 'sh1add.uw', (0x3b, 4, 0x10): 'sh2add.uw', (0x3b, 6, 0x10): 'sh3add.uw',
}


def opimm(x):
    op, rd, f3, rs1, rs2, f7 = fields(x)
    if op == 0x13:
        if f3 == 1: return 'slli', (x >> 20) & 63
        if f3 == 5: return ('srai' if (x >> 26) == 0x10 else 'srli'), (x >> 20) & 63
        return {0: 'addi', 2: 'slti', 3: 'sltiu', 4: 'xori', 6: 'ori', 7: 'andi'}[f3], i_imm(x)
    if op == 0x1b:
        if f3 == 1: return 'slliw', (x >> 20) & 31
        if f3 == 5: return ('sraiw' if (x >> 25) == 0x20 else 'srliw'), (x >> 20) & 31
        if f3 == 0: return 'addiw', i_imm(x)
    return None, None


def evalop(m, a, b):
    a &= M64; b &= M64
    w = lambda v: sx(v & 0xffffffff, 32) & M64
    s64 = lambda v: sx(v, 64)
    if m in ('add', 'addi'): return (a + b) & M64
    if m in ('addw', 'addiw'): return w(a + b)
    if m == 'sub': return (a - b) & M64
    if m == 'subw': return w(a - b)
    if m in ('and', 'andi'): return a & b
    if m in ('or', 'ori'): return a | b
    if m in ('xor', 'xori'): return a ^ b
    if m in ('sll', 'slli'): return (a << (b & 63)) & M64
    if m in ('srl', 'srli'): return a >> (b & 63)
    if m in ('sra', 'srai'): return (s64(a) >> (b & 63)) & M64
    if m in ('sllw', 'slliw'): return w(a << (b & 31))
    if m in ('srlw', 'srliw'): return w((a & 0xffffffff) >> (b & 31))
    if m in ('sraw', 'sraiw'): return w(sx(a, 32) >> (b & 31))
    if m == 'sh1add': return ((a << 1) + b) & M64
    if m == 'sh2add': return ((a << 2) + b) & M64
    if m == 'sh3add': return ((a << 3) + b) & M64
    if m == 'mul': return (a * b) & M64
    if m == 'mulw': return w(a * b)
    return None

# ---- expressions ---------------------------------------------------------------------------------------------------
# ('L', j) | ('A', k) | ('C', c) | ('I', i) | ('U', desc) | ('op', m, e1, e2) | ('T', k, srcs)   (T = widened at word k)
# a trace follows the expressions that hold its source word: L<j> for a lui, I<i> for an addi (a string address)


def luis_of(e):
    """the source words (lui L<j> and immediate I<i> leaves) an expression holds"""
    t = e[0]
    if t in ('L', 'I'): return frozenset((e[1],))
    if t == 'T': return e[2]
    if t == 'op': return luis_of(e[2]) | luis_of(e[3])
    return frozenset()


def depth(e):
    return 1 + max(depth(e[2]), depth(e[3])) if e[0] == 'op' else 1


def show(e, w):
    t = e[0]
    if t == 'L': return 'L@%#x(%#x)' % (w[e[1]][0], sx(w[e[1]][1] >> 12, 20) << 12 & M64)
    if t == 'A': return 'A@%#x' % w[e[1]][0]
    if t == 'C': return '%#x' % (e[1] & M64) if abs(sx(e[1] & M64, 64)) > 9 else '%d' % sx(e[1] & M64, 64)
    if t == 'I':
        v = opimm(w[e[1]][1])[1]
        return '%#x' % (v & M64) if abs(v) > 9 else '%d' % v
    if t == 'U': return e[1]
    if t == 'T': return 'WIDENED@%#x{%s}' % (w[e[1]][0], ','.join('w@%#x' % w[j][0] for j in sorted(e[2])))
    return '%s(%s, %s)' % (e[1], show(e[2], w), show(e[3], w))


def has_auipc(e):
    return e[0] == 'A' or (e[0] == 'op' and (has_auipc(e[2]) or has_auipc(e[3])))


def leaves_unknown(e):
    t = e[0]
    if t in ('U', 'T'): return [e]
    if t == 'op': return leaves_unknown(e[2]) + leaves_unknown(e[3])
    return []


def split_terms(e, sign=1):
    """a sum / difference as (constant terms, runtime terms): the top-level add / addi / addiw / sub chain split into
    the terms whose leaves are all lui / auipc / immediates and the terms that hold a runtime value. Any other shape
    (a shift, an and, a multiply) is ONE term, constant or runtime as its own leaves say."""
    if e[0] == 'op' and e[1] in ('add', 'addi', 'addiw', 'sub', 'subw'):
        s2 = -sign if e[1] in ('sub', 'subw') else sign
        a, b = split_terms(e[2], sign), split_terms(e[3], s2)
        return a[0] + b[0], a[1] + b[1]
    return ([(sign, e)], []) if not leaves_unknown(e) else ([], [(sign, e)])


def evaluate(e, w, base):
    """the value of e on one image (its words w, function address base); None when a leaf is unknown"""
    t = e[0]
    if t == 'L': return (sx(w[e[1]][1] >> 12, 20) << 12) & M64
    if t == 'A': return (base + w[e[1]][0] + (sx(w[e[1]][1] >> 12, 20) << 12)) & M64
    if t == 'C': return e[1] & M64
    if t == 'I': return opimm(w[e[1]][1])[1] & M64       # the immediate of word i in THIS image (pc-relative lo12 differ)
    if t == 'op':
        a, b = evaluate(e[2], w, base), evaluate(e[3], w, base)
        return None if a is None or b is None else evaluate_op(e[1], a, b)
    return None


def evaluate_op(m, a, b):
    return evalop(m, a, b)


def mk(m, a, b, k):
    e = ('op', m, a, b)
    if depth(e) > MAXDEPTH:
        return ('T', k, luis_of(e))
    return e


def cap(s, k):
    if len(s) <= MAXSET: return frozenset(s)
    return frozenset({('T', k, frozenset().union(*[luis_of(e) for e in s]))})

# ---- the analysis --------------------------------------------------------------------------------------------------


class NoFixpoint(Exception):
    """the expression dataflow did not settle inside its step budget: the function is reported, never settled"""


class Fn:
    def __init__(self, s3, b, base, kills=None, noret=None):
        """kills(call word offset, register) -> True only when the callee WRITES that register on every path to its
        return (so the value cannot survive the call). When no kills callback is given, a call is taken to clobber the
        caller-saved registers (the psABI convention). With one, the psABI is NOT relied on: a register the callee may
        leave intact stays live and the trace goes on in the caller past the call."""
        self.s3, self.b, self.base, self.kills = s3, b, base, kills
        self.w = s3.bc_words(b)
        self.parcels = any(n == 2 for o, x, n in self.w)
        self.succ = s3._succ(self.w)
        self.off = {o: i for i, (o, x, n) in enumerate(self.w)}
        if noret is not None:
            # a call to a function that never returns (it dies, or tail-calls only into such functions) has no
            # fall-through edge: the word after it is not reached that way, and the values the call would leave are
            # on no path. Without this the trace carries a value along an edge the program cannot take.
            for i, (o, x, n) in enumerate(self.w):
                if n == 4 and (x & 0x7f) in (0x6f, 0x67) and ((x >> 7) & 31) and noret(o):
                    self.succ[i] = [t for t in self.succ[i] if t != i + 1]

    def sp_slot(self, s, r, imm):
        """a frame slot key when register r holds sp_entry + c on every path (one expression), else None"""
        es = s.get(r, frozenset())
        if len(es) != 1: return None
        e, = es; c = 0
        while e[0] == 'op' and e[1] in ('add', 'addi') and e[3][0] in ('C', 'I'):
            c += e[3][1] if e[3][0] == 'C' else opimm(self.w[e[3][1]][1])[1]; e = e[2]
        return ('slot', c + imm) if e == ('U', 'arg:sp') else None

    def step(self, i, s):
        o, x, n = self.w[i]
        out = dict(s)
        if n != 4: return out
        op, rd, f3, rs1, rs2, f7 = fields(x)
        g = lambda r: frozenset({('C', 0)}) if r == 0 else s.get(r, frozenset({('U', 'arg:%s' % RN[r])}))
        val = None
        if op == 0x37: val = {('L', i)}
        elif op == 0x17: val = {('A', i)}
        elif op in (0x13, 0x1b):
            m, imm = opimm(x)
            if m is None: val = {('U', '?@%#x' % o)}
            elif m == 'addi' and rs1 == 0: val = {('C', imm)}
            elif m == 'addi' and imm == 0 and not any(has_auipc(e) for e in g(rs1)): val = set(g(rs1))
            elif m in ('slti', 'sltiu'): val = {('U', '%s@%#x' % (m, o))}
            else: val = {mk(m, e, ('I', i), i) for e in g(rs1)}
        elif op in (0x33, 0x3b):
            m = OPS.get((op, f3, f7))
            if m is None: val = {('U', '?@%#x' % o)}
            elif m in ('slt', 'sltu'): val = {('U', '%s@%#x' % (m, o))}
            else: val = {mk(m, a, c, i) for a in g(rs1) for c in g(rs2)}
        elif op in (0x03,):
            k = self.sp_slot(s, rs1, i_imm(x))
            val = set(s.get(k, frozenset())) | {('U', 'ld@%#x' % o)} if k else {('U', 'ld@%#x' % o)}
        elif op in (0x23,):
            k = self.sp_slot(s, rs1, s_imm(x))
            if k: out[k] = g(rs2) | (s.get(k, frozenset()) if (f3 != 3) else frozenset())
        elif op == 0x2f: val = {('U', 'amo@%#x' % o)}
        elif op == 0x73:
            if f3 == 0:
                out[10] = frozenset({('U', 'ret@%#x:a0' % o)}); out[11] = frozenset({('U', 'ret@%#x:a1' % o)})
            else: val = {('U', 'csr@%#x' % o)}
        elif op in (0x6f, 0x67):
            if rd:
                for r in CALLER_SAVED:
                    if self.kills is None or self.kills(o, r):
                        out[r] = frozenset({('U', 'ret@%#x:%s' % (o, RN[r]))})
                out[rd] = frozenset({('U', 'ret@%#x:%s' % (o, RN[rd]))})
                val = None
        elif op == 0x53 and (x >> 27) in (0x14, 0x18, 0x1c): val = {('U', 'fp@%#x' % o)}
        elif op in (0x07, 0x27, 0x63, 0x0f): val = None
        else:
            if self.s3._writes(x) is not None: val = {('U', '?@%#x' % o)}
        if val is not None and rd:
            out[rd] = cap(val, i)
        if op in (0x6f, 0x67) and rd:
            pass
        out.pop(0, None)
        return out

    def run(self):
        w = self.w
        entry = {r: frozenset({('U', 'arg:%s' % RN[r])}) for r in range(1, 32)}
        ins = [None] * len(w); ins[0] = entry
        roots = sorted(set(range(1, len(w))) - {t for s in self.succ for t in s})
        jr = [i for i, (o, x, n) in enumerate(w) if n == 4 and x & 0x7f == 0x67 and (x >> 7) & 31 == 0 and not self.s3._isret(x)]

        def join(a, c):
            ks = a.keys() | c.keys()
            return {k: cap(a.get(k, frozenset()) | c.get(k, frozenset()), 0) for k in ks}
        work = [0]
        it = 0
        while True:
            while work:
                it += 1
                if it > max(400000, 2000 * len(w)): raise NoFixpoint('luitrace: no fixpoint in %d steps' % it)
                i = work.pop(); out = self.step(i, ins[i])
                for t in self.succ[i]:
                    new = out if ins[t] is None else join(ins[t], out)
                    if new != ins[t]: ins[t] = new; work.append(t)
            u = {}
            for i in jr:
                if ins[i] is not None: u = join(u, self.step(i, ins[i]))
            for t in roots:
                new = u if ins[t] is None else join(ins[t], u)
                if new != ins[t]: ins[t] = new; work.append(t)
            if not work: break
        self.ins = ins
        return ins

    def reads(self, i):
        """[(register, role, extra)] the integer registers word i reads, with their role.
        No ABI convention is assumed: at a `ret` EVERY register that still holds the value goes to the callers (role
        RET), and at a call EVERY register goes into the callee (role ARG for a0-a7, role CALLEE for the others)."""
        o, x, n = self.w[i]
        if n != 4: return []
        op, rd, f3, rs1, rs2, f7 = fields(x)
        r = []
        if op in (0x03, 0x07): r = [(rs1, 'BASE', i_imm(x))]
        elif op == 0x67:
            r = [(rs1, 'BASE', i_imm(x))]
            if self.s3._isret(x): r += [(a, 'RET', a) for a in LIVE_REGS]
            else: r += [(a, 'ARG', a - 10) for a in ARGS] + [(a, 'CALLEE', None) for a in NONARG_REGS]
        elif op in (0x23, 0x27):
            r = [(rs1, 'BASE', s_imm(x))]
            if op == 0x23: r.append((rs2, 'STORE-DATA', s_imm(x)))
        elif op == 0x2f:
            r = [(rs1, 'BASE', 0)]
            if (x >> 27) != 0x02: r.append((rs2, 'STORE-DATA', 0))          # lr.* has no data operand
        elif op == 0x63: r = [(rs1, 'CMP', None), (rs2, 'CMP', None)]
        elif op in (0x13, 0x1b):
            m, imm = opimm(x)
            if m in ('slti', 'sltiu'): r = [(rs1, 'CMP', None)]
            elif m == 'addi' and imm == 0: r = [(rs1, 'THROUGH', 'mv')]
            else: r = [(rs1, 'THROUGH', m)]
        elif op in (0x33, 0x3b):
            m = OPS.get((op, f3, f7), '?')
            if m in ('slt', 'sltu'): r = [(rs1, 'CMP', None), (rs2, 'CMP', None)]
            else: r = [(rs1, 'THROUGH', m), (rs2, 'THROUGH', m)]
        elif op == 0x6f:
            tgt = o + sx(((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11 | ((x >> 21) & 0x3ff) << 1, 21)
            if rd or not 0 <= tgt < len(self.b):
                r = [(a, 'ARG', a - 10) for a in ARGS] + [(a, 'CALLEE', None) for a in NONARG_REGS]
        elif op == 0x73:
            if f3 == 0: r = [(a, 'ARG', a - 10) for a in ARGS]
            elif f3 in (1, 2, 3): r = [(rs1, 'OTHER', 'csr')]
        elif op == 0x53 and (x >> 27) in (0x1a, 0x1e): r = [(rs1, 'OTHER', 'fp-from-int')]
        return [(q, role, e) for q, role, e in r if q]


def callee(F, i, I, s3):
    t = s3._g['targets'](F.base, F.b)
    if i in t:
        a = t[i][1]
        if I.sec(a) == '.got':
            c = s3.frd(I, a, 8)
            a = int.from_bytes(c, 'little') if c else a
        return s3.qres(I, a) or hex(a)
    return 'register-indirect'


def cstr_at(s3, I, a):
    d = s3.frd(I, a, 160)
    if d is None or not s3.readonly(I, a): return None
    k = d.find(b'\0')
    return d[:k] if k >= 0 else None


def trace(s3, IX, IY, xa, ya, size, lui_off, ybytes=None, src='LUI', kills=None, noret=None):
    """-> dict: words (the trace lines), uses [(off, role, reg, info, settled_by_tool, detail)], parcels flag.
    src 'LUI': the value of the lui at lui_off; src 'ADDR': the value the addi at lui_off writes (a string address).
    kills(call offset, register): see Fn. With it the psABI is not relied on and the trace goes on in the caller past
    a call the callee may return the register from."""
    bx = s3.frd(IX, xa, size)
    by = ybytes if ybytes is not None else s3.frd(IY, ya, size)
    FX, FY = Fn(s3, bx, xa, kills, noret), Fn(s3, by, ya)
    res = {'lines': [], 'uses': [], 'parcels': FX.parcels or FY.parcels}
    if FX.parcels or FY.parcels:
        return res
    j = FX.off[lui_off]
    FX.run()
    w = FX.w
    tainted = lambda es: any(j in luis_of(e) for e in es)

    def strargs(s, i):
        """the a0-a3 that hold one constant address of a read-only C string at word i (format strings, names)"""
        out = []
        for r in (10, 11, 12, 13):
            es = s.get(r, frozenset())
            if len(es) == 1:
                v = evaluate(next(iter(es)), FX.w, xa)
                c = cstr_at(s3, IX, v) if v is not None else None
                if c is not None and not tainted(es): out.append('%s=%r' % (RN[r], c[:48]))
        return (' {%s}' % ', '.join(out)) if out else ''
    for i, (o, x, n) in enumerate(w):
        s = FX.ins[i]
        if s is None: continue
        rd_list = FX.reads(i)
        hits = [(q, role, e) for q, role, e in rd_list if tainted(s.get(q, frozenset()))]
        out = FX.step(i, s)
        rd = (x >> 7) & 31
        wrote = s3._writes(x)
        kill = []
        if wrote and wrote != 0 and tainted(s.get(wrote, frozenset())) and not tainted(out.get(wrote, frozenset())):
            kill.append(wrote)
        if x & 0x7f in (0x6f, 0x67) and rd:
            kill += [r for r in CALLER_SAVED if r != wrote and tainted(s.get(r, frozenset()))
                     and not tainted(out.get(r, frozenset()))]
        if x & 0x7f == 0x73 and (x >> 12) & 7 == 0:
            kill += [r for r in (10, 11) if tainted(s.get(r, frozenset()))]
        slot_hit = None
        if x & 0x7f == 0x23:
            k = FX.sp_slot(s, (x >> 15) & 31, s_imm(x))
            if k and tainted(s.get((x >> 20) & 31, frozenset())): slot_hit = k
        if x & 0x7f == 0x03:
            k = FX.sp_slot(s, (x >> 15) & 31, i_imm(x))
            if k and tainted(s.get(k, frozenset())): slot_hit = ('reload', k)
        if i == j or hits or kill or slot_hit:
            notes = []
            for q, role, imm in hits:
                if role == 'STORE-DATA' and slot_hit and slot_hit[0] == 'slot':
                    notes.append('%s SPILL to frame slot entry_sp%+d (followed)' % (RN[q], slot_hit[1])); continue
                if role == 'BASE' and slot_hit: continue
                es = sorted(s.get(q, frozenset()), key=str)
                info, sett, detail = '', None, ''

                def full(imx, imy):
                    vals = [(v, evaluate(v, FX.w, xa), evaluate(v, FY.w, ya)) for v in es]
                    if not all(vx is not None and vy is not None for v, vx, vy in vals): return None, None
                    rows = []; st = set()
                    for v, vx, vy in vals:
                        ax_, ay_ = (vx + imx) & M64, (vy + imy) & M64
                        nx, ny = name(s3, IX, ax_), name(s3, IY, ay_)
                        rows.append('%#x=%s | %#x=%s' % (ax_, nx, ay_, ny))
                        st.add('EQUAL' if nx == ny and not nx.startswith('(') and nx != '?' else
                               'UNNAMED' if nx == ny else 'DIFFERS')
                    return 'FULL-ADDRESS-' + ('EQUAL' if st == {'EQUAL'} else 'DIFFERS' if 'DIFFERS' in st else 'UNNAMED'), '; '.join(rows)
                def term_full(imx, imy):
                    """the sum's CONSTANT part (its lui / auipc / immediate terms) named on both images, with the
                    runtime terms (an index, a pointer) listed: for a base of the shape `object + index`"""
                    rows = []; st = set(); runt = set(); ptr = set()
                    for v in es:
                        cs, us = split_terms(v)
                        # only an AUIPC term is an object address in that image; a lui-only constant is an offset,
                        # which the lui row's own class settles, not a name. A value in the set that holds no such
                        # address at all is a RUNTIME POINTER: it is listed, and the use then needs a class (iii) line
                        # for that pointer beside the named address
                        if not cs or not any(has_auipc(c) for sg, c in cs):
                            if not leaves_unknown(v): return None, None
                            ptr.add(show(v, w)); continue
                        vx = vy = 0
                        for sign, c in cs:
                            ex, ey = evaluate(c, FX.w, xa), evaluate(c, FY.w, ya)
                            if ex is None or ey is None: return None, None
                            vx += sign * ex; vy += sign * ey
                        ax_, ay_ = (vx + imx) & M64, (vy + imy) & M64
                        nx, ny = name(s3, IX, ax_), name(s3, IY, ay_)
                        rows.append('constant part %#x=%s | %#x=%s' % (ax_, nx, ay_, ny))
                        st.add('EQUAL' if nx == ny and not nx.startswith('(') and nx != '?' else
                               'UNNAMED' if nx == ny else 'DIFFERS')
                        runt |= {('%+d*' % sign if sign < 0 else '') + show(u, w) for sign, u in us}
                    if not st: return None, None
                    return ('FULL-ADDRESS-TERM-' + ('EQUAL' if st == {'EQUAL'} else 'DIFFERS' if 'DIFFERS' in st else 'UNNAMED')
                            + ('+POINTER' if ptr else ''),
                            '; '.join(rows) + ('; also a runtime pointer with the same offset: ' + ', '.join(sorted(ptr)) if ptr else '')
                            + ('; runtime terms: ' + ', '.join(sorted(runt)) if runt else ''))
                if role == 'BASE':
                    sett, detail = full(imm, rd_list_imm(FY.reads(i), q))
                    if sett is None:
                        sett, detail = term_full(imm, rd_list_imm(FY.reads(i), q))
                    if sett is None:
                        unk = sorted({show(u, w) for v in es for u in leaves_unknown(v)})
                        sett = 'BASE-UNKNOWN-POINTER'
                        detail = 'base = %s; unknown leaves: %s' % (' | '.join(show(v, w) for v in es), ', '.join(unk))
                    info = 'imm %d' % imm
                elif role in ('ARG', 'STORE-DATA', 'RET', 'CMP', 'OTHER'):
                    if role == 'ARG':
                        info = 'a%d of %s%s' % (imm, callee(FX, i, IX, s3) if (x & 0x7f) in (0x6f, 0x67) else 'ecall', strargs(s, i))
                    elif role == 'STORE-DATA':
                        bs = sorted(s.get((x >> 15) & 31, frozenset()), key=str)
                        dst = [evaluate(v, FX.w, xa) for v in bs]
                        dn = (' = ' + ', '.join(name(s3, IX, (v + imm) & M64) for v in dst)) if bs and None not in dst else ''
                        info = 'stored to %s%+d%s (width %d)' % (' | '.join(show(v, w) for v in bs), imm, dn, 1 << ((x >> 12) & 3))
                    detail = ' | '.join(show(v, w) for v in es)
                    if role in ('ARG', 'STORE-DATA', 'RET') and es and any(has_auipc(v) for v in es):
                        sett, d2 = full(0, 0)                    # an auipc-based value: the full address it holds
                        if sett is None: sett, d2 = term_full(0, 0)
                        if sett: detail += ' = ' + d2
                elif role == 'THROUGH':
                    continue
                res['uses'].append((o, role, RN[q], info, sett, detail))
                notes.append('%s %s %s%s%s' % (RN[q], role, info, (' -> ' + sett) if sett else '', (' [' + detail + ']') if detail else ''))
            thr = [RN[q] for q, role, e in hits if role == 'THROUGH']
            if thr and wrote and tainted(out.get(wrote, frozenset())):
                notes.append('THROUGH %s -> %s = %s' % ('/'.join(sorted(set(thr))), RN[wrote],
                                                      ' | '.join(show(v, w) for v in sorted(out[wrote], key=str))))
            elif thr:
                notes.append('THROUGH %s (result not derived)' % '/'.join(sorted(set(thr))))
            if slot_hit and slot_hit[0] == 'reload':
                notes.append('RELOAD frame slot entry_sp%+d -> %s' % (slot_hit[1][1], RN[rd]))
            if i == j:
                notes.insert(0, ('LUI %s = %#x' % (RN[rd], (sx(x >> 12, 20) << 12) & M64)) if src == 'LUI' else
                             ('SOURCE %s = %s' % (RN[rd], ' | '.join(show(v, w) for v in sorted(out.get(rd, ()), key=str)))))
            if kill:
                notes.append('KILL %s' % ','.join(RN[r] for r in kill))
            res['lines'].append('  +%-6s %08x  %-28s %s' % (hex(o), x, dis(x), '; '.join(notes)))
    return res


def rd_list_imm(rd_list, q):
    for r, role, e in rd_list:
        if r == q and role == 'BASE': return e
    return 0


def reaching_defs(s3, b, reg, at_off):
    """the words that may define integer register reg on some path into the word at at_off (MAY reaching definitions over
    the kit's successor rule; a call defines the caller-saved registers; 'entry' when the entry value may reach; a word
    only an indirect jump reaches starts with the definitions live at the function's indirect jumps)"""
    w = s3.bc_words(b); succ = s3._succ(w)
    ins = [None] * len(w); ins[0] = frozenset({'entry'})
    roots = sorted(set(range(1, len(w))) - {t for s in succ for t in s})
    jr = [i for i, (o, x, n) in enumerate(w) if n == 4 and x & 0x7f == 0x67 and (x >> 7) & 31 == 0 and not s3._isret(x)]

    def step(i, s):
        o, x, n = w[i]
        if n == 4 and (s3._writes(x) == reg or (x & 0x7f in (0x6f, 0x67) and (x >> 7) & 31 and reg in CALLER_SAVED)
                       or (x & 0x7f == 0x73 and (x >> 12) & 7 == 0 and reg in (10, 11))):
            return frozenset({o})
        return s
    work = [0]
    while True:
        while work:
            i = work.pop(); out = step(i, ins[i])
            for t in succ[i]:
                new = out if ins[t] is None else ins[t] | out
                if new != ins[t]: ins[t] = new; work.append(t)
        u = frozenset()
        for i in jr:
            if ins[i] is not None: u |= step(i, ins[i])
        for t in roots:
            new = u if ins[t] is None else ins[t] | u
            if new != ins[t]: ins[t] = new; work.append(t)
        if not work: break
    k = next(i for i, (o, x, n) in enumerate(w) if o == at_off)
    return sorted(ins[k] or (), key=str), w


def callee_of(s3, I, base, b, off):
    """(address, size, name) of the function the call word at off targets (jal / auipc+jalr / .got), else None"""
    t = s3._g['targets'](base, b); w = s3.bc_words(b)
    i = next((k for k, (o, x, n) in enumerate(w) if o == off), None)
    if i is None or i not in t: return None
    a = t[i][1]
    if I.sec(a) == '.got':
        c = s3.frd(I, a, 8); a = int.from_bytes(c, 'little') if c else None
    c = sorted({(v, z, n) for v, z, n, ty in I.syms if v == a and ty == 'STT_FUNC' and z > 0})
    return c[0] if c else None


# Linux RISC-V (generic) syscall numbers -> the argument registers the kernel reads (a0..a(N-1)); the number is in a7.
# Every number that occurs at an ecall in these images is listed. The number and name are musl's
# arch/riscv64/bits/syscall.h.in; N is the argument count of the kernel's SYSCALL_DEFINE<N>(<name>) for that call.
# A number not listed (the generic syscall() / __syscall_cp entry points, where a7 is not a constant) is taken as 6,
# the maximum: fail closed.
SYSCALL_ARGS = {
    23: 1, 24: 3, 25: 3, 29: 3, 34: 3, 35: 3, 46: 2,           # dup, dup3, fcntl, ioctl, mkdirat, unlinkat, ftruncate
    56: 4, 57: 1, 59: 2, 61: 3, 62: 3, 63: 3, 64: 3,           # openat, close, pipe2, getdents64, lseek, read, write
    65: 3, 66: 3, 73: 5, 78: 4, 79: 4, 80: 2,                  # readv, writev, ppoll, readlinkat, newfstatat, fstat
    93: 1, 94: 1, 96: 1, 98: 6, 99: 2, 101: 2,                 # exit, exit_group, set_tid_address, futex,
                                                               # set_robust_list, nanosleep
    113: 2, 117: 4, 119: 3, 123: 3, 124: 0, 130: 2,            # clock_gettime, ptrace, sched_setscheduler,
                                                               # sched_getaffinity, sched_yield, tkill
    132: 2, 134: 4, 135: 4, 163: 2, 164: 2, 165: 2, 167: 5,    # sigaltstack, rt_sigaction, rt_sigprocmask, getrlimit,
                                                               # setrlimit, getrusage, prctl
    169: 2, 172: 0, 173: 0, 178: 0, 179: 1, 198: 3, 214: 1,    # gettimeofday, getpid, getppid, gettid, sysinfo,
                                                               # socket, brk
    215: 2, 216: 5, 220: 5, 221: 3, 222: 6, 226: 3, 233: 3,    # munmap, mremap, clone, execve, mmap, mprotect, madvise
    260: 4, 261: 4,                                            # wait4, prlimit64
}


_CALLERS = {}


def all_callers(s3, I):
    """{callee address: [(caller address, caller size, call word offset, kind)]} over EVERY sized FUNC of the image:
    direct jal / auipc+jalr calls and tail calls, and calls through a .got cell that holds the callee's address."""
    key = id(I)
    if key in _CALLERS: return _CALLERS[key]
    out = collections.defaultdict(list)
    for a, z in sorted({(v, z) for v, z, n, t in I.syms if t == 'STT_FUNC' and z > 0}):
        b = s3.frd(I, a, z)
        if b is None: continue
        w = s3.bc_words(b); t = s3._g['targets'](a, b)
        for i, (o, x, n) in enumerate(w):
            if n != 4 or (x & 0x7f) not in (0x6f, 0x67) or i not in t: continue
            tg = t[i][1]; kind = 'direct'
            if I.sec(tg) == '.got':
                c8 = s3.frd(I, tg, 8)
                if c8 is None: continue
                tg = int.from_bytes(c8, 'little'); kind = '.got'
            out[tg].append((a, z, o, kind))
    _CALLERS[key] = out
    return out


def addr_taken(s3, I, a):
    """every aligned place in the image's loadable FILE bytes that holds the 8-byte little-endian value a (an address
    taken: a function pointer in a table or a vtable, a relocation addend). Empty means no data word holds the
    address, so the direct call sites ARE the complete caller list."""
    pat = a.to_bytes(8, 'little'); hits = []
    for v, fz, d in I.segs:
        k = d.find(pat, 0, fz)
        while k != -1 and len(hits) < 8:
            if k % 4 == 0: hits.append('%#x (%s)' % (v + k, I.sec(v + k)))
            k = d.find(pat, k + 1, fz)
    return hits


def code_refs(s3, I, a):
    """every place in the image's CODE that forms the address a WITHOUT calling it (an auipc + addi pair that makes a
    function pointer, a jump-table entry the kit's targets() binds): such a reference can reach the function in a way
    the direct call sites do not show, so a caller list is complete only when this is empty too."""
    out = []
    for fa, fz in sorted({(v, z) for v, z, n, t in I.syms if t == 'STT_FUNC' and z > 0}):
        b = s3.frd(I, fa, fz)
        if b is None: continue
        w = s3.bc_words(b)
        for i, t in s3._g['targets'](fa, b).items():
            if t[1] != a: continue
            o, x, nn = w[i]
            if (x & 0x7f) in (0x6f, 0x67): continue          # a call or a tail call: a caller, not a reference
            out.append('%s+%#x %s' % (name(s3, I, fa), o, dis(x)))
            if len(out) >= 8: return out
    return out


def reads_after_call(s3, I, a, z, call_off, reg, depth=0):
    """False when, on EVERY path after the call at call_off in the function at a, integer register reg is written
    before it is read (a value the callee left in it dies there); else a reason string naming a read, or
    'RET-LIVE <word>' when no path reads it but some path still holds it at a `ret` or a tail call (the caller is then
    tested one level up). Reads inside a further callee are followed as in callee_reads; the psABI is not relied on."""
    b = s3.frd(I, a, z)
    if b is None: return '%s: bytes not file-backed' % name(s3, I, a)
    F = Fn(s3, b, a)
    if F.parcels: return '%s: 2-byte parcels' % name(s3, I, a)
    w = F.w; succ = F.succ
    slots = spill_slots(s3, F, reg)
    dead = dead_frame_stores(F, reg)
    start = next((i for i, (o, x, n) in enumerate(w) if o == call_off), None)
    if start is None: return '%s: the call word is not in this function' % name(s3, I, a)
    live = [None] * len(w)
    jr = [i for i, (o, x, n) in enumerate(w) if n == 4 and x & 0x7f == 0x67 and (x >> 7) & 31 == 0 and not s3._isret(x)]
    roots = sorted(set(range(1, len(w))) - {t for s in succ for t in s})

    def step(i, v):
        o, x, n = w[i]
        if not v: return False
        if is_restore_load(x, slots, reg): return True
        if s3._writes(x) == reg: return False
        if x & 0x7f in (0x6f, 0x67) and (x >> 7) & 31:
            ce = callee_of(s3, I, a, b, o)
            if ce is not None and callee_kills(s3, I, ce[0], ce[1], reg, depth + 1): return False
        return True
    work = list(succ[start])
    for t in succ[start]: live[t] = True
    while True:
        while work:
            i = work.pop()
            if not live[i]: continue
            out = step(i, live[i])
            for t in succ[i]:
                new = out if live[t] is None else (live[t] or out)
                if new != live[t]: live[t] = new; work.append(t)
        u = any(step(i, live[i]) for i in jr if live[i])
        for t in roots:
            new = u if live[t] is None else (live[t] or u)
            if new != live[t]: live[t] = new; work.append(t)
        if not work: break
    # every live word on every path is examined; the events are not cut off at the first one in word order. A real
    # read anywhere wins over the value being live at a `ret` or at a tail call (`RET-LIVE`: tested one level up),
    # because a read on one path is not undone by another path that only hands the value on
    FA = None; retlive = None
    for i, (o, x, n) in enumerate(w):
        if not live[i]: continue
        if x & 0x7f == 0x73 and (x >> 12) & 7 == 0:
            if FA is None:
                FA = F
                try: FA.run()
                except NoFixpoint: FA.ins = [None] * len(w)
            es = FA.ins[i].get(17, frozenset()) if FA.ins[i] else frozenset()
            num = next(iter(es))[1] if len(es) == 1 and next(iter(es))[0] == 'C' else None
            na = SYSCALL_ARGS.get(num, 6)
            if reg == 17 or (10 <= reg < 10 + na):
                return '%s+%#x ecall (syscall %s, %d argument(s))' % (name(s3, I, a), o, num, na)
            continue
        if o in dead: continue
        for q, role, e in F.reads(i):
            if q != reg: continue
            if role in ('ARG', 'CALLEE') and x & 0x7f in (0x6f, 0x67):
                ce = callee_of(s3, I, a, b, o)
                if ce is None: return '%s+%#x: unresolved call' % (name(s3, I, a), o)
                r = callee_reads(s3, I, ce[0], ce[1], reg, depth + 1)
                if r: return '%s+%#x -> %s' % (name(s3, I, a), o, r)
                if not ((x >> 7) & 31) and not callee_kills(s3, I, ce[0], ce[1], reg, depth + 1):
                    # a TAIL call: the tail callee returns in this function's place and may give the register back
                    # intact, so the value goes on to this function's callers, the same as at a `ret`
                    retlive = retlive or 'RET-LIVE %s+%#x' % (name(s3, I, a), o)
                continue
            if role == 'RET':
                # the caller gives the register back to ITS caller: not a read, but the same test one level up
                retlive = retlive or 'RET-LIVE %s+%#x' % (name(s3, I, a), o)
                continue
            return '%s+%#x %s (%s)' % (name(s3, I, a), o, dis(x), role)
    return retlive or False


def spill_slots(s3, F, reg):
    """the sp-relative slots a function SAVES `reg` in and RESTORES it from (the prologue / epilogue pair of a
    callee-saved register). A store into such a slot is not a read of the value, and the load back is not a new
    value: the function gives the register back untouched, which is what makes the save / restore pattern safe to
    skip without appealing to the psABI."""
    st, ld = set(), set()
    for i, (o, x, n) in enumerate(F.w):
        if n != 4: continue
        if (x & 0x7f) == 0x23 and ((x >> 12) & 7) == 3 and ((x >> 20) & 31) == reg and ((x >> 15) & 31) == 2:
            st.add(s_imm(x))
        if (x & 0x7f) == 0x03 and ((x >> 12) & 7) == 3 and ((x >> 7) & 31) == reg and ((x >> 15) & 31) == 2:
            ld.add(i_imm(x))
    return st & ld


def forms_sp_pointer(F):
    """True when some word writes a register other than sp with a value derived from sp (`addi rd, sp, k`, `mv rd, sp`,
    an R-type op on sp): a pointer into the frame can then leave the function (a va_list, the address of a local), and
    a store into the frame may be read through it."""
    for o, x, n in F.w:
        if n != 4: continue
        op, rd, rs1, rs2 = x & 0x7f, (x >> 7) & 31, (x >> 15) & 31, (x >> 20) & 31
        if rd in (0, 2): continue
        if op in (0x13, 0x1b) and rs1 == 2: return True
        if op in (0x33, 0x3b) and 2 in (rs1, rs2): return True
    return False


def dead_frame_stores(F, reg):
    """the word offsets of the stores of `reg` into F's own frame that are NOT a read of the value: F forms no
    sp-derived pointer, and no load of F reads any byte the store wrote, except the `ld reg` of the same slot that
    restores an `sd reg` (a save / restore pair). Every other store of `reg` into the frame is a read (the pool
    owner's rule: a varargs save that `va_arg` reads, or a slot read back into another register, is a use)."""
    if forms_sp_pointer(F): return frozenset()
    loads = []
    for o, x, n in F.w:
        if n == 4 and (x & 0x7f) == 0x03 and ((x >> 15) & 31) == 2:
            f3 = (x >> 12) & 7; lo = i_imm(x)
            loads.append((lo, lo + (1 << (f3 & 3)), (x >> 7) & 31, f3))
    out = set()
    for o, x, n in F.w:
        if not (n == 4 and (x & 0x7f) == 0x23 and ((x >> 20) & 31) == reg and ((x >> 15) & 31) == 2): continue
        f3 = (x >> 12) & 7; lo = s_imm(x); hi = lo + (1 << f3)
        ok = True
        for l, h, r, lf3 in loads:
            if not (l < hi and lo < h): continue
            if r == reg and f3 == 3 and lf3 == 3 and l == lo: continue   # the restore of a save / restore pair
            ok = False; break
        if ok: out.add(o)
    return frozenset(out)


def is_spill_store(x, slots, reg):
    return ((x & 0x7f) == 0x23 and ((x >> 12) & 7) == 3 and ((x >> 20) & 31) == reg
            and ((x >> 15) & 31) == 2 and s_imm(x) in slots)


def is_restore_load(x, slots, reg):
    return ((x & 0x7f) == 0x03 and ((x >> 12) & 7) == 3 and ((x >> 7) & 31) == reg
            and ((x >> 15) & 31) == 2 and i_imm(x) in slots)



_RETS = {}


def callee_returns(s3, I, a, z, depth=0):
    """True when the function at a can give control back to its caller: it has a `ret`, an indirect jump, an
    unresolvable call site, or a tail call into a function that returns. False only when every path ends in a
    function that never returns (Die, CheckFailed, __stack_chk_fail, _Exit)."""
    key = (id(I), a)
    if key in _RETS: return _RETS[key]
    if depth > 8: return True
    _RETS[key] = True                       # recursion: assume it returns (fail closed)
    b = s3.frd(I, a, z)
    if b is None: return True
    w = s3.bc_words(b)
    if any(n == 2 for o, x, n in w): return True
    tails = []
    for i, (o, x, n) in enumerate(w):
        if n != 4: continue
        if s3._isret(x): return True
        if (x & 0x7f) == 0x67 and not ((x >> 7) & 31):
            if s3._isret(x): return True
            tails.append(o)                 # jr: an indirect tail call / jump
        elif (x & 0x7f) == 0x6f and not ((x >> 7) & 31):
            tgt = o + sx(((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11 | ((x >> 21) & 0x3ff) << 1, 21)
            if not 0 <= tgt < len(b): tails.append(o)
    for o in tails:
        ce = callee_of(s3, I, a, b, o)
        if ce is None or callee_returns(s3, I, ce[0], ce[1], depth + 1):
            return True
    _RETS[key] = False
    return False



_KILLS = {}


def callee_kills(s3, I, a, z, reg, depth=0):
    """True when the function at a WRITES integer register reg on EVERY path from its entry to a `ret` (so the value
    the caller had cannot survive the call): a direct write of reg, a call whose own callee writes it on every path
    (followed, 8 levels), or an ecall for a0 (the kernel's return value). A function with no reachable `ret` (it dies
    or tail-calls away) also cannot give the value back, so it counts as killing. No psABI assumption is made: a call
    kills nothing by itself."""
    key = (id(I), a, reg)
    if key in _KILLS: return _KILLS[key]
    if depth > 8: return False
    _KILLS[key] = False                      # recursion: assume not killed (fail closed)
    b = s3.frd(I, a, z)
    if b is None: return False
    F = Fn(s3, b, a)
    if F.parcels: return False
    w = F.w; succ = F.succ

    slots = spill_slots(s3, F, reg)

    def writes_here(i):
        o, x, n = w[i]
        if n != 4: return False
        if is_restore_load(x, slots, reg): return False    # it gives the caller's value back, it does not kill it
        if s3._writes(x) == reg: return True
        if x & 0x7f == 0x73 and (x >> 12) & 7 == 0 and reg == 10: return True      # ecall: a0 is the result
        if x & 0x7f in (0x6f, 0x67) and (x >> 7) & 31:
            ce = callee_of(s3, I, a, b, o)
            return ce is not None and callee_kills(s3, I, ce[0], ce[1], reg, depth + 1)
        return False
    # MUST dataflow: written[i] = reg is written on every path from the entry to i
    written = [None] * len(w); written[0] = False
    roots = sorted(set(range(1, len(w))) - {t for s in succ for t in s})
    for t in roots: written[t] = False       # a word only an indirect jump reaches: unknown, take it as not written
    work = [0] + roots
    while work:
        i = work.pop()
        if written[i] is None: continue
        out = written[i] or writes_here(i)
        for t in succ[i]:
            new = out if written[t] is None else (written[t] and out)
            if new != written[t]: written[t] = new; work.append(t)
    # a `ret` AND a TAIL call are both points at which control goes back to this function's caller: at a tail call
    # the register must be written here, or by the function tail-called (which returns in this function's place)
    ok = True
    for i, (o, x, n) in enumerate(w):
        if n != 4 or written[i] is None: continue
        if s3._isret(x):
            ok = ok and bool(written[i])
        elif (x & 0x7f) in (0x6f, 0x67) and not ((x >> 7) & 31):
            if written[i]: continue
            ce = callee_of(s3, I, a, b, o)
            ok = ok and ce is not None and callee_kills(s3, I, ce[0], ce[1], reg, depth + 1)
    _KILLS[key] = ok
    return ok


def callee_reads(s3, I, a, z, reg, depth=0, seen=None):
    """A reason string when the function at a may read integer register reg while it still holds its ENTRY value: as
    an operand, a memory base, at an ecall, or in a function it calls / tail-calls with reg still holding the entry
    value (followed into that callee, 8 levels; an unresolved callee counts as a read). False when no path reads it.
    The psABI is NOT relied on: at a call the register stays live unless THAT callee writes it on every path to its
    return (`callee_kills`). Two things are not reads of the VALUE: a dead store of the register into the function's
    own frame (`dead_frame_stores`: no sp-derived pointer, the bytes never loaded back except by the restore of a save /
    restore pair), and handing it back at a `ret` -- the caller's own trace carries it on from there."""
    seen = set() if seen is None else seen
    if (a, reg) in seen: return False
    seen.add((a, reg))
    if depth > 8: return '%s: call depth 8' % name(s3, I, a)
    b = s3.frd(I, a, z)
    F = Fn(s3, b, a)
    if F.parcels: return '%s: 2-byte parcels' % name(s3, I, a)
    w = F.w; succ = F.succ
    slots = spill_slots(s3, F, reg)
    dead = dead_frame_stores(F, reg)
    live = [None] * len(w); live[0] = True
    roots = sorted(set(range(1, len(w))) - {t for s in succ for t in s})
    jr = [i for i, (o, x, n) in enumerate(w) if x & 0x7f == 0x67 and (x >> 7) & 31 == 0 and not s3._isret(x)]

    def step(i, v):
        o, x, n = w[i]
        if not v: return False
        if is_restore_load(x, slots, reg): return True          # the register gets its entry value back
        if s3._writes(x) == reg: return False
        if x & 0x7f in (0x6f, 0x67) and (x >> 7) & 31:
            ce = callee_of(s3, I, a, b, o)
            if ce is not None and callee_kills(s3, I, ce[0], ce[1], reg, depth + 1): return False
        return True
    work = [0]
    while True:
        while work:
            i = work.pop(); out = step(i, live[i])
            for t in succ[i]:
                new = out if live[t] is None else (live[t] or out)
                if new != live[t]: live[t] = new; work.append(t)
        u = any(step(i, live[i]) for i in jr if live[i] is not None)
        for t in roots:
            new = u if live[t] is None else (live[t] or u)
            if new != live[t]: live[t] = new; work.append(t)
        if not work: break
    FX = None
    for i, (o, x, n) in enumerate(w):
        if not live[i]: continue
        if x & 0x7f == 0x73 and (x >> 12) & 7 == 0:
            # an ecall reads a7 (the syscall number) and a0..a(N-1), N = that syscall's argument count (SYSCALL_ARGS);
            # a6 is never a syscall argument on RISC-V Linux. An unknown number reads a0-a5 and a7
            if FX is None:
                FX = F; FX.run()
            es = FX.ins[i].get(17, frozenset()) if FX.ins[i] else frozenset()
            num = next(iter(es))[1] if len(es) == 1 and next(iter(es))[0] == 'C' else None
            na = SYSCALL_ARGS.get(num, 6)
            if reg == 17 or (10 <= reg < 10 + na): return '%s+%#x ecall (syscall %s, %d argument(s))' % (name(s3, I, a), o, num, na)
            continue
        if o in dead: continue                 # a dead store into this callee's own frame: not a use of the value
        for q, role, e in F.reads(i):
            if q != reg: continue
            if role in ('ARG', 'CALLEE') and x & 0x7f in (0x6f, 0x67):   # a call: does ITS callee read reg?
                ce = callee_of(s3, I, a, b, o)
                if ce is None: return '%s+%#x: unresolved call' % (name(s3, I, a), o)
                r = callee_reads(s3, I, ce[0], ce[1], reg, depth + 1, seen)
                if r: return '%s+%#x -> %s' % (name(s3, I, a), o, r)
                continue
            if role == 'RET': continue       # giving the register back is not a read; the caller's trace goes on
            return '%s+%#x %s (%s)' % (name(s3, I, a), o, dis(x), role)
    return False


def name(s3, I, a):
    r = s3.qres(I, a)
    if r is not None and r.startswith('('):
        r = s3.atname(I, a) or r
    return r or '?'


def main(argv):
    ypin = None
    if '--ypin' in argv:
        k = argv.index('--ypin'); ypin = argv[k + 1]; del argv[k:k + 2]
    kit, xe, ye, rows = argv
    s3 = load_kit(kit)
    IX, IY = s3.Img(xe), s3.Img(ye)
    if ypin:
        from elftools.elf.elffile import ELFFile
        YP = [(g['p_vaddr'], g['p_filesz'], g['p_memsz'], g.data()) for g in ELFFile(open(ypin, 'rb')).iter_segments()
              if g['p_type'] == 'PT_LOAD']
        if [x[:3] for x in YP] != [(v, fz, mz) for (v, fz, d), mz in zip(IY.segs, IY.mzs)]:
            raise SystemExit('luitrace: Y pin and Y twin have different PT_LOAD layouts')
        IY.segs = [(v, fz, d) for v, fz, mz, d in YP]
    print('# luitrace: X sha256 %s; Y sha256 %s%s' % (s3.sha(xe)[:12], s3.sha(ye)[:12],
                                                     '; Y bytes from pin sha256 %s' % s3.sha(ypin)[:12] if ypin else ''))
    for ln in open(rows):
        if not ln.strip() or ln.startswith('#'): continue
        tag, fn, xa, ya, size, off = ln.rstrip('\n').split('\t')[:6]
        xa, ya, size, off = int(xa, 16), int(ya, 16), int(size), int(off, 16)
        r = trace(s3, IX, IY, xa, ya, size, off)
        print('== %s %s X %#x Y %#x lui +%#x' % (tag, fn, xa, ya, off))
        if r['parcels']:
            print('  2-byte parcels: not traced'); continue
        for l in r['lines']: print(l)
        for u in r['uses']:
            print('  USE +%#x %s %s %s %s %s' % u)
        print('  USES %d: %s' % (len(r['uses']), dict(collections.Counter(u[1] for u in r['uses']))))


if __name__ == '__main__':
    main(sys.argv[1:])
