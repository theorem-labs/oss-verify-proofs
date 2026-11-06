#!/usr/bin/env python3
"""Where does a value built from an immediate reach the base of a load, store, jump or atomic? The comparison kit of
record judges a lui-built value only in the shapes its rule 8 follows; its registry lists the shapes it does not
follow (the load / store / jalr immediate on such a value; addi / addiw chains; ori / xori / slli; stack spills, FP
register moves and CSR round trips; a jump-table arm reached only by fall-through; an in-function callee; c.lui; an
address built without lui). This scan lists, in every compared function, in the fm twin and in each fuzz_disco twin,
every site where a value built from ANY immediate word may reach such a base through ANY shape, and gives each site the
scan's own trace; the hand trace of each site is a separate table (addrsite-trace.tsv).

  addrsite.py KIT_DIR PAIRS [--table FUNC:OFF:N ...] fm=FM_TWIN TAG=TWIN ...   > addrsite.tsv

KIT_DIR: the comparison kit (strictcmp3's Img, qres and sec are used; nothing is copied from it). PAIRS: pairs.tsv
(every function with a pairing other than absent is scanned at its address and size in each image; a function whose
size differs between the images is not compared: its sites are listed by offset in a comment line only). --table
FUNC:OFF:N: a rel4 jump table of FUNC (regdef.py's control flow). A function with a 2-byte parcel is not scanned and
is listed as such (none of the compared functions holds one, so none holds a c.lui).

IMMEDIATE WORDS (the sources): every lui, every op-imm / op-imm-32 word whose source register is x0 (li, an address
built without lui), every CSR-immediate word. Each source has one value (lui: its upper immediate; the others: what the
word computes from x0).

CONTROL FLOW: regdef.py's (branches to both successors; `jal x0` / `jalr x0` to their targets; a listed table's
dispatch to its entries; a return to none), and, so that no path is missed: a `jalr x0` that is not a return and not
a listed table's dispatch gets an edge to every word of the function; a call whose target lies in the function gets an
edge to that target, and then every return gets an edge to the word after each such call.

VALUES, a forward dataflow to a fixpoint: each integer register, FP register, CSR and stack slot holds a set of linear
forms. A form is a sum of terms times integer coefficients plus a set of constants (or `any constant`), and the set of
sources whose value it may carry (its taint) and the shapes that value passed through. Terms: `sp` (the stack pointer
at entry), `imm +o` (the value of the source at +o), `arg xN` (a register at entry: x3 is gp, x4 is tp), `auipc +o`,
`ret +o` (the return address a call at +o writes), `q +o ...` (a value an operation at +o made in a way the forms do
not follow; `q*` when it depends on a source), `w` (several terms merged; `w*` when one depends on a source). add, sub,
addi, sh*add, slli, a multiply by a known value and the 64-bit moves follow exactly; an operation whose operands are
all known numbers is computed (32-bit words with their wrap); a 32-bit add on another value is followed without its
wrap and marked; every other operation gives a `q` term whose taint is the union of its operands' taints, so a taint is
never dropped. More than 12 forms: the source terms are folded into the constants, then every term but sp becomes
`w`, then the value is unknown (its taint kept). A word whose in-state changed more than 24 times keeps coarse values
from then on (per sp coefficient one form of numbers and one `w` form, tainted and untainted apart), so the fixpoint
ends.
Memory: a store whose address is a known stack offset (sp at entry plus sources and one constant) writes that slot; a
load from a known stack offset reads it (a partial overlap gives a `q` term with the slots' taints); a load from a
stack address at an unknown offset reads every slot. Every other store (memory that is not a known stack slot) is NOT
followed: each one whose data carries a taint is listed as a `store` row, so a reader sees every value built from an
immediate that leaves the followed state; every other load gives a new untainted value. A call (and ecall for a0)
gives each caller-saved register a new value; a0 and a1 also get every tainted form of a0..a7 at the call (a callee
may return an argument). FP: fmv.d.x / fmv.x.d copy forms; other moves and FP operations give `q` terms with the taint.
CSR: a write then a read returns what was written.

SITES: a load / store / FP load / FP store / jalr / AMO whose base register may carry a taint (`base` rows), and the
stores of tainted data that are not followed (`store` rows). SCAN TRACE per site and image, from the tainted forms of
the base (plus the word's offset) or of the data: `stack address` (sp with coefficient 1); `absolute address` (only
source terms and known constants: each value resolved in the image, symbol + offset, or section); `not an image
address` (the same, every value outside every PT_LOAD of the image); `TLS address` / `gp address` (tp or gp plus a known
immediate part, resolved); `displacement on a runtime value` (untainted terms plus a known immediate part outside every
PT_LOAD); for a store row also `at most 16 bits` (a 1- or 2-byte store; every PT_LOAD starts above 0xffff); else `not
traced`. SHAPES of a site: those its value passed through, and `site immediate` when the word's own offset is not 0.
A last block compares each site of a compared function across the images: the same scan trace with the same symbol +
offset (`same object up to relocation`, else `DIFFERENT OBJECT`), the same stack form, the same numbers.
"""
import argparse
import csv
import hashlib
import heapq
import importlib.util
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import regdef                                      # noqa: E402

RA, SP, GP, TP = 1, 2, 3, 4
M64 = (1 << 64) - 1
CAP_FORMS, CAP_K, CAP_FOLD = 12, 8, 64
ARGS = list(range(10, 18))
FCALLER = [0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]
SPMARK, W32 = ('spdep',), ('w32',)
LV = {}                                            # source offset -> value, of the function being scanned
AUIPC = {}                                         # auipc offset -> the address it builds, of the same function


def sx(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def fields(w):
    return w & 0x7f, (w >> 7) & 31, (w >> 12) & 7, (w >> 15) & 31, (w >> 20) & 31, w >> 25


def simm(w):
    op = w & 0x7f
    if op in (0x23, 0x27):
        return sx(((w >> 25) << 5) | ((w >> 7) & 31), 12)
    if op == 0x2f:
        return 0
    return sx(w >> 20, 12)


def width(w):
    op, f3 = w & 0x7f, (w >> 12) & 7
    if op == 0x2f:
        return 4 if f3 == 2 else 8
    if op in (0x07, 0x27):
        return {1: 2, 2: 4, 3: 8, 4: 16}.get(f3, 8)
    return {0: 1, 1: 2, 2: 4, 3: 8, 4: 1, 5: 2, 6: 4}.get(f3, 8)


def base_of(w):
    """the base register of a load / store / FP load / FP store / jalr / AMO word, else None"""
    return (w >> 15) & 31 if w & 0x7f in (0x03, 0x07, 0x23, 0x27, 0x2f, 0x67) else None


def mnem(w):
    return regdef.text(0, w).split(' ', 1)[1].split(' ')[0]


def source_value(w):
    """the value of an immediate word (a source), else None"""
    op, rd, f3, rs1, rs2, f7 = fields(w)
    if op == 0x37:
        return sx(w & 0xfffff000, 32)
    if op in (0x13, 0x1b) and rs1 == 0:
        im = simm(w)
        val = {0: im, 2: int(0 < im), 3: int(0 < (im & M64)), 4: im, 6: im}.get(f3, 0)
        return sx(val, 32) if op == 0x1b else val
    if op == 0x73 and f3 in (5, 6, 7):
        return rs1
    return None


# ---- values -------------------------------------------------------------------------------------------------------
# form = (terms, ks, tt): terms frozenset((term, coefficient)); ks frozenset of constants or None (any constant);
# tt frozenset of source offsets (int), shapes ('s', name), SPMARK (made from sp other than linearly), W32.
# value = ('v', frozenset(forms)) | ('top', tt)

def form(terms, ks, tt):
    return (frozenset((k, c) for k, c in terms.items() if c != 0), ks, frozenset(tt))


def tainted(tt):
    return any(isinstance(x, int) for x in tt)


def group(forms):
    by = {}
    for t, ks, tt in forms:
        if t in by:
            a, att = by[t]
            by[t] = (None if a is None or ks is None else a | ks, att | tt)
        else:
            by[t] = (ks, tt)
        if by[t][0] is not None and len(by[t][0]) > (CAP_K if t else CAP_FOLD):
            by[t] = (None, by[t][1])
    return by


def norm(forms):
    by = group(forms)
    if len(by) > CAP_FORMS:
        by = group([(frozenset((k, c) for k, c in t if k[0] != 'imm'),
                     None if ks is None else frozenset(sx(sum(c * LV[k[1]] for k, c in t if k[0] == 'imm') + y, 64)
                                                       for y in ks), tt) for t, (ks, tt) in by.items()])
    if len(by) > CAP_FORMS:
        out = []
        for t, (ks, tt) in by.items():
            keep = {k: c for k, c in t if k[0] == 'sp'}
            if any(k[0] != 'sp' for k, c in t):
                keep[('w', any(k[0] in ('q', 'w') and k[-1] is True for k, c in t) if tainted(tt) else None)] = 1
            out.append(form(keep, None, tt))
        by = group(out)
    if len(by) > CAP_FORMS:
        return ('top', frozenset().union(*[tt for ks, tt in by.values()]))
    return ('v', frozenset((t, ks, tt) for t, (ks, tt) in by.items()))


def tt_of(x):
    if x[0] == 'top':
        return x[1]
    return frozenset().union(*[tt for t, ks, tt in x[1]]) if x[1] else frozenset()


def taint(x):
    return frozenset(y for y in tt_of(x) if isinstance(y, int))


def has_sp(x):
    """x may hold a value made from sp (a `w` term keeps sp apart, and an opaque term made from sp marks its form)"""
    return x[0] == 'top' or SPMARK in tt_of(x) or any(k[0] == 'sp' for t, ks, tt in x[1] for k, c in t)


def join(a, b):
    if a == b:
        return a
    if a[0] == 'top' or b[0] == 'top':
        return ('top', tt_of(a) | tt_of(b))
    return norm(list(a[1]) + list(b[1]))


def join_opt(a, b):
    return b if a is None else a if b is None else join(a, b)


def const(k, tt=frozenset()):
    return ('v', frozenset([form({}, frozenset([k]), tt)]))


def term(k, tt=frozenset()):
    return ('v', frozenset([form({k: 1}, frozenset([0]), tt)]))


def lin(a, b, sa=1, sb=1, extra=frozenset()):
    if a[0] == 'top' or b[0] == 'top':
        return ('top', tt_of(a) | tt_of(b) | extra)
    out = []
    for ta, ka, xa in a[1]:
        for tb, kb, xb in b[1]:
            d = {}
            for k, c in ta:
                d[k] = d.get(k, 0) + sa * c
            for k, c in tb:
                d[k] = d.get(k, 0) + sb * c
            ks = None if ka is None or kb is None else frozenset(sx(sa * x + sb * y, 64) for x in ka for y in kb)
            out.append(form(d, ks, xa | xb | extra))
    return norm(out)


def scale(a, c):
    if a[0] == 'top':
        return a
    return norm([form({k: x * c for k, x in t}, None if ks is None else frozenset(sx(y * c, 64) for y in ks), tt)
                 for t, ks, tt in a[1]])


def addk(a, imm, extra=frozenset()):
    if a[0] == 'top':
        return ('top', a[1] | extra)
    return norm([(t, None if ks is None else frozenset(sx(y + imm, 64) for y in ks), tt | extra) for t, ks, tt in a[1]])


def tag(a, name):
    """add the shape `name` to every tainted form of a"""
    s = ('s', name)
    if a[0] == 'top':
        return ('top', a[1] | {s}) if tainted(a[1]) else a
    return ('v', frozenset((t, ks, tt | {s}) if tainted(tt) else (t, ks, tt) for t, ks, tt in a[1]))


def strip(x):
    """the tainted forms of x, None if none"""
    if x[0] == 'top':
        return x if tainted(x[1]) else None
    fs = [f for f in x[1] if tainted(f[2])]
    return ('v', frozenset(fs)) if fs else None


def known(x):
    """the one number x holds, else None"""
    if x[0] != 'v' or len(x[1]) != 1:
        return None
    (t, ks, tt), = x[1]
    if ks is None or len(ks) != 1 or any(k[0] != 'imm' for k, c in t):
        return None
    return sx(sum(c * LV[k[1]] for k, c in t) + next(iter(ks)), 64)


def opaque(o, what, *ins):
    tt = frozenset().union(*[tt_of(x) for x in ins]) if ins else frozenset()
    if any(has_sp(x) for x in ins):
        tt = tt | {SPMARK}
    return term(('q', o, what, tainted(tt)), tt)


def exact_sp(b):
    """the entry-relative stack offset b holds (sp with coefficient 1, source terms, one constant), else None"""
    if b[0] != 'v' or len(b[1]) != 1:
        return None
    (t, ks, tt), = b[1]
    d = dict(t)
    if d.pop(('sp',), 0) != 1 or any(k[0] != 'imm' for k in d) or ks is None or len(ks) != 1 or SPMARK in tt:
        return None
    return sx(sum(c * LV[k[1]] for k, c in d.items()) + next(iter(ks)), 64)


# ---- the dataflow -------------------------------------------------------------------------------------------------
# state = (regs: 32 values, fregs: 32 values or None, csrs: frozenset((csr, value)),
#          slots: frozenset(((off, n), value)))

def join_state(s1, s2):
    r = tuple(join(a, b) for a, b in zip(s1[0], s2[0]))
    f = tuple(join_opt(a, b) for a, b in zip(s1[1], s2[1]))
    c1, c2 = dict(s1[2]), dict(s2[2])
    c = frozenset((k, join_opt(c1.get(k), c2.get(k))) for k in set(c1) | set(c2))
    l1, l2 = dict(s1[3]), dict(s2[3])
    sl = {}
    for k in set(l1) | set(l2):
        if k in l1 and k in l2:
            sl[k] = join(l1[k], l2[k])
        else:                                      # written on one path only: the other holds an untainted value
            sl[k] = join(l1.get(k) or l2.get(k), term(('q', -1, 'slot %#x before' % k[0], False)))
    return (r, f, c, frozenset(sl.items()))


def tag_state(st, name):
    regs, fregs, csrs, slots = st
    return (tuple(tag(x, name) for x in regs), tuple(None if x is None else tag(x, name) for x in fregs),
            frozenset((k, tag(v_, name)) for k, v_ in csrs), frozenset((k, tag(v_, name)) for k, v_ in slots))


def mem_load(o, st, base, imm, n):
    slots = dict(st[3])
    k = exact_sp(base)
    if k is not None:
        a = k + imm
        over = sorted((kk, vv) for kk, vv in slots.items() if kk[0] < a + n and a < kk[0] + kk[1])
        if len(over) == 1 and over[0][0] == (a, n):
            return tag(over[0][1], 'stack spill')
        if over:
            return tag(opaque(o, 'part of stack slots', *[vv for kk, vv in over]), 'stack spill')
        return term(('q', o, 'ld', False))
    val = term(('q', o, 'ld', False))
    if has_sp(base):
        for kk, vv in sorted(slots.items()):
            s_ = strip(vv)
            if s_ is not None:
                val = join(val, tag(s_, 'stack spill'))
    return val


def mem_store(st, base, imm, n, data):
    k = exact_sp(base)
    if k is None:
        return st                                  # not followed; a tainted one is a `store` row
    slots = dict(st[3])
    a = k + imm
    for kk in list(slots):
        if kk[0] < a + n and a < kk[0] + kk[1]:
            if a <= kk[0] and kk[0] + kk[1] <= a + n:
                del slots[kk]
            else:
                slots[kk] = join(slots[kk], opaque(-1, 'partly overwritten slot', data))
    slots[(a, n)] = data
    return (st[0], st[1], st[2], frozenset(slots.items()))


def call(o, st, what, clobber):
    regs, fregs, csrs, slots = st
    r, f = list(regs), list(fregs)
    for x in clobber:
        r[x] = term(('q', o, '%s x%d' % (what, x), False))
    for x in (10, 11):
        if x in clobber:
            for y in ARGS:
                s_ = strip(regs[y])
                if s_ is not None:
                    r[x] = join(r[x], tag(s_, 'call result'))
    if what == 'call':
        for x in FCALLER:
            f[x] = term(('q', o, '%s f%d' % (what, x), False))
    return (tuple(r), tuple(f), csrs, slots)


def step(w, o, st):
    regs, fregs, csrs, slots = st
    op, rd, f3, rs1, rs2, f7 = fields(w)
    g = lambda x: regs[x]
    res = None
    if source_value(w) is not None and op != 0x73:
        res = term(('imm', o), {o})
    elif op == 0x17:
        res = term(('auipc', o))
    elif op in (0x13, 0x1b):
        a, im = g(rs1), simm(w)
        w32 = op == 0x1b
        sh = (w >> 20) & (31 if w32 else 63)
        ka = known(a)
        if ka is not None:
            val = {0: lambda: ka + im, 2: lambda: int(ka < im), 3: lambda: int((ka & M64) < (im & M64)),
                   4: lambda: ka ^ im, 6: lambda: ka | im, 7: lambda: ka & im}.get(f3, lambda: None)()
            if f3 == 1 and f7 >> 1 == 0:
                val = ka << sh
            elif f3 == 5 and w >> 26 == 0:
                val = (ka & (0xffffffff if w32 else M64)) >> sh
            elif f3 == 5 and w >> 26 == 0x10:
                val = sx(ka, 32 if w32 else 64) >> sh
            if val is not None:
                val = sx(val, 32 if w32 else 64)
                res = addk(a, im) if f3 == 0 and val == ka + im else const(val, tt_of(a))
        if res is None:
            if f3 == 0 and not w32:
                res = addk(a, im)
            elif f3 == 0 and taint(a):
                res = addk(a, im, {W32})
            elif f3 == 1 and f7 >> 1 == 0 and not w32:
                res = scale(a, 1 << sh)
            else:
                res = opaque(o, mnem(w), a)
        if taint(a):
            nm = {0: 'addi', 1: 'slli', 2: 'slti', 3: 'sltiu', 4: 'xori', 5: 'srli/srai', 6: 'ori', 7: 'andi'}[f3]
            if f3 == 0:
                nm = ('addiw' if im else 'sext.w') if w32 else ('addi' if im else 'mv')
            if nm in ('addi', 'addiw') and {('s', 'addi'), ('s', 'addiw')} & tt_of(a):
                res = tag(res, 'addi/addiw chain')
            res = tag(res, nm)
    elif op in (0x33, 0x3b):
        a, b = g(rs1), g(rs2)
        w32 = op == 0x3b
        ka, kb = known(a), known(b)
        nm = 'other op'
        if f7 in (0, 0x20) and f3 == 0:
            nm = 'add/sub'
            if not w32:
                res = lin(a, b, 1, -1 if f7 == 0x20 else 1)
            elif ka is None or kb is None:
                res = lin(a, b, 1, -1 if f7 == 0x20 else 1, {W32}) if taint(a) or taint(b) else None
        elif f7 == 0x10 and f3 in (2, 4, 6) and not w32:
            nm = 'sh*add'
            res = lin(a, b, 1 << (f3 // 2), 1)
        elif f7 == 0 and f3 == 1 and kb is not None and not w32:
            nm = 'sll'
            res = scale(a, 1 << (kb & 63))
        elif f7 == 1 and f3 == 0 and not w32 and (ka is not None or kb is not None):
            nm = 'mul'
            res = scale(b, ka) if ka is not None else scale(a, kb)
        elif f7 in (0, 0x20) and f3 in (4, 6, 7):
            nm = 'and/or/xor'
        elif f7 in (0, 0x20) and f3 in (1, 5):
            nm = 'sll/srl/sra'
        elif f7 == 0 and f3 in (2, 3):
            nm = 'slt/sltu'
        elif f7 == 1:
            nm = 'mul/div'
        if res is None and ka is not None and kb is not None:
            m, sh = (0xffffffff if w32 else M64), kb & (31 if w32 else 63)
            val = {(0, 0): ka + kb, (0x20, 0): ka - kb, (0, 4): ka ^ kb, (0, 6): ka | kb, (0, 7): ka & kb,
                   (0, 1): ka << sh, (0, 5): (ka & m) >> sh, (0x20, 5): sx(ka, 32 if w32 else 64) >> sh,
                   (0, 2): int(ka < kb), (0, 3): int((ka & M64) < (kb & M64)), (1, 0): ka * kb}.get((f7, f3))
            if val is not None:
                res = const(sx(val, 32 if w32 else 64), tt_of(a) | tt_of(b))
        if res is None:
            res = opaque(o, mnem(w), a, b)
        if taint(a) or taint(b):
            res = tag(res, nm)
            if w32:
                res = tag(res, '32-bit op')
    elif op in (0x03, 0x07):
        val = mem_load(o, st, g(rs1), simm(w), width(w))
        if op == 0x03:
            res = val
        else:
            f = list(fregs)
            f[rd] = val
            st = (regs, tuple(f), csrs, slots)
    elif op in (0x23, 0x27):
        data = g(rs2) if op == 0x23 else (fregs[rs2] or term(('q', o, 'f%d' % rs2, False)))
        st = mem_store(st, g(rs1), simm(w), width(w), tag(data, 'FP register') if op == 0x27 else data)
    elif op == 0x2f:
        f5 = w >> 27
        if f5 == 2:                                # lr
            res = mem_load(o, st, g(rs1), 0, width(w))
        elif f5 == 3:                              # sc
            st = mem_store(st, g(rs1), 0, width(w), g(rs2))
            res = term(('q', o, 'sc', False))
        else:
            res = mem_load(o, st, g(rs1), 0, width(w))
            st = mem_store(st, g(rs1), 0, width(w), opaque(o, 'amo', res, g(rs2)))
    elif op in (0x6f, 0x67) and rd:
        st = call(o, st, 'call', regdef.CALLER_SAVED)
        res = term(('ret', o))
    elif op == 0x73 and f3 == 0 and w == 0x73:     # ecall: a0 is written
        st = call(o, st, 'ecall', [10])
    elif op == 0x73 and f3:
        csr = w >> 20
        cs = dict(csrs)
        old = cs.get(csr) or term(('q', o, 'csr %#x' % csr, False))
        src = (term(('imm', o), {o}) if f3 in (5, 6, 7) else g(rs1))
        if f3 in (1, 5):
            cs[csr] = tag(src, 'CSR')
        elif rs1:
            cs[csr] = tag(opaque(o, 'csr set / clear', old, src), 'CSR')
        st = (regs, fregs, frozenset(cs.items()), slots)
        res = tag(old, 'CSR')
    elif op in (0x53, 0x43, 0x47, 0x4b, 0x4f):
        f = list(fregs)
        fr = lambda x: fregs[x] or term(('q', o, 'f%d' % x, False))
        f5 = w >> 27
        if op == 0x53 and f5 in (0x14, 0x18, 0x1c):                # to an integer register
            srcs = [fr(rs1)] + ([fr(rs2)] if f5 == 0x14 else [])
            res = tag(srcs[0] if w >> 25 == 0x71 and f3 == 0 and rs2 == 0 else opaque(o, mnem(w), *srcs),
                      'FP register')                               # fmv.x.d copies
        elif op == 0x53 and f5 in (0x1a, 0x1e):                    # from an integer register
            f[rd] = tag(g(rs1) if w >> 25 == 0x79 and rs2 == 0 else opaque(o, mnem(w), g(rs1)), 'FP register')
            st = (regs, tuple(f), csrs, slots)
        else:
            srcs = [fr(rs1), fr(rs2)] + ([fr(w >> 27)] if op != 0x53 else [])
            f[rd] = srcs[0] if op == 0x53 and f5 == 0x04 and rs1 == rs2 and f3 == 0 else opaque(o, mnem(w), *srcs)
            st = (regs, tuple(f), csrs, slots)
    if res is not None and rd:
        r = list(st[0])
        r[rd] = res
        st = (tuple(r),) + st[1:]
    if st[0][0] != const(0):
        r = list(st[0])
        r[0] = const(0)
        st = (tuple(r),) + st[1:]
    return st


def coarse(x):
    """x with at most two forms per sp coefficient: one of numbers (source terms folded into the constants) and one
    `w` form for every form with another term. Applied at a word after WIDEN_AFTER updates; a coarse value joined with
    a value it already covers stays the same, so the fixpoint ends"""
    if x is None or x[0] == 'top':
        return x
    by = {}
    for t, ks, tt in x[1]:
        d = dict(t)
        s = d.pop(('sp',), 0)
        if all(k[0] == 'imm' for k in d):
            key, flag = (s, 'n', tainted(tt)), False
            ks = None if ks is None else frozenset(sx(sum(c * LV[k[1]] for k, c in d.items()) + y, 64) for y in ks)
        else:
            key, flag, ks = (s, 'w', tainted(tt)), any(k[0] in ('q', 'w') and k[-1] is True for k in d), None
        if key in by:
            a, att, af = by[key]
            ks = None if a is None or ks is None else a | ks
            flag, tt = flag or af, tt | att
        by[key] = (None if ks is None or len(ks) > CAP_FOLD else ks, tt, flag)
    forms = []
    for (s, kind, tn), (ks, tt, flag) in by.items():
        terms = {('sp',): s} if s else {}
        if kind == 'w':
            terms[('w', flag if tn else None)] = 1
        forms.append(form(terms, ks, tt))
    return ('v', frozenset(forms))


def coarse_state(st):
    regs, fregs, csrs, slots = st
    return (tuple(coarse(x) for x in regs), tuple(coarse(x) for x in fregs),
            frozenset((k, coarse(v_)) for k, v_ in csrs), frozenset((k, coarse(v_)) for k, v_ in slots))


WIDEN_AFTER = 24


def fixpoint(words, succ, init, edge_tag):
    """in-states of every word a path from the entry reaches (worklist in address order; a word whose in-state changed
    WIDEN_AFTER times keeps coarse values from then on)"""
    state, work, inq, updates = {0: init}, [0], {0}, {}
    while work:
        o = heapq.heappop(work)
        inq.discard(o)
        out = step(words[o], o, state[o])
        for t in succ[o]:
            if t not in words:
                continue
            ns = edge_tag(o, t, out)
            if t in state:
                js = join_state(state[t], ns)
                if js == state[t]:
                    continue
                updates[t] = updates.get(t, 0) + 1
                if updates[t] > WIDEN_AFTER:
                    js = coarse_state(js)
                    if js == state[t]:
                        continue
                state[t] = js
            else:
                state[t] = ns
            if t not in inq:
                inq.add(t)
                heapq.heappush(work, t)
    return state


# ---- the scan trace -----------------------------------------------------------------------------------------------

def name_term(k):
    return {'sp': lambda: 'sp', 'imm': lambda: 'imm +%#x' % k[1], 'arg': lambda: 'arg x%d' % k[1],
            'auipc': lambda: 'auipc +%#x' % k[1], 'ret': lambda: 'ret +%#x' % k[1],
            'q': lambda: 'q%s %s %s' % ('*' if k[3] else '', '+%#x' % k[1] if k[1] >= 0 else '', k[2]),
            'w': lambda: 'w%s' % ('*' if k[1] else '')}[k[0]]()


def hx(y):
    return '%#x' % y if y >= 0 else '-%#x' % -y


def show_form(t, ks, tt):
    parts = ['%s%s' % ('' if c == 1 else '%d * ' % c, name_term(k)) for k, c in sorted(t, key=lambda kc: str(kc))]
    parts.append('any constant' if ks is None else '{%s}' % ', '.join(hx(y) for y in sorted(ks)))
    marks = [m for m, x in (('made from sp other than linearly', SPMARK), ('32-bit wrap not followed', W32)) if x in tt]
    return ' + '.join(parts) + (' [%s]' % ', '.join(marks) if marks else '')


def show_value(x):
    if x[0] == 'top':
        return 'unknown'
    return ' | '.join(sorted(show_form(t, ks, tt) for t, ks, tt in x[1] if tainted(tt)))


class Image:
    def __init__(self, s3, path):
        self.s3, self.img = s3, s3.Img(path)
        self.loads = [(v, v + mz) for (v, fz, d), mz in zip(self.img.segs, self.img.mzs)]
        self.gp = next((v for v, z, n, t in self.img.syms if n == '__global_pointer$'), None)

    def inside(self, a):
        return any(lo <= a & M64 < hi for lo, hi in self.loads)

    def res(self, a):
        a &= M64
        return self.s3.qres(self.img, a) or '(%s)' % self.img.sec(a)


def trace(im, x, mo, store_width=None):
    """(kind, detail, key) of the tainted forms of x plus mo; key compares a site across images: the resolved object
    of an address, else the image-independent text of the form"""
    if x[0] == 'top':
        return 'not traced', 'the value is unknown', ('unknown',)
    kinds, det, key = [], [], []
    for t, ks, tt in sorted(x[1], key=lambda f: show_form(*f)):
        if not tainted(tt):
            continue
        d = dict(t)
        s = d.pop(('sp',), 0)
        imm = {k: c for k, c in d.items() if k[0] == 'imm'}
        rest = {k: c for k, c in d.items() if k[0] != 'imm'}
        nums = None if ks is None else sorted({sx(sum(c * LV[k[1]] for k, c in imm.items()) + y + mo, 64) for y in ks})
        if s == 1:
            kinds.append('stack address')
            det.append('sp + %s' % show_form(frozenset(d.items()), None if ks is None else frozenset(
                y + mo for y in ks), tt))
            key.append(det[-1])
            continue
        k_, objs = 'not traced', None
        if s == 0 and SPMARK not in tt and W32 not in tt and nums is not None:
            pa = None
            if len(rest) == 1 and next(iter(rest))[0] == 'auipc' and next(iter(rest.values())) == 1:
                pa = AUIPC[next(iter(rest))[1]]
            if not rest or pa is not None:
                adr = [(pa or 0) + y for y in nums]
                k_ = 'absolute address' if any(im.inside(y) for y in adr) else 'not an image address'
                objs = [im.res(y) if im.inside(y) else 'outside every PT_LOAD' for y in adr]
                det.append(('auipc +%#x (%s) + ' % (next(iter(rest))[1], hx(pa)) if pa is not None else '') + ', '.join(
                    '%s: %s' % (hx(y), ob) for y, ob in zip(nums, objs)))
                if k_ == 'not an image address':
                    objs = [('auipc +%#x + ' % next(iter(rest))[1] if pa is not None else '') + hx(y) for y in nums]
            elif rest == {('arg', TP): 1}:
                k_, objs = 'TLS address', [im.img.tls(y) or '(not in PT_TLS)' for y in nums]
                det.append('tp + ' + ', '.join('%s: %s' % (hx(y), ob) for y, ob in zip(nums, objs)))
            elif rest == {('arg', GP): 1} and im.gp is not None:
                k_, objs = 'gp address', [im.res(im.gp + y) for y in nums]
                det.append('gp + ' + ', '.join('%s: %s' % (hx(y), ob) for y, ob in zip(nums, objs)))
            elif not any(k[0] in ('q', 'w') and k[-1] is True for k in rest) and not any(im.inside(y) for y in nums):
                k_ = 'displacement on a runtime value'
                det.append('%s + immediate part %s (outside every PT_LOAD)' % (
                    ' + '.join(name_term(k) for k in sorted(rest, key=str)), ', '.join(hx(y) for y in nums)))
                objs = [det[-1]]
        narrow = store_width is not None and store_width <= 2 and min(lo for lo, hi in im.loads) > 0xffff
        if k_ == 'not traced' and narrow:
            k_, objs = 'at most 16 bits', ['a %d-byte store' % store_width]
            det.append(objs[0])
        elif k_ == 'not traced':
            det.append(show_form(t, ks, tt))
            objs = [det[-1]]
        kinds.append(k_)
        key.append('%s: %s' % (k_, ', '.join(objs)))
    kind = 'not traced' if 'not traced' in kinds else ' and '.join(sorted(set(kinds)))
    return kind, ' | '.join(det), tuple(key)


SHAPE_ORDER = [('site immediate', {'site immediate'}), ('addi/addiw chain', {'addi/addiw chain'}),
               ('logical or shift (ori, xori, andi, slli, srli / srai, and, or, xor, sll, srl, sra)',
                {'ori', 'xori', 'andi', 'slli', 'srli/srai', 'and/or/xor', 'sll', 'sll/srl/sra'}),
               ('stack spill', {'stack spill'}), ('FP register', {'FP register'}), ('CSR', {'CSR'}),
               ('fall-through into a jump-table arm', {'fall-through into a jump-table arm'}),
               ('indirect jump (edge to every word)', {'indirect jump (edge to every word)'}),
               ('in-function call', {'in-function call'}), ('call result', {'call result'}),
               ('c.lui', {'c.lui'}), ('built without lui', {'built without lui'}),
               ('two or more lui words', {'two or more lui words'})]


def scan_function(im, v, z, fn, tables):
    """(rows, notes) of one function in one image: a dict per base site or store row, and notes on its control flow"""
    words, succ, pred, tabs = regdef.cfg(im.s3, im.img, v, z, fn, tables, 'addrsite.py')
    LV.clear()
    LV.update({o: source_value(w) for o, w in words.items() if source_value(w) is not None})
    AUIPC.clear()
    AUIPC.update({o: v + o + sx(w & 0xfffff000, 32) for o, w in words.items() if w & 0x7f == 0x17})
    notes = []
    targets = {e for d, (ta, ents) in tabs.items() for e in ents}
    wide = sorted(o for o, w in words.items() if w & 0x7f == 0x67 and (w >> 7) & 31 == 0 and not (
        (w >> 15) & 31 == RA and w >> 20 == 0) and o not in tabs)
    inf = sorted(o for o, w in words.items() if w & 0x7f == 0x6f and (w >> 7) & 31 and
                 regdef.btarget(v + o, w) - v in words)
    rets = sorted(o for o, w in words.items() if w & 0x7f == 0x67 and (w >> 7) & 31 == 0 and (w >> 15) & 31 == RA and
                  w >> 20 == 0)
    inside = sorted(o for o, w in words.items() if w & 0x7f == 0x17 and o + 4 in words and
                    words[o + 4] & 0x7f in (0x03, 0x13, 0x67) and (words[o + 4] >> 15) & 31 == (w >> 7) & 31 and
                    v <= v + o + sx(w & 0xfffff000, 32) + sx(words[o + 4] >> 20, 12) < v + z)
    if inside:
        wide = sorted(set(wide) | {o for o, w in words.items() if w & 0x7f == 0x67 and o not in tabs})
        notes.append('auipc pairs that build an address inside the function at %s: every jalr gets an edge to '
                     'every word' % ', '.join('+%#x' % o for o in inside))
    for o in wide:
        succ[o] = sorted(set(succ[o]) | set(words))
    for o in inf:
        succ[o] = sorted(set(succ[o]) | {regdef.btarget(v + o, words[o]) - v})
        for r in rets:
            succ[r] = sorted(set(succ[r]) | {o + 4})
    if wide:
        notes.append('indirect jumps with no listed table at %s: an edge to every word' % ', '.join(
            '+%#x' % o for o in wide))
    if inf:
        notes.append('calls inside the function at %s (to %s): an edge to the target, and from every return to the '
                     'word after the call' % (', '.join('+%#x' % o for o in inf), ', '.join(
                         '+%#x' % (regdef.btarget(v + o, words[o]) - v) for o in inf)))

    def edge_tag(o, t, st):
        if o in wide:
            return tag_state(st, 'indirect jump (edge to every word)')
        if (o in inf and t != o + 4) or (o in rets and inf):
            return tag_state(st, 'in-function call')
        if t == o + 4 and t in targets:
            return tag_state(st, 'fall-through into a jump-table arm')
        return st
    init = (tuple([const(0), term(('arg', 1)), term(('sp',))] + [term(('arg', x)) for x in range(3, 32)]),
            tuple([None] * 32), frozenset(), frozenset())
    state = fixpoint(words, succ, init, edge_tag)
    dead = sorted(set(words) - set(state))
    if dead:
        notes.append('words no path from the entry reaches: %s' % ', '.join(
            '+%#x %s' % (o, mnem(words[o])) for o in dead))
    rows = []
    for o in sorted(state):
        w = words[o]
        b = base_of(w)
        if b is None:
            continue
        regs, fregs = state[o][0], state[o][1]
        cand = []
        if taint(regs[b]):
            cand.append(('base', b, regs[b], simm(w) if w & 0x7f != 0x67 else sx(w >> 20, 12), None))
        if w & 0x7f in (0x23, 0x27, 0x2f) and exact_sp(regs[b]) is None and not (w & 0x7f == 0x2f and w >> 27 == 2):
            d = regs[(w >> 20) & 31] if w & 0x7f != 0x27 else fregs[(w >> 20) & 31]
            if d is not None and taint(d):
                cand.append(('store', (w >> 20) & 31, d, 0, width(w)))
        for kind, reg, val, mo, sw in cand:
            srcs = sorted(taint(val))
            shapes = {y[1] for y in tt_of(val) if isinstance(y, tuple) and y[0] == 's'}
            if kind == 'base' and mo:
                shapes.add('site immediate')
            if any(words[x] & 0x7f != 0x37 for x in srcs):
                shapes.add('built without lui')
            if sum(1 for x in srcs if words[x] & 0x7f == 0x37) >= 2:
                shapes.add('two or more lui words')
            kd, det, ck = trace(im, val, mo, sw)
            rows.append(dict(kind=kind, off=o, word=regdef.text(v + o, w).split(' ', 1)[1],
                             reg=('f%d' if kind == 'store' and w & 0x7f == 0x27 else 'x%d') % reg,
                             srcs=' | '.join('+%#x %s (%s)' % (x, regdef.text(v + x, words[x]).split(' ', 1)[1],
                                                               hx(LV[x])) for x in srcs),
                             shapes=sorted(shapes), trace=kd, detail=det, forms=show_value(val), key=ck))
    return rows, notes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('kit')
    ap.add_argument('pairs')
    ap.add_argument('images', nargs='+')
    ap.add_argument('--table', action='append', default=[])
    a = ap.parse_args()
    spec = importlib.util.spec_from_file_location('strictcmp3', os.path.join(a.kit, 'strictcmp3.py'))
    s3 = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(s3)
    tables = {}
    for t in a.table:
        fn, o, n = t.split(':')
        tables.setdefault(fn, []).append((int(o, 16), int(n)))
    rows = [r for r in csv.DictReader(open(a.pairs), delimiter='\t') if r['pairing'] != 'absent']
    imgs = [x.split('=', 1) for x in a.images]
    tags = [t for t, p in imgs]
    out, notes, compact, per = [], [], [], {}
    for tg, path in imgs:
        im = Image(s3, path)
        for r in rows:
            fn = r['fm function']
            key = fn if sum(1 for x in rows if x['fm function'] == fn) == 1 else '%s (copy at fm %s)' % (
                fn, r['fm addr'])
            v, z = int(r[tg + ' addr'], 16), int(r[tg + ' size'])
            compared = len({r[t + ' size'] for t in tags}) == 1
            try:
                frows, fnotes = scan_function(im, v, z, fn, tables.get(fn, []))
            except SystemExit as e:
                notes.append('# %s %s: not scanned: %s' % (tg, key, e))
                per[(tg, key)] = None
                continue
            notes += ['# %s %s: %s' % (tg, key, n) for n in fnotes]
            per[(tg, key)] = (compared, frows)
            if not compared:
                b = [x for x in frows if x['kind'] == 'base']
                s = [x for x in frows if x['kind'] == 'store']
                compact.append('# %s %s: not compared (sizes %s): %d base sites (%s); %d store rows (%s)' % (
                    tg, key, ', '.join('%s %s' % (t, r[t + ' size']) for t in tags), len(b),
                    ', '.join('+%#x' % x['off'] for x in b) or 'none', len(s),
                    ', '.join('+%#x' % x['off'] for x in s) or 'none'))
                continue
            for x in frows:
                out.append([tg, key, '%#x' % v, x['kind'], '+%#x' % x['off'], x['word'], x['reg'], x['srcs'],
                            ', '.join(x['shapes']), x['trace'], x['detail'], x['forms'], x['key']])
    names = sorted({r['fm function'] for r in rows})
    print('# sites where a value built from an immediate word may reach a base, and stores of such values that are '
          'not followed; kit %s; names scanned per image: %d; twins: %s' % (
              hashlib.sha256(open(os.path.join(a.kit, 'SHA256SUMS'), 'rb').read()).hexdigest()[:12], len(names),
              ', '.join('%s %s sha256 %s' % (t, os.path.basename(p), regdef.sha(p)) for t, p in imgs)))
    for n in notes + compact:
        print(n)
    for tg in tags:
        fr = [(k, x) for (t, k), pv in sorted(per.items()) if t == tg and pv and pv[0] for x in pv[1]]
        b = [x for k, x in fr if x['kind'] == 'base']
        s = [x for k, x in fr if x['kind'] == 'store']
        print('# %s compared functions: %d with a base site (%s); %d base sites, %d store rows' % (
            tg, len({k for k, x in fr if x['kind'] == 'base'}),
            ', '.join(sorted({k for k, x in fr if x['kind'] == 'base'})) or 'none', len(b), len(s)))
        for kind, xs in (('base sites', b), ('store rows', s)):
            print('# %s %s by shape: %s' % (tg, kind, '; '.join(
                '%s %d' % (nm, sum(1 for x in xs if set(x['shapes']) & sh)) for nm, sh in SHAPE_ORDER)))
            tr = {}
            for x in xs:
                tr[x['trace']] = tr.get(x['trace'], 0) + 1
            print('# %s %s by scan trace: %s' % (tg, kind, '; '.join(
                '%s %d' % kv for kv in sorted(tr.items())) or 'none'))
    print('image\tfunction\tfunction address\tkind\tsite\tsite word\tregister (base, or data of a store)\timmediate '
          'words it may carry (offset, word, value)\tshapes\tscan trace\ttrace detail (the word offset added)\ttainted '
          'forms of the register (without the word offset)')
    for r in out:
        print('\t'.join(r[:12]))
    print('# across the images, per site of a compared function: the scan trace in each image and the verdict')
    print('cross\tfunction\tkind\tsite\tscan trace per image\tverdict')
    for fn, kind, site in sorted({(r[1], r[3], r[4]) for r in out}, key=lambda k: (k[0], int(k[2][1:], 16), k[1])):
        rs = {r[0]: r for r in out if r[1] == fn and r[3] == kind and r[4] == site}
        tr = ' | '.join('%s: %s' % (t, rs[t][9]) if t in rs else '%s: no site' % t for t in tags)
        kinds = {rs[t][9] for t in rs}
        k0 = rs[tags[0]][9] if tags[0] in rs else None
        if len(rs) != len(tags):
            verdict = 'NOT IN EVERY IMAGE'
        elif len({rs[t][5].split(' ')[0] for t in rs}) != 1:
            verdict = 'DIFFERENT words'
        elif len(kinds) != 1 or k0 == 'not traced':
            verdict = 'not traced'
        elif len({rs[t][12] for t in rs}) == 1:
            verdict = 'same object up to relocation' if any(
                x in k0 for x in ('absolute address', 'TLS address', 'gp address')) else '%s in every image' % k0
        else:
            verdict = 'DIFFERENT OBJECT' if any(
                x in k0 for x in ('absolute address', 'TLS address', 'gp address')) else 'DIFFERENT %s' % k0
        print('\t'.join(['cross', fn, kind, site, tr, verdict]))


if __name__ == '__main__':
    main()
