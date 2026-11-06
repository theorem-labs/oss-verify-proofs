#!/usr/bin/env python3
"""Is a lui-built value used as an image address? A hand argument for a `lui-in-section` target of the comparison kit,
measured in the fm twin and in each fuzz_disco twin.

  luiuse.py KIT_DIR FUNC OFFSET [--table OFF:N ...] [--callees TABLE] [--bias BASE:GUARD:WORD,WORD,...] TAG=TWIN ...
      (the first TAG is the reference, the fm twin)

KIT_DIR: the comparison kit (strictcmp3's Img, frd, qres and section lookup are used; nothing is copied from it). FUNC:
a function name that exactly one sized FUNC symbol of each twin carries. OFFSET: the target as the kit reports it: a
`lui` word (its own value is read) or the word that completes a lui pair (addi / addiw on the register that, on every
path reaching it, one lui alone defines). --table OFF:N: the rel4 jump tables of the function (regdef.py's control
flow). The function must have no 2-byte parcel.

Two walks follow the value forward over the control flow (branches, jumps, the table entries; a call ends a path for a
caller-saved register) from where it is made, through every word that reads its register before the register is
written again (and, for a pair, the lui's own register up to the pair).
FIRST LEVEL:
  - a copy or pair (addi / addiw rd, reg, imm) and integer arithmetic (add / sub / mul / div / rem, 32-bit forms)
    continue with their result;
  - a logical, shift or compare read (and / or / xor / sll / srl / sra / slt / sltu, immediate forms) or a branch
    compare ends the path (the kit's own `lui-const` reads);
  - a store to a stack slot (base sp) is a spill: the loads of that slot that a path from the store reaches before the
    slot is stored again continue with their register; it is followed only when sp is written only by the prologue and
    the epilogue, no stack address at or below the slot end is taken and no other access overlaps the slot;
  - flagged (ADDRESS USES): a load / store / jalr / AMO base, store data other than a followed spill, a0-a7 at a call
    or a tail jump, a0 / a1 at a return, an indirect jump that is no listed table, any other read.
TRANSITIVE: the same walk, but a logical / shift / compare result is followed too, and a store to a frame slot (base
s0) is a spill like a stack slot, followed only when s0 is written only by one frame setup `addi s0, sp, N` and by
restores that run straight to a return, no frame address at or below the slot end is taken (other than the epilogue's
`addi sp, s0, -N`) and no other access overlaps it; the sp-relative words after the setup that could alias the slot
are listed as facts. With --bias, a value along a chain is marked net 0 once it is a formed address that carries no
part of the constant (evaluated as below: an operand of the base word BASE with coefficient 1, the lui value and the
other lui-built constants summing to 0); every value derived from a net-0 value is net 0 too, and the walk goes on
through all of them. Every use the transitive walk flags is put in one class:
  - `call argument not read by the callee`: the register is a0-a7 at a call (directly, or through a trampoline that is
    one jump) whose callee takes fewer integer arguments than the register's number, as the callee table says
    (--callees: callee, integer argument registers, prototype, the source text it was read from);
  - `not an image address: a numeric bias` (--bias only): the use lies on a chain through the base word BASE, and
    either the value it reads, evaluated along the chain, contains an operand of the base word (the independent base)
    with coefficient 1 and the lui value and the other lui-built constants contribute 0 to it together (a formed
    address), or the value it reads is net 0 (a value derived from such an address: it holds no part of the constant);
  - `address use`: any other.
The evaluation writes the value as a sum: the lui value times a coefficient, the other lui-built constants (the upper
part a lui builds; the low part its addi / addiw adds counts as an immediate), the immediates and memory offsets, and
named runtime terms (a register at a word, with the words that define it). 32-bit forms are summed without their wrap.
A mul by a constant M, then srai by s, is a division by d = round(2**s / M), accepted only when M = ceil(2**s / d) and d
divides the lui value's contribution: the lui value's share of the quotient is that contribution / d, and the rest of
the srai result becomes one named term; with the product's sign (srli 63, a named term) added, as in the signed
division idiom, the two named terms sum to the floor of the rest / d when the whole dividend is >= 0 and to its ceiling
when it is < 0 (GUARD and its operands are listed).
Columns: the first-level uses, slot facts, flagged count and verdict; the transitive uses, slot facts, flagged count,
the class of each flagged use (with the words of its chain), the chain words and bias facts (--bias), the transitive
verdict; `what the instruction does`: `settled: ...` only when no transitive use is of class `address use`, else `not
settled by this measurement`; `reason`: the claim the kit's lui-in-section rule protects and why the classes meet it.
"""
import argparse
import csv
import hashlib
import importlib.util
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True                     # no cache file beside the shipped scripts
import regdef                                      # noqa: E402  (control flow, word decoding)

SP, RA, FP = 2, 1, 8
ARGREGS = set(range(10, 18))
LOGICAL = {(0x33, 0x00, f) for f in (1, 2, 3, 4, 5, 6, 7)} | {(0x33, 0x20, 5), (0x3b, 0x00, 1), (0x3b, 0x00, 5),
                                                              (0x3b, 0x20, 5)}
ARITH = {(0x33, 0x00, 0), (0x33, 0x20, 0), (0x3b, 0x00, 0), (0x3b, 0x20, 0)} | \
        {(op, 0x01, f) for op in (0x33, 0x3b) for f in range(8)}
M64 = (1 << 64) - 1
CALL_CLASS, BIAS_CLASS, ADDR_CLASS = ('call argument not read by the callee', 'not an image address: a numeric bias',
                                      'address use')


def f(w):
    return w & 0x7f, (w >> 7) & 31, (w >> 12) & 7, (w >> 15) & 31, (w >> 20) & 31, w >> 25


def simm(w):
    op = w & 0x7f
    if op in (0x23, 0x27):
        return regdef.sx(((w >> 25) << 5) | ((w >> 7) & 31), 12)
    return regdef.sx(w >> 20, 12)


def width(w):
    op, f3 = w & 0x7f, (w >> 12) & 7
    return {0: 1, 1: 2, 2: 4, 3: 8, 4: 1, 5: 2, 6: 4}.get(f3) if op in (0x03, 0x23) else {2: 4, 3: 8}.get(f3)


def reads(w):
    """the integer registers word w reads (x0 left out); an ecall reads a0-a7"""
    op, rd, f3, rs1, rs2, f7 = f(w)
    if op in (0x33, 0x3b, 0x2f, 0x63, 0x23):
        r = (rs1, rs2)
    elif op in (0x13, 0x1b, 0x03, 0x07, 0x67, 0x27):
        r = (rs1,)
    elif op == 0x73:
        r = (rs1,) if f3 in (1, 2, 3) else tuple(ARGREGS) if w == 0x73 else ()
    elif op == 0x53:
        r = (rs1,) if (w >> 27) in (0x1a, 0x1e) else ()
    else:
        r = ()
    return {x for x in r if x}


def classify(words, o, reg, trans=False):
    """how word o reads integer register reg: (kind, flagged?, what to follow next: (register, 'pair' / 'arith' /
    'logic'), ('slot', base, offset, width) or None); kind None when o does not read reg. trans: a logical / shift /
    compare result and a frame-slot spill are followed too"""
    w = words[o]
    if reg not in reads(w):
        return None, False, None
    op, rd, f3, rs1, rs2, f7 = f(w)
    if op in (0x03, 0x07):
        return 'load base', True, None
    if op in (0x23, 0x27):
        if rs1 == reg:
            return 'store base', True, None
        if rs1 == SP:
            return 'stack spill sp%+#x (%d bytes)' % (simm(w), width(w)), False, ('slot', SP, simm(w), width(w))
        if rs1 == FP and trans:
            return 'frame spill s0%+#x (%d bytes)' % (simm(w), width(w)), False, ('slot', FP, simm(w), width(w))
        return 'store data', True, None
    if op == 0x67:
        return 'jalr base', True, None
    if op == 0x2f:
        return ('AMO address' if rs1 == reg else 'AMO data'), True, None
    if op in (0x13, 0x1b):
        if f3 == 0:
            return ('copy' if simm(w) == 0 else 'pair %+d' % simm(w)), False, (rd, 'pair') if rd else None
        return 'logical / shift / compare (immediate)', False, (rd, 'logic') if rd and trans else None
    if op in (0x33, 0x3b):
        if (op, f7, f3) in LOGICAL:
            return 'logical / shift / compare', False, (rd, 'logic') if rd and trans else None
        if (op, f7, f3) in ARITH:
            return 'arithmetic', False, (rd, 'arith') if rd else None
        return 'other R-type read', True, None
    if op == 0x63:
        return 'branch compare', False, None
    if op == 0x53:
        return 'conversion to floating point', False, None
    if op == 0x73 and w == 0x73:
        return 'ecall argument', True, None
    return 'other read', True, None


LABEL = {'pair': 'copy / pair', 'arith': 'arithmetic result', 'logic': 'logical result'}


def follow(words, succ, start, reg, how, res, stop=(), trans=False, trail=(), cut=None, net0=False):
    """walk reg forward from the successors of word `start` (a word in `stop` ends a path unread); append (offset,
    how, kind, flagged, trail, net0) to res and return the spill slots met (offset, base register, slot, width, trail,
    net0). trail: the words through which the value was derived, in order. cut (--bias): a function of a trail that
    says whether the value it derives is a formed address that carries no part of the constant; net0 marks a value
    that is such an address or is derived from one (it holds no part of the constant)"""
    slots, seen, work = [], set(), [(t, reg, how, trail, net0) for t in succ[start]]
    while work:
        o, r, h, tr, n0 = work.pop()
        if (o, r, n0) in seen or o not in words or o in stop:
            continue
        seen.add((o, r, n0))
        w = words[o]
        op, rd = w & 0x7f, (w >> 7) & 31
        kind, bad, nxt = classify(words, o, r, trans)
        if kind:
            res.append((o, h, kind, bad, tr, n0))
            if nxt and nxt[0] == 'slot':
                slots.append((o, nxt[1], nxt[2], nxt[3], tr, n0))
            elif nxt:
                m0 = n0 or bool(cut and cut(tr + (o,)))
                work += [(t, nxt[0], '%s via +%#x%s' % (LABEL[nxt[1]], o, ' (net 0 from here)' if m0 and not n0
                                                       else ''), tr + (o,), m0) for t in succ[o]]
        if op in (0x6f, 0x67) and rd != 0 and r in ARGREGS:
            res.append((o, h, 'call argument (a0-a7 at a call: x%d)' % r, True, tr, n0))
        if op == 0x67 and rd == 0:
            ret = (w >> 15) & 31 == RA and w >> 20 == 0
            if ret and r in (10, 11):
                res.append((o, h, 'return value', True, tr, n0))
            if not ret and not succ[o]:
                res.append((o, h, 'indirect jump with no listed table', True, tr, n0))
            if not succ[o]:
                continue
        if op == 0x6f and rd == 0 and succ[o][0] not in words:
            if r in ARGREGS:
                res.append((o, h, 'tail-jump argument', True, tr, n0))
            continue
        wr = regdef.writes(w)
        if wr == r or (wr == 'call' and r in regdef.CALLER_SAVED):
            continue
        work += [(t, r, h, tr, n0) for t in succ[o]]
    return slots


def slot_facts(words, off, wd):
    """(problems, loads of the slot) for the stack slot sp+off of width wd: sp may be written only by the prologue
    (word 0, addi sp, sp, -N) and by epilogues (addi sp, sp, N); no stack address at or below the slot end taken; sp read
    by no other word than a load / store base; no access that overlaps the slot without being it"""
    probs, loads = [], []
    w0 = words[0]
    frame = -simm(w0) if f(w0)[:2] == (0x13, SP) and f(w0)[3] == SP and simm(w0) < 0 else None
    for o, w in sorted(words.items()):
        op, rd, f3, rs1, rs2, f7 = f(w)
        if regdef.writes(w) == SP and not (o == 0 and frame) and not (op == 0x13 and rs1 == SP and simm(w) == frame):
            probs.append('+%#x writes sp' % o)
        if op in (0x13, 0x1b) and rs1 == SP and rd != SP and simm(w) <= off + wd - 1:
            probs.append('+%#x takes the stack address sp%+#x' % (o, simm(w)))
        if op in (0x33, 0x3b, 0x63, 0x2f) and SP in (rs1, rs2) or (op == 0x23 and rs2 == SP) or (op == 0x67 and rs1 == SP):
            probs.append('+%#x reads sp' % o)
        if op in (0x03, 0x07, 0x23, 0x27) and rs1 == SP:
            a, n = simm(w), width(w)
            if n and a < off + wd and off < a + n:
                if (a, n) != (off, wd) or op in (0x07, 0x27):
                    probs.append('+%#x accesses sp%+#x (%d bytes), overlapping the slot' % (o, a, n))
                elif op == 0x03:
                    loads.append((o, rd))
    return probs, loads


def frame_slot_facts(words, succ, off, wd):
    """(problems, loads of the slot, facts) for the frame slot s0+off of width wd (see the module text)"""
    probs, loads, facts = [], [], []
    setup = [(o, simm(w)) for o, w in words.items() if regdef.writes(w) == FP and f(w)[0] == 0x13 and f(w)[3] == SP]
    if len(setup) != 1:
        return ['%d frame setups (addi s0, sp, N)' % len(setup)], [], facts
    so, n = setup[0]
    for o, w in sorted(words.items()):
        op, rd, f3, rs1, rs2, f7 = f(w)
        if regdef.writes(w) == FP and o != so:
            k, ok = o, op == 0x03 and rs1 == SP
            while ok and not (f(words[k])[0] == 0x67 and f(words[k])[3] == RA and words[k] >> 20 == 0):
                k += 4
                ok = k in words and FP not in reads(words[k]) and succ[k - 4] == [k]
            if not ok:
                probs.append('+%#x writes s0' % o)
        if op in (0x13, 0x1b) and rs1 == FP and simm(w) <= off + wd - 1 and not (rd == SP and simm(w) == -n):
            probs.append('+%#x takes the frame address s0%+#x' % (o, simm(w)))
        if FP in reads(w) and not (op in (0x03, 0x07, 0x23, 0x27) and rs1 == FP and not (op == 0x23 and rs2 == FP)) \
                and not (op in (0x13, 0x1b) and rs1 == FP) and not (op == 0x23 and rs2 == FP and o < so):
            probs.append('+%#x reads s0' % o)
        if op in (0x03, 0x07, 0x23, 0x27) and rs1 == FP:
            a, m = simm(w), width(w)
            if m and a < off + wd and off < a + m:
                if (a, m) != (off, wd) or op in (0x07, 0x27):
                    probs.append('+%#x accesses s0%+#x (%d bytes), overlapping the slot' % (o, a, m))
                elif op == 0x03:
                    loads.append((o, rd))
        if o > so and (regdef.writes(w) == SP or (op in (0x13, 0x1b) and rs1 == SP and rd != SP)):
            facts.append('+%#x %s' % (o, 'writes sp' if regdef.writes(w) == SP else 'takes sp%+#x' % simm(w)))
    return probs, loads, ['frame setup +%#x addi s0, sp, %#x (the slot is sp%+#x there)' % (so, n, n + off)] + \
        (['sp-relative words after the setup (possible aliases of the slot, not excluded): ' + ', '.join(facts)]
         if facts else [])


def reached_loads(words, succ, so, base, sa, sw):
    """the loads of the slot base+sa (sw bytes) that a path from the store at `so` reaches before a store to an
    overlapping slot of the same base"""
    out, seen, work = set(), set(), list(succ[so])
    while work:
        o = work.pop()
        if o in seen or o not in words:
            continue
        seen.add(o)
        w = words[o]
        op, rd, f3, rs1, rs2, f7 = f(w)
        if op in (0x03, 0x07, 0x23, 0x27) and rs1 == base:
            a, m = simm(w), width(w)
            if m and a < sa + sw and sa < a + m:
                if op in (0x23, 0x27):
                    continue
                if op == 0x03 and (a, m) == (sa, sw):
                    out.add((o, rd))
        work += succ[o]
    return sorted(out)


def chain(words, succ, lui, off, rd, trans, cut=None):
    """every reached use of the value made at `off` (and of the lui's own register up to it), spills followed; trans:
    logical / shift / compare results and frame-slot spills followed too; cut: see follow(). -> (uses sorted, each
    (offset, how, kind, flagged, trail); slot facts)"""
    res, facts = [], []
    if lui != off:
        # the lui's own register from the lui to the pair: any other read is a use of the high part alone
        follow(words, succ, lui, (words[lui] >> 7) & 31, 'lui value', res, stop={off}, trans=trans)
    slots = follow(words, succ, off, rd, 'the value', res, trans=trans, cut=cut)
    done = set()
    while slots:
        so, base, sa, sw, tr, n0 = slots.pop()
        if (so, base, sa, sw, n0) in done:
            continue
        done.add((so, base, sa, sw, n0))
        if base == SP:
            probs, every = slot_facts(words, sa, sw)
            more = ['sp written only by the prologue and the epilogue, no stack address at or below the slot taken, '
                    'no overlapping access'] if not probs else []
        else:
            probs, every, more = frame_slot_facts(words, succ, sa, sw)
        loads = reached_loads(words, succ, so, base, sa, sw)
        name = '%s%+#x' % ('sp' if base == SP else 's0', sa)
        line = 'slot %s (%d bytes), stored at +%#x: %s; loads reached from the store: %s (of %d loads of the slot)' % (
            name, sw, so, '; '.join(probs + more), ', '.join('+%#x' % o for o, r in loads) or 'none', len(every))
        if line not in facts:
            facts.append(line)
        if probs:
            res.append((so, 'the value', 'spill to %s not followed (%s)' % (name, '; '.join(probs)), True, tr, n0))
            continue
        for lo, lr in loads:
            res.append((lo, 'reload of %s' % name, 'reload', False, tr + (so,), n0))
            slots += follow(words, succ, lo, lr, 'reload at +%#x' % lo, res, trans=trans, trail=tr + (so, lo),
                            cut=cut, net0=n0)
    uniq = {}
    for r in res:
        uniq.setdefault(r[:4] + (r[5],), r)
    return sorted(uniq.values(), key=lambda r: r[:4] + (r[5],)), facts


def const_of(words, pred, at, reg):
    """(upper, low): the value of reg at word `at` when, on every path, one lui (upper), or one addi / addiw on a
    register so built or on x0 (low), defines it; else None"""
    if reg == 0:
        return 0, 0
    d = regdef.reaching(words, pred, at, reg)
    if len(d) != 1:
        return None
    w = words[d[0]]
    op, rd, f3, rs1 = f(w)[:4]
    if op == 0x37:
        return regdef.sx(w & 0xfffff000, 32), 0
    if op in (0x13, 0x1b) and f3 == 0:
        b = const_of(words, pred, d[0], rs1)
        if b is None:
            return None
        up, lo = b[0], b[1] + simm(w)
        if op == 0x1b:
            up = regdef.sx((up + lo) & 0xffffffff, 32) - lo
        return up, lo
    return None


def term_name(words, pred, at, reg):
    return 'x%d (defined at %s)' % (reg, ', '.join('+%#x' % d for d in regdef.reaching(words, pred, at, reg)) or
                                    'function entry')


def text_of(e, val):
    """a value of evaluate() as text"""
    parts = []
    if e.get('V'):
        parts.append('%s * the lui value = %s%#x' % (e['V'], '-' if e['V'] < 0 else '+', abs(int(e['V'] * val))))
    if e.get('L'):
        parts.append('other lui-built constants %s%#x' % ('-' if e['L'] < 0 else '+', abs(e['L'])))
    if e.get('K'):
        parts.append('immediates %s%#x' % ('-' if e['K'] < 0 else '+', abs(e['K'])))
    parts += ['%s * %s' % (c, k) for k, c in e.items() if k not in ('V', 'L', 'K') and c]
    return ' + '.join(parts) or '0'


def evaluate(words, pred, rd, val, path, final=True):
    """the value the last word of `path` reads (final) or derives (not final), as a sum along the chain `path` (the
    words through which it is derived from the lui value, made in register rd): {'V': coefficient of the lui value, 'L':
    other lui-built constants, 'K': immediates and offsets, named term: coefficient}; None when a word of the chain is
    outside the forms of the module text"""
    reg, e, pend = rd, {'V': Fraction(1), 'L': 0, 'K': 0}, None
    for i, s in enumerate(path):
        w = words[s]
        op, d_, f3, rs1, rs2, f7 = f(w)
        if final and i == len(path) - 1:
            if op in (0x03, 0x07, 0x23, 0x27) and rs1 == reg:
                e = dict(e)
                e['K'] += simm(w)
            return e
        if op in (0x23, 0x27) and rs2 == reg:              # a spill; the next word of the chain is its reload
            continue
        if op in (0x03, 0x07) and i > 0 and words[path[i - 1]] & 0x7f in (0x23, 0x27):
            reg = d_
            continue
        other = [x for x in reads(w) if x != reg]
        if pend is not None:
            sh = (w >> 20) & 63
            if not (op == 0x13 and f3 == 5 and rs1 == pend[1]):
                return None
            M, pe = pend[0], pend[2]
            if sh == 63 and not (w >> 30) & 1:              # srli 63: the product's sign
                e = {'V': Fraction(0), 'L': 0, 'K': 0, 'sign of the product (%s) * %#x' % (text_of(pe, val), M):
                     Fraction(1)}
            elif (w >> 30) & 1:                             # srai: a division
                dv = round(2 ** sh / M)
                if dv <= 0 or M != -(-(2 ** sh) // dv) or (pe['V'] * val) % dv:
                    return None
                rest = dict(pe, V=Fraction(0))
                e = {'V': pe['V'] / dv, 'L': 0, 'K': 0, 'quotient (%s) / %d' % (text_of(rest, val), dv): Fraction(1)}
            else:
                return None
            pend = None
        elif op in (0x13, 0x1b) and f3 == 0:
            e = dict(e)
            e['K'] += simm(w)
        elif op in (0x13, 0x1b) and f3 == 1:
            e = {k: c * 2 ** ((w >> 20) & 63) for k, c in e.items()}
        elif op in (0x33, 0x3b) and (f7, f3) in ((0, 0), (0x20, 0)) and len(other) == 1:
            neg = f7 == 0x20 and rs2 == reg                 # other - value
            e = {k: (-c if neg else c) for k, c in e.items()}
            sign = -1 if f7 == 0x20 and not neg else 1
            c = const_of(words, pred, s, other[0])
            if c is not None:
                e['L'] += sign * c[0]
                e['K'] += sign * c[1]
            else:
                key = term_name(words, pred, s, other[0])
                e[key] = e.get(key, 0) + sign
        elif op in (0x33, 0x3b) and f7 == 1 and f3 == 0 and len(other) == 1:
            c = const_of(words, pred, s, other[0])
            if c is None:
                return None
            pend = ((c[0] + c[1]) & M64, d_, e)
        else:
            return None
        reg = d_
    return e if pend is None else None


def tree(v, words, pred, at, reg, depth, seen=()):
    """how reg is defined at word `at`: its defining words, each with the definitions of the registers it reads, to
    `depth` levels (sp, x0 and a load, lui, auipc or call end a branch)"""
    if reg == SP:
        return 'sp'
    ds = regdef.reaching(words, pred, at, reg)
    if not ds:
        return 'x%d at function entry' % reg
    out = []
    for d in ds:
        w = words[d]
        t = '+%#x %s' % (d, ins(v, words, d))
        if depth > 1 and d not in seen and w & 0x7f not in (0x03, 0x07, 0x37, 0x17, 0x6f, 0x67) and reads(w):
            t += ' [%s]' % '; '.join('x%d = %s' % (x, tree(v, words, pred, d, x, depth - 1, seen + (d,)))
                                     for x in sorted(reads(w)))
        out.append(t)
    return ' or '.join(out)


def callee_of(s3, img, v, words, o):
    """(the callee's names, the trampoline text) of the call at o"""
    if words[o] & 0x7f != 0x6f:
        return [], ''
    t = regdef.btarget(v + o, words[o])
    names, hop = [n.split('+')[0] for n in (s3.qres(img, t) or '').split('/')], ''
    tw = s3.frd(img, t, 4)
    tw = int.from_bytes(tw, 'little') if tw else 0
    if tw & 0x7f == 0x6f and (tw >> 7) & 31 == 0:           # a trampoline: one jump to the callee
        q = s3.qres(img, regdef.btarget(t, tw)) or ''
        names, hop = [n.split('+')[0] for n in q.split('/')], ' (a trampoline: j %s)' % q
    return names, hop


def classify_uses(s3, img, v, words, pred, rd, val, tbad, callees, base, cut):
    """[(offset, class, detail)] for every flagged use of the transitive walk. A numeric-bias detail starts with
    `formed address` (the value read is evaluated: the independent base with coefficient 1, net contribution 0) or
    `derived value` (the value read is derived from such an address at the word it names: it holds no part of the
    constant)"""
    out = []
    indep = [term_name(words, pred, base, x) for x in sorted(reads(words[base]))] if base is not None else []
    for o, h, k, bad, tr, n0 in tbad:
        trail = ' > '.join('+%#x' % x for x in tr + (o,))
        if k.startswith('call argument'):
            x = int(k.rsplit('x', 1)[1].rstrip(')'))
            names, hop = callee_of(s3, img, v, words, o)
            n = next((callees[nm] for nm in names if nm in callees), None)
            if n is not None and x - 10 >= n:
                out.append((o, CALL_CLASS, 'a%d live at the call to %s%s, which takes %s (callee table)' % (
                    x - 10, '/'.join(names), hop, 'no argument' if n == 0 else 'a0-a%d' % (n - 1))))
                continue
            k = 'a%d at the call to %s%s: %s' % (x - 10, '/'.join(names) or '?', hop, 'callee not in the callee '
                                                 'table' if n is None else 'one of its arguments')
        if base is not None and base in tr:
            e = evaluate(words, pred, rd, val, tr + (o,))
            net = None if e is None else e['V'] * val + e['L']
            if e is not None and net == 0 and any(e.get(t) == 1 for t in indep):
                out.append((o, BIAS_CLASS, 'formed address: %s = %s; the lui value and the other lui-built constants '
                            'together: +0x0; chain %s' % (k, text_of(e, val), trail)))
                continue
            if n0:
                at = next(tr[i] for i in range(len(tr)) if cut(tr[:i + 1]))
                out.append((o, BIAS_CLASS, 'derived value: %s, derived from the formed address made at +%#x (net '
                            'contribution 0 there; it holds no part of the constant); chain %s' % (k, at, trail)))
                continue
            out.append((o, ADDR_CLASS, '%s = %s; chain %s' % (k, 'not evaluated' if e is None else '%s (net %s%#x)' % (
                text_of(e, val), '-' if net < 0 else '+', abs(int(net))), trail)))
            continue
        out.append((o, ADDR_CLASS, '%s; chain %s' % (k, trail)))
    return out


def ins(v, words, o):
    return regdef.text(v + o, words[o]).split(' ', 1)[1]


def uses(res):
    return ' | '.join('+%#x: %s: %s%s%s' % (o, h, k, ' [net 0]' if n0 else '', ' (FLAGGED)' if b else '')
                      for o, h, k, b, tr, n0 in res)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('kit')
    ap.add_argument('func')
    ap.add_argument('offset')
    ap.add_argument('images', nargs='+')
    ap.add_argument('--table', action='append', default=[])
    ap.add_argument('--callees', help='callee table: callee, integer argument registers, prototype, source')
    ap.add_argument('--bias', help='BASE:GUARD:WORD,...: the base word where the independent base is added, the guard, '
                                   'and the chain words to list')
    a = ap.parse_args()
    spec = importlib.util.spec_from_file_location('strictcmp3', os.path.join(a.kit, 'strictcmp3.py'))
    s3 = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(s3)
    off = int(a.offset, 16)
    tables = [(int(t.split(':')[0], 16), int(t.split(':')[1])) for t in a.table]
    base = guard = None
    listed = []
    if a.bias:
        b, g, ws = a.bias.split(':')
        base, guard, listed = int(b, 16), int(g, 16), sorted({int(x, 16) for x in ws.split(',')})
    callees = {}
    if a.callees:
        for r in csv.DictReader(open(a.callees), delimiter='\t'):
            regs = r['integer argument registers']
            callees[r['callee']] = 0 if regs == 'none' else int(regs.split('-')[-1].lstrip('a')) + 1
    rows, vals = [], []
    for tag, path in (x.split('=', 1) for x in a.images):
        img = s3.Img(path)
        c = [(v, z) for v, z, t in img.byname.get(a.func, ()) if t == 'STT_FUNC' and z > 0]
        if len(set(c)) != 1:
            sys.exit('luiuse.py: %d sized FUNC copies of %s in %s' % (len(set(c)), a.func, tag))
        v, z = c[0]
        words, succ, pred, tabs = regdef.cfg(s3, img, v, z, a.func, tables, 'luiuse.py')
        w = words[off]
        op, rd, f3, rs1 = w & 0x7f, (w >> 7) & 31, (w >> 12) & 7, (w >> 15) & 31
        if op == 0x37:
            lui, val = off, regdef.sx(w & 0xfffff000, 32) & M64
        elif op in (0x13, 0x1b) and f3 == 0:
            up = regdef.reaching(words, pred, off, rs1)
            if len(up) != 1 or words[up[0]] & 0x7f != 0x37 or (words[up[0]] >> 7) & 31 != rs1:
                sys.exit('luiuse.py: %s+%#x is not the end of a lui pair in %s' % (a.func, off, tag))
            lui = up[0]
            val = regdef.sx(words[lui] & 0xfffff000, 32) + regdef.sx(w >> 20, 12)
            val = (regdef.sx(val & 0xffffffff, 32) if op == 0x1b else val) & M64
        else:
            sys.exit('luiuse.py: %s+%#x is neither a lui nor a lui pair in %s' % (a.func, off, tag))
        vals.append((tag, val))
        res, facts = chain(words, succ, lui, off, rd, False)
        bad = [r for r in res if r[3]]
        kinds = sorted({r[2].split(' (')[0].split(' sp')[0] for r in res})
        first = ('settled: not an address (the value %#x is read only as: %s; no memory base, call argument, return '
                 'value or store other than a followed stack spill)' % (val, ', '.join(kinds))) if not bad else \
            'not settled at the first level'
        cut = None
        if base is not None:
            indep = [term_name(words, pred, base, x) for x in sorted(reads(words[base]))]

            def cut(tr, words=words, pred=pred, rd=rd, val=val, indep=indep):
                e = evaluate(words, pred, rd, val, tr, final=False) if base in tr else None
                return e is not None and any(e.get(t) == 1 for t in indep) and e['V'] * val + e['L'] == 0
        tres, tfacts = chain(words, succ, lui, off, rd, True, cut)
        tbad = [r for r in tres if r[3]]
        classes = classify_uses(s3, img, v, words, pred, rd, val, tbad, callees, base, cut)
        n = {k: sum(1 for c in classes if c[1] == k) for k in (CALL_CLASS, BIAS_CLASS, ADDR_CLASS)}
        n['formed'] = sum(1 for c in classes if c[2].startswith('formed address'))
        n['derived'] = sum(1 for c in classes if c[2].startswith('derived value'))
        n['kinds'] = sorted({'the return value' if 'return value' in c[2].split(', derived from')[0] else
                             'a call argument the callee reads' if 'one of its arguments' in c[2] else
                             'a call argument of a callee not in the callee table' if 'not in the callee' in c[2] else
                             c[2][len('derived value: '):].split(', derived from')[0]
                             for c in classes if c[2].startswith('derived value')})
        tverdict = '%d flagged uses: %d %s, %d %s (%d formed addresses, %d derived values), %d %s' % (
            len(tbad), n[CALL_CLASS], CALL_CLASS, n[BIAS_CLASS], BIAS_CLASS, n['formed'], n['derived'], n[ADDR_CLASS],
            ADDR_CLASS)
        what = ('settled: not an image address (the value %#x: every other reached read is no address; at %d flagged '
                'calls the callee does not read the register it is live in; %d uses read it only as a numeric bias '
                'with net contribution 0: %d formed addresses, %d values derived from them)' % (
                    val, n[CALL_CLASS], n[BIAS_CLASS], n['formed'], n['derived'])) if not n[ADDR_CLASS] else \
            'not settled by this measurement'
        chain_words, bias = '-', '-'
        if base is not None:
            chain_words = ' | '.join('+%#x %s [%s]' % (s, ins(v, words, s), '; '.join(
                'x%d = %s%s' % (x, tree(v, words, pred, s, x, 1), '' if const_of(words, pred, s, x) is None else
                                ' (= %#x)' % (sum(const_of(words, pred, s, x)) & M64)) for x in sorted(reads(words[s]))))
                for s in listed)
            bias = ' | '.join([
                'the lui value %#x = %d' % (val, val),
                'base word +%#x %s: %s' % (base, ins(v, words, base), '; '.join(
                    'x%d = %s' % (x, tree(v, words, pred, base, x, 5)) for x in sorted(reads(words[base])))),
                'guard +%#x %s: %s' % (guard, ins(v, words, guard), '; '.join(
                    'x%d = %s' % (x, tree(v, words, pred, guard, x, 5)) for x in sorted(reads(words[guard]))))])
        rows.append([tag, regdef.sha(path), '+%#x %s' % (off, regdef.text(v + off, w)),
                     '+%#x %s' % (lui, regdef.text(v + lui, words[lui])), '%#x' % val, str(img.sec(val)),
                     uses(res), ' | '.join(facts) or '-', str(len(bad)), first, uses(tres), ' | '.join(tfacts) or '-',
                     str(len(tbad)), ' | '.join('+%#x %s (%s)' % c for c in classes) or '-', chain_words, bias,
                     tverdict, what, n])
    same = len({x for _, x in vals}) == 1
    print('# %s+%#x, a lui-built value; kit %s; tables %s; callee table %s; bias %s' % (
        a.func, off, hashlib.sha256(open(os.path.join(a.kit, 'SHA256SUMS'), 'rb').read()).hexdigest()[:12],
        ', '.join(a.table) or 'none', os.path.basename(a.callees) if a.callees else 'none', a.bias or 'none'))
    print('image\ttwin sha256\tinstruction\tlui\tvalue\tvalue section\tfirst-level reached uses (offset: how the value '
          'reaches it: kind)\tfirst-level slot facts\tfirst-level flagged uses\tfirst-level verdict\ttransitive reached '
          'uses (logical / shift results and frame spills followed too)\ttransitive slot facts\ttransitive flagged '
          'uses\ttransitive uses by class (call argument not read by the callee; not an image address: a numeric bias; '
          'address use)\tbias chain words\tbias facts\ttransitive verdict\twhat the instruction does\treason')
    for r in rows:
        n = r.pop()
        claim = ("the claim is 'same code up to relocation', which fails only if a byte-equal word embeds an image "
                 "address of one image; the lui value is %s" % (
                     'the same integer %#x in %s' % (vals[0][1], ', '.join(t for t, _ in vals)) if same else
                     'NOT the same in every twin (%s)' % ', '.join('%s %#x' % x for x in vals)))
        if n[ADDR_CLASS]:
            reason = claim + '; %d flagged uses are of class address use: not settled' % n[ADDR_CLASS]
        elif n[BIAS_CLASS]:
            reason = claim + ('; every flagged use is either a call at which the register it is live in is past the '
                              "callee's arguments (%d; argument counts from the callee table) or a use of a value whose "
                              'share of the constant is 0 (%d): %d formed addresses, each formed from the independent '
                              'base of the base word with the lui value and the other lui-built constants summing to 0, '
                              'and %d uses of values derived from those addresses (%s)' % (
                                  n[CALL_CLASS], n[BIAS_CLASS], n['formed'], n['derived'], '; '.join(n['kinds'])))
        else:
            reason = claim + '; it reaches no memory base, return value or store other than a followed spill' + \
                ('; at the %d flagged calls the callee does not read the register it is live in (its argument count '
                 'from the callee table)' % n[CALL_CLASS] if n[CALL_CLASS] else '')
        print('\t'.join(r + [reason]))


if __name__ == '__main__':
    main()
