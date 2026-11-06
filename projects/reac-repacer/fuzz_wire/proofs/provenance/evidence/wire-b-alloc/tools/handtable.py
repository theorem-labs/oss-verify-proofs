#!/usr/bin/env python3
"""handtable.py -- the HAND SETTLEMENT of a jump table that jtcheck 226254f48c97 refuses (no proof), under this
record's rule for one (RECORD.md states it): (1) ENTRIES, (2) DISPATCH and (3) THE BOUND, each read on BOTH images;
part (4), a read of the settlement by a non-writer, is not this tool's. Read-only.
For each FN@+OFF (OFF: the lo12 `addi` that forms the table address), on X and on Y separately:
  DISPATCH  the straight-line block `bltu rK, rI` (or `bgeu rI, rK`) -> `slli rS, rI, 2` -> `add rB, rS, rT` ->
            `lw rE, 0(rB)` -> `add rJ, rE, rT` -> `jalr zero, 0(rJ)` (the auipc / addi pair of rT may sit inside it),
            each operand's reaching definition the word before it in the block, rT's the table's lo12 `addi`; the
            `slli` is the word right after the guard and reads the register rI the guard compared, so nothing runs
            between the compare and the scaling of that index; every word of the block after the guard has ONE
            predecessor, the word before it, so the guard's fall-through DOMINATES the indexed load and the jalr.
            `bltu` / `bgeu` compare unsigned, so a negative index is out of range.
  CFG       every word's successors: the next word (not after `jal zero`, a `jalr zero` or a taken-only jump), a branch
            target, an in-function `jal` target, and the dispatch's arms (the entries of part 1); a call (`jal` /
            `jalr` with rd != 0) returns to the next word, writes rd and every caller-saved register, and keeps sp and
            s0-s11 (the psABI's callee-saved rule: the same assumption jtcheck makes); an `ecall` writes every
            caller-saved register too; callee code is not read. The function is refused when it holds a 2-byte parcel,
            an opcode outside KNOWN, a branch that leaves the function or a `jal` that lands inside a word of it (a
            `jal` out of the function is a call, or with rd = zero a tail call that leaves it), a word no edge reaches
            other than the entry, an indirect jump other than the dispatch and `ret`, or a `ret` whose ra may come from
            anything but a load (a call's link would return into the function).
  BOUND     for the guard's limit register rK: EVERY definition that reaches the guard on EVERY path (a backward walk
            over the CFG above, to the function entry), each `addi rK, zero, c` with c >= 0; the count is the largest
            c + 1 (bltu) or c (bgeu). A definition of any other kind, or the entry value, refuses the settlement.
  BASE      every word that reads rT (integer, FP and AMO addressing included) while the lo12 `addi` reaches it: only
            the two `add`s of the block.
  ENTRIES   for every index below the count, the 4-byte slot at base + 4 * index, sign-extended and added to the base:
            the target, named as function + offset, which must be a word start of the function; the settled verdict
            is SETTLED-BY-HAND when every X and Y target is the same function + offset, the dispatch block is the
            same words at the same offsets in X and Y (but for the immediates of the auipc / addi that form the table
            address) and the limit definitions are the same; DIFFERS when a target differs; else NOT SETTLED with the
            reason (`the dispatch differs`, `the bound differs`, or the refusal of one image).
It loads jtcheck.py (226254f48c97, this record's copy) from its own directory for the images, the decoder and qres.
usage: handtable.py X_ELF Y_ELF FN@+0xOFF[,FN@+0xOFF...]"""
import os, runpy, sys

HERE = os.path.dirname(os.path.abspath(__file__))
_argv = sys.argv[:]
sys.argv = [os.path.join(HERE, 'jtcheck.py'), _argv[1], _argv[2], '']
jt = runpy.run_path(os.path.join(HERE, 'jtcheck.py'), run_name='jtcheck_lib')
sys.argv = _argv
dc, X, Y, sx = jt['dc'], jt['X'], jt['Y'], jt['sx']
RN = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
      's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
CALLER_SAVED = (1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31)
# opcodes whose rd is an integer register this walk must count as a definition (FP ops included: fmv.x / fcvt / fcmp /
# fclass write an integer rd; counting every FP rd too can only add definitions, never hide one)
WRITES_RD = (0x37, 0x17, 0x6f, 0x67, 0x13, 0x1b, 0x33, 0x3b, 0x03, 0x2f, 0x53, 0x43, 0x47, 0x4b, 0x4f, 0x57)
# every opcode this walk models; any other refuses the function
KNOWN = WRITES_RD + (0x07, 0x0f, 0x23, 0x27, 0x63, 0x73)


class Refused(Exception):
    pass


def f(x):
    return x & 0x7f, (x >> 7) & 31, (x >> 12) & 7, (x >> 15) & 31, (x >> 20) & 31


def btarget(o, x):
    return o + sx(((x >> 31) & 1) << 12 | ((x >> 7) & 1) << 11 | ((x >> 25) & 0x3f) << 5 | ((x >> 8) & 0xf) << 1, 13)


def jtarget(o, x):
    return o + sx(((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11 | ((x >> 21) & 0x3ff) << 1, 21)


def text(o, x):
    op, rd, f3, r1, r2 = f(x)
    if op == 0x13 and f3 == 0: return 'addi %s,%s,%d' % (RN[rd], RN[r1], sx(x >> 20, 12))
    if op == 0x13 and f3 == 1: return 'slli %s,%s,%d' % (RN[rd], RN[r1], (x >> 20) & 63)
    if op == 0x33 and f3 == 0 and x >> 25 == 0: return 'add %s,%s,%s' % (RN[rd], RN[r1], RN[r2])
    if op == 0x03 and f3 == 2: return 'lw %s,%d(%s)' % (RN[rd], sx(x >> 20, 12), RN[r1])
    if op == 0x03 and f3 == 3: return 'ld %s,%d(%s)' % (RN[rd], sx(x >> 20, 12), RN[r1])
    if op == 0x67: return 'jalr %s,%d(%s)' % (RN[rd], sx(x >> 20, 12), RN[r1])
    if op == 0x17: return 'auipc %s,%#x' % (RN[rd], (x >> 12) & 0xfffff)
    if op == 0x63 and f3 in (6, 7): return '%s %s,%s' % ('bltu' if f3 == 6 else 'bgeu', RN[r1], RN[r2])
    return '%08x' % x


class Func:
    def __init__(self, I, fn, off, tab):
        self.I, self.fn = I, fn
        a = jt['fsymq'](I, fn)
        if not a or a == 'ambiguous': raise Refused('no unique sized FUNC %s' % fn)
        self.a, self.z = a
        b = dc.frd(I, self.a, self.z)
        if b is None: raise Refused('the function bytes are not all file bytes')
        self.w = jt['bc_words'](b)
        if any(n != 4 for o, x, n in self.w): raise Refused('a 2-byte parcel')
        bad = [o for o, x, n in self.w if x & 0x7f not in KNOWN]
        if bad: raise Refused('an opcode this walk does not model at +%#x' % bad[0])
        self.at = {o: k for k, (o, x, n) in enumerate(self.w)}
        if off not in self.at: raise Refused('+%#x is not a word' % off)
        self.i = self.at[off]
        self.tab = tab

    def pc(self, k): return '+%#x' % self.w[k][0]
    def x(self, k): return self.w[k][1]

    def defines(self, k, r):
        op, rd, f3, r1, r2 = f(self.x(k))
        if op in (0x6f, 0x67) and rd: return r in CALLER_SAVED or r == rd       # a call: its link and every caller-saved
        if op == 0x73 and f3 == 0: return r in CALLER_SAVED                      # an ecall (or ebreak): as a call
        if op == 0x73 and f3: return rd == r and r != 0                          # a CSR read
        return op in WRITES_RD and rd == r and r != 0

    def cfg(self, arms_of_jalr, final=True):
        """successors of every word; arms_of_jalr: {jalr word: [arm words]}; final: every word but the entry must be
        reached by an edge (the walk with the dispatch's arms known)"""
        n = len(self.w); succ = []
        for k, (o, x, _) in enumerate(self.w):
            op, rd, f3, r1, r2 = f(x)
            s = []
            if op == 0x63:
                t = btarget(o, x)
                if t not in self.at: raise Refused('the branch at %s leaves the function' % self.pc(k))
                s = [k + 1, self.at[t]]
            elif op == 0x6f:
                t = jtarget(o, x)
                if rd == 0: s = [self.at[t]] if t in self.at else []
                else: s = [k + 1] + ([self.at[t]] if t in self.at else [])
                if 0 <= t < self.z and t not in self.at: raise Refused('the jal at %s lands inside a word' % self.pc(k))
            elif op == 0x67:
                if rd: s = [k + 1]
                elif k in arms_of_jalr: s = list(arms_of_jalr[k])
                elif r1 == 1 and sx(x >> 20, 12) == 0: s = []                  # ret
                else: raise Refused('an indirect jump other than the dispatch and ret at %s' % self.pc(k))
            else:
                s = [k + 1]
            if k + 1 in s and k + 1 >= n: s.remove(k + 1)
            succ.append(s)
        self.succ = succ
        self.pred = [set() for _ in range(n)]
        for k, s in enumerate(succ):
            for t in s: self.pred[t].add(k)
        cut = [k for k in range(1, n) if not self.pred[k]]
        if final and cut: raise Refused('no edge reaches %s' % self.pc(cut[0]))

    def is_call(self, k):
        op, rd, f3, r1, r2 = f(self.x(k))
        return (op in (0x6f, 0x67) and rd != 0) or (op == 0x73 and f3 == 0)

    def reaching(self, r, k, calls=None):
        """every word that writes r last on a path into word k, and 'entry' when a path from the function entry
        writes none. `calls`, a set, collects the calls the walk passes without stopping: where r is callee-saved,
        each is taken to keep it (defines(), the psABI rule)"""
        out = set(); seen = set(); work = list(self.pred[k])
        if k == 0: out.add('entry')
        while work:
            p = work.pop()
            if p in seen: continue
            seen.add(p)
            if self.defines(p, r): out.add(p); continue
            if calls is not None and self.is_call(p): calls.add(p)
            if p == 0: out.add('entry')
            work.extend(self.pred[p])
        return out


def dispatch(F):
    """the block of part (2): (guard, index reg, limit reg, plus, slli, add1, lw, add2, jalr, base reg)"""
    op, rT, f3, r1, r2 = f(F.x(F.i))
    if op != 0x13 or f3 != 0: raise Refused('%s is not an addi' % F.pc(F.i))
    for k in range(len(F.w)):
        o2, rd2, f32, a2, b2 = f(F.x(k))
        if not (o2 == 0x67 and rd2 == 0 and sx(F.x(k) >> 20, 12) == 0): continue
        # walk the block backwards from this jalr: add2 <- lw <- add1 <- slli <- guard, in address order with the
        # auipc / addi pair of rT allowed in between
        seq = []; j = k - 1
        while j >= 0 and len(seq) < 4:
            if j in (F.i, F.i - 1): j -= 1; continue
            seq.append(j); j -= 1
        if len(seq) < 4: continue
        add2, lw, add1, sl = seq
        g = sl - 1
        if g < 0: continue
        oa2, ra2, fa2, xa2, ya2 = f(F.x(add2)); olw, rlw, flw, blw, _ = f(F.x(lw))
        oa1, ra1, fa1, xa1, ya1 = f(F.x(add1)); osl, rsl, fsl, isl, _ = f(F.x(sl)); og, _, fg, g1, g2 = f(F.x(g))
        if not (oa2 == 0x33 and fa2 == 0 and F.x(add2) >> 25 == 0 and ra2 == a2 and rlw in (xa2, ya2) and rT in (xa2, ya2)): continue
        if not (olw == 0x03 and flw == 2 and sx(F.x(lw) >> 20, 12) == 0 and blw == ra1): continue
        if not (oa1 == 0x33 and fa1 == 0 and F.x(add1) >> 25 == 0 and rsl in (xa1, ya1) and rT in (xa1, ya1)): continue
        if not (osl == 0x13 and fsl == 1 and (F.x(sl) >> 20) & 63 == 2 and F.x(sl) >> 26 == 0): continue
        if og != 0x63 or fg not in (6, 7): continue
        ri = isl
        if fg == 6 and g2 == ri: rk, plus = g1, 1                                # bltu rK, rI: rI <=u K stays
        elif fg == 7 and g1 == ri: rk, plus = g2, 0                              # bgeu rI, rK: rI <u K stays
        else: continue
        if btarget(F.w[g][0], F.x(g)) == F.w[g + 1][0]: continue
        return g, ri, rk, plus, sl, add1, lw, add2, k, rT
    raise Refused('no dispatch block through the base formed at %s' % F.pc(F.i))


def settle(spec):
    fn, off = spec.rsplit('@', 1); off = int(off.lstrip('+'), 16)
    out = []; res = {}
    for tag, I in (('X', X), ('Y', Y)):
        try:
            F = Func(I, fn, off, None)
            g, ri, rk, plus, sl, add1, lw, add2, jr, rT = dispatch(F)
            st = dc._g['bc_states'](F.w)
            k = st[F.i].get(f(F.x(F.i))[3]) if st[F.i] else None
            if k is None or k < 0 or f(F.x(k))[0] != 0x17: raise Refused('no auipc binds the base at %s' % F.pc(F.i))
            base = jt['hi_lo'](F.a, F.w, k, F.x(F.i), 0x13)
            # the bound first needs the arms, the arms need the count: walk with the count each limit candidate gives,
            # then re-walk with the arms of the largest; the settlement holds only when the two walks agree
            F.cfg({jr: []}, final=False)       # the arms are not known yet: the dispatch has no edge
            cand = F.reaching(rk, g)
            counts = []
            for d in cand:
                if d == 'entry': raise Refused('the limit %s at the guard %s may be the entry value' % (RN[rk], F.pc(g)))
                o, rd, f3, r1, _ = f(F.x(d))
                c = sx(F.x(d) >> 20, 12)
                if not (o == 0x13 and f3 == 0 and r1 == 0 and c >= 0):
                    raise Refused('the limit %s at the guard %s may come from %s %08x' % (RN[rk], F.pc(g), F.pc(d), F.x(d)))
                counts.append((c + plus, d, c))
            n = max(c for c, d, _ in counts)
            ents = []
            for e in range(n):
                s = dc.frd(I, base + 4 * e, 4)
                if s is None: raise Refused('slot %d is not file bytes' % e)
                v = base + int.from_bytes(s, 'little', signed=True)
                if not (F.a <= v < F.a + F.z) or (v - F.a) not in F.at:
                    raise Refused('slot %d targets %#x, not a word of the function' % (e, v))
                ents.append((e, s.hex(), v - F.a))
            F.cfg({jr: sorted({F.at[t] for _, _, t in ents})})
            calls = set()
            cand2 = F.reaching(rk, g, calls)
            if cand2 != cand:
                raise Refused('the limit definitions change once the arms are edges: %s' % sorted(map(str, cand2)))
            # every reaching definition of each block operand is the word before it in the block; rT's the lo12 addi
            chk = [(sl, ri, None), (add1, f(F.x(sl))[1], {sl}), (add1, rT, {F.i}), (lw, f(F.x(add1))[1], {add1}),
                   (add2, f(F.x(lw))[1], {lw}), (add2, rT, {F.i}), (jr, f(F.x(add2))[1], {add2})]
            for at, r, want in chk:
                got = F.reaching(r, at)
                if want is not None and got != want:
                    raise Refused('%s at %s may come from %s' % (RN[r], F.pc(at), sorted(map(str, got))))
            blk = list(range(g + 1, jr + 1))
            for b in blk:
                if F.pred[b] != {b - 1}:
                    raise Refused('the block word %s has predecessors %s' % (F.pc(b), sorted(F.pc(p) for p in F.pred[b])))
            reads = [q for q in range(len(F.w)) if rT in (f(F.x(q))[3], f(F.x(q))[4]) and f(F.x(q))[0] in
                     (0x03, 0x07, 0x23, 0x27, 0x13, 0x1b, 0x33, 0x3b, 0x53, 0x57, 0x63, 0x67, 0x2f, 0x73) and F.i in F.reaching(rT, q)]
            if sorted(reads) != sorted({add1, add2}):
                raise Refused('the base %s is read at %s, not only by the two adds' % (RN[rT], [F.pc(q) for q in reads]))
            rets = [q for q, (o, x, _) in enumerate(F.w) if x & 0x7f == 0x67 and f(x)[1] == 0 and q != jr]
            for q in rets:
                for d in F.reaching(1, q):
                    if d == 'entry': continue
                    if not (f(F.x(d))[0] == 0x03 and f(F.x(d))[2] == 3):
                        raise Refused('ra at the ret %s may come from %s %08x' % (F.pc(q), F.pc(d), F.x(d)))
            res[tag] = dict(F=F, base=base, g=g, rk=rk, ri=ri, plus=plus, n=n, counts=counts, ents=ents, jr=jr,
                            blk=[g] + blk, auipc=k, rets=len(rets), reads=sorted(reads), calls=len(calls))
        except Refused as e:
            res[tag] = dict(refused=str(e))
    out.append('HAND\t%s\t+%#x' % (fn, off))
    for tag in ('X', 'Y'):
        r = res[tag]
        if 'refused' in r:
            out.append('%s\tREFUSED\t%s' % (tag, r['refused'])); continue
        F = r['F']
        out.append('%s\tTABLE\tbase %#x (%s auipc + %s addi), rel4 jump entries: slot + base' % (
            tag, r['base'], F.pc(r['auipc']), F.pc(F.i)))
        out.append('%s\tDISPATCH\t%s' % (tag, '; '.join('%s %s' % (F.pc(b), text(F.w[b][0], F.x(b))) for b in r['blk'])))
        out.append('%s\tDOMINANCE\tthe slli %s, the word right after the guard %s, reads the %s that the guard compared, '
                   'so nothing runs between the compare and the scaling of that index; every word %s..%s has one '
                   'predecessor, the word before it, so the guard\'s fall-through is the only way to the indexed load and '
                   'the jalr; %s is unsigned, so a negative index is out of range'
                   % (tag, F.pc(r['g'] + 1), F.pc(r['g']), RN[r['ri']], F.pc(r['g'] + 1), F.pc(r['jr']),
                      'bltu' if r['plus'] else 'bgeu'))
        out.append('%s\tBOUND\tthe limit %s at the guard %s: every reaching definition on every path of the CFG: %s -> '
                   'index < %d, %d entries; the walk passes %d call(s), each taken to keep %s, which the psABI makes '
                   'callee-saved (Func.defines: a call writes only its link and the caller-saved registers; callee code is '
                   'not read)' % (tag, RN[r['rk']], F.pc(r['g']), '; '.join(
                       '%s addi %s,zero,%d' % (F.pc(d), RN[r['rk']], c) for _, d, c in sorted(r['counts'], key=lambda t: t[1])),
                       r['n'], r['n'], r['calls'], RN[r['rk']]))
        out.append('%s\tCFG\tindirect jumps: the dispatch %s and %d ret, each ra from a load; the base %s is read only at %s'
                   % (tag, F.pc(r['jr']), r['rets'], RN[f(F.x(F.i))[1]], ', '.join(F.pc(q) for q in r['reads'])))
    ok = all('refused' not in res[t] for t in ('X', 'Y'))
    verdict = 'NOT SETTLED (%s)' % '; '.join('%s: %s' % (t, res[t]['refused']) for t in ('X', 'Y') if 'refused' in res[t])
    if ok:
        rx, ry = res['X'], res['Y']
        Fx, Fy = rx['F'], ry['F']
        # the same block at the same offsets, word for word equal in X and Y except the auipc / addi that form the
        # table address (its immediates are the table's place in each image), the same count and the same limits
        same_dispatch = ([Fx.w[b][0] for b in rx['blk']] == [Fy.w[b][0] for b in ry['blk']]
                         and all(Fx.x(b) == Fy.x(c) for b, c in zip(rx['blk'], ry['blk']) if b not in (rx['auipc'], Fx.i)))
        same_bound = rx['n'] == ry['n'] and \
            sorted((c, Fx.w[d][0]) for c, d, _ in rx['counts']) == sorted((c, Fy.w[d][0]) for c, d, _ in ry['counts'])
        diff = 0
        for (e, sxh, tx), (_, syh, ty) in zip(rx['ents'], ry['ents']):
            same = tx == ty
            diff += not same
            out.append('ENTRY\t%d\tX %s -> %s+%#x\tY %s -> %s+%#x\t%s' % (e, sxh, fn, tx, syh, fn, ty,
                                                                       'same' if same else 'DIFFERENT'))
        verdict = ('NOT SETTLED (the dispatch differs between X and Y)' if not same_dispatch else
                   'NOT SETTLED (the bound differs between X and Y)' if not same_bound else
                   'DIFFERS (%d entries)' % diff if diff else
                   'SETTLED-BY-HAND (parts 1-3 on both images; part 4, a non-writer read, is not this tool\'s)')
    out.append('VERDICT\t%s\t+%#x\t%s' % (fn, off, verdict))
    return out


def main():
    for spec in sys.argv[3].split(','):
        print('\n'.join(settle(spec)))


if __name__ == '__main__':
    main()
