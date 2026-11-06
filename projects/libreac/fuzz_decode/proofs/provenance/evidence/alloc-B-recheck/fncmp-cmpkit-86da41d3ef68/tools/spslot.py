#!/usr/bin/env python3
"""spslot.py -- which stack slots of a function are PRIVATE: a store to an sp slot is a spill only if no pointer to the
slot leaves the function's own sp-relative accesses. Per function (objscan.Fn's control-flow graph), a forward data-flow
tracks the stack pointer's offset from its value at entry (`addi sp, sp, c`) and every register holding an sp-derived
POINTER (`mv r, sp`, `addi r, sp, c`, and their copies / addi steps; add / sh*add / any other ALU op with one gives a
pointer of unknown offset at or above its base). Such a pointer
  ESCAPES when it is in a0-a7 at a call, a tail call or an ecall, is stored as data, or is in a0 / a1 at a return;
  ACCESSES the stack when it is the base of a load / store / AMO (its offset + the immediate, the access width).
A slot (entry-relative offset, width) is NOT private when an escaping pointer's object may cover it (an escape at base b
covers every slot at or above b: the callee may read the whole object) or a pointer access overlaps it; with an sp
offset the data-flow cannot fix, every slot is not private. Whole-function and flow-insensitive for the escapes: a
stricter reading than `before the slot is overwritten`, never a looser one.
usage: spslot.py ELF FUNCTION-ADDRESS   (prints the escapes, the accesses and the private test API's view)"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import escape, objscan

MEMOP = re.compile(r'(-?(?:0x[0-9a-f]+|\d+))?\((\w+)\)\s*$')
ARGS = tuple('a%d' % i for i in range(8))       # a fixed order: the first escape found is the same in every run
CLOB = set(ARGS) | {'t%d' % i for i in range(7)} | {'ra'}
WIDTH = {'lb': 1, 'lbu': 1, 'sb': 1, 'lh': 2, 'lhu': 2, 'sh': 2, 'lw': 4, 'lwu': 4, 'sw': 4, 'flw': 4, 'fsw': 4,
         'ld': 8, 'sd': 8, 'fld': 8, 'fsd': 8}
UNK = 'unk'
_CACHE = {}


class Frame:
    def __init__(self, img, a, z):
        self.img, self.a = img, a
        f = objscan.Fn(img, a, z)
        self.ins = f.ins
        self.sp_at = {}                 # instruction index -> entry-relative sp offset (None: not fixed)
        self.escapes, self.accesses = [], []
        self.unfixed = False
        IN = {f.lead[0]: (0, {})}
        work = [f.lead[0]]
        it = 0
        while work and it < 20000:
            it += 1
            s = work.pop()
            sp, regs = IN[s][0], dict(IN[s][1])
            for k in range(s, f.end[s] + 1):
                o, mn, op, n = self.ins[k]
                self.sp_at[k] = sp if k not in self.sp_at or self.sp_at[k] == sp else None
                if self.sp_at[k] is None:
                    self.unfixed = True
                sp, regs = self.step(k, o, mn, op, sp, regs, f.kind[k])
            for t in f.succ[s]:
                if t not in IN:
                    IN[t] = (sp, regs); work.append(t); continue
                osp, oregs = IN[t]
                nsp = osp if osp == sp else None
                nregs = dict(oregs)
                ch = nsp != osp
                for r, v in regs.items():
                    u = (oregs.get(r) or frozenset()) | v
                    if u != oregs.get(r):
                        nregs[r] = u; ch = True
                if ch:
                    IN[t] = (nsp, nregs)
                    if t not in work:
                        work.append(t)
                if nsp is None:
                    self.unfixed = True

    def step(self, k, o, mn, op, sp, regs, kind):
        ops = [x.strip() for x in op.split(',')] if op else []
        rd = ops[0] if ops else None
        bm = mn.split('.')[0]
        get = lambda r: (frozenset({sp}) if sp is not None else frozenset({UNK})) if r == 'sp' else regs.get(r)
        where = '+%#x %s %s' % (o, mn, op)
        if mn == 'addi' and len(ops) == 3 and rd == 'sp' and ops[1] == 'sp':
            return (sp + int(ops[2], 0) if sp is not None else None), regs
        m = MEMOP.search(op) if op else None
        is_ld = bm in ('lb', 'lbu', 'lh', 'lhu', 'lw', 'lwu', 'ld', 'lr', 'flw', 'fld')
        is_st = bm in ('sb', 'sh', 'sw', 'sd', 'sc', 'fsw', 'fsd') or bm.startswith('amo')
        if is_ld or is_st:
            if m and m.group(2) != 'sp' and regs.get(m.group(2)):
                for b in regs[m.group(2)]:
                    self.accesses.append((shift(b, int(m.group(1) or '0', 0)), WIDTH.get(bm, 8), where))
            if is_st and ops and regs.get(ops[0]):
                for b in regs[ops[0]]:
                    self.escapes.append((b, 'stored as data: ' + where))
            if is_ld and rd:
                regs.pop(rd, None)
            if (bm == 'sc' or bm.startswith('amo')) and rd:
                regs.pop(rd, None)
            return sp, regs
        tail_ij = kind[0] == 'ijmp' and self.img.wtarget.get(self.a + o) in self.img.starts
        if kind[0] in ('call', 'tail') or mn == 'ecall' or tail_ij:
            for r in ARGS:
                for b in regs.get(r, ()):
                    self.escapes.append((b, '%s in %s: %s' % ('passed' if mn != 'ecall' else 'given to the kernel', r, where)))
            for r in CLOB:
                regs.pop(r, None)
            return sp, regs
        if kind[0] == 'ret':
            for r in ('a0', 'a1'):
                for b in regs.get(r, ()):
                    self.escapes.append((b, 'returned in %s: %s' % (r, where)))
            return sp, regs
        if not rd or rd in ('zero', 'sp') or mn.startswith('b') or mn in ('j',) or mn.startswith('fence'):
            return sp, regs
        srcs = [x for x in ops[1:] if get(x)]
        if not srcs:
            regs.pop(rd, None)
            return sp, regs
        if mn in ('mv',) and len(ops) == 2:
            regs[rd] = get(ops[1]); return sp, regs
        if mn == 'addi' and len(ops) == 3:
            c = int(ops[2], 0)
            regs[rd] = frozenset(shift(b, c) for b in get(ops[1])); return sp, regs
        # add / sh*add / sub / and / any other op with a pointer: a pointer of unknown offset at or above its base
        regs[rd] = frozenset(lower(b) for x in srcs for b in get(x))
        return sp, regs

    def private(self, k, imm, width=8):
        """(True, '') when the slot sp+imm at instruction index k is private; else (False, the reason)"""
        sp = self.sp_at.get(k)
        if sp is None or self.unfixed:
            return False, 'the stack pointer offset is not fixed in this function'
        off = sp + imm
        for b, why in self.escapes:
            base = b[1] if isinstance(b, tuple) else b
            if base == UNK or base <= off:
                return False, 'a pointer to the frame at entry-sp%s leaves the function (%s)' % (
                    '?' if base == UNK else '%+d' % base, why)
        for ab, w, why in self.accesses:
            if ab == UNK:
                hit = True
            elif isinstance(ab, tuple):
                hit = ab[1] < off + width              # an access at an unknown offset at or above its base
            else:
                hit = ab < off + width and off < ab + w
            if hit:
                return False, 'the slot is read or written through an sp-derived pointer (%s)' % why
        return True, ''


def frame(img, a, z):
    key = (id(img), a)
    if key not in _CACHE:
        _CACHE[key] = Frame(img, a, z)
    return _CACHE[key]


def shift(b, c):
    """an sp-derived pointer moved by c: a fixed offset moves; an unknown offset at or above its base keeps a base no
    higher than before"""
    if b == UNK:
        return UNK
    if isinstance(b, tuple):
        return ('>=', b[1] + min(c, 0))
    return b + c


def lower(b):
    """the pointer an ALU op other than mv / addi makes from b: an unknown offset at or above b's base"""
    return b if b == UNK or isinstance(b, tuple) else ('>=', b)


if __name__ == '__main__':
    I = escape.Image(sys.argv[1]); I._index()
    a = int(sys.argv[2], 0)
    z = [f for f in I.funcs if f[0] == a][0][1]
    fr = frame(I, a, z)
    print('unfixed sp:', fr.unfixed)
    for e in fr.escapes:
        print('ESCAPE', e)
    for x in fr.accesses:
        print('ACCESS', x)
