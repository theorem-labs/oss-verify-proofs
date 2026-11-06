"""Intra-procedural abstract interpretation of RISC-V functions: register/stack-slot provenance.

Atoms: ('in', r, k)   entry value of register r plus k   (r = 'sp' gives entry-sp-relative stack addresses)
       ('c', v)        constant (incl. auipc/global/code addresses)
       ('ret', a, k)   return value (a0) of the call whose jal is at address a, plus k
       ('U', why)      unknown (arithmetic, non-stack load, uninitialised stack slot, ...)
A value is a frozenset of atoms (capped).
"""
import re
from base import tgt

REGS = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
        's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
ALIAS = {'fp': 's0'}
CALLER_SAVED = ['ra', 't0', 't1', 't2', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7', 't3', 't4', 't5', 't6']
CAP = 32
M64 = (1 << 64) - 1


def V(*atoms):
    return frozenset(atoms)


def U(why):
    return V(('U', why))


def addk(val, k):
    k &= M64
    if k >> 63:
        k -= 1 << 64
    out = set()
    for a in val:
        if a[0] == 'in':
            out.add(('in', a[1], a[2] + k))
        elif a[0] == 'c':
            out.add(('c', (a[1] + k) & M64))
        elif a[0] == 'ret':
            out.add(('ret', a[1], a[2] + k))
        else:
            out.add(a)
    return frozenset(out)


def leaves(val):
    out = set()
    for a in val:
        if a[0] == 'A':
            out |= a[2]
        elif a[0] == 'LD':
            out.add(('LDm',))
        else:
            out.add(a)
    if len(out) > 24:
        return frozenset({('U', 'widen')})
    return frozenset(out)


def arith(mn, *vals):
    lv = set()
    for v in vals:
        lv |= leaves(v)
    if len(lv) > 24:
        lv = {('U', 'widen')}
    return V(('A', 'op', frozenset(lv)))


def join(x, y):
    if x is None:
        return y
    if y is None:
        return x
    z = x | y
    if len(z) > CAP:
        return widen(z)
    return z

def widen(z):
    """Summarise a too-large set: constants -> an unknown constant (non-stack); entry values of one register with
    many offsets -> ('inw', r) (that register plus an unknown offset)."""
    kinds = {a[0] for a in z}
    if kinds <= {'c', 'int'}:
        return V(('int', 'const-widen'))
    regs = {a[1] for a in z if a[0] in ('in', 'inw')}
    if kinds <= {'in', 'inw', 'c', 'int'} and len(regs) == 1:
        out = {('inw', regs.pop())}
        if kinds & {'c', 'int'}:
            out.add(('int', 'const-widen'))
        return frozenset(out)
    return U('widen')


def nonzero(I, sites, val):
    """True/False if every atom is known non-zero / zero; None otherwise.
    ASSUMPTION (healthy run): __asan_stack_malloc_N returns a fake frame, not 0."""
    res = set()
    for a in val:
        if a[0] == 'c':
            res.add(a[1] != 0)
        elif a[0] == 'ret' and a[2] == 0 and a[1] in sites and sites[a[1]][1] in getattr(I, 'stackmalloc', ()):
            res.add(True)
        else:
            return None
    return res.pop() if len(res) == 1 else None


def reg(op):
    op = op.strip()
    op = ALIAS.get(op, op)
    return op if op in REGS else None


def imm(s):
    return int(s, 0)


MEMRE = re.compile(r'(-?0x[0-9a-f]+|-?\d+)?\((\w+)\)$')
LOADS = {'ld': 8, 'lw': 4, 'lwu': 4, 'lh': 2, 'lhu': 2, 'lb': 1, 'lbu': 1, 'ldsp': 8, 'lwsp': 4}
STORES = {'sd': 8, 'sw': 4, 'sh': 2, 'sb': 1, 'sdsp': 8, 'swsp': 4}
BRANCH = {'beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu', 'beqz', 'bnez', 'blez', 'bgez', 'bltz', 'bgtz', 'bgt', 'ble', 'bgtu', 'bleu'}


class State:
    __slots__ = ('r', 'm')

    def __init__(self, r, m):
        self.r = r; self.m = m

    def copy(self):
        return State(dict(self.r), dict(self.m))

    def join(self, o):
        r = {k: join(self.r.get(k), o.r.get(k)) for k in set(self.r) | set(o.r)}
        m = {}
        for k in set(self.m) | set(o.m):
            a, b = self.m.get(k), o.m.get(k)
            m[k] = join(a if a is not None else U('uninit-slot'), b if b is not None else U('uninit-slot'))
        return State(r, m)

    def eq(self, o):
        return self.r == o.r and self.m == o.m


def entry_state():
    r = {x: V(('in', x, 0)) for x in REGS}
    r['zero'] = V(('c', 0))
    return State(r, {})


def stack_off(val):
    if len(val) == 1:
        a = next(iter(val))
        if a[0] == 'in' and a[1] == 'sp':
            return a[2]
    return None


def analyze(I, f):
    """Return dict with: sites (list of (addr, kind, target, state)), ret (a0 value at returns), notes."""
    body = I.body(f)
    if not body:
        return None
    lo, hi = f, I.nxt(f)
    at = {x.address: x for x in body}
    order = [x.address for x in body]
    nexta = {order[k]: (order[k + 1] if k + 1 < len(order) else None) for k in range(len(order))}
    IN = {f: entry_state()}
    work = [f]
    sites = {}
    rets = None
    notes = set()
    iters = 0
    while work:
        iters += 1
        if iters > 200000:
            notes.add('iter-cap'); break
        a = work.pop()
        x = at.get(a)
        if x is None:
            notes.add(f'fallout {a:#x}'); continue
        s = IN[a].copy()
        mn = x.mnemonic[2:] if x.mnemonic.startswith('c.') else x.mnemonic
        ops = [o.strip() for o in x.op_str.split(',')] if x.op_str else []
        succ = []
        nx = nexta[a]
        R = s.r

        def g(o):
            rr = reg(o)
            return R[rr] if rr else U('nonreg')

        def setr(o, v):
            rr = reg(o)
            if rr and rr != 'zero':
                R[rr] = v

        fall = True
        if mn == 'jal' and not (ops and ops[0] == 'zero'):
            t = tgt(x)
            sites[a] = ('call', t, s.copy(), x.size)
            if t in getattr(I, 'noreturn', ()):
                fall = False
            for c in CALLER_SAVED:
                R[c] = U('clobber')
            R['a0'] = V(('ret', a, 0))
            R['a1'] = V(('ret1', a, 0))
        elif mn == 'jalr' and not (ops and ops[0] == 'zero'):
            sites[a] = ('icall', None, s.copy(), x.size)
            for c in CALLER_SAVED:
                R[c] = U('clobber')
            R['a0'] = V(('ret', a, 0))
        elif mn in ('j',) or (mn == 'jal' and ops and ops[0] == 'zero'):
            t = tgt(x)
            fall = False
            if t is not None and lo <= t < hi:
                succ.append(t)
            else:
                sites[a] = ('tail', t, s.copy(), x.size)
        elif mn == 'ret' or (mn == 'jr' and ops == ['ra']):
            fall = False
            rets = join(rets, R['a0'])
        elif mn in ('jr',) or (mn == 'jalr' and ops and ops[0] == 'zero'):
            fall = False
            jt = jump_table(I, a, lo, hi)
            if jt:
                succ.extend(jt)
                notes.add(f'jump-table {a:#x} {len(jt)}')
            else:
                sites[a] = ('itail', None, s.copy(), x.size)
                notes.add(f'indirect-jump {a:#x}')
        elif mn in BRANCH:
            t = tgt_branch(x)
            taken, nottaken = True, True
            if mn in ('beqz', 'bnez') or (mn in ('beq', 'bne') and len(ops) == 3 and ops[1] == 'zero'):
                nz = nonzero(I, sites, g(ops[0]))
                if nz is not None:
                    iszero = not nz
                    taken = iszero if mn in ('beqz', 'beq') else not iszero
                    nottaken = not taken
                    notes.add(f'pruned {a:#x}')
            if t is not None and lo <= t < hi:
                if taken:
                    succ.append(t)
            elif t is not None:
                notes.add(f'branch-out {a:#x}')
            if not nottaken:
                fall = False
        elif mn in ('mv',):
            setr(ops[0], g(ops[1]))
        elif mn in ('li',):
            setr(ops[0], V(('c', imm(ops[1]) & M64)))
        elif mn == 'lui':
            v = imm(ops[1]) << 12
            if v & (1 << 31):
                v -= 1 << 32
            setr(ops[0], V(('c', v & M64)))
        elif mn == 'auipc':
            v = imm(ops[1]) << 12
            if v & (1 << 31):
                v -= 1 << 32
            setr(ops[0], V(('c', (a + v) & M64)))
        elif mn in ('addi', 'addiw', 'addi16sp', 'addi4spn') and len(ops) == 3:
            setr(ops[0], addk(g(ops[1]), imm(ops[2])) if mn != 'addiw' else arith('addiw', g(ops[1])))
        elif mn in ('addi16sp',) and len(ops) == 2:
            setr(ops[0], addk(g(ops[0]), imm(ops[1])))
        elif mn == 'addi' and len(ops) == 2:
            setr(ops[0], addk(g(ops[0]), imm(ops[1])))
        elif mn == 'add':
            if len(ops) == 2:
                ops = [ops[0], ops[0], ops[1]]
            p, q = g(ops[1]), g(ops[2])
            if all(t[0] == 'c' for t in q) and len(q) == 1:
                setr(ops[0], addk(p, next(iter(q))[1]))
            elif all(t[0] == 'c' for t in p) and len(p) == 1:
                setr(ops[0], addk(q, next(iter(p))[1]))
            else:
                setr(ops[0], arith('add', p, q))
        elif mn == 'sub' and len(ops) == 3 and len(g(ops[2])) == 1 and next(iter(g(ops[2])))[0] == 'c':
            setr(ops[0], addk(g(ops[1]), -next(iter(g(ops[2])))[1]))
        elif mn in LOADS:
            m = MEMRE.match(ops[1])
            if m and reg(m.group(2)):
                off = int(m.group(1), 0) if m.group(1) else 0
                k = stack_off(R[reg(m.group(2))])
                if k is not None:
                    v = s.m.get(k + off)
                    if LOADS[mn] != 8:
                        v = V(('int', 'subword-load'))
                    elif v is None:
                        v = U(f'slot{k + off}')
                    setr(ops[0], v)
                elif LOADS[mn] != 8:
                    bv = R[reg(m.group(2))]
                    if off == 0 and len(bv) == 1 and next(iter(bv)) == ('LD', frozenset({('c', getattr(I, 'flag_got', -1))}), 0):
                        setr(ops[0], V(('c', 1)))   # __asan_option_detect_stack_use_after_return == 1
                    else:
                        setr(ops[0], V(('int', 'subword-load')))
                else:
                    bv = R[reg(m.group(2))]
                    if off == 0 and len(bv) == 1 and next(iter(bv))[0] == 'LD' and next(iter(bv))[2] == 0 and \
                            any(('c', gg) in next(iter(bv))[1] for gg in getattr(I, 'shadow_gots', ())):
                        setr(ops[0], V(('int', 'shadow-base')))   # __asan_shadow_memory_dynamic_address value
                    elif len(bv) == 1 and next(iter(bv))[0] == 'c':
                        setr(ops[0], V(('LD', frozenset({('c', (next(iter(bv))[1] + off) & M64)}), 0)))
                    else:
                        setr(ops[0], V(('LD', leaves(bv), off)))
            elif ops and reg(ops[0]):
                setr(ops[0], U('load?'))
        elif mn in STORES:
            m = MEMRE.match(ops[1])
            if m and reg(m.group(2)):
                off = int(m.group(1), 0) if m.group(1) else 0
                k = stack_off(R[reg(m.group(2))])
                if k is not None:
                    w = STORES[mn]
                    base_ = k + off
                    for kk in list(s.m):
                        if kk < base_ + w and kk + 8 > base_:
                            del s.m[kk]
                    s.m[base_] = g(ops[0]) if w == 8 else U('subword-store')
                else:
                    if any(t[0] == 'in' and t[1] == 'sp' for t in R[reg(m.group(2))]):
                        notes.add(f'ambiguous-stack-store {a:#x}')
        elif mn == 'andi' and reg(ops[0]) == 'sp' and stack_off(g(ops[1])) is not None and imm(ops[2]) < 0:
            # stack realignment; ASSUMPTION: offsets are taken modulo an entry sp aligned to the mask
            k = stack_off(g(ops[1]))
            setr(ops[0], V(('in', 'sp', k & imm(ops[2]))))
            notes.add(f'realign {a:#x} {ops[2]}')
        elif mn in ('ecall', 'ebreak', 'fence', 'nop', 'unimp', 'fence.i'):
            pass
        else:
            if ops and reg(ops[0]):
                if mn.endswith('w') and mn not in ('sw',) or mn in ('slt', 'sltu', 'slti', 'sltiu', 'seqz', 'snez', 'sltz', 'sgtz'):
                    setr(ops[0], V(('int', mn)))
                else:
                    srcs = [g(o) for o in ops[1:] if reg(o)]
                    setr(ops[0], arith(mn, *srcs))
        if fall and nx is not None:
            succ.append(nx)
        for t in succ:
            if t not in at:
                notes.add(f'succ-outside-body {t:#x}'); continue
            if t in IN:
                j = IN[t].join(s)
                if not j.eq(IN[t]):
                    IN[t] = j; work.append(t)
            else:
                IN[t] = s.copy(); work.append(t)
    return {'sites': sites, 'ret': rets, 'notes': notes, 'IN': IN}


def jump_table(I, a, lo, hi):
    """LLVM RISC-V jump table: auipc rT; addi rT,rT,imm; (slli; add; lw; add rX, rY, rT); jr rX.
    Entries are 32-bit offsets from the table base; count from a preceding 'addi rK,zero,N; bltu rK,idx' if present."""
    k = I.idx[a]
    win = I.ins[max(0, k - 12):k]
    T = None; n = None
    for j, x in enumerate(win):
        ops = [o.strip() for o in x.op_str.split(',')]
        if x.mnemonic == 'auipc' and j + 1 < len(win):
            y = win[j + 1]
            yo = [o.strip() for o in y.op_str.split(',')]
            if y.mnemonic == 'addi' and yo[0] == ops[0] and yo[1] == ops[0]:
                v = int(ops[1], 0) << 12
                if v & (1 << 31):
                    v -= 1 << 32
                T = x.address + v + int(yo[2], 0)
        if x.mnemonic in ('addi', 'c.li', 'li') and len(ops) >= 2 and (ops[1] == 'zero' or x.mnemonic != 'addi'):
            try:
                kk = int(ops[-1], 0)
            except ValueError:
                continue
            if j + 1 < len(win) and win[j + 1].mnemonic in ('bltu', 'bgeu'):
                n = kk + 1
    if T is None:
        return None
    out = []
    i = 0
    while i < (n or 4096):
        w = read32(I, T + 4 * i)
        if w is None:
            break
        if w & (1 << 31):
            w -= 1 << 32
        t = T + w
        if not (lo <= t < hi):
            if n is None:
                break
            return None
        out.append(t); i += 1
    return sorted(set(out)) or None


def read32(I, va):
    for seg in I.e.iter_segments():
        if seg['p_type'] == 'PT_LOAD' and seg['p_vaddr'] <= va < seg['p_vaddr'] + seg['p_filesz']:
            off = va - seg['p_vaddr']
            return int.from_bytes(seg.data()[off:off + 4], 'little')
    return None


def tgt_branch(x):
    last = x.op_str.split(',')[-1].strip()
    try:
        return x.address + int(last, 0)
    except ValueError:
        return None
