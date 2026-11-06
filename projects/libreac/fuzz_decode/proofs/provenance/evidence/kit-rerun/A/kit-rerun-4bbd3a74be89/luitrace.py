#!/usr/bin/env python3
"""luitrace.py -- hand-trace helper for the KIT LIMIT of AGENT TIME (BRANCH 6d8ff128a01):
strictcmp3 rule 8 / luiscan follow a lui value through addi / ld / sd / jalr only, so `memfed 0` is not proof.

For every lui in the named functions of each image, this does a MAY forward dataflow over the whole function
(fail-closed: both successors of every branch, every path, to a fixpoint) that follows the lui's destination
register through EVERY ALU op (add, sub, sh1add/sh2add/sh3add, slli, and/or/xor, mul, shifts, addiw, addw, subw,
mv, ...) and into every register the value is copied or added into, transitively, and reports:
  - every use of a tainted value as the BASE of a load / store / jalr,
  - every tainted value live in a0-a7 at a call (jal / jalr with rd=ra),
  - every other use (ALU operand, branch compare, store data, return value).
Where the whole dataflow is a known constant it also prints the effective address (base + imm) so it can be
resolved against the image's own .symtab.

usage: luitrace.py ELF NAME[,NAME...]      (TSV on stdout; one block per lui)
"""
import sys, os
from elftools.elf.elffile import ELFFile
from capstone import Cs, CS_ARCH_RISCV, CS_MODE_RISCV64, CS_MODE_RISCVC

X = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
     's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
F = (['ft%d' % i for i in range(12)] + ['fs%d' % i for i in range(12)] + ['fa%d' % i for i in range(8)] +
     ['f%d' % i for i in range(32)])
XF = set(X) | set(F)                         # a value can live in an FP register too (fmv.d.x / fmv.x.d)
ARGS = {'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7'}
LOADS = {'lb', 'lh', 'lw', 'ld', 'lbu', 'lhu', 'lwu', 'flw', 'fld', 'c.ld', 'c.lw', 'c.ldsp', 'c.lwsp',
         'c.fld', 'c.fldsp', 'c.flw'}
STORES = {'sb', 'sh', 'sw', 'sd', 'fsw', 'fsd', 'c.sd', 'c.sw', 'c.sdsp', 'c.swsp', 'c.fsd', 'c.fsdsp'}
# ops whose operand roles the trace knows: rd first, every other register operand a source.
RD_FIRST = {'add', 'addi', 'addiw', 'addw', 'sub', 'subw', 'mul', 'mulh', 'mulhu', 'mulhsu', 'mulw', 'div',
            'divu', 'divw', 'divuw', 'rem', 'remu', 'remw', 'remuw', 'and', 'andi', 'or', 'ori', 'xor', 'xori',
            'sll', 'slli', 'sllw', 'slliw', 'srl', 'srli', 'srlw', 'srliw', 'sra', 'srai', 'sraw', 'sraiw',
            'slt', 'slti', 'sltu', 'sltiu', 'mv', 'neg', 'negw', 'not', 'seqz', 'snez', 'sltz', 'sgtz',
            'sext.w', 'sext.b', 'sext.h', 'zext.w', 'zext.b', 'zext.h', 'sh1add', 'sh2add', 'sh3add',
            'sh1add.uw', 'sh2add.uw', 'sh3add.uw', 'add.uw', 'slli.uw', 'min', 'max', 'minu', 'maxu',
            'andn', 'orn', 'xnor', 'rol', 'ror', 'rori', 'rev8', 'orc.b', 'clz', 'ctz', 'cpop', 'li'}
M64 = (1 << 64) - 1


def sx(v, b=64):
    v &= (1 << b) - 1
    return v - (1 << b) if v >> (b - 1) else v


def load(path):
    f = open(path, 'rb')
    e = ELFFile(f)
    syms = {}
    for sec in e.iter_sections():
        if sec.header['sh_type'] not in ('SHT_SYMTAB', 'SHT_DYNSYM'):
            continue
        for s in sec.iter_symbols():
            t = s['st_info']['type']
            if t in ('STT_FUNC', 'STT_OBJECT') and s['st_size']:
                syms.setdefault(s.name, []).append((s['st_value'], s['st_size'], t))
    segs = [(seg['p_vaddr'], seg['p_filesz'], seg['p_offset'], seg['p_memsz']) for seg in e.iter_segments()
            if seg['p_type'] == 'PT_LOAD']
    secs = [(s.name, s['sh_addr'], s['sh_size'], s['sh_flags']) for s in e.iter_sections() if s['sh_addr']]
    allsyms = []
    for sec in e.iter_sections():
        if sec.header['sh_type'] in ('SHT_SYMTAB', 'SHT_DYNSYM'):
            for s in sec.iter_symbols():
                if s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT') and s.name:
                    allsyms.append((s['st_value'], s['st_size'], s.name))
    data = open(path, 'rb').read()
    return e, syms, segs, secs, allsyms, data


def frd(segs, data, a, n):
    for v, fsz, off, msz in segs:
        if v <= a and a + n <= v + fsz:
            return data[off + (a - v): off + (a - v) + n]
    return None


def where(secs, a):
    for nm, ad, sz, fl in secs:
        if ad <= a < ad + sz and (fl & 0x2):
            return nm
    return None


def resolve(allsyms, a):
    best = None
    for v, z, nm in allsyms:
        if z and v <= a < v + z:
            if best is None or z < best[1]:
                best = (v, z, nm)
    return '%s+0x%x' % (best[2], a - best[0]) if best else None


md = Cs(CS_ARCH_RISCV, CS_MODE_RISCV64 | CS_MODE_RISCVC)
md.detail = True


def regs_of(ins):
    """(written reg, [read regs], imm or None) by text parsing of capstone's op_str (stable for RV64 GC)."""
    ops = [o.strip() for o in ins.op_str.split(',')] if ins.op_str else []
    m = ins.mnemonic
    rd = rs = imm = None
    base = None
    flat = []
    for o in ops:
        if '(' in o:                                     # imm(reg)
            i, r = o.split('(')
            r = r.rstrip(')')
            try:
                imm = sx(int(i, 0), 32)
            except ValueError:
                imm = None
            base = r
            flat.append(r)
        elif o in XF:
            flat.append(o)
        else:
            try:
                imm = int(o, 0)
            except ValueError:
                pass
    return m, ops, flat, imm, base


FN = (0, 0)                                      # the function being traced, for the tail-call test


def rd_first(m):
    """True when the trace knows this op's operand roles: rd first, every other register operand a source.
    Anything else is REFUSED by step() (UNKNOWN-OP), never given a default rule."""
    b = m[2:] if m.startswith('c.') else m
    if b in RD_FIRST or b.split('.')[0] in RD_FIRST:
        return True
    return m.startswith('f') and m not in LOADS and m not in STORES   # FP ops (fmv.d.x, fmv.x.d, fcvt.*, ...)


def step(st, ins):
    """abstract transfer; st: reg -> (val|None, tainted). returns (newstate, uses)"""
    m, ops, flat, imm, base = regs_of(ins)
    uses = []
    def g(r):
        return (0, False) if r == 'zero' else st.get(r, (None, False))
    # uses first
    if m in LOADS or m in STORES or m.startswith('amo') or m.startswith('lr.') or m.startswith('sc.'):
        b = base or (flat[1] if len(flat) > 1 else None)
        if b and g(b)[1]:
            uses.append(('MEMBASE', m, b, g(b)[0], imm))
        if m in STORES and flat and g(flat[0])[1]:
            uses.append(('STOREDATA', m, flat[0], g(flat[0])[0], None))
    if m in ('jalr', 'c.jalr', 'c.jr', 'jr'):
        b = base or (flat[-1] if flat else None)
        if b and g(b)[1]:
            uses.append(('JUMPBASE', m, b, g(b)[0], imm))
    if m in ('jal', 'c.jal', 'jalr', 'c.jalr'):
        for r in sorted(ARGS):
            if g(r)[1]:
                uses.append(('CALLARG', m, r, g(r)[0], None))
    if m.startswith('b') and m not in ('bclr',):
        for r in flat:
            if g(r)[1]:
                uses.append(('BRANCH', m, r, g(r)[0], None))
    if m in ('j', 'jr', 'c.j', 'c.jr') and (m in ('jr', 'c.jr') or
                                            not (FN[0] <= ins.address + (imm or 0) < FN[1])):
        for r in sorted(ARGS):                       # a tail call: the arguments leave the function (lt2.py)
            if g(r)[1]:
                uses.append(('TAILARG', m, r, g(r)[0], None))
    if m in ('ret', 'c.ret'):
        for r in ('a0', 'a1'):                       # the value the function returns (lt2.py)
            if g(r)[1]:
                uses.append(('RETVAL', m, r, g(r)[0], None))
    st = dict(st)
    # a spill of a tainted value, and the reload that brings it back (lt2.py): a slot key 'M:<base>:<imm>'
    if m in STORES and flat and g(flat[0])[1]:
        st['M:%s:%s' % (base, imm)] = (None, True)
        if base not in ('sp', 's0'):
            st['M:ANY'] = (None, True)           # a tainted store through a pointer: any later load may reload it
    memload = False
    if m in LOADS:
        memload = st.get('M:%s:%s' % (base, imm), (None, False))[1] or st.get('M:ANY', (None, False))[1]
        if memload:
            uses.append(('RELOAD', m, base, None, imm))
    # writes
    def wr(r, val, taint):
        if r == 'zero':
            return
        for k in [k for k in st if k.startswith('M:%s:' % r)]:
            st.pop(k)                            # the slot's base register changed: forget the slot
        if taint:
            st[r] = (val, True)
        else:
            st.pop(r, None)
            if val is not None:
                st[r] = (val, False)
    if m in ('lui', 'c.lui'):                    # RV64: the lui result is sign-extended from bit 31
        wr(flat[0], sx((imm << 12) if abs(imm) < (1 << 20) else imm, 32) & M64, False)
    elif m == 'auipc':
        wr(flat[0], (ins.address + sx((imm << 12) if abs(imm) < (1 << 20) else imm, 32)) & M64, False)
    elif m in LOADS:
        wr(flat[0], None, memload)
    elif m in ('jal', 'c.jal'):
        for r in ['ra', 'a0', 'a1', 't0', 't1', 't2', 't3', 't4', 't5', 't6', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7']:
            st.pop(r, None)
    elif m in ('jalr', 'c.jalr'):
        for r in ['ra', 'a0', 'a1', 't0', 't1', 't2', 't3', 't4', 't5', 't6', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7']:
            st.pop(r, None)
    elif m in STORES or m.startswith('b') or m in ('c.j', 'j', 'jr', 'c.jr', 'ret', 'c.ret', 'ecall', 'ebreak',
                                                   'fence', 'fence.i', 'c.nop', 'nop', 'unimp'):
        pass
    elif m.startswith('amo') or m.startswith('sc.'):
        if flat:
            wr(flat[0], None, False)
    elif m.startswith('lr.'):
        wr(flat[0], None, False)
    elif flat and rd_first(m):
        rd = flat[0]
        src = flat[1:]
        taint = any(g(r)[1] for r in src)
        vals = [g(r)[0] for r in src]
        val = None
        if all(v is not None for v in vals):
            try:
                a = vals[0] if vals else None
                b = vals[1] if len(vals) > 1 else (imm if imm is not None else None)
                if m in ('addi', 'c.addi', 'c.addi4spn', 'c.addi16sp', 'mv', 'c.mv', 'c.add', 'add', 'addw',
                         'addiw', 'c.addiw', 'c.addw'):
                    val = (a + (b if b is not None else 0)) & M64
                    if m.endswith('w'):
                        val = sx(val, 32) & M64
                elif m in ('sub', 'subw', 'c.sub'):
                    val = (a - b) & M64
                elif m in ('slli', 'c.slli', 'slliw'):
                    val = (a << (imm or 0)) & M64
                elif m in ('srli', 'c.srli', 'srliw'):
                    val = (a >> (imm or 0)) & M64
                elif m in ('and', 'andi', 'c.andi', 'c.and'):
                    val = a & (b if b is not None else 0)
                elif m in ('or', 'ori', 'c.or'):
                    val = a | (b if b is not None else 0)
                elif m in ('xor', 'xori', 'c.xor'):
                    val = a ^ (b if b is not None else 0)
                elif m in ('sh1add', 'sh2add', 'sh3add'):
                    val = ((a << int(m[2])) + b) & M64
                elif m == 'mul':
                    val = (a * b) & M64
            except TypeError:
                val = None
        if src and any(g(r)[1] for r in src):
            uses.append(('ALU', m, ','.join(src), None, None))
        wr(rd, val, taint)
    elif flat:
        # the trace does not know this op's operand roles: REFUSE it, fail closed. Report it and taint every
        # register it names, so no path can lose the value through an op the script was never taught.
        if any(g(r)[1] for r in flat):
            uses.append(('UNKNOWN-OP', m, ','.join(flat), None, None))
            for r in flat:
                wr(r, None, True)
    return st, uses


def analyse(path, names, out):
    e, syms, segs, secs, allsyms, data = load(path)
    for nm in names:
        cands = syms.get(nm, [])
        cands = [c for c in cands if c[2] == 'STT_FUNC']
        if not cands:
            print('# %s: ABSENT in %s' % (nm, path), file=sys.stderr)
            continue
        for (a, z, _t) in sorted(set(cands)):
            b = frd(segs, data, a, z)
            ins = list(md.disasm(b, a))
            if sum(i.size for i in ins) != z:
                print('# %s@0x%x: decode gap (%d of %d bytes)' % (nm, a, sum(i.size for i in ins), z),
                      file=sys.stderr)
            idx = {i.address: k for k, i in enumerate(ins)}
            global FN
            FN = (a, a + z)
            succ = {}
            for k, i in enumerate(ins):
                s = []
                m = i.mnemonic
                # a `jalr` is a CALL: it returns, so it HAS a fall-through edge (the reviewer's jalr plant)
                if m not in ('j', 'c.j', 'ret', 'c.ret', 'jr', 'c.jr', 'unimp', 'c.unimp'):
                    if k + 1 < len(ins):
                        s.append(k + 1)
                if m.startswith('b') or m in ('j', 'c.j', 'jal', 'c.jal'):
                    tok = i.op_str.split(',')[-1].strip()
                    try:                     # capstone prints the target as an offset from this instruction
                        t = i.address + int(tok, 0)
                        if t in idx:
                            s.append(idx[t])
                    except ValueError:
                        pass
                succ[k] = s
            for k, i in enumerate(ins):
                if i.mnemonic not in ('lui', 'c.lui'):
                    continue
                m, ops, flat, imm, base = regs_of(i)
                v = sx((imm << 12) if abs(imm) < (1 << 20) else imm, 32) & M64
                seed = {flat[0]: (v, True)}
                states = {k + 1: seed} if k + 1 < len(ins) else {}
                uses = []
                work = [k + 1] if k + 1 < len(ins) else []
                seen_uses = set()
                while work:
                    p = work.pop()
                    st = states.get(p)
                    if st is None or p >= len(ins):
                        continue
                    ns, us = step(st, ins[p])
                    for u in us:
                        key = (ins[p].address, u[0], u[1], u[2], u[4])
                        if key not in seen_uses:
                            seen_uses.add(key)
                            uses.append((ins[p].address - a, '%s %s' % (ins[p].mnemonic, ins[p].op_str)) + u)
                    live = {r: t for r, t in ns.items() if t[1]}
                    if not live:
                        continue
                    for q in succ.get(p, []):
                        old = states.get(q)
                        merged = dict(ns)
                        if old is not None:
                            merged = {}
                            for r in set(old) | set(ns):
                                ov, ot = old.get(r, (None, False))
                                nv, nt = ns.get(r, (None, False))
                                merged[r] = (ov if ov == nv else None, ot or nt)
                            if merged == old:
                                continue
                        states[q] = merged
                        work.append(q)
                out.append(dict(image=path, fn=nm, faddr=a, off=i.address - a, reg=flat[0], val=v,
                                text='%s %s' % (i.mnemonic, i.op_str), uses=uses, secs=secs, allsyms=allsyms))
    return out


def report(rows, out=sys.stdout):
    for r in rows:
        kinds = sorted({u[2] for u in r['uses']})
        cls = 'b' if ({'MEMBASE', 'JUMPBASE', 'CALLARG'} & set(kinds)) else 'a'
        print('LUI\t%s\t0x%x\t+0x%x\t%s\t0x%x\t%s\t%s' % (r['fn'][:60], r['faddr'], r['off'], r['reg'], r['val'],
                                                          cls, ','.join(kinds) or 'none'), file=out)
        for u in r['uses']:
            off, text, kind, mn, reg, val, imm = u
            ea = None
            if kind in ('MEMBASE', 'JUMPBASE') and val is not None:
                ea = (val + (imm or 0)) & M64
            print('\tUSE\t+0x%x\t%s\t%s\treg=%s\tval=%s\tea=%s\tsec=%s\tsym=%s' % (
                off, text, kind, reg, ('0x%x' % val) if val is not None else '?',
                ('0x%x' % ea) if ea is not None else '-',
                where(r['secs'], ea) if ea is not None else '-',
                resolve(r['allsyms'], ea) if ea is not None else '-'), file=out)


def pair(px, py, names):
    """one row per lui, both images side by side, plus a word compare of every instruction of the trace."""
    rx, ry = analyse(px, names, []), analyse(py, names, [])
    _, _, segx, _, _, datax = load(px)
    _, _, segy, _, _, datay = load(py)
    keyx = {(r['fn'], r['off']): r for r in rx}
    keyy = {(r['fn'], r['off']): r for r in ry}
    print('# X %s' % px)
    print('# Y %s' % py)
    print('ROW\tfunction\t+off\treg\tvalX\tvalY\tvalues-equal\tclass\tuse-kinds\tuses\tchain-words\twords-equal\t'
          'words-differ (offset:mnemonic X/Y)')
    nb = na = 0
    bad = []
    for k in sorted(set(keyx) | set(keyy), key=lambda t: (t[0], t[1])):
        a, b = keyx.get(k), keyy.get(k)
        if a is None or b is None:
            bad.append('%s +0x%x only in %s' % (k[0], k[1], 'X' if b is None else 'Y'))
            continue
        kinds = sorted({u[2] for u in a['uses']} | {u[2] for u in b['uses']})
        cls = 'b' if ({'MEMBASE', 'JUMPBASE', 'CALLARG'} & set(kinds)) else 'a'
        na, nb = (na + 1, nb) if cls == 'a' else (na, nb + 1)
        chain = sorted({a['off']} | {u[0] for u in a['uses']} | {u[0] for u in b['uses']})
        eq = 0
        diff = []
        for off in chain:
            wx = frd(segx, datax, a['faddr'] + off, 4)
            wy = frd(segy, datay, b['faddr'] + off, 4)
            if wx == wy:
                eq += 1
            else:
                mx = next(md.disasm(wx, a['faddr'] + off), None)
                my = next(md.disasm(wy, b['faddr'] + off), None)
                diff.append('+0x%x:%s/%s' % (off, mx.mnemonic if mx else '?', my.mnemonic if my else '?'))
        print('ROW\t%s\t+0x%x\t%s\t0x%x\t0x%x\t%s\t%s\t%s\t%d\t%d\t%d\t%s' % (
            a['fn'], a['off'], a['reg'], a['val'], b['val'], 'yes' if a['val'] == b['val'] else 'NO', cls,
            ','.join(kinds) or 'none', len(a['uses']), len(chain), eq, ' '.join(diff) or '-'))
    print('TOTAL\tlui rows %d\tclass a %d\tclass b %d\tunmatched %s' % (na + nb, na, nb, bad or 'none'))
    print()
    print('# full trace, image X')
    report(rx)
    print()
    print('# full trace, image Y')
    report(ry)


def ops(paths, names):
    """every mnemonic of the named functions and how the trace handles it (the fail-closed rule is the default)."""
    import collections
    seen = collections.Counter()
    for p in paths:
        e, syms, segs, secs, allsyms, data = load(p)
        for nm in names:
            for (a, z, t) in sorted({c for c in syms.get(nm, []) if c[2] == 'STT_FUNC'}):
                for i in md.disasm(frd(segs, data, a, z), a):
                    seen[i.mnemonic] += 1
    print('# mnemonics of %d function(s) in %d image(s), and the trace\'s handling of each' % (len(names), len(paths)))
    print('OP\tmnemonic\tcount\thandling')
    for m, c in sorted(seen.items()):
        if m in ('lui', 'c.lui', 'auipc'):
            h = 'seed / known constant'
        elif m in LOADS:
            h = 'load: rd untainted unknown; a tainted base is reported MEMBASE'
        elif m in ('jal', 'c.jal', 'jalr', 'c.jalr'):
            h = 'call: tainted a0-a7 reported CALLARG, caller-saved cleared (ABI)'
        elif m in ('jr', 'c.jr'):
            h = 'indirect jump: a tainted base is reported JUMPBASE'
        elif m in STORES:
            h = 'store: tainted base MEMBASE, tainted data STOREDATA, no rd'
        elif m.startswith('b'):
            h = 'branch: tainted operand reported BRANCH, no rd'
        elif m.startswith('amo') or m.startswith('sc.') or m.startswith('lr.'):
            h = 'memory op: tainted address reported MEMBASE, rd untainted unknown'
        elif m in ('c.j', 'j', 'ret', 'c.ret', 'ecall', 'ebreak', 'fence', 'fence.i', 'c.nop', 'nop', 'unimp'):
            h = 'no rd'
        elif rd_first(m):
            h = 'FOLLOWED (known roles: rd first): rd tainted if any source register is tainted'
        else:
            h = 'REFUSED (UNKNOWN-OP): reported, and every register it names is tainted'
        print('OP\t%s\t%d\t%s' % (m, c, h))


CALLER = ['ra', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7', 't0', 't1', 't2', 't3', 't4', 't5', 't6']


def sta_run(ins, a):
    """the MAY-STATIC fixpoint over one function: returns (sites, stmap).
    sites: off -> (off, text, base register, may-be-static); stmap: off -> the state reaching that instruction.
    Models integer and FP registers, kept across every join, and memory slots keyed by (base register, imm):
    reviewer scripts static_base.py + static_mem.py (REVIEW_DIR/, AGENT TIME and TIME), logic copied.
    Does NOT model path conditions, or memory other than those slots."""
    MEM = LOADS | STORES
    idx = {i.address: k for k, i in enumerate(ins)}
    succ = {}
    for k, i in enumerate(ins):
        m, s = i.mnemonic, []
        if m not in ('j', 'ret', 'jr') and k + 1 < len(ins):
            s.append(k + 1)
        if m.startswith('b') or m == 'j':
            try:
                tt = i.address + int(i.op_str.split(',')[-1].strip(), 0)
                if tt in idx:
                    s.append(idx[tt])
            except ValueError:
                pass
        succ[k] = s
    st = {0: {r: (r == 'zero') for r in X}}
    work = [0]
    sites = {}
    while work:
        k = work.pop()
        sta = dict(st[k])
        i = ins[k]
        m, o_, flat, imm, base = regs_of(i)
        off = i.address - a
        if m in MEM or m.startswith(('amo', 'lr.', 'sc.')) or m in ('jalr', 'jr'):
            b = base or (flat[-1] if m in ('jalr', 'jr') else (flat[1] if len(flat) > 1 else None))
            sites[off] = (off, '%s %s' % (m, i.op_str), b,
                          sites.get(off, (0, 0, 0, False))[3] or sta.get(b, False))

        def w(r, s):
            if r == 'zero':
                return
            for kk in [kk for kk in sta if kk.startswith('M:%s:' % r)]:
                sta.pop(kk)
            sta[r] = s
        if m in ('lui', 'auipc'):
            w(flat[0], True)
        elif m in LOADS:                       # a reload of a may-static slot stays may-static
            w(flat[0], sta.get('M:%s:%s' % (base, imm), False))
        elif m.startswith(('amo', 'lr.', 'sc.')):
            w(flat[0], False)
        elif m in ('jal', 'jalr'):
            for r in CALLER:
                w(r, False)
        elif m in STORES:
            if flat and sta.get(flat[0], False):
                sta['M:%s:%s' % (base, imm)] = True
            else:
                sta.pop('M:%s:%s' % (base, imm), None)
        elif m.startswith('b') or m in ('j', 'jr', 'ret', 'ecall', 'fence', 'nop'):
            pass
        elif flat:
            w(flat[0], all(sta.get(r, False) for r in flat[1:]))
        for q in succ[k]:
            old = st.get(q)                    # the join unions the WHOLE state: FP registers and slots
            new = dict(sta) if old is None else {r: old.get(r, False) or sta.get(r, False)
                                                 for r in set(old) | set(sta)}
            if new != old:
                st[q] = new
                work.append(q)
    return sites, {ins[k].address - a: v for k, v in st.items()}



def deadarg(path, nm, reg, depth=0, memo=None):
    """settlement class (e) of AGENT TIME: is REG read before it is written, on any path through the callee,
    recursively through the callee's own direct calls? 'dead' = never read, so an argument register the caller left
    set is dead at the call; 'read' or 'unknown' (an indirect call, a callee without a symbol, or depth > 6) does
    not settle. Caller-saved registers are dropped after a direct call whose callee is itself 'dead'."""
    memo = {} if memo is None else memo
    key = (nm, reg)
    if key in memo:
        return memo[key]
    if depth > 6:
        return 'unknown'
    memo[key] = 'dead'                       # optimistic while recursing; refined below
    e, syms, segs, secs, allsyms, data = load(path)
    c = [x for x in syms.get(nm, []) if x[2] == 'STT_FUNC']
    if not c:
        memo[key] = 'unknown'
        return 'unknown'
    a, z, _ = sorted(set(c))[0]
    ins = list(md.disasm(frd(segs, data, a, z), a))
    idx = {i.address: k for k, i in enumerate(ins)}
    succ = {}
    for k, i in enumerate(ins):
        m, s = i.mnemonic, []
        if m not in ('j', 'ret', 'jr') and k + 1 < len(ins):
            s.append(k + 1)
        if m.startswith('b') or m == 'j':
            try:
                t = i.address + int(i.op_str.split(',')[-1].strip(), 0)
                if t in idx:
                    s.append(idx[t])
            except ValueError:
                pass
        succ[k] = s
    work, vis = [0], set()
    while work:
        k = work.pop()
        if k in vis or k >= len(ins):
            continue
        vis.add(k)
        i = ins[k]
        m, o_, flat, imm, base = regs_of(i)
        if m in ('lui', 'c.lui', 'auipc'):
            srcs = []
        elif m in LOADS:
            srcs = [base] if base else []
        elif m in STORES or m.startswith('b') or m in ('jr', 'c.jr', 'ret', 'c.ret'):
            srcs = list(flat)
        elif m in ('jalr', 'c.jalr'):
            srcs = [base or (flat[-1] if flat else None)]
        elif rd_first(m) and flat:
            srcs = flat[1:]
        else:
            srcs = list(flat)
        if reg in [s for s in srcs if s]:
            memo[key] = 'read'
            return 'read'
        if m in ('jal', 'c.jal'):
            try:
                t = i.address + int(i.op_str.split(',')[-1].strip(), 0)
                callee = resolve(allsyms, t)
            except ValueError:
                callee = None
            if not callee or not callee.endswith('+0x0'):
                memo[key] = 'unknown'
                return 'unknown'
            r = deadarg(path, callee.split('+0x')[0], reg, depth + 1, memo)
            if r != 'dead':
                memo[key] = r
                return r
            if reg in CALLER:
                continue
        if m in ('jalr', 'c.jalr', 'jr', 'c.jr'):
            memo[key] = 'unknown'
            return 'unknown'
        if m in ('ecall', 'ebreak'):                 # a syscall may read a0-a7: fail closed
            memo[key] = 'unknown'
            return 'unknown'
        if m in ('j', 'c.j'):                        # a tail jump out of the function: follow it, else fail closed
            try:
                t = i.address + int(i.op_str.split(',')[-1].strip(), 0)
            except ValueError:
                t = None
            if t is None or not (a <= t < a + z):
                cal = resolve(allsyms, t) if t is not None else None
                if not cal or not cal.endswith('+0x0'):
                    memo[key] = 'unknown'
                    return 'unknown'
                r = deadarg(path, cal.split('+0x')[0], reg, depth + 1, memo)   # a tail call: nothing is clobbered
                if r != 'dead':
                    memo[key] = r
                    return r
                continue
        if flat and flat[0] == reg and (m in ('lui', 'c.lui', 'auipc') or m in LOADS or rd_first(m)):
            continue
        for q in succ[k]:
            work.append(q)
    memo[key] = 'dead'
    return 'dead'


def deadargmode(paths, specs):
    print('# DEADARG: is the register read before it is written, on any path through the callee (recursively)?')
    print('# dead = never read: the argument is dead at the call (settlement class (e), AGENT TIME).')
    print('DEADARG\timage\tcallee\treg\tresult')
    for path in paths:
        for s in specs:
            nm, reg = s.rsplit(':', 1)
            print('DEADARG\t%s\t%s\t%s\t%s' % (os.path.basename(path), nm, reg, deadarg(path, nm, reg)))


# settlement classes of AGENT TIME, assigned per use. Citations are file:line in the pinned compiler-rt
# source of these binaries (llvm-project llvmorg-20.1.8; the local pin DEPOT_DIR/
# src-llvm-20.1.8/asan_allocator.cpp is byte-identical, sha256 30b715c3a518..., to the tag's file).
CALL_CLASS = {
    ('_ZN11__sanitizer17CombinedAllocator', 'a2'):
        ('(i) size parameter', 'sanitizer_allocator_combined.h:44 `void *Allocate(AllocatorCache *cache, uptr size,'
         ' uptr alignment)`; call site asan_allocator.cpp:583,587 `allocator.Allocate(cache, needed_size, 8)`'),
    ('_ZN6__asan26ReportAllocationSizeTooBig', 'a2'):
        ('(i) size parameter', 'asan_report.h:74-75 `ReportAllocationSizeTooBig(uptr user_size, uptr total_size,'
         ' uptr max_size, BufferedStackTrace*)`; call site asan_allocator.cpp:576 (a2 = malloc_limit)'),
    ('_ZN11__sanitizer11CheckFailed', 'a3'):
        ('(ii) CheckFailed v1', 'sanitizer_common.h:332-333 decl; body sanitizer_termination.cpp:67-72, which only'
         ' formats v1 / v2: `Printf("... (0x%zx, 0x%zx) ...", ..., (uptr)v1, (uptr)v2, tid)` (the ruling says'
         ' %llu; at this pin the conversion is (uptr) + %zx -- printed, never dereferenced, never stored)'),
    ('_ZN11__sanitizer11CheckFailed', 'a5'):
        ('(e) dead at call', 'sanitizer_common.h:332-333: CheckFailed takes 5 parameters (a0-a4), so a5 is beyond'
         ' its arity. out/luitrace-deadarg.out reports `unknown` for it, and ONLY because the walk is fail-closed'
         ' at a syscall: the one stop is the `ecall` at __sanitizer::GetTid+0x4, whose number is set two words'
         ' earlier by `addi a7, zero, 0xb2` = 178 = gettid, a syscall with no argument, so a5 is not read there.'
         ' That last step is by hand; everything before it is measured'),
    ('_ZN6__lsan20DisabledInThisThread', '*'):
        ('(e) dead at call', 'lsan_common.h:278 `bool DisabledInThisThread()`, no parameter; call site'
         ' asan_allocator.cpp:650; out/luitrace-deadarg.out: never read in the callee'),
    ('_ZN6__asanL10RZSize2Log', 'a1'):
        ('(e) dead at call', 'asan_allocator.cpp:46 `static u32 RZSize2Log(u32 rz_size)`, one parameter (a0);'
         ' call sites asan_allocator.cpp:466-468; out/luitrace-deadarg.out: a1 never read in the callee'),
    ('_ZN6__asan21GetCurrentThreadStats', 'a3'):
        ('(e) dead at call', 'asan_stats.h:55 `AsanStats &GetCurrentThreadStats()`, no parameter;'
         ' out/luitrace-deadarg.out: a3 never read in the callee'),
    ('_ZN6__asan21GetCurrentThreadStats', 'a0'):
        ('(e) dead at call', 'asan_stats.h:55 `AsanStats &GetCurrentThreadStats()`, no parameter; call site'
         ' asan_allocator.cpp:635; out/luitrace-deadarg.out: a0 never read in the callee'),
    ('_ZN11__sanitizer22AllocatorMayReturnNull', 'a0'):
        ('(e) dead at call', 'sanitizer_allocator.h:36 `bool AllocatorMayReturnNull()`, no parameter; call sites'
         ' asan_allocator.cpp:534,569,591; out/luitrace-deadarg.out: a0 never read in the callee'),
    ('_ZN6__asan15CanPoisonMemory', 'a0'):
        ('(e) dead at call', 'asan_poisoning.h:24 `bool CanPoisonMemory()`, no parameter; call site'
         ' asan_allocator.cpp:629; out/luitrace-deadarg.out: a0 never read in the callee'),
    ('_ZN11__sanitizer18LargeMmapAllocator', 'a5'):
        ('(e) dead at call', 'sanitizer_allocator_secondary.h:85 `Allocate(AllocatorStats*, const uptr size, uptr'
         ' alignment)` -> a5 is beyond its arity, and the exhaustive `readsites` walk (tail jumps followed,'
         ' ecall / jalr / jr fail-closed) gives four stops, three of them settled: `sd a5, 0x38(sp)` at'
         ' Report+0xc, the varargs save of'
         ' `Report(const char*, ...)` on the overflow error path. Its format string, "WARNING: %s:'
         ' LargeMmapAllocator allocation overflow: 0x%zx bytes with 0x%zx alignment requested\\n", has three'
         ' conversions (a1, a2, a3), so the saved slot is never read back (AGENT TIME (d): a spill is'
         ' not a use); the `ecall` at GetTid+0x4 with a7 = 178 = gettid, which takes no argument; and the `ecall`'
         ' at getrlimit+0x44 with a7 = 261 = prlimit64, which takes four (a0-a3). The fourth stop is the `jr a1`'
         ' at sysconf+0xf4: it is a 13-entry rel4 switch table (guard `bltu a2,a1`, a2 = 0xc), read entry by'
         ' entry by `luitrace.py swtab` -- the same symbol + offset in both images -- and no target reads a5; but'
         ' walking those targets reaches `jalr a3` at __interceptor_memset+0x9c, which is REAL(memset) again,'
         ' now settled with the +0x6dc row above (its escape is closed read-only in out/luitrace-frameesc.out)'),
    ('_ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddress'
     'SpaceViewEEEEEE6Refill', 'a5'):
        ('(e) dead at call', 'the callee of CombinedAllocator::Allocate +0x2ac is Refill (0x35f10 decode /'
         ' 0x36134 donor), not LocalCache::Allocate: `Refill(PerClass*, SizeClassAllocator*, uptr class_id)`'
         ' (sanitizer_allocator_local_cache.h:99-100) takes a0-a3, so a5 is beyond its arity, and'
         ' out/luitrace-openclose.out: deadarg(Refill, a5) = dead'),
}


def use_class(kind, reg, text, ms, callee, img=False, off=None, fn=''):
    """the settlement class of one non-base use."""
    if kind == 'STOREDATA' and ('(sp)' in text or '(s0)' in text):
        return '(d) frame spill', 'AGENT TIME (d): a spill to the frame is not a use'
    if off == 0x724 and kind == 'STOREDATA' and fn.startswith('_ZN6__asan9Allocator8Allocate'):
        return ('STORE: an integer-typed field',
                'kAllocBegMagic, loaded from the constant pool at +0x714 / +0x718 (asan_allocator.cpp:169-170 and'
                ' 184) and stored to the chunk: a CONSTANT, not an address of either layout, and strictcmp3'
                ' compares that very target byte for byte -- the `full+0x718[0x10328|0x10330]=8` acceptance of'
                ' out/strictcmp3-cmp-86da41d3ef68.out. Owner ruling AGENT TIME (2): this is the STORE class,'
                ' not a new class -- the destination field is `atomic_uintptr_t magic` of `class LargeChunkHeader`'
                ' (asan_allocator.cpp:168-171), an INTEGER-typed field, not a pointer, and the stored value is the'
                ' constant kAllocBegMagic (asan_allocator.cpp:169-170, stored at :184)')
    if not ms and not img:
        return ('(iii-v) no constant value under the model',
                'out/luitrace-maystatic.out: under that model no path gives this register a value built from'
                ' constants only. NARROWED after AGENT\'s third review: this says the value is not a constant'
                ' under the model, NOT that it is not an image address -- the image-address question is answered'
                ' separately by the IMG column (out/luitrace-uses.out), which is `no` for every one of these rows')
    if kind == 'BRANCH':
        return ('(c) compare-only use',
                'the use itself is a branch / compare operand: it neither passes nor stores the value; every'
                ' other use of the same value is its own row of this table')
    if kind == 'RETVAL':
        return ('(iii) runtime pointer returned',
                'out/luitrace-openclose.out `reachdefs`: no lui / auipc definition reaches either `ret`.'
                ' Allocator::Allocate +0x770 returns s4, whose reaching definitions are `mv s4,zero` (the null'
                ' return) and `add s4,s2,s4` / `and s4,s4,s8` (the allocator result s2 plus a redzone offset,'
                ' masked); CombinedAllocator::Allocate +0x220 returns `mv a0,zero`, `add a0,a4,a0`, or the result'
                ' of the call at +0xa4 / +0x2ac. A runtime pointer masked by a lui constant, or the constant 0 --'
                ' AGENT TIME: (iii) applied to the return value')
    if kind == 'CALLARG':
        if callee in ('-', None) or callee.startswith('0x'):
            return ('(e) dead at call',
                    'the `jalr a3` of Allocator::Allocate +0x6dc is REAL(memset) (asan_allocator.cpp:647): a3 is'
                    ' loaded at +0x6d0 out of __interception::real_memset (.data; decode A 0x9abc0 word'
                    ' 0x0000000000092474 = memset+0x0, donor 0xa0098 word 0x000000000009790c = memset+0x0), which'
                    ' `ptrscan` (base+imm) finds written 0 times in .text of either image. The escape of the'
                    ' cell\'s ADDRESS is closed by `luitrace.py frameesc` (out/luitrace-frameesc.out): in'
                    ' __asan_register_globals the frame slot s0-0x10d0 it is spilled to has exactly TWO accesses,'
                    ' the store `sd a1,-0xd0(a2)` at +0x3ec and the load `ld a4,-0xd0(a4)` at +0x868 followed by'
                    ' `ld a4,0(a4)` at +0x86c, a READ of real_memset through it; and every frame pointer the'
                    ' function hands to a callee or stores is s0-0x1000 or above, i.e. above the slot. So the'
                    ' callee set is {memset} and deadarg(memset, a4/a5/a6) = dead (owner rule AGENT TIME)')
        for (pfx, r), v in CALL_CLASS.items():
            if callee.startswith(pfx) and (r == '*' or r == reg):
                return v
    return 'OPEN', 'no class of AGENT TIME applies'



def reachdefs(path, nm, site, reg):
    """every definition of REG that reaches the instruction at offset SITE (MAY, over the whole CFG)."""
    e, syms, segs, secs, allsyms, data = load(path)
    a, z, _ = sorted({c for c in syms[nm] if c[2] == 'STT_FUNC'})[0]
    ins = list(md.disasm(frd(segs, data, a, z), a))
    idx = {i.address: k for k, i in enumerate(ins)}
    succ = {}
    for k, i in enumerate(ins):
        m, s = i.mnemonic, []
        if m not in ('j', 'ret', 'jr') and k + 1 < len(ins):
            s.append(k + 1)
        if m.startswith('b') or m == 'j':
            try:
                t = i.address + int(i.op_str.split(',')[-1], 0)
                if t in idx:
                    s.append(idx[t])
            except ValueError:
                pass
        succ[k] = s
    st, work = {0: frozenset(['entry'])}, [0]
    while work:
        k = work.pop()
        cur, i = st[k], ins[k]
        m, o_, flat, imm, base = regs_of(i)
        new = cur
        if m in ('jal', 'c.jal', 'jalr', 'c.jalr') and reg in CALLER:
            new = frozenset(['the call at +0x%x' % (i.address - a)])
        elif flat and flat[0] == reg and (m in ('lui', 'c.lui', 'auipc') or m in LOADS or rd_first(m)):
            new = frozenset(['+0x%x %s %s' % (i.address - a, i.mnemonic, i.op_str)])
        for q in succ[k]:
            old = st.get(q)
            nn = new if old is None else (old | new)
            if nn != old:
                st[q] = nn
                work.append(q)
    return sorted(st.get(idx[a + site], frozenset()))


def readsites(path, nm, reg, depth=0, seen=None, out=None, start=0):
    """EVERY stop of a dead-argument walk, not just the first (the reviewer's REVIEW_DIR4/allstops.py, logic
    copied): a read of reg before a write, an `ecall` (with the a7 value set in the same block, when constant), an
    indirect `jalr` / `jr`, an unresolved call target, a depth cutoff. The gaps that were closed in deadarg are
    closed here too: a tail `j` out of the function is FOLLOWED into the target symbol, and ecall / jalr / jr are
    fail-closed stops. `start` begins the walk at an offset other than the entry (a switch-table target)."""
    seen = set() if seen is None else seen
    out = [] if out is None else out
    if depth > 6 or (nm, reg, start) in seen:
        return out
    seen.add((nm, reg, start))
    e, syms, segs, secs, allsyms, data = load(path)
    c = [x for x in syms.get(nm, []) if x[2] == 'STT_FUNC']
    if not c:
        out.append((nm, '-', 'NOSYM: no sized FUNC symbol'))
        return out
    a, z, _ = sorted(set(c))[0]
    ins = list(md.disasm(frd(segs, data, a, z), a))
    idx = {i.address: k for k, i in enumerate(ins)}
    if a + start not in idx:
        out.append((nm, '+0x%x' % start, 'NOSTART: not an instruction boundary'))
        return out
    work, vis = [(idx[a + start], None)], set()
    while work:
        k, a7 = work.pop()
        if k in vis or k >= len(ins):
            continue
        vis.add(k)
        i = ins[k]
        m, o_, flat, imm, base = regs_of(i)
        here = '+0x%x' % (i.address - a)
        if m == 'addi' and flat[:2] == ['a7', 'zero']:
            a7 = imm
        if m in ('lui', 'c.lui', 'auipc'):
            srcs = []
        elif m in LOADS:
            srcs = [base] if base else []
        elif m in STORES or m.startswith('b') or m in ('jr', 'c.jr', 'ret', 'c.ret'):
            srcs = list(flat)
        elif m in ('jalr', 'c.jalr'):
            srcs = [base or (flat[-1] if flat else None)]
        elif rd_first(m) and flat:
            srcs = flat[1:]
        else:
            srcs = list(flat)
        if reg in [x for x in srcs if x]:
            out.append((nm, here, 'READ %s %s' % (i.mnemonic, i.op_str)))
            continue
        if m in ('ecall', 'ebreak'):
            out.append((nm, here, 'ECALL a7=%s (fail-closed)' % (a7 if a7 is not None else '?')))
            continue
        if m in ('jalr', 'c.jalr', 'jr', 'c.jr'):
            out.append((nm, here, 'INDIRECT %s %s (fail-closed)' % (i.mnemonic, i.op_str)))
            continue
        if m in ('jal', 'c.jal'):
            try:
                t = i.address + int(i.op_str.split(',')[-1], 0)
                cal = resolve(allsyms, t)
            except ValueError:
                cal = None
            if cal and cal.endswith('+0x0'):
                readsites(path, cal.split('+0x')[0], reg, depth + 1, seen, out)
            else:
                out.append((nm, here, 'UNRESOLVED call to %s' % cal))
            if reg in CALLER:
                continue
        if m in ('j', 'c.j'):                        # a tail jump out of the function: follow it
            try:
                t = i.address + int(i.op_str.split(',')[-1], 0)
            except ValueError:
                t = None
            if t is not None and not (a <= t < a + z):
                cal = resolve(allsyms, t)
                if cal and cal.endswith('+0x0'):
                    readsites(path, cal.split('+0x')[0], reg, depth + 1, seen, out)
                else:
                    out.append((nm, here, 'TAIL-J to %s (unresolved)' % cal))
                continue
        if flat and flat[0] == reg and (m in ('lui', 'c.lui', 'auipc') or m in LOADS or rd_first(m)):
            continue
        nxt = []
        if m not in ('j', 'c.j', 'ret', 'c.ret', 'jr', 'c.jr') and k + 1 < len(ins):
            nxt.append(k + 1)
        if m.startswith('b') or m in ('j', 'c.j'):
            try:
                t = i.address + int(i.op_str.split(',')[-1], 0)
                if t in idx:
                    nxt.append(idx[t])
            except ValueError:
                pass
        for q in nxt:
            work.append((q, a7))
    return out


def swtab(path, nm, auipc_off, addi_off, count):
    """read a base-relative (rel4) switch table: base = auipc+addi, entry i = the 4-byte word at base + 4i, target
    = base + entry. Prints every entry as symbol + offset so the two images can be compared entry by entry."""
    e, syms, segs, secs, allsyms, data = load(path)
    a, z, _ = sorted({c for c in syms[nm] if c[2] == 'STT_FUNC'})[0]
    ins = {i.address - a: i for i in md.disasm(frd(segs, data, a, z), a)}
    au = ins[auipc_off]
    T = (au.address + sx(int(au.op_str.split(',')[-1], 0) << 12, 32) +
         int(ins[addi_off].op_str.split(',')[-1], 0)) & M64
    print('SWTAB\t%s\t%s\ttable 0x%x\tentries %d' % (os.path.basename(path), nm, T, count))
    for k in range(count):
        w = int.from_bytes(frd(segs, data, T + 4 * k, 4), 'little')
        w = w - (1 << 32) if w >> 31 else w
        t = (T + w) & M64
        print('SWTAB\t%s\tentry %d\t%+d\t0x%x\t%s' % (os.path.basename(path), k, w, t, resolve(allsyms, t)))


def ptrscan(path, symname):
    """every .text instruction that reads the VALUE of the data symbol, and every one that stores to it, found by
    following auipc-materialised addresses and pointers loaded from them, and comparing base + imm (not the base
    register alone: AGENT's fourth review). LIMITS, stated: a write through a pointer obtained in another way
    is not seen, and the address of the symbol can leave a tracked register (it is spilled to the stack at
    __asan_register_globals+0x3ec in both images), so the scan is evidence over the image's code, not a proof."""
    e, syms, segs, secs, allsyms, data = load(path)
    tgt = [v for v, z, n in allsyms if n == symname][0]
    init = int.from_bytes(frd(segs, data, tgt, 8), 'little')
    print('# %s: %s @0x%x, initial value 0x%x -> %s' % (os.path.basename(path), symname, tgt, init,
                                                        resolve(allsyms, init)))
    tx = [s for s in secs if s[0] == '.text'][0]
    regv = {}
    reads = writes = 0
    for i in md.disasm(frd(segs, data, tx[1], tx[2]), tx[1]):
        m, o_, flat, imm, base = regs_of(i)
        if m == 'auipc':
            regv[flat[0]] = (i.address + sx((imm << 12), 32)) & M64
        elif m == 'addi' and base is None and len(flat) > 1 and flat[1] in regv:
            regv[flat[0]] = (regv[flat[1]] + (imm or 0)) & M64
        elif m in LOADS and base in regv:
            adr = (regv[base] + (imm or 0)) & M64
            cont = frd(segs, data, adr, 8)
            val = int.from_bytes(cont, 'little') if cont else None
            if adr == tgt:
                reads += 1
                print('READ\t0x%x\t%s' % (i.address, resolve(allsyms, i.address)))
                regv.pop(flat[0], None)
            elif val == tgt:
                regv[flat[0]] = tgt
            else:
                regv.pop(flat[0], None)
        elif m in STORES:
            if base in regv and isinstance(regv[base], int) and (regv[base] + (imm or 0)) & M64 == tgt:
                writes += 1
                print('WRITE\t0x%x\t%s\t%s %s' % (i.address, resolve(allsyms, i.address), m, i.op_str))
        elif flat:
            regv.pop(flat[0], None)
    print('TOTAL\t%s\t%s\treads %d\twrites %d' % (os.path.basename(path), symname, reads, writes))



def imgaddr_run(ins, a):
    """MAY image-address analysis, the reviewer's REVIEW_DIR3/imgaddr.py (AGENT's third review), logic
    copied: a register is IMG when it may hold a value derived, through ANY op and through (base, imm) slots,
    from an auipc result or from a load whose base is auipc-derived (a GOT-style load, whose loaded value is the
    address of a global). Other loads, call results and entry arguments are not IMG. Returns off -> state."""
    idx = {i.address: k for k, i in enumerate(ins)}
    succ = {}
    for k, i in enumerate(ins):
        m, s = i.mnemonic, []
        if m not in ('j', 'ret', 'jr') and k + 1 < len(ins):
            s.append(k + 1)
        if m.startswith('b') or m == 'j':
            try:
                t = i.address + int(i.op_str.split(',')[-1].strip(), 0)
                if t in idx:
                    s.append(idx[t])
            except ValueError:
                pass
        succ[k] = s
    st, work = {0: {}}, [0]
    while work:
        k = work.pop()
        sta = dict(st[k])
        i = ins[k]
        m, o_, flat, imm, base = regs_of(i)
        rawauipc = sta.get('AUIPC:' + str(base), False) if base else False

        def w(r, s, au=False):
            if r == 'zero':
                return
            for kk in [kk for kk in sta if kk.startswith('M:%s:' % r)]:
                sta.pop(kk)
            sta[r] = s
            sta['AUIPC:' + r] = au
        if m == 'auipc':
            w(flat[0], True, True)
        elif m in ('lui', 'c.lui'):
            w(flat[0], False)
        elif m in LOADS:
            w(flat[0], rawauipc or sta.get('M:%s:%s' % (base, imm), False))
        elif m.startswith(('amo', 'lr.', 'sc.')):
            w(flat[0], False)
        elif m in ('jal', 'c.jal', 'jalr', 'c.jalr'):
            for r in CALLER:
                w(r, False)
        elif m in STORES:
            if flat and sta.get(flat[0], False):
                sta['M:%s:%s' % (base, imm)] = True
        elif m.startswith('b') or m in ('j', 'jr', 'ret', 'ecall', 'fence', 'nop'):
            pass
        elif flat:
            srcs = flat[1:]
            au = m in ('addi', 'mv') and srcs and all(sta.get('AUIPC:' + r, False) for r in srcs)
            w(flat[0], any(sta.get(r, False) for r in srcs), au)
        for q in succ[k]:
            old = st.get(q)
            new = dict(sta) if old is None else {r: old.get(r, False) or sta.get(r, False)
                                                 for r in set(old) | set(sta)}
            if new != old:
                st[q] = new
                work.append(q)
    return {ins[k].address - a: v for k, v in st.items()}



def frameesc(path, nm, slot):
    """MAY CFG analysis of one function's FRAME pointers: a register holds a SET of possible s0-deltas, UNIONED at
    every join (the reviewer's REVIEW_DIR6/frameesc_may2.py, AGENT's final review; logic copied). The
    earlier version kept a delta only when both paths agreed, which dropped pointers at joins and missed the
    `lui aX,1; addiw aX,aX,K; sub aX,s0,aX` idiom; `addiw` is handled here. A set of more than 64 deltas becomes
    ANY (fail-closed), and a frame pointer plus an unknown is ANY. Deltas are carried through (base, imm) stack
    slots. Reports every store and load that MAY hit `slot`, every frame pointer that MAY be a call argument or
    be stored to memory, and every access through an ANY frame pointer."""
    e, syms, segs, secs, allsyms, data = load(path)
    a, z, _ = sorted({c for c in syms[nm] if c[2] == 'STT_FUNC'})[0]
    ins = list(md.disasm(frd(segs, data, a, z), a))
    idx = {i.address: k for k, i in enumerate(ins)}
    succ = {}
    for k, i in enumerate(ins):
        m, s2 = i.mnemonic, []
        if m not in ('j', 'ret', 'jr') and k + 1 < len(ins):
            s2.append(k + 1)
        if m.startswith('b') or m == 'j':
            try:
                t = i.address + int(i.op_str.split(',')[-1], 0)
                if t in idx:
                    s2.append(idx[t])
            except ValueError:
                pass
        succ[k] = s2
    ANY = 'ANY'

    def join(x, y):
        if x is None or y is None:
            return x or y
        if x[0] != y[0]:
            return ('S', ANY) if 'S' in (x[0], y[0]) else None
        if x[1] == ANY or y[1] == ANY:
            return (x[0], ANY)
        u = x[1] | y[1]
        return (x[0], ANY if len(u) > 64 else u)

    st, work = {0: {'sp': ('S', frozenset([0]))}}, [0]
    slotw, slotr, callp, anyuse, ptrstore = set(), set(), {}, set(), set()
    s0d = [None]
    while work:
        k = work.pop()
        sta = dict(st[k])
        i = ins[k]
        m, o_, flat, imm, base = regs_of(i)
        off = i.address - a
        b = sta.get(base) if base else None
        if (m in LOADS or m in STORES) and b and b[0] == 'S':
            if b[1] == ANY:
                anyuse.add((off, '%s %s' % (m, i.op_str)))
            elif any(d + (imm or 0) == slot for d in b[1]):
                (slotw if m in STORES else slotr).add((off, '%s %s' % (m, i.op_str)))
        if m in STORES and flat and sta.get(flat[0], ('', 0))[0] == 'S':
            v = sta[flat[0]][1]
            ptrstore.add((off, '%s %s' % (m, i.op_str), 'ANY' if v == ANY else 's0%+d' % (min(v) - (s0d[0] or 0))))
        if m in ('jal', 'jalr'):
            for r in ARGS:
                v = sta.get(r)
                if v and v[0] == 'S':
                    t = None
                    try:
                        t = i.address + int(i.op_str.split(',')[-1], 0)
                    except ValueError:
                        pass
                    callp[(off, r)] = (v[1] if v[1] == ANY else min(v[1]), resolve(allsyms, t) if t else 'indirect')

        def w(r, v):
            if r == 'zero':
                return
            for kk in [kk for kk in sta if kk.startswith('M:%s:' % r)]:
                sta.pop(kk)
            if v is None:
                sta.pop(r, None)
            else:
                sta[r] = v
        if m == 'lui':
            w(flat[0], ('C', frozenset([sx(imm << 12, 32)])))
        elif m in ('addi', 'addiw', 'mv') and len(flat) > 1 and sta.get(flat[1]):
            v = sta[flat[1]]
            d = (imm or 0) if m in ('addi', 'addiw') else 0
            nv = (v[0], ANY if v[1] == ANY else frozenset(x + d for x in v[1]))
            if flat[0] == 's0' and nv[0] == 'S' and nv[1] != ANY and s0d[0] is None:
                s0d[0] = min(nv[1])
            w(flat[0], nv)
        elif m in ('sub', 'add') and len(flat) > 2:
            x, y = sta.get(flat[1]), sta.get(flat[2])
            if x and y and x[0] == 'S' and y[0] == 'C' and x[1] != ANY and y[1] != ANY:
                w(flat[0], ('S', frozenset((p - q if m == 'sub' else p + q) for p in x[1] for q in y[1])))
            elif x and y and m == 'add' and y[0] == 'S' and x[0] == 'C' and x[1] != ANY and y[1] != ANY:
                w(flat[0], ('S', frozenset(p + q for p in x[1] for q in y[1])))
            elif (x and x[0] == 'S') or (y and y[0] == 'S'):
                w(flat[0], ('S', ANY))
            else:
                w(flat[0], None)
        elif m in LOADS:
            w(flat[0], sta.get('M:%s:%s' % (base, imm)))
        elif m in STORES:
            v = sta.get(flat[0]) if flat else None
            if v and v[0] == 'S':
                sta['M:%s:%s' % (base, imm)] = v
            else:
                sta.pop('M:%s:%s' % (base, imm), None)
        elif m in ('jal', 'jalr'):
            for r in CALLER:
                w(r, None)
        elif m.startswith('b') or m in ('j', 'jr', 'ret', 'ecall', 'fence', 'nop'):
            pass
        elif flat:
            w(flat[0], ('S', ANY) if any(sta.get(r, ('', 0))[0] == 'S' for r in flat[1:]) else None)
        for q in succ[k]:
            old = st.get(q)
            new = dict(sta) if old is None else {r: join(old.get(r), sta.get(r)) for r in set(old) | set(sta)}
            new = {r: v for r, v in new.items() if v is not None}
            if new != old:
                st[q] = new
                work.append(q)
    d0 = s0d[0] or 0
    print('FRAME\t%s\t%s\ts0 = frame origin %+d\tslot s0%+d' % (os.path.basename(path), nm, d0, slot - d0))
    for o, t in sorted(slotw):
        print('SLOT-STORE\t+0x%x\t%s' % (o, t))
    for o, t in sorted(slotr):
        print('SLOT-LOAD\t+0x%x\t%s' % (o, t))
    for o, t in sorted(anyuse):
        print('ANY-ACCESS\t+0x%x\t%s' % (o, t))
    for (o, r), (v, cal) in sorted(callp.items()):
        print('CALLARG\t+0x%x\t%s\t%s\t%s' % (o, r, 'ANY' if v == ANY else 's0%+d' % (v - d0), cal))
    for o, t, v in sorted(ptrstore):
        print('PTR-STORE\t+0x%x\t%s\t%s' % (o, t, v))
    lows = [v for (v, _c) in callp.values() if v != ANY]
    print('TOTAL\t%s\tslot stores %d\tslot loads %d\tANY accesses %d\tcall pointers %d (ANY %d)\t'
          'lowest s0%+d\tslot s0%+d\tslot below every pointer: %s' % (
              os.path.basename(path), len(slotw), len(slotr), len(anyuse), len(callp),
              sum(1 for (v, _c) in callp.values() if v == ANY), (min(lows) - d0) if lows else 0, slot - d0,
              'yes' if lows and (slot - d0) < (min(lows) - d0) else 'NO'))



def eaval(paths, names):
    """CONCRETE may-static values, for shapes (a) and (h) of the 86da registry: the CFG MAY fixpoint of
    sta_run(), carrying the VALUE a register may hold when it is built from constants only -- lui, auipc,
    addi / add / sub / and / or / xor / shifts of such values, (base, imm) slots, and a LOAD whose address is
    itself static, whose word is then read out of the image (a GOT-style load gives the pointer it holds). A
    register with two different static values on two paths is dropped, so a printed value is the one every path
    gives. For every load / store / AMO / jalr site whose base has such a value it prints the COMBINED target
    ea = value + the instruction's immediate, its section, its symbol + offset and, when the target is unnamed,
    its CONTENTS (AGENT's final review): a .got cell by the symbol + offset of the pointer it holds, another
    read-only word by that symbol if the word is an address, else by the word's value."""
    res = {}
    for path in paths:
        e, syms, segs, secs, allsyms, data = load(path)
        for nm in names:
            for (a, z, t) in sorted({c for c in syms.get(nm, []) if c[2] == 'STT_FUNC'}):
                ins = list(md.disasm(frd(segs, data, a, z), a))
                idx = {i.address: k for k, i in enumerate(ins)}
                succ = {}
                for k, i in enumerate(ins):
                    m, s2 = i.mnemonic, []
                    if m not in ('j', 'ret', 'jr') and k + 1 < len(ins):
                        s2.append(k + 1)
                    if m.startswith('b') or m == 'j':
                        try:
                            tt = i.address + int(i.op_str.split(',')[-1], 0)
                            if tt in idx:
                                s2.append(idx[tt])
                        except ValueError:
                            pass
                    succ[k] = s2
                st, work, sites = {0: {'zero': 0}}, [0], {}
                while work:
                    k = work.pop()
                    sta = dict(st[k])
                    i = ins[k]
                    m, o_, flat, imm, base = regs_of(i)
                    off = i.address - a
                    if (m in LOADS or m in STORES or m.startswith(('amo', 'lr.', 'sc.')) or m in ('jalr', 'jr')):
                        b = base or (flat[-1] if m in ('jalr', 'jr') else (flat[1] if len(flat) > 1 else None))
                        v = sta.get(b)
                        if v is not None:
                            ea = (v + (imm or 0)) & M64
                            sym = resolve(allsyms, ea)
                            content = '-'
                            if sym is None:
                                wbts = frd(segs, data, ea, 8)
                                if wbts is not None:
                                    wv = int.from_bytes(wbts, 'little')
                                    content = resolve(allsyms, wv) or ('word 0x%016x' % wv)
                            sites[off] = (off, '%s %s' % (i.mnemonic, i.op_str), b, v, imm or 0, ea,
                                          where(secs, ea), sym, content)

                    def w(r, v):
                        if r == 'zero':
                            return
                        for kk in [kk for kk in sta if kk.startswith('M:%s:' % r)]:
                            sta.pop(kk)
                        if v is None:
                            sta.pop(r, None)
                        else:
                            sta[r] = v & M64
                    if m in ('lui', 'c.lui'):
                        w(flat[0], sx((imm << 12), 32))
                    elif m == 'auipc':
                        w(flat[0], i.address + sx((imm << 12), 32))
                    elif m in LOADS:
                        adr = sta.get(base)
                        val = None
                        if adr is not None and i.mnemonic in ('ld', 'lwu', 'lw'):
                            bts = frd(segs, data, (adr + (imm or 0)) & M64, 8 if i.mnemonic == 'ld' else 4)
                            if bts is not None:
                                val = int.from_bytes(bts, 'little')
                        if val is None:
                            val = sta.get('M:%s:%s' % (base, imm))
                        w(flat[0], val)
                    elif m.startswith(('amo', 'lr.', 'sc.')):
                        w(flat[0], None)
                    elif m in ('jal', 'c.jal', 'jalr', 'c.jalr'):
                        for r in CALLER:
                            w(r, None)
                    elif m in STORES:
                        v = sta.get(flat[0]) if flat else None
                        if v is not None:
                            sta['M:%s:%s' % (base, imm)] = v
                        else:
                            sta.pop('M:%s:%s' % (base, imm), None)
                    elif m.startswith('b') or m in ('j', 'jr', 'ret', 'ecall', 'fence', 'nop'):
                        pass
                    elif flat and rd_first(m):
                        vs = [sta.get(r) for r in flat[1:]]
                        v = None
                        if all(x is not None for x in vs):
                            x = vs[0] if vs else None
                            y = vs[1] if len(vs) > 1 else (imm if imm is not None else 0)
                            b2 = m[2:] if m.startswith('c.') else m
                            try:
                                if b2 in ('addi', 'addiw', 'add', 'addw', 'mv'):
                                    v = x + (y if len(vs) > 1 else (imm or 0))
                                elif b2 in ('sub', 'subw'):
                                    v = x - y
                                elif b2 in ('and', 'andi'):
                                    v = x & (y if len(vs) > 1 else (imm or 0))
                                elif b2 in ('or', 'ori'):
                                    v = x | (y if len(vs) > 1 else (imm or 0))
                                elif b2 in ('xor', 'xori'):
                                    v = x ^ (y if len(vs) > 1 else (imm or 0))
                                elif b2 in ('slli', 'slliw'):
                                    v = x << (imm or 0)
                                elif b2 in ('srli', 'srliw'):
                                    v = x >> (imm or 0)
                            except TypeError:
                                v = None
                        w(flat[0], v)
                    elif flat:
                        w(flat[0], None)
                    for q in succ[k]:
                        old = st.get(q)
                        new = dict(sta) if old is None else {r: v for r, v in sta.items() if old.get(r) == v}
                        if new != old:
                            st[q] = new
                            work.append(q)
                for s2 in sorted(sites.values()):
                    res.setdefault((nm, s2[0]), {})[os.path.basename(path)] = s2
                    print('EA\t%s\t%s\t+0x%x\t%s\tbase=%s=0x%x\timm=%+d\tea=0x%x\t%s\t%s\tcontents=%s' % (
                        os.path.basename(path), nm[:34], s2[0], s2[1], s2[2], s2[3], s2[4], s2[5], s2[6],
                        s2[7], s2[8]))
    nz = diff = alloc_nz = 0
    for (nm, off), per in sorted(res.items()):
        vals = list(per.values())
        if vals[0][4]:
            nz += 1
            if nm.startswith('_ZN6__asan9Allocator8Allocate'):
                alloc_nz += 1
        keys = {(v[6], v[7], v[8]) for v in vals}     # section, symbol+offset, and the contents of an unnamed target
        if len(per) == len(paths) and len(keys) > 1:
            diff += 1
            print('MISMATCH\t%s\t+0x%x\t%s' % (nm[:40], off, sorted(keys)))
    unnamed = sum(1 for _k, per in res.items() if list(per.values())[0][7] is None)
    print('TOTAL\tcombined targets %d\tnon-zero immediate %d\tof them in Allocator::Allocate %d\tunnamed '
          '(compared by contents) %d\tMISMATCHES (section, symbol+offset, contents) %d' % (
              len(res), nz, alloc_nz, unnamed, diff))


def usesmode(paths, names):
    """every lui-derived use that is NOT a load / store / jump base, with the may-static verdict for the value it
    carries and, for a call argument, the callee the call resolves to. The settlement classes of AGENT TIME
    are assigned in LUI-HANDTRACE.md section 7 on top of this output."""
    print('USE\timage\tfunction\t+off\tinsn\tkind\treg\tmay-static\timg-addr\tcallee\tclass\tcitation')
    tot = {}
    ncls = {}
    for path in paths:
        e, syms, segs, secs, allsyms, data = load(path)
        maps = {}
        seen = set()
        for r in analyse(path, names, []):
            nm = r['fn']
            if nm not in maps:
                (a, z, t) = sorted({c for c in syms.get(nm, []) if c[2] == 'STT_FUNC'})[0]
                ins = list(md.disasm(frd(segs, data, a, z), a))
                maps[nm] = (a, {i.address - a: i for i in ins}, sta_run(ins, a)[1], imgaddr_run(ins, a))
            a, byoff, stmap, imgmap = maps[nm]
            for off, text, kind, mn, reg, val, imm in r['uses']:
                if kind in ('MEMBASE', 'JUMPBASE', 'ALU', 'RELOAD'):
                    continue
                key = (nm, off, kind, reg)
                if key in seen:
                    continue
                seen.add(key)
                ms = stmap.get(off, {}).get(reg, False)
                callee = '-'
                if kind == 'CALLARG' and mn in ('jal', 'c.jal'):
                    try:
                        tt = byoff[off].address + int(byoff[off].op_str.split(',')[-1], 0)
                        callee = resolve(allsyms, tt) or hex(tt)
                    except ValueError:
                        pass
                img = imgmap.get(off, {}).get(reg, False)
                cls, cite = use_class(kind, reg, text, ms, callee, img, off, nm)
                tot[(kind, ms)] = tot.get((kind, ms), 0) + 1
                ncls[cls] = ncls.get(cls, 0) + 1
                print('USE\t%s\t%s\t+0x%x\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s' % (
                    os.path.basename(path), nm[:40], off, text, kind, reg, 'YES' if ms else 'no',
                    'IMG' if img else 'no', callee, cls, cite))
    for k in sorted(tot):
        print('TOTAL\t%s\tmay-static %s\t%d' % (k[0], 'YES' if k[1] else 'no', tot[k]))
    for c in sorted(ncls):
        print('TOTAL\tclass %s\t%d' % (c, ncls[c]))
    nopen = sum(v for c, v in ncls.items() if c.startswith('OPEN') or c.startswith('NOT CERTIFIED'))
    print('TOTAL\tnon-base uses %d\tmay-static %d\tsettled %d\topen %d' % (
        sum(tot.values()), sum(v for k, v in tot.items() if k[1]), sum(tot.values()) - nopen, nopen))


def maystatic(paths, names):
    """MAY-STATIC check: the reviewer's static_base.py plus static_mem.py (REVIEW_DIR/, AGENT's reviews of
    TIME and TIME), their logic copied here. Independent of the trace's value evaluator, it asks per load /
    store / AMO / jalr site whether the base register CAN, on some path from function entry, hold a value built
    from constants only (lui / auipc / zero / immediates, through ANY op), with no call return value, no entry
    argument and no sp / gp / tp in it. OR over paths, fixpoint, every CFG edge including the fall-through of jal
    and jalr.
    WHAT IT MODELS: integer AND floating-point registers, kept across every CFG join (the join unions the whole
    state, not a fixed register list); and memory slots keyed by (base register, immediate) -- a store of a
    may-static value makes the slot may-static, a load from the same key reads it back, and a write of the base
    register forgets its slots. So a value that is spilled and reloaded, or that passes through an FP register
    across a branch, stays may-static (the reviewer's `spill` and `fpjoin` plants).
    WHAT IT DOES NOT MODEL: path conditions (it is a MAY analysis: it over-reports static-possible, which is the
    safe direction here), and memory other than those slots -- a value stored through a pointer and read back by
    a load with a different (base, imm) key is not followed. A site called `runtime` is therefore runtime UNDER
    THIS MODEL, not under every possible dataflow."""
    MEM = LOADS | STORES
    nst_all = nsite_all = 0
    ms_sites, lui_sites = set(), set()
    for path in paths:
        e, syms, segs, secs, allsyms, data = load(path)
        nst = nsite = 0
        print('# image %s' % path)
        for nm in names:
            for (a, z, t) in sorted({c for c in syms.get(nm, []) if c[2] == 'STT_FUNC'}):
                ins = list(md.disasm(frd(segs, data, a, z), a))
                sites, stmap = sta_run(ins, a)
                for off, txt, b, s in sorted(sites.values()):
                    nsite += 1
                    if s:
                        nst += 1
                        print('MAY-STATIC\t%s\t+0x%x\t%s\tbase=%s' % (nm[:48], off, txt, b))
                        ms_sites.add((nm, off))
        print('TOTAL\t%s\tbase sites %d\tmay be static %d' % (os.path.basename(path), nsite, nst))
        nsite_all += nsite
        nst_all += nst
        for r in analyse(path, names, []):     # the sites a lui-derived value reaches, from the trace itself
            for u in r['uses']:
                if u[2] in ('MEMBASE', 'JUMPBASE'):
                    lui_sites.add((r['fn'], u[0]))
    print('TOTAL\tall\tbase sites %d\tmay be static %d' % (nsite_all, nst_all))
    print('TOTAL\tlui-reached base sites (both images) %d\tmay-static sites %d\tINTERSECTION %d\t%s' % (
        len(lui_sites), len(ms_sites), len(lui_sites & ms_sites),
        sorted('%s+0x%x' % (f[:24], o) for f, o in (lui_sites & ms_sites)) or 'empty'))


if __name__ == '__main__':
    if sys.argv[1] == 'pair':
        pair(sys.argv[2], sys.argv[3], sys.argv[4].split(','))
    elif sys.argv[1] == 'ops':
        ops(sys.argv[2:-1], sys.argv[-1].split(','))
    elif sys.argv[1] == 'reachdefs':
        for d in reachdefs(sys.argv[2], sys.argv[3], int(sys.argv[4], 0), sys.argv[5]):
            print('REACHDEF\t%s\t+0x%x\t%s\t%s' % (os.path.basename(sys.argv[2]), int(sys.argv[4], 0),
                                                      sys.argv[5], d))
    elif sys.argv[1] == 'eaval':
        eaval(sys.argv[2:-1], sys.argv[-1].split(','))
    elif sys.argv[1] == 'frameesc':
        for p in sys.argv[2:-2]:
            frameesc(p, sys.argv[-2], int(sys.argv[-1], 0))
    elif sys.argv[1] == 'swtab':
        swtab(sys.argv[2], sys.argv[3], int(sys.argv[4], 0), int(sys.argv[5], 0), int(sys.argv[6], 0))
    elif sys.argv[1] == 'readsites':
        for o in readsites(sys.argv[2], sys.argv[3], sys.argv[4],
                           start=int(sys.argv[5], 0) if len(sys.argv) > 5 else 0):
            print('READSITE\t%s\t%s\t%s\t%s' % (os.path.basename(sys.argv[2]), o[0], o[1], o[2]))
    elif sys.argv[1] == 'ptrscan':
        for p in sys.argv[2:-1]:
            ptrscan(p, sys.argv[-1])
    elif sys.argv[1] == 'deadarg':
        deadargmode(sys.argv[2:-1], sys.argv[-1].split(','))
    elif sys.argv[1] == 'uses':
        usesmode(sys.argv[2:-1], sys.argv[-1].split(','))
    elif sys.argv[1] == 'static':
        maystatic(sys.argv[2:-1], sys.argv[-1].split(','))
    else:
        elf, names = sys.argv[1], sys.argv[2].split(',')
        print('# image %s' % elf)
        report(analyse(elf, names, []))
