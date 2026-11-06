#!/usr/bin/env python3
"""luicomb.py KIT_DIR FNLIST ELF [ELF ...] -- does any load / store / jalr / AMO base of a function carry TWO OR MORE
lui values at once? Read-only.

The KNOWN FAIL-OPEN of cmpkit 86da41d3ef68: strictcmp3 rule 8 carries ONE lui value to the word that uses it, so two
lui values combined by add / sub / sh*add into one address are not compared as an address. This tool finds that shape.

Per function and image it runs a MAY forward dataflow over the whole control-flow graph (both edges of every branch,
every `j` / `jal` edge inside the function, to a fixpoint), carrying for each register
  - the SET of lui words whose value reached it (a set, so two lui values meeting in one register are seen), and
  - its abstract value where every step is a known constant, else unknown,
through every ALU op (the union of its sources' sets), loads (the loaded value carries no lui), and calls (the
caller-saved registers are cleared). An instruction this tool does not know writes the union of its operands' sets,
so a path is never silently dropped.
At every load / store / jalr / AMO it reports its base register's set. Rows:
  SITE   <fn> +<off> <insn> base <reg> luis <n> [<lui offsets>] value <v or unknown> ea <effective address or ->
  TOTAL  per function and image: sites with 2 or more lui values in the base, and with exactly 1.
A site whose base value is known is an address this tool resolves in the image's own symbols (`ea`), so a caller can
compare the two images' targets. A site whose base is unknown holds a runtime pointer: no static address.
usage: luicomb.py KIT_DIR NAME[,NAME...] ELF [ELF ...]   (FNLIST as strictcmp3 cmp takes it)"""
import importlib.util, os, re, sys
import capstone

KIT, FNS = sys.argv[1], sys.argv[2].split(',')
sp = importlib.util.spec_from_file_location('strictcmp3_kit', os.path.join(KIT, 'strictcmp3.py'))
S = importlib.util.module_from_spec(sp); sp.loader.exec_module(S)
MD = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)
REGS = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
        's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
RSET = set(REGS)
CALLER = {'ra', 't0', 't1', 't2', 't3', 't4', 't5', 't6', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7'}
LOADS = ('lb', 'lh', 'lw', 'ld', 'lbu', 'lhu', 'lwu', 'flw', 'fld', 'c.ld', 'c.lw', 'c.ldsp', 'c.lwsp', 'c.fld')
STORES = ('sb', 'sh', 'sw', 'sd', 'fsw', 'fsd', 'c.sd', 'c.sw', 'c.sdsp', 'c.swsp', 'c.fsd')
MEMOP = re.compile(r'(-?(?:0x)?[0-9a-fA-F]+)?\((\w+)\)')
M64 = (1 << 64) - 1


def sx(v, b=64):
    v &= (1 << b) - 1
    return v - (1 << b) if v >> (b - 1) else v


def ops_of(ins):
    return [o.strip() for o in ins.op_str.split(',')] if ins.op_str else []


def base_of(ins):
    m = MEMOP.search(ins.op_str or '')
    if m:
        return m.group(2), int(m.group(1), 0) if m.group(1) else 0
    for o in ops_of(ins):                      # `jr a0`, `c.jr a0`
        if o in RSET:
            return o, 0
    return None, 0


def step(st, ins):
    """(new state, [(base register, immediate, kind)]) of one instruction"""
    mn, ops = ins.mnemonic, ops_of(ins)
    regs = [o for o in ops if o in RSET]
    uses = []
    if mn in LOADS or mn in STORES or mn.startswith('amo') or mn.startswith('lr.') or mn.startswith('sc.') \
            or mn in ('jalr', 'jr', 'c.jr', 'c.jalr'):
        b, imm = base_of(ins)
        if b:
            uses.append((b, imm, 'jump' if 'j' in mn else 'amo' if mn.startswith(('amo', 'lr.', 'sc.')) else
                         'load' if mn in LOADS else 'store'))
    new = dict(st)
    if mn in ('jal', 'c.jal') or (mn in ('jalr', 'c.jalr') and (not ops or ops[0] == 'ra')):
        for r in CALLER:
            new[r] = (frozenset(), None)
        return new, uses
    if mn in ('ret', 'c.ret') or mn in ('jr', 'c.jr') or mn in STORES or mn.startswith('b') or mn in ('j', 'c.j'):
        return new, uses                        # no destination register
    if not regs:
        return new, uses
    rd = regs[0]
    if rd == 'zero':
        return new, uses
    src = [new.get(r, (frozenset(), None)) for r in regs[1:]]
    tags = frozenset().union(*[s[0] for s in src]) if src else frozenset()
    val = None
    if mn in ('lui', 'c.lui'):
        imm = int(ops[1], 0)
        val = sx(imm << 12, 32)
        tags = frozenset([ins.address])
    elif mn in LOADS:
        tags, val = frozenset(), None           # the value comes from memory, not from a lui
    elif mn in ('li', 'c.li', 'auipc'):
        tags, val = frozenset(), (int(ops[1], 0) if mn != 'auipc' else None)
    elif mn in ('mv', 'c.mv', 'sext.w'):
        val = src[0][1] if src else None
    elif mn in ('addi', 'c.addi', 'addiw', 'c.addiw', 'addi16sp', 'c.addi16sp'):
        imm = int(ops[-1], 0) if ops and re.match(r'^-?(0x)?[0-9a-fA-F]+$', ops[-1]) else None
        if src and src[0][1] is not None and imm is not None:
            val = sx(src[0][1] + imm, 32 if 'w' in mn else 64)
    elif mn in ('add', 'c.add', 'addw', 'c.addw', 'sub', 'subw', 'c.sub', 'and', 'or', 'xor', 'mul',
                'sh1add', 'sh2add', 'sh3add', 'slli', 'srli', 'srai', 'andi', 'ori', 'xori', 'sll', 'srl', 'sra'):
        a = src[0][1] if src else None
        b = src[1][1] if len(src) > 1 else (int(ops[-1], 0) if ops and re.match(r'^-?(0x)?[0-9a-fA-F]+$', ops[-1]) else None)
        if a is not None and b is not None:
            f = {'add': lambda x, y: x + y, 'c.add': lambda x, y: x + y, 'addw': lambda x, y: x + y,
                 'c.addw': lambda x, y: x + y, 'sub': lambda x, y: x - y, 'subw': lambda x, y: x - y,
                 'c.sub': lambda x, y: x - y, 'and': lambda x, y: x & y, 'andi': lambda x, y: x & y,
                 'or': lambda x, y: x | y, 'ori': lambda x, y: x | y, 'xor': lambda x, y: x ^ y,
                 'xori': lambda x, y: x ^ y, 'mul': lambda x, y: x * y,
                 'sh1add': lambda x, y: (x << 1) + y, 'sh2add': lambda x, y: (x << 2) + y,
                 'sh3add': lambda x, y: (x << 3) + y, 'slli': lambda x, y: x << y, 'sll': lambda x, y: x << (y & 63),
                 'srli': lambda x, y: (x & M64) >> y, 'srl': lambda x, y: (x & M64) >> (y & 63),
                 'srai': lambda x, y: x >> y, 'sra': lambda x, y: x >> (y & 63)}.get(mn)
            if f:
                val = sx(f(a, b) & M64, 32 if mn.endswith('w') else 64)
    new[rd] = (tags, val)
    return new, uses


def run(I, path, fn):
    s = I.fsym(fn)
    if not s:
        print('# %s: absent from %s' % (fn, path))
        return
    a, n = s
    b = S.frd(I, a, n)
    ins = {i.address: i for i in MD.disasm(b, 0)}
    start = min(ins)
    state = {start: {}}
    todo, seen2, sites = [start], 0, {}
    while todo:
        o = todo.pop()
        i = ins.get(o)
        if i is None:
            continue
        st = state[o]
        new, uses = step(st, i)
        for breg, imm, kind in uses:
            tags, val = st.get(breg, (frozenset(), None))
            key = (o, breg)
            prev = sites.get(key)
            if prev is None or len(tags) > len(prev[0]):
                sites[key] = (tags, val, imm, kind, i)
        nxt = []
        mn = i.mnemonic
        if mn in ('ret', 'c.ret') or mn in ('jr', 'c.jr', 'jalr', 'c.jalr') and (not ops_of(i) or ops_of(i)[0] != 'ra'):
            nxt = []
        elif mn.startswith('b') and mn not in ('bext', 'binv', 'bclr', 'bset'):
            t = int(ops_of(i)[-1], 0)
            nxt = [o + i.size, (o + t) & M64]
        elif mn in ('j', 'c.j'):
            nxt = [(o + int(ops_of(i)[-1], 0)) & M64]
        else:
            nxt = [o + i.size]
        for q in nxt:
            if q not in ins:
                continue
            old = state.get(q)
            merged = dict(new) if old is None else None
            if old is not None:
                merged = dict(old)
                ch = False
                for r, (tg, vl) in new.items():
                    otg, ovl = old.get(r, (frozenset(), None))
                    u = otg | tg
                    v = vl if (r in old and ovl == vl) else (vl if r not in old else None)
                    if u != otg or v != ovl:
                        merged[r] = (u, v); ch = True
                if not ch:
                    continue
            state[q] = merged
            todo.append(q)
    multi = [(k, v) for k, v in sorted(sites.items()) if len(v[0]) >= 2]
    one = [(k, v) for k, v in sorted(sites.items()) if len(v[0]) == 1]
    for (o, breg), (tags, val, imm, kind, i) in multi:
        ea = '-'
        if val is not None:
            t = (val + imm) & M64
            ea = '%#x %s' % (t, S.qres(I, t) or '(ambiguous)')
        print('SITE\t%s\t+%#x\t%s %s\tbase %s\tluis %d [%s]\tvalue %s\tea %s\t%s'
              % (fn, o, i.mnemonic, i.op_str, breg, len(tags), ' '.join('+%#x' % t for t in sorted(tags)),
                 ('%#x' % (val & M64)) if val is not None else 'unknown', ea, kind))
    print('TOTAL\t%s\t%s\tbases with >=2 lui %d\tbases with 1 lui %d\tbase sites %d'
          % (os.path.basename(path), fn, len(multi), len(one), len(sites)))


for p in sys.argv[3:]:
    I = S.Img(p)
    print('# image %s sha256 %s' % (p, S.sha(p)[:12]))
    for fn in FNS:
        run(I, p, fn)
