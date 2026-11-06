#!/usr/bin/env python3
"""failopen.py -- every load / store / jalr / AMO base of a function that an address value formed in the function
reaches, through any of the KNOWN FAIL-OPEN shapes of cmpkit 86da41d3ef68, with its target named on both sides of a
pair. Read-only: it reads ELF files and GNU objdump listings, and writes nothing.

Input: per image, the ELF file and the listing `riscv64-alpine-linux-musl-objdump -d -M no-aliases --disassemble=FN`
of each function, concatenated (run.sh makes them). The ELF is read for its sections, symbols and bytes only; every
instruction comes from objdump text. A parcel the ELF listing prints as `.insn` (objdump follows the ELF's arch
attribute, which may lack an extension the CPU still executes, e.g. C) is taken from objdump's listing of the same
bytes as a plain binary. A line still not decoded is counted (`undecoded`) and printed.

Dataflow (per function and image): a MAY forward pass over the whole control-flow graph to a fixpoint (both edges of
every branch; every jal / jalr edge that stays inside the function's region, so a callee inside the region gets its
a0-a7; a jalr whose base holds an in-region constant, such as the return to an in-region call), with SYMBOLIC values:
each register, FP register, CSR, stack slot (by its offset from the entry sp) and statically addressed memory cell
holds a set of terms over
  constants, entry values (`in:a0`, `in:sp`, ...), loaded values (`[w addr]`), call results, and every ALU op.
A load from a statically known address in read-only or RELRO memory (.got, .rodata, ...) yields the stored constant
(a loaded constant); a load from writable memory yields a runtime value named by the address it was read from. A
store whose base is neither a stack slot nor a static address updates no tracked cell. Loops are widened to
`phi(+off,reg){...}` terms that keep every constant that flowed in. Code that the pass does not reach from the entry
(a jump-table arm, or code reached only by fall-through from one) is seeded with the merged state of every
unresolved indirect jump, and then walked; no instruction is skipped. The pass is path-insensitive, so it reports a
value on paths the code never takes (more sites and shapes, never fewer).

At every load / store / jalr / AMO the effective address is base + immediate. Each value carries tags: its origins
(lui, c.lui, auipc, a loaded constant `ldk`, an addi-from-zero `li`) and the shapes it passed through.
A site is IN SCOPE when its base carries an address value formed in the function: a lui / c.lui / auipc / loaded
constant origin, or a constant that lies in a PT_LOAD of the image. Shapes of an in-scope site:
  a  the load / store immediate is not 0 (V + imm)
  b  an addi / addiw (immediate not 0) on the value
  c  an ori / xori / slli on the value
  d  a stack spill and reload, an FP move, or a CSR write and read on the value
  e  the site, or an instruction on the value's path, lies in code reached only through an indirect jump or by
     fall-through from such code (a jump-table arm)
  f  the value was passed in a0-a7 to a callee inside the function's region
  g  a c.lui origin
  h  an origin that is not lui / c.lui (auipc, a loaded constant, or a constant built from li)
Target of a site, per side: `static <symbol>+<offset>` when the effective address is a constant (a .got cell is named
by the address it holds, `GOT[<symbol>+<offset>]`; an address in no sized symbol is named by its section and its
bytes: the bytes the access reads, as the kit's full-bytes acceptance compares them), else `runtime <term>`, where
every static address inside the term is named the same way (an address in no sized symbol by its section and the
bytes there: up to the first NUL when they start as a C string, else 64 bytes). A site whose base holds several
values lists every target. Verdict: SAME when the two sides' targets are equal strings, else DIFFERENT. The two sides
must hold the same instruction offsets with the same mnemonic and register operands (checked and printed).
usage:
  failopen.py pair FNLIST NAME1=ELF1=LISTING1[=RAW1] NAME2=ELF2=LISTING2[=RAW2]   (FNLIST: comma-separated names;
      RAW: objdump of the functions' bytes as a plain binary, read only for parcels LISTING prints as `.insn`)
  failopen.py bytes ELF FN OUT        (writes FN's bytes to OUT and prints its address, for the RAW listing)
"""
import hashlib, re, struct, sys

M64 = (1 << 64) - 1
IREGS = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
         's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
FREGS = ['ft%d' % i for i in range(12)] + ['fs%d' % i for i in range(12)] + ['fa%d' % i for i in range(8)]
IR, FR = set(IREGS), set(FREGS)
REGS = IR | FR
ARGS = ['a%d' % i for i in range(8)]
CALLER = ['ra', 't0', 't1', 't2', 't3', 't4', 't5', 't6'] + ARGS + ['ft%d' % i for i in range(12)] + \
    ['fa%d' % i for i in range(8)]
ORIGIN_ADDR = {'lui', 'c.lui', 'auipc', 'ldk'}
LOADW = {'lb': 's1', 'lh': 's2', 'lw': 's4', 'ld': 's8', 'lbu': 'u1', 'lhu': 'u2', 'lwu': 'u4', 'flw': 'f4',
         'fld': 'f8', 'c.ld': 's8', 'c.lw': 's4', 'c.fld': 'f8', 'c.ldsp': 's8', 'c.lwsp': 's4', 'c.fldsp': 'f8'}
STOREW = {'sb': 1, 'sh': 2, 'sw': 4, 'sd': 8, 'fsw': 4, 'fsd': 8, 'c.sd': 8, 'c.sw': 4, 'c.fsd': 8, 'c.sdsp': 8,
          'c.swsp': 4, 'c.fsdsp': 8}
BRANCH = {'beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu'}
CBRANCH = {'c.beqz', 'c.bnez'}
COMMUT = {'add', 'and', 'or', 'xor', 'mul', 'mulhu', 'mulh', 'addw', 'mulw'}
NOP = {'fence', 'fence.i', 'fence.tso', 'c.nop', 'pause', 'ebreak', 'c.ebreak', 'wfi'}
CIMM = {'c.addi': 'addi', 'c.addiw': 'addiw', 'c.slli': 'slli', 'c.srli': 'srli', 'c.srai': 'srai',
        'c.andi': 'andi', 'c.addi16sp': 'addi'}
K, WIDEN_AFTER, DEPTH = 8, 4, 16


def sx(v, b=64):
    v &= (1 << b) - 1
    return v - (1 << b) if v >> (b - 1) else v


def hexs(v):
    v &= M64
    return '-%#x' % ((1 << 64) - v) if v >> 63 else '%#x' % v


# ---------------------------------------------------------------------------------------------------- ELF (read only)
class Elf:
    def __init__(self, path):
        self.path = path
        self.d = open(path, 'rb').read()
        self.sha = hashlib.sha256(self.d).hexdigest()
        d = self.d
        if d[:4] != b'\x7fELF' or d[4] != 2 or d[5] != 1:
            raise SystemExit('failopen: %s is not ELF64 LE' % path)
        (self.type, self.mach, _, self.entry, phoff, shoff, _, _, phes, phn, shes, shn, shstr) = \
            struct.unpack_from('<HHIQQQIHHHHHH', d, 16)
        self.loads, self.tls, self.relro = [], None, []
        for i in range(phn):
            (pt, pf, off, va, _, fsz, msz, _) = struct.unpack_from('<IIQQQQQQ', d, phoff + i * phes)
            if pt == 1:
                self.loads.append((va, msz, fsz, off, pf))
            elif pt == 7:
                self.tls = (va, msz)
            elif pt == 0x6474e552:
                self.relro.append((va, va + msz))
        sh = [struct.unpack_from('<IIQQQQIIQQ', d, shoff + i * shes) for i in range(shn)]
        names = sh[shstr]

        def cstr(base, o):
            e = d.index(b'\0', base + o)
            return d[base + o:e].decode('latin-1')
        self.secs = []
        for (nm, ty, fl, ad, off, sz, ln, inf, al, es) in sh:
            self.secs.append(dict(name=cstr(names[4], nm), type=ty, flags=fl, addr=ad, off=off, size=sz, link=ln,
                                  entsize=es))
        self.syms = []
        for s in self.secs:
            if s['type'] != 2:          # SHT_SYMTAB
                continue
            strs = self.secs[s['link']]['off']
            for j in range(s['size'] // 24):
                (nm, info, oth, shx, val, size) = struct.unpack_from('<IBBHQQ', d, s['off'] + j * 24)
                if not nm:
                    continue
                self.syms.append(dict(name=cstr(strs, nm), value=val, size=size, type=info & 15, bind=info >> 4,
                                      shndx=shx))
        self.alloc = sorted([s for s in self.secs if s['flags'] & 2 and s['size'] and s['addr']],
                            key=lambda s: s['addr'])
        self.sized = sorted([s for s in self.syms if s['size'] and s['type'] in (0, 1, 2) and s['shndx']],
                            key=lambda s: (s['value'], s['size'], s['name']))
        self.byname = {}
        for s in self.syms:
            if s['type'] == 2 and s['size']:
                self.byname.setdefault(s['name'], []).append(s)
        self._names = {}

    def inload(self, a):
        return any(va <= a < va + msz for (va, msz, _, _, _) in self.loads)

    def read(self, a, n):
        for (va, msz, fsz, off, _) in self.loads:
            if va <= a and a + n <= va + fsz:
                return self.d[off + a - va: off + a - va + n]
        return None

    def sec(self, a):
        for s in self.alloc:
            if s['addr'] <= a < s['addr'] + s['size']:
                return s
        return None

    def constmem(self, a):
        """the bytes at a are a link-time constant: a non-writable allocated section, or RELRO (.got, ...)"""
        s = self.sec(a)
        if not s or s['type'] == 8:     # SHT_NOBITS
            return False
        return not (s['flags'] & 1) or any(lo <= a < hi for lo, hi in self.relro) or s['name'] == '.got'

    def fsym(self, fn):
        c = self.byname.get(fn, [])
        if len(c) != 1:
            raise SystemExit('failopen: %s has %d FUNC symbols named %s' % (self.path, len(c), fn))
        return c[0]['value'], c[0]['size']

    def name(self, a, depth=0, width=None):
        """symbol + offset of a static address; None when a lies in no allocated section. An address in no sized
        symbol is named by its section and its bytes: the `width` bytes an access reads, when given, else up to the
        first NUL when they start as a C string, else 64 bytes"""
        a &= M64
        if (a, depth, width) in self._names:
            return self._names[(a, depth, width)]
        s = self.sec(a)
        r = None
        if s is not None:
            if s['name'] in ('.got', '.got.plt'):
                cell = a - ((a - s['addr']) % 8)
                b = self.read(cell, 8)
                v = struct.unpack('<Q', b)[0] if b else None
                inner = (self.name(v, depth + 1) if depth < 2 else None) if v is not None else None
                r = 'GOT[%s]' % (inner if inner else (hexs(v) if v is not None else '?')) + \
                    ('+%d' % (a - cell) if a != cell else '')
            else:
                best = None
                for y in self.sized:
                    if y['value'] > a:
                        break
                    if a < y['value'] + y['size'] and (best is None or y['size'] < best['size'] or
                                                        (y['size'] == best['size'] and y['name'] < best['name'])):
                        best = y
                if best is not None:
                    r = '%s+%#x%s' % (best['name'], a - best['value'], '@tls' if best['type'] == 6 else '')
                elif s['type'] == 8:
                    r = '(%s) unnamed, no bytes, +%#x into the section' % (s['name'], a - s['addr'])
                elif width:
                    b = self.read(a, width) or b''
                    r = '(%s) unnamed, the %d bytes read %s' % (s['name'], width, b.hex())
                else:
                    b = self.read(a, min(64, s['addr'] + s['size'] - a)) or b''
                    z = b.find(b'\0')
                    if b and 32 <= b[0] < 127 and z > 0 and all(32 <= c < 127 or c in (9, 10, 13) for c in b[:z]):
                        r = '(%s) unnamed, C string %r' % (s['name'], b[:z].decode('latin-1'))
                    else:
                        r = '(%s) unnamed, %d bytes %s' % (s['name'], len(b), b.hex())
        self._names[(a, depth, width)] = r
        return r


# ------------------------------------------------------------------------------------------- objdump listing parser
LINE = re.compile(r'^\s*([0-9a-f]+):\t([0-9a-f]+(?: [0-9a-f]+)*)\s*\t(\S+)(?:\t(.*))?$')
HEAD = re.compile(r'^([0-9a-f]+) <(.+)>:$')
MEM = re.compile(r'^(-?(?:0x)?[0-9a-f]*)\((\w+)\)$')


def parse_lines(path):
    """(function name or None, instruction) for every instruction line of an objdump listing"""
    cur = None
    for ln in open(path, encoding='latin-1'):
        ln = ln.rstrip('\n')
        m = HEAD.match(ln)
        if m:
            cur = (m.group(2), int(m.group(1), 16))
            continue
        m = LINE.match(ln)
        if m and cur is not None:
            word = m.group(2).replace(' ', '')
            ops = m.group(4) or ''
            if ' # ' in ops:
                ops = ops.split(' # ', 1)[0]
            sym = re.search(r' <([^>]+)>$', ops)
            ops = re.sub(r' <[^>]+>$', '', ops).strip()
            yield cur, dict(pc=int(m.group(1), 16), size=len(word) // 2, word=word, mn=m.group(3),
                            ops=[o.strip() for o in ops.split(',')] if ops else [],
                            sym=sym.group(1) if sym else None, text=(m.group(3) + ' ' + ops).strip(), raw=False)


def parse_listing(path, raw=None):
    """the listing of the ELF; a parcel it prints as `.insn` (the ELF's arch attribute lacks the extension, e.g. a
    compressed parcel when the attribute has no C) is taken from RAW, objdump's listing of the same bytes as a plain
    binary (`-b binary -m riscv:rv64`, default arch), at the same address and of the same size"""
    fns = {}
    for (fn, a), i in parse_lines(path):
        fns.setdefault(fn, {'addr': a, 'ins': []})['ins'].append(i)
    if raw:
        alt = {i['pc']: i for _, i in parse_lines(raw)}
        for f in fns.values():
            for k, i in enumerate(f['ins']):
                j = alt.get(i['pc'])
                if i['mn'].startswith('.') and j and j['size'] == i['size'] and j['word'] == i['word'] and \
                        not j['mn'].startswith('.'):
                    f['ins'][k] = dict(j, raw=True)
    return fns


# ------------------------------------------------------------------------------------------------ hash-consed terms
TT, TI = [], {}            # term table: id -> (kind, args...); intern map


def term(*t):
    i = TI.get(t)
    if i is None:
        i = len(TT)
        TT.append(t)
        TI[t] = i
        DEP.append(1 + max([DEP[c] for c in kids(t)], default=0))
        KL.append(_kleaves(t))
        KV.append(_vleaves(t))
    return i


DEP, KL, KV = [], [], []


def kids(t):
    k = t[0]
    if k == 'ld':
        return [t[2]]
    if k == 'add':
        return [t[1]]
    if k == 'o':
        return list(t[2])
    return []


def _kleaves(t):
    """constant leaves of a term that may be addresses (>= 0x1000), and the static addresses of its loads"""
    k = t[0]
    if k == 'k':
        return frozenset([('k', t[1])]) if 0x1000 <= t[1] < (1 << 48) else frozenset()
    if k in ('phi', 'cut'):
        return t[3]
    s = frozenset().union(*[KL[c] for c in kids(t)]) if kids(t) else frozenset()
    if k == 'ld' and TT[t[2]][0] == 'k':
        s = s | {('ld', t[1], TT[t[2]][1])}
    if k == 'add':
        s = s | ({('k', t[2] & M64)} if 0x1000 <= (t[2] & M64) < (1 << 48) else frozenset())
    return s if len(s) <= 64 else frozenset(sorted(s)[:64])


def _vleaves(t):
    """the constants (>= 0x1000) that are part of the term's VALUE: not those under a load, whose value is runtime"""
    k = t[0]
    if k == 'k':
        return frozenset([t[1]]) if 0x1000 <= t[1] < (1 << 48) else frozenset()
    if k in ('phi', 'cut'):
        return t[4]
    if k == 'add':
        s = KV[t[1]] | ({t[2] & M64} if 0x1000 <= (t[2] & M64) < (1 << 48) else frozenset())
    elif k == 'o':
        s = frozenset().union(*[KV[c] for c in t[2]]) if t[2] else frozenset()
    else:
        s = frozenset()
    return s if len(s) <= 64 else frozenset(sorted(s)[:64])


def K_(v):
    return term('k', v & M64)


def cval(i):
    t = TT[i]
    return t[1] if t[0] == 'k' else None


def split(i):
    t = TT[i]
    if t[0] == 'k':
        return None, t[1]
    if t[0] == 'add':
        return t[1], t[2]
    return i, 0


def mk_add(a, b):
    xa, oa = split(a)
    xb, ob = split(b)
    off = (oa + ob) & M64
    bases = [x for x in (xa, xb) if x is not None]
    if not bases:
        return K_(off)
    if len(bases) == 1:
        s = bases[0]
    else:
        s = term('o', 'add', tuple(sorted(bases)), ())
    return s if off == 0 else term('add', s, off)


FOLD = {
    'add': lambda x, y: x + y, 'addw': lambda x, y: sx(x + y, 32), 'sub': lambda x, y: x - y,
    'subw': lambda x, y: sx(x - y, 32), 'and': lambda x, y: x & y, 'or': lambda x, y: x | y,
    'xor': lambda x, y: x ^ y, 'sll': lambda x, y: x << (y & 63), 'srl': lambda x, y: (x & M64) >> (y & 63),
    'sra': lambda x, y: sx(x) >> (y & 63), 'sllw': lambda x, y: sx(x << (y & 31), 32),
    'srlw': lambda x, y: sx((x & 0xffffffff) >> (y & 31), 32), 'sraw': lambda x, y: sx(sx(x, 32) >> (y & 31), 32),
    'slt': lambda x, y: int(sx(x) < sx(y)), 'sltu': lambda x, y: int((x & M64) < (y & M64)),
    'mul': lambda x, y: x * y, 'mulw': lambda x, y: sx(x * y, 32),
    'mulhu': lambda x, y: ((x & M64) * (y & M64)) >> 64,
    'sh1add': lambda x, y: (x << 1) + y, 'sh2add': lambda x, y: (x << 2) + y, 'sh3add': lambda x, y: (x << 3) + y,
}
IFOLD = {'addi': 'add', 'addiw': 'addw', 'andi': 'and', 'ori': 'or', 'xori': 'xor', 'slli': 'sll', 'srli': 'srl',
         'srai': 'sra', 'slliw': 'sllw', 'srliw': 'srlw', 'sraiw': 'sraw', 'slti': 'slt', 'sltiu': 'sltu'}


def mk_op(op, a, b, at=None):
    """op on two terms (b may be None for an immediate in `at`)"""
    if op == 'add':
        return mk_add(a, b)
    if op == 'sub' and cval(b) is not None:
        return mk_add(a, K_(-cval(b)))
    ca, cb = cval(a), cval(b) if b is not None else None
    if ca is not None and cb is not None and op in FOLD:
        return K_(FOLD[op](sx(ca), sx(cb)))
    args = (a, b) if b is not None else (a,)
    if op in COMMUT and b is not None:
        args = tuple(sorted(args))
    return term('o', op, args, ())


# --------------------------------------------------------------------------------------------------- the engine
class Fn:
    def __init__(self, img, fn, listing):
        self.img, self.fn = img, fn
        self.lo, self.size = img.fsym(fn)
        self.hi = self.lo + self.size
        L = listing.get(fn)
        if L is None or L['addr'] != self.lo:
            raise SystemExit('failopen: listing has no %s at %#x' % (fn, self.lo))
        self.ins = {i['pc']: i for i in L['ins']}
        self.order = sorted(self.ins)
        got = sum(self.ins[p]['size'] for p in self.order)
        self.covered = got == self.size and self.order[0] == self.lo
        self.undecoded = [self.ins[p] for p in self.order if self.ins[p]['mn'].startswith('.') or
                          self.ins[p]['mn'] in ('unimp', 'c.unimp')]
        self.generic, self.errs, self.incalls = {}, [], set()
        self.state, self.changes = {}, {}
        self.sites = {}
        self.unresolved = []          # (pc, state) of indirect jumps with a base the pass cannot resolve
        self.seeded = set()           # pcs reached only through seeding (jump-table arm code)
        self.seeds = []

    # -- values
    def addr_like(self, av):
        if av[1] & ORIGIN_ADDR:
            return True
        return any(self.img.inload(v) for v in KV[av[0]])

    def get(self, st, key):
        v = st.get(key)
        if v is not None:
            return v
        if isinstance(key, tuple):
            if key[0] == 'S':
                return frozenset([(term('ld', 'u%d' % key[2], mk_add(term('in', 'sp'), K_(key[1]))),
                                   frozenset())])
            return frozenset([(term('ld', 'u%d' % key[2], K_(key[1])), frozenset())])
        if key == 'zero':
            return frozenset([(K_(0), frozenset())])
        return frozenset([(term('in', key), frozenset())])

    def widen(self, pc, key, avs):
        seeds = frozenset().union(*[KL[t] for t, _ in avs])
        vseeds = frozenset().union(*[KV[t] for t, _ in avs])
        tags = frozenset().union(*[g for _, g in avs])
        return frozenset([(term('phi', pc - self.lo, str(key), seeds, vseeds), tags)])

    def merge_into(self, pc, new):
        old = self.state.get(pc)
        if old is None:
            self.state[pc] = dict(new)
            return True
        ch = False
        m = dict(old)
        for key in set(old) | set(new):
            a, b = self.get(old, key), self.get(new, key)
            if b <= a:
                continue
            phis = [x for x in a if TT[x[0]][0] == 'phi' and TT[x[0]][1] == pc - self.lo and TT[x[0]][2] == str(key)]
            u = a | b
            n = self.changes.get((pc, key), 0) + 1
            self.changes[(pc, key)] = n
            if phis or len(u) > K or n > WIDEN_AFTER:
                u = self.widen(pc, key, u)
                if u == a:
                    continue
            m[key] = u
            ch = True
        if ch:
            self.state[pc] = m
        return ch

    # -- one instruction
    def setv(self, st, key, avs, i):
        if key == 'zero':
            return
        if i['pc'] in self.seeded:
            avs = frozenset((t, g | {'jt'}) for t, g in avs)
        avs = frozenset((self.cut(t, i, key), g) for t, g in avs)
        if len(avs) > K:
            avs = self.widen(i['pc'], key, avs)
        st[key] = avs

    def cut(self, t, i, key):
        if DEP[t] <= DEPTH:
            return t
        return term('cut', i['pc'] - self.lo, str(key), KL[t], KV[t])

    def tagged(self, avs, tag):
        return frozenset((t, g | {tag}) if self.addr_like((t, g)) else (t, g) for t, g in avs)

    def binop(self, st, op, ra, rb, tag=None):
        out = set()
        A, B = self.get(st, ra), self.get(st, rb)
        for ta, ga in A:
            for tb, gb in B:
                g = ga | gb
                fa, fb = self.addr_like((ta, ga)), self.addr_like((tb, gb))
                if fa and fb:
                    g = g | {'rr'}
                elif (fa or fb) and tag:
                    g = g | {tag}
                out.add((mk_op(op, ta, tb), g))
        return frozenset(out)

    def immop(self, st, mn, rs, imm):
        out = set()
        op = IFOLD[mn]
        for t, g in self.get(st, rs):
            if rs == 'zero' and mn == 'addi':
                out.add((K_(imm), frozenset(['li'])))
                continue
            if mn == 'addi' and imm == 0:              # a register copy
                out.add((t, g))
                continue
            nt = mk_op(op, t, K_(imm)) if mn != 'addi' else mk_add(t, K_(imm))
            if self.addr_like((t, g)):
                if mn in ('addi', 'addiw'):
                    g = g | ({'addi', 'addi*'} if 'addi' in g else {'addi'})
                elif mn in ('ori', 'xori', 'slli', 'slliw'):
                    g = g | {mn.rstrip('w') if mn == 'slliw' else mn}
                else:
                    g = g | {'alu'}
            out.add((nt, g))
        return frozenset(out)

    def memaddr(self, st, base, imm):
        return frozenset((mk_add(t, K_(imm)), g) for t, g in self.get(st, base))

    def slot(self, ea):
        x, o = split(ea)
        if x is not None and TT[x] == ('in', 'sp'):
            return sx(o)
        return None

    def load(self, st, i, rd, base, imm, w):
        out = set()
        width = int(w[1])
        for ea, g in self.memaddr(st, base, imm):
            d = self.slot(ea)
            c = cval(ea)
            if d is not None:
                key = ('S', d, width)
                if key in st:
                    out |= {(t, gg | ({'spill'} if self.addr_like((t, gg)) else frozenset())) for t, gg in st[key]}
                    continue
                over = [k for k in st if isinstance(k, tuple) and k[0] == 'S' and k[1] < d + width and
                        d < k[1] + k[2]]
                if over:
                    for k in over:
                        out |= {(term('o', 'part', (t,), (k[1] - d, width)),
                                 gg | ({'spill'} if self.addr_like((t, gg)) else frozenset())) for t, gg in st[k]}
                    continue
                out.add((term('ld', w, ea), frozenset()))
                continue
            if c is not None:
                key = ('G', c, width)
                if key in st:
                    out |= {(t, gg | ({'gmem'} if self.addr_like((t, gg)) else frozenset())) for t, gg in st[key]}
                if self.img.constmem(c) and w[0] in 'su':
                    b = self.img.read(c, width)
                    if b is not None:
                        v = int.from_bytes(b, 'little')
                        if w[0] == 's':
                            v = sx(v, 8 * width)
                        out.add((K_(v), g | {'ldk'}))
                        continue
                out.add((term('ld', w, ea), frozenset()))
                continue
            out.add((term('ld', w, ea), frozenset()))
        self.setv(st, rd, frozenset(out), i)

    def store(self, st, i, rs, base, imm, width):
        """a store to a stack slot or a static cell: a strong update when the base holds one value, else weak"""
        val = self.get(st, rs)
        eas = self.memaddr(st, base, imm)
        for ea, g in eas:
            d, c = self.slot(ea), cval(ea)
            if d is not None:
                key = ('S', d, width)
            elif c is not None:
                key = ('G', c, width)
            else:
                continue
            if len(eas) == 1:
                for k in [k for k in st if isinstance(k, tuple) and k[0] == key[0] and k[1] < key[1] + width and
                          key[1] < k[1] + k[2]]:
                    del st[k]
                self.setv(st, key, val, i)
            else:
                self.setv(st, key, self.get(st, key) | val, i)

    def site(self, i, base, imm, kind, st, width=None):
        self.sites[i['pc'] - self.lo] = dict(i=i, base=base, imm=imm, kind=kind, ea=self.memaddr(st, base, imm),
                                             bavs=self.get(st, base), seeded=i['pc'] in self.seeded, width=width)

    def clobber(self, st, i, callee):
        for r in CALLER:
            if r in ('a0', 'a1', 'fa0', 'fa1'):
                st[r] = frozenset([(term('o', 'ret', (), (i['pc'] - self.lo, r, callee)), frozenset())])
            else:
                st[r] = frozenset([(term('o', 'clob', (), (i['pc'] - self.lo, r)), frozenset())])

    def step(self, pc, st):
        """successors [(pc, state)] of one instruction; records its sites"""
        i = self.ins[pc]
        mn, ops = i['mn'], i['ops']
        nxt = pc + i['size']
        st = dict(st)
        I = lambda s: int(s, 0)
        try:
            if mn in ('lui', 'c.lui'):
                v = sx((I(ops[1]) & 0xfffff) << 12, 32)
                self.setv(st, ops[0], frozenset([(K_(v), frozenset([mn]))]), i)
            elif mn == 'auipc':
                v = (pc + sx((I(ops[1]) & 0xfffff) << 12, 32)) & M64
                self.setv(st, ops[0], frozenset([(K_(v), frozenset(['auipc']))]), i)
            elif mn in IFOLD:
                self.setv(st, ops[0], self.immop(st, mn, ops[1], I(ops[2])), i)
            elif mn in ('c.li',):
                self.setv(st, ops[0], frozenset([(K_(I(ops[1])), frozenset(['li']))]), i)
            elif mn in CIMM:
                self.setv(st, ops[0], self.immop(st, CIMM[mn], ops[0], I(ops[1])), i)
            elif mn == 'c.addi4spn':
                self.setv(st, ops[0], self.immop(st, 'addi', ops[1], I(ops[2])), i)
            elif mn == 'c.mv':
                self.setv(st, ops[0], self.get(st, ops[1]), i)
            elif mn in ('c.add', 'c.sub', 'c.xor', 'c.or', 'c.and', 'c.addw', 'c.subw'):
                self.setv(st, ops[0], self.binop(st, mn[2:], ops[0], ops[1]), i)
            elif mn in FOLD and len(ops) == 3:
                self.setv(st, ops[0], self.binop(st, mn, ops[1], ops[2]), i)
            elif mn in LOADW:
                m = MEM.match(ops[1])
                b, imm = m.group(2), (int(m.group(1), 0) if m.group(1) else 0)
                self.site(i, b, imm, 'load', st, int(LOADW[mn][1]))
                self.load(st, i, ops[0], b, imm, LOADW[mn])
            elif mn in STOREW:
                m = MEM.match(ops[1])
                b, imm = m.group(2), (int(m.group(1), 0) if m.group(1) else 0)
                self.site(i, b, imm, 'store', st, STOREW[mn])
                self.store(st, i, ops[0], b, imm, STOREW[mn])
            elif mn.startswith(('amo', 'lr.', 'sc.')):
                m = MEM.match(ops[-1])
                b = m.group(2)
                self.site(i, b, 0, 'amo', st, 8 if mn.split('.')[1] == 'd' else 4)
                self.setv(st, ops[0], frozenset([(term('ld', 'amo', mk_add(t, K_(0))), frozenset())
                                                 for t, _ in self.get(st, b)]), i)
            elif mn in BRANCH or mn in CBRANCH:
                t = int(ops[-1], 16)
                return [(nxt, st), (t, st)]
            elif mn in ('jal', 'c.j', 'c.jal'):
                rd = ops[0] if mn == 'jal' else ('zero' if mn == 'c.j' else 'ra')
                t = int(ops[-1], 16)
                inreg = self.lo <= t < self.hi
                if rd == 'zero':
                    return [(t, st)] if inreg else []
                out = []
                if inreg:
                    self.incalls.add(pc)
                    c = dict(st)
                    for a in ARGS:
                        c[a] = self.tagged(self.get(c, a), 'callee')
                    self.setv(c, rd, frozenset([(K_(nxt), frozenset())]), i)
                    out.append((t, c))
                self.clobber(st, i, i['sym'] or hexs(t))
                if rd != 'ra':
                    self.setv(st, rd, frozenset([(K_(nxt), frozenset())]), i)
                out.append((nxt, st))
                return out
            elif mn in ('jalr', 'c.jr', 'c.jalr'):
                if mn == 'jalr':
                    m = MEM.match(ops[1])
                    rd, b, imm = ops[0], m.group(2), (int(m.group(1), 0) if m.group(1) else 0)
                else:
                    rd, b, imm = ('zero' if mn == 'c.jr' else 'ra'), ops[0], 0
                self.site(i, b, imm, 'jump', st)
                targets, unres = [], False
                for t, g in self.get(st, b):
                    c = cval(t)
                    if c is not None and self.lo <= ((c + imm) & ~1 & M64) < self.hi:
                        targets.append((c + imm) & ~1 & M64)
                    elif TT[t] == ('in', 'ra') and imm == 0:
                        pass                                    # the function's own return
                    else:
                        unres = True
                out = []
                if rd == 'zero':
                    if unres:
                        self.unresolved.append((pc, st))
                    return [(t, st) for t in targets]
                for t in targets:
                    self.incalls.add(pc)
                    c = dict(st)
                    for a in ARGS:
                        c[a] = self.tagged(self.get(c, a), 'callee')
                    self.setv(c, rd, frozenset([(K_(nxt), frozenset())]), i)
                    out.append((t, c))
                self.clobber(st, i, 'indirect')
                if rd != 'ra':
                    self.setv(st, rd, frozenset([(K_(nxt), frozenset())]), i)
                out.append((nxt, st))
                return out
            elif mn in ('ecall',):
                st['a0'] = frozenset([(term('o', 'ret', (), (pc - self.lo, 'a0', 'ecall')), frozenset())])
            elif mn in NOP or (mn == 'c.addi' and ops and ops[0] == 'zero'):
                pass
            elif mn in ('fmv.x.d', 'fmv.x.w', 'fmv.d.x', 'fmv.w.x'):
                self.setv(st, ops[0], self.tagged(self.get(st, ops[1]), 'fmv'), i)
            elif mn in ('fsgnj.d', 'fsgnj.s') and ops[1] == ops[2]:
                self.setv(st, ops[0], self.tagged(self.get(st, ops[1]), 'fmv'), i)
            elif mn in ('csrrw', 'csrrs', 'csrrc', 'csrrwi', 'csrrsi', 'csrrci'):
                rd, csr, src = ops
                ck = 'csr:' + csr
                old = self.tagged(self.get(st, ck), 'csr')
                if mn == 'csrrw':
                    newv = self.get(st, src)
                elif mn == 'csrrwi':
                    newv = frozenset([(K_(I(src)), frozenset())])
                elif mn in ('csrrs', 'csrrc') and src == 'zero' or mn in ('csrrsi', 'csrrci') and I(src) == 0:
                    newv = None
                else:
                    sv = self.get(st, src) if mn in ('csrrs', 'csrrc') else frozenset([(K_(I(src)), frozenset())])
                    newv = frozenset((term('o', mn, (a, b), ()), ga | gb) for a, ga in old for b, gb in sv)
                if newv is not None:
                    self.setv(st, ck, newv, i)
                self.setv(st, rd, old, i)
            else:
                # any other instruction: its first register operand gets a term over all its other operands
                self.generic[mn] = self.generic.get(mn, 0) + 1
                regs = [o for o in ops if o in REGS]
                if regs and ops[0] in REGS:
                    srcs = [self.get(st, r) for r in ops[1:] if r in REGS]
                    imms = tuple(o for o in ops[1:] if o not in REGS)
                    out = {(term('o', mn, (), imms), frozenset())}
                    for s in srcs:
                        out = {(term('o', mn, tuple(TT[t][2]) + (u,), imms) if TT[t][0] == 'o' else t, g | gu)
                               for t, g in out for u, gu in s}
                    self.setv(st, ops[0], frozenset(out), i)
        except (ValueError, IndexError, AttributeError) as e:
            self.errs.append(dict(i, err='%s: %s' % (type(e).__name__, e)))
        return [(nxt, st)]

    def walk(self, starts):
        todo = list(starts)
        while todo:
            pc = todo.pop()
            if pc not in self.ins:
                continue
            for q, s in self.step(pc, self.state[pc]):
                if q in self.ins and self.merge_into(q, s):
                    todo.append(q)

    def run(self):
        self.state[self.lo] = {}
        self.walk([self.lo])
        self.direct = set(self.state)
        while True:
            left = [p for p in self.order if p not in self.state]
            if not left:
                break
            u = left[0]
            # code the pass does not reach from the entry: seeded with the merged state of every unresolved
            # indirect jump (none: the entry values), its values tagged `jt`, and walked like the rest
            src = [s for _, s in self.unresolved]
            keys = set().union(*[set(s) for s in src]) if src else set()
            seed = {k: frozenset().union(*[self.get(s, k) for s in src]) for k in keys}
            self.seeded |= set(left)
            self.seeds.append((u, len(src)))
            self.state[u] = {k: frozenset((t, g | {'jt'}) for t, g in v) for k, v in seed.items()}
            self.walk([u])
        # the sites, read once more from the fixpoint state of each instruction
        self.sites, self.unresolved, self.generic, self.errs, self.incalls = {}, [], {}, [], set()
        for pc in self.order:
            self.step(pc, self.state[pc])
        return self


# ------------------------------------------------------------------------------------------------------- rendering
class Render:
    def __init__(self, img):
        self.img, self.memo = img, {}

    def const(self, v):
        n = self.img.name(v) if self.img.inload(v) or self.img.sec(v) else None
        return ('&' + n) if n else hexs(v)

    def __call__(self, i):
        r = self.memo.get(i)
        if r is not None:
            return r
        t = TT[i]
        k = t[0]
        if k == 'k':
            r = self.const(t[1])
        elif k == 'in':
            r = 'in:' + t[1]
        elif k == 'ld':
            r = '[%s %s]' % (t[1], self(t[2]))
        elif k == 'add':
            r = '%s%s%s' % (self(t[1]), '-' if t[2] >> 63 else '+', self.const(t[2]) if not t[2] >> 63 else
                            hexs(t[2])[1:])
        elif k == 'o':
            cs = [self(c) for c in t[2]]
            if t[1] in COMMUT:
                cs.sort()
            r = '%s(%s)' % (t[1], ','.join(cs + [str(x) for x in t[3]]))
        elif k in ('phi', 'cut'):
            ss = sorted(self.const(x[1]) if x[0] == 'k' else '[%s %s]' % (x[1], self.const(x[2])) for x in t[3])
            r = '%s(+%#x,%s){%s}' % (k, t[1], t[2], ','.join(ss))
        else:
            r = repr(t)
        self.memo[i] = r
        return r


SHAPES = 'abcdefgh'


def shapes_of(F, rec):
    """the shapes (a)-(h) of one site, from the tags of the base values that carry a formed address"""
    sh = set()
    formed = [(t, g) for t, g in rec['bavs'] if F.addr_like((t, g))]
    for t, g in formed:
        if rec['imm'] != 0:
            sh.add('a')
        if g & {'addi'}:
            sh.add('b')
        if g & {'ori', 'xori', 'slli'}:
            sh.add('c')
        if g & {'spill', 'fmv', 'csr'}:
            sh.add('d')
        if 'jt' in g or rec['seeded']:
            sh.add('e')
        if 'callee' in g:
            sh.add('f')
        if 'c.lui' in g:
            sh.add('g')
        if g & {'auipc', 'ldk'} or ('li' in g and not g & {'lui', 'c.lui'}):
            sh.add('h')
    return bool(formed), ''.join(s for s in SHAPES if s in sh), \
        sorted(set().union(*[g for _, g in formed])) if formed else []


def target(F, R, rec):
    out = set()
    for t, g in rec['ea']:
        c = cval(t)
        if c is not None:
            n = F.img.name(c, width=rec['width'])
            out.add('static ' + (n if n else 'abs ' + hexs(c)))
        else:
            out.add('runtime ' + R(t))
    return ' | '.join(sorted(out))


def short(s, n=400):
    return s if len(s) <= n else s[:n - 20] + '...{sha256 %s}' % hashlib.sha256(s.encode()).hexdigest()[:12]


def strip_imm(ins):
    """mnemonic and register operands: what must be equal at one offset on both sides"""
    ops = []
    for o in ins['ops']:
        m = MEM.match(o)
        if m:
            ops.append('(%s)' % m.group(2))
        elif o in REGS:
            ops.append(o)
        else:
            ops.append('#')
    return ins['mn'] + ' ' + ','.join(ops)


def pair(fnlist, sides):
    fns = fnlist.split(',')
    imgs = []
    for s in sides:
        nm, elf, lst, *raw = s.split('=')
        imgs.append((nm, Elf(elf), parse_listing(lst, raw[0] if raw else None)))
    for nm, e, _ in imgs:
        print('# side %s: %s sha256 %s' % (nm, e.path.split('/')[-1], e.sha))
    grand = {'sites': 0, 'scope': 0, 'diff': 0, 'shape': {s: 0 for s in SHAPES}}
    for fn in fns:
        runs = []
        for nm, e, L in imgs:
            F = Fn(e, fn, L).run()
            runs.append((nm, e, F, Render(e)))
        (n1, e1, F1, R1), (n2, e2, F2, R2) = runs
        print('## %s  %s %#x : %s %#x  size %d : %d' % (fn, n1, F1.lo, n2, F2.lo, F1.size, F2.size))
        for nm, e, F, R in runs:
            print('# %s: %d instructions, cover %s, undecoded %d, generic %s, unresolved indirect jumps %d, '
                  'seeded runs %s, unreached-by-entry instructions %d, parcels decoded from the raw listing %d'
                  % (nm, len(F.order), F.covered, len(F.undecoded) + len(F.errs),
                     ','.join('%s:%d' % kv for kv in sorted(F.generic.items())) or '-', len(F.unresolved),
                     ','.join('+%#x(from %d jumps)' % (u - F.lo, n) for u, n in F.seeds) or '-',
                     len(set(F.order) - F.direct), sum(1 for i in F.ins.values() if i['raw'])) +
                  ', calls into its own region %d' % len(F.incalls))
            for u in F.undecoded + F.errs:
                print('UNDECODED\t%s\t+%#x\t%s\t%s' % (nm, u['pc'] - F.lo, u['text'], u.get('err', '')))
        offs1 = [p - F1.lo for p in F1.order]
        offs2 = [p - F2.lo for p in F2.order]
        mism = []
        if offs1 != offs2:
            mism.append('instruction offsets differ')
        else:
            for o in offs1:
                a, b = F1.ins[F1.lo + o], F2.ins[F2.lo + o]
                if strip_imm(a) != strip_imm(b):
                    mism.append('+%#x %s | %s' % (o, a['text'], b['text']))
        print('# instructions: %d offsets, mnemonic + register operands differ at %d%s'
              % (len(offs1), len(mism), (': ' + '; '.join(mism[:8])) if mism else ''))
        cnt = {s: 0 for s in SHAPES}
        nsites = nscope = ndiff = nstatic = nrt = 0
        for off in sorted(set(F1.sites) | set(F2.sites)):
            r1, r2 = F1.sites.get(off), F2.sites.get(off)
            if r1 is None or r2 is None:
                print('SITE\t%s\t+%#x\tone side only\tDIFFERENT' % (fn, off))
                ndiff += 1
                continue
            sc1, sh1, tg1 = shapes_of(F1, r1)
            sc2, sh2, tg2 = shapes_of(F2, r2)
            t1, t2 = target(F1, R1, r1), target(F2, R2, r2)
            v = 'SAME' if t1 == t2 else 'DIFFERENT'
            nsites += 1
            sc = sc1 or sc2
            sh = ''.join(s for s in SHAPES if s in sh1 + sh2)
            if sc:
                nscope += 1
                for s in sh:
                    cnt[s] += 1
                if all(x.startswith('static ') for x in t1.split(' | ')):
                    nstatic += 1
                else:
                    nrt += 1
            if v == 'DIFFERENT':
                ndiff += 1
            print('SITE\t%s\t+%#x\t%s\t%s base %s imm %d\t%s\tshapes %s\ttags %s\t%s: %s\t%s: %s\t%s'
                  % (fn, off, r1['i']['text'], r1['kind'], r1['base'], r1['imm'],
                     'in-scope' if sc else 'no-formed-address', sh or '-', ','.join(sorted(set(tg1) | set(tg2))) or
                     '-', n1, short(t1), n2, short(t2), v))
        print('TOTAL\t%s\tsites %d\tin-scope %d (static %d, runtime %d)\t%s\tDIFFERENT %d'
              % (fn, nsites, nscope, nstatic, nrt, ' '.join('%s %d' % (s, cnt[s]) for s in SHAPES), ndiff))
        grand['sites'] += nsites
        grand['scope'] += nscope
        grand['diff'] += ndiff
        for s in SHAPES:
            grand['shape'][s] += cnt[s]
    print('GRAND\tsites %d\tin-scope %d\t%s\tDIFFERENT %d'
          % (grand['sites'], grand['scope'], ' '.join('%s %d' % (s, grand['shape'][s]) for s in SHAPES),
             grand['diff']))


if __name__ == '__main__':
    if len(sys.argv) == 5 and sys.argv[1] == 'pair':
        pair(sys.argv[2], sys.argv[3:5])
    elif len(sys.argv) == 5 and sys.argv[1] == 'bytes':
        e = Elf(sys.argv[2])
        a, n = e.fsym(sys.argv[3])
        open(sys.argv[4], 'wb').write(e.read(a, n))
        print('%#x' % a)
    else:
        raise SystemExit(__doc__)
