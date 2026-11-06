#!/usr/bin/env python3
"""failopen.py -- the check of cmpkit 86da41d3ef68's known fail-opens on the functions behind the EQUAL* verdicts of
this record, with the hand traces of every site it finds. Read-only.

The kit does not judge a lui-derived address that reaches a load / store / jalr / AMO base through the load / store
immediate, an addi / addiw chain, ori / xori / slli, a stack spill, an FP move or a CSR round trip, a jump-table arm
reached only by fall-through, an in-function callee or c.lui, and it does not see addresses built without lui. An EQUAL*
verdict on a function where an address value reaches a base through one of these shapes needs a hand trace that names
the target on both sides.

The scan. For every function behind a compare row of the record, on both sides, a MAY dataflow over the function's
control-flow graph (union at every merge, fixed point; it leaves out only what is named below: the edges of a tail call,
of unimp and of a call that does not return, and the tokens a branch against x0 contradicts) carries each constant to
every register, stack slot, other memory cell with a known address, FP register and CSR that some path brings it to. A
constant comes from: a lui (4-byte) or a c.lui; an OP-IMM word with rs1 = x0 (li, c.li: built without lui); a load from
a fixed address in a read-only or RELRO section (a .got slot or a constant-pool word: built without lui); an auipc
(followed only past the pairing the kit judges: auipc, at most one addi, then the base). Each carried token keeps its
exact value on its paths (more than 8 values at one place, a partial reload, an FP conversion or a CSR read make it
unknown; a combination with a non-constant value makes it a dynamic addend) and the shapes it went through. A branch
against x0 drops, on each edge, the tokens whose exact value contradicts the edge. An indirect jump has an edge to every
word of the function, unless sp is back at its entry value and the target is the contents of a writable word (a tail
call through a function pointer such as REAL(strcmp)). A jal to a word inside the function carries the whole state
there, and every ret of the function returns to the word after it. unimp traps: it has no successor. A call out of the
function clears the caller-saved registers. A call to a function that does not return (abort, exit, _exit, _Exit,
__assert_fail, __stack_chk_fail, __asan_report_* other than *_noabort, __ubsan_handle_*_abort) has no edge to the next
word: the compiled code puts no return path after such a call (the next word starts another block or is unimp).

A SITE is a base whose carried constant can name an image object: a token whose exact value had magnitude >= 0x10000
(the lowest PT_LOAD address of every image of the record) at some point, a token whose value is unknown, or a base whose
value is one exact constant. Every other base that carries a constant carries only values below 0x10000 in magnitude
(frame sizes, the page constant, small offsets, masks, counters): it is counted, not traced, because every image starts
at 0x10000, so no such value names an image object.

The traces. For each compare row that one of the 62 EQUAL* / same claims cites (and, after them, each row that one of
the 7 claims with a DIFFERENT or SIZE kit verdict cites), the sites of the two sides inside the compared range are
paired by their offset from the range start, and each pair gets a row of fail-open-traces.tsv: a base that one .got
slot feeds is traced from the image bytes (the auipc + ld pair, the slot, the value in the slot, the symbol and offset
of value + immediate); every other site has a hand trace in HAND below, written after reading both listings. The tool
stops if a site has no trace, if a HAND entry has no site, or if the two sides name different targets.

usage: failopen.py KITDIR IMGDIR OUTFILE CMPOUT [CMPOUT ...]
       failopen.py --selftest
  KITDIR  the files of cmpkit 86da41d3ef68 (sha256(SHA256SUMS) starts 86da41d3ef68 and every member matches); the
          kit's word reader is used.
  IMGDIR  the unstripped twins; each compare output names its sides by tag in its `# TAG = path sha256 ...` lines.
  OUTFILE fail-open-traces.tsv.
  CMPOUT  the strictcmp3 `cmp` and kitrange outputs of the record.
  --selftest  one planted function per shape of the list; each must give a site.
"""
import sys, os, hashlib, importlib.util, bisect, collections
from elftools.elf.elffile import ELFFile

M64 = (1 << 64) - 1
NORET = ('abort', 'exit', '_exit', '_Exit', '__assert_fail', '__stack_chk_fail')
CALLER = (1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31)
FCALLER = tuple(32 + r for r in (0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31))


def sx(v, b):
    v &= (1 << b) - 1
    return v - (1 << b) if v & (1 << (b - 1)) else v


# ---- decoding: one word or parcel -> (kind, rd, rs1, rs2, imm, name); FP registers are 32..63
def dec(x, n):
    if n == 2:
        return dec16(x)
    op, rd, f3, rs1, rs2, f7 = x & 0x7f, (x >> 7) & 31, (x >> 12) & 7, (x >> 15) & 31, (x >> 20) & 31, x >> 25
    ii = sx(x >> 20, 12)
    if op == 0x37:
        return ('lui', rd, 0, 0, sx(x & 0xfffff000, 32), 'lui')
    if op == 0x17:
        return ('auipc', rd, 0, 0, sx(x & 0xfffff000, 32), 'auipc')
    if op == 0x6f:
        return ('jal', rd, 0, 0, sx((((x >> 31) & 1) << 20) | (((x >> 12) & 0xff) << 12) | (((x >> 20) & 1) << 11) |
                                    (((x >> 21) & 0x3ff) << 1), 21), 'jal')
    if op == 0x67:
        return ('jalr', rd, rs1, 0, ii, 'jalr')
    if op == 0x63:
        return ('br', 0, rs1, rs2, sx((((x >> 31) & 1) << 12) | (((x >> 7) & 1) << 11) | (((x >> 25) & 0x3f) << 5) |
                                     (((x >> 8) & 0xf) << 1), 13),
                ('beq', 'bne', 'b?', 'b?', 'blt', 'bge', 'bltu', 'bgeu')[f3])
    if op == 0x03:
        return ('ld', rd, rs1, 0, ii, ('lb', 'lh', 'lw', 'ld', 'lbu', 'lhu', 'lwu', 'l?')[f3])
    if op == 0x07:
        return ('fld', 32 + rd, rs1, 0, ii, {2: 'flw', 3: 'fld'}.get(f3, 'fl?'))
    if op == 0x23:
        return ('st', 0, rs1, rs2, sx((f7 << 5) | rd, 12), ('sb', 'sh', 'sw', 'sd', 's?', 's?', 's?', 's?')[f3])
    if op == 0x27:
        return ('fst', 0, rs1, 32 + rs2, sx((f7 << 5) | rd, 12), {2: 'fsw', 3: 'fsd'}.get(f3, 'fs?'))
    if op in (0x13, 0x1b):
        w = op == 0x1b
        if f3 == 0:
            nm = 'addiw' if w else ('mv' if ii == 0 else 'addi')
        elif f3 == 1:
            nm = 'slli'
        elif f3 == 5:
            nm = 'srai' if (x >> 30) & 1 else 'srli'
        else:
            nm = {2: 'slt', 3: 'slt', 4: 'xori', 6: 'ori', 7: 'andi'}[f3]
        imm = ii if f3 not in (1, 5) else (x >> 20) & 0x3f
        return ('opi', rd, rs1, 0, imm, nm + ('w' if w and f3 else ''))
    if op in (0x33, 0x3b):
        if f7 == 1:
            nm = ('mul', 'mulh', 'mulh', 'mulh', 'div', 'div', 'rem', 'rem')[f3]
        elif f7 == 0x10 and f3 in (2, 4, 6):
            nm = 'shadd%d' % (f3 >> 1)
        elif f7 == 4 and f3 == 0 and op == 0x3b:
            nm = 'add.uw'
        elif f7 in (0, 0x20):
            nm = {(0, 0): 'add', (0, 0x20): 'sub', (1, 0): 'sll', (2, 0): 'slt', (3, 0): 'slt', (4, 0): 'xor',
                  (5, 0): 'srl', (5, 0x20): 'sra', (6, 0): 'or', (7, 0): 'and'}.get((f3, f7), 'other')
        else:
            nm = 'other'
        return ('op', rd, rs1, rs2, 0, nm + ('w' if op == 0x3b and nm != 'add.uw' else ''))
    if op == 0x2f:
        f5 = x >> 27
        nm = {0: 'amoadd', 1: 'amoswap', 2: 'lr', 3: 'sc', 4: 'amoxor', 8: 'amoor', 12: 'amoand', 16: 'amomin',
              20: 'amomax', 24: 'amominu', 28: 'amomaxu'}.get(f5, 'amo?')
        return ('amo', rd, rs1, rs2, 0, nm + {2: '.w', 3: '.d'}.get(f3, '.?'))
    if op == 0x73:
        if x == 0xc0001073:
            return ('sys', 0, 0, 0, 0, 'unimp')                 # csrrw zero, cycle, zero: traps
        if f3 == 0:
            return ('sys', 0, 0, 0, 0, 'ecall' if x == 0x73 else 'sys')
        return ('csr', rd, rs1 if f3 < 4 else 0, 0, x >> 20, 'csr')
    if op == 0x53:
        f5 = f7 >> 2
        if f5 in (0x14, 0x18, 0x1c):
            return ('fp2x', rd, 32 + rs1, 32 + rs2, 0, 'fmv.x' if f5 == 0x1c and f3 == 0 else 'fp2x')
        if f5 in (0x1a, 0x1e):
            return ('x2fp', 32 + rd, rs1, 0, 0, 'fmv.f' if f5 == 0x1e else 'x2fp')
        return ('fop', 32 + rd, 32 + rs1, 32 + rs2, 0, 'fop')
    if op in (0x43, 0x47, 0x4b, 0x4f):
        return ('fop', 32 + rd, 32 + rs1, 32 + rs2, 0, 'fop')
    if op == 0x0f:
        return ('fence', 0, 0, 0, 0, 'fence')
    return ('other', rd, 0, 0, 0, 'op%#x' % op)


def dec16(x):
    q, f3 = x & 3, (x >> 13) & 7
    r3 = lambda b: 8 + ((x >> b) & 7)
    rd, rs2 = (x >> 7) & 31, (x >> 2) & 31
    i6 = sx((((x >> 12) & 1) << 5) | ((x >> 2) & 31), 6)
    if q == 0:
        if f3 == 0:
            imm = (((x >> 7) & 0xf) << 6) | (((x >> 11) & 3) << 4) | (((x >> 5) & 1) << 3) | (((x >> 6) & 1) << 2)
            return ('opi', r3(2), 2, 0, imm, 'addi')
        ld = (((x >> 10) & 7) << 3) | (((x >> 5) & 3) << 6)
        lw = (((x >> 10) & 7) << 3) | (((x >> 6) & 1) << 2) | (((x >> 5) & 1) << 6)
        return {1: ('fld', 32 + r3(2), r3(7), 0, ld, 'c.fld'), 2: ('ld', r3(2), r3(7), 0, lw, 'c.lw'),
                3: ('ld', r3(2), r3(7), 0, ld, 'c.ld'), 5: ('fst', 0, r3(7), 32 + r3(2), ld, 'c.fsd'),
                6: ('st', 0, r3(7), r3(2), lw, 'c.sw'), 7: ('st', 0, r3(7), r3(2), ld, 'c.sd')}.get(
                    f3, ('other', 0, 0, 0, 0, 'c.q0'))
    if q == 1:
        if f3 == 0:
            return ('opi', rd, rd, 0, i6, 'addi' if i6 else 'mv')
        if f3 == 1:
            return ('opi', rd, rd, 0, i6, 'addiw')
        if f3 == 2:
            return ('opi', rd, 0, 0, i6, 'addi')                          # c.li: built from x0
        if f3 == 3:
            if rd == 2:
                imm = sx((((x >> 12) & 1) << 9) | (((x >> 3) & 3) << 7) | (((x >> 5) & 1) << 6) |
                         (((x >> 2) & 1) << 5) | (((x >> 6) & 1) << 4), 10)
                return ('opi', 2, 2, 0, imm, 'addi')
            return ('c.lui', rd, 0, 0, i6 << 12, 'c.lui')
        if f3 == 4:
            f2 = (x >> 10) & 3
            sh = (((x >> 12) & 1) << 5) | ((x >> 2) & 31)
            if f2 == 0:
                return ('opi', r3(7), r3(7), 0, sh, 'srli')
            if f2 == 1:
                return ('opi', r3(7), r3(7), 0, sh, 'srai')
            if f2 == 2:
                return ('opi', r3(7), r3(7), 0, i6, 'andi')
            nm = (('sub', 'xor', 'or', 'and'), ('subw', 'addw', 'other', 'other'))[(x >> 12) & 1][(x >> 5) & 3]
            return ('op', r3(7), r3(7), r3(2), 0, nm)
        if f3 == 5:
            imm = sx((((x >> 12) & 1) << 11) | (((x >> 11) & 1) << 4) | (((x >> 9) & 3) << 8) | (((x >> 8) & 1) << 10) |
                     (((x >> 7) & 1) << 6) | (((x >> 6) & 1) << 7) | (((x >> 3) & 7) << 1) | (((x >> 2) & 1) << 5), 12)
            return ('jal', 0, 0, 0, imm, 'c.j')
        imm = sx((((x >> 12) & 1) << 8) | (((x >> 10) & 3) << 3) | (((x >> 5) & 3) << 6) | (((x >> 3) & 3) << 1) |
                 (((x >> 2) & 1) << 5), 9)
        return ('br', 0, r3(7), 0, imm, 'beq' if f3 == 6 else 'bne')
    if f3 == 0:
        return ('opi', rd, rd, 0, (((x >> 12) & 1) << 5) | ((x >> 2) & 31), 'slli')
    lsp = (((x >> 12) & 1) << 5) | (((x >> 5) & 3) << 3) | (((x >> 2) & 7) << 6)
    wsp = (((x >> 12) & 1) << 5) | (((x >> 4) & 7) << 2) | (((x >> 2) & 3) << 6)
    ssd = (((x >> 10) & 7) << 3) | (((x >> 7) & 7) << 6)
    ssw = (((x >> 9) & 0xf) << 2) | (((x >> 7) & 3) << 6)
    if f3 == 1:
        return ('fld', 32 + rd, 2, 0, lsp, 'c.fldsp')
    if f3 == 2:
        return ('ld', rd, 2, 0, wsp, 'c.lwsp')
    if f3 == 3:
        return ('ld', rd, 2, 0, lsp, 'c.ldsp')
    if f3 == 4:
        if not (x >> 12) & 1:
            return ('jalr', 0, rd, 0, 0, 'c.jr') if rs2 == 0 else ('opi', rd, rs2, 0, 0, 'mv')
        if rs2 == 0:
            return ('sys', 0, 0, 0, 0, 'c.ebreak') if rd == 0 else ('jalr', 1, rd, 0, 0, 'c.jalr')
        return ('op', rd, rd, rs2, 0, 'add')
    if f3 == 5:
        return ('fst', 0, 2, 32 + rs2, ssd, 'c.fsdsp')
    if f3 == 6:
        return ('st', 0, 2, rs2, ssw, 'c.swsp')
    return ('st', 0, 2, rs2, ssd, 'c.sdsp')


def isret(d):
    return d[0] == 'jalr' and d[1] == 0 and d[2] == 1 and d[4] == 0


def load_kit(kit):
    sums = open(os.path.join(kit, 'SHA256SUMS'), 'rb').read()
    kid = hashlib.sha256(sums).hexdigest()[:12]
    if kid != '86da41d3ef68':
        raise SystemExit('failopen.py: kit id %s, want 86da41d3ef68' % kid)
    for line in sums.decode().splitlines():
        h, f = line.split()
        if hashlib.sha256(open(os.path.join(kit, f), 'rb').read()).hexdigest() != h:
            raise SystemExit('failopen.py: %s does not match SHA256SUMS' % f)
    sp = importlib.util.spec_from_file_location('strictcmp3', os.path.join(kit, 'strictcmp3.py'))
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m, kid


class Image:
    """the sized FUNC and OBJECT symbols, the allocated sections and the file bytes of one image"""

    def __init__(self, path):
        self.path, self.name = path, os.path.basename(path).replace('.debug', '')
        e = ELFFile(open(path, 'rb'))
        syms = [y for y in e.get_section_by_name('.symtab').iter_symbols()
                if y['st_shndx'] not in ('SHN_UNDEF', 'SHN_ABS')]
        self.funcs = sorted((y['st_value'], y['st_size'], y.name) for y in syms
                            if y['st_info']['type'] == 'STT_FUNC' and y['st_size'] > 0)
        self.fstarts = [f[0] for f in self.funcs]
        self.objs = sorted((y['st_value'], y['st_size'], y.name) for y in syms
                           if y['st_info']['type'] in ('STT_OBJECT', 'STT_FUNC', 'STT_TLS', 'STT_NOTYPE') and y.name
                           and not y.name.startswith('$'))
        self.ostarts = [o[0] for o in self.objs]
        self.noret = frozenset(v for v, z, n in self.funcs if n in NORET or n.startswith('__asan_report_') and
                               not n.endswith('_noabort') or n.startswith('__ubsan_handle_') and n.endswith('_abort'))
        self.secs = [(s['sh_addr'], s['sh_size'], s.name, s['sh_flags'], s['sh_type'])
                     for s in e.iter_sections() if s['sh_flags'] & 2 and s['sh_size']]
        self.segs = [(g['p_vaddr'], g['p_filesz'], g.data()) for g in e.iter_segments() if g['p_type'] == 'PT_LOAD']

    def func_at(self, a):
        i = bisect.bisect_right(self.fstarts, a) - 1
        while i >= 0 and a - self.funcs[i][0] < (1 << 20):
            v, z, n = self.funcs[i]
            if v <= a < v + z:
                return (v, z, n)
            i -= 1
        return None

    def sec(self, a):
        return next((s for s in self.secs if s[0] <= a < s[0] + s[1]), None)

    def rd(self, a, n):
        return next((d[a - v:a - v + n] for v, fz, d in self.segs if v <= a and a + n <= v + fz), None)

    def name_of(self, a):
        """section, then the symbol that holds a (sized), else the nearest symbol at or below a in that section"""
        s = self.sec(a)
        if s is None:
            return 'no section'
        i = bisect.bisect_right(self.ostarts, a) - 1
        best = None
        while i >= 0 and self.objs[i][0] >= s[0]:
            v, z, n = self.objs[i]
            if v <= a < v + max(z, 1):
                return '%s %s+%#x' % (s[2], n, a - v)
            if best is None:
                best = (v, n)
            i -= 1
        if best:
            return '%s (unsized) %s+%#x' % (s[2], best[1], a - best[0])
        return '%s+%#x (no symbol)' % (s[2], a - s[0])

    def pool_value(self, a, nbytes):
        """the constant at a when a lies in a non-writable or RELRO section (else None)"""
        s = self.sec(a)
        if s is None or s[4] == 'SHT_NOBITS':
            return None
        if s[3] & 1 and s[2] not in ('.got', '.data.rel.ro', '.init_array', '.fini_array', '.preinit_array'):
            return None
        b = self.rd(a, nbytes)
        return None if b is None else int.from_bytes(b, 'little')


# ---- the dataflow over one function
FLOOR = 0x10000      # the lowest PT_LOAD address of every image: a value below it in magnitude names nothing mapped
WIDEN = 8            # more exact values than this for one (origin, shapes) group at one place: the value is unknown
LW = {'lb': (1, 1), 'lbu': (1, 0), 'lh': (2, 1), 'lhu': (2, 0), 'lw': (4, 1), 'lwu': (4, 0), 'ld': (8, 0),
      'c.lw': (4, 1), 'c.lwsp': (4, 1), 'c.ld': (8, 0), 'c.ldsp': (8, 0), 'flw': (4, 0), 'fld': (8, 0),
      'c.fld': (8, 0), 'c.fldsp': (8, 0)}
SW = {'sb': 1, 'sh': 2, 'sw': 4, 'sd': 8, 'c.sw': 4, 'c.swsp': 4, 'c.sd': 8, 'c.sdsp': 8, 'fsw': 4, 'fsd': 8,
      'c.fsd': 8, 'c.fsdsp': 8}


def big(v):
    return isinstance(v, int) and abs(sx(v, 64)) >= FLOOR


def overlap(c, cw, k, kw):
    """do the bytes [c, c + cw) and [k, k + kw) meet (64-bit offsets)"""
    d = sx((k - c) & M64, 64)
    return -kw < d < cw


def opi_val(nm, a, imm):
    """the exact result of an OP-IMM word on the 64-bit value a (None: not computed)"""
    f = {'mv': lambda: a, 'addi': lambda: a + imm, 'addiw': lambda: sx(a + imm, 32), 'slli': lambda: a << imm,
         'srli': lambda: a >> imm, 'srai': lambda: sx(a, 64) >> imm, 'xori': lambda: a ^ imm, 'ori': lambda: a | imm,
         'andi': lambda: a & imm, 'slliw': lambda: sx(a << imm, 32), 'srliw': lambda: sx((a & 0xffffffff) >> imm, 32),
         'sraiw': lambda: sx(sx(a, 32) >> imm, 32)}.get(nm)
    return None if f is None else f() & M64


def op_val(nm, a, b):
    """the exact result of an R-type word on the 64-bit values a, b (None: not computed)"""
    w = nm.endswith('w') and nm != 'add.uw'
    base = nm[:-1] if w else nm
    m = 31 if w else 63
    f = {'add': lambda: a + b, 'sub': lambda: a - b, 'xor': lambda: a ^ b, 'or': lambda: a | b, 'and': lambda: a & b,
         'sll': lambda: a << (b & m), 'srl': lambda: ((a & 0xffffffff) if w else a) >> (b & m),
         'sra': lambda: sx(a, 32 if w else 64) >> (b & m), 'mul': lambda: a * b, 'add.uw': lambda: (a & 0xffffffff) + b,
         'shadd1': lambda: (a << 1) + b, 'shadd2': lambda: (a << 2) + b, 'shadd3': lambda: (a << 3) + b}.get(base)
    if f is None:
        return None
    v = f() & M64
    return sx(v, 32) & M64 if w else v


def analyse(img, words, fa, noret=frozenset()):
    """words: [(offset, word, nbytes)]; fa: the function address. Returns the base sites that carry a constant
    origin, the address-like constants stored where no stack slot is known, and counts. noret: the addresses of the
    functions that do not return; a call to one has no edge to the next word.

    A token is (origin word index, frozenset of shapes, value): value is the exact 64-bit value the register holds on
    the paths that carry the token, 'dyn' once the constant has been combined with a value that is not a constant, or
    'unk' when the exact value is not kept (more than WIDEN values at one place, a partial reload, an FP conversion, a
    CSR read). The shape 'big' marks a token whose exact value had magnitude >= FLOOR at some point."""
    n = len(words)
    D = [dec(x, nb) for (o, x, nb) in words]
    off2i = {o: i for i, (o, x, nb) in enumerate(words)}
    EMPTY = frozenset()
    TOP = None
    incall, after_call, succ = set(), [], [[] for _ in range(n)]
    for i, d in enumerate(D):
        k, o = d[0], words[i][0]
        nxt = [(i + 1, '')] if i + 1 < n else []
        if k == 'jal':
            t = off2i.get(o + d[4])
            if d[1] and t is not None:
                succ[i].append((t, 'callee'))
                incall.add(i)
                if i + 1 < n:
                    after_call.append(i + 1)
            elif d[1] and (fa + o + d[4]) & M64 not in noret:
                succ[i] += nxt
            elif t is not None:
                succ[i].append((t, ''))
        elif k == 'br':
            t = off2i.get(o + d[4])
            if t is not None:
                succ[i].append((t, 'taken'))
            succ[i] += [(j, 'fall') for j, _ in nxt]
        elif k == 'jalr':
            if d[1]:
                succ[i] += nxt
            elif not isret(d):
                succ[i] += [(t, 'jt') for t in range(n)]       # dropped in flow() for a proven tail call
        elif d[5] != 'unimp':
            succ[i] += nxt

    def tok(oi, ft, v):
        if isinstance(v, int):
            v &= M64
            if big(v):
                ft = ft | {'big'}
        return (oi, frozenset(ft), v)

    def feat(ft, f):
        return ft | {f, f + '2'} if f in ('addi', 'addiw') and f in ft else ft | {f}

    def step(i, st):
        taint, lin = st
        T, L = dict(taint), dict(lin)
        k, rd, r1, r2, imm, nm = D[i]
        o = words[i][0]
        g = lambda r: taint.get(r, EMPTY) if r else EMPTY
        l = lambda r: (None, 0) if r == 0 else lin.get(r, TOP)
        fresh = lambda r: (('d', i, r), 0)

        def setr(r, t, lv):
            if r == 0:
                return
            if t:
                T[r] = frozenset(t)
            else:
                T.pop(r, None)
            if lv is TOP:
                L.pop(r, None)
            else:
                L[r] = lv

        def cell(b, off):
            if b is TOP or b[0] is None:
                return None if b is TOP else ('M', None, (b[1] + off) & M64)
            return ('S' if b[0] == ('e', 2) else 'M', b[0], (b[1] + off) & M64)
        if k in ('lui', 'c.lui'):
            setr(rd, [tok(i, EMPTY, imm)], (None, imm & M64))
        elif k == 'auipc':
            v = (fa + o + imm) & M64
            setr(rd, [tok(i, EMPTY, v)], (None, v))
        elif k == 'opi':
            if r1 == 0:
                v = opi_val(nm, 0, imm)
                setr(rd, [tok(i, EMPTY, 'unk' if v is None else v)], TOP if v is None else (None, v))
            else:
                out = []
                for oi, ft, v in g(r1):
                    nv = (opi_val(nm, v, imm) if isinstance(v, int) else v)
                    out.append(tok(oi, feat(ft, nm), 'unk' if nv is None else nv))
                b = l(r1)
                if b is not TOP and nm in ('mv', 'addi'):
                    lv = (b[0], (b[1] + imm) & M64)
                elif b is not TOP and b[0] is None and opi_val(nm, b[1], imm) is not None:
                    lv = (None, opi_val(nm, b[1], imm))
                else:
                    lv = fresh(rd)
                setr(rd, out, lv)
        elif k == 'op':
            base = 'shadd' if nm.startswith('shadd') else nm[:-1] if nm.endswith('w') else nm
            a, b = l(r1), l(r2)
            out = set()
            for mine, other, ol, first in ((g(r1), g(r2), b, True), (g(r2), g(r1), a, False)):
                partners = [ol[1]] if ol is not TOP and ol[0] is None else \
                    [v for oi, ft, v in other if isinstance(v, int)] + ['dyn']
                for oi, ft, v in mine:
                    for pv in partners:
                        if isinstance(v, int) and isinstance(pv, int):
                            nv = op_val(nm, v, pv) if first else op_val(nm, pv, v)
                            nv = 'unk' if nv is None else nv
                        else:                         # combined with a value that may be dynamic: its addend / mask
                            nv = 'unk' if v == 'unk' and pv != 'dyn' else 'dyn'
                        out.add(tok(oi, feat(ft, base), nv))
            lv = fresh(rd)
            if a is not TOP and b is not TOP:
                if a[0] is None and b[0] is None and op_val(nm, a[1], b[1]) is not None:
                    lv = (None, op_val(nm, a[1], b[1]))
                elif nm == 'add':
                    lv = (b[0], (a[1] + b[1]) & M64) if a[0] is None else \
                        (a[0], (a[1] + b[1]) & M64) if b[0] is None else (('d', i, rd), (a[1] + b[1]) & M64)
                elif nm == 'sub':
                    lv = (a[0], (a[1] - b[1]) & M64) if b[0] is None else \
                        (None, (a[1] - b[1]) & M64) if a[0] == b[0] and a[0][0] == 'e' else \
                        (('d', i, rd), (a[1] - b[1]) & M64)
                elif nm.startswith('shadd'):
                    lv = (b[0], ((a[1] << int(nm[5])) + b[1]) & M64) if a[0] is None else (('d', i, rd), b[1])
            setr(rd, out, lv)
        elif k in ('ld', 'fld'):
            wl, sgn = LW.get(nm, (8, 0))
            b = l(r1)
            out, lv = [], (fresh(rd) if k == 'ld' else TOP)
            key = cell(b, imm)
            pv = img.pool_value(key[2], wl) if key is not None and key[1] is None and k == 'ld' else None
            if pv is not None:
                pv = sx(pv, 8 * wl) & M64 if sgn else pv
                out, lv = [tok(i, EMPTY, pv)], (None, pv)
            elif key is not None:
                shape = 'spill' if key[0] == 'S' else 'mem'
                for c, ts in taint.items():
                    if not (isinstance(c, tuple) and len(c) == 3 and c[:2] == key[:2]):
                        continue
                    for oi, ft, (sv, ws) in ts:
                        if c == key and wl <= ws and isinstance(sv, int):
                            v = sv & ((1 << (8 * wl)) - 1)
                            out.append(tok(oi, feat(ft, shape), sx(v, 8 * wl) & M64 if sgn else v))
                        elif overlap(c[2], ws, key[2], wl):
                            out.append(tok(oi, feat(ft, shape), 'dyn' if sv == 'dyn' else 'unk'))
                if key[1] is None:
                    lv = (('w', key[2]), 0)                     # the contents of a writable word at a fixed address
                elif wl == 8 and key in lin:
                    lv = lin[key]
            setr(rd, out, lv)
        elif k in ('st', 'fst'):
            ws = SW.get(nm, 8)
            key = cell(l(r1), imm)
            if key is not None:
                for c in [c for c in T if isinstance(c, tuple) and len(c) == 3 and c[:2] == key[:2]]:
                    # bytes this store overwrites: a value stored there before keeps its token, value unknown;
                    # a value at the same place no wider than this store is gone
                    T[c] = frozenset((oi, ft, ('unk' if isinstance(sv, int) else sv, w)) if overlap(c[2], w, key[2], ws)
                                     else (oi, ft, (sv, w)) for oi, ft, (sv, w) in T[c]
                                     if not (c == key and w <= ws))
                    if not T[c]:
                        del T[c]
                ts = frozenset((oi, ft, (v & ((1 << (8 * ws)) - 1) if isinstance(v, int) else v, ws))
                               for oi, ft, v in g(r2))
                if ts:
                    T[key] = T.get(key, EMPTY) | ts
                if ws == 8 and k == 'st' and l(r2) is not TOP:
                    L[key] = l(r2)
                else:
                    L.pop(key, None)
        elif k in ('jal', 'jalr'):
            if rd and i not in incall:
                for r in CALLER + FCALLER:
                    T.pop(r, None)
                    L.pop(r, None)
                L[rd], L[10], L[11] = fresh(rd), fresh(10), fresh(11)
            elif rd:
                setr(rd, EMPTY, fresh(rd))
        elif k == 'amo':
            setr(rd, EMPTY, fresh(rd))
        elif k == 'csr':
            key = ('C', imm)
            out = [tok(oi, feat(ft, 'csr'), 'unk') for oi, ft, v in taint.get(key, EMPTY)]
            if r1:
                T[key] = taint.get(key, EMPTY) | g(r1)
            setr(rd, out, fresh(rd))
        elif k == 'sys':
            if nm == 'ecall':
                setr(10, EMPTY, fresh(10))
                setr(11, EMPTY, fresh(11))
        elif k in ('fp2x', 'x2fp', 'fop'):
            keep = nm in ('fmv.x', 'fmv.f')
            out = [tok(oi, feat(ft, 'fp'), v if keep else 'unk') for oi, ft, v in g(r1) | g(r2)]
            setr(rd, out, fresh(rd) if k == 'fp2x' else TOP)
        elif k == 'other' and rd:
            setr(rd, EMPTY, fresh(rd))
        T.pop(0, None)
        L.pop(0, None)
        for key, ts in list(T.items()):                 # widening: too many exact values in one group -> unknown
            cellk = isinstance(key, tuple) and len(key) == 3
            exact = (lambda v: isinstance(v[0], int)) if cellk else (lambda v: isinstance(v, int))
            grp = collections.Counter((oi, ft) for oi, ft, v in ts if exact(v))
            if any(c > WIDEN for c in grp.values()):
                T[key] = frozenset((oi, ft, ('unk', v[1]) if cellk else 'unk') if exact(v) and grp[(oi, ft)] > WIDEN
                                   else (oi, ft, v) for oi, ft, v in ts)
        return (T, L)

    def refine(i, kind, st):
        """a branch against x0: on the edge where the register is 0 a token whose exact value is not 0 cannot be in
        it, and on the other edge a token whose exact value is 0 cannot"""
        k, rd, r1, r2, imm, nm = D[i]
        if kind not in ('taken', 'fall') or nm not in ('beq', 'bne') or (r1 and r2):
            return st
        r = r1 or r2
        zero = (nm == 'beq') == (kind == 'taken')
        T = dict(st[0])
        if r in T:
            T[r] = frozenset(t for t in T[r] if not isinstance(t[2], int) or (t[2] == 0) == zero)
            if not T[r]:
                del T[r]
        return (T, st[1])

    tail = {}

    def flow(IN, work):
        while work:
            i = work.pop()
            out = step(i, IN[i])
            targets = list(succ[i])
            if D[i][0] == 'jalr' and not D[i][1] and not isret(D[i]):
                lt, ls = IN[i][1].get(D[i][2]), IN[i][1].get(2)
                tail[i] = lt is not None and lt[0] is not None and lt[0][0] == 'w' and ls == (('e', 2), 0)
                if tail[i]:                               # sp is back at its entry value and the target is the
                    targets = []                          # contents of a writable word: a tail call, no successor
            if isret(D[i]):
                targets += [(j, 'callee') for j in after_call]
            for t, kind in targets:
                ot, ol = refine(i, kind, out)
                if kind in ('jt', 'callee'):
                    ot = {r: frozenset((oi, feat(ft, kind), v) for oi, ft, v in ts) for r, ts in ot.items()}
                if IN[t] is None:
                    new = (ot, ol)
                else:
                    nt = dict(IN[t][0])
                    for r, v in ot.items():
                        nt[r] = nt.get(r, EMPTY) | v
                    new = (nt, {r: v for r, v in IN[t][1].items() if ol.get(r) == v})
                if IN[t] is None or new != IN[t]:
                    IN[t] = new
                    work.append(t)

    IN = [None] * n
    IN[0] = ({}, {r: (('e', r), 0) for r in range(1, 32)})
    flow(IN, [0])
    roots = 0
    for i in range(n):                     # a word no decoded edge reaches starts with no carried value
        if IN[i] is None:
            IN[i] = ({}, {})
            roots += 1
            flow(IN, [i])

    def okind(oi):
        return {'opi': 'x0', 'ld': 'pool'}.get(D[oi][0], D[oi][0])
    alike = lambda ft, v: 'big' in ft or v == 'unk'
    sites, small, escapes = [], [], []
    for i in range(n):
        k, rd, r1, r2, imm, nm = D[i]
        taint, lin = IN[i]
        if k in ('ld', 'fld', 'st', 'fst', 'jalr', 'amo') and r1:
            keep = [(oi, okind(oi), ft, v) for oi, ft, v in taint.get(r1, ())
                    if not (okind(oi) == 'auipc' and ft - {'big'} <= {'mv', 'addi'})]   # auipc [+ addi]: kit-paired
            if keep:
                b = lin.get(r1, TOP)
                flag = any(alike(ft, v) for oi, ok, ft, v in keep) or (b is not TOP and b[0] is None)
                (sites if flag else small).append((i, D[i], keep, b))
        if k in ('st', 'fst') and r2:
            b = lin.get(r1, TOP)
            if b is TOP or b[0] != ('e', 2):
                t = [(oi, okind(oi), ft, v) for oi, ft, v in taint.get(r2, ()) if alike(ft, v)]
                if t:
                    escapes.append((i, D[i], t, b))
    return dict(D=D, sites=sites, small=small, escapes=escapes, n=n, tail=sorted(i for i in tail if tail[i]),
                comp=sum(1 for w in words if w[2] == 2), clui=sum(1 for d in D if d[0] == 'c.lui'),
                jt=sum(1 for d in D if d[0] == 'jalr' and not d[1] and not isret(d)), callee=len(incall), roots=roots)


def shape_of(ok, ft):
    """the fail-open shapes of the kit's list that one token went through"""
    s = []
    if ok == 'c.lui':
        s.append('c.lui')
    if ok in ('x0', 'pool'):
        s.append('without-lui(%s)' % ok)
    if ok == 'auipc':
        s.append('auipc-pair(not-in-list)')
    for f, nm in (('spill', 'spill'), ('fp', 'fp-move'), ('csr', 'csr'), ('jt', 'jump-table'), ('callee', 'callee'),
                  ('mem', 'memory')):
        if f in ft:
            s.append(nm)
    if ft & {'ori', 'xori', 'slli', 'andi', 'srli', 'srai', 'slliw', 'srliw', 'sraiw'}:
        s.append('ori/xori/slli')
    if ft & {'add', 'sub', 'shadd', 'mul', 'slt', 'xor', 'or', 'and', 'sll', 'srl', 'sra', 'add.uw', 'other', 'mulh',
             'div', 'rem'}:
        s.append('combined')
    if ft & {'addi2', 'addiw2'}:
        s.append('addi-chain')
    elif ft & {'addi', 'addiw'}:
        s.append('addi')
    if not s or s in (['without-lui(%s)' % ok], ['c.lui'], ['auipc-pair(not-in-list)']):
        s.append('immediate')
    return s


# ---- the claims of claims.tsv whose kit verdict is EQUAL* (any EQUAL variant) and whose settled verdict is 'same', and
# the compare rows (output file, row label, pair) each one cites
G1, G2R, G2P, G2PR = 'g1-strcmp-grant.cmp.tsv', 'g2-rt.cmp.tsv', 'g2-prog.cmp.tsv', 'g2-prog-ranges.kitrange.tsv'
G2S, G2V = 'g2-answer-settle.kitrange.tsv', 'g2-verbs-receive.kitrange.tsv'
G3, G4 = 'g3-sm3-disco.cmp.tsv', 'g4-cgif.cmp.tsv'
G5, G9 = 'g5-printf-common.cmp.tsv', 'g9-memchr.cmp.tsv'
PF = '_ZL13printf_commonPvPKcS_'
SIX = ['___interceptor_strcmp', '__interceptor_trampoline_strcmp', '__sanitizer_weak_hook_strcmp',
       '_ZN6__asan18TryAsanInitFromRtlEv', '__asan_region_is_poisoned', '_ZN11__sanitizer11mem_is_zeroEPKcm']
SM3 = ['__asan_stack_malloc_3', '_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE',
       '___interceptor___tls_get_addr', '__tls_get_addr', '_ZN6__asan16GetCurrentThreadEv', '_ZN6__asan10AsanTSDGetEv',
       '__pthread_getspecific', '_ZN11__sanitizer20DTLS_on_tls_get_addrEPvS0_mm',
       '_ZN6__asanL11MemToShadowEm{asan_fake_stack.cpp}']
MCP = ['__asan_memcpy', '__asan_region_is_poisoned', 'memcpy']
MST = ['__asan_memset', '__asan_region_is_poisoned', 'memset']


def rows(f, names, *prs):
    return [(f, n, pr) for pr in prs for n in names]


CLAIMS = {}
for _c, _r in ((('C03', 'C04'), rows(G5, [PF], 'R:A')),
               (('C05',), rows(G4, MCP, 'C:A')), (('C06',), rows(G4, MST, 'C:A')),
               (('C07', 'C52'), rows(G3, SM3, 'D:A')),
               (('C08', 'C14', 'C16', 'C58', 'C67', 'C70'), rows(G1, SIX[:1], 'G:A')),
               (('C09', 'C11', 'C13', 'C15'), rows(G1, SIX, 'G:A')),
               (('C10', 'C12', 'C61', 'C64'), rows(G1, [SIX[0], SIX[4]], 'G:A')),
               (('C17',), rows(G4, [SIX[4]], 'C:A')), (('C19',), rows(G9, ['memchr'], 'B:A')),
               (('C20',), rows(G2PR, ['answer[entry..0x8ab6c]'], 'B:A') +
                rows(G2S, ['answer[entry..0x8ab6c]+consumer', 'answer[entry..0x8ab6c)excl'], 'B:A')),
               (('C21',), rows(G2PR, ['answer[0x8aca4..0x8ad2c]'], 'B:A')),
               (('C24',), rows(G2PR, ['number[0x8e0ac..0x8e124]'], 'B:A')),
               (('C25',), rows(G2P, ['rec_clear'], 'B:A')), (('C27', 'C28'), rows(G2P, ['rec_code_declared'], 'B:A')),
               (('C29', 'C30', 'C31'), rows(G2P, ['rec_shape_of'], 'B:A')), (('C32',), rows(G2P, ['reply'], 'B:A')),
               (('C37',), rows(G2P, ['verb_is'], 'B:A')),
               (('C38',), rows(G2V, ['verbs_receive[+0..+0x70) prologue, saves, side-stack call'], 'B:A')),
               (('C39', 'C40'), rows(G5, [PF], 'R:B', 'RB:B')),
               (('C41', 'C42'), rows(G2R, ['___interceptor_malloc'], 'B:A')),
               (('C43',), rows(G2R, ['_ZN11__sanitizer18BufferedStackTrace10UnwindImplEmmPvbj',
                                     '_ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj'], 'B:A')),
               (('C44',), rows(G2R, ['___interceptor_strdup'], 'B:A')), (('C45',), rows(G2R, ['memcpy'], 'B:A')),
               (('C46', 'C47', 'C48'),
                rows(G2R, ['___interceptor_strndup', '__interceptor_trampoline_strndup'], 'B:A')),
               (('C49',), rows(G2R, MCP, 'B:A')), (('C50', 'C51'), rows(G2R, MST, 'B:A')),
               (('C53', 'C54', 'C55'),
                rows(G2R, ['___interceptor_strcspn', '__interceptor_trampoline_strcspn'], 'B:A')),
               (('C56',), rows(G2R, ['strcspn'], 'B:A')), (('C57',), rows(G2R, ['strtok_r'], 'B:A')),
               (('C59', 'C68', 'C71'), rows(G2R, SIX[:4], 'B:A')),
               (('C60', 'C63', 'C66', 'C69'), rows(G1, SIX, 'G:B')),
               (('C62', 'C65'), rows(G2R, [SIX[0], SIX[4]], 'B:A')),
               (('C72',), rows(G4, [SIX[4]], 'C:B', 'CB:B'))):
    for _k in _c:
        CLAIMS[_k] = _r
# not EQUAL*: the kit verdict is DIFFERENT or SIZE and the settled verdict is 'same as stated' (outside the migration)
OTHER = {'C01': rows(G2PR, ['sup_policy_set:sup_lv2_worker_set(A)'], 'A:A'),
         'C02': rows(G2PR, ['sup_reset:sup_quarantine_clear(A)'], 'A:A'),
         'C22': rows(G2PR, ['check_refusal[+0..+0xac)', 'check_refusal[B+0xb0..end|A+0xac..end]'], 'B:A'),
         'C23': rows(G2P, ['is_instance_verb'], 'B:A') + rows(G2PR, ['is_instance_verb'], 'B:A'),
         'C33': rows(G2PR, ['send_message[+0..+0x250)', 'send_message[B+0x254..end|A+0x250..end]'], 'B:A'),
         'C34': rows(G2PR, ['send_message[+0..+0x250)', 'send_message[B+0x254..end|A+0x250..end]'], 'B:A'),
         'C35': rows(G2PR, ['sup_quarantine_clear:sup_reset(B)'], 'B:B')}

ABI = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1'] + ['a%d' % i for i in range(8)] + \
      ['s%d' % i for i in range(2, 12)] + ['t%d' % i for i in range(3, 7)]


def rname(r):
    return ABI[r] if r < 32 else 'f%d' % (r - 32)


def text(d):
    k, rd, r1, r2, imm, nm = d
    h = '%#x' % imm if imm >= 0 else '-%#x' % -imm
    if k in ('ld', 'fld'):
        return '%s %s, %s(%s)' % (nm, rname(rd), h, rname(r1))
    if k in ('st', 'fst'):
        return '%s %s, %s(%s)' % (nm, rname(r2), h, rname(r1))
    if k == 'amo':
        if nm.startswith('lr.'):
            return '%s %s, (%s)' % (nm, rname(rd), rname(r1))
        return '%s %s, %s, (%s)' % (nm, rname(rd), rname(r2), rname(r1))
    if k == 'jalr':
        return 'jalr %s, %s(%s)' % (rname(rd), h, rname(r1))
    return nm


class Side:
    """the facts of one side of one site: the image, the function, the word, the carried tokens, the address form"""

    def __init__(self, img, fn, w, r, s):
        self.img, self.fn, self.w, self.r = img, fn, w, r
        self.i, self.d, self.keep, self.b = s
        self.off = w[self.i][0]
        self.addr = fn[0] + self.off

    def site(self):
        return '%#x (+%#x) %s' % (self.addr, self.off, text(self.d))

    def word(self, off):
        return text(self.r['D'][[j for j, (o, x, nb) in enumerate(self.w) if o == off][0]])

    def absolute(self):
        return None if self.b is None or self.b[0] is not None else (self.b[1] + self.d[4]) & M64

    def pair(self, oi):
        """the value of an auipc and the first OP-IMM word after it that reads its register (the kit's pair)"""
        D = self.r['D']
        v = (self.fn[0] + self.w[oi][0] + D[oi][4]) & M64
        j = next(j for j in range(oi + 1, len(D)) if D[j][0] == 'opi' and D[j][2] == D[oi][1])
        return (v + D[j][4]) & M64

    def slot(self, oi):
        """a pool load: (the auipc offset, the slot address, its section, the value in it)"""
        D = self.r['D']
        j = oi - 1
        while D[j][1] != D[oi][2]:
            j -= 1
        if D[j][0] != 'auipc':
            raise SystemExit('failopen.py: %s +%#x: the pool load is not an auipc pair' % (self.fn[2], self.w[oi][0]))
        a = (self.fn[0] + self.w[j][0] + D[j][4] + D[oi][4]) & M64
        return self.w[j][0], a, self.img.sec(a)[2], int.from_bytes(self.img.rd(a, 8), 'little')

    def name(self, a):
        s = self.img.name_of(a)
        sec, _, rest = s.partition(' ')
        return '%s in %s' % (rest, sec) if rest else s


def got_only(s):
    return s.absolute() is not None and len(s.keep) == 1 and s.keep[0][1] == 'pool' and \
        s.slot(s.keep[0][0])[2] == '.got'


def got_trace(s1, s2):
    t = []
    for s in (s1, s2):
        (oi, ok, ft, v), = s.keep
        au, a, sec, val = s.slot(oi)
        t.append((au, s.w[oi][0], a, val, s.name(s.absolute())))
    how = ('auipc +%#x and ld +%#x read the .got slot %#x | %#x, which holds %#x | %#x (image bytes); the base is that '
           'value plus %s on every path to the site (one exact value)' % (t[0][0], t[0][1], t[0][2], t[1][2], t[0][3],
                                                                          t[1][3], '%#x' % s1.d[4] if s1.d[4] >= 0
                                                                          else '-%#x' % -s1.d[4]))
    return 'built without lui (.got load); immediate', t[0][4], t[1][4], how, \
        'correspond' if t[0][4] == t[1][4] else 'TARGETS DIFFER'


# ---- the hand traces: every site that is not fed by one .got slot, keyed (row label, offset from the range start).
# Each entry was written after reading the two listings; the function gets the two Sides and gives (shape, target side
# 1, target side 2, how traced, verdict); the verdict compares the names the two sides give the target.
def h_amo(a, b):
    oi = next(oi for oi, ok, ft, v in a.keep if ok == 'auipc')
    oj = next(oi for oi, ok, ft, v in b.keep if ok == 'auipc')
    t = ['the word at %s (%#x, 4-aligned) for lr.w / sc.w; the lane mask 0xff0000 selects byte +2, %s'
         % (s.name(s.absolute()), s.absolute(), s.name(s.absolute() + 2)) for s in (a, b)]
    same = all(x.name(x.absolute()) == a.name(a.absolute()) and x.name(x.absolute() + 2) == a.name(a.absolute() + 2)
               and x.absolute() % 4 == 0 for x in (a, b))
    how = ('s0 = the auipc pair at +0xc / +0x10 = %#x | %#x, _ZN6__asanL11asan_initedE (the kit\'s pcrel target); a0 = '
           '(s0 + 2) & -4 (+0x34, +0x3c); asan_inited is 4-aligned in both images, so a0 = asan_inited+0; lr.w +0x44 / '
           'sc.w +0x58 on a0 with lane value 0x10000 and mask 0xff0000 (+0x38, +0x40) write byte +2'
           % (a.pair(oi), b.pair(oj)))
    return 'auipc pair (not in the list); addi chain; andi', t[0], t[1], how, 'correspond' if same else 'TARGETS DIFFER'


def _tbl(s, oi):
    t = s.pair(oi)
    return t, s.name(t)


def _at(name, step):
    """'g_shapes+0x0 in .data.rel.ro', '16k' -> 'g_shapes+16k in .data.rel.ro'"""
    sym, _, sec = name.partition(' in ')
    return '%s+%s in %s' % (sym[:-4] if sym.endswith('+0x0') else sym, step, sec)


def h_codes(kind):
    def f(a, b):
        (ta, na), (tb, nb) = (_tbl(s, next(oi for oi, ok, ft, v in s.keep if ok == 'auipc')) for s in (a, b))
        loop = ('a3 = a1 = the auipc pair at +0x14 / +0x18 = %#x | %#x (the kit\'s pcrel target, rec_codes, 288 bytes, '
                'in both); each pass adds 4 to a1 and a3 (+0x3c, +0x44) and a4 counts 0x3a passes (+0x1c, +0x40)'
                % (ta, tb))
        v = 'correspond' if na == nb == 'rec_codes+0x0 in .rodata' else 'TARGETS DIFFER'
        if kind == 'shadow':
            t = ('the ASan shadow byte of rec_codes+4k, k < 58 (shadow base: the value of '
                 '__asan_shadow_memory_dynamic_address); no image object')
            return ('auipc pair (not in the list); addi chain; srli; add', t, t,
                    loop + '; a5 = (a1 >> 3) + a2 (+0x24, +0x28), a2 = the shadow base loaded through the .got (+0x8 '
                    'to +0x10)', v)
        return ('auipc pair (not in the list); addi chain', '%s, k < 58 (%#x + 4k)' % (_at(na, '4k'), ta),
                '%s, k < 58 (%#x + 4k)' % (_at(nb, '4k'), tb), loop + '; lw +0x34 reads 0(a3)', v)
    return f


def h_shapes(kind):
    def f(a, b):
        (ta, na), (tb, nb) = (_tbl(s, [j for j, (o, x, n) in enumerate(s.w) if o == 0x44][0]) for s in (a, b))
        loop = ('s2 = the auipc pair at +0x44 / +0x4c = %#x | %#x (the kit\'s pcrel target, g_shapes, 544 bytes, in '
                'both), s6 = s2 + 8; each pass adds 16 to s2 and s6 and 2 to s8, and s5 steps by -2 to -0x38: '
                '28 passes '
                '(+0x5c, +0x64, +0x94 to +0xa4)' % (ta, tb))
        v = 'correspond' if na == nb == 'g_shapes+0x0 in .data.rel.ro' else 'TARGETS DIFFER'
        if kind == 'shadow0':
            t = 'the ASan shadow byte of g_shapes+16k, k < 28; no image object'
            return ('auipc pair (not in the list); addi chain; srli; add', t, t,
                    loop + '; s8 = (s2 >> 3) + s7 (+0x58, +0x60), s7 = the value of '
                    '__asan_shadow_memory_dynamic_address loaded through the .got (+0x3c, +0x40, +0x50)', v)
        if kind == 'entry0':
            return ('auipc pair (not in the list); addi chain', '%s, k < 28 (%#x + 16k)' % (_at(na, '16k'), ta),
                    '%s, k < 28 (%#x + 16k)' % (_at(nb, '16k'), tb),
                    loop + '; ld +0x70 reads -8(s6) = g_shapes + 16k', v)
        if kind == 'shadow8':
            t = 'the ASan shadow byte of g_shapes+8+16k, k < 28; no image object'
            return ('auipc pair (not in the list); addi; srli; add; sub', t, t,
                    'a0 = the auipc pair at +0xac / +0xb0 = g_shapes+8 (%#x | %#x); a0 = (a0 >> 3) + s7 - s5 (+0xb4 to '
                    '+0xbc), s5 = -2k from the loop above, s7 = the shadow base' % (
                        a.pair([j for j, (o, x, n) in enumerate(a.w) if o == 0xac][0]),
                        b.pair([j for j, (o, x, n) in enumerate(b.w) if o == 0xac][0])), v)
        return ('auipc pair (not in the list); addi chain', '%s, k < 28 (%#x + 8 + 16k)' % (_at(na, '8+16k'), ta),
                '%s, k < 28 (%#x + 8 + 16k)' % (_at(nb, '8+16k'), tb),
                loop + '; after the loop ld +0xc8 reads 0(s6) = g_shapes + 8 + 16k, the field of the entry found', v)
    return f


def h_printf(kind):
    def f(a, b):
        sl = []
        for s in (a, b):
            oi = next(oi for oi, ok, ft, v in s.keep if ok == 'pool')
            au, slot, sec, val = s.slot(oi)
            sl.append('%#x in %s = %#x' % (slot, sec, val))
        tgt = ('the ASan shadow word (andi -8) that holds the shadow byte of s6 + s7 - 1' if kind == 'word' else
               'the ASan shadow byte of s6 + s7 - 1') + \
            ' (s6: a string pointer read from the va_list, s7: its length); no image object'
        how = ('the only constant >= 0x10000 that reaches the base is the pattern word loaded by auipc +0xc8 / '
               'ld +0xe4 from %s | %s (the kit row\'s full-bytes acceptance full+0xe4, equal bytes); it fills the '
               'directive at s8 '
               '(sd +0x114 to +0x124, a stack slot) and the precision word lw -0x1c(s8) (+0x4b4, +0x4c4) bounds the '
               'length: s7 = n + (n < precision) (sltu +0x4c8, add +0x4cc); the address is (s6 + s7 - 1) >> 3 plus the '
               'shadow base from the .got (+0x544 to +0x564)%s' % (sl[0], sl[1], ', andi -8 at +0x56c' if kind == 'word'
                                                                  else ''))
        same = all(x.endswith('= 0xaaaaaaaaaaaaaaaa') and ' in .rodata ' in x for x in sl)
        return ('built without lui (constant-pool load); stack spill; slt; add; srli', tgt, tgt, how,
                'correspond' if same else 'TARGETS DIFFER')
    return f



# ---- hand traces for the sites of the 7 claims outside the rule (kit verdict DIFFERENT or SIZE)
def _gotv(s, ld):
    """the .got slot an auipc / ld pair at function offset ld reads: (auipc offset, slot, value, name of value)"""
    oi = [j for j, (o, x, n) in enumerate(s.w) if o == ld][0]
    au, slot, sec, val = s.slot(oi)
    return au, slot, val, s.name(val)


def h_gotshadow(ld, field, words, base):
    def f(a, b):
        ga, gb = _gotv(a, ld), _gotv(b, ld)
        ta, tb = ('the ASan shadow byte of %s (%#x)' % (_at(g[3], '%#x' % field), g[2] + field) for g in (ga, gb))
        how = ('V = the .got slot that auipc +%#x / ld +%#x read (%#x | %#x), which holds %#x | %#x; the base is '
               '(V + %#x) >> 3 plus %s (%s)' % (ga[0], ld, ga[1], gb[1], ga[2], gb[2], field, base, words))
        return '', ta, tb, how, 'correspond' if ga[3] == gb[3] else 'TARGETS DIFFER'
    return f


def h_ivverbs(kind):
    def f(a, b):
        (ta, na), (tb, nb) = (_tbl(s, [j for j, (o, x, n) in enumerate(s.w) if o == 0x50][0]) for s in (a, b))
        v = 'correspond' if na == nb == 'g_instance_verbs+0x0 in .data.rel.ro' else 'TARGETS DIFFER'
        loop = ('s5 = the auipc pair at +0x50 / +0x58 = %#x | %#x (the kit\'s pcrel target, g_instance_verbs, 192 '
                'bytes, in both); each pass adds 8 to s5 and 1 to s6 (+0xa0, +0xa4), and s4 steps by -8 to -0x90: 18 '
                'passes (+0x4c, +0x68, +0x9c, +0xa8)' % (ta, tb))
        if kind == 'shadow':
            t = 'the ASan shadow byte of g_instance_verbs+8k, k < 18; no image object'
            return '', t, t, loop + ('; s6 = (s5 >> 3) plus the shadow base (+0x60, +0x64), the value of '
                                     '__asan_shadow_memory_dynamic_address read through the .got (+0x28 to +0x30)'), v
        return '', '%s, k < 18 (%#x + 8k)' % (_at(na, '8k'), ta), '%s, k < 18 (%#x + 8k)' % (_at(nb, '8k'), tb), \
            loop + '; ld +0x74 reads 0(s5)', v
    return f


SUP = {'sup_reset:sup_quarantine_clear(A)': (
    0x24, 0x40, {0x7c: (1, '0'), 0x8c: (0, '0'), 0x98: (1, '4'), 0xa0: (0, '4'), 0xb8: (1, '4'), 0xc0: (0, '4'),
                 0xd0: (0, '4'), 0xe0: (1, '8+8m'), 0xe8: (0, '8+8m')},
    'n = lw 8(a1) (+0x2c); when n = 16 (+0x34, +0x3c) s0 = record.spill, else the word is stored back plus one and '
    's0 = g_rec + 56n + 0x10 (+0x58 to +0x70), n < 16, inside g_rec (1184 bytes); s2 = s0 + 4 (+0x88); m = lw 0(s2) '
    '(+0xc0), the argument count, written 0 at +0xa0; a1 = s0 + 8 + 8m (+0xc4, +0xcc, +0xd4); a shadow byte is '
    '(address >> 3) plus s3 (+0x74 to +0x78, +0x90 to +0x94, +0xd8 to +0xdc), s3 = the value of '
    '__asan_shadow_memory_dynamic_address read through the .got (+0x1c, +0x20, +0x30)'),
    'sup_policy_set:sup_lv2_worker_set(A)': (
    0x2c, 0x48, {0x84: (1, '0'), 0x94: (0, '0'), 0xa0: (1, '4'), 0xa8: (0, '4'), 0xc0: (1, '4'), 0xc8: (0, '4'),
                 0xd8: (0, '4'), 0xe8: (1, '8+8m'), 0xf4: (0, '8+8m'), 0x110: (1, '4'), 0x118: (0, '4'),
                 0x124: (0, '4'), 0x134: (1, '8+8m'), 0x13c: (0, '8+8m')},
    'n = lw 8(a1) (+0x34); when n = 16 (+0x3c, +0x44) s0 = record.spill, else the word is stored back plus one and '
    's0 = g_rec + 56n + 0x10 (+0x60 to +0x78), n < 16, inside g_rec (1184 bytes); s2 = s0 + 4 (+0x90); s3 = s0 + 8 '
    '(+0xcc); m = lw 0(s2), the argument count, written 0 at +0xa8 and read at +0xc8 and again at +0x118 (one more '
    'after +0xd8); a1 = s3 + 8m (+0xd4, +0xdc and +0x120, +0x128); a shadow byte is (address >> 3) plus s4 (+0x7c to '
    '+0x80, +0x98 to +0x9c, +0xe0 to +0xe4, +0x12c to +0x130), s4 = the value of __asan_shadow_memory_dynamic_address '
    'read through the .got (+0x24, +0x28, +0x38)')}


def h_sup(label):
    gp, spp, fields, rest = SUP[label]

    def f(a, b):
        sh, fld = fields[a.off]
        objs = []
        for s in (a, b):
            g = s.pair([j for j, (o, x, n) in enumerate(s.w) if o == gp][0])
            r = s.pair([j for j, (o, x, n) in enumerate(s.w) if o == spp][0])
            objs.append((g, s.name(g), r, s.name(r)))
        rec = 'R+%s, R = g_rec+0x10+56n (n < 16) or record.spill+0x0 (n = 16), in .bss' % fld
        t = ('the ASan shadow byte of ' + rec + '; no image object') if sh else rec
        how = ('a1 = the auipc pair at +%#x / +%#x = %#x | %#x, %s; record.spill = the auipc pair at +%#x / +%#x = '
               '%#x | %#x; ' % (gp, gp + 4, objs[0][0], objs[1][0], objs[0][1], spp, spp + 4, objs[0][2], objs[1][2])
               + rest)
        same = objs[0][1] == objs[1][1] == 'g_rec+0x0 in .bss' and objs[0][3] == objs[1][3] == \
            'record.spill+0x0 in .bss'
        return '', t, t, how, 'correspond' if same else 'TARGETS DIFFER'
    return f


HAND = {}
for _lab in ('_ZN6__asan18TryAsanInitFromRtlEv',):
    HAND[(_lab, 0x44)] = HAND[(_lab, 0x58)] = h_amo
HAND[('rec_code_declared', 0x2c)] = h_codes('shadow')
HAND[('rec_code_declared', 0x34)] = h_codes('entry')
HAND[('rec_shape_of', 0x68)] = h_shapes('shadow0')
HAND[('rec_shape_of', 0x70)] = h_shapes('entry0')
HAND[('rec_shape_of', 0xc0)] = h_shapes('shadow8')
HAND[('rec_shape_of', 0xc8)] = h_shapes('entry8')
HAND[(PF, 0x574)] = h_printf('word')
HAND[(PF, 0x580)] = h_printf('byte')
_CR = 'check_refusal[+0..+0xac)'
_CRW = ('the shadow base s1, the value of __asan_shadow_memory_dynamic_address read through the .got (+0x14, +0x18, '
        '+0x24)')
HAND[(_CR, 0x34)] = h_gotshadow(0x20, 0x3a0, 'addi +0x28, srli +0x2c, add +0x30', _CRW)
HAND[(_CR, 0x5c)] = h_gotshadow(0x20, 0x3b0, 'addi +0x50, srli +0x54, add +0x58', _CRW)
HAND[(_CR, 0x7c)] = h_gotshadow(0x70, 0, 'srli +0x74, add +0x78', _CRW)
HAND[('send_message[+0..+0x250)', 0x150)] = h_gotshadow(
    0x13c, 0, 'srli +0x148, add +0x14c', 'the shadow base s9, the value of __asan_shadow_memory_dynamic_address read '
    'through the .got (+0x44, +0x50, +0x58)')
HAND[('is_instance_verb', 0x6c)] = h_ivverbs('shadow')
HAND[('is_instance_verb', 0x74)] = h_ivverbs('entry')
for _lab, (_g, _sp, _fl, _r) in SUP.items():
    for _o in _fl:
        HAND[(_lab, _o)] = h_sup(_lab)


def read_outputs(outs, imgdir):
    """the compare rows of the record: (output file, row label, pair) -> ((image path, address), (image path, address),
    length or None for a whole function)"""
    tagfile, pairs = {}, {}
    for p in outs:
        local = {}
        for line in open(p):
            if line.startswith('# ') and ' = ' in line and ' sha256 ' in line:
                t, rest = line[2:].split(' = ', 1)
                local[t.strip()] = os.path.join(imgdir, os.path.basename(rest.split(' sha256 ')[0]))
            elif not line.startswith(('#', 'fn\t', 'label\t', 'CSTR')):
                f = line.rstrip('\n').split('\t')
                if len(f) < 6 or ':' not in f[1]:
                    continue
                try:
                    a1, a2 = int(f[2], 16), int(f[3], 16)
                except ValueError:
                    continue
                t1, t2 = f[1].split(':')
                ln = int(f[4], 16) if p.endswith('.kitrange.tsv') else None
                pairs[(os.path.basename(p), f[0], f[1])] = ((local[t1], a1), (local[t2], a2), ln)
        tagfile.update(local)
    return tagfile, pairs


def shapes_of(s):
    """the shapes of the tokens that make a site: the address-like ones, or all for an exact base"""
    ks = [(ok, ft) for oi, ok, ft, v in s.keep if 'big' in ft or v == 'unk'] or [(ok, ft) for oi, ok, ft, v in s.keep]
    return sorted({x for ok, ft in ks for x in shape_of(ok, ft)})


def main():
    kit, imgdir, outfile, outs = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
    s3, kid = load_kit(kit)
    me = hashlib.sha256(open(os.path.abspath(__file__), 'rb').read()).hexdigest()
    tagfile, pairs = read_outputs(outs, imgdir)
    for c, rs in list(CLAIMS.items()) + list(OTHER.items()):
        for k in rs:
            if k not in pairs:
                raise SystemExit('failopen.py: %s cites %s, which no compare output has' % (c, k))
    imgs = {p: Image(p) for p in sorted(set(tagfile.values()))}
    bodies = {}

    def body(p, a):
        fn = imgs[p].func_at(a)
        if fn is None:
            raise SystemExit('failopen.py: no function holds %#x in %s' % (a, p))
        if (p, fn[0]) not in bodies:
            b = imgs[p].rd(fn[0], fn[1])
            if b is None:
                raise SystemExit('failopen.py: %s+%#x is not file bytes' % (p, fn[0]))
            w = s3._bc['words'](b)
            bodies[(p, fn[0])] = (fn, w, analyse(imgs[p], w, fn[0], imgs[p].noret))
        return bodies[(p, fn[0])]

    def sites(key, strict=True):
        """the site pairs of one compare row inside its compared range: [(offset from the range start, Side, Side)]"""
        (p1, a1), (p2, a2), ln = pairs[key]
        b1, b2 = body(p1, a1), body(p2, a2)
        if ln is None and b1[0][1] != b2[0][1]:
            return None
        L = b1[0][1] if ln is None else ln
        got = []
        for (p, a), (fn, w, r) in (((p1, a1), b1), ((p2, a2), b2)):
            got.append({fn[0] + w[s[0]][0] - a: Side(imgs[p], fn, w, r, s) for s in r['sites']
                        if 0 <= fn[0] + w[s[0]][0] - a < L})
        if not strict:
            return sorted(set(got[0]) | set(got[1]))
        if set(got[0]) != set(got[1]):
            raise SystemExit('failopen.py: %s: the two sides have different sites' % (key,))
        return [(o, got[0][o], got[1][o]) for o in sorted(got[0])]
    for key, (s1, s2, ln) in pairs.items():
        body(*s1), body(*s2)
    used = set()

    def trace(group, skip=()):
        """the rows of every compare row the claims of group cite (rows in skip excluded)"""
        cited = collections.defaultdict(list)
        for c, rs in sorted(group.items()):
            for k in rs:
                if k not in skip:
                    cited[k].append(c)
        out, shapes, persite, luisites = [], collections.Counter(), set(), 0
        for key in sorted(cited):
            sp = sites(key)
            if sp is None:
                raise SystemExit('failopen.py: %s compares two sizes' % (key,))
            for o, a, b in sp:
                if got_only(a) and got_only(b):
                    sh, ta, tb, how, verdict = got_trace(a, b)
                else:
                    h = HAND.get((key[1], o))
                    if h is None:
                        raise SystemExit('failopen.py: %s +%#x has no hand trace' % (key, o))
                    used.add((key[1], o))
                    sh, ta, tb, how, verdict = h(a, b)
                sh = '; '.join(sorted(set(shapes_of(a)) | set(shapes_of(b))))       # both sides' shapes
                if verdict != 'correspond':
                    raise SystemExit('failopen.py: %s +%#x: %s | %s' % (key, o, ta, tb))
                for x in sh.split('; '):
                    shapes[x] += 1
                luisites += any(ok in ('lui', 'c.lui') and ('big' in ft or v == 'unk') for x in (a, b)
                                for oi, ok, ft, v in x.keep)
                persite.add((a.img.name, a.addr))
                persite.add((b.img.name, b.addr))
                out.append('\t'.join([' '.join(cited[key]), '%s %s %s' % key,
                                      '%s %s %#x | %s %s %#x' % (a.img.name, a.fn[2], a.fn[0],
                                                                 b.img.name, b.fn[2], b.fn[0]),
                                      '%s | %s' % (a.site(), b.site()), sh, ta, tb, how, verdict]) + '\n')
        return cited, out, shapes, persite, luisites
    cited, out, shapes, persite, luisites = trace(CLAIMS)
    ocited, oout, oshapes, opersite, oluisites = trace(OTHER, set(cited))
    if used != set(HAND):
        raise SystemExit('failopen.py: hand traces with no site: %s' % sorted(set(HAND) - used))
    behind = {(p, imgs[p].func_at(a)[0]) for k in cited for p, a in pairs[k][:2]}
    tot = collections.Counter()
    luiv = set()
    for k in ('n', 'comp', 'clui', 'jt', 'callee', 'roots'):
        tot[k] = sum(bodies[x][2][k] for x in behind)
    tot['tail'] = sum(len(bodies[x][2]['tail']) for x in behind)
    tot['small'] = sum(len(bodies[x][2]['small']) for x in behind)
    tot['esc'] = sum(len(bodies[x][2]['escapes']) for x in behind)
    for x in behind:
        for i, d, keep, b in bodies[x][2]['small']:
            luiv |= {sx(bodies[x][2]['D'][oi][4], 64) for oi, ok, ft, v in keep if ok in ('lui', 'c.lui')}
    outside = sum(len(bodies[x][2]['sites']) for x in behind) - len(persite)
    alloc = [fn[2] for fn, w, r in bodies.values() if 'Allocator8Allocate' in fn[2]]
    head = [
        '# The fail-open check of cmpkit %s on the EQUAL* / same claims of this record (claims.tsv), with the hand'
        % kid,
        '# trace of every site found. Written by failopen.py (this directory, sha256 %s).' % me,
        '# Claims checked: %d (%s).' % (len(CLAIMS), ' '.join(sorted(CLAIMS))),
        '# Compare rows they cite: %d; function bodies behind those rows, both sides: %d (%d words; 2-byte parcels %d,'
        % (len(cited), len(behind), tot['n'], tot['comp']),
        '# so c.lui %d; indirect jumps %d, all %d tail calls through a writable function pointer with sp back at its'
        % (tot['clui'], tot['jt'], tot['tail']),
        '# entry value; in-function calls %d; words no decoded edge reaches %d). No body is Allocator::Allocate (%d of'
        ' all'
        % (tot['callee'], tot['roots'], len(alloc)),
        '# %d bodies scanned), so its five immediate-case rows per asan image are not in this record.' % len(bodies),
        '# Sites (a base that may carry a constant of magnitude >= 0x10000 or of unknown value, or one exact constant),'
        ' as',
        '# site pairs inside the compared ranges: %d (%d distinct words over the two sides), all traced, %d with'
        ' targets'
        % (len(out), len(persite), 0),
        '# that differ. Per shape: %s.' % '; '.join('%s %d' % kv for kv in sorted(shapes.items())),
        '# Sites in these bodies outside the compared ranges of the range rows (not part of a claim): %d.' % outside,
        '# Sites where a lui or c.lui value is the address-like constant: %d. The lui words whose values reach a base'
        ' in'
        % luisites,
        '# these bodies are %s (frame and page constants); every value they give there is below 0x10000.'
        % ', '.join('%#x' % v if v >= 0 else '-%#x' % -v for v in sorted(luiv)),
        '# Bases that carry only constants below 0x10000 in magnitude: %d (counted, not traced: every image starts at'
        % tot['small'],
        '# 0x10000, so no such value names an image object). Stores of a constant >= 0x10000 where no stack slot is'
        ' known:',
        '# %d (the value is the store\'s data; a reload through the same base and offset is followed, no other).'
        % tot['esc'],
        '# Also traced, below the rows of the 62: the %d claims whose kit verdict is DIFFERENT or SIZE (%s; outside'
        % (len(OTHER), ' '.join(sorted(OTHER))),
        '# the rule, settled by S5): %d further compare rows, %d site pairs (%d lui-derived), 0 with targets that'
        ' differ.' % (len(ocited), len(oout), oluisites),
        '# Per shape: %s.' % '; '.join('%s %d' % kv for kv in sorted(oshapes.items())),
        'claims\tcompare row (output, row, pair)\tfunction side 1 | side 2 (image, name, address)\tsite side 1 | side 2'
        ' (address, offset, word)\tshape\ttarget side 1\ttarget side 2\thow traced\tverdict']
    open(outfile, 'w').write('\n'.join(head) + '\n' + ''.join(out) + ''.join(oout))
    print('failopen: %d claims, %d bodies behind them (%d scanned), %d site pairs traced, 0 differ; per shape %s; '
          'the other %d claims: %d site pairs traced, 0 differ'
          % (len(CLAIMS), len(behind), len(bodies), len(out), dict(sorted(shapes.items())), len(OTHER), len(oout)))


# ---- the self-test: one planted function per shape of the list; each must give a site
def _enc_i(op, rd, f3, rs1, imm):
    return op | (rd << 7) | (f3 << 12) | (rs1 << 15) | ((imm & 0xfff) << 20)


def _enc_s(op, f3, rs1, rs2, imm):
    return op | ((imm & 31) << 7) | (f3 << 12) | (rs1 << 15) | (rs2 << 20) | (((imm >> 5) & 0x7f) << 25)


def _lui(rd, hi):
    return 0x37 | (rd << 7) | ((hi & 0xfffff) << 12)


def _jal(rd, off):
    return 0x6f | (rd << 7) | (((off >> 12) & 0xff) << 12) | (((off >> 11) & 1) << 20) | \
        (((off >> 1) & 0x3ff) << 21) | (((off >> 20) & 1) << 31)


ADDI = lambda rd, rs, imm: _enc_i(0x13, rd, 0, rs, imm)
LD = lambda rd, rs, imm: _enc_i(0x03, rd, 3, rs, imm)
SD = lambda rs1, rs2, imm: _enc_s(0x23, 3, rs1, rs2, imm)
RET = _enc_i(0x67, 0, 0, 1, 0)
PLANTS = {
    'immediate': [_lui(5, 0x5f3), LD(6, 5, 0x750), RET],
    'addi-chain': [_lui(10, 0x22), ADDI(10, 10, 16), ADDI(10, 10, 8), LD(11, 10, 0), RET],
    'ori/xori/slli': [_lui(10, 0x22), _enc_i(0x13, 10, 1, 10, 4), _enc_i(0x13, 10, 6, 10, 8),
                      _enc_i(0x13, 10, 4, 10, 1), LD(11, 10, 0), RET],
    'spill': [_lui(10, 0x22), SD(2, 10, 8), ADDI(10, 0, 0), LD(12, 2, 8), LD(11, 12, 0), RET],
    'fp-move': [_lui(10, 0x22), 0x53 | (10 << 7) | (10 << 15) | (0x79 << 25),           # fmv.d.x fa0, a0
                0x53 | (11 << 7) | (10 << 15) | (0x71 << 25), LD(12, 11, 0), RET],    # fmv.x.d a1, fa0
    'csr': [_lui(10, 0x22), _enc_i(0x73, 0, 1, 10, 0x800), _enc_i(0x73, 11, 2, 0, 0x800), LD(12, 11, 0), RET],
    'jump-table': [_lui(10, 0x22), _enc_i(0x17, 5, 0, 0, 0), _enc_i(0x67, 0, 0, 5, 12), ADDI(10, 0, 0), LD(11, 10, 0),
                   RET],
    'callee': [_lui(10, 0x22), _jal(1, 8), RET, LD(11, 10, 0), RET],
    'c.lui': [0x6541, 0x610c, 0x8082],                              # c.lui a0, 0x10; c.ld a1, 0(a0); c.jr ra
    'without-lui(x0)': [ADDI(10, 0, 1), _enc_i(0x13, 10, 1, 10, 20), LD(11, 10, 0), RET],
}


class _NoImage:
    def pool_value(self, a, n):
        return None


def selftest():
    bad = []
    for shape, ws in PLANTS.items():
        b = b''.join(x.to_bytes(2 if x < 0x10000 and x & 3 != 3 else 4, 'little') for x in ws)
        out, i = [], 0
        while i < len(b):
            lo = b[i] | (b[i + 1] << 8)
            n = 4 if lo & 3 == 3 else 2
            out.append((i, int.from_bytes(b[i:i + n], 'little'), n))
            i += n
        r = analyse(_NoImage(), out, 0x100000)
        got = sorted({x for i, d, keep, bb in r['sites'] for oi, ok, ft, v in keep for x in shape_of(ok, ft)})
        print('%-16s sites %d  shapes %s' % (shape, len(r['sites']), ' '.join(got)))
        if not r['sites'] or shape not in got:
            bad.append(shape)
    print('selftest: %d of %d plants give a site with their shape%s' % (len(PLANTS) - len(bad), len(PLANTS),
                                                                       '; FAILED: ' + ' '.join(bad) if bad else ''))
    return 1 if bad else 0


if __name__ == '__main__':
    if sys.argv[1:] == ['--selftest']:
        sys.exit(selftest())
    main()
