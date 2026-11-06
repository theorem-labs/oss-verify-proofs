#!/usr/bin/env python3
"""measure-B.py: the values of overrides-B.tsv and B-ceg-const.patch, each by its ROLE, on the donor image (control: the
rule must print the donor's own value, the one its released text holds) and on libdiginet fuzz_decode.asan-ubsan.
Images: the pinned stripped ELF for bytes, the unstripped twin for symbols.
  P     libreac's pinned image tree (bin/fuzz_decode, unstripped/fuzz_decode)
  T     libdiginet's pinned image tree (result/bin/fuzz_decode, result/unstripped/fuzz_decode)
  STAGE (optional) a run's work dir: the FMT of each driver file is read from its stage/ (donor) and stage-out/ (target)
        text, and its hull_zero length from the same file
Roles:
  FILE.buf       the buffer pointer of __stdout_FILE / __stderr_FILE / __stdin_FILE (FILE + 88), read from the image
  BUFEND         stdout's buf + 1024 (STDOUT_BSZ)
  SH window      [floor8(shadow(FMT)), floor8(shadow(FMT + len - 1)) + 8): hull_zero's own bounds, shadow(x) = 0x7fff8000 + x / 8
  instance cell  _ZN6__asanL8instanceE + 0x318 / + 0x328: the two adjacent allocator cells YFgi / YFgm / YFgn state with flit8
  rw range       tfib_at_rw_lo = page-down start of the last PT_LOAD, tfib_at_rw_len = IMG_TOP - rw_lo
                 (IMG_TOP = page-up end of the last PT_LOAD)
  const reads    lib_const_addr: every load of the program's own functions (LLVMFuzzerTestOneInput .. end of the last
                 program function before __wrap_getenv) whose effective address is formed by auipc (+ the load's own
                 offset) or gp, and lands in a PT_LOAD without the W flag: [addr, addr + access width). A read of the
                 .got (the runtime's cells) is listed apart."""
import bisect, os, re, struct, sys
import capstone
from elftools.elf.elffile import ELFFile

P, T = os.environ['P'], os.environ['T'] + '/result'
STAGE = os.environ.get('STAGE')
SHADOW = 0x7fff8000
WIDTH = {'ld': 8, 'fld': 8, 'lwu': 4, 'lw': 4, 'flw': 4, 'lhu': 2, 'lh': 2, 'lbu': 1, 'lb': 1,
         'c.ld': 8, 'c.lw': 4, 'c.fld': 8, 'c.flw': 4}


class Im:
    def __init__(self, pin, twin):
        self.e = ELFFile(open(pin, 'rb'))
        self.loads = [(g['p_vaddr'], g['p_memsz'], g['p_filesz'], g['p_flags'], g.data()) for g in self.e.iter_segments()
                      if g['p_type'] == 'PT_LOAD']
        self.sym, self.funcs = {}, []
        for s in ELFFile(open(twin, 'rb')).get_section_by_name('.symtab').iter_symbols():
            if s.name:
                self.sym.setdefault(s.name, s['st_value'])
                if s['st_info']['type'] == 'STT_FUNC' and s['st_value'] and s['st_size']:
                    self.funcs.append((s['st_value'], s['st_size'], s.name))
        self.funcs.sort()
        self.secs = {s.name: (s['sh_addr'], s['sh_size']) for s in self.e.iter_sections() if s['sh_addr']}

    def rd(self, a, n):
        for v, m, fz, fl, d in self.loads:
            if v <= a and a + n <= v + fz:
                return d[a - v:a - v + n]
        raise KeyError(hex(a))

    def q(self, a):
        return struct.unpack('<Q', self.rd(a, 8))[0]

    def cstr(self, a):
        return self.rd(a, 64).split(b'\0')[0]

    def top(self):
        return -(-max(v + m for v, m, _, _, _ in self.loads) // 4096) * 4096

    def last_lo(self):
        return max(v for v, _, _, _, _ in self.loads) // 4096 * 4096

    def ro(self, a, n=1):
        return any(v <= a and a + n <= v + m and not fl & 2 for v, m, _, fl, _ in self.loads)

    def prog(self):
        lo, wg = self.sym['LLVMFuzzerTestOneInput'], self.sym['__wrap_getenv']
        return [f for f in self.funcs if lo <= f[0] < wg]


def win(fmt, ln):
    sh = lambda x: SHADOW + (x >> 3)
    return sh(fmt) // 8 * 8, sh(fmt + ln - 1) // 8 * 8 + 8


MD = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)


def const_reads(I):
    gp = I.sym.get('__global_pointer$')
    got = I.secs.get('.got')
    out = []
    for a, n, name in I.prog():
        code, reg = I.rd(a, n), {}
        for i in MD.disasm(code, a):
            ops = [x.strip() for x in i.op_str.split(',')]
            m = i.mnemonic
            if m == 'auipc':
                v = int(ops[1], 0)
                reg[ops[0]] = i.address + ((v - (1 << 20) if v >= 1 << 19 else v) << 12)
                continue
            mm = re.match(r'(-?\w+)\((\w+)\)', ops[-1]) if ops else None
            if m in WIDTH and mm:
                base = mm.group(2)
                ea = reg.get(base) if base != 'gp' else gp
                if ea is not None:
                    ea += int(mm.group(1), 0)
                    out.append((name, i.address, m, ea, WIDTH[m]))
            if m.startswith('c.') and not m in WIDTH:
                reg.clear()                          # a 16-bit instruction other than a load ends the tracking
            elif ops and re.fullmatch(r'[a-z]\w*', ops[0]) and m not in ('sd', 'sw', 'sh', 'sb', 'fsd', 'fsw', 'c.sd',
                                                                         'c.sw', 'j', 'jal', 'beq', 'bne', 'blt', 'bge',
                                                                         'bltu', 'bgeu', 'c.j', 'c.beqz', 'c.bnez'):
                reg.pop(ops[0], None)               # the destination register no longer holds the auipc value
    ro = [(nm, pc, m, ea, w) for nm, pc, m, ea, w in out if I.ro(ea, w) and not (got and got[0] <= ea < got[0] + got[1])]
    gr = [(nm, pc, m, ea, w) for nm, pc, m, ea, w in out if got and got[0] <= ea < got[0] + got[1]]
    return sorted({(ea, w) for _, _, _, ea, w in ro}), ro, gr


def report(name, I, fmts):
    out = {}
    for f in ('__stdout_FILE', '__stderr_FILE', '__stdin_FILE'):
        out[f + '.buf (FILE+88)'] = I.q(I.sym[f] + 88)
    out['BUFEND (stdout buf + 1024)'] = out['__stdout_FILE.buf (FILE+88)'] + 1024
    ins = I.sym['_ZN6__asanL8instanceE']
    out['__asan::instance + 0x318'] = ins + 0x318
    out['__asan::instance + 0x328'] = ins + 0x328
    out['IMG_TOP (page-up end of last PT_LOAD)'] = I.top()
    out['tfib_at_rw_lo (page-down start of last PT_LOAD)'] = I.last_lo()
    out['tfib_at_rw_len (IMG_TOP - rw_lo)'] = I.top() - I.last_lo()
    print(f'== {name}')
    for k, v in out.items():
        print(f'  {k:48s} {v:#x} = {v}')
    for f, (fmt, ln) in fmts.items():
        lo, hi = win(fmt, ln)
        print(f'  {f} FMT {fmt:#x} {I.cstr(fmt)!r} len {ln}: SH [{lo:#x}, {hi:#x})')
    rng, ro, gr = const_reads(I)
    pr = I.prog()
    print(f'  program functions [{pr[0][0]:#x}, {pr[-1][0] + pr[-1][1]:#x}): {len(pr)}')
    for nm, pc, m, ea, w in ro:
        print(f'    const read {nm} pc {pc:#x} {m} {ea:#x} ({w} bytes)')
    for nm, pc, m, ea, w in gr:
        print(f'    .got read  {nm} pc {pc:#x} {m} {ea:#x} ({w} bytes; the runtime\'s cell, not a constant of the program)')
    print('  lib_const_addr: ' + ' \\/ '.join(f'({a:#x} <= a < {a + w:#x})' for a, w in rng))


def fmts_of(root):
    res = {}
    for f in ('B/YE2t.v', 'B/YE2u.v', 'B/YE2v.v', 'B/YE2w.v', 'B/YE35.v'):
        t = open(f'{root}/{f}').read()
        fmt = int(re.search(r'Definition FMT : Z := (0x[0-9a-f]+)\.', t).group(1), 16)
        ln = int(re.search(r'hull_zero \(aview[^\n]*?\) FMT\w* (\d+) ->', t).group(1))
        res[f] = (fmt, ln)
    return res


D = Im(f'{P}/bin/fuzz_decode/fuzz_decode.asan-ubsan', f'{P}/unstripped/fuzz_decode/fuzz_decode.asan-ubsan')
G = Im(f'{T}/bin/fuzz_transport/fuzz_transport.asan-ubsan', f'{T}/unstripped/fuzz_transport/fuzz_transport.asan-ubsan')
report('libreac fuzz_decode.asan-ubsan (CONTROL: must equal the donor text)', D, fmts_of(f'{STAGE}/stage') if STAGE else {})
report('libdiginet fuzz_transport.asan-ubsan', G, fmts_of(f'{STAGE}/stage-out') if STAGE else {})
