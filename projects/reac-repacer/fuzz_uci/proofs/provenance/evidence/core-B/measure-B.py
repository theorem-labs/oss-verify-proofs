#!/usr/bin/env python3
"""measure-B.py: the values of overrides-B.tsv, each by its ROLE, on the donor image (control: must print the donor's
own value) and on fuzz_uci.asan-ubsan. Images: pinned stripped ELF for bytes, unstripped twin for symbols."""
import os, struct, sys
from elftools.elf.elffile import ELFFile

P = os.environ['P']   # libreac's pinned image tree (bin/fuzz_grant, unstripped/fuzz_grant)
R = os.environ['R']   # reac-repacer's pinned image tree (result/bin/fuzz_uci, result/unstripped/fuzz_uci)


class Im:
    def __init__(self, pin, twin):
        self.e = ELFFile(open(pin, 'rb'))
        self.loads = [(g['p_vaddr'], g['p_memsz'], g['p_filesz'], g.data()) for g in self.e.iter_segments()
                      if g['p_type'] == 'PT_LOAD']
        self.sym = {}
        for s in ELFFile(open(twin, 'rb')).get_section_by_name('.symtab').iter_symbols():
            if s.name:
                self.sym.setdefault(s.name, s['st_value'])

    def rd(self, a, n):
        for v, m, fz, d in self.loads:
            if v <= a and a + n <= v + fz:
                return d[a - v:a - v + n]
        raise KeyError(hex(a))

    def q(self, a):
        return struct.unpack('<Q', self.rd(a, 8))[0]

    def cstr(self, a):
        return self.rd(a, 64).split(b'\0')[0]

    def top(self):
        return -(-max(v + m for v, m, _, _ in self.loads) // 4096) * 4096


def win(fmt, ln):
    sh = lambda x: 0x7fff8000 + (x >> 3)
    return sh(fmt) // 8 * 8, sh(fmt + ln) // 8 * 8 + 8


def report(name, I, fmts):
    out = {}
    for f in ('__stdout_FILE', '__stderr_FILE', '__stdin_FILE'):
        out[f + '.buf'] = I.q(I.sym[f] + 88)
    out['BUFEND (stdout buf + 1024)'] = out['__stdout_FILE.buf'] + 1024
    bss = I.sym['__stop_asan_globals']
    out['TFIB_BSS (__stop_asan_globals)'] = bss
    out['IMG_TOP (page-up end of last PT_LOAD)'] = I.top()
    out['.bss+0x20 (__do_init.__object + 16)'] = I.sym['__do_init.__object'] + 16
    out['first PT_LOAD'] = min(v for v, _, _, _ in I.loads)
    out['(.bss+0x20) / 8'] = out['.bss+0x20 (__do_init.__object + 16)'] // 8
    out['TFIB_BSS / 8'] = bss // 8
    out['(IMG_TOP - TFIB_BSS) / 8'] = (I.top() - bss) // 8
    for k in ('__asan_memset', '__interceptor_trampoline_bcmp', 'bcmp'):
        out['symbol ' + k] = I.sym.get(k)
    print(f'== {name}')
    for k, v in out.items():
        print(f'  {k:40s} {v if v is None else f"{v:#x} = {v}"}')
    for f, (fmt, ln) in fmts.items():
        lo, hi = win(fmt, ln)
        print(f'  {f} FMT {fmt:#x} {I.cstr(fmt)!r} len {ln}: SH [{lo:#x}, {hi:#x})')


G = Im(f'{P}/bin/fuzz_grant/fuzz_grant.asan-ubsan', f'{P}/unstripped/fuzz_grant/fuzz_grant.asan-ubsan')
U = Im(f'{R}/result/bin/fuzz_uci/fuzz_uci.asan-ubsan', f'{R}/result/unstripped/fuzz_uci/fuzz_uci.asan-ubsan')
# FMT: the donor file's own FMT (grant), the relocated FMT in stage-out (uci); len: the file's hull_zero length
report('fuzz_grant.asan-ubsan (CONTROL: must equal the donor text)', G,
       {'B/YE2t.v': (0x1d6e7, 21), 'B/YE2u.v': (0x1d6fc, 23), 'B/YE2w.v': (0x1583c, 17), 'B/YE35.v': (0x1479a, 4),
        'B/YE2v.v': (0x196a4, 33)})
report('fuzz_uci.asan-ubsan', U,
       {'B/YE2t.v': (0x1d5e6, 21), 'B/YE2u.v': (0x1d5fb, 23), 'B/YE2w.v': (0x157cd, 17), 'B/YE35.v': (0x14763, 4),
        'B/YE2v.v': (0x19614, 33)})


def canary_index(yf0m, ye22):
    """index of the cell z8 (ANum A_GOT_CANARY) ... in YF0m's Tfib_const_abs, A_GOT_CANARY read from the YE22 / AE22 text"""
    import re
    t = open(yf0m).read()
    i = t.find('Definition Tfib_const_abs')
    cells = [c.strip() for c in t[t.find('[', i) + 1:t.find('].', i)].split(';') if c.strip()]
    a = re.search(r'Definition A_GOT_CANARY : Z := (0x[0-9a-f]+)', open(ye22).read()).group(1)
    hit = [k for k, c in enumerate(cells) if re.search(r'ANum %s\)' % a, c)]
    return a, hit, len(cells)


# YE22's index into Tfib_const_abs. GRANTLIB = fuzz_grant's released lib (recipes 4f87de75d67); CORE = this unit's tree
if os.environ.get('GRANTLIB') and os.environ.get('CORE'):
    gl, cl = os.environ['GRANTLIB'], os.environ['CORE'] + '/lib'
    for name, yf, ye in (('fuzz_grant B (CONTROL: the donor text says 273)', gl + '/B/YF0m.v', gl + '/B/YE22.v'),
                         ('fuzz_uci A (CONTROL: AE22.v says 273)', cl + '/A/AF0m.v', cl + '/A/AE22.v'),
                         ('fuzz_uci B', cl + '/B/YF0m.v', cl + '/B/YE22.v')):
        a, hit, n = canary_index(yf, ye)
        print(f'== {name}: canary cell ANum {a} at index {hit} of {n} Tfib_const_abs cells')
