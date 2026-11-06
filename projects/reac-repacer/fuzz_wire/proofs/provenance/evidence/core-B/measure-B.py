#!/usr/bin/env python3
"""measure-B.py: the values of fuzz_wire's image-B overrides-B.tsv, each by its ROLE, on the donor image (control: must
print the donor's own value) and on fuzz_wire.asan-ubsan. Images: pinned stripped ELF for bytes and section headers,
unstripped twin for symbols. Values the start-up tables decide (TFIB_BSS = the last range of Tfib_zero_shadow, the const
shadow cells, the canary cell's index) are read from lib/B/YF0m.v at the end, with fuzz_grant's released tables as control.
fuzz_wire registers no ASan global (no asan_globals section, __stop_asan_globals = 0)."""
import os, struct, sys
from elftools.elf.elffile import ELFFile

P = os.environ['P']   # libreac's pinned image tree (bin/fuzz_grant, unstripped/fuzz_grant)
R = os.environ['R']   # reac-repacer's pinned image tree (result/bin/fuzz_wire, result/unstripped/fuzz_wire)


class Im:
    def __init__(self, pin, twin):
        self.e = ELFFile(open(pin, 'rb'))
        self.secs = {s.name: (s['sh_addr'], s['sh_size']) for s in self.e.iter_sections() if s['sh_addr']}
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
    bss = I.secs['.bss'][0]
    out['.bss start (information)'] = bss
    out['__stop_asan_globals (symbol)'] = I.sym.get('__stop_asan_globals')
    out['IMG_TOP (page-up end of last PT_LOAD)'] = I.top()
    out['.bss+0x20 (__do_init.__object + 16)'] = I.sym['__do_init.__object'] + 16
    out['first PT_LOAD'] = min(v for v, _, _, _ in I.loads)
    out['(.bss+0x20) / 8'] = out['.bss+0x20 (__do_init.__object + 16)'] // 8
    for k in ('__asan_memset', '__interceptor_trampoline_bcmp', 'bcmp', 'asan.module_dtor'):
        out['symbol ' + k] = I.sym.get(k)
    print(f'== {name}')
    for k, v in out.items():
        print(f'  {k:40s} {v if v is None else f"{v:#x} = {v}"}')
    for f, (fmt, ln) in fmts.items():
        lo, hi = win(fmt, ln)
        print(f'  {f} FMT {fmt:#x} {I.cstr(fmt)!r} len {ln}: SH [{lo:#x}, {hi:#x})')


G = Im(f'{P}/bin/fuzz_grant/fuzz_grant.asan-ubsan', f'{P}/unstripped/fuzz_grant/fuzz_grant.asan-ubsan')
U = Im(f'{R}/result/bin/fuzz_wire/fuzz_wire.asan-ubsan', f'{R}/result/unstripped/fuzz_wire/fuzz_wire.asan-ubsan')
# FMT: the donor file's own FMT (grant), the relocated FMT in stage-out (wire); len: the file's hull_zero length
report('fuzz_grant.asan-ubsan (CONTROL: must equal the donor text)', G,
       {'B/YE2t.v': (0x1d6e7, 21), 'B/YE2u.v': (0x1d6fc, 23), 'B/YE2w.v': (0x1583c, 17), 'B/YE35.v': (0x1479a, 4),
        'B/YE2v.v': (0x196a4, 33)})
report('fuzz_wire.asan-ubsan', U,
       {'B/YE2t.v': (0x1d5f9, 21), 'B/YE2u.v': (0x1d60e, 23), 'B/YE2w.v': (0x157da, 17), 'B/YE35.v': (0x1476b, 4),
        'B/YE2v.v': (0x19632, 33)})


def canary_index(yf0m, ye22):
    """index of the cell z8 (ANum A_GOT_CANARY) ... in YF0m's Tfib_const_abs, A_GOT_CANARY read from the YE22 / AE22 text"""
    import re
    t = open(yf0m).read()
    i = t.find('Definition Tfib_const_abs')
    cells = [c.strip() for c in t[t.find('[', i) + 1:t.find('].', i)].split(';') if c.strip()]
    a = re.search(r'Definition A_GOT_CANARY : Z := (0x[0-9a-f]+)', open(ye22).read()).group(1)
    hit = [k for k, c in enumerate(cells) if re.search(r'ANum %s\)' % a, c)]
    return a, hit, len(cells)


def zero_shadow_last(yf0m):
    """the last (start, length) of YF0m's Tfib_zero_shadow, the range YD1o / YD25's bss_zero_shadow names"""
    import re
    t = open(yf0m).read()
    i = t.find('Definition Tfib_zero_shadow')
    body = t[t.find('[', i) + 1:t.find('].', i)]
    ranges = re.findall(r'\(\s*(0x[0-9a-f]+)\s*,\s*(0x[0-9a-f]+)\s*-\s*(0x[0-9a-f]+)\s*\)', body)
    s, top, s2 = ranges[-1]
    return int(s, 16), int(top, 16), len(ranges)


def const_shadow_max(yf0m):
    import re
    t = open(yf0m).read()
    i = t.find('Definition Tfib_const_shadow')
    cells = [int(x, 16) for x in re.findall(r'ANum (0x[0-9a-f]+)\)', t[i:t.find('].', i)])]
    return len(cells), (max(cells) if cells else None)


# Values read from the start-up tables (lib/B/YF0m.v is generated from the image by the start-up layer). GRANTLIB =
# fuzz_grant's released lib (recipes 4f87de75d67); CORE = this unit's tree; YE22 = the relocated YE22.v (stage-out).
if os.environ.get('GRANTLIB') and os.environ.get('CORE'):
    gl, cl = os.environ['GRANTLIB'], os.environ['CORE'] + '/lib'
    ye22 = os.environ.get('YE22', cl + '/B/YE22.v')
    for name, yf, ye in (('fuzz_grant B (CONTROL: the donor text says 273)', gl + '/B/YF0m.v', gl + '/B/YE22.v'),
                         ('fuzz_wire A (CONTROL: AE22.v says 273)', cl + '/A/AF0m.v', cl + '/A/AE22.v'),
                         ('fuzz_wire B', cl + '/B/YF0m.v', ye22)):
        a, hit, n = canary_index(yf, ye)
        print(f'== {name}: canary cell ANum {a} at index {hit} of {n} Tfib_const_abs cells')
    for name, yf in (('fuzz_grant B (CONTROL: the donor text says 0xa22c0, 0x5fb000)', gl + '/B/YF0m.v'),
                     ('fuzz_wire B', cl + '/B/YF0m.v')):
        s, top, n = zero_shadow_last(yf)
        k, mx = const_shadow_max(yf)
        print(f'== {name}: Tfib_zero_shadow {n} ranges, last ({s:#x}, {top:#x} - {s:#x}): TFIB_BSS = {s:#x} = {s}, '
              f'/8 = {s // 8}, (IMG_TOP - TFIB_BSS) / 8 = {(top - s) // 8}; Tfib_const_shadow {k} cells, highest '
              f'{mx if mx is None else hex(mx)}')
