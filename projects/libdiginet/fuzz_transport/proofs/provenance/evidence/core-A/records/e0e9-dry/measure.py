#!/usr/bin/env python3
"""measure.py: the ELF facts E0E9-DRY.md cites (pyelftools only). Checks each image's sha256 first, then prints the
.rodata / .text / .tbss / .bss section bounds and the image top (last PT_LOAD end, page-rounded) of the target and the
donor, and the TOT bound arithmetic of A/AFem.v TOT_range."""
import hashlib
import sys

from elftools.elf.elffile import ELFFile

IMGS = [
    ('target fuzz_transport.asan', 'TIMG/stripped/fuzz_transport.asan',
     'e89be137db17'),
    ('target twin', 'TIMG/unstripped/fuzz_transport.asan',
     '86efc3a80314'),
    ('donor fuzz_grant.asan', 'PG/bin/fuzz_grant/fuzz_grant.asan',
     'c2c7559b29bd'),
    ('donor twin', 'PG/unstripped/fuzz_grant/fuzz_grant.asan',
     '57c26f993615'),
]
for who, path, pin in IMGS:
    sha = hashlib.sha256(open(path, 'rb').read()).hexdigest()[:12]
    if sha != pin:
        sys.exit(f'pin mismatch: {path} is {sha}, not {pin}')
    print(f'{who}: {path} sha256 {sha} (pin {pin}): OK')
    if 'twin' in who:
        continue
    e = ELFFile(open(path, 'rb'))
    for s in e.iter_sections():
        if s.name in ('.rodata', '.text', '.tbss', '.bss'):
            lo, sz = s['sh_addr'], s['sh_size']
            print(f'  {s.name:8s} sh_addr {lo:#x} sh_size {sz:#x} end {lo + sz:#x}')
    top = max(p['p_vaddr'] + p['p_memsz'] for p in e.iter_segments() if p['p_type'] == 'PT_LOAD')
    print(f'  last PT_LOAD end {top:#x}, page-rounded {(top + 0xfff) & ~0xfff:#x}')
F, CAP, K = 31, 4096, 30
print(f'TOT bound: F + 1 + F * CAP = {F} + 1 + {F} * {CAP} = {F + 1 + F * CAP}; post-store bound N + K + 1 = '
      f'{F + 1 + F * CAP} + {K} + 1 = {F + 1 + F * CAP + K + 1} <= 131072: {F + 1 + F * CAP + K + 1 <= 131072}')
