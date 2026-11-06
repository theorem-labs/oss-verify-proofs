#!/usr/bin/env python3
"""cellcheck.py STAGE_DIR NEW_ELF -- every `zN (ANum A) V` cell whose address A is file-backed in NEW_ELF:
compare V with NEW_ELF's little-endian N bytes at A. Prints file, line, addr, n, written, elf. Exit status 1 when
any cell differs (or no file-backed cell was found), 0 otherwise."""
import re, sys, glob, os
from elftools.elf.elffile import ELFFile
d, elf = sys.argv[1:3]
raw = open(elf, 'rb').read(); ef = ELFFile(open(elf, 'rb'))
segs = [(s['p_vaddr'], s['p_vaddr'] + s['p_filesz'], s['p_offset']) for s in ef.iter_segments() if s['p_type'] == 'PT_LOAD']
def fb(a, n):
    for lo, hi, off in segs:
        if lo <= a and a + n <= hi:
            return int.from_bytes(raw[off + a - lo: off + a - lo + n], 'little')
cell = re.compile(r'\bz(1|2|4|8)\s+\(ANum\s+(0x[0-9a-fA-F]+|\d+)\)\s+(0x[0-9a-fA-F]+|\d+)')
tot = bad = 0
for p in sorted(glob.glob(os.path.join(d, '**', '*.v'), recursive=True)):
    for i, l in enumerate(open(p).read().split('\n'), 1):
        for m in cell.finditer(l):
            n, a, v = int(m.group(1)), int(m.group(2), 0), int(m.group(3), 0)
            e = fb(a, n)
            if e is None:
                continue
            tot += 1
            if e != v:
                bad += 1
                print(f'{os.path.relpath(p, d)}\t{i}\t{a:#x}\t{n}\t{v:#x}\t{e:#x}')
print(f'# {tot} file-backed cells, {bad} mismatch', file=sys.stderr)
sys.exit(1 if bad or not tot else 0)
