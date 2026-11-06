#!/usr/bin/env python3
"""Check that an unstripped twin is the same link as a stripped pin: equal PT_LOAD headers and equal loaded bytes,
except the .note.gnu.build-id bytes. Usage: check_twin.py PIN TWIN [PIN TWIN ...]; prints one line per pair."""
import sys
from elftools.elf.elffile import ELFFile


def loads(path):
    f = open(path, 'rb')
    e = ELFFile(f)
    segs = [(s['p_vaddr'], s['p_filesz'], s['p_memsz'], s['p_flags'], s.data()) for s in e.iter_segments()
            if s['p_type'] == 'PT_LOAD']
    bid = e.get_section_by_name('.note.gnu.build-id')
    bid = (bid['sh_addr'], bid['sh_addr'] + bid['sh_size']) if bid else None
    return segs, bid


args = sys.argv[1:]
for pin, twin in zip(args[0::2], args[1::2]):
    a, bida = loads(pin)
    b, bidb = loads(twin)
    if [s[:4] for s in a] != [s[:4] for s in b] or bida != bidb:
        print(f'{pin} {twin} DIFFERENT PT_LOAD headers')
        continue
    diff = []
    for (va, _, _, _, da), (_, _, _, _, db) in zip(a, b):
        for i, (x, y) in enumerate(zip(da, db)):
            if x != y and not (bida and bida[0] <= va + i < bida[1]):
                diff.append(va + i)
    # the ELF header (first 64 bytes of the first PT_LOAD, file offset 0) carries e_shoff / e_shnum / e_shstrndx,
    # which differ between a stripped file and its twin; any other byte is a real difference
    base = a[0][0]
    hdr = [d for d in diff if d - base < 64]
    print(f'{pin} {twin} {len(a)} PT_LOAD equal headers; differing loaded bytes outside build-id: {len(diff)} '
          f'({len(hdr)} in the ELF header at offsets {",".join(hex(d - base) for d in hdr)}; '
          f'{len(diff) - len(hdr)} elsewhere)')
