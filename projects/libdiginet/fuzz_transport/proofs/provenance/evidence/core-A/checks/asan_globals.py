#!/usr/bin/env python3
"""asan_globals.py ELF -- list the ASan global descriptors of ELF's asan_globals section (LLVM __asan_global, 8 words:
beg, size, size_with_redzone, name, module_name, has_dynamic_init, location, odr_indicator), one row per descriptor:
beg size size_with_redzone name. Reads only section bytes and the strings the name pointers point at."""
import struct
import sys
from elftools.elf.elffile import ELFFile


def main():
    path = sys.argv[1]
    with open(path, 'rb') as f:
        elf = ELFFile(f)
        sec = elf.get_section_by_name('asan_globals')
        data = sec.data()
        segs = [s for s in elf.iter_segments() if s['p_type'] == 'PT_LOAD']

        def cstr(addr):
            for s in segs:
                if s['p_vaddr'] <= addr < s['p_vaddr'] + s['p_filesz']:
                    f.seek(s['p_offset'] + addr - s['p_vaddr'])
                    raw = f.read(256)
                    return raw.split(b'\0', 1)[0].decode('latin-1')
            return '?'
        n = len(data) // 64
        print(f'# asan_globals at {sec["sh_addr"]:#x} size {sec["sh_size"]:#x}: {n} descriptors')
        for i in range(n):
            beg, size, szr, name, mod, dyn, loc, odr = struct.unpack_from('<8Q', data, 64 * i)
            print(f'{beg:#x}\t{size}\t{szr}\t{cstr(name)}')


main()
