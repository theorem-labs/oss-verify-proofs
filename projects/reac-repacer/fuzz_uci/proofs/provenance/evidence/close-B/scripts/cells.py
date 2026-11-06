#!/usr/bin/env python3
"""cells.py IMAGE TWIN -- the runtime cells of lib/{A,B}/AsanCells.v, measured on one image: each cell's address
(the unstripped twin's symbol), its section, the GOT word of the pinned image's .got that holds the cell's address,
the 8-byte value of the two file-backed REAL cells, the musl memcpy / memchr entries, MARGIN_MAX's registered global
(__start_asan_globals) and the four PT_LOADs. Prints one line per item. Needs pyelftools.
"""
import struct
import sys

from elftools.elf.elffile import ELFFile

CELLS = [('CELL_K', '__asan_shadow_memory_dynamic_address'),
         ('UAR', '__asan_option_detect_stack_use_after_return'),
         ('INITED', '_ZN6__asanL11asan_initedE'),
         ('REPLACE', '_ZN6__asan21replace_intrin_cachedE'),
         ('CANPOISON', '_ZN6__asanL17can_poison_memoryE'),
         ('HIEND', '_ZN6__asan11kHighMemEndE'),
         ('MIDBEG', '_ZN6__asan10kMidMemBegE'),
         ('MIDEND', '_ZN6__asan10kMidMemEndE'),
         ('REAL_MEMCPY', '_ZN14__interception11real_memcpyE'),
         ('REAL_MEMCHR', '_ZN14__interception11real_memchrE')]


def main():
    img, twin = sys.argv[1:3]
    fi, ft = ELFFile(open(img, 'rb')), ELFFile(open(twin, 'rb'))
    segs = [(s['p_vaddr'], s['p_filesz'], s['p_memsz'], s['p_flags'], s.data()) for s in fi.iter_segments()
            if s['p_type'] == 'PT_LOAD']
    syms = {}
    for s in ft.get_section_by_name('.symtab').iter_symbols():
        if s.name:
            syms.setdefault(s.name, s['st_value'])
    secs = [(s.name, s['sh_addr'], s['sh_size']) for s in ft.iter_sections() if s['sh_addr']]

    def u64(a):
        for va, fs, ms, fl, d in segs:
            if va <= a and a + 8 <= va + fs:
                return struct.unpack('<Q', d[a - va:a - va + 8])[0]
        return None

    def sec(a):
        return ','.join(n for n, b, z in secs if b <= a < b + z)
    g0, gs = [(b, z) for n, b, z in secs if n == '.got'][0]
    got = {}
    for a in range(g0, g0 + gs, 8):
        got.setdefault(u64(a), []).append(a)
    for va, fs, ms, fl, d in segs:
        print('PT_LOAD %#x filesz %#x memsz %#x flags %d' % (va, fs, ms, fl))
    for tag, sym in CELLS:
        a = syms[sym]
        print('%s %#x %s %s GOT %s' % (tag, a, sym, sec(a), ' '.join('%#x' % g for g in got.get(a, [])) or '-'))
    for tag in ('REAL_MEMCPY', 'REAL_MEMCHR'):
        print('%s holds %#x' % (tag, u64(syms[dict(CELLS)[tag]])))
    for sym in ('memcpy', 'memchr', '__start_asan_globals', '__wrap_getenv'):
        print('%s %#x' % (sym, syms[sym]))


if __name__ == '__main__':
    main()
