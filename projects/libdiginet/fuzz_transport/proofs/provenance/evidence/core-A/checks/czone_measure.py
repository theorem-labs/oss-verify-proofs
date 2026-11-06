#!/usr/bin/env python3
"""The CZONE shadow bound of the image-A core: the end of the shadow of the unit's registered globals, and the shadow
of the image top. Reads the asan_globals section of the unstripped twin (one 64-byte descriptor per global: beg, size,
size_with_redzone, ...) and the last PT_LOAD of the image.
usage: czone_measure.py IMAGE_TWIN"""
import hashlib
import struct
import sys

from elftools.elf.elffile import ELFFile

SHADOW_OFF = 0x7fff8000
path = sys.argv[1]
print('image', path, 'sha256', hashlib.sha256(open(path, 'rb').read()).hexdigest())
e = ELFFile(open(path, 'rb'))
names = {}
for s in e.get_section_by_name('.symtab').iter_symbols():
    if s['st_info']['type'] == 'STT_OBJECT':
        names.setdefault(s['st_value'], s.name)
d = e.get_section_by_name('asan_globals').data()
hi = 0
for i in range(0, len(d), 64):
    beg, size, szr = struct.unpack_from('<QQQ', d, i)
    end = SHADOW_OFF + ((beg + szr + 7) >> 3)
    hi = max(hi, end)
    print('global %#x size %d with redzone %d shadow end %#x %s' % (beg, size, szr, end, names.get(beg, '?')))
top = max(s['p_vaddr'] + s['p_memsz'] for s in e.iter_segments() if s['p_type'] == 'PT_LOAD')
top = (top + 0xfff) & ~0xfff
print('descriptors %d; highest shadow end of a registered global %#x' % (len(d) // 64, hi))
print('image top (last PT_LOAD end, page-rounded) %#x; shadow_of(image top) = %#x' % (top, SHADOW_OFF + (top >> 3)))
print('bound %#x covers the globals: %s' % (SHADOW_OFF + (top >> 3), SHADOW_OFF + (top >> 3) >= hi))
