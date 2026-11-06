#!/usr/bin/env python3
"""syms.py -- print every symbol (any type) whose name is in the list, with value, size, type, bind. usage: syms.py ELF n1,n2,..."""
import sys
from elftools.elf.elffile import ELFFile
want = set(sys.argv[2].split(','))
e = ELFFile(open(sys.argv[1], 'rb'))
for s in e.get_section_by_name('.symtab').iter_symbols():
    if s.name in want:
        print('%s\t%#x\t%d\t%s\t%s' % (s.name, s['st_value'], s['st_size'], s['st_info']['type'], s['st_info']['bind']))
