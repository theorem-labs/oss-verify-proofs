#!/usr/bin/env python3
"""dwarfline.py -- the source file and line of an address in an unstripped twin, from its .debug_line (pyelftools):
the row of the line table with the greatest address <= the queried address, in the sequence that holds it.
usage: dwarfline.py ELF ADDR [ADDR ..]   (prints `ADDR file:line`)"""
import bisect, os, sys
from elftools.elf.elffile import ELFFile

_CACHE = {}


def table(path):
    """sorted [(address, file, line, end_sequence)] of every line-table row of the image"""
    if path in _CACHE:
        return _CACHE[path]
    rows = []
    with open(path, 'rb') as f:
        dw = ELFFile(f).get_dwarf_info()
        for cu in dw.iter_CUs():
            lp = dw.line_program_for_CU(cu)
            if lp is None:
                continue
            fe = lp['file_entry']
            de = lp['include_directory']
            v5 = lp.header['version'] >= 5

            def fname(i):
                e = fe[i if v5 else i - 1]
                n = e.name.decode() if isinstance(e.name, bytes) else e.name
                d = e.dir_index
                dn = de[d if v5 else d - 1] if (d if v5 else d - 1) >= 0 and (d if v5 else d - 1) < len(de) else b''
                dn = dn.decode() if isinstance(dn, bytes) else dn
                return os.path.join(dn, n) if dn and not n.startswith('/') else n
            for ent in lp.get_entries():
                st = ent.state
                if st is None:
                    continue
                try:
                    fn = fname(st.file)
                except (IndexError, AttributeError):
                    fn = '?'
                rows.append((st.address, fn, st.line, st.end_sequence))
    rows.sort()
    _CACHE[path] = (rows, [r[0] for r in rows])
    return _CACHE[path]


def where(path, addr):
    rows, keys = table(path)
    i = bisect.bisect_right(keys, addr) - 1
    while i >= 0 and rows[i][3]:
        i -= 1
    if i < 0:
        return None
    return '%s:%d' % (rows[i][1], rows[i][2])


if __name__ == '__main__':
    for x in sys.argv[2:]:
        print(x, where(sys.argv[1], int(x, 0)))
