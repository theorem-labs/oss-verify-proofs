#!/usr/bin/env python3
"""ro_pins.py -- the owned read-only static bytes of an AF0m.v, and how many of them a const cell pins.

From the file's own tables: the Tfib_owned_static rows wholly inside a read-only PT_LOAD of the image (no W flag),
their bytes, and how many of those bytes the distinct Tfib_const_abs cells wholly inside a read-only PT_LOAD cover.
The parsing and the rule are af0m.py's own (`ro_segs`, `list_parts`, `parse_cell`, `ro_counts` of af0m f8201f503394,
startup-set-2026-10-30d), imported from the set directory SETDIR. af0m's `ro_counts` is also called, and its answer
(cell bytes, cells, ranges, or its refusal) is printed.

Usage: ro_pins.py SETDIR AF0m.v IMAGE
Exit 0 when every owned read-only byte is pinned by a cell, 1 otherwise.
"""
import hashlib, re, sys, types


def main():
    setdir, af0m_path, image = sys.argv[1:4]
    sys.path.insert(0, setdir)
    import af0m
    from elftools.elf.elffile import ELFFile
    txt = open(af0m_path).read()
    ro = af0m.ro_segs(types.SimpleNamespace(e=ELFFile(open(image, 'rb'))))

    def grab_t(name):
        i = txt.index('Definition %s ' % name); j = txt.index('].', i)
        return txt[i:j + 2]
    inro = lambda a, n: any(lo <= a and a + n <= hi for lo, hi in ro)
    own = [(int(x, 16), int(eval(y))) for x, y in re.findall(r'\((0x[0-9a-f]+), ([^)]+)\)', grab_t('Tfib_owned_static'))]
    cells = [c for c in (af0m.parse_cell(r) for r in af0m.list_parts(grab_t('Tfib_const_abs'))[1] if r.strip()) if c]
    oro = [(a, n) for a, n in own if inro(a, n)]
    cro = sorted({(w, a) for w, a, v in cells if w and inro(a, w)})
    cov = {z for w, a in cro for z in range(a, a + w)}
    ownb = {z for a, n in oro for z in range(a, a + n)}
    print(f'af0m.py sha256 {hashlib.sha256(open(af0m.__file__, "rb").read()).hexdigest()}')
    print(f'image sha256 {hashlib.sha256(open(image, "rb").read()).hexdigest()}')
    print(f'file sha256 {hashlib.sha256(txt.encode()).hexdigest()}')
    print('read-only PT_LOADs: ' + ', '.join(f'[{lo:#x}, {hi:#x})' for lo, hi in ro))
    miss = sorted(ownb - cov)
    print(f'owned read-only ranges {len(oro)} of {len(own)}, owned read-only bytes {len(ownb)}, '
          f'pinned by a const cell {len(ownb & cov)}, unpinned {len(miss)}'
          + (f' (first {", ".join(hex(z) for z in miss[:4])})' if miss else ''))
    try:
        print('af0m.ro_counts: %d cell bytes in %d cells, from %d ranges' % af0m.ro_counts(txt, ro))
    except ValueError as e:
        print(f'af0m.ro_counts: REFUSED: {e}')
    sys.exit(1 if miss else 0)


if __name__ == '__main__':
    main()
