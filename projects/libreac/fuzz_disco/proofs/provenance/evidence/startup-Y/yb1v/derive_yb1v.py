#!/usr/bin/env python3
"""derive_yb1v.py SYMS IMAGE MUSL_SYMBOL GUARD_SYMBOL -- the four window values of YB1v.v, from the image's .text and
two named function symbols, printed as `MUSL_START MUSL_COUNT GUARD_START GUARD_COUNT` (gen_y.py's argument order).

The values of record were read by hand (nm / readelf). This script writes down the rules behind them and applies them:
  MUSL_START   the address of MUSL_SYMBOL (the first musl function; the caller names it)
  MUSL_COUNT   (end of IMAGE's .text section - MUSL_START) // 4, the formula of the full gen_y.py
  GUARD_START  the address of GUARD_SYMBOL
  GUARD_COUNT  the 4-byte instructions of GUARD_SYMBOL from its start through its first `ret` (jalr x0, 0(ra))
SYMS is nm text (`addr size type name`, hex address and size; `#` lines are skipped), as extract_syms.py writes it.
It refuses when a symbol is missing or not inside .text, or when the guard holds a 2-byte instruction or no `ret`.
"""
import struct
import sys
from elftools.elf.elffile import ELFFile

RET = 0x00008067


def main():
    syms_path, image, musl_name, guard_name = sys.argv[1:5]
    syms = {}
    for line in open(syms_path):
        p = line.split()
        if line.startswith('#') or len(p) < 4:
            continue
        syms.setdefault(p[3], set()).add((int(p[0], 16), int(p[1], 16)))
    for n in (musl_name, guard_name):
        if len(syms.get(n, ())) != 1:
            sys.exit('derive_yb1v: REFUSED: %s has %d entries in %s' % (n, len(syms.get(n, ())), syms_path))
    (musl, _), = syms[musl_name]
    (guard, gsize), = syms[guard_name]
    with open(image, 'rb') as f:
        t = ELFFile(f).get_section_by_name('.text')
        lo, data = t['sh_addr'], t.data()
    hi = lo + len(data)
    for n, a, size in ((musl_name, musl, 4), (guard_name, guard, gsize)):
        if not (lo <= a and a + size <= hi):
            sys.exit('derive_yb1v: REFUSED: %s %#x..%#x is not inside .text %#x..%#x' % (n, a, a + size, lo, hi))
    count = 0
    while True:
        if 4 * count >= gsize:
            sys.exit('derive_yb1v: REFUSED: no ret in %s' % guard_name)
        word = struct.unpack_from('<I', data, guard - lo + 4 * count)[0]
        if word & 3 != 3:
            sys.exit('derive_yb1v: REFUSED: a 2-byte instruction at %#x in %s' % (guard + 4 * count, guard_name))
        count += 1
        if word == RET:
            break
    print('%#x %d %#x %d' % (musl, (hi - musl) // 4, guard, count))


main()
