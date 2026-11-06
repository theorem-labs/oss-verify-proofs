#!/usr/bin/env python3
"""Writes a symbol extract (.tsv) as `name addr size` text lines, the --old-syms form port_core tag d9e0589898fd reads.

Usage: syms_txt.py EXTRACT.tsv > OUT.txt

Keeps the rows y5-g8g7/resolve_code.py (tag abfd17f8b3d2) reads from the same extract: sized STT_FUNC and STT_OBJECT
symbols, in .symtab order. So both tags see the same donor symbols.
"""
import sys


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    out = []
    for line in open(sys.argv[1]):
        if line.startswith('#'):
            continue
        f = line.rstrip('\n').split('\t')
        name, value, size, kind = f[0], int(f[1], 16), int(f[2]), f[3]
        if kind in ('STT_FUNC', 'STT_OBJECT') and size > 0:
            out.append(f'{name} {value:x} {size}\n')
    sys.stdout.write(''.join(out))


if __name__ == '__main__':
    main()
