#!/usr/bin/env python3
"""check_globals_in_af0m.py TABLE AF0M_V [RUNTIME_TSV] -- confirm that a table printed by gen_globals_cells.py
is in lib/A/AF0m.v.

  DESC   every `z8 (ANum A) V` cell of the table is a cell of Definition Tfib_const_abs;
  SHADOW every `z1 (ANum A) V` cell of the table is a cell of Definition Tfib_const_shadow;
  ZERO   every `(LO, HI - LO)` pair of the table is a pair of Definition Tfib_zero_shadow (HI compared as text,
         so a name such as YImgTop.IMG_TOP must be the same name).

For each block it also says whether the table's sequence is the definition's whole list, a contiguous run of it,
the same order with other entries between, or none of these. With RUNTIME_TSV (header line, then addr, width,
value, section rows), every row must be a `z<width> (ANum addr) value` cell of Tfib_const_abs. Lines of TABLE
that start with '(*' or '#' are skipped.
Prints one count line per block; exit status 1 when a line is missing or a block is empty, 0 otherwise.
"""
import re
import sys

CELL = re.compile(r'\bz(1|2|4|8)\s+\(ANum\s+(0x[0-9a-fA-F]+|\d+)\)\s+(0x[0-9a-fA-F]+|\d+)')
PAIR = re.compile(r'\(\s*(0x[0-9a-fA-F]+)\s*,\s*([^,()]+?)\s*-\s*(0x[0-9a-fA-F]+)\s*\)')


def cells(text):
    return [(int(n), int(a, 0), int(v, 0)) for n, a, v in CELL.findall(text)]


def pairs(text):
    return [(int(lo, 0), hi.strip(), int(lo2, 0)) for lo, hi, lo2 in PAIR.findall(text)]


def definition(text, name):
    i = text.index('Definition %s ' % name)
    return text[i:text.index('].', i)]


def table(path):
    blocks, cur = {'DESC': [], 'SHADOW': [], 'ZERO': []}, None
    for line in open(path).read().split('\n'):
        s = line.strip()
        if not s or s.startswith('(*') or s.startswith('#'):
            continue
        if s in blocks:
            cur = s
            continue
        if cur is None:
            sys.exit('check_globals_in_af0m: %s: line before the first block marker: %r' % (path, line))
        got = pairs(s) if cur == 'ZERO' else cells(s)
        if len(got) != 1:
            sys.exit('check_globals_in_af0m: %s: not one entry in %s line %r' % (path, cur, line))
        blocks[cur].append(got[0])
    return blocks


def order(sub, full):
    if sub == full:
        return 'same sequence as the definition'
    for k in range(len(full) - len(sub) + 1):
        if full[k:k + len(sub)] == sub:
            return 'contiguous run at entries %d..%d of %d' % (k + 1, k + len(sub), len(full))
    pos = [full.index(x) for x in sub if x in full]
    if len(pos) == len(sub) and pos == sorted(pos) and len(set(pos)) == len(pos):
        return 'same order, entries %d..%d of %d, %d other entries between' % (
            pos[0] + 1, pos[-1] + 1, len(full), pos[-1] - pos[0] + 1 - len(pos))
    return 'not in the definition\'s order'


def main():
    if len(sys.argv) not in (3, 4):
        sys.exit(__doc__)
    blocks = table(sys.argv[1])
    t = open(sys.argv[2]).read()
    defs = {'DESC': ('Tfib_const_abs', cells), 'SHADOW': ('Tfib_const_shadow', cells),
            'ZERO': ('Tfib_zero_shadow', pairs)}
    bad = 0
    for blk in ('DESC', 'SHADOW', 'ZERO'):
        name, parse = defs[blk]
        full = parse(definition(t, name))
        have = set(full)
        miss = [x for x in blocks[blk] if x not in have]
        for x in miss:
            print('MISSING %s %r' % (blk, x))
        bad += len(miss) + (not blocks[blk])
        print('%-6s %d table lines, %d present in %s (%d entries), %d missing; %s'
              % (blk, len(blocks[blk]), len(blocks[blk]) - len(miss), name, len(full), len(miss),
                 order(blocks[blk], full)))
    if len(sys.argv) == 4:
        rows = [r.split('\t') for r in open(sys.argv[3]).read().split('\n')[1:] if r.strip()]
        want = [(int(w), int(a, 0), int(v, 0)) for a, w, v, _ in rows]
        have = set(cells(definition(t, 'Tfib_const_abs')))
        miss = [x for x in want if x not in have]
        for x in miss:
            print('MISSING RUNTIME %r' % (x,))
        bad += len(miss) + (not want)
        print('RUNTIME %d table rows, %d present in Tfib_const_abs, %d missing' % (len(want), len(want) - len(miss), len(miss)))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
