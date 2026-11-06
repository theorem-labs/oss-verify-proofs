#!/usr/bin/env python3
"""ab1w_swaps.py AB1W.v TWIN LIB OUT.tsv -- the crossed-pair check of AB1w's cells: for each `Definition
tfib_<S>_<NAME> : Z := V.` of AB1W.v with S in A (a start), E (an end) or D (a data start), the NAME TAIL is compared
with the symbols that are AT V in TWIN (the unstripped image the cell describes, read from its .symtab):
  A / D: the symbols that start at V, else the one that covers V;
  E:     the symbols that end at V (start + size = V), else the one that covers V - 1.
A symbol's words are the identifiers of its name: for an Itanium-mangled C++ name, every <length><identifier> run in
it (namespaces, classes, the function, template and argument types); for a C name, its `_`-separated parts. The
tail's words are its `_`-separated parts, without numerals and hex runs (`_71714`) and the generic words of
GENERIC. score(cell, V') = the share of the tail's words (case-insensitive) that are words of a symbol at V', the best
symbol counted.
A CROSSED PAIR is two cells of the same kind (A, E or D), c1 at V1 and c2 at V2 with V1 != V2, such that
score(c1, V2) > score(c1, V1) and score(c2, V1) > score(c2, V2): each name reads better at the other's value. Every
crossed pair is written, with each cell's readers (the files of LIB, AB1W.v left out, whose text holds the cell's
name as a word) and the symbols at both values. The run also prints the counts of the cells whose tail scores 1 at
their own value, below 1, and 0. It reads only; it changes nothing."""
import bisect
import os
import re
import sys

# elftools from the environment (PYTHONPATH)
from elftools.elf.elffile import ELFFile  # noqa: E402

CELL = re.compile(r'Definition (tfib_([AED])_(\w+))\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+|\d+)\s*\.')
GENERIC = {'helper', 'thunk', 'part', 'cold', 'constprop', 'isra', 'impl', 'fn', 'the', 'of', 'by', 'at', 'a'}
HEXRUN = re.compile(r'^(?:[0-9]+|[0-9a-f]{4,})$')


def words_of_symbol(name):
    if name.startswith('_Z'):
        out, i = set(), 0
        while i < len(name):
            m = re.match(r'(\d+)', name[i:])
            if m:
                n, j = int(m.group(1)), i + len(m.group(1))
                ident = name[j:j + n]
                if n > 0 and len(ident) == n and re.match(r'^[A-Za-z_][A-Za-z0-9_]*$', ident):
                    out.add(ident.strip('_').lower())
                    out.update(p.lower() for p in ident.split('_') if p)
                    i = j + n
                    continue
                i = j
                continue
            i += 1
        return out
    base = name.split('.')[0]
    return {p.lower() for p in base.split('_') if p} | {base.strip('_').lower()}


def tail_words(tail):
    return [w.lower() for w in tail.split('_') if w and not HEXRUN.match(w.lower()) and w.lower() not in GENERIC]


def main():
    ab1w, twin, lib, out = sys.argv[1:5]
    text = open(ab1w, encoding='utf-8').read()
    cells = [(m.group(1), m.group(2), m.group(3), int(m.group(4), 0)) for m in CELL.finditer(text)]
    syms = []
    for s in ELFFile(open(twin, 'rb')).get_section_by_name('.symtab').iter_symbols():
        if s.name and s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT', 'STT_NOTYPE', 'STT_TLS') \
                and not s.name.startswith('$') and s['st_shndx'] != 'SHN_UNDEF':
            syms.append((s['st_value'], s['st_size'], s.name))
    syms.sort()
    starts = [a for a, _, _ in syms]
    by_start, by_end = {}, {}
    for a, z, n in syms:
        by_start.setdefault(a, []).append(n)
        by_end.setdefault(a + z, []).append(n) if z else None

    def covering(v):
        i = bisect.bisect_right(starts, v) - 1
        best = None
        while i >= 0 and starts[i] > v - 0x100000:
            a, z, n = syms[i]
            if a <= v < a + z and (best is None or z < best[1]):
                best = (a, z, n)
            i -= 1
        return [best[2]] if best else []

    def at(kind, v):
        if kind == 'E':
            return by_end.get(v) or covering(v - 1)
        return by_start.get(v) or covering(v)

    wcache = {}

    def score(tail, kind, v):
        tw = tail_words(tail)
        if not tw:
            return None, '-'
        best, bn = 0.0, '-'
        for n in at(kind, v):
            w = wcache.setdefault(n, words_of_symbol(n))
            s = sum(1 for x in tw if x in w) / len(tw)
            if s > best:
                best, bn = s, n
        return best, bn

    own = {}
    for name, kind, tail, v in cells:
        own[name] = score(tail, kind, v)
    files = []
    for dp, _, fs in os.walk(lib):
        for f in fs:
            p = os.path.join(dp, f)
            if f.endswith('.v') and os.path.abspath(p) != os.path.abspath(ab1w):
                files.append((os.path.relpath(p, lib), open(p, encoding='utf-8', errors='replace').read()))

    def readers(name):
        pat = re.compile(r'(?<![\w.])' + re.escape(name) + r'(?![\w])')
        return [f for f, t in files if pat.search(t)]

    rows = []
    for kind in 'AED':
        cs = [c for c in cells if c[1] == kind]
        for i, (n1, _, t1, v1) in enumerate(cs):
            s11 = own[n1][0]
            if s11 is None or s11 == 1.0:
                continue
            for n2, _, t2, v2 in cs[i + 1:]:
                if v1 == v2:
                    continue
                s22 = own[n2][0]
                if s22 is None:
                    continue
                s12, sym12 = score(t1, kind, v2)
                s21, sym21 = score(t2, kind, v1)
                if s12 > s11 and s21 > s22:
                    rows.append([kind, n1, hex(v1), '%.2f' % s11, '%.2f' % s12, own[n1][1], n2, hex(v2), '%.2f' % s22,
                                 '%.2f' % s21, own[n2][1], ' '.join(readers(n1)) or '-', ' '.join(readers(n2)) or '-'])
    with open(out, 'w') as o:
        o.write('\t'.join(['kind', 'cell 1', 'value 1', 'cell 1 score at own value', 'cell 1 score at value 2',
                           'symbol at value 1', 'cell 2', 'value 2', 'cell 2 score at own value',
                           'cell 2 score at value 1', 'symbol at value 2', 'readers of cell 1', 'readers of cell 2'])
                + '\n')
        for r in rows:
            o.write('\t'.join(r) + '\n')
    full = sum(1 for n, *_ in cells if own[n][0] == 1.0)
    zero = sum(1 for n, *_ in cells if own[n][0] == 0.0)
    none = sum(1 for n, *_ in cells if own[n][0] is None)
    read = sum(1 for r in rows if r[11] != '-' or r[12] != '-')
    print('ab1w_swaps: %d cell(s) (A %d, E %d, D %d); tail scores 1 at its own value: %d, below 1: %d, 0: %d, no '
          'word: %d; crossed pairs: %d, of which a proof reads a cell: %d' % (
              len(cells), *(sum(1 for c in cells if c[1] == k) for k in 'AED'), full, len(cells) - full - none, zero,
              none, len(rows), read))


if __name__ == '__main__':
    main()
