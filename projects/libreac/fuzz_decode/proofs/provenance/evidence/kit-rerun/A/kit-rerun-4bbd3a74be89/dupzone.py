#!/usr/bin/env python3
"""dupzone.py NUMERALS.TSV RESOLVE.TSV PAIRS.TSV -- read-only: every STT_FUNC name that decode A (and the donor)
carries more than once, and whether ANY address of this record lies inside one of those functions: the re-run's own
numerals and every address the 47 released headers cite. funcpair.py d37a0f9a14fb keeps only the first symtab entry
per name, so a duplicated name is where it can take the wrong same-size copy."""
import collections, sys
from elftools.elf.elffile import ELFFile
NUM, RES, PAIRS = sys.argv[1:4]
A = 'DECODE_A_TWIN'
C = 'DONOR_TWIN'


def dups(p):
    c = collections.defaultdict(list)
    for s in ELFFile(open(p, 'rb')).get_section_by_name('.symtab').iter_symbols():
        if s['st_info']['type'] == 'STT_FUNC' and s.name:
            c[s.name].append((s['st_value'], s['st_size']))
    return {k: sorted(set(v)) for k, v in c.items() if len({a for a, _ in v}) > 1}


dA, dC = dups(A), dups(C)
print('# decode A duplicated STT_FUNC names:', {k: [(hex(a), z) for a, z in v] for k, v in dA.items()})
print('# donor duplicated STT_FUNC names:', {k: [(hex(a), z) for a, z in v] for k, v in dC.items()})
rng = [(a, a + z, k) for k, v in dA.items() for a, z in v]


def hit(vals):
    return [(hex(v), k, hex(lo)) for v in vals for lo, hi, k in rng if lo <= v < hi]


placed = sorted({int(l.split('\t')[2], 16) for l in open(NUM).read().splitlines()[1:] if l.strip()})
print('# 417 numerals (%d distinct placed values) inside a duplicated-name function:' % len(placed),
      hit(placed) or 'none')
cited = sorted({int(c, 0) if c.startswith('0x') else int(c)
                for c in (l.split('\t')[3] for l in open(RES).read().splitlines()[1:] if l.strip())})
print('# header-cited values (%d distinct) inside a duplicated-name function:' % len(cited), hit(cited) or 'none')
pairs = [l.split('\t')[0] for l in open(PAIRS).read().splitlines()[1:] if l.strip()]
print('# any of the 7 paired names duplicated:', [p for p in pairs if p in dA or p in dC] or 'none')
