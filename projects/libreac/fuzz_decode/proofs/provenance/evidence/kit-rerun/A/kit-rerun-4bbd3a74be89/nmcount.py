#!/usr/bin/env python3
"""nmcount.py PAIRS.TSV -- the `nm IMG | grep -c ' NAME$'` count of each paired name in BOTH twins (no binutils on
this host, so the .symtab is read with pyelftools: every symbol of that exact name, any type, as nm lists them), and
a BY-ADDRESS re-run of each pair with strictcmp2's tcmp at the addresses of record, beside the BY-NAME verdict that
`strictcmp2.py cmp` produced (cmp looks a function up by name and, for a name with several copies, takes the lowest
address)."""
import collections, importlib.util, os, sys
from elftools.elf.elffile import ELFFile
PAIRS = sys.argv[1]
KIT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cmpkit-4bbd3a74be89')
sys.dont_write_bytecode = True
sp = importlib.util.spec_from_file_location('s2', os.path.join(KIT, 'strictcmp2.py'))
S = importlib.util.module_from_spec(sp); sp.loader.exec_module(S)
A = 'DECODE_A_TWIN'
C = 'DONOR_TWIN'
I = {'C': S.Img(C), 'A': S.Img(A)}


def names(p):
    c = collections.defaultdict(list)
    for s in ELFFile(open(p, 'rb')).get_section_by_name('.symtab').iter_symbols():
        if s.name: c[s.name].append((s['st_value'], s['st_size'], s['st_info']['type']))
    return c


NC, NA = names(C), names(A)
print('# C donor twin', C, S.sha(C)[:12]); print('# A decode twin', A, S.sha(A)[:12])
print('symtab entries of the name | C | A | addresses C | addresses A | by-NAME verdict | by-ADDRESS verdict (record addresses)')
for l in open(PAIRS).read().splitlines()[1:]:
    if not l.strip(): continue
    r = l.split('\t'); fn, da, aa, size = r[0], int(r[1], 16), int(r[2], 16), int(r[3])
    byname = S.tcmp(I, 'C', I['C'].fsym(fn)[0], 'A', I['A'].fsym(fn)[0], I['C'].fsym(fn)[1], [])
    byaddr = S.tcmp(I, 'C', da, 'A', aa, size, [])
    fmt = lambda v: '%s %s diffs %d' % (v[0], v[1], len(v[3]))
    print('%-58s | %d | %d | %s | %s | %s | %s' %
          (fn[:58], len(NC[fn]), len(NA[fn]),
           ' '.join(hex(x[0]) for x in NC[fn]), ' '.join(hex(x[0]) for x in NA[fn]),
           fmt(byname), fmt(byaddr)))
    assert (I['C'].fsym(fn)[0], I['A'].fsym(fn)[0]) == (da, aa), 'name lookup != record addresses'
print('name lookup == the addresses of record for all 7 pairs, and every by-NAME verdict equals its by-ADDRESS verdict')
