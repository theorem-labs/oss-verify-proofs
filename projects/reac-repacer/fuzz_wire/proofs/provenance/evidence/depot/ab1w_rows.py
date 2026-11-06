#!/usr/bin/env python3
"""ab1w_rows.py UNIT_AB1W KNOCK_AB1W TWIN NAME... -- take knock's AB1w symbol rows NAME (each line `Definition tfib_A_N :
Z := 0x... .  Definition tfib_E_N : Z := 0x... .`, as port_core relocated them onto fuzz_wire.asan, run-knock.sh) into
the unit's A/AB1w.v, after its tfib_A_StackStore_Alloc row; the unit's own rows are not touched.
Measured reason: knock's depot first-use chain (the Require closure files A/AD3*.v, here A/AD3g.v:163) names these
functions by knock's row names, and the unit's AB1w (grant lineage) has no row for them.
GATE: each NAME is absent from the unit's AB1w; each row's A value is the entry of a function the unstripped TWIN
(fuzz_wire.asan, sha256 d2f662a22962) DEFINES, and E = A + its st_size; the symtab line is printed. Refuses otherwise."""
import hashlib, re, sys
from elftools.elf.elffile import ELFFile

ua, ka, twin = sys.argv[1:4]
names = sys.argv[4:]
if hashlib.sha256(open(twin, 'rb').read()).hexdigest() != 'd2f662a229626fd402f1018631498190e800834bad837fa4027204b79088b128':
    sys.exit('ab1w_rows: twin pin mismatch')
st = ELFFile(open(twin, 'rb')).get_section_by_name('.symtab')
funcs = {s['st_value']: (s.name, s['st_size']) for s in st.iter_symbols() if s['st_info']['type'] == 'STT_FUNC' and s['st_value']}
u = open(ua).read().split('\n')
k = open(ka).read().split('\n')
rows = []
for n in names:
    if any(re.search(r'\bDefinition tfib_A_%s\b' % re.escape(n), x) for x in u):
        sys.exit('ab1w_rows: tfib_A_%s is already in the unit\'s AB1w' % n)
    ln = [x for x in k if re.search(r'\bDefinition tfib_A_%s : Z := (0x[0-9a-f]+)\.' % re.escape(n), x)]
    if len(ln) != 1:
        sys.exit('ab1w_rows: knock\'s AB1w has %d rows for %s' % (len(ln), n))
    a = int(re.search(r'tfib_A_%s : Z := (0x[0-9a-f]+)' % re.escape(n), ln[0]).group(1), 16)
    e = int(re.search(r'tfib_E_%s : Z := (0x[0-9a-f]+)' % re.escape(n), ln[0]).group(1), 16)
    if a not in funcs or a + funcs[a][1] != e:
        sys.exit('ab1w_rows: %s: %#x..%#x is not a function the twin defines' % (n, a, e))
    print('ab1w_rows: tfib_A_%s = %#x, tfib_E = %#x: twin symtab %s %#x %d' % (n, a, e, funcs[a][0], a, funcs[a][1]))
    rows.append(ln[0])
at = [i for i, x in enumerate(u) if re.search(r'\bDefinition tfib_A_StackStore_Alloc\b', x)]
if len(at) != 1:
    sys.exit('ab1w_rows: no single tfib_A_StackStore_Alloc row in the unit\'s AB1w')
u[at[0] + 1:at[0] + 1] = rows
open(ua, 'w').write('\n'.join(u))
print('ab1w_rows: %d row(s) taken after line %d' % (len(rows), at[0] + 1))
