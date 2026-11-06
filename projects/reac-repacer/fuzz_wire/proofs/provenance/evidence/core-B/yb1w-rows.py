#!/usr/bin/env python3
"""yb1w-rows.py UNIT_YB1W KNOCK_YB1W TWIN TWIN_SHA256 NAME... : the image-B twin of the image-A core's ab1w_rows.py.
Take knock's image-B symbol rows NAME (each line `Definition tfib_A_N : Z := 0x... .  Definition tfib_E_N : Z := 0x... .`,
as port_core relocated knock's released lib/AU/YB1w.v onto the unit's asan-ubsan image, run-knockB.sh) into the unit's
B/YB1w.v, after its tfib_A_StackStore_Alloc row; the unit's own rows are not touched.
Reason (the image-A core's, measured there): knock's depot first-use chain (the Require-closure files of the empty-depot
form) names these functions by knock's row names, and the unit's YB1w (grant lineage) has no row for them.
GATE: TWIN's sha256 is TWIN_SHA256; each NAME is absent from the unit's YB1w; each row's A value is the entry of a function
the unstripped TWIN defines, and E = A + its st_size; the symtab line is printed. Writes no comment. Refuses otherwise."""
import hashlib, re, sys
from elftools.elf.elffile import ELFFile

ub, kb, twin, pin = sys.argv[1:5]
names = sys.argv[5:]
if hashlib.sha256(open(twin, 'rb').read()).hexdigest() != pin:
    sys.exit('yb1w-rows: twin pin mismatch')
st = ELFFile(open(twin, 'rb')).get_section_by_name('.symtab')
funcs = {s['st_value']: (s.name, s['st_size']) for s in st.iter_symbols() if s['st_info']['type'] == 'STT_FUNC' and s['st_value']}
u = open(ub).read().split('\n')
k = open(kb).read().split('\n')
rows = []
for n in names:
    if any(re.match(r'Definition tfib_A_%s : ' % re.escape(n), l) for l in u):
        sys.exit("yb1w-rows: tfib_A_%s is already in the unit's YB1w" % n)
    ln = [l for l in k if re.match(r'Definition tfib_A_%s : Z := 0x[0-9a-f]+\.\s+Definition tfib_E_%s : Z := 0x[0-9a-f]+\.$'
                                   % (re.escape(n), re.escape(n)), l)]
    if len(ln) != 1:
        sys.exit("yb1w-rows: knock's YB1w has %d rows for %s" % (len(ln), n))
    a, e = [int(x, 16) for x in re.findall(r':= (0x[0-9a-f]+)\.', ln[0])]
    if a not in funcs or a + funcs[a][1] != e:
        sys.exit('yb1w-rows: %s: %#x..%#x is not a function the twin defines' % (n, a, e))
    print('yb1w-rows: tfib_A_%s = %#x, tfib_E = %#x: twin symtab %s %#x %d' % (n, a, e, funcs[a][0], a, funcs[a][1]))
    rows.append(ln[0])
at = [i for i, l in enumerate(u) if l.startswith('Definition tfib_A_StackStore_Alloc : ')]
if len(at) != 1:
    sys.exit("yb1w-rows: no single tfib_A_StackStore_Alloc row in the unit's YB1w")
u[at[0] + 1:at[0] + 1] = rows
open(ub, 'w').write('\n'.join(u))
print('yb1w-rows: %d row(s) taken after line %d' % (len(rows), at[0] + 1))
