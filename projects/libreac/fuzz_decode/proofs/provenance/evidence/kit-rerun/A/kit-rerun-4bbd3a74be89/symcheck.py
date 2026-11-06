#!/usr/bin/env python3
"""symcheck.py KIT_DIR -- the selection check of the old record, re-measured on the twins the kit compares: strictcmp2
takes each function by NAME (Img.fsym), so each of the 7 names must name exactly ONE symbol in each image. Prints every
symbol carrying the name in C and in A (address, size, type), and whether the name is unique (the kit's own qname rule:
a name several symbols carry is only usable when its STT_FILE makes it unique)."""
import os, sys, importlib.util
KIT = os.path.abspath(sys.argv[1]); PAIRS = sys.argv[2]
sys.dont_write_bytecode = True
sp = importlib.util.spec_from_file_location('s2', os.path.join(KIT, 'strictcmp2.py'))
S = importlib.util.module_from_spec(sp); sp.loader.exec_module(S)
C = 'DONOR_TWIN'
A = 'DECODE_A_TWIN'
I = {'C': S.Img(C), 'A': S.Img(A)}
print('# C', C, S.sha(C)[:12]); print('# A', A, S.sha(A)[:12])
ok = True
for ln in open(PAIRS).read().splitlines()[1:]:
    if not ln.strip(): continue
    f = ln.split('\t')[0]
    out = []
    for k in 'CA':
        cop = [(v, z, ty) for (v, z, nm, ty) in I[k].syms if nm == f]
        out.append('%s: %s' % (k, ' '.join('%#x/%d/%s' % c for c in cop) or 'NONE'))
        if len(cop) != 1: ok = False
    print('%-100s %s  fsym C %s A %s' % (f[:100], '  '.join(out),
                                         I['C'].fsym(f) and hex(I['C'].fsym(f)[0]), I['A'].fsym(f) and hex(I['A'].fsym(f)[0])))
print('every name exactly one symbol in both images:', ok)
