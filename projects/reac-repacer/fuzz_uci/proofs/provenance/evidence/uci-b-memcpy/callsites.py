#!/usr/bin/env python3
"""KIT=<cmpkit 86da41d3ef68 dir> callsites.py ELF TARGET_SYMBOL ROLE: every direct call (jal, or auipc+jalr bound by
bytecmp 1480ca2faea0's dataflow, through the kit's repin_check (e6883477399d; Img and targets text unchanged) `targets`, loaded by the kit's drvcmp
4d70e90bc1fa) whose target is TARGET_SYMBOL's entry, in every FUNC of ELF; one row per site: caller+offset, site address.
The header names ELF by ROLE and its sha256 (no path). Read-only."""
import sys, os, hashlib, importlib.util
KIT = os.environ['KIT']
spec = importlib.util.spec_from_file_location('drvcmp', os.path.join(KIT, 'drvcmp.py'))
dc = importlib.util.module_from_spec(spec); spec.loader.exec_module(dc)
Img, targets = dc.Img, dc._g['targets']
X = Img(sys.argv[1])
ent = X.fsym(sys.argv[2])[0]
print('# %s sha256 %s %s entry %#x' % (sys.argv[3], hashlib.sha256(open(sys.argv[1], 'rb').read()).hexdigest(), sys.argv[2], ent))
seen = set()
for v, z, n, t in sorted(X.syms):
    if t != 'STT_FUNC' or z <= 0 or (v, z) in seen:
        continue
    seen.add((v, z))
    b = X.rd(v, z)
    if b is None:
        continue
    w = dc.bc_words(b); tg = targets(v, b)
    for i, (o, x, ln) in enumerate(w):
        if ln == 4 and (x & 0x7f) in (0x6f, 0x67) and i in tg and tg[i][1] == ent and ((x >> 7) & 31) == 1:
            print('%s+%#x\t%#x' % (n, o, v + o))
