#!/usr/bin/env python3
"""fulldiff.py PAIRS.TSV -- the FULL differing-target list of every pair, taken from strictcmp2's tcmp directly (not
from any printed output): tcmp returns (verdict, counts, accepted-target counts, diff) and `diff` holds EVERY
reported target, one tuple per word: (word offset, donor resolution, decode resolution, kind, info). Printed in full,
with the kinds counted, so no row can be settled on a truncated list (cmpkit's closure_strict2.py:88 / paircl.py:67
print only the first 2 per function; this is tcmp's own list, which those printers truncate)."""
import collections, importlib.util, os, sys
PAIRS = sys.argv[1]
KIT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cmpkit-4bbd3a74be89')
sys.dont_write_bytecode = True
sp = importlib.util.spec_from_file_location('s2', os.path.join(KIT, 'strictcmp2.py'))
S = importlib.util.module_from_spec(sp); sp.loader.exec_module(S)
A = 'DECODE_A_TWIN'
C = 'DONOR_TWIN'
I = {'C': S.Img(C), 'A': S.Img(A)}
print('# C', C, S.sha(C)[:12]); print('# A', A, S.sha(A)[:12])
print('# strictcmp2', S.sha(os.path.join(KIT, 'strictcmp2.py'))[:12])
tot = collections.Counter()
for l in open(PAIRS).read().splitlines()[1:]:
    if not l.strip(): continue
    r = l.split('\t'); fn, da, aa, size = r[0], int(r[1], 16), int(r[2], 16), int(r[3])
    fb = []
    v, c, t3, diff = S.tcmp(I, 'C', da, 'A', aa, size, fb)
    kinds = collections.Counter(d[3] for d in diff)
    tot.update(kinds); tot['rows'] += len(diff)
    print('\n%s\n  %s pcrel/real/unmeasured %s; accepted targets (full, gotval/tlsindex, cstr) %s' % (fn, v, c, t3))
    print('  tcmp returned %d differing/unmeasured target entries in FULL: %s' % (len(diff), dict(kinds) or 'none'))
    for d in diff:
        print('    %-8s %-40s %-40s %s' % (d[0], str(d[1])[:40], str(d[2])[:40], d[3]))
print('\nTOTAL over the 7 pairs: %d entries %s' % (tot.pop('rows', 0), dict(tot)))
print('UNMEASURED entries (kind unmeasured / got-unreadable / one-side):',
      sum(tot[k] for k in ('unmeasured', 'got-unreadable', 'one-side')))
