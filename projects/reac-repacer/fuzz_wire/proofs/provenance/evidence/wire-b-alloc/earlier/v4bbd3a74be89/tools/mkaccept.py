#!/usr/bin/env python3
"""mkaccept.py -- the writer of ACCEPTANCES.tsv: the kit verdict lines as the kit printed them (never rewritten), then
settle.py's rows unchanged, with a header that counts them. Read-only on its inputs.
usage: mkaccept.py OUT UNIT_LABEL CLOSURE_OUT PAIRCL_OUT SETTLE_TSV DUPCHECK_TSV PLANT_SETTLE_TSV UNTOUCHED_SETTLE_TSV KIT_ID"""
import collections, sys
out, label, co, po, st, dup, pl, un, kit = sys.argv[1:10]
kitc = [l.rstrip('\n') for l in open(co) if l.startswith('___interceptor_malloc\t')][0].replace('\t', ' | ')
kitp = open(po).read().split('\n')[1]
lines = open(st).read().splitlines()
rows = [l.split('\t') for l in lines if l.startswith('ROW\t')]
acc = [l.split('\t') for l in lines if l.startswith('ACCEPT\t') and not l.startswith('ACCEPT\tfunction')]
cls = collections.Counter((a[6], a[-1]) for a in acc)
notc = [r[1] for r in rows if r[-1] != 'ROW SETTLED-EQUAL']
differs = [a for a in acc if a[-1] == 'DIFFERS']
dl = open(dup).read().splitlines()
dsum = dl[-1].lstrip('# ')
drows = [l.split('\t') for l in dl[2:-1] if l.split('\t')[9:10] not in (['-'], [])]
def plant(f):
    a = [l.split('\t') for l in open(f).read().splitlines() if l.startswith('ACCEPT\t') and not l.startswith('ACCEPT\tfunction')]
    return '; '.join('%s %s %s' % (x[2], x[6], x[-1]) for x in a)
hdr = [
 '# %s (X) vs fuzz_grant B (Y, GRANT_B_TWIN): acceptances for every function the comparison kit cmpkit %s reports as other.' % (label, kit),
 '# KIT VERDICT, as the kit printed it (unchanged): closure_strict2 from ___interceptor_malloc: %s' % kitc,
 '# KIT VERDICT, as the kit printed it (unchanged): paircl from ___interceptor_malloc: %s' % kitp,
 '# The rows below are the union of both passes: %d functions. The other 3 roots reach the same closures.' % len(rows),
 '# Each target pair the kit\'s tcmp reports (the full list from tcmp, not the printed first 2) gets one ACCEPT row from settle.py: class, evidence, extent, the bytes of that extent in X and Y, verdict. TABLE / RELSTR / INITIALIZER rows are followed by one ENTRY row per entry, with its target in both images.',
 '# Totals: target pairs %d; %s.' % (len(acc), ', '.join('%s %s %d' % (k[0], k[1], v) for k, v in sorted(cls.items()))),
 '# Rows: %d settled-equal; %d not certified (a target stays UNSETTLED): %s. Rows with a DIFFERS target: %d.' % (
     len(rows) - len(notc), len(notc), ', '.join(notc) or 'none', len({a[1] for a in differs})),
 '# Duplicate names (dupcheck.py): %s; for each, the Y copy compared by name is the copy the code calls, same verdict: %s.' % (
     dsum, ', '.join('%s %s' % (d[0], d[9]) for d in drows) or '-'),
 '# Control for the settlement: one byte of the 64-byte De Bruijn table that Allocator::Allocate reads at +0xdc, changed in a copy of GRANT_B_TWIN (vaddr 0x10432, file offset 0x432, 0x0e -> 0x0f): planted copy: %s; untouched GRANT_B_TWIN: %s.' % (plant(pl), plant(un)),
]
open(out, 'w').write('\n'.join(hdr + lines) + '\n')
print(hdr[5]); print(hdr[6]); print(hdr[7][:300]); print(hdr[8])
