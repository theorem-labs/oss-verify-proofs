#!/usr/bin/env python3
"""mkaccept.py -- the writer of ACCEPTANCES.tsv: the kit verdict lines as the kit printed them (never rewritten), then
settle.py's rows unchanged, then one LUI row per target the kit leaves unsettled as `lui-in-section`, carrying the hand
trace's classes for that lui word (luitrace.py; the rows themselves stay in luitrace.tsv), then the plant verdicts.
Read-only on its inputs.
usage: mkaccept.py OUT UNIT_LABEL CLOSURE_OUT PAIRCL_OUT SETTLE_TSV DUPCHECK_TSV PLANT_SETTLE_TSV UNTOUCHED_SETTLE_TSV
       KIT_ID LUIROWS_TSV LUITRACE_TSV PLANTS_OUT"""
import collections, sys
out, label, co, po, st, dup, pl, un, kit = sys.argv[1:10]
lrp, ltp, plp = sys.argv[10:13]
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

# the hand traces: the lui word each kit target is formed from (luirows.tsv), and the rows of that word (luitrace.tsv)
luiof = {}
for l in open(lrp):
    f = l.rstrip('\n').split('\t')
    if f[0] != 'TARGET': continue
    w = f[3].split('`')[0].replace('lui at ', '').strip()
    luiof[(f[1], f[2] if f[2].startswith('+') else '+' + f[2])] = w
tr = collections.defaultdict(list); luival = {}; trace = {}; nouse = {}
for l in open(ltp):
    f = l.rstrip('\n').split('\t')
    if f[0] == 'LUI': luival[(f[1], f[2])] = (f[3], f[4])
    elif f[0] == 'TRACE': trace[(f[1], f[2])] = f[3]
    elif f[0] == 'ROW': tr[(f[1], f[2])].append((f[3], f[5], f[6]))
    elif f[0] in ('NOTARG', 'NOTECALL', 'NOTRET'): tr[(f[1], f[2])].append((f[3] if len(f) > 3 else '-', f[0], f[-1]))
    elif f[0] in ('CMPONLY', 'NOUSE'): nouse[(f[1], f[2])] = f[0]
luiacc = []
for a in acc:
    if len(a) < 4 or a[3] != 'lui-in-section': continue
    fn, off = a[1], a[2] if a[2].startswith('+') else '+' + a[2]
    w = luiof.get((fn, off), off)
    key = (fn, w)
    rs = tr.get(key, [])
    c = collections.Counter(r[1] for r in rs)
    bad = [r for r in rs if r[1] == 'DIFFERS']
    v = ('DIFFERS' if bad else
         'COMPARE-ONLY: no row; the trace holds a branch / compare' if not rs and nouse.get(key) == 'CMPONLY' else
         'NO USE: no row and no compare (the value is not read)' if not rs and nouse.get(key) == 'NOUSE' else
         'HAND-TRACED: %d use(s), %d certified, %d not certified' %
         (len(rs), sum(v2 for k2, v2 in c.items() if k2.startswith('(') or k2 == 'STORE-UNREAD'), c.get('NOT CERTIFIED', 0)))
    luiacc.append('LUI\t%s\t%s\t%s\t%s\t%s\t%s\t%s' % (
        fn, off, w, luival.get(key, ('-', '-'))[0], luival.get(key, ('-', '-'))[1],
        ', '.join('%s %d' % kv for kv in sorted(c.items())) or 'no row',
        v))
ltot = collections.Counter(); meetv = collections.Counter()
for l in open(ltp):
    f = l.rstrip('\n').split('\t')
    if f[0] == 'ROW': ltot[f[5]] += 1
    elif f[0] in ('NOTARG', 'NOTECALL', 'NOTRET', 'UNMEASURED', 'NOY', 'CMPONLY', 'NOUSE', 'UNREACH'): ltot[f[0]] += 1
    elif f[0] == 'LUI': ltot['lui words traced'] += 1
    elif f[0] == 'LUIMEET': meetv[f[5].split(':')[0].split(',')[0]] += 1
plants = [l.rstrip('\n') for l in open(plp) if l.startswith(('PLANT-A', 'PLANT-B', 'PLANT-C'))]
hdr = [
 '# %s (X) vs fuzz_grant B (Y, GRANT_B_TWIN): acceptances for every function the comparison kit cmpkit %s reports as other.' % (label, kit),
 '# KIT VERDICT, as the kit printed it (unchanged): closure_strict3 from ___interceptor_malloc: %s' % kitc,
 '# KIT VERDICT, as the kit printed it (unchanged): paircl from ___interceptor_malloc: %s' % kitp,
 '# The rows below are the union of both passes: %d functions. The other 3 roots reach the same closures.' % len(rows),
 '# Each target pair the kit\'s tcmp reports (the full list from tcmp, not the printed first 2) gets one ACCEPT row from settle.py: class, evidence, extent, the bytes of that extent in X and Y, verdict. TABLE / RELSTR / INITIALIZER rows are followed by one ENTRY row per entry, with its target in both images.',
 '# Totals: target pairs %d; %s.' % (len(acc), ', '.join('%s %s %d' % (k[0], k[1], v) for k, v in sorted(cls.items()))),
 '# Rows: %d settled-equal; %d not certified (a target stays UNSETTLED): %s. Rows with a DIFFERS target: %d.' % (
     len(rows) - len(notc), len(notc), ', '.join(notc) or 'none', len({a[1] for a in differs})),
 '# Duplicate names (dupcheck.py): %s; for each, the Y copy compared by name is the copy the code calls, same verdict: %s.' % (
     dsum, ', '.join('%s %s' % (d[0], d[9]) for d in drows) or '-'),
 '# Control for the settlement: one byte of the 64-byte De Bruijn table that Allocator::Allocate reads at +0xdc, changed in a copy of GRANT_B_TWIN (vaddr 0x10432, file offset 0x432, 0x0e -> 0x0f): planted copy: %s; untouched GRANT_B_TWIN: %s.' % (plant(pl), plant(un)),
 '# LUI rows (one per target the kit leaves as lui-in-section, %d of them): the hand trace of that lui word, by classes '
 '(i) CALL ARGUMENT / (ii) RETURN / (iii) DISPLACEMENT / (iv) STORE / STORE-UNREAD / NOT CERTIFIED, and the measured non-rows NOTARG / '
 'NOTECALL / NOTRET. Every use of the value is a row of luitrace.tsv; this file keeps the counts.' % len(luiacc),
 '# Hand trace over the whole compared set (luitrace.tsv, every lui of every compared function, not only these targets): %s.' % (
     ', '.join('%s %d' % kv for kv in sorted(ltot.items()))),
 '# lui+lui->base (luitrace.tsv LUIMEET lines: a load / store / jalr / AMO base that two or more lui values reach): %s.' % (
     ('%d sites: ' % sum(meetv.values()) + ', '.join('%s %d' % kv for kv in sorted(meetv.items()))) if meetv else 'none'),
 '# Plants that must be caught (a, c) or refused (b) (plants.out): %s' % ' | '.join(p.replace('\t', ' ') for p in plants if 'VERDICT' in p or p.startswith(('PLANT-A\t', 'PLANT-B\t', 'PLANT-C\t'))),
]
open(out, 'w').write('\n'.join(hdr + lines + luiacc) + '\n')
for h in hdr[5:]: print(h[:400])
