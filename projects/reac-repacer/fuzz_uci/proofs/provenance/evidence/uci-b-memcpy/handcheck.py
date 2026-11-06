#!/usr/bin/env python3
"""handcheck.py LUIUSE_OUT [LUIUSE_OUT ...] HAND_TSV: every HAND use luiuse.py printed (in any of the outputs) (its text before ' via ') has a row in HAND_TSV,
and every HAND_TSV row is used. Prints the count per row; exit 1 on a missing or unused row, or on any luiuse row
whose verdict is not NUMBER / NUMBER+HAND or whose X and Y disagree."""
import sys, re, collections
reasons = {}
for l in open(sys.argv[-1]).read().split('\n')[1:]:
    if l.strip():
        k, r = l.split('\t', 1); reasons[k] = r
used = collections.Counter(); bad = []
for l in [l for f in sys.argv[1:-1] for l in open(f).read().split('\n')[1:]]:
    p = l.split('\t')
    if len(p) < 6: continue
    if p[3] not in ('NUMBER', 'NUMBER+HAND') or p[4] != 'True': bad.append('row %s %s: %s %s' % (p[0], p[1], p[3], p[4]))
    for u in filter(None, p[5].split(' | ')):
        k = re.sub(r' via .*', '', u).strip()
        if k in reasons: used[k] += 1
        else: bad.append('no reason: ' + k)
for k in reasons:
    print('%d\t%s' % (used[k], k))
    if not used[k]: bad.append('unused reason: ' + k)
for b in bad: print('FAIL', b)
print('hand keys %d, uses %d, failures %d' % (len(reasons), sum(used.values()), len(bad)))
sys.exit(1 if bad else 0)
