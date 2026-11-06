#!/usr/bin/env python3
"""triage_unexplained.py FUNNEL.out SAFE.tsv -- check every value funnel.py leaves UNEXPLAINED is a recorded disco-own
value.

funnel.py classifies the donor_decimals rows and prints the rows it cannot explain (the `--- UNEXPLAINED rows` block,
one row per line, the decimal value in column 4). Each distinct such value must appear in SAFE.tsv (a per-value table,
`value<TAB>hex<TAB>files<TAB>reason`, `#` comments), where it was judged disco-own by hand. Prints the count and exits 0
when every UNEXPLAINED value is listed, 1 (naming each one) otherwise: an unlisted UNEXPLAINED value is a candidate
donor-stale decimal, a defect to report.
"""
import sys

funnel, safe = sys.argv[1:3]
want = {}
for l in open(safe):
    if l.startswith('#') or not l.strip():
        continue
    f = l.rstrip('\n').split('\t')
    want[int(f[0])] = f[3] if len(f) > 3 else ''
rows, vals = [], {}
seen = False
for l in open(funnel):
    if l.startswith('--- UNEXPLAINED'):
        seen = True
        continue
    if seen and l.strip() and not l.startswith('#'):
        c = l.rstrip('\n').split('\t')
        if len(c) > 4:
            rows.append(c)
            vals.setdefault(int(c[3]), []).append(c[2])
missing = sorted(v for v in vals if v not in want)
print(f'UNEXPLAINED {len(rows)} rows, {len(vals)} values; all recorded disco-own: {not missing}')
for v in sorted(vals):
    tag = want.get(v, 'NOT IN SAFE TABLE -- candidate donor-stale decimal')
    print(f'  {v} ({v:#x}) x{len(vals[v])}: {tag}')
sys.exit(1 if missing else 0)
