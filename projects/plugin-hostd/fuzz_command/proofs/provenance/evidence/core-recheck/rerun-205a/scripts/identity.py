#!/usr/bin/env python3
"""Identity check: this re-run's 0d24592683b6 runs against the rerun-0d24 record.

Usage: identity.py RUNS_DIR RECORD_DIR OUT.txt
For each of RA RB PA-base PA-plant PB-base PB-plant: the FLAGGED line of RUNS_DIR/<run>-0d24/stderr.txt against the
record's flagged.txt line `<run>-0d24: FLAGGED ...` (byte-equal), the exit code (rc=4), and the sha256 of full.tsv's
rows without its `#` header block (computed as rerun-0d24's diff_rows.py computes it) against the record's
counts-R?.txt / plants.txt. Exit 0 only when every check is equal.
"""
import hashlib
import os
import re
import sys

runs, rec, out = sys.argv[1:4]
RUNS = ['RA', 'RB', 'PA-base', 'PA-plant', 'PB-base', 'PB-plant']
flag_rec = {}
for l in open(os.path.join(rec, 'flagged.txt'), encoding='utf-8'):
    m = re.match(r'(\S+)-0d24: (FLAGGED .*)$', l.rstrip('\n'))
    if m:
        flag_rec[m.group(1)] = m.group(2)
sha_rec = {}
for g in ('RA', 'RB'):
    for l in open(os.path.join(rec, f'counts-{g}.txt'), encoding='utf-8'):
        m = re.match(r'new \S+-0d24: (\d+) rows .*without the # header block ([0-9a-f]{12})', l)
        if m:
            sha_rec[g] = (int(m.group(1)), m.group(2))
for l in open(os.path.join(rec, 'plants.txt'), encoding='utf-8'):
    m = re.match(r'new (\S+)-0d24: (\d+) rows .*without the # header block ([0-9a-f]{12})', l)
    if m:
        sha_rec[m.group(1)] = (int(m.group(2)), m.group(3))


def rows_sha(p):
    h = hashlib.sha256()
    n = -1
    with open(p, encoding='utf-8', errors='replace', newline='') as f:
        for line in f:
            if line.startswith('#'):
                continue
            h.update(line.encode('utf-8', 'replace'))
            n += 1
    return n, h.hexdigest()[:12]


bad = 0
lines = []
for r in RUNS:
    d = os.path.join(runs, f'{r}-0d24')
    fl = next((l.rstrip('\n') for l in open(os.path.join(d, 'stderr.txt'), encoding='utf-8')
               if l.startswith('FLAGGED')), '')
    rc = open(os.path.join(d, 'rc')).read().split()[0]
    n, s = rows_sha(os.path.join(d, 'full.tsv'))
    ok_f = fl == flag_rec.get(r)
    ok_s = (n, s) == sha_rec.get(r)
    ok_rc = rc == 'rc=4'
    bad += not (ok_f and ok_s and ok_rc)
    lines.append(f'{r}: FLAGGED line {"EQUAL" if ok_f else "DIFFERS"} to the record; {rc}; rows {n}, sha256 of the '
                 f'rows without the # header {s} (record {sha_rec.get(r, ("?", "?"))[1]}: '
                 f'{"EQUAL" if ok_s else "DIFFERS"})')
    if not ok_f:
        lines.append(f'  here:   {fl}\n  record: {flag_rec.get(r)}')
lines.append(f'identity: {"6 of 6 runs equal the record" if not bad else f"{bad} run(s) differ"}')
open(out, 'w').write('\n'.join(lines) + '\n')
print('\n'.join(lines))
sys.exit(1 if bad else 0)
