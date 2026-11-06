#!/usr/bin/env python3
"""compare.py REC NEW OUT: compare two port_core work dirs of one unit (REC = run of record, NEW = cross-check run).

Writes to OUT:
  new-fail-rows.tsv   check.tsv rows of NEW whose column 5 starts FAIL and that REC does not have
                      (key: file, line, old, new, FAIL class)
  gone-fail-rows.tsv  the same, REC rows that NEW does not have
  check-diff.tsv      every check.tsv / review.tsv row that is in one run only (multiset difference)
  stage-out-cells.tsv every stage-out line that differs, other than the provenance line whose only change is the tool
                      sha (`by port_core <sha12>`); one row per differing numeral or text cell
Prints the counts."""
import collections
import os
import re
import sys

REC, NEW, OUT = sys.argv[1:4]
OLD_SHA, NEW_SHA = '83f5203d2a2f', 'e0e94a04094b'


def rows(p):
    return [l.rstrip('\n').split('\t') for l in open(p)]


def fail_class(r):
    return r[4].split(' ')[1] if len(r) > 4 and r[4].startswith('FAIL ') else ''


def key(r):
    return (r[0], r[1], r[2], r[3], fail_class(r))


def w(name, hdr, data):
    with open(os.path.join(OUT, name), 'w') as f:
        f.write('\t'.join(hdr) + '\n')
        for r in data:
            f.write('\t'.join(map(str, r)) + '\n')


c_rec, c_new = rows(f'{REC}/check.tsv'), rows(f'{NEW}/check.tsv')
f_rec = [r for r in c_rec[1:] if fail_class(r)]
f_new = [r for r in c_new[1:] if fail_class(r)]
k_rec, k_new = {key(r) for r in f_rec}, {key(r) for r in f_new}
new = [r for r in f_new if key(r) not in k_rec]
gone = [r for r in f_rec if key(r) not in k_new]
hdr = ['file', 'line', 'old', 'new', 'class', 'text']
w('new-fail-rows.tsv', hdr + ['verdict', 'reason'], [(*r[:4], fail_class(r), r[4], '', '') for r in new])
w('gone-fail-rows.tsv', hdr, [(*r[:4], fail_class(r), r[4]) for r in gone])

diff = []
for name in ('check.tsv', 'review.tsv'):
    a = collections.Counter(tuple(r) for r in rows(f'{REC}/{name}'))
    b = collections.Counter(tuple(r) for r in rows(f'{NEW}/{name}'))
    diff += [(name, 'rec-only', *r) for r in sorted((a - b).elements())]
    diff += [(name, 'new-only', *r) for r in sorted((b - a).elements())]
w('check-diff.tsv', ['table', 'side', 'file', 'line', 'old', 'new', 'status', 'class', 'old_fn', 'new_sym'], diff)

NUM = re.compile(r"(?<![A-Za-z0-9_'.])(?:0x[0-9a-fA-F]+|\d+)(?![0-9A-Za-z_])")
S_rec, S_new = f'{REC}/stage-out', f'{NEW}/stage-out'


def tree(d):
    return sorted(os.path.relpath(os.path.join(r, f), d) for r, _, fs in os.walk(d) for f in fs)


t_rec, t_new = tree(S_rec), tree(S_new)
cells, prov, nfiles = [], 0, 0
for rel in sorted(set(t_rec) | set(t_new)):
    if rel not in t_rec or rel not in t_new:
        cells.append((rel, 0, 'file', 'present' if rel in t_rec else 'absent',
                      'present' if rel in t_new else 'absent', '', ''))
        continue
    a = open(os.path.join(S_rec, rel)).read().split('\n')
    b = open(os.path.join(S_new, rel)).read().split('\n')
    if a != b:
        nfiles += 1
    if len(a) != len(b):
        cells.append((rel, 0, 'line-count', len(a), len(b), '', ''))
        continue
    for i, (x, y) in enumerate(zip(a, b)):
        if x == y:
            continue
        if 'Relocated from' in x and x.replace(f'by port_core {OLD_SHA}', f'by port_core {NEW_SHA}') == y:
            prov += 1
            continue
        nx, ny = NUM.findall(x), NUM.findall(y)
        if len(nx) == len(ny) and NUM.sub('#', x) == NUM.sub('#', y):
            cells += [(rel, i + 1, 'numeral', p, q, '', '') for p, q in zip(nx, ny) if p != q]
        else:
            cells.append((rel, i + 1, 'text', x, y, '', ''))
w('stage-out-cells.tsv', ['file', 'line', 'kind', 'rec4', 'e0e9', 'verdict', 'reason'], cells)

ov_new = rows(f'{NEW}/overrides.tsv')
st = collections.Counter(r[5].split(' (')[0] for r in ov_new[1:])
req_same = open(f'{REC}/required.tsv').read() == open(f'{NEW}/required.tsv').read()
print(f'check.tsv FAIL rows: rec {len(f_rec)}, new {len(f_new)}; new FAIL rows {len(new)} '
      f'{dict(collections.Counter(fail_class(r) for r in new))}; gone FAIL rows {len(gone)} '
      f'{dict(collections.Counter(fail_class(r) for r in gone))}')
print(f'check/review rows in one run only: {len(diff)}')
for nm in ('interval-delta', 'tot-bound', 'hypothesis-decimal-moved', 'bound-name-mismatch', 'shadow-offset',
           'value-role-conflict'):
    print(f'  class {nm}: rec FAIL {sum(1 for r in f_rec if fail_class(r) == nm)}, '
          f'new FAIL {sum(1 for r in f_new if fail_class(r) == nm)}, '
          f'new rows of any status {sum(1 for r in c_new[1:] if len(r) > 4 and nm in r[4])}')
print(f'overrides.tsv (new): {len(ov_new) - 1} rows {dict(st)}; NO-FILE {st.get("NO-FILE", 0)}; '
      f'rec rows equal: {rows(f"{REC}/overrides.tsv") == ov_new}')
print(f'required.tsv equal: {req_same}')
print(f'stage-out: files rec {len(t_rec)}, new {len(t_new)}, differing files {nfiles}; provenance-sha-only lines '
      f'{prov}; other differing cells {len(cells)}')
