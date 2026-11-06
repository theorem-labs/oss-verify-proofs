#!/usr/bin/env python3
"""pac_table.py CONTROL.tsv UNIT.tsv -- per file: numerals paired and every FLAG class with its count, the unit's run
beside the control's (port_addr_check 16f8a030c869 TSVs; FLAGS = the tool's own set). Markdown on stdout."""
import collections
import csv
import sys

FLAGS = {'DIFFERENT-SYMBOL', 'NO-COUNTERPART', 'UNRESOLVED', 'KIND-CHANGED', 'NON-ADDRESS-CHANGED', 'INSN-CHANGED',
         'IDENT-MISMATCH', 'GEOMETRY-CHANGED', 'STALE-DONOR-CODE-POINTER', 'UNPAIRED-SOURCE', 'UNPAIRED-PORTED',
         'UNPAIRED-FILE', 'IMAGE-EXTENT-CHANGED', 'IMAGE-EXTENT-STALE-ABOVE', 'IMAGE-EXTENT-STALE-BELOW',
         'SAME-VALUE-DIFFERENT-OBJECT', 'SLID-TO-NEIGHBOUR', 'HASH-UNCHANGED', 'LABEL-MIXED', 'LABEL-COMPARED-WITH-PC',
         'STALE-DONOR-DATA-POINTER'}


def load(p):
    rows = [l for l in open(p) if not l.startswith('#')]
    per = collections.defaultdict(collections.Counter)
    for r in csv.DictReader(rows, delimiter='\t'):
        f = (r.get('dst_file') or r.get('src_file') or '?').split('/')[-1]
        per[f][r['verdict']] += 1
    return per


ctl, unit = load(sys.argv[1]), load(sys.argv[2])
print('| file | numerals (uci / ctl) | uci B flags | control flags (cgif A -> B) | flag classes only in uci B |')
print('|---|---|---|---|---|')
tot_u, tot_c = collections.Counter(), collections.Counter()
for f in sorted(set(ctl) | set(unit)):
    u, c = unit.get(f, collections.Counter()), ctl.get(f, collections.Counter())
    tot_u.update(u); tot_c.update(c)
    fu = {k: v for k, v in u.items() if k in FLAGS}
    fc = {k: v for k, v in c.items() if k in FLAGS}
    only = sorted(set(fu) - set(fc))
    show = lambda d: ', '.join('%s %d' % kv for kv in sorted(d.items())) or '0'
    print('| %s | %d / %d | %d: %s | %d: %s | %s |' % (f, sum(u.values()), sum(c.values()), sum(fu.values()), show(fu),
                                                   sum(fc.values()), show(fc), ', '.join(only) or '-'))
fu = {k: v for k, v in tot_u.items() if k in FLAGS}
fc = {k: v for k, v in tot_c.items() if k in FLAGS}
print('| **all** | %d / %d | %d | %d | %s |' % (sum(tot_u.values()), sum(tot_c.values()), sum(fu.values()),
                                              sum(fc.values()), ', '.join(sorted(set(fu) - set(fc))) or '-'))
print()
print('uci B verdicts:', dict(sorted(tot_u.items())))
print('control verdicts:', dict(sorted(tot_c.items())))
print()
print('uci B rows of the classes STALE-DONOR-CODE-POINTER / NO-COUNTERPART / IDENT-MISMATCH / GEOMETRY-CHANGED '
      '(distinct by file, definition, source value, ported value; count of rows):')
seen = collections.Counter()
info = {}
for r in csv.DictReader([l for l in open(sys.argv[2]) if not l.startswith('#')], delimiter='\t'):
    if r['verdict'] in ('STALE-DONOR-CODE-POINTER', 'NO-COUNTERPART', 'IDENT-MISMATCH', 'GEOMETRY-CHANGED'):
        k = (r['verdict'], r['dst_file'], r['sentence'], r['src_value'], r['dst_value'])
        seen[k] += 1
        info.setdefault(k, (r['src_line'], r['dst_line'], r['note'][:260]))
for k in sorted(seen):
    print('  %s x%d  %s %s  src %s:%s %s -> dst line %s %s  | %s' % (k[0], seen[k], k[1], k[2], k[1], info[k][0], k[3],
                                                              info[k][1], k[4], info[k][2]))
