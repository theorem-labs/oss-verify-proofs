#!/usr/bin/env python3
"""pac_moved.py OLD.tsv NEW.tsv -- row-level comparison of two port_addr_check runs over the SAME inputs (here
cb0e067e3bae and e165063a0081 on the final 19 files): each row is keyed by (src file, src line, dst file, dst line,
sentence, index, src value, dst value). Prints the verdict counts that differ, every row whose verdict MOVED (same key,
other verdict), every row only one run has (NEW / GONE), and the GENERATOR-FILL rows of NEW with the basis the tool
gives (a generator mark, or the positional reading that e165 allows only where the donor row's object is absent from
the target). Writes nothing; exit 0.

  pac_moved.py OLD.tsv NEW.tsv
"""
import collections, csv, sys


def load(p):
    rows = list(csv.reader((l for l in open(p) if not l.startswith('#')), delimiter='\t'))
    return [dict(zip(rows[0], r)) for r in rows[1:]]


def key(r):
    return (r['src_file'], r['src_line'], r['dst_file'], r['dst_line'], r['sentence'], r['idx'], r['src_value'],
            r['dst_value'])


def show(tag, r):
    print('%s %s src %s:%s dst %s:%s `%s` idx %s %s -> %s | %s' % (tag, r['verdict'], r['src_file'], r['src_line'],
          r['dst_file'], r['dst_line'], r['sentence'][:60], r['idx'], r['src_value'], r['dst_value'], r['note'][:220]))


A, B = load(sys.argv[1]), load(sys.argv[2])
ca, cb = collections.Counter(r['verdict'] for r in A), collections.Counter(r['verdict'] for r in B)
print('rows: old %d, new %d; verdict counts that differ: %s' % (len(A), len(B), {k: (ca[k], cb[k]) for k in
      sorted(set(ca) | set(cb)) if ca[k] != cb[k]} or 'none'))
da, db = collections.defaultdict(list), collections.defaultdict(list)
for r in A:
    da[key(r)].append(r)
for r in B:
    db[key(r)].append(r)
moved = [(k, da[k], db[k]) for k in da if k in db and sorted(r['verdict'] for r in da[k]) !=
         sorted(r['verdict'] for r in db[k])]
print('MOVED rows (same key, another verdict): %d' % len(moved))
for k, ra, rb in moved:
    for r in ra:
        show('  MOVED from', r)
    for r in rb:
        show('  MOVED to  ', r)
gone = [r for k in da if k not in db for r in da[k]]
new = [r for k in db if k not in da for r in db[k]]
print('GONE rows (old run only): %d' % len(gone))
for r in gone:
    show('  GONE', r)
print('NEW rows (new run only): %d' % len(new))
for r in new:
    show('  NEW ', r)
gf = [r for r in B if r['verdict'] == 'GENERATOR-FILL']
basis = collections.Counter('positional, donor object absent from the target' if 'in no symbol of the target' in r['note']
                            else 'generator mark' if 'filled by generator' in r['note']
                            else 'in-place copy, no donor row' if 'no donor row of its own' in r['note'] else 'OTHER'
                            for r in gf)
print('GENERATOR-FILL rows of the new run: %d, basis: %s' % (len(gf), dict(basis)))
