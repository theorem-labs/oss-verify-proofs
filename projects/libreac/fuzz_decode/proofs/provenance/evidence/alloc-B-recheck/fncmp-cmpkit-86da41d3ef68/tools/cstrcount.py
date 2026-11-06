#!/usr/bin/env python3
"""cstrcount.py -- counts the kit's acceptances printed by the closure script (out/<closure>.out or .out.xz):
CSTR rows (one per C-string acceptance: CSTR, function, pair, word, addr1, addr2, length, hex, repr) and ACCEPT lines
(full-bytes / .got-value / table acceptances), per root and over the union of the roots. A row is the same acceptance when
(function, word) is the same; the closure prints each member's rows once per root whose closure holds it.
usage: cstrcount.py"""
import collections, lzma, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common


def main():
    p = os.path.join(common.OUT, common.CLOSURE_OUT)
    text = lzma.open(p + '.xz', 'rt').read() if not os.path.exists(p) else open(p).read()
    root, per, acc = None, collections.OrderedDict(), collections.OrderedDict()
    lines_total = collections.Counter()
    for l in text.split('\n'):
        if '\tclosure ' in l and not l.startswith((' ', 'CSTR')):
            root = l.split('\t')[0]
            per[root], acc[root] = [], []
            continue
        if l.startswith('CSTR\t'):
            c = l.split('\t')
            per[root].append((c[1], c[3])); lines_total['CSTR'] += 1
        elif l.startswith('   ACCEPT '):
            acc[root].append((l.split()[1], l.strip())); lines_total['ACCEPT'] += 1
    out = ['CSTR lines in the file: %d; ACCEPT lines in the file: %d' % (lines_total['CSTR'], lines_total['ACCEPT'])]
    for r in per:
        out.append('root %s: CSTR rows %d, distinct (function, word) %d, distinct members with ACCEPT lines %d' % (
            r[:70], len(per[r]), len(set(per[r])), len({a[0] for a in acc[r]})))
    uni = set().union(*[set(v) for v in per.values()]) if per else set()
    unim = set().union(*[{a[0] for a in v} for v in acc.values()]) if acc else set()
    out.append('UNION over the roots: distinct C-string acceptances (function, word) %d; distinct members with ACCEPT lines %d; '
               'distinct ACCEPT lines %d' % (len(uni), len(unim), len(set().union(*[set(v) for v in acc.values()]))))
    print('\n'.join(out))


if __name__ == '__main__':
    main()
