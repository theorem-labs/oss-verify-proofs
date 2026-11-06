#!/usr/bin/env python3
"""certify.py -- writes out/certify.tsv and out/certify.out: the certification of every differing target of the functions this
record settles by hand, from these inputs only:
  out/fulldiff.tsv     the FULL tcmp diff lists (fulldiff.py), each target with settle.py's measurement by address;
  out/tables.tsv       tables.py's by-address measurement of the targets jtcheck accepted as a table / initializer;
  out/switchbound.tsv  switchbound.py's data-flow bound of the two jump tables jtcheck refused (RELJUMP);
  scans/luiclass.tsv   the settlement class of every `lui-in-section` target (luiclass.py over luitrace.py's traces);
  out/settle.tsv       settle.py run on jtcheck's own UNMEASURED / DIFF lines (marks which targets jtcheck left open).
A target is certified by settle.py when its fulldiff measurement is a settled class, else by tables.py or switchbound.py
when they settled it, else (a lui target) by its luiclass class; otherwise it is NOT CERTIFIED: REAL 0. Column
`jtcheck`: `open` = jtcheck left it UNMEASURED / DIFF (in settle.tsv); `ACCEPT` = jtcheck accepted it itself (a table /
initializer line). usage: certify.py"""
import collections, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common

SETTLED = {'DEBRUIJN', 'RELJUMP', 'RELSTR', 'INDEXED', 'CSTR-EMPTY', 'CSTR-NONPRINT', 'CSTR-PRINT'}


def rows(name):
    return [l.rstrip('\n').split('\t') for l in list(open(os.path.join(common.OUT, name)))[1:]]


def main():
    tab = {(c[0], int(c[1], 16)): c[2] for c in rows('tables.tsv')}
    for c in rows('switchbound.tsv'):
        if c[2] == 'RELJUMP' and 'targets equal' in c[5]:
            tab[(c[0], int(c[1], 16))] = 'RELJUMP (data-flow bound)'
    lui = {}
    for l in list(open(os.path.join(common.SCANS, 'luiclass.tsv')))[1:]:
        c = l.rstrip('\n').split('\t')
        if c[4] == 'luitrace.tsv':
            lui[(c[0], int(c[2], 16))] = c[6]
    jopen = {(c[0], int(c[1].lstrip('+'), 16)) for c in rows('settle.tsv')}
    out, final, uncert = [], collections.Counter(), []
    for c in rows('fulldiff.tsv'):
        k = (c[0], int(c[3], 16))
        if c[5] in SETTLED:
            s, by = c[5], 'settle.py'
        elif tab.get(k, 'DIFFERS') != 'DIFFERS':
            s, by = tab[k], 'tables.py' if not tab[k].startswith('RELJUMP (') else 'switchbound.py'
        elif c[5] == 'LUI' and k in lui and not lui[k].startswith('NOT'):
            s, by = 'LUI ' + lui[k], 'luiclass.py'
        else:
            s, by = 'NOT CERTIFIED: REAL 0', '-'
            uncert.append(k)
        final[s] += 1
        out.append((c[0], c[3], s, by, 'open' if k in jopen else 'ACCEPT'))
    with open(os.path.join(common.OUT, 'certify.tsv'), 'w') as f:
        f.write('function\tword\tsettlement\tby\tjtcheck\n')
        for r in out:
            f.write('\t'.join(r) + '\n')
    fns = {r[0] for r in out}
    lines = ['functions %d; differing targets from tcmp %d' % (len(fns), len(out)),
             'jtcheck left open %d, jtcheck accepted itself %d' % (sum(r[4] == 'open' for r in out), sum(r[4] == 'ACCEPT' for r in out)),
             'settlement: %s' % dict(sorted(final.items())),
             'by: %s' % dict(sorted(collections.Counter(r[3] for r in out).items())),
             'NOT CERTIFIED: %d %s' % (len(uncert), uncert)]
    open(os.path.join(common.OUT, 'certify.out'), 'w').write('\n'.join(lines) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main()
