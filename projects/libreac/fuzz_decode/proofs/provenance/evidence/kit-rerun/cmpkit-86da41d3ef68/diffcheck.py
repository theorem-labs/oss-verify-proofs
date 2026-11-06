#!/usr/bin/env python3
"""diffcheck.py OLD NEW -- does a strictcmp3 run (cmpkit 86da41d3ef68) give a record made on cmpkit 4bbd3a74be89 the
same result? Read-only.

NEW is a `strictcmp3.py cmp` output. OLD is either a `strictcmp2.py cmp` output (any file holding its rows: a cmp row is
a line whose 5th and 6th tab fields are sizes and whose 11th is the accepted-target tuple) or a settle.py settled.tsv.
Per (function, pair):
  cmp OLD      the old word-only verdict, the pcrel / real / unmeasured counts, the accepted-target tuple and the set
               of differing targets (word offset, kind) against strictcmp3's words-only verdict, counts, tuple and
               differing targets; SAME when all four are equal;
  settled OLD  the set of (word, kit kind) of the settled rows against strictcmp3's differing targets of that pair;
               SAME when equal (each settled row is the same kit difference, so its settlement still applies).
Prints one row per key and a TOTAL line; exit 1 when a key differs or is on one side only."""
import ast, csv, sys


def cmp_rows(path, new):
    out = {}
    for line in open(path, encoding='utf-8'):
        c = line.rstrip('\n').split('\t')
        if len(c) < 12 or not (c[4].isdigit() and c[5].isdigit() and c[10].startswith('(')):
            continue
        diff = [] if c[11] == '0' else ast.literal_eval(c[11])
        words = c[15] if new else c[6]
        out[(c[0], c[1])] = dict(words=words, counts=tuple(c[7:10]), targets=c[10],
                                 diff=frozenset((d[0], d[3]) for d in diff), verdict=c[6])
    return out


def main():
    old_p, new_p = sys.argv[1:3]
    new = cmp_rows(new_p, True)
    head = open(old_p, encoding='utf-8').readline()
    bad = 0
    if head.startswith('pair\t'):
        old = {}
        for r in csv.DictReader(open(old_p, encoding='utf-8'), delimiter='\t'):
            old.setdefault((r['fn'], r['pair']), set()).add((r['word'], r['kit kind']))
        print('fn\tpair\tsettled rows (word, kit kind)\tstrictcmp3 differing targets\tstrictcmp3 verdict\tresult')
        for k in sorted(old):
            n = new.get(k)
            if n is None:
                bad += 1; print('%s\t%s\t%s\t-\t-\tNO NEW ROW' % (k + (sorted(old[k]),))); continue
            same = set(old[k]) == set(n['diff'])
            bad += not same
            print('%s\t%s\t%s\t%s\t%s\t%s' % (k + (sorted(old[k]), sorted(n['diff']), n['verdict'], 'SAME' if same else 'CHANGED')))
        print('TOTAL\tsettled keys %d\tchanged or missing %d' % (len(old), bad))
    else:
        old = cmp_rows(old_p, False)
        print('fn\tpair\told words / counts / targets / differing\tnew words-only / counts / targets / differing\tnew verdict\tresult')
        for k in sorted(set(old) | set(new)):
            o, n = old.get(k), new.get(k)
            if o is None or n is None:
                bad += 1; print('%s\t%s\t%s\t%s\t-\tON ONE SIDE ONLY' % (k + (o and 'old row', n and 'new row'))); continue
            same = all(o[x] == n[x] for x in ('words', 'counts', 'targets', 'diff'))
            bad += not same
            f = lambda r: '%s %s %s %s' % (r['words'], '/'.join(r['counts']), r['targets'], sorted(r['diff']))
            print('%s\t%s\t%s\t%s\t%s\t%s' % (k[0], k[1], f(o), f(n), n['verdict'], 'SAME' if same else 'CHANGED'))
        print('TOTAL\tkeys %d\tchanged or on one side %d' % (len(set(old) | set(new)), bad))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
