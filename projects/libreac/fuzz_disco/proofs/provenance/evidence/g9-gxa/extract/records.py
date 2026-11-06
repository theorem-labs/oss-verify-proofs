#!/usr/bin/env python3
"""Per-value extracts of the G9 records that are not in git. Each subcommand reads its source record(s), given as
arguments, and writes one clean tab-separated table to standard output: only the columns a script of this directory
reads or a reader checks, no comment text and no path of the machine the record was made on.

  records.py codeid-pairs CODEID_A CODEID_Y
      The function list and the pairing of the P0 code-identity record (one table per image), WITHOUT its verdicts:
      fm function, aliases, fm address and size, the paired address and size in image A and in image B, how the pair
      was found, and whether the function is a route function or one of the fm harness program. codeid_kit.py reads it.

  records.py p0-numerals NUMERALS_TSV
      P0's numeral table with the columns numerals.py reads (file, numeral, kind, disco A, disco Y, status, how): every
      row; `how` only where numerals.py prints it (status UNRESOLVED or DROP, its first 120 characters), else empty.

  records.py route-classes ROUTE_TABLE
      The route table with the two columns validate.py reads: fm path (lib/) and class.
"""
import csv
import sys


def rows(path):
    lines = [l for l in open(path).read().split('\n') if l and not l.startswith('#')]
    return list(csv.DictReader(lines, delimiter='\t'))


def codeid_pairs(a_path, y_path):
    ra, ry = rows(a_path), rows(y_path)
    if [(r['fm function'], r['fm addr']) for r in ra] != [(r['fm function'], r['fm addr']) for r in ry]:
        sys.exit('records.py: the two code-identity tables list different functions')
    da, dy = list(ra[0])[5], list(ry[0])[5]          # 'disco.asan addr' / 'disco.asan-ubsan addr'
    sa, sy = list(ra[0])[6], list(ry[0])[6]
    out = ['fm function\taliases\tfm addr\tfm size\tA addr\tA size\tB addr\tB size\tpairing\tfunction kind']
    for a, y in zip(ra, ry):
        if a['pairing'] != y['pairing']:
            sys.exit('records.py: %s is paired %s in A and %s in B' % (a['fm function'], a['pairing'], y['pairing']))
        kind = 'harness' if a['verdict'].startswith('harness') else 'route'
        out.append('\t'.join([a['fm function'], a['aliases'], a['fm addr'], a['fm size'], a[da], a[sa], y[dy], y[sy],
                              a['pairing'], kind]))
    sys.stdout.write('\n'.join(out) + '\n')


def p0_numerals(path):
    cols = ['file', 'numeral', 'kind', 'disco A', 'disco Y', 'status', 'how']
    out = ['\t'.join(cols)]
    for r in rows(path):
        how = r['how'][:120] if r['status'] in ('UNRESOLVED', 'DROP') else ''
        out.append('\t'.join([r[c] for c in cols[:-1]] + [how]))
    sys.stdout.write('\n'.join(out) + '\n')


def route_classes(path):
    out = ['fm path (lib/)\tclass'] + ['%s\t%s' % (r['fm path (lib/)'], r['class']) for r in rows(path)]
    sys.stdout.write('\n'.join(out) + '\n')


if __name__ == '__main__':
    cmd, args = sys.argv[1:2], sys.argv[2:]
    if cmd == ['codeid-pairs'] and len(args) == 2:
        codeid_pairs(*args)
    elif cmd == ['p0-numerals'] and len(args) == 1:
        p0_numerals(*args)
    elif cmd == ['route-classes'] and len(args) == 1:
        route_classes(*args)
    else:
        sys.exit(__doc__)
