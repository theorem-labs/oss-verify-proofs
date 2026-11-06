#!/usr/bin/env python3
"""merge.py -- join the per-file triage tables into triage-rows.tsv and the controls into controls.tsv.

    merge.py --gen RA.gen.tsv RB.gen.tsv --states DIR --light DIR --out-rows triage-rows.tsv --out-ctl controls.tsv

Checks that every flagged row of the eight files appears exactly once, in input order, with its 16 input columns
unchanged, and that no table text names a host path."""
import argparse
import collections
import csv
import re
import sys

FILES = {'AB01.v': 'states', 'AB03.v': 'states', 'AB1w.v': 'light', 'ACej.v': 'light',
         'YB01.v': 'states', 'YB03.v': 'states', 'YB1w.v': 'light', 'YCej.v': 'light'}
HDR = ['verdict', 'kernel_checked', 'image', 'src_file', 'src_line', 'dst_file', 'dst_line', 'sentence', 'idx', 'kind',
       'src_value', 'dst_value', 'src_class', 'src_res', 'dst_res', 'note', 'reason', 'measurement', 'result',
       'finding_kind', 'new_value', 'read_by']
HOST = re.compile(r'/(?:tmp|home|mnt|root|var)/')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--gen', nargs=2, required=True)
    ap.add_argument('--states', required=True)
    ap.add_argument('--light', required=True)
    ap.add_argument('--out-rows', required=True)
    ap.add_argument('--out-ctl', required=True)
    a = ap.parse_args()
    inp = collections.defaultdict(list)
    for g in a.gen:
        for r in csv.reader(open(g), delimiter='\t'):
            if r and r[0] != 'verdict' and r[5] in FILES:
                inp[r[5]].append(r)
    out, bad = [], 0
    for f, where in FILES.items():
        d = a.states if where == 'states' else a.light
        rows = [r for r in csv.reader(open(f'{d}/{f[:-2]}.rows.tsv'), delimiter='\t') if r]
        if len(rows) != len(inp[f]) or any(x[:16] != y for x, y in zip(rows, inp[f])):
            sys.exit(f'{f}: {len(rows)} triage rows for {len(inp[f])} flagged rows, or the input columns differ')
        for r in rows:
            if len(r) != 22:
                sys.exit(f'{f}: a row has {len(r)} columns')
            if any(HOST.search(x) for x in r[16:]):
                sys.exit(f'{f}: host path in {r[16:18]}')
            bad += r[18] != 'OK'
        out += rows
    with open(a.out_rows, 'w') as fh:
        fh.write('\t'.join(HDR) + '\n')
        for r in out:
            fh.write('\t'.join(r) + '\n')
    # controls
    ctl = []
    for f, where in FILES.items():
        stem = f[:-2]
        if where == 'states':
            for r in csv.reader(open(f'{a.states}/{stem}.ctlrules.tsv'), delimiter='\t'):
                ctl.append([r[0], 'numeral', r[1], r[2], r[3], r[4], r[5]])
            c = collections.Counter((r[4], r[5]) for r in csv.reader(open(f'{a.states}/{stem}.ctl.tsv'),
                                                                     delimiter='\t'))
            for (kind, v), n in sorted(c.items()):
                ctl.append([f'lib/{"A" if f.startswith("A") else "B"}/{f}', 'row', f'row-verdict:{v}', kind, str(n),
                            '-', '-'])
        else:
            c = collections.Counter()
            rel = None
            for r in csv.reader(open(f'{a.light}/{stem}.ctl.tsv'), delimiter='\t'):
                rel = r[0]
                rule = r[3] if stem.endswith('1w') else 'TRACES-GEN+UNIVERSE+IPC'
                c[(rule, r[4], r[5])] += 1
            for rule, kind in sorted({(k[0], k[1]) for k in c}):
                ref, acc = c[(rule, kind, 'refused')], c[(rule, kind, 'accepted')]
                other = sum(v for k, v in c.items() if k[0] == rule and k[1] == kind and k[2] not in
                            ('refused', 'accepted'))
                ctl.append([rel, 'numeral' if stem.endswith('ej') else 'row', rule, kind, str(ref + acc), str(ref),
                            str(acc) + (f' (+{other} n/a or same-value)' if other else '')])
    with open(a.out_ctl, 'w') as fh:
        fh.write('file\tlevel\trule\tperturbation\tjudged\trefused\taccepted\n')
        for r in ctl:
            fh.write('\t'.join(r) + '\n')
    print('rows', len(out), 'not OK', bad)
    print(collections.Counter((r[5], r[16], r[18]) for r in out).most_common(80))


if __name__ == '__main__':
    main()
