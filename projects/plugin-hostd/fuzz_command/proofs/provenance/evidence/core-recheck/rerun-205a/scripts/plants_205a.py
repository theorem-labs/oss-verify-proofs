#!/usr/bin/env python3
"""The planted controls under 205a90fd19b8: each plant's row in the plant run and the same numeral in the base run.

Usage: plants_205a.py RUNS_DIR PLANTS.tsv FLAG_CLASSES.txt
For each plant of plants.tsv (side, file, line, unit value, planted value, class): the verdict and note of the row
of P<side>-plant-205a/full.tsv at that file and line whose ported value is the planted value, and of the row of
P<side>-base-205a/full.tsv whose ported value is the unit value. A plant FIRES when its verdict is a finding class.
Then every other row: base and plant runs are paired by numeral identity minus the ported value (image, files,
lines, sentence, index, source value); a pair outside the plant lines whose verdict differs is listed.
"""
import collections
import os
import sys

runs, plants_p, fc_p = sys.argv[1:4]
flags = {l.strip() for l in open(fc_p) if l.strip()}


def load(p):
    rows = [l.rstrip('\n').split('\t') for l in open(p, encoding='utf-8', errors='replace') if not l.startswith('#')]
    ix = {c: i for i, c in enumerate(rows[0])}
    return ix, rows[1:]


plants = [l.rstrip('\n').split('\t') for l in open(plants_p, encoding='utf-8')][1:]
fired = 0
for side in ('A', 'B'):
    bix, base = load(os.path.join(runs, f'P{side}-base-205a', 'full.tsv'))
    pix, plant = load(os.path.join(runs, f'P{side}-plant-205a', 'full.tsv'))
    mine = [p for p in plants if p[0] == side]
    for _, f, ln, old, new, cls in mine:
        pr = [r for r in plant if r[pix['dst_file']] == f and r[pix['dst_line']] == ln and r[pix['dst_value']] == new]
        br = [r for r in base if r[bix['dst_file']] == f and r[bix['dst_line']] == ln and r[bix['dst_value']] == old]
        pv = pr[0][pix['verdict']] if pr else 'NO ROW'
        bv = br[0][bix['verdict']] if br else 'NO ROW'
        fire = pv in flags
        fired += fire
        print(f'P{side} {f}:{ln} {old} -> {new} ({cls}): plant {pv} [{"FIRES" if fire else "DOES NOT FIRE"}]; '
              f'base {bv}; tool note (plant): {pr[0][pix["note"]] if pr else "-"}')
    key = ('image', 'src_file', 'src_line', 'dst_file', 'dst_line', 'sentence', 'idx', 'src_value')
    pool = collections.defaultdict(collections.deque)
    for r in base:
        pool[tuple(r[bix[k]] for k in key)].append(r)
    planted = {(p[1], p[2]) for p in mine}
    other = 0
    for r in plant:
        q = pool.get(tuple(r[pix[k]] for k in key))
        b = q.popleft() if q else None
        if (r[pix['dst_file']], r[pix['dst_line']]) in planted:
            continue
        if b is None or b[bix['verdict']] != r[pix['verdict']]:
            other += 1
            print(f'  P{side} other change: {r[pix["dst_file"]]}:{r[pix["dst_line"]]} '
                  f'{b[bix["verdict"]] if b else "NO BASE ROW"} -> {r[pix["verdict"]]}')
    print(f'P{side}: rows outside the plant lines whose verdict differs between base and plant: {other}')
print(f'plants firing: {fired} of {len(plants)}')
