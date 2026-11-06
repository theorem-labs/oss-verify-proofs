#!/usr/bin/env python3
"""plant_check.py -- judge one planted control of the roundconst gate: the gate's rows on a planted copy of one file
against its rows on the unplanted copy of the same file (both runs: the same checker, the same images, one file).

A plant sets ONE numeral of the copy back to the donor's numeral at that position, so the checker sees a kept value
and passes it; the value is a donor image quantity whose target counterpart differs. The control FIRES when:
  --want MISMATCH  the planted run has exactly one non-SAME row more than the unplanted run, that row has status
                   MISMATCH, it is at --at FILE:LINE and its value is --value; every other row is unchanged;
  --want SAME      (the gap control) the planted run has the same non-SAME rows as the unplanted run, and a SAME row
                   at --at with value --value that the unplanted run does not have.
The roundconst v1 tables (--v1-base / --v1-plant) are compared too and their difference is printed (v1 has no /4
divisor and a 0x100 floor, so it is expected to give the same rows on a word-count or small-table plant).
Prints one line `plant_check: FIRED ...` or `plant_check: VOID ...`; exit 0 when FIRED, 1 when VOID.

Usage: plant_check.py --base BASE.tsv --plant PLANT.tsv --at FILE:LINE --value 0xV --want MISMATCH|SAME
                      [--v1-base V1BASE.tsv --v1-plant V1PLANT.tsv]
"""
import argparse, collections, sys

ap = argparse.ArgumentParser()
for k in ('base', 'plant', 'at', 'value', 'want'):
    ap.add_argument('--' + k, required=True)
ap.add_argument('--v1-base')
ap.add_argument('--v1-plant')
a = ap.parse_args()


def rows(p):
    L = [l.rstrip('\n').split('\t') for l in open(p)]
    return L[0], L[1:]


def diff(b, p):
    cb, cp = collections.Counter(map(tuple, b)), collections.Counter(map(tuple, p))
    return list((cp - cb).elements()), list((cb - cp).elements())


H, B = rows(a.base)
_, P = rows(a.plant)
c = {k: i for i, k in enumerate(H)}
st = lambda R: collections.Counter(r[c['status']] for r in R)
print(f'unplanted: {len(B)} selected rows {dict(sorted(st(B).items()))}')
print(f'planted:   {len(P)} selected rows {dict(sorted(st(P).items()))}')
more, less = diff(B, P)
for r in more:
    print(f'only planted:   {r[c["status"]]} {r[c["verdict"]]} {r[c["dst"]]} {r[c["value"]]} {r[c["class"]]}')
for r in less:
    print(f'only unplanted: {r[c["status"]]} {r[c["verdict"]]} {r[c["dst"]]} {r[c["value"]]} {r[c["class"]]}')
at = lambda r: r[c['dst']] == a.at and r[c['value']] == a.value
ns_more = [r for r in more if r[c['status']] != 'SAME']
ns_less = [r for r in less if r[c['status']] != 'SAME']
if a.want == 'MISMATCH':
    ok = len(ns_more) == 1 and not ns_less and ns_more[0][c['status']] == 'MISMATCH' and at(ns_more[0])
else:
    ok = not ns_more and not ns_less and any(r[c['status']] == 'SAME' and at(r) for r in more)
if a.v1_base and a.v1_plant:
    _, V1B = rows(a.v1_base)
    _, V1P = rows(a.v1_plant)
    m1, l1 = diff(V1B, V1P)
    print(f'v1: unplanted {len(V1B)} rows, planted {len(V1P)} rows; only planted {len(m1)}, only unplanted {len(l1)}'
          + ''.join(f'\n  v1 only planted: {r[0]} {r[3]} {r[8]}' for r in m1 if len(r) > 8))
w = f'{a.want} at {a.at} value {a.value}'
print(f'plant_check: {"FIRED" if ok else "VOID"} ({w}; non-SAME rows +{len(ns_more)} -{len(ns_less)})')
sys.exit(0 if ok else 1)
