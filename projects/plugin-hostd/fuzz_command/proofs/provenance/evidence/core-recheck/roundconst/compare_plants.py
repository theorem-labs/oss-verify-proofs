#!/usr/bin/env python3
"""controls.tsv for the v2 by-value gate on plugin-hostd/fuzz_command: every control of the gate README, judged from
the run outputs.
  (1) donor-on-donor: controls/c1-C{A,B}{,-mv}.summary must select 0 non-SAME rows.
  (2) kept donor PT_LOAD lengths (v1's plant shape), (3) a kept donor word count and a kept small table length,
  (4) the gap control: for each plant of plants/plants.tsv, the port_addr_check 3d2eee813cce run of the plant copy and of
      the unplanted base copy (one file each, controls/pac/), then v2 (controls/v2/) and v1 (controls/v1/) with
      --all-verdicts. A plant is VALID when the plant run's row at the planted position keeps the donor numeral
      (src_value = dst_value = the planted value = column 11 of the base run's row) and its verdict is a pass
      (NON-ADDRESS-SAME / ROUND-CONSTANT-SAME / SAME-GEOMETRY). Expected: (2), (3) v2 has exactly one MISMATCH row
      more than base, at the planted position; (3) v1's rows are the same as on base; (4) v2 calls the planted row SAME
      and has no MISMATCH row more.
usage: compare_plants.py DIR   (DIR holds plants/plants.tsv and controls/)"""
import collections, gzip, os, sys

D = sys.argv[1]
C = os.path.join(D, 'controls')
PASS = {'NON-ADDRESS-SAME', 'ROUND-CONSTANT-SAME', 'SAME-GEOMETRY'}


def full(name):
    out = []
    for l in gzip.open(os.path.join(C, 'pac', name + '.full.tsv.gz'), 'rt', encoding='utf-8', errors='replace'):
        if not l.startswith('#') and not l.startswith('verdict\t'):
            out.append((l.rstrip('\n').split('\t') + [''] * 16)[:16])
    return out


def gate(ver, name):
    p = os.path.join(C, ver, name + '.tsv')
    f = gzip.open(p + '.gz', 'rt') if os.path.exists(p + '.gz') else open(p)
    return [l.rstrip('\n').split('\t') for l in f][1:]


def key(r):     # status-independent identity of a gate row: dst, src, sentence, idx, kind
    return tuple(r[3:8])


out = []
for n in ('CA', 'CB'):
    for mv in ('', '-mv'):
        s = open(os.path.join(C, f'c1-{n}{mv}.summary')).read()
        nonsame = sum(int(l.split('\t')[-1]) for l in s.split('\n') if l.startswith('#   ') and not l.startswith('#   SAME')
                      and not l.startswith('#   class'))
        sel = s.split('selected ')[1].split(' ')[0]
        out.append(('1 donor-on-donor', f'{n} {"--moved" if mv else "normal"}', f'selected {sel}; non-SAME 0',
                    f'selected {sel}; non-SAME {nonsame}', 'PASS' if nonsame == 0 else 'FAIL'))

BASE = {'AB13.v': 'RCv2-A-base-AB13', 'AB1h.v': 'RCv2-A-base-AB1h', 'AB01.v': 'RCv2-A-base-AB01',
        'AD1k.v': 'RCv2-A-base-AD1k', 'AF0m.v': 'RCv2-A-base-AF0m', 'YB13.v': 'RCv2-B-base-YB13',
        'YB01.v': 'RCv2-B-base-YB01', 'YF0m.v': 'RCv2-B-base-YF0m'}
CTL = {'2': '2 kept donor PT_LOAD length', '3w': '3 kept donor word count', '3t': '3 kept donor small table length',
       '4': '4 gap control'}
for p in [l.rstrip('\n').split('\t') for l in open(os.path.join(D, 'plants', 'plants.tsv'))][1:]:
    name, side, fn, ln, old, new, ctl, dv, what = p
    run, base = 'RCv2-' + name, BASE[fn]
    fp, fb = full(run), full(base)
    pos = [r for r in fp if r[5] == fn and r[6] == ln and r[10] == dv and r[11] == dv]
    bpos = [r for r in fb if r[5] == fn and r[6] == ln and r[10] == dv]
    valid = bool(pos) and all(r[0] in PASS for r in pos) and bool(bpos) and bpos[0][11] != dv
    vtxt = (f'plant run row {fn}:{ln} verdict {pos[0][0] if pos else "none"} src=dst={dv}; base row dst '
            f'{bpos[0][11] if bpos else "none"} (column 11 of base = {bpos[0][10] if bpos else "none"})')
    g2p, g2b = gate('v2', run), gate('v2', base)
    mp = {key(r) for r in g2p if r[0] == 'MISMATCH'}
    mb = {key(r) for r in g2b if r[0] == 'MISMATCH'}
    extra = sorted(mp - mb)
    lost = sorted(mb - mp)
    at = [r for r in g2p if r[3] == f'{fn}:{ln}' and int(r[8], 16) == int(dv, 16)]
    st = ','.join(sorted({r[0] for r in at})) or 'not selected'
    cls = ','.join(sorted({r[9] for r in at}))
    g1p, g1b = gate('v1', run), gate('v1', base)
    n1p, n1b = collections.Counter(r[0] for r in g1p), collections.Counter(r[0] for r in g1b)
    v1same = {tuple(r[:1] + r[3:8]) for r in g1p if r[0] != 'SAME'} == {tuple(r[:1] + r[3:8]) for r in g1b if r[0] != 'SAME'}
    v1at = [r[0] for r in g1p if r[3] == f'{fn}:{ln}' and int(r[8], 16) == int(dv, 16)]
    if ctl == '4':
        exp = 'valid plant; v2 status at the planted row SAME; MISMATCH rows = base'
        ok = valid and st == 'SAME' and not extra and not lost
    else:
        exp = 'valid plant; v2 exactly one MISMATCH row more than base, at the planted row' + \
              ('; v1 rows = base' if ctl.startswith('3') else '')
        ok = valid and len(extra) == 1 and extra[0][0] == f'{fn}:{ln}' and not lost and (v1same or not ctl.startswith('3'))
    got = (f'{vtxt}; v2 MISMATCH base {len(mb)} plant {len(mp)} (+{len(extra)} -{len(lost)}), planted row {st} {cls}; '
           f'v1 non-SAME rows {"same as" if v1same else "DIFFER from"} base ({dict(n1p)} vs {dict(n1b)}), v1 at planted '
           f'row: {",".join(v1at) or "not selected"}')
    out.append((CTL[ctl], f'{name}: {side}/{fn}:{ln} {old.strip()} -> {new.strip()} ({what})', exp, got,
                'PASS' if ok else 'FAIL'))
with open(os.path.join(D, 'controls.tsv'), 'w') as o:
    o.write('control\tcase\texpected\tgot\tresult\n')
    for r in out:
        o.write('\t'.join(r) + '\n')
for r in out:
    print(r[0], '|', r[1][:70], '|', r[4])
    print('    ', r[3][:400])
