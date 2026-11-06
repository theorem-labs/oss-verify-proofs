#!/usr/bin/env python3
"""The numerals the header comments of the six generated files state, each measured against the file's own image.

  comments_check.py --lib OURS_LIB --donor-lib DONOR_LIB --img IMG_DIR --out OUT_DIR

Writes OUT_DIR/comment-checks.tsv (every claim: file, line, claim, measured, result) and OUT_DIR/comment-rows.tsv
(the FINDINGs, in the measured-rows form: unit, file, line, old, new, evidence)."""
import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import imgmeas  # noqa: E402
from d2j_rules import parse  # noqa: E402

UNIT = 'plugin-hostd/fuzz_command'
ROLE = {'A': 'fuzz_command.asan', 'B': 'fuzz_command.asan-ubsan'}


def h(x):
    return f'{x:#x}'


def main():
    ap = argparse.ArgumentParser()
    for x in ('--lib', '--donor-lib', '--img', '--out'):
        ap.add_argument(x, required=True)
    a = ap.parse_args()
    rows, finds = [], []
    for k, side in (('A', 'A'), ('B', 'B')):
        im = imgmeas.Img(os.path.join(a.img, f'cmd.{k}.pin'), os.path.join(a.img, f'cmd.{k}.twin'), k)
        D = im.descriptors()
        n_ro = sum(1 for d, f in D if im.secname(f[0]) == '.rodata')
        eh_end = im.section('.eh_frame')[2]
        ro_end = im.section('.rodata')[2]
        pre = 'A/A' if k == 'A' else 'B/Y'
        d2j = parse(open(os.path.join(a.lib, f'{pre}D2j.v')).read())
        a5a = [r for r in d2j if r['name'] == 'R_A5a'][0]
        hs = sum(1 for t in open(os.path.join(a.lib, f'{pre}B01.v')) if re.match(r'Definition HS_tfib_\d+_kn', t))
        dE3i = open(os.path.join(a.donor_lib, 'A/AE3i.v' if k == 'A' else 'YE3i.v')).read()
        d_ro_hi = int(re.search(r'IMG_RO_HI : Z := (0x[0-9a-f]+)', dE3i)[1], 16)
        meas = {
            'globals': (len(D), f'asan_globals section size / 64 = {len(D)} descriptors'),
            'ro_globals': (n_ro, f'{n_ro} descriptors whose beg lies in .rodata'),
            'eh_end': (eh_end, f'.eh_frame end {h(eh_end)} (section header)'),
            'ro_end': (ro_end, f'.rodata end {h(ro_end)} (section header)'),
            'cgif_ro_hi': (d_ro_hi, f'the donor file\'s IMG_RO_HI {h(d_ro_hi)}'),
            'win': ((a5a['wlo'], a5a['whi']), f'R_A5a write window [{h(a5a["wlo"])}, {h(a5a["whi"])}) of this file'),
            'handoff': (hs, f'{hs} HS_tfib_<k>_kn hand-off states in {pre}B01.v'),
        }
        claims = {
            f'{pre}F0m.v': [(r'the (\d+) registered globals', 'globals', int)],
            f'{pre}E3i.v': [(r'(\d+) rodata globals', 'ro_globals', int),
                            (r'IMG_RO_HI = (0x[0-9a-f]+) \(\.eh_frame end', 'eh_end', lambda s: int(s, 16)),
                            (r'cgif (0x[0-9a-f]+)\)', 'cgif_ro_hi', lambda s: int(s, 16)),
                            (r'\((0x[0-9a-f]+), \.rodata end\)', 'ro_end', lambda s: int(s, 16)),
                            (r'cut at the \.rodata end (0x[0-9a-f]+)', 'ro_end', lambda s: int(s, 16))],
            f'{pre}D2j.v': [(r'write window is the driver\'s own statics \[(0x[0-9a-f]+), (0x[0-9a-f]+)\)', 'win',
                             None),
                            (r'(\d+) hand-off states', 'handoff', int)],
        }
        for rel, cl in claims.items():
            lines = open(os.path.join(a.lib, rel)).read().split('\n')
            for ln, t in enumerate(lines[:8], 1):
                if not t.startswith('(*'):
                    continue
                for rx, key, conv in cl:
                    for m in re.finditer(rx, t):
                        if key == 'win':
                            got = (int(m[1], 16), int(m[2], 16))
                            old = f'[{m[1]}, {m[2]})'
                        else:
                            s = next(g for g in m.groups() if g)
                            got, old = conv(s), s
                        exp, why = meas[key]
                        ok = got == exp
                        new = (f'[{h(exp[0])}, {h(exp[1])})' if key == 'win' else
                               (h(exp) if old.startswith('0x') else str(exp)))
                        rows.append((f'lib/{rel}', ln, m[0], why, 'OK' if ok else 'FINDING'))
                        if not ok:
                            arel = 'A/A' + rel[3:]
                            aline = open(os.path.join(a.lib, arel)).read().split('\n')[ln - 1] if k == 'B' else None
                            inh = (f'; this line is word for word line {ln} of lib/{arel} (the A file\'s modification '
                                   f'line, copied with the file; it holds the A image\'s value), and line {ln + 1} '
                                   f'states this file\'s value' if aline == t else '')
                            finds.append((UNIT, f'lib/{rel}', ln, old, new,
                                          f'{why}, image {ROLE[k]} {im.sha_pin}{inh}'))
    rows = sorted(set(rows))
    os.makedirs(a.out, exist_ok=True)
    with open(os.path.join(a.out, 'comment-checks.tsv'), 'w') as fh:
        fh.write('file\tline\tclaim\tmeasured\tresult\n')
        for r in rows:
            fh.write('\t'.join(map(str, r)) + '\n')
    with open(os.path.join(a.out, 'comment-rows.tsv'), 'w') as fh:
        fh.write('unit\tfile\tline\told\tnew\tevidence\n')
        for r in sorted(set(finds)):
            fh.write('\t'.join(map(str, r)) + '\n')
    for r in rows:
        print(*r, sep='\t')


if __name__ == '__main__':
    main()
