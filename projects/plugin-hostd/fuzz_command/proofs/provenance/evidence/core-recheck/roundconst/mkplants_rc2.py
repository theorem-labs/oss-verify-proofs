#!/usr/bin/env python3
"""Planted controls of the v2 by-value gate (roundconst.py 32b39f3b34e9) on plugin-hostd/fuzz_command.

Each plant is a copy of the unit's lib/A (or lib/B) with ONE numeral set to the DONOR's numeral at that position
(column 11, src_value, of the base run of port_addr_check 3d2eee813cce), so the row becomes a kept value. Each planted
value is a cgif image quantity whose fuzz_command counterpart differs (or, for the gap control, also a right
fuzz_command quantity). The positions were chosen from find_plants.py's list (controls/plant_candidates.*.txt).
The plants are textual: no Coq build.

usage: mkplants_rc2.py UNIT_LIB OUTDIR      (UNIT_LIB holds A/ and B/ of tree a3c671fb9bb; writes OUTDIR/base-A/A,
       OUTDIR/base-B/B, OUTDIR/<plant>/<side> and OUTDIR/plants.tsv)"""
import os, shutil, sys

unit, out = sys.argv[1:3]
# name, side, file, line, old text, new text, control, donor value (base run col 11), what the planted value is
PLANTS = [
    ('A-c2a', 'A', 'AB13.v', 119, '= 143360%N.', '= 131072%N.', '2',
     '0x20000', 'cgif PT_LOAD0 page length 0x20000; fuzz_command 0x23000 (tfib_len0, v1 plant r1 shape)'),
    ('A-c2b', 'A', 'AB1h.v', 49, '(Z_to_bv 64 0x33000, Z_to_bv 64 0x72000)', '(Z_to_bv 64 0x33000, Z_to_bv 64 0x6d000)',
     '2', '0x6d000', 'cgif PT_LOAD1 page length 0x6d000; fuzz_command 0x72000 (tfib_res_eq, v1 plant r2 shape)'),
    ('A-c3w', 'A', 'AB01.v', 188, '++ seg HS_tfib_10_kn 1215 785', '++ seg HS_tfib_10_kn 214 785', '3w',
     '0xd6', 'WORD COUNT: 214 = cgif .relro_padding.size/4 (0x358/4); fuzz_command .relro_padding.size/4 differs'),
    ('A-c3w2', 'A', 'AD1k.v', 260, 'R_A1k 134700 631)', 'R_A1k 134700 67)', '3w',
     '0x43', 'WORD COUNT: 67 = cgif sym(errmsgidx).extent/4; fuzz_command sym(errmsgidx).extent/4 = 7'),
    ('A-c3t', 'A', 'AB01.v', 107, '++ seg HS_tfib_0_kn 1091 13', '++ seg HS_tfib_0_kn 88 13', '3t',
     '0x58', 'SMALL TABLE LENGTH: 88 = cgif sym(states).extent (musl states table); fuzz_command = 0x1d0'),
    ('A-c4', 'A', 'AF0m.v', 5175, '(0xaad00, 0x2d00);', '(0xaad00, 0xc0);', '4',
     '0xc0', 'GAP: 192 = cgif .asan_globals.size (fuzz_command 0x2d00) and also '
             'sym(_ZN6__lsanL23suppression_placeholderE).extent, 192 in both images'),
    ('B-c2a', 'B', 'YB13.v', 120, '= 143360%N.', '= 131072%N.', '2',
     '0x20000', 'cgif PT_LOAD0 page length 0x20000; fuzz_command 0x23000 (tfib_len0)'),
    ('B-c3w', 'B', 'YB01.v', 225, '++ seg HS_tfib_11_kn 1127 12', '++ seg HS_tfib_11_kn 126 12', '3w',
     '0x7e', 'WORD COUNT: 126 = cgif sym(sysconf.values).extent/4; fuzz_command = 0x7f'),
    ('B-c4', 'B', 'YF0m.v', 5176, '(0xaa860, 0x2d00);', '(0xaa860, 0xc0);', '4',
     '0xc0', 'GAP: 192 = cgif .asan_globals.size (fuzz_command 0x2d00) and also '
             'sym(_ZN6__lsanL23suppression_placeholderE).extent, 192 in both images'),
]
for side in ('A', 'B'):
    d = os.path.join(out, f'base-{side}', side)
    if os.path.exists(d):
        shutil.rmtree(d)
    shutil.copytree(os.path.join(unit, side), d)
with open(os.path.join(out, 'plants.tsv'), 'w') as fh:
    fh.write('plant\tside\tfile\tline\tunit_text\tplanted_text\tcontrol\tdonor_value\twhat\n')
    for name, side, f, ln, old, new, ctl, dv, what in PLANTS:
        d = os.path.join(out, name, side)
        if os.path.exists(d):
            shutil.rmtree(d)
        shutil.copytree(os.path.join(unit, side), d)
        p = os.path.join(d, f)
        L = open(p).read().split('\n')
        assert L[ln - 1].count(old) == 1, (name, L[ln - 1][:200])
        L[ln - 1] = L[ln - 1].replace(old, new)
        open(p, 'w').write('\n'.join(L))
        fh.write('\t'.join([name, side, f, str(ln), old, new, ctl, dv, what]) + '\n')
        print('planted', name, f'{side}/{f}:{ln}', old, '->', new)
