#!/usr/bin/env python3
"""Planted known answers for the value gate (port_addr_check 3d2eee813cce) on copies of this unit's lib/A and lib/B.
Each plant replaces ONE numeral on ONE line of a copy; the base copy is the unit's file unchanged.
Classes planted: (1) stale donor code pointer, (2) .got cell moved to the adjacent GOT word (mis-map class A),
(3) model constant that looks like an address moved by a delta (mis-map class B), (4) stale donor data pointer.
Usage: mkplants.py UNIT_LIB OUTDIR   (writes OUTDIR/{A,B}-{base,plant}/ and OUTDIR/plants.tsv)"""
import os, shutil, sys

unit, out = sys.argv[1:3]
PLANTS = [
    # side, file, line, old, new, class
    ('A', 'AB1v.v', 15, '0x8646c', '0x80418', 'stale donor code pointer (cgif tfibguard_start)'),
    ('A', 'ACeg.v', 21, '0xa6448', '0xa6450', '.got cell moved to the next GOT word (class A)'),
    ('A', 'AE6k.v', 1387, '0x200000', '0x20051c', 'model constant moved by a code delta (class B)'),
    ('A', 'AE7d.v', 35, '0xa8258', '0x9fdd0', 'stale donor data pointer (cgif real_strnlen slot)'),
    ('B', 'YB1v.v', 15, '0x864b8', '0x80448', 'stale donor code pointer (cgif YB1v tfibguard_start)'),
    ('B', 'YCeg.v', 22, '0xa5fa8', '0xa5fb0', '.got cell moved to the next GOT word (class A)'),
    ('B', 'YE30.v', 1394, '0x200000', '0x20051c', 'model constant moved by a code delta (class B)'),
    ('B', 'YE7d.v', 36, '0xa7db8', '0xa0040', 'stale donor data pointer (cgif YE7d real_strnlen slot)'),
]
rows = []
for side in ('A', 'B'):
    src = os.path.join(unit, side)
    for kind in ('base', 'plant'):
        d = os.path.join(out, f'{side}-{kind}')
        if os.path.exists(d):
            shutil.rmtree(d)
        shutil.copytree(src, d)
for side, f, ln, old, new, cls in PLANTS:
    p = os.path.join(out, f'{side}-plant', f)
    lines = open(p).read().split('\n')
    assert lines[ln - 1].count(old) == 1, (f, ln, lines[ln - 1])
    lines[ln - 1] = lines[ln - 1].replace(old, new)
    open(p, 'w').write('\n'.join(lines))
    rows.append((side, f, str(ln), old, new, cls))
with open(os.path.join(out, 'plants.tsv'), 'w') as fh:
    fh.write('side\tfile\tline\tunit_value\tplanted\tclass\n')
    for r in rows:
        fh.write('\t'.join(r) + '\n')
print(len(rows), 'plants')
