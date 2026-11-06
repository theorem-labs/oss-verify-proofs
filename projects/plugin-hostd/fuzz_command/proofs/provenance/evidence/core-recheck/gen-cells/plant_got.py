#!/usr/bin/env python3
"""Known-answer control for mis-map class (A), a .got cell mapped to the wrong GOT word, on AF0m.v / YF0m.v.

For every donor-position cell of Tfib_const_abs that lies in .got, plant the cell at the GOT word 8 and 16 bytes
below and above (address A' and value V' = the image's bytes at A', so the value rule alone passes), and re-judge
the planted cell with the address and value rules of f0m_rules.  Also plant every word of the owned .got ranges of
Tfib_owned_static one word over.  A plant the rules accept is printed.

  plant_got.py --lib OURS_LIB --donor-lib DONOR_LIB --img IMG_DIR --out OUT_DIR   (writes plant-got.tsv)
"""
import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import imgmeas  # noqa: E402
import f0m_rules  # noqa: E402

FILES = {'A': ('A/AF0m.v', 'A/AF0m.v'), 'B': ('B/YF0m.v', 'YF0m.v')}


def main():
    ap = argparse.ArgumentParser()
    for x in ('--lib', '--donor-lib', '--img', '--out'):
        ap.add_argument(x, required=True)
    a = ap.parse_args()
    out = []
    for k in 'AB':
        im = imgmeas.Img(os.path.join(a.img, f'cmd.{k}.pin'), os.path.join(a.img, f'cmd.{k}.twin'), k)
        dm = imgmeas.Img(os.path.join(a.img, f'cgif.{k}.pin'), os.path.join(a.img, f'cgif.{k}.twin'), k)
        g = f0m_rules.F0m(open(os.path.join(a.lib, FILES[k][0])).read(),
                          open(os.path.join(a.donor_lib, FILES[k][1])).read(), im, dm, k)
        glo, ghi = im.section('.got')[1:3]
        for i, (ln, w, ad, v) in enumerate(g.abs[:f0m_rules.N_DONOR]):
            if im.secname(ad) != '.got':
                continue
            for d in (-16, -8, 8, 16):
                a2 = ad + d
                if not (glo <= a2 and a2 + w <= ghi):
                    continue
                v2 = im.word(a2, w)
                oka = g.addr_judge(i, ln, w, a2, v2)(a2)
                okv = g.val_judge(i, ln, w, a2, v2)(v2)
                acc = oka[0] and okv[0]
                out.append((k, FILES[k][0], ln, 'cell', f'{ad:#x}', f'{a2:#x}', f'{v2:#x}',
                            'ACCEPTED' if acc else 'refused', oka[2]))
        # owned .got ranges: shift the range by one word
        for s in g.owned_slots():
            if s.role != 'owned-lo' or im.secname(s.value) != '.got':
                continue
            for d in (-8, 8):
                ok = s.judge(s.value + d)
                out.append((k, FILES[k][0], s.line, 'owned-lo', f'{s.value:#x}', f'{s.value + d:#x}', '-',
                            'ACCEPTED' if ok[0] else 'refused', ok[2]))
    with open(os.path.join(a.out, 'plant-got.tsv'), 'w') as fh:
        fh.write('key\tfile\tline\twhat\taddr\tplanted_addr\tplanted_value\tresult\tmeasurement\n')
        for r in out:
            fh.write('\t'.join(map(str, r)) + '\n')
    n = len(out)
    acc = [r for r in out if r[7] == 'ACCEPTED']
    print(f'plants {n}, refused {n - len(acc)}, accepted {len(acc)}')
    for r in acc:
        print('ACCEPTED', *r)


if __name__ == '__main__':
    main()
