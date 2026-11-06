#!/usr/bin/env python3
"""ae3i.py -- a unit's lib/A/AE3i.v (image A) / its B twin: IMG_RO_LO, IMG_RO_HI and img_ro_chunks from the unit's own
ELF and its generated AF0m, with the donor's text otherwise.

  ae3i.py --tmpl DONOR/A/AE3i.v --owned <unit AF0m.v> --image <unit ELF> --out A/AE3i.v
          [--img-ro-hi 0x...] [--ns FROM=TO ...] [--modified TEXT]

THE RULE, measured on the donor (cgif A): `img_ro_chunks` is exactly [IMG_RO_LO, IMG_RO_HI) MINUS the Tfib_owned_static
ranges, as CImg chunks - the same cut AD2j makes below .data - and reproduces cgif's 15 chunks byte for byte.
IMG_RO_LO is the read-only PT_LOAD's start (0x10000 on every Pau image so far).

IMG_RO_HI IS NOT DERIVABLE. cgif states 0x2f1ac on BOTH its images, and that address falls inside an .eh_frame FDE at a
different offset in each (A: inside the FDE at 0x2f18c, 60 bytes; B: inside the one at 0x2f1a8, 20 bytes), while the two
sections have different lengths - so it is a number chosen once, below both segment ends, not a structural boundary.
Relocating it is therefore wrong by construction: boxreg's relocated 0x2f034 is PAST its own read-only segment end
0x2ef58, which would claim image bytes that do not exist. The rule here is the sound one: IMG_RO_HI = the unit's OWN
read-only PT_LOAD end (--img-ro-hi overrides, e.g. to reproduce the donor's file). Gates, each refusing: every chunk
inside [IMG_RO_LO, IMG_RO_HI), ordered and disjoint; IMG_RO_HI <= the read-only segment's end; every chunk byte
file-backed in that segment.
"""
import argparse, re, sys
from elftools.elf.elffile import ELFFile


def ro_segment(image):
    e = ELFFile(open(image, 'rb'))
    segs = [(s['p_vaddr'], s['p_vaddr'] + s['p_filesz'], s['p_vaddr'] + s['p_memsz'])
            for s in e.iter_segments() if s['p_type'] == 'PT_LOAD' and not (s['p_flags'] & 2) and not (s['p_flags'] & 1)]
    if not segs:
        sys.exit('ae3i: %s has no read-only (non-writable, non-executable) PT_LOAD' % image)
    lo, fend, mend = sorted(segs)[0]
    if fend != mend:
        sys.exit('ae3i: the read-only PT_LOAD of %s has %d bytes with no file content' % (image, mend - fend))
    return lo, mend


def owned(af0m):
    t = open(af0m).read()
    i = t.index('Definition Tfib_owned_static'); j = t.index('].', i)
    return sorted((int(x, 16), int(eval(y))) for x, y in re.findall(r'\((0x[0-9a-f]+), ([^)]+)\)', t[i:j]))


def chunks(lo, hi, own):
    out, cur = [], lo
    for a, n in own:
        b = a + n
        if b <= cur or a >= hi:
            continue
        if a > cur:
            out.append((cur, min(a, hi)))
        cur = max(cur, b)
    if cur < hi:
        out.append((cur, hi))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tmpl', required=True); ap.add_argument('--owned', required=True); ap.add_argument('--image', required=True)
    ap.add_argument('--out', required=True); ap.add_argument('--img-ro-hi', type=lambda s: int(s, 0), default=None)
    ap.add_argument('--ns', action='append', default=[]); ap.add_argument('--modified', default=None)
    a = ap.parse_args()
    lo, send = ro_segment(a.image)
    hi = a.img_ro_hi if a.img_ro_hi is not None else send
    if hi > send:
        sys.exit('ae3i: REFUSED: IMG_RO_HI %#x is past the read-only segment end %#x of %s' % (hi, send, a.image))
    cs = chunks(lo, hi, owned(a.owned))
    prev = lo
    for c0, c1 in cs:
        if not (lo <= c0 < c1 <= hi) or c0 < prev:
            sys.exit('ae3i: REFUSED: chunk %#x..%#x is outside [%#x, %#x) or out of order' % (c0, c1, lo, hi))
        prev = c1
    t = open(a.tmpl).read()
    t = re.sub(r'Definition IMG_RO_LO : Z := 0x[0-9a-f]+\.', 'Definition IMG_RO_LO : Z := %#x.' % lo, t)
    t = re.sub(r'Definition IMG_RO_HI : Z := 0x[0-9a-f]+\.', 'Definition IMG_RO_HI : Z := %#x.' % hi, t)
    body = ';\n'.join('YP09.mkChunk %#x (CImg (%s - %#x))' % (c0, 'IMG_RO_HI' if c1 == hi else '%#x' % c1, c0) for c0, c1 in cs)
    t = re.sub(r'Definition img_ro_chunks : list YP09\.chunk :=\n\[.*?\]\.', 
               'Definition img_ro_chunks : list YP09.chunk :=\n[ %s ].' % body, t, flags=re.S)
    for x in a.ns:
        f_, to_ = x.split('=', 1)
        t = t.replace(f_, to_)
    if a.modified:
        L = t.split('\n'); last = max(i for i, l in enumerate(L[:12]) if l.startswith('(*'))
        L[last + 1:last + 1] = ['(* Modified by Theorem Labs, 2026-10: %s *)' % a.modified]
        t = '\n'.join(L)
    open(a.out, 'w').write(t)
    print('ae3i: wrote %s: IMG_RO_LO %#x, IMG_RO_HI %#x (read-only PT_LOAD %#x..%#x), %d chunks (the region minus %d owned '
          'ranges)' % (a.out, lo, hi, lo, send, len(cs), len(owned(a.owned))))


if __name__ == '__main__':
    main()
