#!/usr/bin/env python3
"""Measured rules for every numeral of the read-only image chunk file (lib/A/AE3i.v, lib/B/YE3i.v).

  RO-LO          IMG_RO_LO = the vaddr of the first PT_LOAD (section/segment headers of the pin).
  RO-HI          IMG_RO_HI = the end of .eh_frame = the end of the first PT_LOAD's file bytes.
  RO-CHUNK-BOUND img_ro_chunks = the runs of [IMG_RO_LO, IMG_RO_HI) that no Tfib_owned_static range of the sibling
                 cell file (lib/A/AF0m.v, lib/B/YF0m.v; every row of it measured by f0m_rules) covers, cut at the
                 .rodata end; each chunk is written mkChunk LO (CImg (HI - LO)), the last one with HI = IMG_RO_HI.
                 The file's list must equal the recomputed list entry by entry.  (The bytes are the image's by
                 construction, CImg; the file's img_ro_bytes_ok checks by vm_compute that every chunk byte is an
                 image byte.)
"""
import re

from f0m_rules import Slot, blocks, pairs

CH = re.compile(r'mkChunk (0x[0-9a-fA-F]+) \(CImg \((0x[0-9a-fA-F]+|IMG_RO_HI) - (0x[0-9a-fA-F]+)\)\)')


def h(x):
    return f'{x:#x}'


def runs(lo, hi, own, cuts):
    holes = sorted((a, a + s) for a, s in own if a < hi and a + s > lo)
    out, cur = [], lo
    why = []
    cw = 'IMG_RO_LO'
    for a, b in holes:
        if a > cur:
            out.append((cur, min(a, hi)))
            why.append((cw, f'start of owned range ({h(a)}, {h(b - a)})'))
        if b > cur:
            cur, cw = b, f'end of owned range ({h(a)}, {h(b - a)})'
    if cur < hi:
        out.append((cur, hi))
        why.append((cw, 'IMG_RO_HI'))
    res, rw = [], []
    for (a, b), (wa, wb) in zip(out, why):
        for c, cn in sorted(cuts):
            if a < c < b:
                res.append((a, c))
                rw.append((wa, f'cut at {cn} {h(c)}'))
                a, wa = c, f'cut at {cn} {h(c)}'
        res.append((a, b))
        rw.append((wa, wb))
    return res, rw


class E3i:
    def __init__(self, text, f0m_text, im):
        self.im = im
        self.text = text
        own = [(lo, sz) for ln, lo, sz, _ in pairs(blocks(f0m_text)['Tfib_owned_static'])]
        self.lo_exp = im.loads[0][0]
        self.hi_exp = im.section('.eh_frame')[2]
        first_file_end = im.loads[0][0] + im.loads[0][1]
        self.hi_note = (f'.eh_frame end {h(self.hi_exp)}; first PT_LOAD file bytes end {h(first_file_end)}')
        self.ro_end = im.section('.rodata')[2]
        self.exp, self.why = runs(self.lo_exp, self.hi_exp, own, [(self.ro_end, '.rodata end')])

    def slots(self):
        out = []
        lines = self.text.split('\n')
        im = self
        k = 0
        for i, t in enumerate(lines, 1):
            m = re.match(r'Definition IMG_RO_LO : Z := (0x[0-9a-fA-F]+)\.', t)
            if m:
                out.append(Slot(i, 0, int(m[1], 16), 'hex', 'IMG_RO_LO', 'ro-lo',
                                lambda x: (x == self.lo_exp, 'RO-LO', f'first PT_LOAD vaddr {h(self.lo_exp)}',
                                           self.lo_exp)))
            m = re.match(r'Definition IMG_RO_HI : Z := (0x[0-9a-fA-F]+)\.', t)
            if m:
                out.append(Slot(i, 0, int(m[1], 16), 'hex', 'IMG_RO_HI', 'ro-hi',
                                lambda x: (x == self.hi_exp, 'RO-HI', self.hi_note, self.hi_exp)))
            m = re.search(r'mkRegion None IMG_RO_LO IMG_RO_HI (\d+) (\d+)', t)
            if m:
                for p in (0, 1):
                    out.append(Slot(i, p, int(m[1 + p]), 'dec', 'img_ro_region', 'window',
                                    lambda x: (x == 0, 'MODEL-CONSTANT', 'no write window over the read-only image '
                                                                         '(0 0, as the donor)', 0)))
            for m in re.finditer(r'Z_to_bv (\d+)', t):
                out.append(Slot(i, 0, int(m[1]), 'dec', 'proof-step', 'word-width',
                                lambda x: (x == 64, 'MODEL-CONSTANT', 'word width of Z_to_bv 64 (RV64)', 64)))
            for m in CH.finditer(t):
                lo, lo2 = int(m[1], 16), int(m[3], 16)
                hi = None if m[2] == 'IMG_RO_HI' else int(m[2], 16)
                e = self.exp[k] if k < len(self.exp) else (None, None)
                wl, wh = self.why[k] if k < len(self.why) else ('?', '?')
                n = f'chunk {k} of {len(self.exp)}'
                pos = 0
                out.append(Slot(i, pos, lo, 'hex', 'img_ro_chunks', 'chunk-lo',
                                lambda x, e=e, wl=wl, n=n: (x == e[0], 'RO-CHUNK-BOUND', f'{n} lo = {wl}', e[0])))
                pos += 1
                if hi is not None:
                    out.append(Slot(i, pos, hi, 'hex', 'img_ro_chunks', 'chunk-hi',
                                    lambda x, e=e, wh=wh, n=n: (x == e[1], 'RO-CHUNK-BOUND', f'{n} hi = {wh}', e[1])))
                    pos += 1
                else:
                    assert e[1] == self.hi_exp, (k, e)
                out.append(Slot(i, pos, lo2, 'hex', 'img_ro_chunks', 'chunk-lo',
                                lambda x, e=e, wl=wl, n=n: (x == e[0], 'RO-CHUNK-BOUND', f'{n} lo = {wl}', e[0])))
                k += 1
        self.n_file = k
        return out
