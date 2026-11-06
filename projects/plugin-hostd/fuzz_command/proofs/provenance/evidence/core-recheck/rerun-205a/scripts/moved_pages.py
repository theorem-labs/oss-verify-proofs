#!/usr/bin/env python3
"""Supplementary: every 205a SAME-SYMBOL row whose donor value is page-aligned and whose ported value differs, i.e.
a value 205a's closed size-slot list did not read as a size although it moved. Each is measured against our pin:
  EXTENT          the tool names an image quantity (dst_res `val:<q>`): our value against that quantity of our pin
  symbol+offset   both sides name the same symbol + offset and our value is not page-aligned: an address the port
                  moved with its symbol, not a size (a size would keep its page-aligned value)
Usage: moved_pages.py GATE FULL_205A.tsv IMGDIR OUT.tsv"""
import os
import re
import sys
from elftools.elf.elffile import ELFFile

gate, full_p, imgdir, out_p = sys.argv[1:5]
side = {'RA': 'A', 'RB': 'B'}[gate]
P = 0x1000


def geom(pin):
    with open(pin, 'rb') as f:
        L = [(s['p_vaddr'], s['p_memsz']) for s in ELFFile(f).iter_segments() if s['p_type'] == 'PT_LOAD']
    g = {}
    for i, (a, n) in enumerate(L):
        g[f'seg{i}.lo'], g[f'seg{i}.hi'] = a & ~(P - 1), (a + n + P - 1) & ~(P - 1)
        g[f'seg{i}.size'] = g[f'seg{i}.hi'] - g[f'seg{i}.lo']
    g['image.lo'] = min(g[f'seg{i}.lo'] for i in range(len(L)))
    g['image.top'] = max(g[f'seg{i}.hi'] for i in range(len(L)))
    g['image.span'] = g['image.top'] - g['image.lo']
    return g


G = geom(os.path.join(imgdir, f'cmd.{side}.pin'))
GD = geom(os.path.join(imgdir, f'cgif.{side}.pin'))
rows = [l.rstrip('\n').split('\t') for l in open(full_p, encoding='utf-8', errors='replace') if not l.startswith('#')]
ix = {c: i for i, c in enumerate(rows[0])}
out, bad = [], 0
for r in rows[1:]:
    if not r[ix['verdict']].startswith('SAME-SYMBOL'):
        continue
    try:
        sv, tv = int(r[ix['src_value']], 0), int(r[ix['dst_value']], 0)
    except ValueError:
        continue
    if not sv or sv % P or sv == tv:
        continue
    res = r[ix['dst_res']]
    if res.startswith('EXTENT'):
        qs = re.findall(r'val:([\w.]+)', res)
        hit = [q for q in qs if G.get(q) == tv]
        dhit = [q for q in re.findall(r'val:([\w.]+)', r[ix['src_res']]) if GD.get(q) == sv]
        ok = bool(hit) and bool(dhit)
        why = (f'our value {tv:#x} = {", ".join(hit) or "no named quantity"} of cmd.{side}.pin; the donor value '
               f'{sv:#x} = {", ".join(dhit) or "no named quantity"} of cgif.{side}.pin')
    else:
        # a `pc: ` prefix is the tool's role note (a fetch address), not part of the symbol + offset
        so, sd = (x.split(';')[0].replace('pc: ', '', 1).strip() for x in (res, r[ix['src_res']]))
        ok = tv % P != 0 and so == sd
        why = (f'both sides name {so}; our value {tv:#x} is not page-aligned: an address moved with its symbol, not '
               f'a size' if ok else 'OPEN: not an image quantity and not an unaligned same-symbol address')
    bad += not ok
    out.append([gate, f'lib/{side}/{r[ix["dst_file"]]}:{r[ix["dst_line"]]}', r[ix['sentence']], r[ix['src_value']],
                r[ix['dst_value']], 'OK' if ok else 'OPEN', why])
with open(out_p, 'w') as f:
    f.write('\t'.join(['gate', 'file:line', 'sentence', 'donor_value', 'our_value', 'triage', 'measured']) + '\n')
    for o in out:
        f.write('\t'.join(o) + '\n')
print(f'{gate}: {len(out)} rows, {len(out) - bad} OK, {bad} OPEN')
sys.exit(1 if bad else 0)
