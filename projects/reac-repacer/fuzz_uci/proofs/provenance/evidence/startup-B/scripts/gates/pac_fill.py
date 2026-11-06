#!/usr/bin/env python3
"""pac_fill.py -- triage of EVERY GENERATOR-FILL row of a port_addr_check cb0e067e3bae TSV (finding of record: cb0e can
class a WRONG code pointer as GENERATOR-FILL when it repeats another value of the same sentence). Each row
gets a MEASURED reason or is UNEXPLAINED (exit 1). Part of the image-B start-up gate set. Reads only.

  pac_fill.py UNIT.tsv UCI_YF0m.v CGIF_YF0m.v UCI_IMG UCI_NMS CGIF_IMG CGIF_NM

Per ported LINE of YF0m.v named by a GENERATOR-FILL row (a z8 row carries two numerals: its cell and its value):
  A. the line is one of af0m's in-place FILLs (`(* FILL k: duplicate of row j (CELL/W) ... *)`, k listed in
     Tfib_const_abs_filled): row j must be (cell, width, value)-identical to this row and not itself a fill, and row j
     must hold the same symbol+offset in donor and unit (cell sym+off and value sym+off by each image's names, or the
     same image word). The donor slot it replaces must have no counterpart in this image (its cell's symbol absent from
     the unit's names, or a descriptor word past the unit's asan_globals).
  B. any other line: the cell must be file-backed with the stated value in the unit's image, and the donor slot's cell
     must hold the donor value in cgif's image with the same section and the same word (the same link-time datum).
"""
import collections
import csv
import re
import sys

from elftools.elf.elffile import ELFFile

TSV, UF, CF, UI, UN, CI, CN = sys.argv[1:8]


def nm(p):
    rows = []
    for l in open(p):
        s = l.split()
        if l.startswith('#') or len(s) < 3:
            continue
        a, z, t, n = (int(s[0], 16), int(s[1], 16), s[2], s[3]) if len(s) == 4 else (int(s[0], 16), 0, s[1], s[2])
        if t not in 'nNaA' and not n.startswith('$'):
            rows.append((a, z, n))
    return rows


def sym(rows, v):
    c = [(a, n) for a, z, n in rows if a <= v < a + max(z, 1)]
    return '%s+%#x' % (c[0][1], v - c[0][0]) if c else None


class Img:
    def __init__(self, p):
        e = ELFFile(open(p, 'rb'))
        self.loads = [(s['p_vaddr'], s['p_filesz'], s.data()) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
        self.secs = [(s.name, s['sh_addr'], s['sh_addr'] + s['sh_size'], s['sh_type']) for s in e.iter_sections()
                     if s['sh_addr']]
        ag = e.get_section_by_name('asan_globals')
        self.ag = (ag['sh_addr'], ag['sh_size']) if ag else None
        d = ag.data() if ag else b''
        # asan_globals descriptors: (beg, size, size_with_redzone) = words 0, 1, 2 of each 64-byte descriptor
        self.globs = [tuple(int.from_bytes(d[i + 8 * w:i + 8 * w + 8], 'little') for w in range(3))
                      for i in range(0, len(d), 64)]

    def word(self, a, n=8):
        for v, f, d in self.loads:
            if v <= a and a + n <= v + f:
                return int.from_bytes(d[a - v:a - v + n], 'little')

    def sec(self, a):
        c = [n for n, lo, hi, t in self.secs if lo <= a < hi]
        return c[0] if c else None

    def secoff(self, a):
        c = [(n, lo) for n, lo, hi, t in self.secs if lo <= a < hi]
        return '%s+%#x' % (c[0][0], a - c[0][1]) if c else None


def rows_of(path):
    t = open(path).read()
    m = re.search(r'Definition Tfib_const_abs : list acell :=\s*\[(.*?)\]\s*\.', t, re.S)
    start = t[:m.start(1)].count('\n') + 1
    out = []
    for i, l in enumerate(m.group(1).split('\n')):
        r = re.search(r'z(\d)\s+\(ANum (0x[0-9a-f]+)\)\s+(0x[0-9a-f]+|\d+)', l)
        if r:
            f = re.search(r'FILL (\d+): duplicate of row (\d+) \((0x[0-9a-f]+)/(\d+)\)', l)
            out.append(dict(line=start + i, w=int(r.group(1)), cell=int(r.group(2), 16), val=int(r.group(3), 0),
                            fill=(int(f.group(1)), int(f.group(2))) if f else None, text=l.strip()))
    filled = re.search(r'Definition Tfib_const_abs_filled : list nat := \[(.*?)\]', t, re.S)
    fl = {int(x) for x in re.findall(r'(\d+)%nat', filled.group(1))} if filled else set()
    return out, fl


U, C = Img(UI), Img(CI)
UNM, CNM = nm(UN), nm(CN)
urows, ufilled = rows_of(UF)
crows, _ = rows_of(CF)
byline = {r['line']: (k, r) for k, r in enumerate(urows)}
gf = [r for r in csv.DictReader([l for l in open(TSV) if not l.startswith('#')], delimiter='\t')
      if r['verdict'] == 'GENERATOR-FILL']
per = collections.defaultdict(list)
for r in gf:
    per[(r['dst_file'], int(r['dst_line']))].append(r)
print('GENERATOR-FILL rows: %d, on %d ported lines: %s' % (len(gf), len(per), dict(collections.Counter(f for f, _ in per))))
bad = 0


def key(nmrows, img, a):
    """an address by name: the covering sized symbol + offset, else section + offset (asan_globals has no sized symbol)"""
    return sym(nmrows, a) or img.secoff(a)


def same_sym_in_donor(r):
    """the unit row's cell and value by the unit's names, and a donor row with the same cell key and value key (or the
    same value when it is not an address of the image)"""
    cs, vs = key(UNM, U, r['cell']), (sym(UNM, r['val']) if U.sec(r['val']) else None)
    for d in crows:
        if key(CNM, C, d['cell']) == cs and cs is not None and \
                ((sym(CNM, d['val']) == vs) if vs else (d['val'] == r['val'] and not C.sec(d['val']))):
            return cs, vs, d
    return cs, vs, None


for (f, ln), trs in sorted(per.items()):
    src = sorted({(t['src_line'], t['src_value']) for t in trs if t['src_value']})
    if f != 'YF0m.v' or ln not in byline:
        print('  UNEXPLAINED %s:%d (not a Tfib_const_abs row of YF0m.v): %s' % (f, ln, [t['note'][:80] for t in trs]))
        bad += 1
        continue
    k, r = byline[ln]
    head = '  %s:%d row %d `%s`' % (f, ln, k, re.sub(r'\s*\(\*.*', '', r['text']))
    if r['fill']:
        fk, j = r['fill']
        rj = urows[j]
        ok_dup = (rj['cell'], rj['w'], rj['val']) == (r['cell'], r['w'], r['val']) and rj['fill'] is None and fk == k \
            and k in ufilled
        cs, vs, d = same_sym_in_donor(rj)
        # the donor slot this fill stands in for: the cgif cell at the same position, from the TSV's source numerals
        dcells = [int(v, 16) for _, v in src]
        dslot = [x for x in dcells if CI and any(dr['cell'] == x for dr in crows)]
        via = 'TSV'
        if not dslot:
            # no paired donor numeral (the tool: "an in-place fill, with no donor row of its own"): af0m's own comment
            # names the refused donor cell this fill stands in for
            mm = re.search(r'refused donor (?:cell|descriptor word) (0x[0-9a-f]+)', r['text'])
            dslot, via = ([int(mm.group(1), 16)], 'af0m comment') if mm else ([], 'none')
        why = []
        for x in dslot:
            s = sym(CNM, x)
            g = [(b, sz, rz) for b, sz, rz in C.globs if b <= x < b + rz]
            if C.ag and C.ag[0] <= x < C.ag[0] + C.ag[1]:
                off = x - C.ag[0]
                why.append('donor slot %#x = cgif asan_globals+%#x (descriptor %d word %d); this image\'s asan_globals is '
                           '%#x bytes (%d descriptor), so it has no such word' % (x, off, off // 64, (off % 64) // 8,
                                                                                    U.ag[1], U.ag[1] // 64))
            elif g:
                b, sz, rz = g[0]
                why.append('donor slot %#x (from the %s) = byte %d of cgif global [%#x, +%d) %s (size %d, with redzone %d); '
                           'this image\'s %d global(s) %s: no such global, so no such byte' % (
                               x, via, x - b, b, rz, 'REDZONE' if x - b >= sz else 'body', sz, rz, len(U.globs),
                               ['%#x/%d' % (bb, ss) for bb, ss, _ in U.globs]))
            elif s:
                name = s.split('+')[0]
                has = any(n == name for _, _, n in UNM)
                why.append('donor slot %#x = cgif %s; this image defines %s: %s' % (x, s, name, 'YES' if has else 'NO'))
            else:
                why.append('donor slot %#x = cgif %s (no name)' % (x, C.sec(x)))
        nocp = bool(why) and all(('NO' in w and 'YES' not in w) or 'no such' in w for w in why)
        ok = ok_dup and d is not None and nocp
        print('%s FILL %d = duplicate of row %d (line %d `%s`): identical and not a fill itself: %s; row %d by name: cell '
              '%s, value %s; donor row with the same cell + value names: %s; %s -> %s' % (
                  head, fk, j, rj['line'], re.sub(r'\s*\(\*.*', '', rj['text']), ok_dup, j, cs, vs or 'a datum',
                  'cgif line %d `%s`' % (d['line'], re.sub(r'\s*\(\*.*', '', d['text'])) if d else 'NONE',
                  '; '.join(why) or 'no donor slot in the TSV', 'ACCEPTED' if ok else 'UNEXPLAINED'))
    else:
        uw = U.word(r['cell'], r['w'])
        dcell = [int(v, 16) for _, v in src if any(dr['cell'] == int(v, 16) for dr in crows)]
        dr = [x for x in crows if dcell and x['cell'] == dcell[0]]
        dw = C.word(dr[0]['cell'], dr[0]['w']) if dr else None
        others = [x['line'] for x in urows if x is not r and (x['val'] == r['val'] or x['cell'] == r['cell'])]
        ok = uw == r['val'] and dr and dw == dr[0]['val'] == r['val'] and U.sec(r['cell']) == C.sec(dr[0]['cell'])
        print('%s not an af0m FILL: unit image word at %#x (%s) = %s; donor slot %s holds %s in cgif\'s image (%s), %s; '
              'other unit rows with this cell or value: lines %s -> %s' % (
                  head, r['cell'], U.sec(r['cell']), hex(uw) if uw is not None else 'not file-backed',
                  '%#x' % dr[0]['cell'] if dr else '?', hex(dw) if dw is not None else '?',
                  C.sec(dr[0]['cell']) if dr else '?', 'the same link-time word, a tp offset (negative), not an address'
                  if ok and r['val'] >= 1 << 63 else '', others, 'ACCEPTED' if ok else 'UNEXPLAINED'))
    bad += 0 if ok else 1
print('pac_fill: %d of %d ported lines UNEXPLAINED (%d GENERATOR-FILL rows)' % (bad, len(per), len(gf)))
sys.exit(1 if bad else 0)
