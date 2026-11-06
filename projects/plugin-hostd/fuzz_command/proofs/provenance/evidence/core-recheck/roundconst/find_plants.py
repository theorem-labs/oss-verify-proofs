#!/usr/bin/env python3
"""Candidate positions for the planted controls of the v2 by-value gate on this unit.

A candidate is a row of the base run (port_addr_check full TSV) where the port CHANGED the donor numeral
(src_value != dst_value) and the donor numeral is a donor image quantity Q whose target counterpart is the
port's value (T[Q] == dst_value) -- i.e. the port moved a donor quantity to the target's own. Planting the donor
numeral back at that position makes the row "kept" (the false negative the gate is for).
Each candidate is put in one control class by the gate's own rules (the definitions of roundconst.py v2 and v1
are loaded from their files, not re-implemented):
  C2   segment / section length (no divisor), value >= 0x100, v2 status after the plant MISMATCH
  C3w  word count: a name with divisor /4, v2 MISMATCH after the plant, and v1 does NOT select the value
  C3t  small table length: value < 0x100, a symbol-size / extent-to-next name, v2 MISMATCH (v1 floors it)
  C4   gap: value < 0x100, v2 SAME after the plant (one name agrees in the target), while a name of it has the
       port's value as its target counterpart
Only lines where the dst numeral occurs exactly once (as hex or decimal text) are listed, so the plant is one
textual replacement. Usage: find_plants.py RUN_FULL_TSV KEY DONOR_SPEC TARGET_SPEC V2_PY V1_PY UNIT_LIBDIR SIDE"""
import collections, re, sys

tsv, key, dspec, tspec, v2py, v1py, libdir, side = sys.argv[1:9]


def load(py):
    src = open(py).read()
    cut = src.index('\ntsv, dspec, tspec, pre = sys.argv[1:5]')
    ns = {'__name__': 'gate'}
    exec(compile(src[:cut], py, 'exec'), ns)
    return ns


g2, g1 = load(v2py), load(v1py)
D, DC = g2['geometry'](dspec)
T, TC = g2['geometry'](tspec)
MIN, POS, SYMB = g2['MIN'], g2['POSITIONAL'], g2['SYMBOLIC']
INV = collections.defaultdict(list)
for nm, v in D.items():
    if v >= MIN or DC[nm] not in POS:
        INV[v].append(nm)
D1 = g1['geometry'](dspec.split(':')[0])
INV1 = {v for v in D1.values() if v >= g1['MIN']}


def status(val):
    """v2's status for a kept value `val` (the code of roundconst.py v2, lines 218-233)"""
    names = [nm for nm in INV.get(val, []) if nm in T or (val >= MIN and DC[nm] not in SYMB)]
    if not names:
        return None, []
    tq = [(nm, T.get(nm)) for nm in names]
    eq = [nm for nm, v in tq if v == val]
    miss = [nm for nm, v in tq if v is None]
    if val >= MIN:
        st = ('SAME' if len(eq) == len(names) else 'MISMATCH' if not eq and not miss else
              'NO-COUNTERPART' if not eq else 'MIXED')
    else:
        st = 'SAME' if eq else 'MISMATCH'
    return st, names


GEN = {'AB01', 'AB03', 'AF0m', 'AD2j', 'AE3i', 'ACej', 'AB1w', 'YB01', 'YB03', 'YF0m', 'YD2j', 'YE3i', 'YCej', 'YB1w'}
cache = {}
out = collections.defaultdict(list)
for l in open(tsv, encoding='utf-8', errors='replace'):
    if l.startswith('#') or l.startswith('verdict\t'):
        continue
    f = l.rstrip('\n').split('\t') + [''] * 16
    if f[2] != key or f[9] == 'ident' or not f[10] or not f[11]:
        continue
    try:
        sv, tv = int(f[10], 16), int(f[11], 16)
    except ValueError:
        continue
    if sv == tv or sv not in INV:
        continue
    moved_to = [nm for nm in INV[sv] if T.get(nm) == tv]     # the port's value is that name's target quantity
    st, names = status(sv)
    if st is None:
        continue
    undiv = lambda nm: '/' not in nm.rsplit(')', 1)[-1]
    c = None
    if sv >= MIN and st == 'MISMATCH' and any(DC[nm] in ('segment', 'section') and undiv(nm) for nm in names):
        c = 'C2'
    elif st == 'MISMATCH' and any(nm.endswith('/4') for nm in names) and sv not in INV1:
        c = 'C3w'
    elif sv < MIN and st == 'MISMATCH' and any(DC[nm] in ('symbol-size', 'extent-to-next') and undiv(nm)
                                               for nm in names):
        c = 'C3t'
    elif sv < MIN and st == 'SAME' and moved_to:
        c = 'C4'
    if c is None:
        continue
    fn, ln = f[5], int(f[6])
    base = fn.rsplit('/', 1)[-1].split('.')[0]
    if fn not in cache:
        try:
            cache[fn] = open(f'{libdir}/{side}/{fn}').read().split('\n')
        except OSError:
            cache[fn] = None
    L = cache[fn]
    if L is None or ln > len(L):
        continue
    t = L[ln - 1]
    hits = [p for p in (hex(tv), str(tv)) if re.search(r'(?<![\w.])' + re.escape(p) + r'(?![\w])', t, re.I)]
    cnt = sum(len(re.findall(r'(?<![\w.])' + re.escape(p) + r'(?![\w])', t, re.I)) for p in (hex(tv), str(tv)))
    if cnt != 1:
        continue
    out[c].append((fn, ln, f[0], hex(sv), hex(tv), hits[0], '; '.join(moved_to[:3]), '; '.join(names[:4]),
                   'GEN' if base in GEN else '', t.strip()[:140]))
ROLEW = re.compile(r'_count|_len|_words|_nwords|_size|_cnt|length|_tab|_table|_entries|seg ')
for c in ('C2', 'C3w', 'C3t', 'C4'):
    rows = sorted(out[c], key=lambda r: (not r[6], not ROLEW.search(r[9]), r[0], r[1]))
    print(f'## {c} {len(rows)}  (sorted: the port moved it to the name\'s target quantity first, then role words)')
    for r in rows[:80]:
        print('\t'.join(map(str, r)))
