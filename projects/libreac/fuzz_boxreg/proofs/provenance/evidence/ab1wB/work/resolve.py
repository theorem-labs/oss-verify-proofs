"""Resolve each A-core AB1w row to fuzz_boxreg.asan-ubsan and verdict it by code."""
import json
import os
import re
import sys

sys.path.insert(0, os.environ.get('REVCHECK_DIR') or sys.exit('set REVCHECK_DIR to the directory holding revcheck.py (NOTES.md, Commands)'))
sys.path.insert(0, os.environ.get('ELFDIS_DIR') or sys.exit('set ELFDIS_DIR to the directory holding elfdis.py (NOTES.md, Commands)'))
import elfdis  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
W = HERE + '/'
SRC = os.path.join(HERE, '../../../../lib/A/AB1w.v')
ROOT = os.environ.get('PIPELINE_ROOT') or sys.exit('set PIPELINE_ROOT to the pipeline libreac root (it holds bin/ and unstripped/)')
PA = ROOT + '/unstripped/fuzz_boxreg/fuzz_boxreg.asan'
PB = ROOT + '/unstripped/fuzz_boxreg/fuzz_boxreg.asan-ubsan'

S = json.load(open(W + 'syms.json'))
FA = sorted({(v, z, n) for n, t, v, z in S['asan']['syms'] if t == 2 and n})
FB = sorted({(v, z, n) for n, t, v, z in S['ubsan']['syms'] if t == 2 and n})
IA, IB = elfdis.load(PA), elfdis.load(PB)
REG = re.compile(r'\b(x\d+|zero|ra|sp|gp|tp|t[0-6]|s10|s11|s[0-9]|a[0-7]|f[a-z0-9]+)\b')


def shape(ins):
    return [(m, tuple(REG.findall(o))) for _a, m, o in ins]


def full(ins):
    return [(m, o) for _a, m, o in ins]


def verdict(a, sa, b, sb):
    xa, xb = elfdis.disasm(IA, a, sa), elfdis.disasm(IB, b, sb)
    if full(xa) == full(xb):
        return 'SAME', len(xa), len(xb), len(xa)
    sh_a, sh_b = shape(xa), shape(xb)
    if sh_a == sh_b:
        return 'IMM', len(xa), len(xb), len(xa)
    n = min(len(sh_a), len(sh_b))
    eq = sum(1 for i in range(n) if sh_a[i] == sh_b[i])
    return 'SHAPE', len(xa), len(xb), eq


rows = []
for ln, line in enumerate(open(SRC), 1):
    m = re.match(r'Definition tfib_A_(\w+) : Z := (0x[0-9a-f]+)\.\s+Definition tfib_E_\1 : Z := (0x[0-9a-f]+)\.', line.strip())
    if m:
        rows.append((m.group(1), int(m.group(2), 16), int(m.group(3), 16), ln))

byaddr_a, byname_b = {}, {}
for v, z, n in FA:
    byaddr_a.setdefault(v, []).append((n, z))
for v, z, n in FB:
    byname_b.setdefault(n, []).append((v, z))
addrs_b = sorted({v for v, z, n in FB})

res, notwin, amb = [], [], []
for name, a, e, ln in rows:
    cands = [(n, z) for n, z in byaddr_a.get(a, []) if a + z == e]
    zero = False
    if not cands:
        cands = list(byaddr_a.get(a, []))
        zero = True
    anames = sorted({n for n, _ in cands})
    per = {n: sorted(set(byname_b.get(n, []))) for n in anames}
    single = sorted({p[0] for n, p in per.items() if len(p) == 1})
    if single:                              # a name that occurs once in asan-ubsan decides
        places = single
        pick_name = [n for n in anames if len(per[n]) == 1][0]
    else:
        places = sorted({x for p in per.values() for x in p})
        pick_name = anames[0]
    if not places:
        notwin.append((name, hex(a), anames))
        continue
    if len(places) == 1:
        b, bz = places[0]
        how = 'unique-symbol %s' % pick_name
    else:
        # duplicate static symbol (identical instances): pair by ordinal, then verify by code
        aa = sorted({v for v, z, n in FA if n == pick_name})
        bb = sorted({(v, z) for v, z, n in FB if n == pick_name})
        if len(aa) != len(bb) or a not in aa:
            raise SystemExit('cannot pair %s at %#x' % (name, a))
        b, bz = bb[aa.index(a)]
        vd0 = verdict(a, e - a, b, bz)
        how = 'ordinal %d/%d of %s, code %s %d/%d' % (aa.index(a) + 1, len(aa), pick_name, vd0[0], vd0[1], vd0[2])
        amb.append((name, hex(a), pick_name, hex(b), how,
                    [(hex(v), verdict(a, e - a, v, z)[0]) for v, z in bb]))
    if zero:                                # size-0 asm symbol: A-core's own rule per row
        if name == 'start':                 # row covers _start + _start_c (A notes)
            nxt = min((v for v, z, n in FB if v > b), default=None)
            nz = max(z for v, z, n in FB if v == nxt)
            be = nxt + nz
        else:                               # set_thread_area: E = next FUNC start
            be = min((x for x in addrs_b if x > b), default=None)
        vd = verdict(a, e - a, b, be - b)
    else:
        be = b + bz
        vd = verdict(a, e - a, b, bz)
    res.append(dict(row=name, line=ln, a=a, e=e, b=b, be=be, anames=anames, how=how, zero=zero,
                    verdict=vd[0], na=vd[1], nb=vd[2], eq=vd[3]))

json.dump(dict(res=res, notwin=notwin, amb=amb), open(W + 'resolved.json', 'w'))
from collections import Counter  # noqa: E402
print('rows', len(rows), 'resolved', len(res), 'no-twin', len(notwin))
print(Counter(r['verdict'] for r in res))
print('size differs:', sum(1 for r in res if r['e'] - r['a'] != r['be'] - r['b']))
print('ambiguous resolved by code:', len(amb))
for x in amb:
    print('  ', x)
print('no-twin:', notwin)
print('SHAPE rows:')
for r in res:
    if r['verdict'] == 'SHAPE':
        print('   %-50s A %#x..%#x  B %#x..%#x  insns %d/%d eq %d' % (r['row'], r['a'], r['e'], r['b'], r['be'], r['na'], r['nb'], r['eq']))
