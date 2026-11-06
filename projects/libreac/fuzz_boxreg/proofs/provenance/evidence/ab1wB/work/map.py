"""Map every tfib_A_*/tfib_E_* row of the A core's AB1w.v (fuzz_boxreg.asan) to
fuzz_boxreg.asan-ubsan, by symbol identity and, where a name occurs more than
once, by instruction comparison."""
import json
import os
import re
import sys

sys.path.insert(0, os.environ.get('REVCHECK_DIR') or sys.exit('set REVCHECK_DIR to the directory holding revcheck.py (NOTES.md, Commands)'))
sys.path.insert(0, os.environ.get('ELFDIS_DIR') or sys.exit('set ELFDIS_DIR to the directory holding elfdis.py (NOTES.md, Commands)'))
import elfdis  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, '../../../../lib/A/AB1w.v')
ROOT = os.environ.get('PIPELINE_ROOT') or sys.exit('set PIPELINE_ROOT to the pipeline libreac root (it holds bin/ and unstripped/)')
PA = ROOT + '/unstripped/fuzz_boxreg/fuzz_boxreg.asan'
PB = ROOT + '/unstripped/fuzz_boxreg/fuzz_boxreg.asan-ubsan'

S = json.load(open(os.path.join(HERE, 'syms.json')))
FA = [(n, v, z) for n, t, v, z in S['asan']['syms'] if t == 2 and n]
FB = [(n, v, z) for n, t, v, z in S['ubsan']['syms'] if t == 2 and n]
IA, IB = elfdis.load(PA), elfdis.load(PB)

REG = re.compile(r'\b(x\d+|zero|ra|sp|gp|tp|t[0-6]|s(?:[0-9]|10|11)|a[0-7]|f[a-z0-9]+)\b')


def shape(ins):
    """mnemonic + register sequence; immediates ignored (fnstart.tsv's IMM rule)."""
    return [(m, tuple(REG.findall(o))) for _a, m, o in ins]


def cmp_code(a, sa, b, sb):
    x, y = shape(elfdis.disasm(IA, a, sa)), shape(elfdis.disasm(IB, b, sb))
    if not x and not y:
        return 1.0, 0, 0
    n = min(len(x), len(y))
    eq = sum(1 for i in range(n) if x[i] == y[i])
    return eq / max(len(x), len(y), 1), eq, max(len(x), len(y))


rows, order = [], []
for ln, line in enumerate(open(SRC), 1):
    m = re.match(r'Definition tfib_A_(\w+) : Z := (0x[0-9a-f]+)\.\s+Definition tfib_E_\1 : Z := (0x[0-9a-f]+)\.', line.strip())
    if m:
        rows.append((m.group(1), int(m.group(2), 16), int(m.group(3), 16), ln))
    order.append((ln, line.rstrip('\n')))

byaddr_a = {}
for n, v, z in FA:
    byaddr_a.setdefault(v, []).append((n, z))
byname_b = {}
for n, v, z in FB:
    byname_b.setdefault(n, []).append((v, z))

out = []
for name, a, e, ln in rows:
    cands = [(n, z) for n, z in byaddr_a.get(a, []) if a + z == e]
    exact = bool(cands)
    if not cands:                                   # size-0 asm symbols (start, set_thread_area)
        cands = [(n, z) for n, z in byaddr_a.get(a, [])]
    anames = sorted({n for n, _ in cands})
    hits = []
    for n in anames:
        for v, z in byname_b.get(n, []):
            hits.append((n, v, z))
    out.append(dict(row=name, line=ln, a=a, e=e, exact=exact, anames=anames, hits=hits))

json.dump(out, open(os.path.join(HERE, 'rows.json'), 'w'))
print('rows', len(rows))
print('no asan symbol at A:', [(r['row'], hex(r['a'])) for r in out if not r['anames']])
print('no ubsan twin:', [(r['row'], r['anames']) for r in out if r['anames'] and not r['hits']])
amb = [r for r in out if len(r['hits']) > 1]
print('ambiguous:', len(amb))
for r in amb:
    print('  ', r['row'], hex(r['a']), r['anames'], [(hex(v), hex(z)) for _n, v, z in r['hits']])
