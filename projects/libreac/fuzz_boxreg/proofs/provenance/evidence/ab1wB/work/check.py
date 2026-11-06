"""Checks on ../AB1w.v (the same file as lib/B/AB1w.v) against fuzz_boxreg.asan-ubsan and the A-core file."""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
W = HERE + '/'
B = os.path.join(HERE, '../AB1w.v')
A = os.path.join(HERE, '../../../../lib/A/AB1w.v')
S = json.load(open(W + 'syms.json'))
FB = sorted({(v, z, n) for n, t, v, z in S['ubsan']['syms'] if t == 2 and n})
starts = {v for v, z, n in FB}
ends = {(v, v + z) for v, z, n in FB}
TEXT = (0x2ffb8, 0x97d40)
ASM0 = {'start', 'set_thread_area'}


def rows(p):
    out = []
    for ln, line in enumerate(open(p), 1):
        m = re.match(r'Definition tfib_A_(\w+) : Z := (0x[0-9a-f]+)\.\s+Definition tfib_E_\1 : Z := (0x[0-9a-f]+)\.$', line.strip())
        if m:
            out.append((m.group(1), int(m.group(2), 16), int(m.group(3), 16), ln))
    return out


ra, rb = rows(A), rows(B)
bad = []
print('A rows', len(ra), '| B rows', len(rb))
print('same names, same order:', [x[0] for x in ra] == [x[0] for x in rb])
names = [x[0] for x in rb]
print('duplicate names:', [n for n in set(names) if names.count(n) > 1])
rng = [(a, e) for _n, a, e, _l in rb]
print('duplicate ranges:', [r for r in set(rng) if rng.count(r) > 1])
print('outside .text [%#x, %#x):' % TEXT, [(n, hex(a), hex(e)) for n, a, e, _l in rb if not (TEXT[0] <= a < e <= TEXT[1])])
print('A not a FUNC st_value:', [(n, hex(a)) for n, a, e, _l in rb if a not in starts])
print('E not st_value+st_size of the same symbol:',
      [(n, hex(a), hex(e)) for n, a, e, _l in rb if (a, e) not in ends and n not in ASM0])
print('port_core_refused occurrences:', sum(l.count('port_core_refused') for l in open(B)))
print('literal 0x5f6000 / 6250496 / 781312 (must be 0, image end is YImgTop):',
      sum(1 for l in open(B) if re.search(r'\b(0x5f6000|6250496|781312)\b', l)))
# every A row's byte length vs B row's
dif = [(n, hex(ea - aa), hex(eb - ab)) for (n, aa, ea, _1), (_n2, ab, eb, _2) in zip(ra, rb) if ea - aa != eb - ab]
print('rows whose length differs from the A row:', dif)
# tail rows present and parse
ta = [l.strip() for l in open(A) if l.strip().startswith('Definition tfib_D_') or l.strip().startswith('Definition tfib_at_')]
tb = [l.strip() for l in open(B) if l.strip().startswith('Definition tfib_D_') or l.strip().startswith('Definition tfib_at_')]
print('tail rows A/B:', len(ta), len(tb), 'names equal:',
      [x.split()[1] for x in ta] == [x.split()[1] for x in tb])
# all B tail addresses inside the image
vals = []
for l in tb:
    vals += [int(x, 16) for x in re.findall(r'0x[0-9a-f]+', l)]
print('tail values outside [0x10000, 0x5f6000) other than shadow_off/rw_len:',
      [hex(v) for v in vals if not (0x10000 <= v < 0x5f6000) and v not in (0x7fff8000, 0x55c000)])
print('line count:', sum(1 for _ in open(B)))
