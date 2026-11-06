"""Port the tail of AB1w.v (tfib_D_* data cells, tfib_at_* anchors) to asan-ubsan.

Every address is placed in the asan image (symbol + offset, or GOT word target),
then the same place is looked up in asan-ubsan."""
import json
import os
import re
import struct
import sys

sys.path.insert(0, os.environ.get('REVCHECK_DIR') or sys.exit('set REVCHECK_DIR to the directory holding revcheck.py (NOTES.md, Commands)'))
sys.path.insert(0, os.environ.get('ELFDIS_DIR') or sys.exit('set ELFDIS_DIR to the directory holding elfdis.py (NOTES.md, Commands)'))
import elfdis  # noqa: E402
import revcheck as rc  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
W = HERE + '/'
SRC = os.path.join(HERE, '../../../../lib/A/AB1w.v')
ROOT = os.environ.get('PIPELINE_ROOT') or sys.exit('set PIPELINE_ROOT to the pipeline libreac root (it holds bin/ and unstripped/)')
PA = ROOT + '/unstripped/fuzz_boxreg/fuzz_boxreg.asan'
PB = ROOT + '/unstripped/fuzz_boxreg/fuzz_boxreg.asan-ubsan'
EA, EB = rc.Elf(PA), rc.Elf(PB)
IA, IB = elfdis.load(PA), elfdis.load(PB)
S = json.load(open(W + 'syms.json'))
GOT = {'asan': (0x98e58, 0x99bb0), 'ubsan': (0x99278, 0x99fd0)}


def syms(k, types=(1, 2)):
    return [(v, z, n, t) for n, t, v, z in S[k]['syms'] if t in types and n]


def place(k, addr):
    """(name, offset, kind) of the symbol covering addr; prefers the smallest."""
    c = [(z, v, n, t) for v, z, n, t in syms(k) if v <= addr < v + max(z, 1)]
    c.sort()
    return [(n, addr - v, t, v, z) for z, v, n, t in c]


def lookup(k, name, off):
    c = sorted({(v, z, t) for v, z, n, t in syms(k) if n == name})
    return [(v + off, v, z, t) for v, z, t in c]


def word(E, a):
    return struct.unpack('<Q', E.read(a, 8))[0]


rows = []
for line in open(SRC):
    m = re.match(r'Definition (tfib_(?:D|at)_\w+) : (?:Z|nat|list Z) := (.*)\.$', line.strip())
    if m:
        rows.append((m.group(1), m.group(2)))

print('# tail rows', len(rows))
for name, val in rows:
    print('==', name, '=', val)
    for a in [int(x, 16) for x in re.findall(r'0x[0-9a-f]+', val)]:
        pl = place('asan', a)
        if pl:
            n, off, t, v, z = pl[0]
            tw = [hex(x[0]) for x in lookup('ubsan', n, off)]
            print('    %#x -> %s+%#x (sym %#x+%#x, type %d) => ubsan %s' % (a, n, off, v, z, t, tw))
        elif GOT['asan'][0] <= a < GOT['asan'][1]:
            w = word(EA, a)
            pw = place('asan', w)
            print('    %#x GOT slot, word %#x (%s)' % (a, w, pw[0][:2] if pw else '?'))
        else:
            print('    %#x UNPLACED (sections: %s)' % (a, [s for s, vv in EA.secs.items() if any(x[0] <= a < x[0] + x[1] for x in vv)]))
