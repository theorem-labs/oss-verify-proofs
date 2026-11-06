"""Check every interior (non-function-start) tail address: same instruction index,
same mnemonic+registers in both images. Also read the shadow offset out of the code."""
import json
import os
import sys

sys.path.insert(0, os.environ.get('REVCHECK_DIR') or sys.exit('set REVCHECK_DIR to the directory holding revcheck.py (NOTES.md, Commands)'))
sys.path.insert(0, os.environ.get('ELFDIS_DIR') or sys.exit('set ELFDIS_DIR to the directory holding elfdis.py (NOTES.md, Commands)'))
import elfdis  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
W = HERE + '/'
ROOT = os.environ.get('PIPELINE_ROOT') or sys.exit('set PIPELINE_ROOT to the pipeline libreac root (it holds bin/ and unstripped/)')
PA = ROOT + '/unstripped/fuzz_boxreg/fuzz_boxreg.asan'
PB = ROOT + '/unstripped/fuzz_boxreg/fuzz_boxreg.asan-ubsan'
IA, IB = elfdis.load(PA), elfdis.load(PB)
S = json.load(open(W + 'syms.json'))
FA = sorted({(v, z, n) for n, t, v, z in S['asan']['syms'] if t == 2 and n and z})
FB = sorted({(v, z, n) for n, t, v, z in S['ubsan']['syms'] if t == 2 and n and z})

CASES = [('x_popfree', 0x36344), ('x_envscan', 0x87f88), ('x_envscan_k', 0x87f94),
         ('x_pnscan', 0x8804c), ('x_pnscan_k', 0x88058)] + \
        [('stops_more[%d]' % i, a) for i, a in enumerate(
            [0x33fb8, 0x355dc, 0x53730, 0x59ae8, 0x59afc, 0x59b10, 0x5f4a0, 0x5f570, 0x6ca9c, 0x6d9a8, 0x6db38, 0x77890])]


def encl(F, a):
    c = sorted((z, v, n) for v, z, n in F if v <= a < v + z)
    return c[0][1], c[0][0], c[0][2]


for nm, a in CASES:
    va, za, n = encl(FA, a)
    cand = sorted({(v, z) for v, z, nn in FB if nn == n})
    assert len(cand) == 1, (nm, n, cand)
    vb, zb = cand[0]
    off = a - va
    xa = elfdis.disasm(IA, va, za)
    xb = elfdis.disasm(IB, vb, zb)
    ia = [i for i, x in enumerate(xa) if x[0] == a][0]
    b = vb + off
    ib = [i for i, x in enumerate(xb) if x[0] == b]
    same = bool(ib) and ia == ib[0] and xa[ia][1] == xb[ib[0]][1]
    print('%-16s %#x = %s+%#x (insn %d/%d) -> %#x insn %s  %-8s | %-8s  %s' %
          (nm, a, n[:46], off, ia, len(xa), b, ib[0] if ib else '-', xa[ia][1], xb[ib[0]][1] if ib else '-',
           'OK' if same else 'MISMATCH'))

# shadow offset: the literal MemToShadow adds
for tag, I, v, z in [('asan', IA, 0x3c6cc, 0x13c), ('ubsan', IB, 0x3c72c, 0x13c)]:
    ins = elfdis.disasm(I, v, z)
    print(tag, 'MemToShadow literals:', sorted({o for _a, m, o in ins if m in ('lui', 'addi', 'addiw') and '0x' in o})[:8])
