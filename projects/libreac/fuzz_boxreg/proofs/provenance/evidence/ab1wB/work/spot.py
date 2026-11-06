"""Spot checks: size-0 asm rows, the `dummy`-alias rows, MemToShadow neighbours."""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
W = HERE + '/'
S = json.load(open(W + 'syms.json'))
R = json.load(open(W + 'resolved.json'))['res']
FA = sorted({(v, z, n) for n, t, v, z in S['asan']['syms'] if t == 2 and n})
FB = sorted({(v, z, n) for n, t, v, z in S['ubsan']['syms'] if t == 2 and n})


def near(F, addr):
    pre = [x for x in F if x[0] < addr]
    nxt = [x for x in F if x[0] > addr]
    at = [n for v, z, n in F if v == addr]
    return (pre[-1] if pre else None), at, (nxt[0] if nxt else None)


by = {r['row']: r for r in R}
for nm in ('start', 'set_thread_area', 'init', 'fini', 'testcancel',
           'aio_close_stub_j_ret_used_by_close_stdio_close', 'call',
           'MemToShadow_3c6cc', 'MemToShadow_CHECK_AddrIsInMem_instance',
           'MemToShadow_checked', 'MemToShadow_checked_instance_3'):
    r = by.get(nm)
    if not r:
        print(nm, 'MISSING')
        continue
    print('%-46s A %#x..%#x (%d insn) -> B %#x..%#x (%d insn) %s %s' %
          (nm, r['a'], r['e'], (r['e'] - r['a']) // 4, r['b'], r['be'], (r['be'] - r['b']) // 4, r['verdict'], r['how']))
    pa, aa, na = near(FA, r['a'])
    pb, ab, nb = near(FB, r['b'])
    f = lambda x: 'none' if x is None else '%s @%#x' % (x[2], x[0])
    print('      A: prev %s | at %s | next %s' % (f(pa), aa, f(na)))
    print('      B: prev %s | at %s | next %s' % (f(pb), ab, f(nb)))
