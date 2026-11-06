#!/usr/bin/env python3
"""tr0.py -- the start-up depot trace TFIB_TR0 (the donor's A/AF0m.v:288) of an image, and its depot hashes.

  tr0.py IMAGE --symbols SYMBOLS.tsv

The trace is [ipc_rg; ra]: ipc_rg = the return address of the GetCurrentPc call (`mv a0,ra; ret`) in
__asan_register_globals (its StackTrace for the globals' registration site), ra = the return address of the call to
__asan_register_globals in __asan_register_elf_globals (whose s0 holds a0 = the address of a global flag, so the walk ends,
the trace kit's notes, section "Runtime depot users"). TFIB_TR0 0 = [ipc_rg; ra], TFIB_TR0 _ = [ipc_rg]; TFIB_HASH h = the depot murmur hash of
TFIB_TR0 h (dphash.py, the relink kit's tool, which reproduces the donor's two values).

A new version of tr0.py 14f49a0b2243: the names come from the shared symbol extract (--symbols, through symbols.nm_lines,
which gives the names file the earlier version read through the vendored names.py, byte for byte), read by the same rule
(trace-image/rvdis.py syms: one name per `ADDR SIZE T NAME` line). Everything else is unchanged.
"""
import argparse, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'trace-image'))
from base import Image, tgt


def main():
    ap = argparse.ArgumentParser(); ap.add_argument('img'); ap.add_argument('--symbols', required=True)
    a = ap.parse_args()
    sys.path.insert(0, HERE)
    import symbols
    d = {}
    for line in symbols.nm_lines(a.symbols):    # rvdis.syms's rule
        p = line.split()
        if len(p) == 3 and p[1] in 'tTwW':
            d.setdefault(int(p[0], 16), []).append(p[2])
        elif len(p) >= 4 and p[2] in 'tTwW':
            d.setdefault(int(p[0], 16), []).append(p[3])
    byname = {}
    for addr, ns in d.items():
        for n in ns:
            byname.setdefault(n, addr)
    I = Image(a.img)
    rg = byname['__asan_register_globals']; eg = byname['__asan_register_elf_globals']
    body = I.body(rg)
    gc = [x for x in body if x.mnemonic in ('jal', 'c.jal') and tgt(x) in I.gcp]
    # long branch: `li a1, 2; bltu a1, a0, X` after GetMallocContextSize (depth > 2); ipc = after the first GetCurrentPc
    # call at or after X (the trace kit's compose.py find_ipc)
    import absint
    lb = [x for x in body if x.mnemonic == 'bltu' and x.op_str.startswith('a1, a0,')]
    xl = absint.tgt_branch(lb[0])
    gcl = [x for x in gc if x.address >= xl]
    ipc = gcl[0].address + gcl[0].size
    ras = [ra for (o, ra) in I.calls.get(rg, []) if o == eg]
    assert len(gc) >= 1 and len(ras) == 1, (gc, ras)
    sys.path.insert(0, HERE)
    import dphash
    tr = [[ipc, ras[0]], [ipc]]
    hs = [dphash.hash_trace(t) for t in tr]
    print('register_globals %#x (GetCurrentPc calls %s), register_elf_globals %#x' % (rg, [hex(x.address) for x in gc], eg))
    print('TFIB_TR0 0 = [%s]; TFIB_TR0 _ = [%s]' % ('; '.join(hex(x) for x in tr[0]), hex(tr[1][0])))
    print('TFIB_HASH 0 = %d; TFIB_HASH _ = %d' % tuple(hs))
    print('buckets (mod d_tab_words = %d): %d / %d' % (dphash.D_TAB_WORDS, hs[0] % dphash.D_TAB_WORDS, hs[1] % dphash.D_TAB_WORDS))


if __name__ == '__main__':
    main()
