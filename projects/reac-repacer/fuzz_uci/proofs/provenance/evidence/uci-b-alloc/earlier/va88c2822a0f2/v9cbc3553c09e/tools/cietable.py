#!/usr/bin/env python3
"""cietable.py -- settle jtcheck's one 'target differs' row, libunwind parseCIE +0x23c, by reading the table. Read-only.

parseCIE loads a table base at +0x238/+0x23c (auipc + addi into s6) and dispatches on it later. jtcheck's bound() takes
the first `addi rK, zero, K` + bltu/bgeu in the 10 words BEFORE the auipc as the entry count; here it finds an unrelated
check (K = 255), so table() must read 255 jump entries, stops at the end of the real table and falls back to an 8-byte
compare. This script prints the words that bound the real dispatch (after the auipc) and the dispatch itself, then reads
every 4-byte table entry (target = base + int32 entry) while it points into the function, in each image, and compares
the entries as function-relative offsets.
usage: cietable.py X_ELF Y_ELF [Y2_ELF ...]"""
import sys, os, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('drvcmp', os.path.join(HERE, 'drvcmp.py'))
dc = importlib.util.module_from_spec(spec); spec.loader.exec_module(dc)
sx = dc._g['sx']
src = open(os.path.join(HERE, 'jtcheck.py')).read()
ns = {'sx': sx}; exec(src[src.index('def bound('):src.index('def memcpy_len(')], ns); bound = ns['bound']
FN = '_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE8parseCIEERS1_mPNS2_8CIE_InfoE'
ref = None
for p in sys.argv[1:]:
    I = dc.Img(p); fa, z = I.fsym(FN); w = dc.bc_words(I.rd(fa, z))
    at = {o: (i, x) for i, (o, x, n) in enumerate(w)}
    k, hx = at[0x238]; _, lx = at[0x23c]
    assert hx & 0x7f == 0x17 and (lx & 0x7f) == 0x13 and (lx >> 15) & 31 == (hx >> 7) & 31
    tb = fa + 0x238 + sx(hx >> 12, 20) * 4096 + sx(lx >> 20, 12)
    offs = []
    while True:
        v = tb + int.from_bytes(I.rd(tb + 4 * len(offs), 4), 'little', signed=True)
        if not (fa <= v < fa + z): break
        offs.append(v - fa)
    print('# %s sha256 %s: parseCIE %#x size %d; table base %#x (rd x%d of +0x23c); jtcheck bound() -> %s; '
          'entries pointing into parseCIE: %d' % (p, dc.sha(p)[:12], fa, z, tb, (lx >> 7) & 31, bound(w, k), len(offs)))
    if ref is None:
        ref = offs
        for o in (0x234, 0x250, 0x254, 0x258, 0x25c, 0x260, 0x264, 0x268, 0x26c):
            print('   +%#x %08x' % (o, at[o][1]))
        print('   offsets', ' '.join('%#x' % o for o in offs))
    else:
        print('   entries equal to X as function-relative offsets: %s (%d vs %d entries)' % (offs == ref, len(offs), len(ref)))
