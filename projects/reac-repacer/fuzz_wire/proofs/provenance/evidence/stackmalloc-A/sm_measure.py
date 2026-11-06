#!/usr/bin/env python3
"""sm_measure.py DONOR_ELF TARGET_ELF -- the one unchanged shadow-space bound of StackMalloc0.v:254 and AF0s.v:254,
`assert (HSHe : 2148213760 <= SH /\\ ...)`, measured on both images (fuzz_uci's measure-sm1.py rule): the assertion is
proved by lia from SH >= kLowShadowBeg + IMG_TOP / 8 + ..., so it holds on an image exactly when the donor constant
is at most that image's kLowShadowBeg + IMG_TOP / 8 (kLowShadowBeg = 0x7fff7000, lib/Reusable/YG0f.v; IMG_TOP = the
page-rounded end of the last PT_LOAD). Exit 1 if it exceeds either."""
import sys

# elftools from the environment (PYTHONPATH)
from elftools.elf.elffile import ELFFile  # noqa: E402

K_LOW_SHADOW_BEG = 0x7fff7000
DONOR_BOUND = 2148213760
bad = 0
for who, path in (('donor fuzz_grant.asan', sys.argv[1]), ('target fuzz_wire.asan', sys.argv[2])):
    e = ELFFile(open(path, 'rb'))
    end = max(p['p_vaddr'] + p['p_memsz'] for p in e.iter_segments() if p['p_type'] == 'PT_LOAD')
    top = (end + 0xfff) & ~0xfff
    v = K_LOW_SHADOW_BEG + top // 8
    ok = DONOR_BOUND <= v
    bad += not ok
    print('%s: last PT_LOAD end %#x, IMG_TOP %#x, kLowShadowBeg + IMG_TOP / 8 = %d (%#x); the donor bound %d (%#x) %s it: %s'
          % (who, end, top, v, v, DONOR_BOUND, DONOR_BOUND, '<=' if ok else '>', 'holds' if ok else 'FAILS'))
sys.exit(1 if bad else 0)
