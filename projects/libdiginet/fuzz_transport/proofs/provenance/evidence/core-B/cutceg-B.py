#!/usr/bin/env python3
"""cutceg-B.py STAGE_OUT OUT.patch: B-ceg-const.patch for libdiginet/fuzz_transport's image-B core.

B/YCeg.v `lib_const_addr` is the program's own measured constant reads (measure-B.py `const reads`, on the pin
41113a03c82f: every load of a program function whose effective address is formed by auipc or gp and lands in a
read-only PT_LOAD, .got reads listed apart). Transport's program [0x812a0, 0x8cc1c) has four, all 8-byte `ld` of
.rodata (sh_addr 0x102e0): LLVMFuzzerTestOneInput pc 0x81ffc -> 0x10310 and pc 0x822ac -> 0x103a8, check_latest_sent
pc 0x84954 -> 0x10338, diginet_session_poll pc 0x8ac78 -> 0x10360. The donor's line holds libreac fuzz_decode's five
ranges, which port_core refuses (per-unit-definition: 10 values); the new line states transport's four. The replaced
line must occur exactly once; a fresh unified diff, -p0 from stage-out, 3 lines of context. No comment line changes."""
import difflib, re, sys

so, out = sys.argv[1:3]
RANGES = [(0x10310, 8), (0x10338, 8), (0x10360, 8), (0x103a8, 8)]
f = 'B/YCeg.v'
txt = open(f'{so}/{f}').read().splitlines(keepends=True)
hits = [i for i, l in enumerate(txt) if l.startswith('Definition lib_const_addr (a : Z) : Prop :=')]
assert len(hits) == 1, hits
new = list(txt)
new[hits[0]] = ('Definition lib_const_addr (a : Z) : Prop := '
                + ' \\/ '.join(f'({a:#x} <= a < {a + w:#x})' for a, w in RANGES) + '.\n')
d = ''.join(difflib.unified_diff(txt, new, f, f, n=3))
assert d, 'no change'
open(out, 'w').write(d)
print(f'{out}: {f} line {hits[0] + 1}: {new[hits[0]].strip()}')
