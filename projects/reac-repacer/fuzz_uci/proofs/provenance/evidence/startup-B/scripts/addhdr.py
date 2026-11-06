#!/usr/bin/env python3
"""addhdr.py IN.v OUT.v 'MODIFIED TEXT' [--read-from] -- inserts `(* Modified by Theorem Labs: TEXT *)` (and, with
--read-from, the `(* Read from: fuzz_uci.asan-ubsan ... sha256 ...; unstripped twin sha256 ... *)` pin line) after the
donor's release header lines, for a generator that copies the donor header unchanged (boxb1.py's YB1v / YB1m). It
changes nothing else; it asserts the donor header has the Copyright / SPDX / Modified lines gen_ab1hk.header expects."""
import sys

src, dst, text = sys.argv[1:4]
lines = open(src).read().split('\n')
assert lines[0].startswith('(* Copyright') and lines[1].startswith('(* SPDX') and lines[2].startswith('(* Modified by')
k = 3
while lines[k].startswith('(* Modified by'):
    k += 1
new = ['(* Modified by Theorem Labs: %s *)' % text]
if '--read-from' in sys.argv[4:]:
    new.append('(* Read from: fuzz_uci.asan-ubsan (the reac-repacer/fuzz_uci asan-ubsan pin) sha256 '
               'a1b86e424adde6f65d345459822690a6c21e9e606446b91b4ad25e9f3ef6e7fc; unstripped twin sha256 '
               '8d07ffcf594874884207465cc34ff9f3b1062f21f6d9b3622e0771fa76490b16 *)')
open(dst, 'w').write('\n'.join(lines[:k] + new + lines[k:]))
