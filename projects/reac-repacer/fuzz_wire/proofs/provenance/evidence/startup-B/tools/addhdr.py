#!/usr/bin/env python3
"""addhdr.py IN.v OUT.v 'MODIFIED TEXT' [--read-from] -- inserts an undated `(* Modified by Theorem Labs: TEXT *)` (and,
with --read-from, pins.py's provenance line `(* Read from: fuzz_wire.asan-ubsan (reac-repacer/fuzz_wire asan-ubsan)
sha256 ...; unstripped twin sha256 ... *)`) after the donor's release header lines, for a generator that copies the
donor header unchanged (boxb1.py's YB1v / YB1m). It changes nothing else; it asserts the donor header has the
Copyright / SPDX / Modified lines gen_ab1hk.header expects."""
import sys

src, dst, text = sys.argv[1:4]
lines = open(src).read().split('\n')
assert lines[0].startswith('(* Copyright') and lines[1].startswith('(* SPDX') and lines[2].startswith('(* Modified by')
k = 3
while lines[k].startswith('(* Modified by'):
    k += 1
new = ['(* Modified by Theorem Labs: %s *)' % text]
if '--read-from' in sys.argv[4:]:
    new.append('(* Read from: fuzz_wire.asan-ubsan (reac-repacer/fuzz_wire asan-ubsan) sha256 '
               'af4534831a4528320c7dc74ca3f64bb96e8232ed2e313f01126d10879f3417d6; unstripped twin sha256 '
               '51eb4bef24252e4df6e11baa89f653d20d74e38ae684f61bc94f4fb339ac97c3 *)')
open(dst, 'w').write('\n'.join(lines[:k] + new + lines[k:]))
