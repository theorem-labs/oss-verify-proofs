#!/usr/bin/env python3
"""cutarm-B.py STAGE_OUT OUT.patch: B-yd1g-arm.patch for libdiginet/fuzz_transport's image-B core.

The release lead 21:05Z (form (a), the only form): B/YD1g.v's tfib_layout_ok proof carries the donor's alternation
`apply Z_mod_mult || (change <N> with (<K> * 4096); apply Z_mod_mult)`. It is dead text: `repeat split; try lia; try
reflexivity` before it closes every goal it could reach, so the arm never runs; it is deleted, leaving
`apply Z_mod_mult`, even where <K> is right (here port_core wrote 6316032 = 1542 * 4096, which is right). The whole-unit
build is the check. Exactly one line must hold the arm; a fresh unified diff, -p0 from stage-out, 3 lines of context."""
import difflib, re, sys

so, out = sys.argv[1:3]
f = 'B/YD1g.v'
ARM = re.compile(r' \|\| \(change \d+ with \(\d+ \* 4096\); apply Z_mod_mult\)')
txt = open(f'{so}/{f}').read().splitlines(keepends=True)
hits = [i for i, l in enumerate(txt) if ARM.search(l)]
assert len(hits) == 1, hits
new = list(txt)
new[hits[0]] = ARM.sub('', txt[hits[0]], count=1)
assert 'apply Z_mod_mult' in new[hits[0]] and not ARM.search(new[hits[0]])
open(out, 'w').write(''.join(difflib.unified_diff(txt, new, f, f, n=3)))
print(f'{out}: {f} line {hits[0] + 1}: removed {ARM.search(txt[hits[0]]).group(0).strip()!r}')
