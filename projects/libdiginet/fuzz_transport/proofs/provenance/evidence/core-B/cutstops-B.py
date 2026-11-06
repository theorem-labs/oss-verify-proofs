#!/usr/bin/env python3
"""cutstops-B.py STAGE_OUT YB12 OUT.patch: B-stops-more.patch for libdiginet/fuzz_transport's image-B core.

B/YB1w.v `tfib_at_stops_more` must list every self-loop site of the image that the unit's own atable lists
(lib/B/YB12.v `stops_more`, atable.py e88affcf0526 on the pin + twin). The run moves the donor's 12 sites; the image's
13th, 0x6effc (_ZN11__sanitizerL23SealedRepairReservationEmm + 0xc0, the same site D6 added on decode: the donor's
released list also lacks it), is added in YB12.v's order (last). The script reads YB12's list, requires the stage-out
list to be a prefix of it with exactly the missing tail, and writes the diff (-p0 from stage-out, 3 lines of context).
No file reads tfib_at_stops_more (checked in the run record)."""
import difflib, re, sys

so, yb12, out = sys.argv[1:4]
want = [int(x, 16) for x in re.search(r'stops_more := \[([^\]]*)\]', open(yb12).read()).group(1).replace(' ', '').split(';')]
f = 'B/YB1w.v'
txt = open(f'{so}/{f}').read().splitlines(keepends=True)
hits = [i for i, l in enumerate(txt) if l.startswith('Definition tfib_at_stops_more : list Z :=')]
assert len(hits) == 1, hits
have = [int(x, 16) for x in re.findall(r'0x[0-9a-f]+', txt[hits[0]])]
assert have == want[:len(have)] and len(want) > len(have), (have, want)
new = list(txt)
new[hits[0]] = 'Definition tfib_at_stops_more : list Z := (' + ' :: '.join(f'{a:#x}' for a in want) + ' :: nil)%list.\n'
open(out, 'w').write(''.join(difflib.unified_diff(txt, new, f, f, n=3)))
print(f'{out}: {f} line {hits[0] + 1}: {len(have)} -> {len(want)} sites, added {[hex(a) for a in want[len(have):]]}')
