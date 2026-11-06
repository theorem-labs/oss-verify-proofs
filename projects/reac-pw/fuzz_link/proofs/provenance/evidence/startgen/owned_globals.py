#!/usr/bin/env python3
"""owned_globals.py AF0m.v ELF OUT.v -- gen_ad2's --owned INPUT for reac-pw/fuzz_link image A: AF0m.v with the BODIES of
the asan_globals descriptors whose beg lies in .bss appended to Tfib_owned_static as (beg, size) rows (redzones are
already rows of AF0m). The pcap lane's --globals-bss prep (its AD2j.v header), the harness-globals hull of A/AD1y.v.
Not a committed proof file: a recorded generator input (DEVIATION: not in the start-up set)."""
import re, struct, sys
from elftools.elf.elffile import ELFFile

af0m, elf, out = sys.argv[1:4]
e = ELFFile(open(elf, 'rb'))
g, bss = e.get_section_by_name('asan_globals'), e.get_section_by_name('.bss')
raw, lo, hi = g.data(), bss['sh_addr'], bss['sh_addr'] + bss['sh_size']
bodies = [(b, s) for b, s in (struct.unpack_from('<2Q', raw, 64 * i) for i in range(len(raw) // 64)) if lo <= b < hi]
txt = open(af0m).read()
m = re.search(r'(Definition Tfib_owned_static : list \(Z \* Z\) :=\n\[.*?)(\n\]\.)', txt, re.S)
assert m and not any('(0x%x, %d)' % bd in m.group(1) for bd in bodies), 'no owned list, or a body already owned'
add = ''.join(' ;\n(0x%x, %d)' % bd for bd in bodies)
open(out, 'w').write(txt[:m.end(1)] + add + txt[m.end(1):])
print('owned_globals: %d .bss descriptor bodies appended: %s' % (len(bodies), ', '.join('(0x%x, %d)' % bd for bd in bodies)))
