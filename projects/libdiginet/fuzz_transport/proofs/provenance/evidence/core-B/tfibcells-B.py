#!/usr/bin/env python3
"""tfibcells-B.py PIN ROOT [ROOT ...]: the tfib_*_lo / tfib_*_hi section cells of libdiginet/fuzz_transport's image-B
lib against the pin's section headers (the release lead 20:58Z / 21:04Z / 21:06Z).

ENUMERATED: every `Definition tfib_<n>_(lo|hi) : Z := <numeral>.` in a .v under each ROOT (by name, word boundary).
A cell names section `.` + <n> with '_' -> '.' (data_rel_ro -> .data.rel.ro, init_array -> .init_array, preinit_array ->
.preinit_array, rodata -> .rodata, ...); the plain `.`+<n> spelling is tried too. CHECKED: the section exists in the
pin: lo must equal sh_addr, hi must equal sh_addr + sh_size. SYNTHETIC: no section of that name (listed by name).
FALSE: a checked cell whose value differs. Valid only if ENUMERATED = CHECKED + SYNTHETIC.
Control: run it on the donor lib against the donor pin (its known defect tfib_rodata_hi must show FALSE)."""
import os, re, sys
from elftools.elf.elffile import ELFFile

pin, roots = sys.argv[1], sys.argv[2:]
secs = {s.name: (s['sh_addr'], s['sh_size']) for s in ELFFile(open(pin, 'rb')).iter_sections() if s.name}
DEF = re.compile(r'\bDefinition\s+(tfib_(\w+?)_(lo|hi))\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+|\d+)\s*\.')
enum, chk, syn, false = [], [], [], []
for root in roots:
    for dp, _, fs in os.walk(root):
        for fn in sorted(fs):
            if not fn.endswith('.v'):
                continue
            p = os.path.join(dp, fn)
            for ln, line in enumerate(open(p, errors='replace'), 1):
                for m in DEF.finditer(line):
                    full, n, side, val = m.group(1), m.group(2), m.group(3), int(m.group(4), 0)
                    rel = os.path.relpath(p, root)
                    enum.append((rel, ln, full))
                    cands = ['.' + n.replace('_', '.'), '.' + n, n]   # n: a dotless section such as asan_globals
                    sec = next((c for c in cands if c in secs), None)
                    if sec is None:
                        syn.append((rel, ln, full, val))
                        continue
                    a, z = secs[sec]
                    want = a if side == 'lo' else a + z
                    chk.append((rel, ln, full, val, sec, want))
                    if val != want:
                        false.append((rel, ln, full, val, sec, want))
print(f'pin {pin}')
print(f'ENUMERATED {len(enum)}  CHECKED {len(chk)}  SYNTHETIC {len(syn)}  FALSE {len(false)}  '
      f'valid={len(enum) == len(chk) + len(syn)}')
for r in chk:
    print('  CHECKED  %s:%d %s = %#x; %s %s = %#x%s' % (r[0], r[1], r[2], r[3], r[4], 'lo' if r[2].endswith('_lo') else 'hi',
                                                     r[5], '' if r[3] == r[5] else '  FALSE'))
for r in syn:
    print('  SYNTHETIC %s:%d %s = %#x (no section of that name)' % r)
