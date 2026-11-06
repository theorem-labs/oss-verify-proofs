#!/usr/bin/env python3
"""icpt-memmove.py YE34 [UNSTRIPPED_TWIN]: fuzz_wire's own code calls __asan_memmove (the CALLED-RUNTIME inventory: 1
call in image B), which fuzz_grant, the donor, does not, so the relocated icpt_ranges of lib/B/YE34.v has no range for it
and a walk through it stops at its first fetch. This post-step adds the one range
    (0x510b0, 220%nat)      __asan_memmove of fuzz_wire.asan-ubsan: 880 bytes = 220 words
after the range that ends where it starts, (0x50c0c, 297%nat) (0x50c0c + 4 * 297 = 0x510b0). It writes no comment
(stream-lead rule 1j-octies / -novies: no lane writes a notice line into a copied file); this record carries the reason. tbl_icpt is built from the image's own words for every range (build_ranges_ok holds for any
range with lo >= 0), so a range adds coverage and no assumption. With UNSTRIPPED_TWIN the symbol's address and size are
checked against the image's symtab first. Exit 1 unless each anchor occurs exactly once."""
import sys

p = sys.argv[1]
LO, WORDS = 0x510b0, 220
if len(sys.argv) > 2:
    from elftools.elf.elffile import ELFFile
    syms = {s.name: (s['st_value'], s['st_size']) for s in ELFFile(open(sys.argv[2], 'rb')).get_section_by_name('.symtab').iter_symbols()}
    if syms.get('__asan_memmove') != (LO, 4 * WORDS):
        sys.exit(f'__asan_memmove is {syms.get("__asan_memmove")}, expected ({LO:#x}, {4 * WORDS})')
t = open(p).read()
ANCH = '(0x50c0c, 297%nat); (0x51420, 568%nat);'
NEW = '(0x50c0c, 297%nat); (0x510b0, 220%nat); (0x51420, 568%nat);'
if t.count(ANCH) != 1:
    sys.exit(f'{p}: icpt anchor occurs {t.count(ANCH)} times')
t = t.replace(ANCH, NEW)
open(p, 'w').write(t)
print(f'{p}: __asan_memmove range (0x510b0, 220) added')
