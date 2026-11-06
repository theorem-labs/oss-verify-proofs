#!/usr/bin/env python3
"""ae34_memmove.py AE34 TWIN -- the one recorded patch row of the WIRE-MEMMOVE row in lib/A/AE34.v: icpt_ranges gains
`(0x51310, 220%nat)` right after `(0x50c2c, 441%nat)`, so the code table holds __asan_memmove (the relocated walk of
lib/A/Rt/Memmove*.v reads its code from tbl_icpt).
GATE (measured on the unstripped twin, sha256 d2f662a22962): __asan_memmove is a function at 0x51310 of 880 bytes =
220 words; the range before it ends there (0x50c2c + 441 * 4 = 0x51310) and the next one starts at its end (0x51680);
the row is not present yet. Refuses otherwise; prints the symtab line and the changed line."""
import hashlib, re, sys
from elftools.elf.elffile import ELFFile

ae34, twin = sys.argv[1:3]
if hashlib.sha256(open(twin, 'rb').read()).hexdigest() != 'd2f662a229626fd402f1018631498190e800834bad837fa4027204b79088b128':
    sys.exit('ae34_memmove: twin pin mismatch')
st = ELFFile(open(twin, 'rb')).get_section_by_name('.symtab')
mm = [(s['st_value'], s['st_size']) for s in st.iter_symbols() if s.name == '__asan_memmove' and s['st_info']['type'] == 'STT_FUNC']
if mm != [(0x51310, 880)]:
    sys.exit('ae34_memmove: __asan_memmove is %s in the twin' % mm)
print('ae34_memmove: twin symtab __asan_memmove 0x51310 880 (= 220 words)')
t = open(ae34).read()
if '(0x51310, 220%nat)' in t:
    sys.exit('ae34_memmove: the row is already there')
if 0x50c2c + 441 * 4 != 0x51310 or '(0x51680, ' not in t:
    sys.exit('ae34_memmove: the neighbouring ranges are not (0x50c2c, 441) .. (0x51680, _)')
old = '(0x50c2c, 441%nat);'
if t.count(old) != 1:
    sys.exit('ae34_memmove: `%s` occurs %d times' % (old, t.count(old)))
t2 = t.replace(old, old + ' (0x51310, 220%nat);')
open(ae34, 'w').write(t2)
ln = t2[:t2.index('(0x51310, 220%nat)')].count('\n') + 1
print('ae34_memmove: A/AE34.v:%d: %s' % (ln, t2.split('\n')[ln - 1].strip()[:200]))
