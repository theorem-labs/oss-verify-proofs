#!/usr/bin/env python3
"""pinback.py -- the stripped pin a symtwin.py twin was made from, rebuilt from the twin, for `drvcmp.py twins`.

symtwin.py copies the pinned ELF byte for byte, appends .strtab, .symtab, a new .shstrtab and a new section header table,
and changes only e_shoff and e_shnum in the ELF header. So the pin is the twin's first N bytes (N = the file offset of
the appended .strtab, the last section header) with e_shoff set to N - 64 * (e_shnum - 2) and e_shnum to e_shnum - 2.
Checks that this old header table is the twin's table less its last two entries (the .shstrtab entry excepted, which
symtwin.py re-points), writes OUT and prints its sha256; the caller compares it with the pin of record.
Usage: pinback.py TWIN OUT"""
import hashlib, struct, sys

tw = open(sys.argv[1], 'rb').read()
shoff, = struct.unpack_from('<Q', tw, 0x28)
shentsize, shnum, shstrndx = struct.unpack_from('<HHH', tw, 0x3a)
assert shentsize == 64
sh = [struct.unpack_from('<IIQQQQIIQQ', tw, shoff + 64 * i) for i in range(shnum)]
assert sh[-2][1] == 2 and sh[-1][1] == 3, 'the last two sections are not the appended .symtab / .strtab'
n = sh[-1][4]
old_off, old_num = n - 64 * (shnum - 2), shnum - 2
old = [struct.unpack_from('<IIQQQQIIQQ', tw, old_off + 64 * i) for i in range(old_num)]
assert all(old[i] == sh[i] for i in range(old_num) if i != shstrndx), 'old section header table does not match'
pin = bytearray(tw[:n])
struct.pack_into('<Q', pin, 0x28, old_off)
struct.pack_into('<H', pin, 0x3c, old_num)
open(sys.argv[2], 'wb').write(pin)
print('pinback: %s sha256 %s -> %s (%d bytes, e_shoff %d, e_shnum %d) sha256 %s'
      % (sys.argv[1], hashlib.sha256(tw).hexdigest(), sys.argv[2], n, old_off, old_num, hashlib.sha256(pin).hexdigest()))
