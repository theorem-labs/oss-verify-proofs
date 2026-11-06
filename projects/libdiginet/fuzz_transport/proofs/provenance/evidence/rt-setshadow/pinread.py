#!/usr/bin/env python3
"""pinread.py -- reads words, 8-byte cells and section headers from a stripped (pinned) ELF image, by address only: no
symbol table is needed. Read-only (pyelftools).

usage: pinread.py ELF SHA12 [--words ADDR:LEN,...] [--u64 ADDR,...] [--sections NAME,...]
  ELF         the image; SHA12 must be a prefix of its sha256, else exit 1
  --words     LEN bytes at ADDR (LEN a multiple of 4), printed as little-endian 32-bit words
  --u64       the little-endian 8-byte value at ADDR
  --sections  each section's address, size and flags from the section headers
Every read is of FILE bytes: all of them inside one PT_LOAD's [p_vaddr, p_vaddr + p_filesz), else exit 1.
Output: `# pin ELF SHA256`, then one line per --words item, per --u64 item and per section, in that order."""
import hashlib
import struct
import sys

from elftools.elf.elffile import ELFFile


def opt(argv, name):
    if name not in argv:
        return []
    return argv[argv.index(name) + 1].split(',')


def main(argv):
    if len(argv) < 2:
        raise SystemExit(__doc__)
    path, want = argv[0], argv[1]
    h = hashlib.sha256(open(path, 'rb').read()).hexdigest()
    if not h.startswith(want):
        raise SystemExit('pinread: %s is sha256 %s, not %s' % (path, h, want))
    e = ELFFile(open(path, 'rb'))
    loads = [(s['p_vaddr'], s['p_filesz'], s.data()) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']

    def rd(a, n):
        for v, fz, d in loads:
            if v <= a and a + n <= v + fz:
                return d[a - v:a - v + n]
        raise SystemExit('pinread: %#x+%d is not file bytes of one PT_LOAD' % (a, n))

    print('# pin %s %s' % (path, h))
    for item in opt(argv, '--words'):
        a, n = (int(x, 0) for x in item.split(':'))
        if n % 4:
            raise SystemExit('pinread: --words %s: length not a multiple of 4' % item)
        b = rd(a, n)
        words = ' '.join('%08x' % struct.unpack('<I', b[i:i + 4])[0] for i in range(0, n, 4))
        print('%#x %d bytes words: %s' % (a, n, words))
    for item in opt(argv, '--u64'):
        a = int(item, 0)
        print('%#x u64 = %#x' % (a, struct.unpack('<Q', rd(a, 8))[0]))
    for name in opt(argv, '--sections'):
        s = e.get_section_by_name(name)
        if s is None:
            raise SystemExit('pinread: no section %s' % name)
        print('section %s %#x %#x flags %#x' % (name, s['sh_addr'], s['sh_size'], s['sh_flags']))


if __name__ == '__main__':
    main(sys.argv[1:])
