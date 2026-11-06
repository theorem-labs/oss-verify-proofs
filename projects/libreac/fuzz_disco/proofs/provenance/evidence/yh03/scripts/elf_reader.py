#!/usr/bin/env python3
"""elf_reader.py: small ELF64-LE reader for the YH03 checks (a neutral-named copy of the fix's reader; code unchanged).
  elf_reader.py loads PIN TWIN          compare every PT_LOAD's file bytes (and vaddr / memsz / flags) of PIN and TWIN
  elf_reader.py syms TWIN NAME...       symbol value / size / type / section for each NAME (all matches)
  elf_reader.py at TWIN ADDR N          the N bytes at virtual ADDR (hex), with the section and the symbol covering it
  elf_reader.py sect TWIN               section headers
No external dependencies."""
import struct
import sys


class Elf:
    def __init__(self, path):
        self.d = d = open(path, 'rb').read()
        assert d[:4] == b'\x7fELF' and d[4] == 2 and d[5] == 1, path
        phoff, shoff = struct.unpack_from('<QQ', d, 0x20)
        phentsize, phnum, shentsize, shnum, shstrndx = struct.unpack_from('<HHHHH', d, 0x36)
        self.ph = [struct.unpack_from('<IIQQQQQQ', d, phoff + i * phentsize) for i in range(phnum)]
        self.sh = [struct.unpack_from('<IIQQQQIIQQ', d, shoff + i * shentsize) for i in range(shnum)] if shoff else []
        names = self.sh[shstrndx][4] if self.sh else 0
        self.shn = [self.cstr(names + s[0]) for s in self.sh] if self.sh else []
        self.syms = []
        for s, n in zip(self.sh, self.shn):
            if n == '.symtab':
                strt = self.sh[s[6]][4]
                for i in range(s[5] // 24):
                    st_name, st_info, _, shndx, val, size = struct.unpack_from('<IBBHQQ', d, s[4] + i * 24)
                    self.syms.append((self.cstr(strt + st_name), val, size, st_info & 15, st_info >> 4, shndx))

    def cstr(self, off):
        return self.d[off:self.d.index(b'\0', off)].decode(errors='replace')

    def loads(self):
        return [p for p in self.ph if p[0] == 1]

    def read(self, addr, n):
        for p in self.loads():
            _, flags, off, vaddr, _, filesz, memsz, _ = p
            if vaddr <= addr and addr + n <= vaddr + memsz:
                out = bytearray()
                for a in range(addr, addr + n):
                    out.append(self.d[off + a - vaddr] if a - vaddr < filesz else 0)
                return bytes(out)
        return None

    def section_of(self, addr):
        for s, n in zip(self.sh, self.shn):
            if s[2] & 2 and s[3] <= addr < s[3] + s[5]:
                return '%s [%#x, %#x)' % (n, s[3], s[3] + s[5])
        return '-'

    def sym_at(self, addr):
        best = [s for s in self.syms if s[1] <= addr < s[1] + max(s[2], 1) and s[3] in (1, 2)]
        return ', '.join('%s@%#x+%d' % (s[0], s[1], s[2]) for s in best) or '-'


def main():
    cmd = sys.argv[1]
    if cmd == 'loads':
        a, b = Elf(sys.argv[2]), Elf(sys.argv[3])
        la, lb = a.loads(), b.loads()
        print('PT_LOAD count pin %d twin %d' % (len(la), len(lb)))
        for i, (p, q) in enumerate(zip(la, lb), 1):
            hp = (p[3], p[5], p[6], p[1])
            hq = (q[3], q[5], q[6], q[1])
            bp = a.d[p[2]:p[2] + p[5]]
            bq = b.d[q[2]:q[2] + q[5]]
            print('PT_LOAD %d vaddr %#x filesz %#x memsz %#x flags %d: headers %s, bytes %s' % (
                i, p[3], p[5], p[6], p[1], 'EQUAL' if hp == hq else 'DIFFER %r' % (hq,),
                'EQUAL' if bp == bq else 'DIFFER'))
    elif cmd == 'syms':
        e = Elf(sys.argv[2])
        for n in sys.argv[3:]:
            hits = [s for s in e.syms if s[0] == n]
            print(n, ' | '.join('val %#x size %d type %d bind %d shndx %d sect %s' % (
                s[1], s[2], s[3], s[4], s[5], e.section_of(s[1])) for s in hits) or 'ABSENT')
    elif cmd == 'at':
        e = Elf(sys.argv[2])
        addr, n = int(sys.argv[3], 16), int(sys.argv[4])
        b = e.read(addr, n)
        print('%#x %s: %s | sect %s | sym %s' % (addr, n, b.hex() if b is not None else 'NOT MAPPED',
                                                 e.section_of(addr), e.sym_at(addr)))
    elif cmd == 'sect':
        e = Elf(sys.argv[2])
        for s, n in zip(e.sh, e.shn):
            if s[2] & 2:
                print('%-20s %#x %#x' % (n, s[3], s[3] + s[5]))


main()
