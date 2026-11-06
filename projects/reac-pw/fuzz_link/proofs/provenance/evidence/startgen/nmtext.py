#!/usr/bin/env python3
"""nmtext.py ELF > names.txt -- an `nm -S` listing (ADDR [SIZE] TYPE NAME, mangled names) of an ELF's .symtab, read with
pyelftools, for the tools that take nm text (pautrlen's PT_NAMES). This box has no binutils / llvm nm.
Type letters as GNU nm: U undefined (skipped), A absolute, W/w weak (V/v weak object), B/b .bss / .tbss / .sbss,
D/d writable data, R/r read-only data, T/t executable code, N other; upper case = global, lower = local.
Section, file and mapping ($x / $d) symbols are skipped. The control is --compare REAL_NM.txt (a real `nm -S
--size-sort` listing of the same ELF, sized rows only): every real row (address, size, type, name) must be a row here,
and every sized row here must be a real row.
"""
import sys
from elftools.elf.elffile import ELFFile


def rows(path):
    e = ELFFile(open(path, 'rb'))
    secs = list(e.iter_sections())
    out = []
    for s in e.get_section_by_name('.symtab').iter_symbols():
        t, b, ndx = s['st_info']['type'], s['st_info']['bind'], s['st_shndx']
        if not s.name or s.name.startswith('$') or t in ('STT_SECTION', 'STT_FILE') or ndx == 'SHN_UNDEF':
            continue
        if ndx == 'SHN_ABS':
            c = 'a'
        else:
            sec = secs[ndx]
            fl, nm = sec['sh_flags'], sec.name
            if sec['sh_type'] == 'SHT_NOBITS':
                c = 'b'
            elif fl & 4:
                c = 't'
            elif fl & 2 and fl & 1:
                c = 'd'
            elif fl & 2:
                c = 'r'
            else:
                c = 'n'
        if b == 'STB_WEAK':
            c = 'v' if t == 'STT_OBJECT' else 'w'
            c = c.upper() if ndx != 'SHN_UNDEF' else c
        elif b in ('STB_GLOBAL', 'STB_GNU_UNIQUE'):
            c = c.upper()
        out.append((s['st_value'], s['st_size'], c, s.name))
    return out


def main():
    if len(sys.argv) == 4 and sys.argv[2] == '--compare':
        mine = set(rows(sys.argv[1]))
        real = set()
        for line in open(sys.argv[3]):
            p = line.split()
            if len(p) == 4:
                real.add((int(p[0], 16), int(p[1], 16), p[2], p[3]))
        msized = {r for r in mine if r[1]}
        print('mine %d rows (%d sized), real %d sized rows' % (len(mine), len(msized), len(real)))
        miss, extra = sorted(real - mine), sorted(msized - real)
        print('real rows missing from mine: %d' % len(miss))
        for x in miss[:10]:
            print('  MISSING 0x%x %d %s %s' % x)
        print('mine sized rows not in real: %d' % len(extra))
        for x in extra[:10]:
            print('  EXTRA 0x%x %d %s %s' % x)
        ok = not miss and not extra
        print('COMPARE: %s' % ('EQUAL (sized rows)' if ok else 'DIFFERENT'))
        sys.exit(0 if ok else 1)
    for a, s, c, n in sorted(rows(sys.argv[1]), key=lambda r: (r[0], r[3])):
        print('%016x %016x %s %s' % (a, s, c, n) if s else '%016x %s %s' % (a, c, n))


if __name__ == '__main__':
    main()
