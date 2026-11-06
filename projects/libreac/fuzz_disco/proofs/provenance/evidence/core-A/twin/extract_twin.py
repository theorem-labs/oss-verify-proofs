#!/usr/bin/env python3
"""extract_twin.py TWIN PIN OUT.txt

Writes the symbol and section facts of an unstripped twin as text, so that the scripts of this directory can run
without the twin binary. The twin is the same build as the released (stripped) PIN plus its symbol table, section
headers and debug sections. The extract header names the sha256 of both files and checks that PT_LOAD 2..4 of the
twin and the pin are byte-equal (PT_LOAD 1 holds the ELF header and the build-id note, which differ). Every byte a
script reads from a loaded segment is then taken from the pin.

Lines:
  S <index> <name> <sh_type> <sh_addr> <sh_size> <sh_flags>             one per section header, in table order
  Y <index> <st_value> <st_size> <type> <bind> <st_shndx> <name>      one per .symtab entry, in table order
Numbers are hexadecimal with 0x, except index. A missing name is written as '-'.
"""
import hashlib, sys
from elftools.elf.elffile import ELFFile


def loads(path):
    raw = open(path, 'rb').read()
    e = ELFFile(open(path, 'rb'))
    return [raw[s['p_offset']:s['p_offset'] + s['p_filesz']] for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']


def main():
    twin, pin, out = sys.argv[1:4]
    tl, pl = loads(twin), loads(pin)
    if len(tl) != len(pl) or len(tl) < 4 or any(tl[i] != pl[i] for i in (1, 2, 3)):
        sys.exit('extract_twin: PT_LOAD 2..4 of twin and pin are NOT byte-equal')
    sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
    e = ELFFile(open(twin, 'rb'))
    lines = [
        '# Symbol and section facts of an unstripped twin (text extract written by extract_twin.py).',
        f'# twin sha256 {sha(twin)}',
        f'# pin sha256 {sha(pin)}',
        f'# PT_LOAD 2..4 of twin and pin: byte-equal ({len(tl)} PT_LOAD segments in each)',
    ]
    for i, s in enumerate(e.iter_sections()):
        lines.append(f"S {i} {s.name or '-'} {s['sh_type']} {s['sh_addr']:#x} {s['sh_size']:#x} {s['sh_flags']:#x}")
    for i, s in enumerate(e.get_section_by_name('.symtab').iter_symbols()):
        lines.append(f"Y {i} {s['st_value']:#x} {s['st_size']:#x} {s['st_info']['type']} {s['st_info']['bind']} "
                     f"{s['st_shndx']} {s.name or '-'}")
    open(out, 'w').write('\n'.join(lines) + '\n')
    print(f'extract_twin: {out}: {sum(l[0] == "S" for l in lines)} sections, {sum(l[0] == "Y" for l in lines)} symbols')


if __name__ == '__main__':
    main()
