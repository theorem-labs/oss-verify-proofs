#!/usr/bin/env python3
"""elfinfo.py TWIN_ELF OUTPREFIX -- listings of an unstripped ELF (pyelftools; this host has no binutils):
  OUTPREFIX.nmS.txt      `nm -S` form: ADDR SIZE TYPE NAME (hex, 16 digits), the form af0m.py --names reads
  OUTPREFIX.nm.txt       `nm` form:    ADDR TYPE NAME
  OUTPREFIX.sections.txt name addr size flags (hex), one section per line
  OUTPREFIX.phdrs.txt    type vaddr filesz memsz flags, one program header per line
T/t function, D/d object (or TLS), N/n other; local symbols lower case. Computes nothing else."""
import sys
from elftools.elf.elffile import ELFFile

e = ELFFile(open(sys.argv[1], 'rb'))
out = sys.argv[2]
with open(out + '.nmS.txt', 'w') as fs, open(out + '.nm.txt', 'w') as fn:
    for s in e.get_section_by_name('.symtab').iter_symbols():
        ty, b = s['st_info']['type'], s['st_info']['bind']
        if not s.name or ty in ('STT_FILE', 'STT_SECTION') or s['st_shndx'] == 'SHN_UNDEF':
            continue
        c = 'T' if ty == 'STT_FUNC' else 'D' if ty in ('STT_OBJECT', 'STT_TLS') else 'N'
        c = c.lower() if b == 'STB_LOCAL' else c
        fs.write('%016x %016x %s %s\n' % (s['st_value'], s['st_size'], c, s.name))
        fn.write('%016x %s %s\n' % (s['st_value'], c, s.name))
with open(out + '.sections.txt', 'w') as f:
    for sec in e.iter_sections():
        f.write('%s 0x%x 0x%x 0x%x\n' % (sec.name or '-', sec['sh_addr'], sec['sh_size'], sec['sh_flags']))
with open(out + '.phdrs.txt', 'w') as f:
    for p in e.iter_segments():
        f.write('%s 0x%x 0x%x 0x%x 0x%x\n' % (p['p_type'], p['p_vaddr'], p['p_filesz'], p['p_memsz'], p['p_flags']))
