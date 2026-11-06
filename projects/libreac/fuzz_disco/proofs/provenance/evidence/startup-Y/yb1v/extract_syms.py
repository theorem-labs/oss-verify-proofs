#!/usr/bin/env python3
"""extract_syms.py TWIN PIN OUT [NAME ...] -- the function-symbol extract of an image's unstripped twin, as nm text.

gen_traces.py reads the image's .text from the pin itself, and the function symbols (lo, hi, name) through
resolve_code.sym_ranges, which takes them from an unstripped twin's .symtab (every STT_FUNC symbol of non-zero size) or
from an nm text file whose name ends in `.txt` (`addr size type name`, address and size in hex, type T or t). This
script writes the second form from the first: one line per STT_FUNC symbol of TWIN with a non-zero size, type t for a
LOCAL symbol and T for any other binding, so sym_ranges returns the same list from OUT as from TWIN. With NAMEs, only
the symbols of those names are kept (each must be present): the form derive_yb1v.py reads.

It refuses unless PT_LOAD 2..4 (the executable segment and the two writable ones) of TWIN and PIN are byte-equal, so
the symbols describe the pin's code. The `#` header lines name both sha256 and that check; sym_ranges skips them.
"""
import hashlib, sys
from elftools.elf.elffile import ELFFile


def sha256(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def loads(e):
    return [(s['p_vaddr'], s['p_filesz'], s['p_memsz'], s['p_flags'], s.data())
            for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']


def main():
    twin, pin, out, names = sys.argv[1], sys.argv[2], sys.argv[3], set(sys.argv[4:])
    if not out.endswith('.txt'):
        sys.exit('extract_syms: OUT must end in .txt (sym_ranges reads nm text only from such a file)')
    with open(twin, 'rb') as ft, open(pin, 'rb') as fp:
        et, ep = ELFFile(ft), ELFFile(fp)
        lt, lp = loads(et), loads(ep)
        if len(lt) < 4 or len(lp) < 4 or lt[1:4] != lp[1:4]:
            sys.exit('extract_syms: REFUSED: PT_LOAD 2..4 of %s and %s are not byte-equal' % (twin, pin))
        rows = set()
        for s in et.get_section_by_name('.symtab').iter_symbols():
            if s['st_info']['type'] == 'STT_FUNC' and s['st_size'] > 0 and (not names or s.name in names):
                if len(s.name.split()) != 1:
                    sys.exit('extract_syms: REFUSED: symbol name %r is not one nm field' % s.name)
                rows.add((s['st_value'], s['st_size'], 't' if s['st_info']['bind'] == 'STB_LOCAL' else 'T', s.name))
    missing = names - {r[3] for r in rows}
    if missing:
        sys.exit('extract_syms: REFUSED: no sized function symbol named %s in %s' % (' '.join(sorted(missing)), twin))
    with open(out, 'w') as f:
        f.write('# function symbols of an unstripped twin, nm text: addr size type name (hex, hex, T or t, name)\n')
        f.write('# twin sha256 %s\n' % sha256(twin))
        f.write('# pin  sha256 %s\n' % sha256(pin))
        f.write('# PT_LOAD 2..4 of twin and pin: byte-equal (checked)\n')
        for lo, n, t, name in sorted(rows):
            f.write('%016x %016x %s %s\n' % (lo, n, t, name))


main()
