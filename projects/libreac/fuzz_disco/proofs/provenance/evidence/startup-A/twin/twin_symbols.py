#!/usr/bin/env python3
"""twin_symbols.py TWIN PIN OUT -- the symbol facts of an unstripped twin, as text, for tools that would read the twin.

The twin is the same build as the pinned (released) image, with its symbol table and debug sections kept. Tools that
read the twin read only its .symtab; the code and data they read come from the pin. OUT is an `nm -S` style listing,
one line per symbol, `ADDRESS SIZE TYPE NAME` (16 hex digits each, the nm type letter), in .symtab order. Left out:
symbols with no name, the RISC-V mapping symbols (`$x`, `$d`, ...), source-file symbols (STT_FILE) and undefined
symbols. Each header line starts with `#` and has more than four fields, so no nm reader takes it for a symbol. A
reader that takes t/T/w/W for a function is exact here: this script refuses a twin in which a symbol that is not
STT_FUNC would get one of those letters.

The header names the twin's sha256 and the pin's sha256, and states what this script checks before it writes: PT_LOAD 2
to 4 of twin and pin are byte-equal, and PT_LOAD 1 differs only in the ELF header's section-table fields and the GNU
build-id note. So the twin's symbols describe the pinned image. A twin that fails a check is refused (exit 1).
"""
import hashlib
import sys

from elftools.elf.elffile import ELFFile


def sha256(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


def loads(path):
    raw = open(path, 'rb').read()
    e = ELFFile(open(path, 'rb'))
    return raw, e, [(s['p_vaddr'], s['p_offset'], s['p_filesz'], s['p_memsz'])
                    for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']


def letter(e, s):
    """the nm type letter of a defined symbol (GNU nm's rules for ELF)"""
    t, b, x = s['st_info']['type'], s['st_info']['bind'], s['st_shndx']
    if b == 'STB_WEAK':
        return 'V' if t == 'STT_OBJECT' else 'W'
    if x == 'SHN_ABS':
        c = 'a'
    elif x == 'SHN_COMMON':
        c = 'c'
    else:
        sec = e.get_section(x)
        fl, ty = sec['sh_flags'], sec['sh_type']
        if fl & 0x4:
            c = 't'
        elif not fl & 0x2:
            c = 'n'
        elif ty == 'SHT_NOBITS':
            c = 'b'
        elif fl & 0x1:
            c = 'd'
        else:
            c = 'r'
    return c.upper() if b == 'STB_GLOBAL' else c


def main():
    if len(sys.argv) != 4:
        sys.exit('usage: twin_symbols.py TWIN PIN OUT')
    twin, pin, out = sys.argv[1:]
    traw, te, tl = loads(twin)
    praw, pe, pl = loads(pin)
    if len(tl) != 4 or len(pl) != 4 or [x[0::2] for x in tl] != [x[0::2] for x in pl]:
        sys.exit('twin_symbols: REFUSED: the PT_LOAD tables of twin and pin differ')
    for k in (1, 2, 3):
        (_, to, tf, _), (_, po, pf, _) = tl[k], pl[k]
        if traw[to:to + tf] != praw[po:po + pf]:
            sys.exit('twin_symbols: REFUSED: PT_LOAD %d of twin and pin differ' % (k + 1))
    note = pe.get_section_by_name('.note.gnu.build-id')
    skip = set(range(0x28, 0x30)) | set(range(0x3c, 0x40))           # e_shoff, e_shnum, e_shstrndx
    if note is not None:
        skip |= set(range(note['sh_offset'], note['sh_offset'] + note['sh_size']))
    (_, to, tf, _), (_, po, pf, _) = tl[0], pl[0]
    bad = [i for i in range(tf) if traw[to + i] != praw[po + i] and to + i not in skip]
    if bad:
        sys.exit('twin_symbols: REFUSED: PT_LOAD 1 of twin and pin differ outside the ELF header section-table fields '
                 'and the build-id note (first at file offset %#x)' % (to + bad[0]))
    st = te.get_section_by_name('.symtab')
    if st is None:
        sys.exit('twin_symbols: REFUSED: %s has no .symtab (not an unstripped twin)' % twin)
    rows, n = [], 0
    for s in st.iter_symbols():
        n += 1
        if (not s.name or s.name.startswith('$') or s['st_info']['type'] == 'STT_FILE'
                or s['st_shndx'] == 'SHN_UNDEF'):
            continue
        c = letter(te, s)
        if c in 'tTwW' and s['st_info']['type'] != 'STT_FUNC':
            sys.exit('twin_symbols: REFUSED: %s (%s) would get the function letter %s' % (s.name, s['st_info']['type'], c))
        rows.append('%016x %016x %s %s' % (s['st_value'], s['st_size'], c, s.name))
    head = [
        '# symbols of the unstripped twin sha256 %s, made by twin_symbols.py' % sha256(twin),
        '# the pinned image is sha256 %s (the released image this listing describes)' % sha256(pin),
        '# check before writing: PT_LOAD 2 to 4 of twin and pin are byte-equal; PT_LOAD 1 differs only in the ELF header '
        'section-table fields and the build-id note',
        '# %d of the %d .symtab entries: no unnamed, mapping ($), source-file or undefined symbols; format: address size '
        'nm-type name' % (len(rows), n),
    ]
    with open(out, 'w') as f:
        f.write('\n'.join(head + rows) + '\n')
    print('twin_symbols: wrote %s (%d symbols)' % (out, len(rows)))


if __name__ == '__main__':
    main()
