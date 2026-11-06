#!/usr/bin/env python3
"""mknm.py -- the text extracts of an unstripped twin that the start-up generators read in place of the twin itself
(the twin is a host binary and is not shipped).

  mknm.py TWIN IMAGE NAMES_OUT SYMTAB_OUT [--same TWIN2]

NAMES_OUT   the names file (hsform.py --names): one line per NAME,
                <16-hex address> <hex size> T <name>
            from the twin's .symtab, the FIRST symtab entry of each name, sorted by address (stable).
SYMTAB_OUT  the symbol extract (--twin of hsform.py, gen_ad2.py, gen_ad1k.py and pins.py stamp): one line per .symtab
            entry that has a name not starting with `$` (the mapping symbols, which every consumer skips), in .symtab
            order,
                <16-hex value> <hex size> <symbol type> <name>
            gen_ad2.py reads it as an nm listing (load_syms), gen_ad1k.py as its .symtab list (all_symbols), and
            hsform.py / pins.py take the twin's sha256 from its first header line.

Before it writes anything it checks that TWIN is IMAGE's twin: PT_LOAD 2..4 of the two (the text and the two data
segments: p_vaddr, p_filesz, p_memsz, p_flags and the bytes) are equal; else it refuses. Each output starts with `#`
lines that name the twin's sha256, the image's sha256 and that check.

--same TWIN2: a second twin of the same image. It must pass the same check, and TWIN and TWIN2 must have the same size
and be byte-equal outside .note.gnu.build-id and the .debug_* sections (so the same .symtab and .strtab, and the same
extract). The header says so, with TWIN2's sha256."""
import argparse, hashlib, sys

from elftools.elf.elffile import ELFFile


def sha256(b):
    return hashlib.sha256(b).hexdigest()


def loads(e):
    return [(s['p_vaddr'], s['p_filesz'], s['p_memsz'], s['p_flags'], s.data())
            for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']


def check_twin(twin, tl, il, label):
    if len(tl) < 4 or len(il) < 4 or tl[1:4] != il[1:4]:
        sys.exit('mknm: REFUSED: PT_LOAD 2..4 of %s and of the image differ: it is not the image\'s twin' % label)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('twin'); ap.add_argument('image'); ap.add_argument('names_out'); ap.add_argument('symtab_out')
    ap.add_argument('--same', default=None, help='a second twin of the same image (see above)')
    a = ap.parse_args()
    tb, ib = open(a.twin, 'rb').read(), open(a.image, 'rb').read()
    te, ie = ELFFile(open(a.twin, 'rb')), ELFFile(open(a.image, 'rb'))
    il = loads(ie)
    check_twin(a.twin, loads(te), il, 'the twin')
    st = te.get_section_by_name('.symtab')
    assert st is not None, 'the twin has no .symtab (it is not an unstripped twin)'
    head = ['# unstripped twin sha256 %s (%d bytes): text extract of its .symtab, made by mknm.py' % (sha256(tb), len(tb)),
            '# image sha256 %s (%d bytes): PT_LOAD 2..4 of the twin and of the image are byte-equal (checked)'
            % (sha256(ib), len(ib))]
    if a.same:
        sb = open(a.same, 'rb').read()
        se = ELFFile(open(a.same, 'rb'))
        check_twin(a.same, loads(se), il, 'the second twin')
        assert len(sb) == len(tb), 'the second twin has another size'
        x, y = bytearray(tb), bytearray(sb)
        for s in te.iter_sections():
            if s.name == '.note.gnu.build-id' or s.name.startswith('.debug_'):
                o, n = s['sh_offset'], s['sh_size']
                x[o:o + n] = y[o:o + n] = bytes(n)
        if x != y:
            sys.exit('mknm: REFUSED: the two twins differ outside .note.gnu.build-id and the .debug_* sections')
        head.append('# twin sha256 %s gives the same extract: the same .symtab (%d entries), PT_LOAD 2..4 byte-equal to '
                    'the image, and the two twins differ only inside .note.gnu.build-id and the .debug_* sections'
                    % (sha256(sb), st.num_symbols()))
    syms = [(s.name, s['st_value'], s['st_size'], s['st_info']['type']) for s in st.iter_symbols()]
    first = {}
    for n, v, sz, _ in syms:
        if n:
            assert len(n.split()) == 1 and n == n.strip(), 'symbol name with white space: %r' % n
            first.setdefault(n, (v, sz))
    rows = sorted(((v, sz, n) for n, (v, sz) in first.items()), key=lambda t: t[0])
    nhead = head + ['# names file: one line per name, <16-hex address> <hex size> T <name>, the first .symtab entry of '
                    'each name, sorted by address']
    shead = head + ['# symbol extract: one line per .symtab entry with a name not starting with $, <16-hex value> <hex size> '
                    '<symbol type> <name>, in .symtab order']
    keep = [(n, v, sz, t) for n, v, sz, t in syms if n and not n.startswith('$')]
    open(a.names_out, 'w').write('\n'.join(nhead + ['%016x %x T %s' % r for r in rows]) + '\n')
    open(a.symtab_out, 'w').write('\n'.join(shead + ['%016x %x %s %s' % (v, sz, t, n) for n, v, sz, t in keep]) + '\n')
    print('mknm: %s (%d names), %s (%d entries)' % (a.names_out, len(rows), a.symtab_out, len(keep)))


if __name__ == '__main__':
    main()
