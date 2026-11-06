"""symbols.py -- the names table the start-up generators read, made from the shared symbol extract (no binary is read).

nm_lines(SYMBOLS.tsv) returns the lines of the names file these generators were written for, one line per NAME:

    <16-hex address> <hex size> T <name>

the FIRST .symtab entry of each name, sorted by address (stable). SYMBOLS.tsv is extract/symbols-asan-ubsan.tsv, written
by extract/extract_symbols.py from the unstripped twin in .symtab order, so this is the rule the names file of record was
made with (genad2/tools/mknm.py); on fuzz_disco.asan-ubsan's extract it gives that file byte for byte (2895 lines,
sha256 63ea9840e4b7).
"""


def nm_lines(path):
    first = {}
    for line in open(path):
        if line.startswith('#'):
            continue
        p = line.rstrip('\n').split('\t')
        if p[0]:
            first.setdefault(p[0], (int(p[1], 16), int(p[2])))
    rows = sorted(((v, sz, n) for n, (v, sz) in first.items()), key=lambda t: t[0])
    return ['%016x %x T %s\n' % r for r in rows]
