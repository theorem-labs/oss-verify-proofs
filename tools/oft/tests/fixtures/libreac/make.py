"""Write the two symbol facts of this folder (README.md) from libreac's fuzz_pcap plain builds, 1.8.0 and 1.9.0.

    cd tools && PYTHONPATH=. python3 -B oft/tests/fixtures/libreac/make.py BEFORE AFTER FUNCTIONS

BEFORE and AFTER are the two stripped binaries and FUNCTIONS the table that names their functions and gives each one's
address and size in both (columns name, addr_before, size_before, addr_after, size_after; a function's aliases are
joined by `,` in its name).  The binaries have no symbol table, so oft symbols cannot read them: each kept function's
bytes are cut out of .text at its address and size, with elf.Elf, and hashed as symbols.read hashes them, exact and
through symbols.mask with the binary's Image (symbols.build_image), but with no function known never to return (that
list needs the symbol table).  No line table is read, so every function's lines are `-`."""
import csv
import hashlib
import os
import sys

from oft import elf, symbols

HERE = os.path.dirname(os.path.abspath(__file__))
# the functions kept, as FUNCTIONS names them: the two that libreac 1.9.0 changed or moved in pcap_source.c, the two
# beside them, the fuzz target's own fopen and musl's libc_start_init with its alias __libc_start_init
KEEP = ("main", "libreac_fuzz_fopen", "pcap_source_open", "pcap_source_next", "pcap_source_close",
        "__libc_start_init,libc_start_init")


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def fact(binary, rows, side):
    """(the binary's sha256, [Sym] of each kept function and alias of it, by address and then name)."""
    bare = elf.Elf(binary)
    image = symbols.build_image(bare, bare.sections(), frozenset())
    syms = []
    for row in rows:
        address, size = int(row["addr_" + side], 16), int(row["size_" + side])
        start = address - bare.text_addr
        if start < 0 or start + size > len(bare.text):
            raise ValueError("%s: %s at 0x%x (%d bytes) is outside .text" % (binary, row["name"], address, size))
        code = bare.text[start:start + size]
        syms += [symbols.Sym(name, "func", address, size, sha256(code), sha256(symbols.mask(code, address, image)),
                             "-")
                 for name in row["name"].split(",")]
    return bare.sha256, sorted(syms, key=lambda s: (s.address, s.name))


def main(before, after, functions):
    with open(functions, encoding="utf-8", newline="") as f:
        rows = {r["name"]: r for r in csv.DictReader(f, delimiter="\t") if r["name"] in KEEP}
    missing = sorted(set(KEEP) - set(rows))
    if missing:
        raise ValueError("%s names no function %s" % (functions, ", ".join(missing)))
    kept = [rows[name] for name in KEEP]
    for binary, side, out in ((before, "before", "fuzz_pcap-1.8.0.plain.tsv"),
                              (after, "after", "fuzz_pcap-1.9.0.plain.tsv")):
        sha, syms = fact(binary, kept, side)
        symbols.write(os.path.join(HERE, out), syms, sha)
        print("%s: %d names, sha256 %s" % (out, len(syms), sha))


if __name__ == "__main__":
    if len(sys.argv) != 4:
        sys.exit(__doc__)
    main(*sys.argv[1:])
