"""Write the two symbol facts of this folder (README.md) from libreac's fuzz_pcap plain builds, 1.8.0 and 1.9.0.

    cd tools && PYTHONPATH=. python3 -B oft/tests/fixtures/libreac/make.py BEFORE AFTER FUNCTIONS

BEFORE and AFTER are the two stripped binaries and FUNCTIONS the table that names their functions and gives each one's
address and size in both (columns name, addr_before, size_before, addr_after, size_after; a function's aliases are
joined by `,` in its name).  The binaries have no symbol table, so oft symbols cannot read them: each kept function's
bytes are cut out of .text at its address and size, with elf.Elf, and hashed as symbols.read hashes them, exact and
through symbols.mask_targets with the binary's Image (symbols.build_image), but with no function known never to
return (that list needs the symbol table); its targets are resolved against every function FUNCTIONS names and
every section of the binary, as a real fact resolves them against the whole symbol table.  No line table is read,
so every function's lines are `-`."""
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


def fact(binary, rows, keep, side):
    """(the binary's sha256, [Sym] of each kept function and alias of it, by address and then name).  Every function
    of rows, not only the kept ones, and every section of the binary are there to resolve the targets of a kept
    function (symbols.locator), as the whole symbol table is in a real fact."""
    bare = elf.Elf(binary)
    image = symbols.build_image(bare, bare.sections(), frozenset())
    places, syms, points = [], [], {}
    for row in rows:
        if not row["addr_" + side]:    # a function of the other build only
            continue
        address, size = int(row["addr_" + side], 16), int(row["size_" + side])
        start = address - bare.text_addr
        if start < 0 or start + size > len(bare.text):
            if row["name"] in keep:
                raise ValueError("%s: %s at 0x%x (%d bytes) is outside .text"
                                 % (binary, row["name"], address, size))
            continue
        places += [symbols.Sym(name, "func", address, size, "-", "-", "-", "-") for name in row["name"].split(",")]
        if row["name"] not in keep:
            continue
        code = bare.text[start:start + size]
        masked, found = symbols.mask_targets(code, address, image)
        for name in row["name"].split(","):
            points[len(syms)] = found
            syms.append(symbols.Sym(name, "func", address, size, sha256(code), sha256(masked), "-", "-"))
    places += [symbols.Sym(s.name, "section", s.address, s.size, "-", "-", "-", "-") for s in bare.sections()]

    def word(address):
        try:
            data = bare.contents(address, 8)
        except ValueError:
            return None
        return None if data is None else int.from_bytes(data, "little")

    find = symbols.locator(places, word)
    for i, found in points.items():
        syms[i] = syms[i]._replace(targets=symbols.target_id(found, find))
    return bare.sha256, sorted(syms, key=lambda s: (s.address, s.name))


def main(before, after, functions):
    with open(functions, encoding="utf-8", newline="") as f:
        rows = list(csv.DictReader(f, delimiter="\t"))
    named = {r["name"] for r in rows}
    missing = sorted(set(KEEP) - named)
    if missing:
        raise ValueError("%s names no function %s" % (functions, ", ".join(missing)))
    for binary, side, out in ((before, "before", "fuzz_pcap-1.8.0.plain.tsv"),
                              (after, "after", "fuzz_pcap-1.9.0.plain.tsv")):
        sha, syms = fact(binary, rows, KEEP, side)
        symbols.write(os.path.join(HERE, out), syms, sha)
        print("%s: %d names, sha256 %s" % (out, len(syms), sha))


if __name__ == "__main__":
    if len(sys.argv) != 4:
        sys.exit(__doc__)
    main(*sys.argv[1:])
