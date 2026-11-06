#!/usr/bin/env python3
"""symbol_table.py -- the symbol table of an unstripped twin, in `nm -S --size-sort` form, for the listing scripts.

The released (pinned) image is stripped, so the symbol names and addresses the listings use come from its
unstripped twin. This script reads the twin's .symtab and writes one line `ADDR SIZE TYPE NAME` (16 hex digits
each; TYPE is the letter binutils nm prints) per defined symbol of nonzero size, sorted by size, then name, then
address: the order `nm -S --size-sort` gives. RISC-V mapping symbols ($x, $d, ...) and section / file symbols
are left out, as nm leaves them out.

Before the symbol lines it writes header lines of ONE word each (`#key=value`), which the listing scripts skip
(they read lines of three or more words): the sha256 of the twin and of the pin, and the result of comparing
the twin's and the pin's 2nd, 3rd and 4th PT_LOAD segments byte for byte (address, file size and file bytes).
It exits 1, writing nothing, if those segments differ, so an extract always belongs to the pin it names.

Usage: symbol_table.py TWIN PIN OUT
"""
import hashlib
import struct
import sys

SHT_SYMTAB, SHT_NOBITS = 2, 8
SHF_WRITE, SHF_ALLOC, SHF_EXECINSTR = 0x1, 0x2, 0x4
SHN_UNDEF, SHN_ABS, SHN_COMMON = 0, 0xFFF1, 0xFFF2
STB_LOCAL, STB_GLOBAL, STB_WEAK, STB_GNU_UNIQUE = 0, 1, 2, 10
STT_OBJECT, STT_SECTION, STT_FILE, STT_GNU_IFUNC = 1, 3, 4, 10


def elf_header(d):
    if d[:4] != b"\x7fELF" or d[4] != 2 or d[5] != 1:
        sys.exit("not a 64-bit little-endian ELF")
    (_t, _m, _v, _entry, phoff, shoff, _f, _ehs, phes, phn, shes, shn, shstrndx) = struct.unpack_from(
        "<HHIQQQIHHHHHH", d, 16)
    return phoff, phes, phn, shoff, shes, shn, shstrndx


def pt_loads(d):
    phoff, phes, phn = elf_header(d)[:3]
    out = []
    for i in range(phn):
        p_type, _fl, p_off, p_vaddr, _pa, p_filesz, p_memsz, _al = struct.unpack_from("<IIQQQQQQ", d, phoff + i * phes)
        if p_type == 1:
            out.append((p_vaddr, p_filesz, p_memsz, d[p_off:p_off + p_filesz]))
    return out


def sections(d):
    _po, _pe, _pn, shoff, shes, shn, _si = elf_header(d)
    secs = []
    for i in range(shn):
        (nm, typ, flags, addr, off, size, link, info, _al, entsize) = struct.unpack_from("<IIQQQQIIQQ", d, shoff + i * shes)
        secs.append(dict(name=nm, type=typ, flags=flags, addr=addr, off=off, size=size, link=link, entsize=entsize))
    return secs


def cstr(d, off):
    return d[off:d.index(b"\0", off)].decode()


def letter(secs, bind, typ, shndx):
    """The letter binutils nm prints for a defined symbol (its ELF symbol classes)."""
    if typ == STT_GNU_IFUNC:
        return "i"
    if bind == STB_WEAK:
        return "V" if typ == STT_OBJECT else "W"
    if bind == STB_GNU_UNIQUE:
        return "u"
    if shndx == SHN_COMMON:
        return "C"
    if shndx == SHN_ABS:
        c = "a"
    else:
        s = secs[shndx]
        if s["flags"] & SHF_EXECINSTR:
            c = "t"
        elif not s["flags"] & SHF_ALLOC:
            c = "n"
        elif s["type"] == SHT_NOBITS:
            c = "b"
        elif s["flags"] & SHF_WRITE:
            c = "d"
        else:
            c = "r"
    return c.upper() if bind == STB_GLOBAL else c


def symbol_lines(d):
    secs = sections(d)
    st = [s for s in secs if s["type"] == SHT_SYMTAB]
    if not st:
        sys.exit("no .symtab: give the unstripped twin, not the pin")
    st = st[0]
    strtab = secs[st["link"]]["off"]
    rows = []
    for k in range(st["size"] // st["entsize"]):
        nm, info, _other, shndx, value, size = struct.unpack_from("<IBBHQQ", d, st["off"] + k * st["entsize"])
        bind, typ = info >> 4, info & 0xF
        name = cstr(d, strtab + nm)
        if not name or shndx == SHN_UNDEF or size == 0 or typ in (STT_SECTION, STT_FILE) or name.startswith("$"):
            continue
        rows.append((size, name, value, letter(secs, bind, typ, shndx)))
    rows.sort()
    return ["%016x %016x %s %s" % (a, s, c, n) for s, n, a, c in rows]


def main():
    if len(sys.argv) != 4:
        sys.exit(__doc__)
    twin_p, pin_p, out_p = sys.argv[1:]
    twin, pin = open(twin_p, "rb").read(), open(pin_p, "rb").read()
    lt, lp = pt_loads(twin), pt_loads(pin)
    same = len(lt) >= 4 and len(lp) >= 4 and all(
        lt[i][0] == lp[i][0] and lt[i][1] == lp[i][1] and lt[i][3] == lp[i][3] for i in (1, 2, 3))
    if not same:
        sys.exit("PT_LOAD 2..4 of the twin and the pin differ: this twin does not belong to this pin")
    head = ["#symbol-table-extract", "#form=nm-S-size-sort",
            "#twin_sha256=" + hashlib.sha256(twin).hexdigest(),
            "#pin_sha256=" + hashlib.sha256(pin).hexdigest(),
            "#pt_load_2_3_4_of_twin_and_pin=byte-equal"]
    open(out_p, "w").write("".join(x + "\n" for x in head + symbol_lines(twin)))


if __name__ == "__main__":
    main()
