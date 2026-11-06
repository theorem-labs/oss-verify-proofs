#!/usr/bin/env python3
"""image_facts.py -- the section and segment facts of a pinned image that the listings and the read-only range use.

Reads the pinned image's section headers and program headers and writes a text table:
  pin_sha256 <hex>
  load <k> <vaddr> <filesz> <memsz>          one line per PT_LOAD, k = 1, 2, ...
  nseg <count of PT_LOAD>
  section <name> <addr> <size> <end>          one line per allocated section, in header order
  relro <lo> <hi>                             .data.rel.ro start .. .got end: the read-only-after-relocation range
  got <slot> <cell>                           for each --got-of CELL: the one .got slot whose 8-byte word is CELL
All numbers are hex without 0x except k and the count.

Usage: image_facts.py PIN OUT [--got-of CELL ...]
"""
import argparse
import hashlib
import struct
import sys

SHF_ALLOC = 0x2


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("pin")
    ap.add_argument("out")
    ap.add_argument("--got-of", action="append", default=[])
    a = ap.parse_args()
    d = open(a.pin, "rb").read()
    if d[:4] != b"\x7fELF" or d[4] != 2 or d[5] != 1:
        sys.exit("not a 64-bit little-endian ELF")
    (_t, _m, _v, _entry, phoff, shoff, _f, _ehs, phes, phn, shes, shn, shstrndx) = struct.unpack_from(
        "<HHIQQQIHHHHHH", d, 16)
    out = ["pin_sha256 " + hashlib.sha256(d).hexdigest()]
    loads = []
    for i in range(phn):
        p_type, _fl, p_off, p_vaddr, _pa, p_filesz, p_memsz, _al = struct.unpack_from("<IIQQQQQQ", d, phoff + i * phes)
        if p_type == 1:
            loads.append((p_vaddr, p_off, p_filesz, p_memsz))
            out.append("load %d %x %x %x" % (len(loads), p_vaddr, p_filesz, p_memsz))
    out.append("nseg %d" % len(loads))
    sh = [struct.unpack_from("<IIQQQQIIQQ", d, shoff + i * shes) for i in range(shn)]
    stroff = sh[shstrndx][4]
    secs = {}
    for (nm, _typ, flags, addr, _off, size, _l, _i, _al, _es) in sh:
        name = d[stroff + nm:d.index(b"\0", stroff + nm)].decode()
        if flags & SHF_ALLOC:
            out.append("section %s %x %x %x" % (name, addr, size, addr + size))
            secs[name] = (addr, size)
    if ".data.rel.ro" not in secs or ".got" not in secs:
        sys.exit("no .data.rel.ro or .got section")
    out.append("relro %x %x" % (secs[".data.rel.ro"][0], secs[".got"][0] + secs[".got"][1]))
    got_lo, got_hi = secs[".got"][0], secs[".got"][0] + secs[".got"][1]

    def word(addr):
        seg = [s for s in loads if s[0] <= addr and addr + 8 <= s[0] + s[2]]
        return struct.unpack_from("<Q", d, seg[0][1] + addr - seg[0][0])[0] if seg else None

    for c in a.got_of:
        cell = int(c, 16)
        slots = [x for x in range(got_lo, got_hi, 8) if word(x) == cell]
        if len(slots) != 1:
            sys.exit("%d .got slots hold %x (want exactly one)" % (len(slots), cell))
        out.append("got %x %x" % (slots[0], cell))
    open(a.out, "w").write("".join(x + "\n" for x in out))


if __name__ == "__main__":
    main()
