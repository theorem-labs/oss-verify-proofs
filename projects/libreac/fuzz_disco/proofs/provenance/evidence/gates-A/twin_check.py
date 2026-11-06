#!/usr/bin/env python3
"""twin_check.py -- are an unstripped twin and a released (stripped) pin the same program image?

Prints both files' sha256 and, for every PT_LOAD of the pin (numbered from 1 in program-header order), its vaddr,
file size, memory size and flags, and whether the twin has a PT_LOAD with the same header whose file bytes are equal.
Also prints the image top (the highest p_vaddr + p_memsz) and whether the twin's symbol table has _start.

Exit 0 when PT_LOAD 2..4 of twin and pin are byte-equal; 1 otherwise.

Usage: twin_check.py PIN TWIN
"""
import hashlib, struct, sys


def phdrs(raw):
    assert raw[:4] == b'\x7fELF' and raw[4] == 2 and raw[5] == 1, 'not a little-endian ELF64'
    e_phoff, = struct.unpack_from('<Q', raw, 0x20)
    e_phentsize, e_phnum = struct.unpack_from('<HH', raw, 0x36)
    out = []
    for i in range(e_phnum):
        p_type, p_flags, p_offset, p_vaddr, p_paddr, p_filesz, p_memsz, p_align = \
            struct.unpack_from('<IIQQQQQQ', raw, e_phoff + i * e_phentsize)
        out.append(dict(type=p_type, flags=p_flags, off=p_offset, vaddr=p_vaddr, filesz=p_filesz, memsz=p_memsz))
    return out


def has_start(raw):
    e_shoff, = struct.unpack_from('<Q', raw, 0x28)
    e_shentsize, e_shnum = struct.unpack_from('<HH', raw, 0x3a)
    secs = [struct.unpack_from('<IIQQQQIIQQ', raw, e_shoff + i * e_shentsize) for i in range(e_shnum)]
    for name, typ, flags, addr, off, size, link, info, align, entsize in secs:
        if typ != 2:                      # SHT_SYMTAB
            continue
        stroff = secs[link][4]
        for k in range(size // 24):
            st_name, = struct.unpack_from('<I', raw, off + k * 24)
            end = raw.index(b'\0', stroff + st_name)
            if raw[stroff + st_name:end] == b'_start':
                return True
    return False


def main():
    pin_path, twin_path = sys.argv[1:3]
    pin, twin = open(pin_path, 'rb').read(), open(twin_path, 'rb').read()
    print(f'pin  sha256 {hashlib.sha256(pin).hexdigest()}')
    print(f'twin sha256 {hashlib.sha256(twin).hexdigest()}')
    pl = [p for p in phdrs(pin) if p['type'] == 1]
    tl = [p for p in phdrs(twin) if p['type'] == 1]
    ok = True
    for n, p in enumerate(pl, 1):
        same = [t for t in tl if (t['vaddr'], t['filesz'], t['memsz'], t['flags']) ==
                (p['vaddr'], p['filesz'], p['memsz'], p['flags'])]
        eq = bool(same) and pin[p['off']:p['off'] + p['filesz']] == twin[same[0]['off']:same[0]['off'] + same[0]['filesz']]
        print(f'PT_LOAD {n} vaddr {p["vaddr"]:#x} filesz {p["filesz"]:#x} memsz {p["memsz"]:#x} flags {p["flags"]} '
              f'{"byte-equal" if eq else "DIFFERENT"}')
        if 2 <= n <= 4 and not eq:
            ok = False
    top = max(p['vaddr'] + p['memsz'] for p in pl)
    print(f'image top (max vaddr+memsz) {top:#x}')
    print(f'twin symtab has _start: {"yes" if has_start(twin) else "no"}')
    print(f'PT_LOAD 2..4 twin = pin: {"yes" if ok else "NO"}')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
