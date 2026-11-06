"""elfdis.py -- the loaded bytes of a RISC-V64 ELF and a capstone disassembly of an address range.

load(path) -> (bytes, {symbol: [(addr, size, st_type), ...]}, [(vaddr, off, filesz)] of the PT_LOAD segments, path)
disasm(img, lo, size) -> [(address, mnemonic, op_str)] of the bytes that map to [lo, lo + size)
_NUM: the numeral pattern; a caller masks the operands of an instruction with _NUM.sub('#', op_str)

Only these definitions are here: they are what gen_symtab.py calls. Needs capstone (5.0.7 on the run of record).
"""
import struct

import capstone
import re

_NUM = re.compile(r'-?0x[0-9a-fA-F]+|-?\b\d+\b')


def load(path):
    """Return (bytes, {sym: [(addr, size, st_type), ...] in symbol-table order}, [(vaddr, off, filesz)], path)."""
    f = open(path, 'rb').read()
    if f[:4] != b'\x7fELF':
        raise SystemExit(f'{path}: not an ELF')

    e_shoff = struct.unpack_from('<Q', f, 0x28)[0]
    e_shentsize = struct.unpack_from('<H', f, 0x3a)[0]
    e_shnum = struct.unpack_from('<H', f, 0x3c)[0]
    secs = []
    for i in range(e_shnum):
        o = e_shoff + i * e_shentsize
        secs.append(dict(
            type=struct.unpack_from('<I', f, o + 4)[0],
            off=struct.unpack_from('<Q', f, o + 0x18)[0],
            size=struct.unpack_from('<Q', f, o + 0x20)[0],
            link=struct.unpack_from('<I', f, o + 0x28)[0],
            entsize=struct.unpack_from('<Q', f, o + 0x38)[0]))

    syms = {}
    for s in secs:
        if s['type'] not in (2, 11) or not s['entsize']:  # SYMTAB, DYNSYM
            continue
        strt = secs[s['link']]
        for j in range(s['size'] // s['entsize']):
            o = s['off'] + j * s['entsize']
            nameoff = struct.unpack_from('<I', f, o)[0]
            info = f[o + 4]
            val = struct.unpack_from('<Q', f, o + 8)[0]
            sz = struct.unpack_from('<Q', f, o + 16)[0]
            tail = f[strt['off'] + nameoff:]
            name = tail[:tail.index(b'\0')].decode('utf-8', 'replace')
            if name:
                syms.setdefault(name, []).append((val, sz, info & 0xf))

    e_phoff = struct.unpack_from('<Q', f, 0x20)[0]
    e_phentsize = struct.unpack_from('<H', f, 0x36)[0]
    e_phnum = struct.unpack_from('<H', f, 0x38)[0]
    segs = []
    for i in range(e_phnum):
        o = e_phoff + i * e_phentsize
        if struct.unpack_from('<I', f, o)[0] != 1:  # PT_LOAD
            continue
        segs.append((struct.unpack_from('<Q', f, o + 0x10)[0],
                     struct.unpack_from('<Q', f, o + 0x08)[0],
                     struct.unpack_from('<Q', f, o + 0x20)[0]))
    return f, syms, segs, path


def v2o(segs, v):
    for vaddr, off, filesz in segs:
        if vaddr <= v < vaddr + filesz:
            return off + (v - vaddr)
    raise SystemExit(f'address {v:#x} is in no PT_LOAD segment')


_MD = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64)


def disasm(img, lo, size):
    f, _syms, segs, _path = img
    o = v2o(segs, lo)
    return [(i.address, i.mnemonic, i.op_str) for i in _MD.disasm(f[o:o + size], lo)]
