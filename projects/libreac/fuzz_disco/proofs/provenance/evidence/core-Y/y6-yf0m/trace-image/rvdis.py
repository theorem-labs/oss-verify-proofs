"""rvdis.py -- the three helpers that the vendored base.py and names.py import from the trace kit's rvdis (not on this machine):
load(img) -> (text address, text bytes, ELFFile); md (capstone RISC-V 64 + C, detail off); syms(nm.txt) -> {addr: [names]}."""
import capstone
from elftools.elf.elffile import ELFFile

md = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)
md.skipdata = True


def load(img):
    e = ELFFile(open(img, 'rb'))
    t = e.get_section_by_name('.text')
    return t['sh_addr'], t.data(), e


def syms(nm):
    """nm listing, `ADDR TYPE NAME` or `ADDR SIZE TYPE NAME` (nm -S)"""
    d = {}
    for line in open(nm):
        p = line.split()
        if len(p) == 3 and p[1] in 'tTwW':
            d.setdefault(int(p[0], 16), []).append(p[2])
        elif len(p) >= 4 and p[2] in 'tTwW':
            d.setdefault(int(p[0], 16), []).append(p[3])
    return d
