#!/usr/bin/env python3
"""imgfacts.py -- what one ELF image says about an address: the facts every gen-states rule measures.

    Img(pin, twin, kit)   pin = the unit's pinned (stripped) image: bytes and headers are read from it;
                          twin = its unstripped twin of the same link: only the symbol table is read from it;
                          kit = the directory that holds rvelf.py, sha256 23152d9ca11c (linear RISC-V decode of .text).

Facts (all measured from the two files, nothing assumed):
  sections    allocated sections (name, lo, hi, nobits) of the PIN's section headers
  loads       PT_LOAD segments (vaddr, filesz, memsz, flags) of the PIN's program headers
  hull        [lowest PT_LOAD page, highest PT_LOAD end rounded up to a page)
  funcs       FUNC symbols of the twin with size > 0: (lo, hi, name)
  objs        OBJECT / TLS symbols of the twin with size > 0
  insns       the instruction start addresses of .text by rvelf's linear decode
The twin's PT_LOAD headers are compared with the pin's when the object is made (`same_link`): the rules use the
pin's bytes with the twin's names only if the two links agree.
"""
import bisect
import hashlib
import struct
import sys

from elftools.elf.elffile import ELFFile

PAGE = 4096


def sha12(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()[:12]


class Img:
    def __init__(self, pin, twin, kit=None, decode=True):
        self.pin, self.twin = pin, twin
        self.pin_sha, self.twin_sha = sha12(pin), sha12(twin)
        self.data = open(pin, 'rb').read()
        e = ELFFile(open(pin, 'rb'))
        self.phnum, self.phentsize, self.phoff, self.entry = (e['e_phnum'], e['e_phentsize'], e['e_phoff'],
                                                             e['e_entry'])
        self.loads, self.tls, self.phdr = [], None, None
        for s in e.iter_segments():
            h = s.header
            if h.p_type == 'PT_LOAD':
                self.loads.append((h.p_vaddr, h.p_filesz, h.p_memsz, h.p_flags, h.p_offset))
            elif h.p_type == 'PT_TLS':
                self.tls = (h.p_vaddr, h.p_memsz)
            elif h.p_type == 'PT_PHDR':
                self.phdr = (h.p_vaddr, h.p_memsz)
        self.sections = []
        for s in e.iter_sections():
            if s['sh_addr'] and s['sh_size'] and (s['sh_flags'] & 2):
                self.sections.append((s['sh_addr'], s['sh_addr'] + s['sh_size'], s.name, s['sh_type'] == 'SHT_NOBITS',
                                      s['sh_flags']))
        self.sections.sort()
        lo = min(v for v, *_ in self.loads) & ~(PAGE - 1)
        hi = max(v + m for v, _, m, *_ in self.loads)
        self.hull = (lo, (hi + PAGE - 1) & ~(PAGE - 1))
        t = ELFFile(open(twin, 'rb'))
        tl = [(s.header.p_vaddr, s.header.p_filesz, s.header.p_memsz, s.header.p_flags, s.header.p_offset)
              for s in t.iter_segments() if s.header.p_type == 'PT_LOAD']
        self.same_link = tl == self.loads
        self.funcs, self.objs, self.syms = [], [], []
        for s in t.get_section_by_name('.symtab').iter_symbols():
            v, z, ty = s['st_value'], s['st_size'], s['st_info']['type']
            if not v or not s.name or s.name.startswith('$'):
                continue
            self.syms.append((v, z, ty, s.name))
            if z and ty == 'STT_FUNC':
                self.funcs.append((v, v + z, s.name))
            elif z and ty in ('STT_OBJECT', 'STT_TLS'):
                self.objs.append((v, v + z, s.name))
        self.funcs.sort()
        self.objs.sort()
        self.syms.sort()
        self.flo = [f[0] for f in self.funcs]
        self.olo = [o[0] for o in self.objs]
        self.byname = {}
        for v, z, ty, n in self.syms:
            self.byname.setdefault(n, []).append((v, z, ty))
        self.insns = None
        if decode and kit:
            sys.path.insert(0, kit)
            import rvelf  # noqa: E402
            tx = next(s for s in self.sections if s[2] == '.text')
            off = self.file_off(tx[0])
            self.code = rvelf.Code(self.data[off:off + tx[1] - tx[0]], tx[0])
            self.insns = set(self.code.pcs)

    # ---- raw reads -------------------------------------------------------------------------------------------
    def file_off(self, a):
        for v, fs, ms, fl, off in self.loads:
            if v <= a < v + fs:
                return off + a - v
        return None

    def word(self, a, n=8):
        """n little-endian bytes at a from the PIN; 0 for a NOBITS byte inside a PT_LOAD; None outside."""
        out = 0
        for i in range(n):
            o = self.file_off(a + i)
            if o is None:
                if not self.in_load(a + i):
                    return None
                b = 0
            else:
                b = self.data[o]
            out |= b << (8 * i)
        return out

    # ---- geometry --------------------------------------------------------------------------------------------
    def in_load(self, a):
        return any(v <= a < v + m for v, _, m, *_ in self.loads)

    def load_of(self, a, end_ok=False):
        for k, (v, fs, m, fl, off) in enumerate(self.loads):
            if v <= a < v + m or (end_ok and a == v + m):
                return k, v, m, fl
        return None

    def section_of(self, a, end_ok=False):
        for lo, hi, n, nb, fl in self.sections:
            if lo <= a < hi or (end_ok and a == hi):
                return n
        return None

    def func_of(self, a):
        k = bisect.bisect_right(self.flo, a) - 1
        while k >= 0:
            lo, hi, n = self.funcs[k]
            if lo <= a < hi:
                return lo, hi, n
            if self.funcs[k][0] < a - 0x100000:
                break
            k -= 1
        return None

    def obj_of(self, a):
        k = bisect.bisect_right(self.olo, a) - 1
        best = None
        while k >= 0 and k >= bisect.bisect_right(self.olo, a) - 64:
            lo, hi, n = self.objs[k]
            if lo <= a < hi and (best is None or hi - lo < best[1] - best[0]):
                best = (lo, hi, n)
            k -= 1
        return best

    def is_insn(self, a):
        return self.insns is not None and a in self.insns

    def resolve(self, a):
        """One short measured string for address a: section, and FUNC / OBJECT symbol + offset."""
        sec = self.section_of(a)
        parts = [sec or ('end of ' + self.section_of(a, True) if self.section_of(a, True) else 'no section')]
        f = self.func_of(a)
        if f:
            parts.append(f'{f[2]}+{a - f[0]:#x}' + (' insn' if self.is_insn(a) else ' NOT-insn'))
        o = self.obj_of(a)
        if o:
            parts.append(f'{o[2]}+{a - o[0]:#x}')
        return ' '.join(parts)

    def describe(self):
        return f'{self.pin_sha} (twin {self.twin_sha})'
