"""Symbol and byte reader for one unstripped ELF (pyelftools). No disassembly listing is printed by this module."""
import bisect
from elftools.elf.elffile import ELFFile


class Img:
    def __init__(self, path):
        self.path = path
        self.f = open(path, 'rb')
        self.e = ELFFile(self.f)
        self.data = open(path, 'rb').read()
        self.segs = [(s['p_vaddr'], s['p_filesz'], s['p_memsz'], s['p_offset'], s['p_flags'])
                     for s in self.e.iter_segments() if s['p_type'] == 'PT_LOAD']
        self.secs = [(s.name, s['sh_addr'], s['sh_size'], s['sh_type']) for s in self.e.iter_sections()
                     if s['sh_flags'] & 2]
        syms = []
        self.byname = {}
        for s in self.e.get_section_by_name('.symtab').iter_symbols():
            t = s['st_info']['type']
            if s.name and t in ('STT_FUNC', 'STT_OBJECT', 'STT_NOTYPE', 'STT_TLS') and s['st_shndx'] != 'SHN_UNDEF':
                syms.append((s['st_value'], s['st_size'], t, s['st_info']['bind'], s.name))
                self.byname.setdefault(s.name, []).append((s['st_value'], s['st_size'], t))
        syms.sort()
        self.syms = syms
        self.keys = [s[0] for s in syms]

    def sec(self, a):
        for n, b, sz, t in self.secs:
            if b <= a < b + sz:
                return n
        return None

    def sym_at(self, a):
        """the sized FUNC/OBJECT symbols containing a (preferring GLOBAL), else the nearest symbol below"""
        i = bisect.bisect_right(self.keys, a)
        cands = []
        j = i - 1
        while j >= 0 and j >= i - 400:
            v, sz, t, b, n = self.syms[j]
            if v <= a < v + max(sz, 1) and t in ('STT_FUNC', 'STT_OBJECT', 'STT_TLS'):
                cands.append((v, sz, t, b, n))
            j -= 1
        if cands:
            cands.sort(key=lambda c: (c[3] != 'STB_GLOBAL', c[3] != 'STB_WEAK', -c[0], c[4]))
            return cands
        return []

    def name(self, a):
        c = self.sym_at(a)
        if c:
            v, sz, t, b, n = c[0]
            return '%s+%#x' % (n, a - v)
        s = self.sec(a)
        return '<%s %#x>' % (s, a) if s else '<none %#x>' % a

    def read(self, a, n):
        for v, fsz, msz, off, fl in self.segs:
            if v <= a and a + n <= v + fsz:
                return self.data[off + a - v: off + a - v + n]
        return None

    def u(self, a, n):
        b = self.read(a, n)
        return None if b is None else int.from_bytes(b, 'little')

    def sym(self, name):
        return self.byname.get(name, [])
