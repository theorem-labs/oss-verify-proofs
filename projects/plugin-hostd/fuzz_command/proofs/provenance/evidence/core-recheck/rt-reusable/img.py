"""Read-only queries on an ELF image (pin) with the symbol table of its unstripped twin (pyelftools)."""
import bisect, hashlib
from elftools.elf.elffile import ELFFile


class Img:
    def __init__(self, pin, twin=None, role=''):
        self.role = role
        self.pin, self.twin = pin, twin or pin
        self.sha = hashlib.sha256(open(pin, 'rb').read()).hexdigest()[:12]
        self.twin_sha = hashlib.sha256(open(self.twin, 'rb').read()).hexdigest()[:12]
        with open(pin, 'rb') as f:
            e = ELFFile(f)
            self.ehdr = dict(e.header)
            self.loads = []
            for s in e.iter_segments():
                if s['p_type'] == 'PT_LOAD':
                    self.loads.append((s['p_vaddr'], s['p_vaddr'] + s['p_memsz'], s['p_vaddr'] + s['p_filesz'],
                                       s['p_flags'], s.data()))
            self.phdrs = [(s['p_type'], s['p_vaddr'], s['p_memsz']) for s in e.iter_segments()]
        with open(self.twin, 'rb') as f:
            e = ELFFile(f)
            self.secs = {s.name: (s['sh_addr'], s['sh_addr'] + s['sh_size']) for s in e.iter_sections() if s['sh_addr']}
            self.syms = {}
            rows = []
            st = e.get_section_by_name('.symtab')
            for s in (st.iter_symbols() if st else []):
                v, sz, ty = s['st_value'], s['st_size'], s['st_info']['type']
                if v and ty in ('STT_FUNC', 'STT_OBJECT', 'STT_NOTYPE', 'STT_TLS') and s.name:
                    self.syms.setdefault(s.name, []).append((v, sz, ty))
                    if ty != 'STT_TLS':
                        rows.append((v, sz, s.name, ty))
        rows.sort()
        self._rows = rows
        self._starts = [r[0] for r in rows]
        self.base = min(l[0] for l in self.loads)
        self.top = max(l[1] for l in self.loads)

    def phdr_vaddr(self):
        """vaddr of the program header table: the PT_LOAD at file offset 0 plus e_phoff"""
        return self.base + self.ehdr['e_phoff']

    def read(self, a, n):
        for lo, hi, fhi, _, data in self.loads:
            if lo <= a and a + n <= hi:
                out = bytearray()
                for x in range(a, a + n):
                    out.append(data[x - lo] if x < fhi else 0)
                return bytes(out)
        return None

    def word(self, a, n=8):
        b = self.read(a, n)
        return None if b is None else int.from_bytes(b, 'little')

    def sym_at(self, a):
        """(name, offset, size, type) of the sized symbol covering a (largest start <= a with a < start+size);
        else the symbol starting exactly at a; else None"""
        i = bisect.bisect_right(self._starts, a) - 1
        best = None
        while i >= 0 and self._rows[i][0] > a - 0x100000:
            v, sz, name, ty = self._rows[i]
            if v == a and best is None:
                best = (name, 0, sz, ty)
            if sz and v <= a < v + sz:
                return (name, a - v, sz, ty)
            if v < a - 0x10000:
                break
            i -= 1
        return best

    def starts_at(self, a):
        return [(r[2], r[1], r[3]) for r in self._rows[bisect.bisect_left(self._starts, a):
                                                      bisect.bisect_right(self._starts, a)]]

    def sec_of(self, a):
        for n, (lo, hi) in self.secs.items():
            if lo <= a < hi:
                return n
        return None

    def label(self, a):
        s = self.sym_at(a)
        return f'{s[0]}+{s[1]:#x}' if s else (self.sec_of(a) or 'none')
