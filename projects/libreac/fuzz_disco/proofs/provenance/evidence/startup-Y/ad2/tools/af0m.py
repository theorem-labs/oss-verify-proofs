"""af0m.py (startup-Y evidence copy): the three definitions hsform.py imports (Mem, state_bytes, descriptors), cut
VERBATIM from the start-up generator's af0m.py sha256 2ac2dbe25a9a, lines 34-44, 47-84 and 87-94. The rest of af0m.py (the
runtime-state table assembler) is not used by hsform.py, gen_ad2.py, gen_ad1k.py or check4.py and is not shipped here."""
import re, struct
from elftools.elf.elffile import ELFFile


class Mem:
    def __init__(self, image):
        e = ELFFile(open(image, 'rb'))
        self.segs = [(s['p_vaddr'], s['p_filesz'], s['p_memsz'], s.data()) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
        self.e = e

    def byte(self, a):
        for va, fs, ms, d in self.segs:
            if va <= a < va + ms:
                return d[a - va] if a - va < fs else 0
        return None


def state_bytes(kn, mem):
    known, imgr = {}, []
    for x in kn:
        m = re.match(r'KWord \{\| a_base := ELit 0; a_off := (\d+) \|\} (\d+) \(ELit (-?\d+)\)$', x)
        if m:
            a, w, v = int(m.group(1)), int(m.group(2)), int(m.group(3)) % (1 << 64)
            for i in range(w):
                known.setdefault(a + i, (v >> (8 * i)) & 0xff)
            continue
        m = re.match(r'KFill \{\| a_base := ELit 0; a_off := (\d+) \|\} \(ELit (\d+)\) (\d+)$', x)
        if m:
            a, n, b = int(m.group(1)), int(m.group(2)), int(m.group(3))
            for i in range(n):
                known.setdefault(a + i, b)
            continue
        m = re.match(r'KZero \{\| a_base := ELit 0; a_off := (\d+) \|\} \(ELit (\d+)\)$', x)
        if m:
            a, n = int(m.group(1)), int(m.group(2))
            (imgr.append(('zero', a, a + n)) if n >= 1 << 24 else [known.setdefault(a + i, 0) for i in range(n)])
            continue
        m = re.match(r'KImg (\d+) (\d+)$', x)
        if m:
            imgr.append(('img', int(m.group(1)), int(m.group(2))))

    def read(a, w):
        v = 0
        for i in range(w):
            b = known.get(a + i)
            if b is None:
                for k, lo, hi in imgr:
                    if lo <= a + i < hi:
                        b = 0 if k == 'zero' else mem.byte(a + i)
                        break
            if b is None:
                return None
            v |= b << (8 * i)
        return v
    return read


def descriptors(image):
    e = ELFFile(open(image, 'rb'))
    s = e.get_section_by_name('asan_globals')
    if s is None:
        return 0, 0, []
    d = s.data()
    out = [struct.unpack_from('<8Q', d, 64 * i) for i in range(len(d) // 64)]
    return s['sh_addr'], len(d), out
