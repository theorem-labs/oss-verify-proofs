"""Image quantities of one build, read with pyelftools.

An Img is a stripped release image (the unit pin: program headers, section headers and bytes) plus its unstripped
twin (same link; its .symtab names the symbols).  Every quantity is read from those two files only.

Quantity expressions (used by recompute.py) are Python expressions over these names:
  seg(i)        i-th PT_LOAD (0..3): .lo .memsz .filesz .hi (lo+memsz) .fhi (lo+filesz) .pglo .pghi .align
  tls, relro    PT_TLS / PT_GNU_RELRO, same fields
  sec(NAME)     section header: .lo .size .hi
  sym(NAME, k)  k-th symbol of that name by address (default the only one): .addr .size .end
  top, base     image top (last PT_LOAD end rounded up to 4096) and image base (first PT_LOAD start rounded down)
  phnum, entry  ELF header e_phnum / e_entry
  q64(a), w32(a), u8(a)   little-endian 8 / 4 / 1 byte(s) of the loaded image at address a
  pg(x), pgdn(x)          x rounded up / down to 4096
  sym_at(a)     the symbol that starts at a (FUNC/OBJECT preferred), sym_cover(a) the smallest sized symbol covering a
"""
import bisect
import collections
import hashlib
import struct

from elftools.elf.elffile import ELFFile

PAGE = 0x1000


def pg(x):
    return (x + PAGE - 1) & ~(PAGE - 1)


def pgdn(x):
    return x & ~(PAGE - 1)


class Rng:
    def __init__(self, lo, memsz, filesz=None, align=None, name=''):
        self.lo, self.memsz = lo, memsz
        self.filesz = memsz if filesz is None else filesz
        self.align, self.name = align, name

    size = property(lambda s: s.memsz)
    hi = property(lambda s: s.lo + s.memsz)
    fhi = property(lambda s: s.lo + s.filesz)
    pglo = property(lambda s: pgdn(s.lo))
    pghi = property(lambda s: pg(s.lo + s.memsz))

    def __repr__(self):
        return f'Rng({self.name} {self.lo:#x}+{self.memsz:#x})'


class Sym:
    def __init__(self, name, addr, size, typ, bind):
        self.name, self.addr, self.size, self.typ, self.bind = name, addr, size, typ, bind

    end = property(lambda s: s.addr + s.size)

    def __repr__(self):
        return f'{self.name}@{self.addr:#x}+{self.size:#x}'


class Img:
    def __init__(self, pin, twin, role):
        self.role, self.pin, self.twin = role, pin, twin
        raw = open(pin, 'rb').read()
        self.sha = hashlib.sha256(raw).hexdigest()
        self.twin_sha = hashlib.sha256(open(twin, 'rb').read()).hexdigest()
        e = ELFFile(open(pin, 'rb'))
        self.phnum, self.entry, self.phentsize = e['e_phnum'], e['e_entry'], e['e_phentsize']
        self.loads, self.tls, self.relro, self.ehfh, self.phdr = [], None, None, None, None
        self._chunks = []
        for s in e.iter_segments():
            t = s['p_type']
            r = Rng(s['p_vaddr'], s['p_memsz'], s['p_filesz'], s['p_align'], t)
            if t == 'PT_LOAD':
                self.loads.append(r)
                self._chunks.append((s['p_vaddr'], s['p_vaddr'] + s['p_filesz'], raw[s['p_offset']:s['p_offset'] + s['p_filesz']]))
            elif t == 'PT_TLS':
                self.tls = r
            elif t == 'PT_GNU_RELRO':
                self.relro = r
            elif t == 'PT_GNU_EH_FRAME':
                self.ehfh = r
            elif t == 'PT_PHDR':
                self.phdr = r
        self.secs = {}
        for s in e.iter_sections():
            if s['sh_addr']:
                self.secs[s.name] = Rng(s['sh_addr'], s['sh_size'], name=s.name)
        self.top = max(pg(r.hi) for r in self.loads)
        self.base = min(pgdn(r.lo) for r in self.loads)
        te = ELFFile(open(twin, 'rb'))
        self.syms = []
        for s in te.get_section_by_name('.symtab').iter_symbols():
            if s['st_info']['type'] in ('STT_FILE', 'STT_SECTION') or not s.name or not s['st_value']:
                continue
            self.syms.append(Sym(s.name, s['st_value'], s['st_size'], s['st_info']['type'], s['st_info']['bind']))
        self.syms.sort(key=lambda x: (x.addr, -x.size))
        self.byname = collections.defaultdict(list)
        for s in self.syms:
            if not any(o.addr == s.addr and o.size == s.size for o in self.byname[s.name]):
                self.byname[s.name].append(s)
        self.symv = [s.addr for s in self.syms]

    # ---- expression environment
    def seg(self, i):
        return self.loads[i]

    def sec(self, name):
        return self.secs[name]

    def sym(self, name, k=None):
        hits = self.byname.get(name, [])
        if not hits:
            raise KeyError(f'no symbol {name} in {self.role}')
        if k is None:
            if len(hits) != 1:
                raise KeyError(f'{len(hits)} symbols named {name} in {self.role}: give k')
            return hits[0]
        return hits[k]

    def has(self, name):
        return bool(self.byname.get(name))

    def read(self, a, n):
        for lo, hi, b in self._chunks:
            if lo <= a and a + n <= hi:
                return b[a - lo:a - lo + n]
        for r in self.loads:
            if r.lo <= a and a + n <= r.hi:
                return bytes(n)            # .bss: zero-filled
        raise KeyError(f'{a:#x}+{n} not in a loaded segment of {self.role}')

    def q64(self, a):
        return struct.unpack('<Q', self.read(a, 8))[0]

    def w32(self, a):
        return struct.unpack('<I', self.read(a, 4))[0]

    def u8(self, a):
        return self.read(a, 1)[0]

    def sym_at(self, a):
        i = bisect.bisect_left(self.symv, a)
        best = None
        while i < len(self.syms) and self.syms[i].addr == a:
            s = self.syms[i]
            if best is None or (s.typ in ('STT_FUNC', 'STT_OBJECT') and best.typ not in ('STT_FUNC', 'STT_OBJECT')) \
                    or (s.typ == best.typ and s.size > best.size):
                best = s
            i += 1
        if best is None:
            raise KeyError(f'no symbol starts at {a:#x} in {self.role}')
        return best

    def sym_cover(self, a):
        i = bisect.bisect_right(self.symv, a)
        best = None
        for s in self.syms[max(0, i - 400):i]:
            if s.size and s.addr <= a < s.end and (best is None or s.size < best.size):
                best = s
        if best is None:
            raise KeyError(f'no sized symbol covers {a:#x} in {self.role}')
        return best

    def describe(self, a):
        try:
            s = self.sym_cover(a)
            return f'{s.name}+{a - s.addr:#x}'
        except KeyError:
            pass
        for n, r in self.secs.items():
            if r.lo <= a <= r.hi:
                return f'{n}+{a - r.lo:#x}'
        return 'outside'

    def cstr_at(self, a, n=512):
        """The NUL-terminated byte string that holds address a (its start and bytes), or None."""
        try:
            lo = max(self.base, a - n)
            b = self.read(lo, a - lo + 1)
        except KeyError:
            return None
        s = b.rfind(b'\0', 0, len(b) - 1 if b[-1:] == b'\0' else len(b))
        start = lo + s + 1
        try:
            tail = self.read(start, n)
        except KeyError:
            return None
        e = tail.find(b'\0')
        return (start, tail[:e]) if e >= 0 else None

    def find_cstr(self, bs):
        """Every start address of the NUL-terminated string bs in the read-only data (.rodata)."""
        r = self.secs.get('.rodata')
        if r is None:
            return []
        data = self.read(r.lo, r.size)
        out, i = [], data.find(bs + b'\0')
        while i >= 0:
            if i == 0 or data[i - 1] == 0:
                out.append(r.lo + i)
            i = data.find(bs + b'\0', i + 1)
        return out

    def strlen0(self, a):
        """Length of the NUL-terminated string that starts at a, its NUL included."""
        b = self.read(a, 4096 if a + 4096 <= self.top else 1)
        return b.index(b'\0') + 1

    def findbytes(self, bs):
        """Every address where the byte string bs stands in the file-backed part of a PT_LOAD."""
        out = []
        for lo, hi, b in self._chunks:
            i = b.find(bs)
            while i >= 0:
                out.append(lo + i)
                i = b.find(bs, i + 1)
        return out

    def frame(self, a, n=24):
        """Stack frame size a function opens at its start: minus the sum of the negative immediates of the
        `addi sp, sp, imm` instructions among its first n 4-byte words (the prologue)."""
        tot = 0
        for i in range(n):
            w = self.w32(a + 4 * i)
            if w & 0x7f == 0x13 and (w >> 7) & 31 == 2 and (w >> 12) & 7 == 0 and (w >> 15) & 31 == 2:
                imm = w >> 20
                imm = imm - 4096 if imm & 0x800 else imm
                if imm < 0:
                    tot -= imm
        return tot

    def aglobs(self):
        """[(beg, size, size_with_redzone)] of the __asan_global records of section asan_globals (64 bytes each)."""
        if getattr(self, '_aglobs', None) is None:
            r = self.secs.get('asan_globals')
            self._aglobs = [] if r is None else [(self.q64(r.lo + 64 * i), self.q64(r.lo + 64 * i + 8), self.q64(r.lo + 64 * i + 16))
                                                  for i in range(r.size // 64)]
        return self._aglobs

    def env(self):
        return dict(seg=self.seg, sec=self.sec, sym=self.sym, sym_at=self.sym_at, sym_cover=self.sym_cover,
                    tls=self.tls, relro=self.relro, ehfh=self.ehfh, phdr=self.phdr, top=self.top, base=self.base,
                    phnum=self.phnum, phentsize=self.phentsize, entry=self.entry, q64=self.q64, w32=self.w32,
                    u8=self.u8, pg=pg, pgdn=pgdn, has=self.has, nload=len(self.loads), img=self,
                    cstr=lambda bs: self.find_cstr(bs.encode() if isinstance(bs, str) else bs),
                    strlen0=self.strlen0, findbytes=self.findbytes, bytes=bytes, frame=self.frame, aglobs=self.aglobs())

    def eval(self, expr):
        g = self.env()
        g['__builtins__'] = {'len': len, 'sum': sum, 'min': min, 'max': max, 'abs': abs}
        return eval(expr, g)

    # ---- catalog of named quantities (for proposing which quantity a donor value is)
    def catalog(self):
        cat = collections.defaultdict(set)

        def add(name, v):
            if isinstance(v, int) and v > 0:
                cat[v].add(name)
        for i, r in enumerate(self.loads):
            for f in ('lo', 'memsz', 'filesz', 'hi', 'fhi', 'pglo', 'pghi'):
                add(f'seg({i}).{f}', getattr(r, f))
            add(f'seg({i}).pghi-seg({i}).pglo', r.pghi - r.pglo)
            add(f'pg(seg({i}).memsz)', pg(r.memsz))
        for nm in ('tls', 'relro', 'ehfh'):
            r = getattr(self, nm)
            for f in ('lo', 'memsz', 'filesz', 'hi', 'pglo', 'pghi'):
                add(f'{nm}.{f}', getattr(r, f))
        for n, r in self.secs.items():
            for f in ('lo', 'size', 'hi'):
                add(f"sec('{n}').{f}", getattr(r, f))
        add('top', self.top)
        add('base', self.base)
        add('top-base', self.top - self.base)
        add('phnum', self.phnum)
        for s in self.syms:
            if s.typ in ('STT_FUNC', 'STT_OBJECT', 'STT_TLS') and s.size:
                k = '' if len(self.byname[s.name]) == 1 else f', {self.byname[s.name].index(s)}' if s in self.byname[s.name] else None
                if k is None:
                    continue
                add(f"sym('{s.name}'{k}).size", s.size)
        return cat
