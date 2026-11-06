#!/usr/bin/env python3
"""Image measurements used by the gen-cells rules: section and segment headers, file bytes, the symbol table of the
unstripped twin, and the registered-global descriptors of the asan_globals section.

Every number a rule compares with comes from here, read with pyelftools from the pinned image (bytes, headers)
and its twin (symbol table; the twin is the same link, so its addresses are the pin's).  Nothing is taken from a
generator or from a proof file."""
import bisect
import hashlib
from elftools.elf.elffile import ELFFile

SHADOW_OFF = 0x7FFF8000
PAGE = 0x1000
F9 = 0xF9  # kAsanGlobalRedzoneMagic


def sha12(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()[:12]


class Img:
    def __init__(self, pin, twin, role=''):
        self.role = role
        self.pin, self.twin = pin, twin
        self.sha_pin, self.sha_twin = sha12(pin), sha12(twin)
        self.data = open(pin, 'rb').read()
        with open(pin, 'rb') as f:
            e = ELFFile(f)
            self.secs = []
            for s in e.iter_sections():
                if s['sh_addr'] and s['sh_flags'] & 2:  # SHF_ALLOC
                    self.secs.append((s.name, s['sh_addr'], s['sh_addr'] + s['sh_size'], s['sh_type'],
                                      s['sh_offset']))
            self.secs.sort(key=lambda x: x[1])
            self.loads = [(p['p_vaddr'], p['p_filesz'], p['p_memsz'], p['p_offset'], p['p_flags'])
                          for p in e.iter_segments() if p['p_type'] == 'PT_LOAD']
            self.relro = [(p['p_vaddr'], p['p_memsz']) for p in e.iter_segments() if p['p_type'] == 'PT_GNU_RELRO']
            self.tls = [(p['p_vaddr'], p['p_memsz']) for p in e.iter_segments() if p['p_type'] == 'PT_TLS']
            self.tls_hdr = [(p['p_filesz'], p['p_memsz'], p['p_align']) for p in e.iter_segments()
                            if p['p_type'] == 'PT_TLS']
        syms = set()
        with open(twin, 'rb') as f:
            st = ELFFile(f).get_section_by_name('.symtab')
            for s in st.iter_symbols():
                t = s['st_info']['type']
                if s.name and s['st_value'] and t in ('STT_OBJECT', 'STT_FUNC', 'STT_NOTYPE'):
                    syms.add((s['st_value'], s['st_size'], t, s.name))
        self.syms = sorted(syms)
        self.sized = [x for x in self.syms if x[1] > 0 and x[2] in ('STT_OBJECT', 'STT_FUNC')]
        self.by_name = {}
        for v, sz, t, n in self.syms:
            self.by_name.setdefault(n, []).append((v, sz, t))
        self.starts = {}
        for v, sz, t, n in self.sized:
            self.starts.setdefault(v, []).append((sz, t, n))
        self._sv = [x[0] for x in self.sized]
        self._pmax, m = [], 0
        for v, sz, t, n in self.sized:
            m = max(m, v + sz)
            self._pmax.append(m)
        self.hull = (min(l[0] for l in self.loads) // PAGE * PAGE,
                     -(-max(l[0] + l[2] for l in self.loads) // PAGE) * PAGE)

    # ---- headers ---------------------------------------------------------------------------------------------
    def sec(self, a):
        for s in self.secs:
            if s[1] <= a < s[2]:
                return s
        return None

    def secname(self, a):
        s = self.sec(a)
        return s[0] if s else 'no-section'

    def section(self, name):
        for s in self.secs:
            if s[0] == name:
                return s
        raise KeyError(name)

    def load_of(self, a):
        for l in self.loads:
            if l[0] <= a < l[0] + l[2]:
                return l
        return None

    def filebacked(self, a, n=1):
        """[a, a+n) lies in the file bytes of one PT_LOAD and in a section that has file bytes."""
        l = self.load_of(a)
        if not l or a + n > l[0] + l[1]:
            return False
        s = self.sec(a)
        return bool(s) and s[3] != 'SHT_NOBITS' and a + n <= s[2]

    def nobits(self, a):
        s = self.sec(a)
        return bool(s) and s[3] == 'SHT_NOBITS'

    def read(self, a, n):
        l = self.load_of(a)
        if not l or a + n > l[0] + l[1]:
            return None
        o = l[3] + (a - l[0])
        return self.data[o:o + n]

    def word(self, a, n=8):
        b = self.read(a, n)
        return None if b is None else int.from_bytes(b, 'little')

    def cstr(self, a, n=200):
        b = self.read(a, n)
        if b is None:
            return None
        i = b.find(b'\0')
        return b[:i] if i >= 0 else b

    def rom(self):
        """page-rounded read-only PT_LOADs (no PF_W)."""
        out = []
        for v, fs, ms, off, fl in self.loads:
            if fl & 2:
                continue
            out.append((v // PAGE * PAGE, -(-(v + ms) // PAGE) * PAGE))
        return out

    def page_loads(self):
        return sorted((v // PAGE * PAGE, -(-(v + ms) // PAGE) * PAGE) for v, fs, ms, off, fl in self.loads)

    # ---- symbols ---------------------------------------------------------------------------------------------
    def sym_at(self, a):
        """smallest sized OBJECT/FUNC symbol of the twin containing a: (value, size, type, name) or None."""
        j = bisect.bisect_right(self._sv, a) - 1
        best = None
        while j >= 0 and self._pmax[j] > a:
            v, sz, t, n = self.sized[j]
            if v <= a < v + sz and (best is None or sz < best[1]):
                best = self.sized[j]
            j -= 1
        return best

    def sym_exact(self, a):
        return self.starts.get(a, [])

    def ident(self, a):
        """the identity of an address, comparable across images: 'name+off' of the smallest containing sized
        symbol; for a string literal (.str*) its bytes; else 'section+off'."""
        s = self.sym_at(a)
        if s:
            v, sz, t, n = s
            if n.startswith('.str') or n.startswith('.L.str'):
                return f'str:{self.cstr(v)!r}+{a - v:#x}'
            return f'{n}+{a - v:#x}'
        sc = self.sec(a)
        if sc:
            return f'{sc[0]}+{a - sc[1]:#x}(unnamed)'
        return f'none:{a:#x}'

    def name(self, a):
        s = self.sym_at(a)
        if s:
            return f'{s[3]}+{a - s[0]:#x}'
        return f'{self.secname(a)}+{a - self.sec(a)[1]:#x}' if self.sec(a) else f'{a:#x}'

    def got_ident(self, a):
        """for a .got word: the identity of the address it holds."""
        v = self.word(a - a % 8, 8)
        if v is None:
            return None
        return 'GOT->' + self.ident(v) if v else 'GOT->0'

    # ---- registered globals ----------------------------------------------------------------------------------
    def descriptors(self):
        lo, hi = self.section('asan_globals')[1:3]
        out = []
        for d in range(lo, hi, 64):
            out.append((d, [self.word(d + 8 * k, 8) for k in range(8)]))
        return out

    # ---- code references ---------------------------------------------------------------------------------
    def xrefs(self):
        """{target: [(function name, offset of the auipc, opcode, funct3)]} for every auipc rd + lo12 (addi/load/
        store/jalr on rd) pair of .text, by a linear sweep (RISC-V: 2-byte compressed or 4-byte instructions)."""
        if hasattr(self, '_xr'):
            return self._xr
        lo, hi = self.section('.text')[1:3]
        code = self.read(lo, hi - lo)
        out = {}
        n = len(code)
        pcs = []
        i = 0
        while i + 2 <= n:
            h = code[i] | (code[i + 1] << 8)
            if h & 3 == 3:
                if i + 4 > n:
                    break
                pcs.append((i, int.from_bytes(code[i:i + 4], 'little'), 4))
                i += 4
            else:
                pcs.append((i, h, 2))
                i += 2
        for k, (off, w, ln) in enumerate(pcs):
            if ln != 4 or w & 0x7F != 0x17:
                continue
            rd = (w >> 7) & 31
            if rd == 0:
                continue
            pc = lo + off
            base = pc + _sx(w & 0xFFFFF000, 32)
            for off2, w2, ln2 in pcs[k + 1:k + 9]:
                if ln2 != 4:
                    continue
                op = w2 & 0x7F
                rs1 = (w2 >> 15) & 31
                if op in (0x03, 0x07, 0x13, 0x67) and rs1 == rd and (op != 0x13 or (w2 >> 12) & 7 == 0):
                    t = base + _sx(w2 >> 20, 12)
                elif op in (0x23, 0x27) and rs1 == rd:
                    t = base + _sx(((w2 >> 25) << 5) | ((w2 >> 7) & 31), 12)
                else:
                    if op not in (0x23, 0x27, 0x63) and (w2 >> 7) & 31 == rd:
                        break
                    continue
                f = self.sym_at(pc)
                out.setdefault(t, []).append((f[3] if f else '?', pc - f[0] if f else pc, op, (w2 >> 12) & 7))
                break
        self._xr = out
        return out

    def xref_names(self, t):
        return sorted(set(x[0] for x in self.xrefs().get(t, [])))

    def load_widths(self, t):
        """the access widths (bytes) of the loads that read t through an auipc pair."""
        wid = {0: 1, 1: 2, 2: 4, 3: 8, 4: 1, 5: 2, 6: 4}
        return sorted(set(wid[x[3]] for x in self.xrefs().get(t, []) if x[2] in (0x03, 0x07) and x[3] in wid))

    def field_reads(self, obj):
        """{offset: [(function, pc, width)]}: the loads `l{b,h,w,d}[u] rd, off(rs)` of .text whose base register rs
        holds the address obj, by a forward scan of each function: rs gets obj from an auipc pair that forms obj
        (addi) or loads it from a .got word that holds obj (ld), and keeps it through register moves (addi rd, rs, 0;
        c.mv); any other write to the register, and every call (caller-saved registers), drops it."""
        lo, hi = self.section('.text')[1:3]
        code = self.read(lo, hi - lo)
        gotw = {a for a in range(self.section('.got')[1], self.section('.got')[2], 8) if self.word(a) == obj}
        wid = {0: 1, 1: 2, 2: 4, 3: 8, 4: 1, 5: 2, 6: 4}
        clob = set(range(5, 8)) | set(range(10, 18)) | set(range(28, 32)) | {1}
        out = {}
        i, n = 0, len(code)
        have, hi20 = set(), {}
        fn_end = 0
        while i + 2 <= n:
            pc = lo + i
            if pc >= fn_end:
                f = self.sym_at(pc)
                have, hi20 = set(), {}
                fn_end = f[0] + f[1] if f else pc + 2
                fname = f[3] if f else '?'
            hw = code[i] | (code[i + 1] << 8)
            if hw & 3 != 3:                                  # compressed
                if hw >> 12 == 0b1000 and (hw >> 2) & 31 and hw & 3 == 2:      # c.mv rd, rs2
                    rd, rs = (hw >> 7) & 31, (hw >> 2) & 31
                    have.discard(rd)
                    if rs in have:
                        have.add(rd)
                elif hw & 3 == 2 and hw >> 12 == 0b1001 and not (hw >> 2) & 31:  # c.jalr / c.ebreak
                    have -= clob
                else:
                    rd = (hw >> 7) & 31
                    if hw & 3 in (1, 2):                     # most C1/C2 forms write rd/rs1 (bits 11:7)
                        have.discard(rd)
                    else:                                    # C0 loads write rd' (bits 4:2)
                        have.discard(8 + ((hw >> 2) & 7))
                i += 2
                continue
            w = int.from_bytes(code[i:i + 4], 'little')
            op, rd, f3, rs1 = w & 0x7F, (w >> 7) & 31, (w >> 12) & 7, (w >> 15) & 31
            imm = _sx(w >> 20, 12)
            if op == 0x17:
                hi20[rd] = pc + _sx(w & 0xFFFFF000, 32)
                have.discard(rd)
            elif op == 0x13 and f3 == 0 and rs1 in hi20 and hi20[rs1] + imm == obj:
                have.add(rd)
                hi20.pop(rd, None)
            elif op == 0x03 and f3 == 3 and rs1 in hi20 and hi20[rs1] + imm in gotw:
                have.add(rd)
                hi20.pop(rd, None)
            elif op == 0x13 and f3 == 0 and imm == 0 and rs1 in have:
                have.add(rd)
            elif op == 0x03 and rs1 in have and f3 in wid:
                out.setdefault(imm, []).append((fname, pc, wid[f3]))
                have.discard(rd)
                hi20.pop(rd, None)
            elif op in (0x6F, 0x67):
                have -= clob
                have.discard(rd)
            elif op not in (0x23, 0x27, 0x63):
                have.discard(rd)
                if rd in hi20 and op != 0x17:
                    hi20.pop(rd, None)
            i += 4
        return out

    # ---- identities comparable across two images ---------------------------------------------------------
    def ident_set(self, a, w=1, depth=0):
        """names of the thing at address a, comparable with another image's: the smallest containing sized symbol
        (+offset; a string literal by its bytes), a section start or end at a, for a .got word the identities of the
        address it holds, for an unnamed .rodata address its bytes and the functions that form it, or its place in
        a jump table (the function that forms the table base and the entry offset)."""
        out = set()
        s = self.sym_at(a)
        if s:
            v, sz, t, n = s
            if n.startswith('.str') or n.startswith('.L.str'):
                out.add(f'str:{self.cstr(v)!r}+{a - v:#x}')
            else:
                out.add(f'sym:{n}+{a - v:#x}')
        sc0 = self.sec(a)
        if not s and sc0 and sc0[0] not in ('.rodata', '.got'):
            # padding after an object: the nearest sized symbol that starts before a, in the same section
            j = bisect.bisect_right(self._sv, a) - 1
            if j >= 0 and self._sv[j] >= sc0[1]:
                v, sz, t, n = self.sized[j]
                out.add(f'after:{n}+{a - v:#x}')
        for sc in self.secs:
            if a == sc[1]:
                out.add(f'secstart:{sc[0]}')
            if a == sc[2]:
                out.add(f'secend:{sc[0]}')
        sc = self.sec(a)
        if sc and sc[0] == '.got' and depth < 2:
            base = a - (a - sc[1]) % 8
            tv = self.word(base, 8)
            if tv is not None and self.hull[0] <= tv < self.hull[1] and \
                    (self.sec(tv) or any(tv == s[2] for s in self.secs)):
                for x in self.ident_set(tv, 1, 2):
                    out.add(f'got->{x}@{a - base}')
            elif tv is not None:
                # a GOT word that holds a number (a TLS offset, a module id): the number and the functions that
                # load it; unreferenced: the number and the names of the neighbouring GOT words
                xr = self.xref_names(base)
                for fn in xr:
                    out.add(f'gotval:{tv:#x}:{fn}@{a - base}')
                if not xr and depth == 0:
                    for nb, tag in ((base - 8, 'prev'), (base + 8, 'next')):
                        if self.sec(nb) and self.sec(nb)[0] == '.got':
                            for x in self.ident_set(nb, 1, 1):
                                out.add(f'gotval:{tv:#x}:{tag}={x}@{a - base}')
        if sc and sc[0] == '.rodata' and not s:
            b = self.read(a, w)
            xr = self.xref_names(a)
            if xr and b is not None:
                out.add(f'ro:{b.hex()}:{",".join(xr)}')
            jt = self.jt_place(a)
            if jt:
                out.add(jt)
        return out

    def jt_place(self, a):
        """'jt:F:+off' when a lies within 0x400 above a .rodata address that function F forms (a table base)."""
        if not hasattr(self, '_rots'):
            self._rots = sorted(t for t in self.xrefs() if self.secname(t) == '.rodata')
        j = bisect.bisect_right(self._rots, a) - 1
        if j < 0 or a - self._rots[j] > 0x400 or a == self._rots[j]:
            return None
        t = self._rots[j]
        return f'jt:{",".join(self.xref_names(t))}:+{a - t:#x}'

    def end_ident_set(self, e):
        """names of an END address e (exclusive): symbols that end at e, sections that end at e, and the identity
        of the last byte e-1 marked '+1'."""
        out = {f'end:{n}' for v, sz, t, n in self.sized if v + sz == e and not n.startswith('.str')}
        out |= {f'secend:{sc[0]}' for sc in self.secs if sc[2] == e}
        out |= {f'last:{x}' for x in self.ident_set(e - 1)}
        out |= {f'before:{n}' for sz, t, n in self.sym_exact(e) if not n.startswith('.str')}
        return out


def _sx(v, b):
    v &= (1 << b) - 1
    return v - (1 << b) if v & (1 << (b - 1)) else v
