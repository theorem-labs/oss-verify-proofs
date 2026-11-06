"""feq_lib.py -- image, RV64 decoder and proof-text helpers for the false-equal re-check of port_addr_check rows.

Independent of port_addr_check.py: it reads ELF bytes and symbols with pyelftools, decodes RISC-V words itself and
reads the proof files' own text. Nothing here imports the gate.
"""
import bisect, collections, hashlib, os, re
from elftools.elf.elffile import ELFFile


def sha12(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()[:12]


# ------------------------------------------------------------------------------------------------ images
class Img:
    """One pinned image (bytes from the PT_LOAD segments of the pin) named with the symbol table of its twin."""

    def __init__(self, role, pin, twin):
        self.role, self.pin, self.twin = role, pin, twin
        self.pin_sha, self.twin_sha = sha12(pin), sha12(twin)
        with open(pin, 'rb') as f:
            raw = f.read()
        e = ELFFile(open(pin, 'rb'))
        self.segs = []
        for s in e.iter_segments():
            if s['p_type'] == 'PT_LOAD':
                data = raw[s['p_offset']:s['p_offset'] + s['p_filesz']] + b'\0' * (s['p_memsz'] - s['p_filesz'])
                self.segs.append((s['p_vaddr'], s['p_vaddr'] + s['p_memsz'], s['p_flags'], data))
        self.lo = min(a for a, _, _, _ in self.segs)
        self.hi = max(b for _, b, _, _ in self.segs)
        t = ELFFile(open(twin, 'rb'))
        self.secs = [(x['sh_addr'], x['sh_addr'] + x['sh_size'], x.name) for x in t.iter_sections()
                     if x['sh_addr'] and x['sh_flags'] & 2]
        st = t.get_section_by_name('.symtab')
        syms = []
        for s in st.iter_symbols():
            ty = s['st_info']['type']
            if ty not in ('STT_FUNC', 'STT_OBJECT', 'STT_NOTYPE', 'STT_TLS') or not s.name:
                continue
            if s['st_shndx'] in ('SHN_UNDEF', 'SHN_ABS') or ty == 'STT_TLS':
                continue
            if s.name.startswith(('$x', '$d', '.L')):
                continue
            syms.append((s['st_value'], s['st_size'], s.name, ty, s['st_info']['bind']))
        syms.sort()
        self.syms = syms
        self.starts = [x[0] for x in syms]
        self.byname = collections.defaultdict(list)
        for v, sz, n, ty, b in syms:
            self.byname[n].append((v, sz))

    def exec_at(self, a):
        return any(lo <= a < hi and fl & 1 for lo, hi, fl, _ in self.segs)

    def read(self, a, n):
        for lo, hi, fl, data in self.segs:
            if lo <= a and a + n <= hi:
                return data[a - lo:a - lo + n]
        return None

    def word(self, a):
        b = self.read(a, 4)
        return None if b is None else int.from_bytes(b, 'little')

    def sec(self, a):
        for lo, hi, n in self.secs:
            if lo <= a < hi:
                return n
        return None

    def covering(self, a):
        """The most specific sized symbol that holds a: (start, size, name), else None."""
        i = bisect.bisect_right(self.starts, a)
        best = None
        j = i - 1
        while j >= 0 and j >= i - 4000:
            v, sz, n, ty, b = self.syms[j]
            if v <= a < v + sz and (best is None or sz < best[1] or (sz == best[1] and b == 'STB_GLOBAL')):
                best = (v, sz, n)
            j -= 1
        return best

    def where(self, a):
        """`name+0xoff` of the symbol that holds a; `name+0xoff (unsized)` by the nearest named start below; else
        `section: unnamed`."""
        c = self.covering(a)
        if c:
            return f'{c[2]}+{a - c[0]:#x}'
        i = bisect.bisect_right(self.starts, a) - 1
        sec = self.sec(a)
        while i >= 0:
            v, sz, n, ty, b = self.syms[i]
            if '$' in n:
                i -= 1
                continue
            if sz == 0 and self.sec(v) == sec:
                return f'{n}+{a - v:#x} (unsized label)'
            if v + sz <= a:
                break
            i -= 1
        return f'{sec or "no section"}: unnamed'

    def cstr(self, a, back=4096):
        """(start, bytes up to the NUL, offset of a) of the NUL-terminated string that holds a."""
        b = self.read(a, 1)
        if b is None:
            return None
        s = a
        while s > a - back and self.read(s - 1, 1) not in (None, b'\0'):
            s -= 1
        e = a
        while self.read(e, 1) not in (None, b'\0') and e < a + 4096:
            e += 1
        return s, self.read(s, e - s), a - s

    def find_all(self, pat, exec_only=True):
        out = []
        for lo, hi, fl, data in self.segs:
            if exec_only and not fl & 1:
                continue
            i = data.find(pat)
            while i >= 0:
                out.append(lo + i)
                i = data.find(pat, i + 1)
        return out

    def xrefs(self):
        """address -> [pc of the auipc / lui] for every auipc or lui whose rd is next used, within 8 words and
        before it is overwritten, as the base of an addi / load / store / jalr (the address the pair forms).
        Executable segments only (rv64g: every word 4-aligned). Memoised."""
        if getattr(self, '_xr', None) is not None:
            return self._xr
        xr = collections.defaultdict(list)
        for lo, hi, fl, data in self.segs:
            if not fl & 1:
                continue
            base = lo + (-lo % 4)
            n = (hi - base) // 4
            ws = [int.from_bytes(data[base - lo + 4 * i:base - lo + 4 * i + 4], 'little') for i in range(n)]
            for i, w in enumerate(ws):
                op = w & 0x7f
                if op not in (0x17, 0x37):
                    continue
                rd = (w >> 7) & 31
                if rd == 0:
                    continue
                a = base + 4 * i
                hi20 = imm_u(w) + (a if op == 0x17 else 0)
                for j in range(i + 1, min(n, i + 9)):
                    w2 = ws[j]
                    op2, rs1, rd2 = w2 & 0x7f, (w2 >> 15) & 31, (w2 >> 7) & 31
                    if rs1 == rd and op2 in (0x67, 0x13, 0x03, 0x07, 0x1b):
                        xr[(hi20 + imm_i(w2)) & ((1 << 64) - 1)].append(a)
                        if rd2 == rd:
                            break
                        continue
                    if rs1 == rd and op2 in (0x23, 0x27):
                        xr[(hi20 + imm_s(w2)) & ((1 << 64) - 1)].append(a)
                        continue
                    if op2 in (0x6f, 0x67, 0x63):      # control flow ends the window
                        break
                    if rd2 == rd and op2 not in (0x23, 0x27, 0x63):
                        break
        self._xr = xr
        return xr

    def label(self):
        return f'{os.path.basename(self.pin)} {self.pin_sha} (symbols: twin {self.twin_sha})'


# ------------------------------------------------------------------------------------------------ RV64 decoder
def sx(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >> (bits - 1) else v


def imm_i(w): return sx(w >> 20, 12)
def imm_s(w): return sx(((w >> 25) << 5) | ((w >> 7) & 31), 12)
def imm_u(w): return sx(w & 0xfffff000, 32)
def imm_j(w): return sx((((w >> 31) & 1) << 20) | (((w >> 12) & 0xff) << 12) | (((w >> 20) & 1) << 11) |
                        (((w >> 21) & 0x3ff) << 1), 21)
def imm_b(w): return sx((((w >> 31) & 1) << 12) | (((w >> 7) & 1) << 11) | (((w >> 25) & 0x3f) << 5) |
                        (((w >> 8) & 0xf) << 1), 13)


OPN = {0x03: 'load', 0x07: 'fload', 0x0f: 'fence', 0x13: 'opimm', 0x17: 'auipc', 0x1b: 'opimm32', 0x23: 'store',
       0x27: 'fstore', 0x2f: 'amo', 0x33: 'op', 0x37: 'lui', 0x3b: 'op32', 0x43: 'fmadd', 0x47: 'fmsub',
       0x4b: 'fnmsub', 0x4f: 'fnmadd', 0x53: 'opfp', 0x63: 'branch', 0x67: 'jalr', 0x6f: 'jal', 0x73: 'system'}
BR = {0: 'beq', 1: 'bne', 4: 'blt', 5: 'bge', 6: 'bltu', 7: 'bgeu'}


def decode(w):
    """(kind, text, rel) where rel is the pc-relative offset of a jal / branch / auipc, else None."""
    if w & 3 != 3:
        return 'not32', f'not a 32-bit encoding (low bits {w & 3:02b})', None
    op = w & 0x7f
    rd, f3, rs1, rs2 = (w >> 7) & 31, (w >> 12) & 7, (w >> 15) & 31, (w >> 20) & 31
    k = OPN.get(op, f'op{op:#x}')
    if op == 0x6f:
        return ('j' if rd == 0 else 'jal'), f'jal x{rd}, pc{imm_j(w):+#x}', imm_j(w)
    if op == 0x63:
        return 'branch', f'{BR.get(f3, "b?")} x{rs1}, x{rs2}, pc{imm_b(w):+#x}', imm_b(w)
    if op == 0x17:
        return 'auipc', f'auipc x{rd}, {imm_u(w) & 0xffffffff:#x}', imm_u(w)
    if op == 0x37:
        return 'lui', f'lui x{rd}, {(w >> 12) & 0xfffff:#x}', None
    if op == 0x67:
        return 'jalr', f'jalr x{rd}, {imm_i(w)}(x{rs1})', None
    if op == 0x13 and f3 == 0:
        return 'addi', f'addi x{rd}, x{rs1}, {imm_i(w)}', None
    if op in (0x03, 0x07):
        return k, f'{k} f3={f3} x{rd}, {imm_i(w)}(x{rs1})', None
    if op in (0x23, 0x27):
        return k, f'{k} f3={f3} x{rs2}, {imm_s(w)}(x{rs1})', None
    if op in (0x13, 0x1b):
        return k, f'{k} f3={f3} x{rd}, x{rs1}, {imm_i(w)}', None
    return k, f'{k} rd=x{rd} rs1=x{rs1} rs2=x{rs2} f3={f3}', None


def pair_target(img, pc, w):
    """The full target of an auipc at pc: pc + imm_u + the low part of the next word that uses its rd."""
    rd = (w >> 7) & 31
    w2 = img.word(pc + 4)
    if w2 is None:
        return None, None
    op2, rs1 = w2 & 0x7f, (w2 >> 15) & 31
    if rs1 != rd:
        return None, w2
    if op2 in (0x67, 0x13, 0x03, 0x07):
        return (pc + imm_u(w) + imm_i(w2)) & ((1 << 64) - 1), w2
    if op2 in (0x23, 0x27):
        return (pc + imm_u(w) + imm_s(w2)) & ((1 << 64) - 1), w2
    return None, w2


# ------------------------------------------------------------------------------------------------ proof text
COMMENT = re.compile(r'\(\*.*?\*\)', re.S)


def strip_comments(t):
    """Comments blanked to spaces, newlines kept, so line numbers survive (nested comments: innermost first)."""
    prev = None
    while prev != t:
        prev = t
        t = re.sub(r'\(\*(?:(?!\(\*|\*\)).)*?\*\)', lambda m: re.sub(r'[^\n]', ' ', m.group(0)), t, flags=re.S)
    return t


DEFKW = re.compile(r"(?<![\w'.])(?:Definition|Notation|Let)\s+([A-Za-z_][\w']*)\s*(?::(?!=)\s*([^:=.]{0,80}?))?\s*:=")
SENT_END = re.compile(r"\.(?=\s|$)")
REC = re.compile(r"(?:Definition|Let)\s+([A-Za-z_][\w']*)\s*(?::\s*\w+\s*)?:=\s*\{\|(.*?)\|\}\s*\.", re.S)
FROM_REQ = re.compile(r"(?<![\w.])From\s+([\w.]+)\s+Require\s+(?:Import\s+|Export\s+)?([\w.\s]+?)\.(?=\s|$)", re.S)


class Tree:
    """One lib folder of proof files: their definitions, records and Require graph."""

    def __init__(self, root, libpfx):
        self.root, self.libpfx = root, libpfx      # libpfx: the logical path of `root`, e.g. '...fuzz_command.lib'
        self.text, self.lines, self.defs, self.recs, self.reqs = {}, {}, {}, {}, {}
        for dp, dn, fn in os.walk(root):
            for f in fn:
                if f.endswith('.v'):
                    rel = os.path.relpath(os.path.join(dp, f), root)
                    self._load(rel)
        self.mod = collections.defaultdict(list)
        for rel in self.text:
            self.mod[(os.path.dirname(rel), os.path.basename(rel)[:-2])].append(rel)

    def override(self, rel, text):
        """Replace one file's text (a planted control copy); its own definitions are re-read."""
        self.recs.pop(rel, None)
        self._load(rel, text)

    def _load(self, rel, text=None):
        t = open(os.path.join(self.root, rel), encoding='utf-8', errors='replace').read() if text is None else text
        c = strip_comments(t)
        self.text[rel], self.lines[rel] = c, t.split('\n')
        d, reqs = {}, []
        for m in DEFKW.finditer(c):
            e = SENT_END.search(c, m.end(), m.end() + 6000)
            if e and m.group(1) not in d:
                d[m.group(1)] = c[m.end():e.start()].strip()
        for m in FROM_REQ.finditer(c):
            reqs.append((m.group(1), m.group(2).split()))
        for m in REC.finditer(c):
            fl = {}
            for part in m.group(2).split(';'):
                if ':=' in part:
                    k, v = part.split(':=', 1)
                    fl[k.strip()] = v.strip()
            self.recs.setdefault(rel, {})[m.group(1)] = fl
        self.defs[rel], self.reqs[rel] = d, reqs

    def req_files(self, rel):
        out = []
        for pfx, mods in self.reqs.get(rel, ()):
            if not pfx.startswith(self.libpfx):
                continue
            sub = pfx[len(self.libpfx):].lstrip('.').replace('.', '/')
            for m in mods:
                out += self.mod.get((sub, m), [])
        return out

    def closure(self, rel):
        """Files reachable through Require, nearest first (BFS); memoised."""
        memo = self.__dict__.setdefault('_clo', {})
        if rel in memo:
            return memo[rel]
        seen, order, q = {rel}, [], collections.deque([rel])
        while q:
            x = q.popleft()
            for y in self.req_files(x):
                if y not in seen:
                    seen.add(y)
                    order.append(y)
                    q.append(y)
        memo[rel] = order
        return order

    def lookup(self, rel, name):
        """(rhs, file) of the nearest definition of name seen from rel."""
        if '.' in name:
            mod, n = name.rsplit('.', 1)
            mod = mod.split('.')[-1]
            for f in [rel] + self.closure(rel):
                if os.path.basename(f)[:-2] == mod and n in self.defs[f]:
                    return self.defs[f][n], f
            name = n
        for f in [rel] + self.closure(rel):
            if name in self.defs[f]:
                return self.defs[f][name], f
        return None, None

    def record_field(self, rel, field, rec):
        for f in [rel] + self.closure(rel):
            if rec in self.recs.get(f, {}) and field in self.recs[f][rec]:
                return self.recs[f][rec][field], f
        return None, None


NUM = re.compile(r'0x[0-9a-fA-F]+|\d+')


def num(s):
    return int(s, 16) if s.lower().startswith('0x') else int(s)


def eval_expr(tree, rel, e, depth=0):
    """The integer value of a pc / address expression, or None."""
    if depth > 12 or e is None:
        return None
    e = e.strip()
    e = re.sub(r'%(?:bv|Z|N)\b', ' ', e)
    e = re.sub(r':\s*(?:word|Z|N|bv\s*\d+)\s*$', '', e).strip()
    e = re.sub(r'^Z_to_bv\s+\d+\s*', '', e).strip()
    e = re.sub(r'^Z\.of_N\s*', '', e).strip()
    while e.startswith('(') and _close(e) == len(e) - 1:
        e = e[1:-1].strip()
        e = re.sub(r':\s*(?:word|Z|N|bv\s*\d+)\s*$', '', e).strip()
        e = re.sub(r'^Z_to_bv\s+\d+\s*', '', e).strip()
    toks = re.findall(r"\(|\)|[+-]|0x[0-9a-fA-F]+|\d+|[A-Za-z_][\w'.]*", e)
    if not toks:
        return None
    total, sign, i = 0, 1, 0
    expect_term = True
    while i < len(toks):
        t = toks[i]
        if t in '+-' and not expect_term:
            sign = 1 if t == '+' else -1
            expect_term = True
            i += 1
            continue
        if not expect_term:
            return None
        if t == '(':
            d, j = 0, i
            while j < len(toks):
                d += toks[j] == '('
                d -= toks[j] == ')'
                if d == 0:
                    break
                j += 1
            v = eval_expr(tree, rel, ' '.join(toks[i + 1:j]), depth + 1)
            i = j + 1
        elif NUM.fullmatch(t):
            v = num(t)
            i += 1
        else:
            # FIELD REC application, or a name
            if i + 1 < len(toks) and re.fullmatch(r"[A-Za-z_][\w'.]*", toks[i + 1]):
                rhs, _ = tree.record_field(rel, t, toks[i + 1].split('.')[-1])
                v = eval_expr(tree, rel, rhs, depth + 1) if rhs is not None else None
                i += 2
            else:
                rhs, f = tree.lookup(rel, t)
                v = eval_expr(tree, f, rhs, depth + 1) if rhs is not None else None
                i += 1
        if v is None:
            return None
        total += sign * v
        expect_term = False
    return total


def _close(s, i=0):
    d = 0
    for k in range(i, len(s)):
        if s[k] == '(':
            d += 1
        elif s[k] == ')':
            d -= 1
            if d == 0:
                return k
    return -1


def group_at(s, i):
    """Text inside the parentheses that open at s[i] (after blanks), and the index after ')'."""
    j = i
    while j < len(s) and s[j] in ' \t\n':
        j += 1
    if j >= len(s) or s[j] != '(':
        return None, i
    k = _close(s, j)
    if k < 0:
        return None, i
    return s[j + 1:k], k + 1


FETCH = re.compile(r"fetch_word\s+([\w.']+)\s*")
SOME = re.compile(r"\s*=\s*Some\s*")


def fetch_facts(text):
    """[(segs, pc_expr, rhs, offset of `fetch_word`, offset of the word)] for every `fetch_word SEGS (PC) = Some X`
    in text; rhs is an int literal or a name."""
    out = []
    for m in FETCH.finditer(text):
        expr, end = group_at(text, m.end())
        if expr is None:
            # bare pc name: fetch_word segs PC = Some ..
            mm = re.match(r"([A-Za-z_][\w'.]*)", text[m.end():m.end() + 200])
            if not mm:
                continue
            expr, end = mm.group(1), m.end() + mm.end()
        ms = SOME.match(text, end)
        if not ms:
            continue
        j = ms.end()
        inner, e2 = group_at(text, j)
        if inner is None:
            mm = re.match(r"([A-Za-z_][\w'.]*|0x[0-9a-fA-F]+|\d+)", text[j:j + 200])
            if not mm:
                continue
            inner = mm.group(1)
        t = re.sub(r"%bv|:\s*bv\s*32|:\s*word", ' ', inner).strip()
        t = re.sub(r'^Z_to_bv\s+32\s+', '', t).strip()
        if NUM.fullmatch(t):
            rhs = num(t)
        elif re.fullmatch(r"[A-Za-z_][\w'.]*", t):
            rhs = t.rstrip('.')
        else:
            continue
        out.append((m.group(1), expr, rhs, m.start(), j))
    return out
