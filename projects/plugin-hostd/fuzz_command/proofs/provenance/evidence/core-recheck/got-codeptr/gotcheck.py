#!/usr/bin/env python3
"""gotcheck.py - check every numeral of a proof tree that lies inside its image's .got, by the GOT word itself.

Why: the pin-keyed value gate port_addr_check 3d2eee813cce does not catch a .got cell moved to the 16-aligned
neighbour word (planted control: lib/A/ACeg.v:21 A_GOT_uar 0xa6448 -> 0xa6450 is judged SAME-SYMBOL-ROUNDED).
This tool reads the 8-byte GOT word at the numeral's address and names what it points at, then checks:

  (a) DONOR   the paired gate row (same dst file:line, same value; k-th occurrence on the line = k-th row) gives the
              donor numeral; the donor's GOT word, read in the donor image, must name the SAME pointee.
  (b) NAME    where the enclosing definition's name names a symbol (GOT_x, got_x, D_GOT_x, D_x_musl, real_x, ...),
              the pointee must carry that name (substring, or an alias listed in ALIASES with its reason).
  (c) STATED  where the text states the word next to the address (lit8 V W, val_mem .. V 8 W, (V, 8, [(0, 8%N, W)]),
              (ANum V) W, CVal 8 (SLit W), [V] = W, V -> W, ...), the stated W must equal the image word.
  (d) TWIN    the other image's twin file (lib/B/Yxxx.v <-> lib/A/Axxx.v, lib/B/Rt/X.v <-> lib/A/Rt/X.v), at the same
              line with the same text up to numerals: the twin numeral's GOT word must name the same pointee.

Pointee of a GOT word: the twin's .symtab (FUNC / OBJECT / NOTYPE, aliases at one address all kept, compared as a
set) when the word lies inside a named symbol; otherwise (zero, small constants, TLS offsets) the word VALUE plus its
place: the nearest earlier GOT word that names a symbol and the distance in words. GOT[0] (the word at .got start)
is named GOT[0] (lld writes _DYNAMIC there; _DYNAMIC is SHN_UNDEF, value 0, in these static images).

A row is OK when no check disagrees and at least one check agrees; else FLAG (with the disagreeing checks named).
Every OK row is re-judged with the value perturbed (+4, +8, -8, and := the donor's value): --perturb prints how
many perturbed rows the checks would still accept (the known-answer control of the rules).

Usage:
  gotcheck.py --lib LIBDIR --img A=PIN:TWIN --img B=PIN:TWIN --donor-img A=PIN:TWIN --donor-img B=PIN:TWIN
              [--gate A=full.tsv] [--gate B=full.tsv] [--gate R=full.tsv] [--side-dir A=DIR] [--side-dir B=DIR]
              --out got-cells.tsv [--perturb]
LIBDIR is the unit's lib/ (scanned: A/A*.v, B/Y*.v, A/Rt/*.v, B/Rt/*.v, Reusable/*.v). --side-dir checks a flat
directory of side-A or side-B files instead (the planted-control copies).
"""
import argparse, bisect, csv, glob, os, re, struct, sys
from elftools.elf.elffile import ELFFile

csv.field_size_limit(1 << 30)
NUM = re.compile(r'(?<![\w.])(0x[0-9a-fA-F]+|\d+)(?![\w])')
DEF_RE = re.compile(r'^[ \t]*(?:#\[[^\]]*\]\s*)?(?:(?:Local|Global|Program|Polymorphic)\s+)*'
                    r'(Definition|Lemma|Theorem|Fixpoint|Let|Record|Hypothesis|Hypotheses|Notation|Example|Fact|'
                    r'Corollary|Remark|Instance|Ltac|Axiom|Parameter|Variable|Variables|Inductive|Goal|Proposition)\s+'
                    r'([^\s:(]+)', re.M)
# a name token that names the pointee by another word; each with the reason it is the same object
ALIASES = {
    'shadow': ('shadow_memory_dynamic_address', 'the ASan shadow offset variable __asan_shadow_memory_dynamic_address'),
    'uar': ('detect_stack_use_after_return', 'use-after-return = __asan_option_detect_stack_use_after_return'),
    'canary': ('stack_chk_guard', 'the stack-protector canary = __stack_chk_guard'),
    'ssp': ('stack_chk_guard', 'stack-smashing protector = __stack_chk_guard'),
    'cflags': ('common_flags', 'common flags = __sanitizer::common_flags_dont_use'),
    'environ': ('environ', 'musl environ'),
}
NAME_PATTERNS = [  # (regex on the definition name, group = the name token)
    re.compile(r'(?i)(?:^|_)D_GOT_(\w+)$'), re.compile(r'(?i)(?:^|_)GOT_(\w+)$'),
    re.compile(r'(?i)^(?:[AB]_|Y_)?(\w+?)_GOT$'),  # X_GOT: only when X is an ALIASES key (A_SSP_GOT), see name_token
    re.compile(r'(?i)(?:^|_)as_got_(\w+)$'), re.compile(r'(?i)(?:^|_)D_(\w+?)_musl$'), re.compile(r'(?i)(?:^|_)real_(\w+)$'),
]
# numerals that are QUANTITIES by the file's own grammar, not addresses (a length, a size, a count)
QTY_BEFORE = [
    (re.compile(r'K(?:Zero|Fill)\s*\{\|[^|]*\|\}\s*\(ELit\s+$'), 'the length operand (ELit n) of a KZero / KFill write'),
    (re.compile(r'\bC(?:Img|Val)\s+$'), 'a chunk length (CImg n / CVal n)'),
]
QTY_AFTER = [(re.compile(r'^%nat\b'), 'a %nat literal')]


def num(s):
    return int(s, 16) if s.lower().startswith('0x') else int(s)


class Img:
    def __init__(self, pin, twin, role):
        self.role = role
        ep, et = ELFFile(open(pin, 'rb')), ELFFile(open(twin, 'rb'))
        g, gt = ep.get_section_by_name('.got'), et.get_section_by_name('.got')
        self.glo, self.ghi = g['sh_addr'], g['sh_addr'] + g['sh_size']
        self.gotdata = g.data()
        if (gt['sh_addr'], gt['sh_size'], gt.data()) != (self.glo, g['sh_size'], self.gotdata):
            sys.exit('gotcheck: REFUSED: %s: the pin and the twin .got differ' % role)
        self.words = struct.unpack('<%dQ' % (len(self.gotdata) // 8), self.gotdata)
        tx = ep.get_section_by_name('.text')
        self.tlo, self.text = tx['sh_addr'], tx.data()
        st = et.get_section_by_name('.symtab')
        if st is None:
            sys.exit('gotcheck: REFUSED: %s twin has no .symtab' % role)
        syms = []
        for s in st.iter_symbols():
            t = s['st_info']['type']
            if t in ('STT_FUNC', 'STT_OBJECT', 'STT_NOTYPE') and s['st_value'] and s.name \
                    and not s.name.startswith(('$', '.L')) and s['st_shndx'] != 'SHN_UNDEF':
                syms.append((s['st_value'], s['st_size'], s.name))
        syms.sort()
        self.syms, self.slo = syms, [x[0] for x in syms]
        self.keys = [self._key(i) for i in range(len(self.words))]

    def in_got(self, v):
        return self.glo <= v < self.ghi

    def sym(self, w):
        i = bisect.bisect_right(self.slo, w) - 1
        hits = []
        while i >= 0 and self.syms[i][0] > w - 0x200000:
            s, sz, n = self.syms[i]
            if s <= w < s + max(sz, 1):
                hits.append((w - s, n))
            i -= 1
        if not hits:
            return None
        off = min(o for o, _ in hits)
        return frozenset(n for o, n in hits if o == off), off

    def _key(self, i):
        w = self.words[i]
        if i == 0:
            return ('GOT0', w)
        s = self.sym(w) if 0x10000 <= w < 1 << 63 else None
        if s:
            return ('SYM', s[0], s[1])
        j = i - 1
        while j >= 0 and not (0x10000 <= self.words[j] < 1 << 63 and self.sym(self.words[j])):
            j -= 1
        prev = ('.got start' if j < 0 else '|'.join(sorted(self.sym(self.words[j])[0])))
        return ('VAL', w, prev, i - j)

    def cell(self, v):
        """(index, word, key) of the GOT word at address v: word = the 8 bytes at v (an unaligned v reads across two
        words and its key is MISALIGNED); None when v is not inside .got"""
        if not self.in_got(v):
            return None
        i, k = divmod(v - self.glo, 8)
        if k == 0:
            return i, self.words[i], self.keys[i]
        o = v - self.glo
        w = struct.unpack('<Q', self.gotdata[o:o + 8].ljust(8, b'\0'))[0]
        return i, w, ('MISALIGNED', k, self.keys[i])

    def u32(self, a):
        o = a - self.tlo
        return struct.unpack('<I', self.text[o:o + 4])[0] if 0 <= o and o + 4 <= len(self.text) else None

    def auipc_targets(self, near):
        """{target: auipc pc} of every `auipc rd, hi; ld|addi rd2, lo(rd)` pair that starts in [near - 8, near + 0x20)"""
        out = {}
        for p in range(near - 8, near + 0x20, 2):
            i1 = self.u32(p)
            if i1 is None or i1 & 0x7f != 0x17:
                continue
            rd, hi = (i1 >> 7) & 31, i1 & 0xfffff000
            hi = hi - (1 << 32) if hi & 0x80000000 else hi
            i2 = self.u32(p + 4)
            if i2 is None:
                continue
            op, f3, rs1 = i2 & 0x7f, (i2 >> 12) & 7, (i2 >> 15) & 31
            if rs1 == rd and ((op == 0x03 and f3 == 3) or (op == 0x13 and f3 == 0)):
                lo = i2 >> 20
                lo = lo - 4096 if lo & 0x800 else lo
                out[p + hi + lo] = p
        return out


def label(key):
    if key is None:
        return '-'
    if key[0] == 'GOT0':
        return 'GOT[0]=%#x' % key[1]
    if key[0] == 'SYM':
        return '|'.join(sorted(key[1])) + ('+%#x' % key[2] if key[2] else '')
    if key[0] == 'VAL':
        return 'VAL %#x (%d word(s) after GOT[%s])' % (key[1], key[3], key[2])
    if key[0] == 'MISALIGNED':
        return 'MISALIGNED +%d inside %s' % (key[1], label(key[2]))
    return repr(key)


def same(k1, k2):
    if k1 is None or k2 is None or k1[0] != k2[0]:
        return False
    if k1[0] == 'SYM':
        return bool(k1[1] & k2[1]) and k1[2] == k2[2]
    if k1[0] == 'MISALIGNED':
        return k1[1] == k2[1] and same(k1[2], k2[2])
    if k1[0] == 'VAL':
        # value and place; the place's name compared as a set (aliases differ between images)
        return k1[1] == k2[1] and k1[3] == k2[3] and bool(set(k1[2].split('|')) & set(k2[2].split('|')))
    return k1 == k2


def comment_spans(t):
    """[(start, end)] of Coq comments (nested) outside strings"""
    out, i, n, depth, st, instr = [], 0, len(t), 0, 0, False
    while i < n:
        if not depth and t[i] == '"':
            instr = not instr
        elif not instr and t.startswith('(*', i):
            if depth == 0:
                st = i
            depth += 1
            i += 2
            continue
        elif not instr and depth and t.startswith('*)', i):
            depth -= 1
            if depth == 0:
                out.append((st, i + 2))
            i += 2
            continue
        i += 1
    if depth:
        out.append((st, n))
    return out


N_ = r'(0x[0-9a-fA-F]+|\d+)'
STATED = [  # (name, regex anchored right after the numeral, preceding-text regex or None)
    ('lit8 V W', re.compile(r'^\s+' + N_ + r'(?![\w])'), re.compile(r'(?:^|[\s(\[;])(?:f|ub_)?lit8\s+$')),
    ('V 8 W', re.compile(r'^\s+8(?:%N)?\s+' + N_ + r'(?![\w])'), None),
    ('(V, 8, [(0, 8%N, W)])', re.compile(r'^\s*,\s*8(?:%N)?\s*,\s*\[\s*\(\s*0\s*,\s*8%N\s*,\s*' + N_ + r'\s*\)'), None),
    ('(V, 8%N, W)', re.compile(r'^\s*,\s*8%N\s*,\s*' + N_ + r'\s*\)'), None),
    ('CVal 8 (SLit W)', re.compile(r'^\s*\(CVal 8 \(SLit ' + N_ + r'\)\)'), None),
    ('(ANum V) W', re.compile(r'^\)\s+' + N_ + r'(?![\w])'), re.compile(r'ANum\s+$')),
    ('le8 W', re.compile(r'^\s*\(BM\.le8 \((?:Z_to_bv 64|BM\.wa) ' + N_ + r'\)\)'), None),
    ('C8 W', re.compile(r'^\s*\[(?:\w+\.)?C8 \(Z_to_bv 64 ' + N_ + r'\)\]'), None),
    ('(V + 0) 8 (SLit W)', re.compile(r'^\s*\+\s*0\)\s*8\s*\(SLit ' + N_ + r'\)'), None),
    ('[V] = W', re.compile(r'^\s*\]\s*=\s*' + N_ + r'(?![\w])'), re.compile(r'\[\s*$')),
    ('V -> W', re.compile(r'^\s*(?:\([^()]{0,60}\)\s*)?->\s*' + N_ + r'(?![\w])'), None),
    ('V = W', re.compile(r'^\s*=\s*' + N_ + r'(?![\w])'), None),
    ('word_mem / RO8 / ro_c8 / bz_guard / realizes V W', re.compile(r'^\s+' + N_ + r'(?![\w])'),
     re.compile(r'(?:word_mem\s+\S+\s+\S+|word_mem_ld\s+\S+\s+\S+|RO8|ro_c8(?:\s+\S+){6}|ub_region_ok_lit\s+\S+\s+\S+|'
                r'bz_guard_bytes(?:\s+\S+){2,3}|word_cells_of_rdword\s+\S+\s+\S+|_realizes(?:\s+\S+){1,6})\s+$')),
]
LIST_RE = re.compile(r'^\s*,\s*(\d+)\s*,\s*\[((?:\s*\(\s*\d+\s*,\s*\d+%N\s*,\s*(?:0x[0-9a-fA-F]+|\d+)\s*\)\s*;?)+)\s*\]')
LIST_EL = re.compile(r'\(\s*(\d+)\s*,\s*(\d+)%N\s*,\s*(0x[0-9a-fA-F]+|\d+)\s*\)')


def stated(t, m, img):
    """(kind, [(addr, W)]) the text states at the numeral match m, or None"""
    after, before = t[m.end():m.end() + 200], t[max(0, m.start() - 80):m.start()]
    v = num(m.group(1))
    lm = LIST_RE.match(after)
    if lm:
        els = [(v + int(o), num(w)) for o, sz, w in LIST_EL.findall(lm.group(2)) if sz == '8']
        if els:
            return '(V, n, [(off, 8%N, W); ...])', els
    for name, rx, pre in STATED:
        mm = rx.match(after)
        if mm and (pre is None or pre.search(before)):
            return name, [(v, num(mm.group(1)))]
    return None


def defname(defs, pos):
    i = bisect.bisect_right([d[0] for d in defs], pos) - 1
    return defs[i][1] if i >= 0 else '-'


def name_token(d):
    for j, rx in enumerate(NAME_PATTERNS):
        mm = rx.search(d)
        if mm:
            tok = mm.group(1)
            if j == 2 and tok.lower() not in ALIASES:
                return None          # X_GOT with an X that names nothing (CM_GOT, CMD_GOTW)
            return None if tok.upper() in ('W', 'LO', 'HI') else tok
    return None


def name_check(d, key):
    tok = name_token(d)
    if tok is None:
        return '-', ''
    if key is None or key[0] != 'SYM':
        return 'MISMATCH', 'name %s, pointee %s' % (tok, label(key))
    names = ' '.join(key[1]).lower()
    if tok.lower() in names:
        return 'MATCH', tok
    for k, (sub, why) in ALIASES.items():
        if tok.lower() == k and sub.lower() in names:
            return 'ALIAS', '%s = %s (%s)' % (tok, sub, why)
    # a token made of several words, each in the name (asan_shadow_memory_dynamic_address)
    parts = [p for p in re.split(r'_+', tok.lower()) if p]
    if parts and all(p in names for p in parts):
        return 'MATCH', tok
    return 'MISMATCH', 'name %s, pointee %s' % (tok, label(key))


def file_image(path, side_hint=None):
    """A or B: by directory (lib/A, lib/B, lib/A/Rt, lib/B/Rt); lib/Reusable by its Requires, else B (gate RU key)"""
    if side_hint:
        return side_hint, 'side-dir'
    p = path.replace(os.sep, '/')
    if '/A/' in p or p.startswith('A/'):
        return 'A', 'directory'
    if '/B/' in p or p.startswith('B/'):
        return 'B', 'directory'
    t = open(path).read()
    a = re.search(r'Require[^.]*\blib\.A\.', t)
    b = re.search(r'Require[^.]*\blib\.B\.', t)
    if a and not b:
        return 'A', 'Require lib.A'
    if b and not a:
        return 'B', 'Require lib.B'
    return 'B', 'no image Require: the gate key of lib/Reusable (RU, key B)'


def load_gate(path, img):
    """{(dst_file, dst_line): [(idx, dst_value, src_value, verdict, src_file, src_line)]} for rows whose dst value
    is in img's .got"""
    out = {}
    with open(path) as f:
        for r in csv.reader(f, delimiter='\t'):
            if not r or r[0].startswith('#') or r[0] == 'verdict' or len(r) < 12:
                continue
            if not r[11] or not r[6]:
                continue
            dv = int(r[11], 16)
            if not img.in_got(dv):
                continue
            out.setdefault((r[5], int(r[6])), []).append(
                (int(r[8]) if r[8].isdigit() else 0, dv, int(r[10], 16) if r[10] else None, r[0], r[3], r[4]))
    for k in out:
        out[k].sort()
    return out


SVX_RE = re.compile(r'\bsvx?\s+S_([0-9a-fA-F]+)\s+DS_\1\s+\(Z_to_bv 64\s+$')


def auipc_value(before, v, img):
    """the reason, when the numeral is the register value a walk states after an auipc (`svx S_<pc> DS_<pc> (Z_to_bv
    64 V)`) and the image's instruction at <pc> is an auipc whose result is V: a register value, not a cell"""
    mm = SVX_RE.search(before)
    if not mm:
        return None
    pc = int(mm.group(1), 16)
    i = img.u32(pc)
    if i is None or i & 0x7f != 0x17:
        return None
    hi = i & 0xfffff000
    hi = hi - (1 << 32) if hi & 0x80000000 else hi
    if pc + hi != v:
        return None
    tg = [a for a, p in img.auipc_targets(pc).items() if p == pc]
    return 'the result of the auipc at %#x (x%d := %#x), a register value, not a cell%s' % (
        pc, (i >> 7) & 31, v, ('; the next instruction loads %#x' % tg[0]) if tg else '')


def numerals(t, img):
    """[(match, value, comment span or None, qty_reason or None, definition)] of the numerals of text t inside
    img's .got"""
    cs = comment_spans(t)
    cst = [c[0] for c in cs]
    defs = [(m.start(), m.group(2)) for m in DEF_RE.finditer(t)]
    out = []
    for m in NUM.finditer(t):
        v = num(m.group(1))
        if not img.in_got(v):
            continue
        i = bisect.bisect_right(cst, m.start()) - 1
        incom = cs[i] if i >= 0 and cs[i][0] <= m.start() < cs[i][1] else None
        before, after = t[max(0, m.start() - 200):m.start()], t[m.end():m.end() + 10]
        q = next((w for rx, w in QTY_BEFORE if rx.search(before)), None) or \
            next((w for rx, w in QTY_AFTER if rx.search(after)), None) or auipc_value(before, v, img)
        out.append((m, v, incom, q, defname(defs, m.start())))
    return out


# words a comment may use for a pointee, beyond the identifiers of its symbol name (each with its reason)
COMMENT_WORDS = {
    '__stack_chk_guard': ['stack-protector', 'stack protector', 'canary'],   # the guard musl's -fstack-protector reads
    '_ZN14__interception11real_memsetE': ['REAL(memset)'],
    '_ZN14__interception11real_memcpyE': ['REAL(memcpy)'],
    '__asan_shadow_memory_dynamic_address': ['shadow'],                      # the shadow offset variable
}
NS_WORDS = {'__sanitizer', '__asan', '__interception', '__lsan', '__ubsan', '_GLOBAL__N_1'}


def name_words(key):
    """identifiers a text may use for the pointee of key: each symbol name's identifiers (mangled names parsed),
    namespaces dropped, leading underscores and the _dont_use / _dont_use_directly suffixes stripped, real_X -> X"""
    if key is None or key[0] != 'SYM':
        return []
    out = set()
    for n in key[1]:
        ids = []
        if n.startswith('_Z'):
            i = 0
            while i < len(n):
                mm = re.match(r'\d+', n[i:])
                if not mm:
                    i += 1
                    continue
                k = int(mm.group(0))
                ids.append(n[i + len(mm.group(0)):i + len(mm.group(0)) + k])
                i += len(mm.group(0)) + k
        else:
            ids = [n]
        for x in ids:
            if x in NS_WORDS or not x:
                continue
            x = re.sub(r'_dont_use(_directly)?$', '', x.lstrip('_'))
            out.add(x)
            if x.startswith('real_'):
                out.add(x[5:])
        out |= set(COMMENT_WORDS.get(n, []))
    return sorted(w for w in out if len(w) >= 4)


def comment_check(t, m, span, key, word, img, tw):
    """(result, detail) for a numeral inside a comment: WORD (the GOT word is written in the comment within 160
    characters after it), NAME (an identifier of the pointee in the numeral's own clause: between the previous and the
    next .got numeral of the comment, at most 80 before / 120 after, and the numeral not a block start `V..`), DISASM
    (an auipc + ld|addi pair at a pc written on the same line computes the address), TWIN-LINE (the twin file has a
    comment line with the same text up to numerals whose numeral at the same place has the same pointee); else -"""
    lo, hi = span
    after = t[m.end():min(hi, m.end() + 160)]
    if word >= 0x10000 and any(num(x) == word for x in NUM.findall(after)):
        return 'WORD', 'the comment writes the word %#x after it' % word
    a0, b0 = max(lo, m.start() - 80), min(hi, m.end() + 120)
    for mm in NUM.finditer(t, a0, m.start()):
        if img.in_got(num(mm.group(1))):
            a0 = mm.end()
    for mm in NUM.finditer(t, m.end(), b0):
        if img.in_got(num(mm.group(1))):
            b0 = mm.start()
            break
    win = t[a0:b0]
    if not t.startswith('..', m.end()):
        for w in name_words(key):
            variants = {w.lower(), w.lower().replace('_', ' '), w.lower().replace('_', '-')}
            if any(x in win.lower() for x in variants):
                return 'NAME', 'the comment names %s in its clause' % w
    ls, le = t.rfind('\n', 0, m.start()) + 1, t.find('\n', m.end())
    line = t[ls:le if le >= 0 else len(t)]
    for tok in re.findall(r'(?<![\w])(?:0x)?([0-9a-fA-F]{5,6})(?![\w])', line):
        pc = int(tok, 16)
        if img.tlo <= pc < img.tlo + len(img.text):
            hits = img.auipc_targets(pc)
            v = num(m.group(1))
            if v in hits:
                return 'DISASM', 'auipc at %#x + its ld/addi compute %#x (the pc %#x is written on the line)' % (hits[v], v, pc)
    if tw is not None and tw.clines:
        ordn = sum(1 for _ in NUM.finditer(line, 0, m.start() - ls))
        for keys in tw.clines.get(mask(line).strip(), []):
            if ordn < len(keys) and keys[ordn] is not None and same(key, keys[ordn]):
                return 'TWIN-LINE', 'the twin file has this comment line with the pointee %s at the same place' % label(key)
    return '-', ''


def match_multiset(xs, ys):
    """greedy pairing by same(): (unmatched xs, unmatched ys)"""
    ys = list(ys)
    left = []
    for x in xs:
        j = next((j for j, y in enumerate(ys) if same(x, y)), None)
        if j is None:
            left.append(x)
        else:
            ys.pop(j)
    return left, ys


def mask(line):
    return NUM.sub('#', line)


class Twin:
    """the other image's twin file: {definition name: [GOT keys of its code numerals in the other image's .got]}"""
    def __init__(self, path, other):
        self.path, self.defs, self.clines = path, None, None
        if not (path and os.path.exists(path) and other is not None):
            return
        t = open(path).read()
        self.defs, self.clines = {}, {}
        for m, v, incom, q, d in numerals(t, other):
            if not incom and not q:
                self.defs.setdefault(d, []).append(other.cell(v)[2])
        # {line text with numerals masked: [[the key of each numeral of the line, None outside .got]]}
        for line in t.split('\n'):
            ks = [other.cell(num(mm.group(1)))[2] if other.in_got(num(mm.group(1))) else None for mm in NUM.finditer(line)]
            if any(k is not None for k in ks):
                self.clines.setdefault(mask(line).strip(), []).append(ks)

    def check(self, d, mine):
        """the definition's GOT pointees here (mine) against the twin definition's, as multisets"""
        if self.defs is None:
            return '-', ''
        if d not in self.defs:
            return 'NO-TWIN-CELL', '%s: no .got numeral in %s' % (os.path.basename(self.path), d)
        a, b = match_multiset(mine, self.defs[d])
        if not a and not b:
            return 'SAME', '%s %s: the same %d pointee(s)' % (os.path.basename(self.path), d, len(mine))
        return 'SET-DIFF', '%s %s: only here %s; only in the twin %s' % (
            os.path.basename(self.path), d, ', '.join(label(k) for k in a)[:200] or '-',
            ', '.join(label(k) for k in b)[:200] or '-')


def scan(path, rel, side, imgs, dimgs, gates, twin_path, other):
    img = imgs[side]
    t = open(path).read()
    tw = Twin(twin_path, other)
    base = os.path.basename(path)
    gate = gates.get('R' if '/Reusable/' in '/' + rel else side, {})
    seen = {}
    rows = []
    nums = numerals(t, img)
    bydef = {}
    for m, v, incom, q, d in nums:
        if not incom and not q:
            bydef.setdefault(d, []).append(img.cell(v)[2])
    for m, v, incom, q, d in nums:
        ln = t.count('\n', 0, m.start()) + 1
        idx, word, key = img.cell(v)
        if q:
            rows.append(dict(file=rel, line=ln, value='%#x' % v, pointee=label(key), donor_value='-', donor_pointee='-',
                             name_check='-', status='NOT-ADDRESS', image=side, in_comment='yes' if incom else 'no',
                             definition=d, word='%#x' % word, got_index=idx, donor='-', stated='-', twin='-',
                             comment='-', disagree='-', qty=q, _key=key, _dkey=None, _v=v, _dval=None, _st=None, _def=None))
            continue
        # (a) donor
        k = seen.get((ln, v), 0)
        seen[(ln, v)] = k + 1
        grows = [g for g in gate.get((base, ln), []) if g[1] == v]
        dval = dkey = None
        dnote = 'no gate row (comment)' if incom else ('no gate run for this directory' if not gate else 'no gate row')
        dres = '-'
        if k < len(grows):
            g = grows[k]
            dval = g[2]
            dnote = 'gate %s src %s:%s' % (g[3], g[4], g[5])
            if dval is None:
                dres = 'NO-DONOR-VALUE'
            elif dimgs[side].in_got(dval):
                dkey = dimgs[side].cell(dval)[2]
                dres = 'SAME' if same(key, dkey) else 'DIFF'
            else:
                dres = 'DONOR-NOT-GOT'
        # (b) name
        nres, ndet = name_check(d, key) if not incom else ('-', '')
        # (c) stated
        st = stated(t, m, img)
        sres, sdet = '-', ''
        if st:
            kind, els = st
            bad = []
            for a, w in els:
                c = img.cell(a)
                if c is None or c[1] != w:
                    bad.append((a, w, None if c is None else c[1]))
            if not bad:
                sres, sdet = 'OK', '%s: %s' % (kind, '; '.join('[%#x]=%#x' % (a, w) for a, w in els))
            elif kind in ('lit8 V W', 'word_mem / RO8 / ro_c8 / bz_guard / realizes V W', 'V = W', 'V -> W') \
                    and len(els) == 1 and v < els[0][1] <= v + 0x1000 and (els[0][1] - v) % 8 == 0:
                sres, sdet = 'RANGE?', '%s: next numeral %#x is %#x past V (a range end?), the word is %#x' % (
                    kind, els[0][1], els[0][1] - v, word)
            else:
                sres, sdet = 'MISMATCH', '%s: %s' % (kind, '; '.join('stated [%#x]=%#x, image %s' % (
                    a, w, '-' if iw is None else '%#x' % iw) for a, w, iw in bad))
        # (d) twin: the definition's GOT pointees, as a multiset, against the twin definition's
        tres, tdet = tw.check(d, bydef[d]) if not incom else ('-', '')
        # (e) a comment numeral: what the comment itself says about it
        cres, cdet = comment_check(t, m, incom, key, word, img, tw) if incom else ('-', '')
        agree = [x for x in (dres == 'SAME', nres in ('MATCH', 'ALIAS'), sres == 'OK', tres == 'SAME', cres != '-') if x]
        disagree = [n for n, x in (('donor', dres in ('DIFF', 'DONOR-NOT-GOT')), ('name', nres == 'MISMATCH'),
                                    ('stated', sres in ('MISMATCH', 'RANGE?')), ('twin', tres == 'SET-DIFF'),
                                    ('misaligned', key[0] == 'MISALIGNED')) if x]
        status = 'FLAG' if disagree else ('OK' if agree else 'UNCHECKED')
        rows.append(dict(file=rel, line=ln, value='%#x' % v, pointee=label(key), donor_value='-' if dval is None else '%#x' % dval,
                         donor_pointee=label(dkey) if dkey else '-', name_check=nres + (' ' + ndet if ndet else ''),
                         status=status, image=side, in_comment='yes' if incom else 'no', definition=d,
                         word='%#x' % word, got_index=idx, donor=dres + ' ' + dnote, stated=sres + (' ' + sdet if sdet else ''),
                         twin=tres + (' ' + tdet if tdet else ''), comment=cres + (' ' + cdet if cdet else ''),
                         disagree=','.join(disagree) or '-', qty='-', _key=key, _dkey=dkey, _v=v, _dval=dval, _st=st,
                         _def=(bydef[d], tw.defs.get(d) if tw.defs else None) if not incom else None,
                         _cargs=(t, m, incom, tw) if incom else None))
    # (e') a comment numeral nothing in the comment checks: CODE-SAME-FILE when the same value is a code numeral of
    # this file that is OK (the comment repeats an address the code uses and the checks accepted there)
    codeok = {x['_v'] for x in rows if x['in_comment'] == 'no' and x['status'] == 'OK'}
    for x in rows:
        x['_codeok'] = codeok
        if x['status'] == 'UNCHECKED' and x['in_comment'] == 'yes' and x['_v'] in codeok:
            x['status'], x['comment'] = 'OK', 'CODE-SAME-FILE the value is a code numeral of this file, OK there'
    return rows


def rejudge(row, nv, img):
    """{rule: does it still accept the row with the value nv} for each rule that accepted `row` (the perturbation
    control); {} when nv is not inside .got (every rule refuses)"""
    c = img.cell(nv)
    if c is None:
        return {}
    key = c[2]
    res = {}
    if row['donor'].startswith('SAME'):
        res['donor'] = same(key, row['_dkey'])
    if row['name_check'].split()[0] in ('MATCH', 'ALIAS'):
        res['name'] = name_check(row['definition'], key)[0] in ('MATCH', 'ALIAS')
    if row['stated'].startswith('OK'):
        kind, els = row['_st']
        cells = [img.cell(a + nv - row['_v']) for a, w in els]
        res['stated'] = all(cc is not None and cc[1] == w for cc, (a, w) in zip(cells, els))
    if row['twin'].startswith('SAME'):
        mine, theirs = row['_def']
        j = next(j for j, k in enumerate(mine) if same(k, row['_key']))
        a, b = match_multiset(mine[:j] + [key] + mine[j + 1:], theirs)
        res['twin'] = not a and not b
    if row['comment'].split()[0] != '-':
        t, m, span, twobj = row['_cargs']
        # the comment rule on the perturbed address: the word and the pointee of nv, the auipc target must be nv
        r = comment_check(t, m, span, key, c[1], img, twobj)
        if r[0] == 'DISASM':
            pc = int(re.search(r'the pc (0x[0-9a-f]+)', r[1]).group(1), 16)
            r = ('-', '') if nv not in img.auipc_targets(pc) else r
        res['comment-' + row['comment'].split()[0]] = r[0] != '-' or (
            row['comment'].startswith('CODE-SAME-FILE') and nv in row['_codeok'])
    return res


PERTURB = (('+4', lambda x: x['_v'] + 4), ('+8', lambda x: x['_v'] + 8), ('-8', lambda x: x['_v'] - 8),
           (':=donor', lambda x: x['_dval']))


def accepted_by(x):
    out = []
    if x['donor'].startswith('SAME'):
        out.append('donor')
    if x['name_check'].split()[0] in ('MATCH', 'ALIAS'):
        out.append('name')
    if x['stated'].startswith('OK'):
        out.append('stated')
    if x['twin'].startswith('SAME'):
        out.append('twin')
    if x['comment'].split()[0] != '-':
        out.append('comment-' + x['comment'].split()[0])
    return out


def control(rows, imgs):
    """re-judge every OK row under each perturbation; set row['control'] to the perturbations still accepted; print
    per rule how many accepted rows each perturbation leaves accepted by that rule"""
    oks = [x for x in rows if x['status'] == 'OK']
    per = {}
    for x in oks:
        surv = []
        for nm, fn in PERTURB:
            nv = fn(x)
            if nv is None:
                continue
            r = rejudge(x, nv, imgs[x['image']])
            for rule in accepted_by(x):
                p = per.setdefault((rule, nm), [0, 0])
                p[0] += 1
                p[1] += 1 if r.get(rule) else 0
            if r and all(r.values()):
                surv.append('%s=%#x' % (nm, nv))
        x['control'] = ','.join(surv) or 'refused'
    for x in rows:
        x.setdefault('control', '-')
    print('perturbation control: %d OK rows; a perturbed row stays accepted only if every rule that accepted the row '
          'accepts it' % len(oks))
    for nm, _ in PERTURB:
        s = [x for x in oks if ('%s=' % nm) in x['control']]
        print('  %-8s %d still accepted%s' % (nm, len(s), (': ' + '; '.join('%s:%s' % (x['file'], x['line']) for x in s)) if s else ''))
    print('  per rule (rows the rule accepted / of those, still accepted by that rule after the perturbation):')
    for rule in sorted({k[0] for k in per}):
        print('    %-18s %s' % (rule, '  '.join('%s %d/%d' % (nm, per[(rule, nm)][0], per[(rule, nm)][1])
                                             for nm, _ in PERTURB if (rule, nm) in per)))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--lib')
    ap.add_argument('--side-dir', action='append', default=[], metavar='A=DIR')
    ap.add_argument('--img', action='append', required=True, metavar='A=PIN:TWIN')
    ap.add_argument('--donor-img', action='append', required=True, metavar='A=PIN:TWIN')
    ap.add_argument('--gate', action='append', default=[], metavar='A=full.tsv')
    ap.add_argument('--relto', default=None, help='write file paths relative to this directory (default: --lib\'s parent)')
    ap.add_argument('--out', required=True)
    ap.add_argument('--perturb', action='store_true')
    a = ap.parse_args()
    imgs = {k: Img(*v.split(':'), role='ours ' + k) for k, v in (x.split('=', 1) for x in a.img)}
    dimgs = {k: Img(*v.split(':'), role='donor ' + k) for k, v in (x.split('=', 1) for x in a.donor_img)}
    gates = {}
    for x in a.gate:
        k, p = x.split('=', 1)
        gates[k] = load_gate(p, imgs['B' if k == 'R' else k])
    files = []
    if a.lib:
        L = a.lib
        for pat in ('A/A*.v', 'B/Y*.v', 'A/Rt/*.v', 'B/Rt/*.v', 'Reusable/*.v'):
            files += sorted(glob.glob(os.path.join(L, pat)))
        relto = a.relto or os.path.dirname(os.path.abspath(L))
    for x in a.side_dir:
        k, d = x.split('=', 1)
        files += [(f, k) for f in sorted(glob.glob(os.path.join(d, '*.v')))]
        relto = a.relto or os.path.dirname(os.path.abspath(d))
    rows, nfiles, imgsrc = [], {}, {}
    for f in files:
        f, hint = (f if isinstance(f, tuple) else (f, None))
        side, why = file_image(f, hint)
        imgsrc[why] = imgsrc.get(why, 0) + 1
        rel = os.path.relpath(f, relto)
        # the twin: same relative path with the side swapped (lib/B/Yxxx.v <-> lib/A/Axxx.v, Rt by name)
        twin = None
        if a.lib and not hint and '/Reusable/' not in '/' + rel:
            p = os.path.relpath(f, a.lib)
            if p.startswith('A/'):
                q = 'B/' + p[2:]
                q = re.sub(r'^B/A(\w+\.v)$', r'B/Y\1', q)
            else:
                q = 'A/' + p[2:]
                q = re.sub(r'^A/Y(\w+\.v)$', r'A/A\1', q)
            twin = os.path.join(a.lib, q)
        other = imgs['B' if side == 'A' else 'A'] if twin else None
        r = scan(f, rel, side, imgs, dimgs, gates, twin, other)
        rows += r
        nfiles[side] = nfiles.get(side, 0) + 1
    cnt = {}
    for x in rows:
        cnt[(x['image'], x['status'])] = cnt.get((x['image'], x['status']), 0) + 1
    print('gotcheck: %d files (%s), image by %s; %d numerals inside .got (A [%#x,%#x), B [%#x,%#x))' % (
        len(files), ', '.join('%s %d' % kv for kv in sorted(nfiles.items())), imgsrc, len(rows),
        imgs['A'].glo, imgs['A'].ghi, imgs['B'].glo, imgs['B'].ghi))
    for k in sorted(cnt):
        print('  image %s %-9s %d' % (k[0], k[1], cnt[k]))
    for name in ('donor', 'name_check', 'stated', 'twin', 'comment'):
        c = {}
        for x in rows:
            kk = x[name].split()[0]
            c[kk] = c.get(kk, 0) + 1
        print('  check %-10s %s' % (name, ', '.join('%s %d' % kv for kv in sorted(c.items()))))
    if a.perturb:
        control(rows, imgs)
    for x in rows:
        x.setdefault('control', '-')
    cols = ['file', 'line', 'value', 'pointee', 'donor_value', 'donor_pointee', 'name_check', 'status', 'image',
            'in_comment', 'definition', 'word', 'got_index', 'donor', 'stated', 'twin', 'comment', 'disagree', 'qty',
            'control']
    with open(a.out, 'w') as f:
        f.write('\t'.join(cols) + '\n')
        for x in rows:
            f.write('\t'.join(str(x[c]) for c in cols) + '\n')
    return rows


if __name__ == '__main__':
    main()
