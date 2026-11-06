#!/usr/bin/env python3
"""triage.py: a measured reason for every non-SAME row of the symbol + offset sweep (rows.tsv from sweep.py).

Each row gets: reason, measurement, result (OK / FINDING), finding_kind (code / comment / -), new_value, read_by.
Rules run in this order; the first that measures a reason wins. Every rule names what it read: a symbol table entry
(twin symtab), image bytes (pin), section / PT_LOAD bounds, a GOT word, an instruction decoded from the pin, or the
file's own text (src = donor file, dst = our file).

  STR      both values lie in a NUL-terminated .rodata string, the same text at the same offset (image bytes).
  END      both values are the end of a symbol of the same name whose st_size differs between the images.
  PLAIN    (run RU) the file is one of lib/Reusable's pre-port files, which describe the PLAIN build: the pair is
           resolved again in the plain images (cgif plain twin / our plain twin); SAME there.
  DERIVED  both values are the same expression of named image quantities on their own side: a symbol start / end,
           a section or PT_LOAD bound, an image bound, a difference of one such quantity and a bound, that value / 8,
           / 4, / 4096, or the ASan shadow (x / 8 + 0x7fff8000) of one.
  BYTES    unnamed read-only data: the 16 bytes at the donor value equal the 16 bytes at ours (pin bytes).
  RET      both values are the return address of (or the pc of) a call to the same symbol (jal / auipc+jalr
           decoded from the pin).
  REGION   the numeral names a region of lib/A/AD2j.v / lib/B/YD2j.v (generated from our image) and equals that
           region's start / end / length in our file.
  NAMED    a generated table row whose definition names a symbol (tfib_A_<f> start, tfib_E_<f> end): ours equals that
           symbol's start / end in our symtab.
  GENSET   a generated file (whole file written from our image): ours' symbol + offset also occurs among the donor's
           values of the same definition, so the pair is a reordering of one table.
  HAND     a row read by hand: hand.tsv names the measurement.
Rows no rule explains are written with result OPEN (the run fails the triage).
"""
import argparse
import collections
import os
import re
import struct
import sys
import warnings

warnings.filterwarnings('ignore', category=SyntaxWarning)   # eval of a malformed candidate expression

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sweep  # noqa: E402

SHADOW = 0x7fff8000
GEN_A = {'AB01', 'AB03', 'AF0m', 'AD2j', 'AE3i', 'ACej', 'AB1w'}
GEN_B = {'Y' + x[1:] for x in GEN_A}
COLS = ['run', 'src', 'dst', 'sentence', 'src_value', 'dst_value', 'donor_symoff', 'ours_symoff', 'status', 'rule',
        'reason', 'measurement', 'result', 'finding_kind', 'new_value', 'read_by']


def rows_of(path):
    with open(path) as f:
        h = f.readline().rstrip('\n').split('\t')
        return [dict(zip(h, ln.rstrip('\n').split('\t'))) for ln in f]


def key(r):
    return (r['src'], r['dst'], r['sentence'], r['idx'])


# ---------------------------------------------------------------- RISC-V decode (the few forms the rules need)
def sext(x, bits):
    return x - (1 << bits) if x & (1 << (bits - 1)) else x


def word(img, a):
    b = img.mem(a, 4)
    return struct.unpack('<I', b)[0] if b else None


def call_target(img, pc):
    """Target of a call at pc: `jal ra, T` or `auipc rX, hi; jalr ra, lo(rX)`; else None."""
    w = word(img, pc)
    if w is None or w & 3 != 3:
        return None
    op, rd = w & 0x7f, (w >> 7) & 31
    if op == 0x6f and rd == 1:
        imm = (((w >> 31) & 1) << 20) | (((w >> 21) & 0x3ff) << 1) | (((w >> 20) & 1) << 11) | (((w >> 12) & 0xff) << 12)
        return pc + sext(imm, 21)
    if op == 0x17:
        w2 = word(img, pc + 4)
        if w2 is not None and w2 & 0x7f == 0x67 and (w2 >> 7) & 31 == 1 and (w2 >> 15) & 31 == rd:
            return pc + sext(w & 0xfffff000, 32) + sext(w2 >> 20, 12)
    return None


def call_desc(img, v):
    """('ret', T) when v - 4 / v - 8 holds a call to T (v is its return address), ('call', T) when v does."""
    for pc, how in ((v - 4, 'ret'), (v - 8, 'ret'), (v, 'call')):
        t = call_target(img, pc)
        if t is None:
            continue
        if how == 'ret' and pc == v - 8 and word(img, v - 8) & 0x7f != 0x17:
            continue
        r = img.resolve(t)
        if r['cover'] or r['alias']:
            s = (r['alias'] or r['cover'])[0]
            return how, pc, t, s.key, t - s.value
    return None


OPS = {0x03: 'load', 0x23: 'store', 0x13: 'op-imm', 0x1b: 'op-imm-32', 0x33: 'op', 0x3b: 'op-32', 0x37: 'lui',
       0x17: 'auipc', 0x6f: 'jal', 0x67: 'jalr', 0x63: 'branch', 0x73: 'system', 0x07: 'fp-load', 0x27: 'fp-store'}


def insn_text(w):
    op = w & 0x7f
    if w & 3 != 3 or op not in OPS:
        return None
    return f'{OPS[op]} rd={(w >> 7) & 31} funct3={(w >> 12) & 7} rs1={(w >> 15) & 31}'


# ---------------------------------------------------------------- anchors for DERIVED
class Anchors:
    def __init__(self, img):
        a = {}
        for s in img.syms:
            a.setdefault(s.key, s.value)
            if s.size:
                a.setdefault(s.key + '.end', s.value + s.size)
        b = {}
        for lo, hi, n in img.secs:
            b['sec:' + n], b['secend:' + n] = lo, hi
        for i, (va, m, fs, _) in enumerate(img.loads):
            b[f'load{i}'], b[f'load{i}.end'] = va, va + m
            b[f'load{i}.pfloor'], b[f'load{i}.pceil'] = va & ~0xfff, (va + m + 0xfff) & ~0xfff
        b['image.lo'] = min(v for k, v in b.items() if k.endswith('.pfloor'))
        b['image.top'] = max(v for k, v in b.items() if k.endswith('.pceil'))
        b['zero'] = 0
        a.update(b)
        self.a, self.bounds = a, b
        self.by_v = collections.defaultdict(set)
        for k, v in a.items():
            self.by_v[v].add(k)

    def exprs(self, v):
        out = set()
        forms = [(v, '{}')]
        for k, f in ((8, '({}) / 8'), (4, '({}) / 4'), (4096, '({}) / 4096')):
            forms.append((v * k, f))
        if v >= SHADOW:
            forms.append(((v - SHADOW) * 8, 'shadow({})'))
        for x, f in forms:
            for n in self.by_v.get(x, ()):
                out.add(f.format(n))
            for bn, bv in self.bounds.items():
                if bn == 'zero':
                    continue
                for n in self.by_v.get(x + bv, ()):
                    out.add(f.format(f'{n} - {bn}'))
                for n in self.by_v.get(bv - x, ()):
                    out.add(f.format(f'{bn} - {n}'))
        return out


# ---------------------------------------------------------------- text helpers
_cache = {}


def text(path):
    if path not in _cache:
        try:
            _cache[path] = open(path, errors='replace').read().split('\n')
        except OSError:
            _cache[path] = []
    return _cache[path]


def snippet(lines, ln, v, w=70):
    """The text around numeral v on line ln (1-based), in any of its written forms."""
    if not ln or ln > len(lines):
        return ''
    t = lines[ln - 1]
    for f in (f'{v:#x}', str(v), f'0x{v:08x}', f'0x{v:X}'):
        m = re.search(r'(?<![\w])' + re.escape(f) + r'(?![\w])', t)
        if m:
            return ' '.join(t[max(0, m.start() - w): m.end() + w // 2].split())
    return ' '.join(t[:w * 2].split())


def forms(v):
    return (f'{v:#x}', str(v), f'0x{v:08x}', f'0x{v:X}')


def has_num(t, v):
    return any(re.search(r'(?<![\w])' + re.escape(f) + r'(?![\w%])', t) for f in forms(v))


# ---------------------------------------------------------------- closed arithmetic of one line
def group(t, i):
    """t[i] == '(' -> index after its matching ')'."""
    d = 0
    for j in range(i, len(t)):
        d += {'(': 1, ')': -1}.get(t[j], 0)
        if d == 0:
            return j + 1
    return None


IDENT = re.compile(r"(?<![\w'])[A-Za-z_][\w']*")


def zeval(e, env=None):
    """Value of a closed Z expression (+ - * / mod ^ and parentheses); identifiers take their value from env."""
    e = e.strip()
    names = [n for n in IDENT.findall(e) if n != 'mod']
    if names and env is None:
        return None
    x = re.sub(r'\bmod\b', '%', e)
    for n in sorted(set(names), key=len, reverse=True):
        x = re.sub(r"(?<![\w'])" + re.escape(n) + r"(?![\w'])", f'({env[n]})', x)
    if not re.fullmatch(r"[\s0-9a-fA-Fx()+\-*/^%]+", x):
        return None
    x = x.replace('^', '**').replace('/', '//')
    try:
        return eval(x, {'__builtins__': {}}, {})
    except Exception:
        return None


def zequal(a, b):
    """a = b as Z expressions: closed, or for every value of their identifiers among 0, 1, 2, 7, 1000 (a linear
    identity checked at five points)."""
    names = sorted({n for n in IDENT.findall(a + ' ' + b) if n != 'mod'})
    if not names:
        x, y = zeval(a), zeval(b)
        return x is not None and x == y
    for k in (0, 1, 2, 7, 1000):
        env = {n: k + i for i, n in enumerate(names)}
        x, y = zeval(a, env), zeval(b, env)
        if x is None or x != y:
            return False
    return True


def arith(t, v):
    """`change (E) with N` / `replace (E) with (F)` / `change N with (E)` on line t where v is written in it and the
    two sides are equal on the line's own numbers: the statement text, else None."""
    for m in re.finditer(r'\b(change|replace)\s*', t):
        i = m.end()
        if i < len(t) and t[i] == '(':
            j = group(t, i)
            lhs = t[i + 1:j - 1] if j else None
        else:
            n = re.match(r'(0x[0-9a-fA-F]+|\d+)', t[i:])
            j, lhs = (i + n.end(), n.group(1)) if n else (None, None)
        if not lhs:
            continue
        w = re.match(r'\s*with\s*', t[j:])
        if not w:
            continue
        k = j + w.end()
        if k < len(t) and t[k] == '(':
            e = group(t, k)
            rhs = t[k + 1:e - 1] if e else None
        else:
            n = re.match(r'(0x[0-9a-fA-F]+|\d+)', t[k:])
            e, rhs = (k + n.end(), n.group(1)) if n else (None, None)
        if not rhs:
            continue
        stmt = t[m.start():e]
        if not has_num(stmt, v):
            continue
        if zequal(lhs, rhs):
            return ' '.join(stmt.split())
    return None


# ---------------------------------------------------------------- the decoded fields of an instruction word
def insn_fields(w):
    op = w & 0x7f
    f = {'rd': (w >> 7) & 31, 'rs1': (w >> 15) & 31, 'rs2': (w >> 20) & 31, 'imm12': w >> 20, 'imm20': w >> 12}
    if op == 0x6f:
        f['jimm'] = (((w >> 31) & 1) << 20) | (((w >> 21) & 0x3ff) << 1) | (((w >> 20) & 1) << 11) | (
            ((w >> 12) & 0xff) << 12)
    if op == 0x63:
        f['bimm'] = (((w >> 31) & 1) << 12) | (((w >> 7) & 1) << 11) | (((w >> 25) & 0x3f) << 5) | (((w >> 8) & 0xf) << 1)
    if op == 0x23:
        f['simm'] = ((w >> 25) << 5) | ((w >> 7) & 31)
    return f


# ---------------------------------------------------------------- the run table
class Run:
    def __init__(self, name, D, O, sdir, ddir, note=''):
        self.name, self.D, self.O, self.sdir, self.ddir, self.note = name, D, O, sdir, ddir, note
        self.AD, self.AO = Anchors(D), Anchors(O)

    def src_lines(self, f):
        return text(os.path.join(self.sdir, f))

    def dst_lines(self, f):
        return text(os.path.join(self.ddir, f))


def img_name(img):
    return f'{img.pin_sha}/{img.twin_sha}'


def fmt(v):
    return f'{v:#x}'


# ---------------------------------------------------------------- rules
def r_str(R, r, sv, dv, S, T):
    if r['donor_str'] and r['donor_str'] == r['ours_str']:
        return ('STR', 'the same C string at the same offset on both sides',
                f"pin bytes: donor {fmt(sv)} and ours {fmt(dv)} both lie in the NUL-terminated .rodata string "
                f"{r['donor_str']}")


def r_end(R, r, sv, dv, S, T):
    de = set(filter(None, r['donor_end_of'].split(','))) & set(filter(None, r['ours_end_of'].split(',')))
    for n in sorted(de):
        a = [s for s in R.D.syms if s.name == n and s.value + s.size == sv]
        b = [s for s in R.O.syms if s.name == n and s.value + s.size == dv]
        if a and b:
            return ('END', f'the end of {n} on both sides; its size differs',
                    f'symtab: {n} [{fmt(a[0].value)}, {fmt(sv)}) size {fmt(a[0].size)} in the donor, '
                    f'[{fmt(b[0].value)}, {fmt(dv)}) size {fmt(b[0].size)} in ours')


def r_derived(R, r, sv, dv, S, T):
    if r['src_class'] == 'JTREL':
        return None
    e = R.AD.exprs(sv) & R.AO.exprs(dv)
    if e:
        x = sorted(e, key=lambda s: (s.count('-') + s.count('/') + s.count('shadow'), len(s)))[0]
        return ('DERIVED', f'the same image quantity on both sides: {x}',
                f'symtab / section / PT_LOAD bounds: donor {x} = {fmt(sv)}, ours {x} = {fmt(dv)}')


def r_bytes(R, r, sv, dv, S, T):
    sd, so = R.D.section(sv), R.O.section(dv)
    if not sd or not so or sd[2] != so[2] or sd[2] not in ('.rodata', '.data.rel.ro', '.data'):
        return None
    n = min(16, sd[1] - sv, so[1] - dv)
    a, b = R.D.mem(sv, n), R.O.mem(dv, n)
    if n >= 8 and a == b and any(a):
        return ('BYTES', f'the same {sd[2]} data at both values',
                f'pin bytes: the {n} bytes at donor {fmt(sv)} and at ours {fmt(dv)} are equal ({a.hex()})')


def r_ret(R, r, sv, dv, S, T):
    sd = R.D.section(sv)
    if not sd or sd[2] != '.text':
        return None
    a, b = call_desc(R.D, sv), call_desc(R.O, dv)
    if a and b and a[0] == b[0] and a[3] == b[3] and a[4] == b[4]:
        what = 'the return address of a call' if a[0] == 'ret' else 'the pc of a call'
        return ('RET', f'{what} to {a[3].split(":")[-1]}+{fmt(a[4])} on both sides',
                f'instruction decoded from the pin: donor {fmt(a[1])} calls {fmt(a[2])}, ours {fmt(b[1])} calls '
                f'{fmt(b[2])}; both = {a[3].split(":")[-1]}+{fmt(a[4])} in their symtabs')


def r_arith(R, r, sv, dv, S, T):
    df, dl = r['dst'].rsplit(':', 1)
    t = T[int(dl) - 1] if dl and int(dl) <= len(T) else ''
    s = arith(t, dv)
    if s:
        return ('ARITH', 'a number the line computes from its own operands',
                f'{df}:{dl}: `{s[:160]}` holds on ours\' numbers (each operand that names an object has a row of '
                f'its own)')


def r_insn(R, r, sv, dv, S, T):
    """An immediate of the instruction word the same line decodes (`decode_any (0x..%bv : bv 32) = Some (Jal 1 N, 4)`),
    or an instruction encoding passed as a number (`icpt_ld8 .. 14%bv 14%bv 472835`)."""
    df, dl = r['dst'].rsplit(':', 1)
    t = T[int(dl) - 1] if dl and int(dl) <= len(T) else ''
    for m in re.finditer(r'decode_any\s*\((0x[0-9a-fA-F]+)%bv\s*:\s*bv\s*32\)\s*=\s*Some\s*\(([^)]*)\)', t):
        w = int(m.group(1), 16)
        if has_num(m.group(2), dv):
            f = insn_fields(w)
            hit = [k for k, x in f.items() if x == dv]
            if hit:
                return ('INSN', 'an immediate of the instruction word the line decodes, not an address',
                        f'{df}:{dl}: word {m.group(1)} decodes to {hit[0]} = {dv} (`{m.group(0)[:90]}`); the word '
                        f'itself is an instruction-word row of the gate (INSN)')
    if sv == dv and dv < 1 << 32 and insn_text(dv):
        sn = snippet(T, int(dl), dv, 60)
        f = insn_fields(dv)
        m = None
        for num in forms(dv):
            m = m or re.search(r'(\d+)%bv\s+(\d+)%bv\s+' + re.escape(num) + r'(?![\w])', sn)
        regs = m and {int(m.group(1)), int(m.group(2))} <= {f['rd'], f['rs1']}
        if regs or re.search(r'\b(?:icpt|ci|sc)_\w+|\bldR\b|\btbl_sc_ok\b|\binsn\b|\bfetch_word\b', sn):
            why = (f'; its rd / rs1 fields are the two register arguments before it ({m.group(1)}, {m.group(2)})'
                   if regs else '')
            return ('INSN', 'an instruction encoding passed as a number, the same word on both sides',
                    f'{df}:{dl}: `{sn}`; {dv} = {fmt(dv)} encodes {insn_text(dv)}{why}')


# (role, pattern on the text around the numeral, {n} = the numeral): a quantity that is not an address. Used only for
# a numeral that is the SAME on both sides, is no symbol start in the donor and does not lie in a small data object of
# the donor (a pointer would): the object it lands in moved (or is another object) in ours, so an address there
# would have changed with it.
CONST_ROLES = [
    ('the length of a mapping', r'am_len := ELit {n}|\bmk e\d+ {n} KRW|\bPG \d+%nat {n}|\(aMS, mkAF {n}|'
                                r'\bdm e\w+ {n} KRW|KZero \(SA \w+ \d+\) \(ELit {n}\)'),
    ('the length of a zero run (kn_zero / KZ)', r'kn_zero ch \(.*\) \d+ {n}|\bKZ _ \d+%nat \d+ {n}'),
    ('the upper bound of a value range', r'KRange \(EVar \w+\) \S+ {n}|\(EVar \w+\) \d+ {n}\)|0 <= \w+ <= {n}'),
    ('a word a generated hand-off state stores (ELit)', r'\|\} \(ELit {n}\)|\|\} \d+ \(ELit {n}\)|a_eager := {n}'),
    ('a bound of an atom fact (mkAF)', r'mkAF \S+ {n}|mkAF {n}|mkAF \S+ \(\S+ [-+] {n}\)'),
    ('the stretch length argument of do_stretch', r'do_stretch \w+ \d+%nat \S+ {n}'),
    ('a count or fuel (nat / N)', r'{n}%nat|: nat := {n}|{n}%N|FUEL|\birun {n}|pop_batches {n}'),
    ('an immediate of a decoded instruction', r'decode_any [^=]*= Some \(\w+ [^)]*{n}'),
    ('a named size', r'Definition \w*(?:SIZE|LEN|MAX|CAP)\w* : Z := {n}'),
    ('a term of a sum on the line', r'{n} \+ \d|\d \+ {n}\b'),
    ('a length / size bound', r'(?:length|dlen|zlen|size|bv_unsigned|Z\.of_nat|<=\?)[^;]{0,40}{n}|'
                              r'Z\.ltb_spec \(dlen data\) {n}|page_round_up_Z {n}'),
    ('an offset added to a symbolic register value (SOff r N)', r'SOff \w+ {n}'),
    ('an allocation size of a malloc script', r'\b(?:Malloc|Realloc \d+|SP \d+ \d+,)\s*{n}'),
    ('arithmetic on the line', r'(?:\bmod\b|\*|/|\^|zcanon|shiftl|exists \(|mod_pos_bound|mod_divide)[^;]{0,60}{n}|'
                               r'{n}[^;]{0,40}(?:\bmod\b|\*|/)'),
    ('a named model constant', r'(?:MMAP_THRESHOLD|PID_MAX|FS_FROFF|kFake\w+|MALLOC_MAX|CEIL_MAX)[^;]{0,40}{n}'),
    ('an mmap flag word', r'mmap_\w+|ff_class|noreplace_core|flags|\bFLR\b'),
    ('a syscall register value (length / flags)', r'SLit {n}'),
]
DATA_SECS = ('.data', '.bss', '.rodata', '.got', '.data.rel.ro', 'asan_globals', '.init_array', '.fini_array')


def mmap_flags(v):
    """musl MAP_* bits of v when v is a sum of them and nothing else, else None."""
    bits = {0x1: 'SHARED', 0x2: 'PRIVATE', 0x10: 'FIXED', 0x20: 'ANONYMOUS', 0x100: 'GROWSDOWN', 0x4000: 'NORESERVE',
            0x8000: 'POPULATE', 0x100000: 'FIXED_NOREPLACE', 0x20000: 'STACK'}
    out, x = [], v
    for b, n in sorted(bits.items()):
        if x & b:
            out.append(n)
            x &= ~b
    return out if not x and out else None


def r_const(R, r, sv, dv, S, T):
    if sv != dv or R.D.starts.get(sv):
        return None
    d = R.D.resolve(sv)
    if d['cover'] and d['cover'][0].size < 0x10000 and d['sec'] in DATA_SECS:
        return None
    df, dl = r['dst'].rsplit(':', 1)
    sn = snippet(T, int(dl), dv, 60) if dl else ''
    num = next((f for f in forms(dv) if re.search(r'(?<![\w])' + re.escape(f) + r'(?![\w])', sn)), None)
    if not num:
        return None
    n = r'(?<![\w])' + re.escape(num) + r'(?![\w])'
    roles = list(CONST_ROLES)
    if dv in MODEL_CONSTS:
        roles.append((f'the value of the model constant {MODEL_CONSTS[dv]}', r'.'))
    for role, pat in roles:
        if not re.search(pat.replace('{n}', n), sn):
            continue
        fl = mmap_flags(dv) if 'flag word' in role else None
        if 'flag word' in role and not fl:
            continue
        extra = f' (= MAP_{"|MAP_".join(fl)})' if fl else ''
        where = (f'donor {r["donor_symoff"] or "unnamed " + (d["sec"] or "")} / ours '
                 f'{r["ours_symoff"] or "unnamed"}')
        return ('CONST', f'not an address: {role}{extra}; the same numeral on both sides',
                f'{df}:{dl}: `{sn}`; read as an address it would name {where}, not one object+offset: the numeral '
                f'was not relocated, which is right for a quantity')
    return None


MODEL_CONSTS = {}   # value -> 'NAME (lib/Reusable/YG00.v:LINE)': the ASan allocator model's named constants


def load_model_consts(path):
    for i, t in enumerate(text(path), 1):
        for m in re.finditer(r'Definition (\w+) : Z := (0x[0-9a-fA-F]+|\d+)\.', t):
            MODEL_CONSTS.setdefault(int(m.group(2), 0), f'{m.group(1)} (lib/Reusable/{os.path.basename(path)}:{i})')


def r_cell(R, r, sv, dv, S, T):
    """A cell `zN (ANum A) V` / `litN A V` / `val_mem SEGS M A N V` whose V equals ours' image bytes at A."""
    df, dl = r['dst'].rsplit(':', 1)
    t = T[int(dl) - 1] if dl and int(dl) <= len(T) else ''
    pats = [r'\bz([1248])\s*\(ANum\s+(0x[0-9a-fA-F]+|\d+)\)\s+(0x[0-9a-fA-F]+|\d+)',
            r'\blit([1248])\s+(0x[0-9a-fA-F]+|\d+)\s+(0x[0-9a-fA-F]+|\d+)',
            r'\bval_mem\s+\w+\s+(?:\([^()]*(?:\([^()]*\))*[^()]*\)|\w+)\s+(0x[0-9a-fA-F]+|\d+)\s+([1248])\s+(0x[0-9a-fA-F]+|\d+)']
    for k, p in enumerate(pats):
        for m in re.finditer(p, t):
            if k < 2:
                n, a, v = int(m.group(1)), int(m.group(2), 0), int(m.group(3), 0)
            else:
                a, n, v = int(m.group(1), 0), int(m.group(2)), int(m.group(3), 0)
            if dv not in (a, v):
                continue
            b = R.O.mem(a, n)
            if b is not None and int.from_bytes(b, 'little') == v:
                return ('CELL', 'a cell whose stated content is ours\' image bytes',
                        f'{df}:{dl}: `{m.group(0)[:80]}`: the pin holds {fmt(v)} in the {n} bytes at {fmt(a)}')


_XREF = {}


def xrefs(img):
    """address -> pcs of the auipc whose pair (addi / load / store on the auipc's register, within 3 instructions)
    forms that address: a linear sweep of .text in the pin."""
    k = id(img)
    if k in _XREF:
        return _XREF[k]
    out = collections.defaultdict(list)
    hi_out = collections.defaultdict(list)
    lo, hi, _ = next(s for s in img.secs if s[2] == '.text')
    code = img.mem(lo, hi - lo)
    pcs, i = [], 0
    while i + 2 <= len(code):
        h = code[i] | (code[i + 1] << 8)
        n = 4 if h & 3 == 3 else 2
        pcs.append((lo + i, n))
        i += n
    for j, (pc, n) in enumerate(pcs):
        if n != 4:
            continue
        w = struct.unpack_from('<I', code, pc - lo)[0]
        if w & 0x7f != 0x17:
            continue
        rd, hi20 = (w >> 7) & 31, sext(w & 0xfffff000, 32)
        hi_out[(pc + hi20) & ((1 << 64) - 1)].append(pc)
        for pc2, n2 in pcs[j + 1:j + 4]:
            if n2 != 4:
                continue
            w2 = struct.unpack_from('<I', code, pc2 - lo)[0]
            op = w2 & 0x7f
            if op in (0x13, 0x03, 0x07) and (w2 >> 15) & 31 == rd:
                out[(pc + hi20 + sext(w2 >> 20, 12)) & ((1 << 64) - 1)].append(pc)
                break
            if op in (0x23, 0x27) and (w2 >> 15) & 31 == rd:
                out[(pc + hi20 + sext(((w2 >> 25) << 5) | ((w2 >> 7) & 31), 12)) & ((1 << 64) - 1)].append(pc)
                break
    _XREF[k] = out
    _AUIPC[k] = hi_out
    return out


_AUIPC = {}


def r_auipc(R, r, sv, dv, S, T):
    """The intermediate value an auipc forms (pc + its upper immediate), at the same symbol + offset on both sides:
    a walk step's register value (`svx S_.. (Z_to_bv 64 V)`), proof-checked against the instruction."""
    xrefs(R.D), xrefs(R.O)
    a, b = _AUIPC[id(R.D)].get(sv), _AUIPC[id(R.O)].get(dv)
    if not a or not b:
        return None
    common = ref_keys(R.D, a) & ref_keys(R.O, b)
    if common:
        n, o = sorted(common)[0]
        n = n.split(':')[-1]
        return ('AUIPC', f'the value the auipc at {n}+{fmt(o)} forms, on both sides',
                f'auipc decoded from the pins: at {n}+{fmt(o)} the auipc forms donor {fmt(sv)} and ours {fmt(dv)} '
                f'(pc + its upper immediate)')


def ref_keys(img, pcs):
    out = set()
    for pc in pcs:
        r = img.resolve(pc)
        for s in r['cover']:
            out.add((s.key, pc - s.value))
    return out


def r_xref(R, r, sv, dv, S, T):
    """An unnamed data value that the same code references on both sides: the auipc pair at S+o forms v in the donor
    and w in ours (or forms v - k and w - k, a table / constant pool base k bytes below)."""
    sd, so = R.D.section(sv), R.O.section(dv)
    if not sd or not so or sd[2] != so[2] or sd[2] == '.text':
        return None
    XD, XO = xrefs(R.D), xrefs(R.O)
    for k in range(0, 0x200, 1):
        a, b = sv - k, dv - k
        if a < sd[0] or b < so[0]:
            break
        if a in XD and b in XO:
            common = ref_keys(R.D, XD[a]) & ref_keys(R.O, XO[b])
            if common:
                n, o = sorted(common)[0]
                n = n.split(':')[-1]
                where = f'{fmt(a)} / {fmt(b)}' + (f', the values are that address + {fmt(k)}' if k else '')
                return ('XREF', f'the {sd[2]} object the same code references: {n}+{fmt(o)} forms {where}',
                        f'auipc pair decoded from the pins: {n}+{fmt(o)} forms donor {fmt(a)} and ours {fmt(b)}'
                        + (f'; donor {fmt(sv)} = {fmt(a)} + {fmt(k)}, ours {fmt(dv)} = {fmt(b)} + {fmt(k)}' if k else ''))
            if XD.get(a) or XO.get(b):
                break
    return None



# ---------------------------------------------------------------- generated files
def gen_family(f):
    return f[:-2] if f.endswith('.v') else f


def name_syms(img, n):
    """Function symbols a table name stands for: n, _n, __n, or a C++ name with the component n."""
    pat = re.compile(r'\d' + re.escape(n) + r'(E|v|[A-Z0-9]|$)')
    return [s for s in img.syms if s.type == 'STT_FUNC' and (s.name in (n, '_' + n, '__' + n) or pat.search(s.name))]


def sym_end(img, s):
    """st_value + st_size; a symbol of size 0 ends where the next function starts."""
    if s.size:
        return s.value + s.size
    nxt = [x.value for x in img.syms if x.type == 'STT_FUNC' and x.value > s.value]
    return min(nxt) if nxt else s.value


def r_named(R, r, sv, dv, S, T):
    """A table row whose definition names a function: tfib_A_<f> / src0_A_<f> is its start, tfib_E_<f> /
    src0_E_<f> its end (a size-0 symbol ends at the next function). OK when ours is that value in our symtab;
    a FINDING (code) when it is not."""
    m = re.match(r'Definition (?:tfib|src0)_([AE])_(\w+)', r['sentence'])
    if not m:
        return None
    end, n = m.group(1) == 'E', m.group(2)
    want = lambda img, s: sym_end(img, s) if end else s.value
    what = 'end' if end else 'start'
    os_ = name_syms(R.O, n)
    hit = [s for s in os_ if want(R.O, s) == dv]
    if hit:
        s = hit[0]
        return ('NAMED', f'table row: ours is the {what} of {n}, the function the definition names',
                f'ours symtab: {s.name} [{fmt(s.value)}, {fmt(sym_end(R.O, s))}); the row value {fmt(dv)}')
    ds = [s for s in name_syms(R.D, n) if want(R.D, s) == sv]
    if not ds:
        return None
    if os_:
        s = os_[0]
        return ('NAMED', f'table row names {n}; ours is not its {what}',
                f'ours symtab: {s.name} [{fmt(s.value)}, {fmt(sym_end(R.O, s))}), so {r["sentence"].split()[-1]} '
                f'should be {fmt(want(R.O, s))}; the file has {fmt(dv)} ({r["ours_symoff"] or "unnamed"}); the '
                f'donor value {fmt(sv)} is the {what} of {ds[0].name} in the donor twin',
                'FINDING', 'code', fmt(want(R.O, s)), '')
    return ('NAMED', f'table row names {n}, a function our image does not have',
            f'donor twin: {ds[0].name} {what} = {fmt(sv)}; ours symtab has no {n} / _{n} / __{n} function; the file '
            f'has {fmt(dv)} ({r["ours_symoff"] or "unnamed"})', 'FINDING', 'code', f'none (no {n} in ours)', '')

_REGIONS = {}


def regions(R):
    """region name -> (lo, hi, [(chunk start, length)]) of our generated AD2j.v / YD2j.v (beside the dst files)."""
    if R.ddir in _REGIONS:
        return _REGIONS[R.ddir]
    out = {}
    for f in ('AD2j.v', 'YD2j.v'):
        t = '\n'.join(text(os.path.join(R.ddir, f)))
        for m in re.finditer(r'Definition (R_\w+) : region :=\s*mkRegion None (\d+) (\d+) \d+ \d+\s*\[(.*?)\]\.', t, re.S):
            ch = [(int(a), int(n)) for a, n in re.findall(r'mkChunk (\d+) \(CImg (\d+)\)', m.group(4))]
            out[m.group(1)] = (int(m.group(2)), int(m.group(3)), ch, f)
    _REGIONS[R.ddir] = out
    return out


def r_region(R, r, sv, dv, S, T):
    """`R_X A N` on the line (a chunk reference: `CH R_X A N`, `img_rd_of_mem_ok .. R_X A N`): (A, N) is a chunk of
    region R_X in our generated AD2j.v / YD2j.v (or its whole span)."""
    df, dl = r['dst'].rsplit(':', 1)
    t = T[int(dl) - 1] if dl and int(dl) <= len(T) else ''
    rg = regions(R)
    for m in re.finditer(r'\b(R_\w+)\s+(0x[0-9a-fA-F]+|\d+)\s+(0x[0-9a-fA-F]+|\d+)', t):
        name, a, n = m.group(1), int(m.group(2), 0), int(m.group(3), 0)
        if dv not in (a, n) or name not in rg:
            continue
        lo, hi, ch, f = rg[name]
        if (a, n) in ch or (a, n) == (lo, hi - lo):
            return ('REGION', f'a chunk of region {name} of our generated {f}',
                    f'{df}:{dl}: `{m.group(0)}`; {f} (generated from our image) has {name} = mkRegion {lo} {hi} with '
                    f'chunk ({a}, {n})')
    return None


A_IMGS = {}   # 'D' / 'O' -> the A images (cgif asan twin, our asan twin), set by main
LABEL_CTX = r'(?:\bmcheck\b|\bspin\b|\bISpin\b|\bFCheck\b|\bend\b)[^;]*?{n}'


def r_label(R, r, sv, dv, S, T):
    """A check-site label (`mcheck (..) N`, `spin N`, `FCheck N`, `ISpin N`): an opaque name that the unit keeps
    as the ASan (A) image's pc of the check site, in every file. Resolved in the two A images it is the same
    symbol + offset."""
    df, dl = r['dst'].rsplit(':', 1)
    t = T[int(dl) - 1] if dl and int(dl) <= len(T) else ''
    sn = snippet(T, int(dl), dv, 70) if dl else ''
    num = next((f for f in forms(dv) if re.search(r'(?<![\w])' + re.escape(f) + r'(?![\w])', t)), None)
    if not num or not re.search(LABEL_CTX.replace('{n}', r'(?<![\w])' + re.escape(num) + r'(?![\w])'), t):
        return None
    D, O = A_IMGS.get('D'), A_IMGS.get('O')
    if not D:
        return None
    common = D.resolve(sv)['cands'] & O.resolve(dv)['cands']
    if common:
        k, o = sorted(common, key=lambda x: x[0].startswith(('sec', 'load')))[0]
        return ('LABEL', f'a check-site label: the A images\' pc of the same site, {k.split(":")[-1]}+{fmt(o)}',
                f'{df}:{dl}: `{sn}`; in the asan twins (cgif 488e39500746, ours 68db792d5fa7) donor {fmt(sv)} and '
                f'ours {fmt(dv)} are both {k.split(":")[-1]}+{fmt(o)}')


RULES = [r_str, r_end, r_named, r_derived, r_xref, r_auipc, r_bytes, r_ret, r_insn, r_cell, r_region, r_label,
         r_const, r_arith]


def r_genset(R, r, sv, dv, S, T, sets):
    if sets is None:
        return None
    src_set, dst_set = sets
    sf = r['src'].rsplit(':', 1)[0]
    oc = R.O.resolve(dv)['cands']
    hit = oc & src_set.get((sf, r['sentence']), set())
    if hit:
        k, o = sorted(hit)[0]
        return ('GENSET', f'generated table, another order: ours names {k.split(":")[-1]}+{fmt(o)}, which the '
                          f'donor\'s same definition also names',
                f'symtab: ours {fmt(dv)} = {k.split(":")[-1]}+{fmt(o)}; the donor\'s {r["sentence"]} holds a value '
                f'that is {k.split(":")[-1]}+{fmt(o)} in the donor twin')


def build_sets(tsv, R):
    """(src file, sentence) -> candidates of every donor value of a generated file; the same for ours."""
    S, D = collections.defaultdict(set), collections.defaultdict(set)
    gen = GEN_A | GEN_B
    cs, cd = {}, {}
    with open(tsv) as f:
        for ln in f:
            if ln.startswith('#'):
                continue
            g = ln.rstrip('\n').split('\t')
            if len(g) < 16 or g[0] == 'verdict' or g[9] == 'ident' or g[12] == 'INSN':
                continue
            if gen_family(g[3]) in gen and g[10]:
                v = int(g[10], 16)
                if v not in cs:
                    cs[v] = R.D.resolve(v)['cands'] if R.D.inload(v) else set()
                S[(g[3], g[7])].update(cs[v])
            if gen_family(g[5]) in gen and g[11]:
                v = int(g[11], 16)
                if v not in cd:
                    cd[v] = R.O.resolve(v)['cands'] if R.O.inload(v) else set()
                D[(g[5], g[7])].update(cd[v])
    return S, D


# ---------------------------------------------------------------- hand decisions
def load_hand(path):
    out = []
    if not os.path.exists(path):
        return out
    with open(path) as f:
        h = f.readline().rstrip('\n').split('\t')
        for ln in f:
            if not ln.strip() or ln.startswith('#'):
                continue
            d = dict(zip(h, ln.rstrip('\n').split('\t')))
            d['_run'] = re.compile(d['run'])
            d['_dst'] = re.compile(d['dst'])
            d['_used'] = 0
            out.append(d)
    return out


CONTROL_OF = {'PA-base': 'RA', 'PA-plant': 'RA', 'PB-base': 'RB', 'PB-plant': 'RB'}   # a control is judged as its run


def hand_match(H, r):
    run = CONTROL_OF.get(r['run'], r['run'])
    for d in H:
        if not d['_run'].fullmatch(run) or not d['_dst'].fullmatch(r['dst']):
            continue
        if d['src_value'] not in ('*', r['src_value']) or d['dst_value'] not in ('*', r['dst_value']):
            continue
        d['_used'] += 1
        return d
    return None


# ---------------------------------------------------------------- main
def env(k, d):
    return os.environ.get(k, d)


def make_runs():
    IMG, PIMG = env('IMG', '$W/img'), env('PIMG', 'work/img')
    RTIMG, RTW = env('RTIMG', '$W/rt-reusable/work/img'), env('RTW', '$W/rt-reusable/work/rt')
    CG = env('CG', '$DONOR/proofs/cgif/cgif_file_fuzzer/lib')
    CM = env('CM', '$OURS/proofs/plugin-hostd/fuzz_command/lib')
    PLANT = env('PLANT', '$W/plant')
    imgs = {}

    def I(d, n):
        if n not in imgs:
            imgs[n] = sweep.Img(f'{d}/{n}.pin', f'{d}/{n}.twin')
        return imgs[n]
    spec = {
        'RA': (lambda: I(IMG, 'cgif.A'), lambda: I(IMG, 'cmd.A'), f'{CG}/A', f'{CM}/A'),
        'RB': (lambda: I(IMG, 'cgif.B'), lambda: I(IMG, 'cmd.B'), CG, f'{CM}/B'),
        'RU': (lambda: I(IMG, 'cgif.B'), lambda: I(IMG, 'cmd.B'), CG, f'{CM}/Reusable'),
        'RU-P': (lambda: I(PIMG, 'cgif.P'), lambda: I(PIMG, 'cmd.P'), CG, f'{CM}/Reusable'),
        'RUP': (lambda: I(PIMG, 'cgif.P'), lambda: I(PIMG, 'cmd.P'), CG, f'{CM}/Reusable'),
        'RtCgifA': (lambda: I(IMG, 'cgif.A'), lambda: I(IMG, 'cmd.A'), f'{RTW}/RtCgifA/src', f'{RTW}/RtCgifA/dst'),
        'RtCgifB': (lambda: I(IMG, 'cgif.B'), lambda: I(IMG, 'cmd.B'), f'{RTW}/RtCgifB/src', f'{RTW}/RtCgifB/dst'),
        'RtDisco': (lambda: I(RTIMG, 'disco.A'), lambda: I(IMG, 'cmd.A'), f'{RTW}/RtDisco/src', f'{RTW}/RtDisco/dst'),
        'RtGrant': (lambda: I(RTIMG, 'grant.A'), lambda: I(IMG, 'cmd.A'), f'{RTW}/RtGrant/src', f'{RTW}/RtGrant/dst'),
        'RtPreset': (lambda: I(RTIMG, 'presetR.A'), lambda: I(IMG, 'cmd.A'), f'{RTW}/RtPreset/src',
                     f'{RTW}/RtPreset/dst'),
        'RtRelay': (lambda: I(IMG, 'cmd.A'), lambda: I(IMG, 'cmd.B'), f'{CM}/A/Rt', f'{CM}/B/Rt'),
        'PA-base': (lambda: I(IMG, 'cgif.A'), lambda: I(IMG, 'cmd.A'), f'{CG}/A', f'{PLANT}/A-base'),
        'PA-plant': (lambda: I(IMG, 'cgif.A'), lambda: I(IMG, 'cmd.A'), f'{CG}/A', f'{PLANT}/A-plant'),
        'PB-base': (lambda: I(IMG, 'cgif.B'), lambda: I(IMG, 'cmd.B'), CG, f'{PLANT}/B-base'),
        'PB-plant': (lambda: I(IMG, 'cgif.B'), lambda: I(IMG, 'cmd.B'), CG, f'{PLANT}/B-plant'),
    }
    runs = {}

    def get(n):
        if n not in runs:
            d, o, s, t = spec[n]
            runs[n] = Run(n, d(), o(), s, t)
        return runs[n]
    return get


GEN_TSV = {'RA': 'RA', 'RB': 'RB'}


def triage_row(R, r, H, sets):
    sv, dv = int(r['src_value'], 16), int(r['dst_value'], 16)
    sf, sl = r['src'].rsplit(':', 1)
    df, dl = r['dst'].rsplit(':', 1)
    S, T = R.src_lines(sf), R.dst_lines(df)
    if r['src_class'] == 'JTREL':
        m = re.match(r'jt-target (0x[0-9a-f]+) \(base [^)]*\) / (0x[0-9a-f]+)', r['basis'])
        if m:
            sv, dv = int(m.group(1), 16), int(m.group(2), 16)
    for rule in RULES:
        x = rule(R, r, sv, dv, S, T)
        if x:
            return x
    if gen_family(df) in GEN_A | GEN_B:
        x = r_genset(R, r, sv, dv, S, T, sets)
        if x:
            return x
        hdr = ' '.join(l for l in T[:8] if 'generat' in l.lower() or 'collected' in l.lower())
        m = re.search(r'[^.;]*(?:[Gg]enerated|regenerated|collected)[^.;]*', hdr)
        if m:
            o = r['ours_symoff'] or ('unnamed ' + (r['ours_sec'] if 'ours_sec' in r else ''))
            return ('GENERATED', 'a row of a file written from our image by its generator: the pair is a positional '
                                 'pairing of two different tables, and ours names an object of our image',
                    f'{df} header: "{" ".join(m.group(0).split())[:150]}"; ours {fmt(dv)} = {o}; no donor entry of the '
                    f'same definition names it')
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--rows', default='rows.tsv')
    ap.add_argument('--ru-plain', default='work/rows.RU-P.tsv')
    ap.add_argument('--portera', default='work/portera.files', help="lib/Reusable's files added by the port (ASan models)")
    ap.add_argument('--hand', default='hand.tsv')
    ap.add_argument('--runs-dir', default=env('RUNS', '$W/runs'))
    ap.add_argument('--out', default='mismatches.tsv')
    ap.add_argument('--adjacent', default='adjacent.tsv',
                    help="rows of lib/Reusable's pre-port files (not port_core outputs): measured, out of scope")
    a = ap.parse_args()
    get = make_runs()
    A_IMGS['D'], A_IMGS['O'] = get('RA').D, get('RA').O
    load_model_consts(os.path.join(env('CM', '$OURS/proofs/plugin-hostd/fuzz_command/lib'),
                                   'Reusable', 'YG00.v'))
    H = load_hand(a.hand)
    rows = rows_of(a.rows)
    plain = {key(r): r for r in rows_of(a.ru_plain)} if os.path.exists(a.ru_plain) else {}
    portera = set(open(a.portera).read().split()) if os.path.exists(a.portera) else set()
    sets = {}
    out, adj, tally = [], [], collections.Counter()
    for r in rows:
        if r['status'] == 'SAME':
            continue
        R, row, pre = get(r['run']), r, ''
        df = r['dst'].rsplit(':', 1)[0]
        if r['run'] == 'RU' and df not in portera:
            p = plain.get(key(r))
            pre = ('lib/Reusable pre-port file (it describes the plain build, Images.plain): the pair resolved in '
                   'the plain images ' + img_name(get('RU-P').D) + ' / ' + img_name(get('RU-P').O) + ': ')
            if p is None:
                x = ('PLAIN', pre + 'not checked there',
                     f'the donor value {r["src_value"]} lies outside every PT_LOAD of the plain donor image (or is a '
                     f'size by name): no address of the image the file describes')
                row, R = r, None
            elif p['status'] == 'SAME':
                x = ('PLAIN', pre + f'SAME ({p["basis"]})',
                     f'plain twin symtabs: donor {p["donor_symoff"]}, ours {p["ours_symoff"]}')
                R = None
            else:
                row, R = p, get('RU-P')
        elif r['run'] == 'RUP' and df in portera:
            x = ('IMAGE', 'lib/Reusable file added by the port (an ASan model file, not the plain build): the plain images are '
                          'not its image; its pairs are judged in run RU (images B)',
                 f'{df} is one of the 140 lib/Reusable files the port commit 6b559e1f018 added; run RU holds the same '
                 f'pair resolved in the B images')
            R = None
        if R is not None:
            d = hand_match(H, row)
            if d:
                x = ('HAND', d['reason'], d['measurement'], d['result'], d['finding_kind'], d['new_value'],
                     d['read_by'])
            else:
                gf = gen_family(df)
                st = None
                if gf in GEN_A | GEN_B and row['run'] in GEN_TSV:
                    if row['run'] not in sets:
                        sets[row['run']] = build_sets(f"{a.runs_dir}/{GEN_TSV[row['run']]}/full.tsv", R)
                    st = sets[row['run']]
                x = triage_row(R, row, H, st)
                if x and pre:
                    x = (x[0], pre + x[1]) + tuple(x[2:])
        if not x:
            x = ('NONE', '', '', 'OPEN', '', '', '')
        x = tuple(x) + ('OK', '-', '', '-')[len(x) - 3:] if len(x) < 7 else tuple(x)
        rule, reason, meas, res, kind, new, rb = x
        o = [r['run'], r['src'], r['dst'], r['sentence'], r['src_value'], r['dst_value'], r['donor_symoff'],
             r['ours_symoff'], r['status'], rule, reason, meas, res, kind, new, rb]
        if r['run'] in ('RU', 'RUP') and df not in portera:
            o[12] = 'OUT-OF-SCOPE-PREPORT'
            adj.append(o + [res])
            tally[(r['run'], rule, 'PREPORT-' + res)] += 1
            continue
        tally[(r['run'], rule, res)] += 1
        out.append(o)
    for path, rows_out, cols in ((a.out, out, COLS), (a.adjacent, adj, COLS + ['measured'])):
        with open(path, 'w') as f:
            f.write('\t'.join(cols) + '\n')
            for o in rows_out:
                f.write('\t'.join(str(c).replace('\t', ' ') for c in o) + '\n')
    for (run, rule, res), n in sorted(tally.items()):
        print(f'{run}\t{rule}\t{res}\t{n}')
    unused = [d for d in H if not d['_used']]
    if unused:
        print(f'hand.tsv: {len(unused)} entries matched no row', file=sys.stderr)


if __name__ == '__main__':
    main()
