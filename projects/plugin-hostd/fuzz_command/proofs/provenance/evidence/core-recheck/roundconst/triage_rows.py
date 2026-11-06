#!/usr/bin/env python3
"""Triage of every non-SAME row of the v2 by-value gate (roundconst.py 32b39f3b34e9) on plugin-hostd/fuzz_command.

A gate row is a numeral the port KEPT (donor value = ported value; for --moved rows: a SAME-GEOMETRY numeral the port
changed) whose value equals a cgif image quantity whose fuzz_command counterpart differs (the row's DIFFERING NAMES).
The question per row (README gap 5): is the numeral that quantity (a kept donor quantity: FINDING) or a value with
another role (a coincidence: OK)? Each row gets the first rule below that settles it; every rule measures something
(image bytes, symbol tables, segment headers, the unit's own text) and the measurement is written out per row.

Global measurement used by the run-time rules (printed in the README): every function both images have under one name
has the same size in cgif and fuzz_command except LLVMFuzzerTestOneInput (asan 1400 of 1401, asan-ubsan 1400 of 1401,
plain 123 of 124), so a quantity of the sanitizer run-time or of musl (a stack frame, a code offset, a structure field
offset, an allocator constant) is the same number in both images; the image LAYOUT (segment, section, object
placement) is what differs, and that is what the differing names are.

Rules, in order:
  COLLECTED_STATE    lib/A/AB01.v, AB03.v, lib/B/YB01.v, YB03.v: the whole file is the start-up checker's collected
                     states over fuzz_command's image (file header); no port_core value.
  FETCH_WORD_AT      `fetch_word segs (SYM + N) = Some (0xW)`: the image word at SYM+N is W (image bytes).
  FUNC_OFFSET        `SYM + N` with SYM a function start of the unit's row table: SYM+N is inside that function
                     in the image's .symtab.
  BUILD_TABLE_RANGE  `build_table segs START N`: START + 4N is the end of a function in the image's .symtab.
  MOVED_TO_SEGMENT   (--moved rows) the port's value is fuzz_command's own PT_LOAD page length (program headers).
  CELL_STARTUP       `z8 (ANum ADDR) N` of lib/A/AF0m.v / lib/B/YF0m.v: the collected start-up state of AB01/YB01
                     writes N at ADDR.
  PAGE_SIZE          4096 = p_align of every PT_LOAD of both images, not halved in its text.
  BYTE_ARITH         256 = 2^8 in a sentence that does 8-bit arithmetic.
  ARITH_EQ           the numeral is the value of the expression its sentence rewrites (unit definitions
                     substituted), or an operand of a literal identity the sentence checks.
  VAR_INDEX / INDEX / EXPONENT   the numeral's own text makes it a variable / register / atom index or an exponent.
  RT_OFFSET          an offset from a run-time base of the allocator / stack / shadow / thread model (the base's
                     definition is named); with the code-identity measurement.
  RT_CONST           the value of a named run-time constant (stack windows, buffer size, size class ...).
  SYMLIT             a literal of a symbolic register / expression value (SLit / ELit / escale / w64) below the
                     image base or a power of two.
  KERNEL_CHECKED     the statement is closed by `vm_compute. reflexivity.` (fail-loud: a wrong value fails the build).
  HAND_*             one-family readings with their own measurement (see HANDLERS).
  NOT_FLAGGED_QTY    the value is below the image base and nothing in its text ties it to the differing quantities:
                     the sentence holds no bound address / object name of them (donor or target), the numeral has no
                     table / length / slice role, no image identifier or image-address literal is within two tokens,
                     and no x k / / k of a quotient name is next to it.
usage: triage_rows.py --unit-lib DIR --img DIR --pimg DIR --main DIR --in DIR --pac PY --v2 PY --out DIR"""
import argparse, bisect, collections, gzip, importlib.util, os, re, sys
from elftools.elf.elffile import ELFFile

ap = argparse.ArgumentParser()
for a in ('unit-lib', 'img', 'pimg', 'main', 'in', 'pac', 'v2', 'out'):
    ap.add_argument('--' + a, required=True)
A = ap.parse_args()
OUT = A.out
os.makedirs(OUT, exist_ok=True)

# ---------------------------------------------------------------- tools of record (loaded, not re-implemented)
spec = importlib.util.spec_from_file_location('pac', A.pac)
pac = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pac)
src = open(A.v2).read()
g2 = {'__name__': 'gate'}
exec(compile(src[:src.index('\ntsv, dspec, tspec, pre = sys.argv[1:5]')], A.v2, 'exec'), g2)

IMGS = {'dA': ('cgif.A.pin', 'cgif.A.twin'), 'tA': ('cmd.A.pin', 'cmd.A.twin'), 'dB': ('cgif.B.pin', 'cgif.B.twin'),
        'tB': ('cmd.B.pin', 'cmd.B.twin'), 'dP': ('cgif.P.pin', 'cgif.P.twin'), 'tP': ('cmd.P.pin', 'cmd.P.twin')}
ROLE = {'dA': 'cgif_file_fuzzer.asan 7093581aab04', 'tA': 'fuzz_command.asan c0661b96b5bd',
        'dB': 'cgif_file_fuzzer.asan-ubsan 1c29845fe605', 'tB': 'fuzz_command.asan-ubsan bbe55d24d096',
        'dP': 'cgif_file_fuzzer.plain 19dedd1bc682', 'tP': 'fuzz_command.plain a20873dc7f0e'}


def path(k, i):
    return os.path.join(A.pimg if k.endswith('P') else A.img, IMGS[k][i])


GEO = {k: g2['geometry'](path(k, 0) + ':' + path(k, 1)) for k in ('dA', 'tA', 'dB', 'tB', 'dP', 'tP')}
LOADS, SECS, SYMS, SEGBYTES = {}, {}, {}, {}
for k in IMGS:
    e = ELFFile(open(path(k, 0), 'rb'))
    LOADS[k] = [(s['p_vaddr'], s['p_memsz'], s['p_filesz'], s['p_align']) for s in e.iter_segments()
                if s['p_type'] == 'PT_LOAD']
    SEGBYTES[k] = [(s['p_vaddr'], s['p_filesz'], s.data()) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
    SECS[k] = {s.name: (s['sh_addr'], s['sh_addr'] + s['sh_size']) for s in e.iter_sections()
               if s['sh_addr'] and s['sh_flags'] & 2}
    st = ELFFile(open(path(k, 1), 'rb')).get_section_by_name('.symtab')
    SYMS[k] = sorted((s['st_value'], s.name, s['st_size'], s['st_info']['type']) for s in st.iter_symbols()
                     if s.name and s['st_value'] and s['st_shndx'] != 'SHN_UNDEF')
FIRST = {k: {} for k in SYMS}
for k in SYMS:
    for a, n, sz, t in SYMS[k]:
        FIRST[k].setdefault(n, (a, sz, t))
FSTART = {k: {a for a, n, sz, t in SYMS[k] if t == 'STT_FUNC'} for k in SYMS}
FEND = {k: {a + sz for a, n, sz, t in SYMS[k] if t == 'STT_FUNC' and sz} for k in SYMS}


def read_word(k, addr):
    for va, fs, d in SEGBYTES[k]:
        if va <= addr and addr + 4 <= va + fs:
            return int.from_bytes(d[addr - va:addr - va + 4], 'little')
    return None


def containing(k, addr, types=('STT_FUNC',)):
    best = None
    for a, n, sz, t in SYMS[k]:
        if t in types and a <= addr < a + max(sz, 1) and (best is None or a > best[1]):
            best = (n, a, sz)
    return best


def code_identity(dk, tk):
    def funcs(k):
        f = collections.defaultdict(list)
        for a, n, sz, t in SYMS[k]:
            if t == 'STT_FUNC' and not n.startswith('$'):
                f[n].append(sz)
        return f
    fd, ft = funcs(dk), funcs(tk)
    both = [n for n in fd if len(fd[n]) == 1 and len(ft.get(n, [])) == 1]
    diff = sorted(n for n in both if fd[n][0] != ft[n][0])
    return len(both), len(both) - len(diff), diff


CODE_ID = {key: code_identity('d' + key, 't' + key) for key in ('A', 'B', 'P')}
P_ALIGN = {LOADS[k][i][3] for k in ('dA', 'tA', 'dB', 'tB') for i in range(len(LOADS[k]))}
assert P_ALIGN == {0x1000}, P_ALIGN
PAGE = 0x1000
IMG_LO, IMG_HI = 0x10000, max(max(va + mz for va, mz, fz, al in LOADS[k]) for k in ('tA', 'tB'))

# ---------------------------------------------------------------- the unit's text
SIDE = {'rc-A': 'A', 'mv-A': 'A', 'rc-B': 'B', 'mv-B': 'B', 'rc-U': 'Reusable', 'mv-U': 'Reusable',
        'rc-UP': 'Reusable', 'mv-UP': 'Reusable'}
# the image key of each gate run: RU is keyed B in the run of record; rc-UP / mv-UP are the extra plain-keyed runs
RUNKEY = {'rc-A': 'A', 'mv-A': 'A', 'rc-B': 'B', 'mv-B': 'B', 'rc-U': 'B', 'mv-U': 'B', 'rc-UP': 'P', 'mv-UP': 'P'}
TIMG = {'A': 'tA', 'B': 'tB', 'Reusable': 'tP'}       # the image a side's proofs describe (Reusable: src0 = plain)
COLLECTED = {'AB01', 'AB03', 'YB01', 'YB03'}
_sent, _text = {}, {}


def text(side, fn):
    if (side, fn) not in _text:
        _text[(side, fn)] = open(os.path.join(A.unit_lib, side, fn), encoding='utf-8', errors='replace').read()
    return _text[(side, fn)]


def sents(side, fn):
    if (side, fn) not in _sent:
        _sent[(side, fn)] = pac.sentences(text(side, fn))
    return _sent[(side, fn)]


DEFN = re.compile(r"Definition\s+([A-Za-z_][\w']*)\s*(?::\s*[ZN]\s*)?:=\s*(0x[0-9a-fA-F]+|\d+)\s*(?:%[ZN])?\s*\.")
UD = {}
for side in ('A', 'B', 'Reusable'):
    d = {}
    for fn in sorted(os.listdir(os.path.join(A.unit_lib, side))):
        if fn.endswith('.v'):
            for m in DEFN.finditer(text(side, fn)):
                d.setdefault(m.group(1), int(m.group(2), 16 if m.group(2).startswith('0x') else 10))
    UD[side] = d
for side in ('A', 'B'):
    for k_, v_ in UD['Reusable'].items():
        UD[side].setdefault(k_, v_)
ROWDEF = {}     # the unit's row tables: SYM -> start, SYM_E -> end (lib/A/AB1w.v, lib/B/YB1w.v, Reusable/YH03.v)
for side, fn in (('A', 'AB1w.v'), ('B', 'YB1w.v'), ('Reusable', 'YH03.v')):
    ROWDEF[side] = {m.group(1): int(m.group(2), 16 if m.group(2).startswith('0x') else 10)
                    for m in DEFN.finditer(text(side, fn))}


def ctx(y):
    return y.ctx_long.replace('\n', ' '), y.ctx_after.replace('\n', ' ')


# ---------------------------------------------------------------- differing names and their anchors
def inv(key):
    D, DC = GEO['d' + key]
    out = collections.defaultdict(list)
    for nm, v in D.items():
        if v >= 0x100 or DC[nm] != 'span':
            out[v].append(nm)
    return out


INV = {'A': inv('A'), 'B': inv('B'), 'P': inv('P')}


def differing(key, v, moved=False):
    D, DC = GEO['d' + key]
    T, TC = GEO['t' + key]
    out = []
    for nm in INV[key].get(v, []):
        t = T.get(nm)
        if moved or (t is not None and t != v):
            out.append((nm, DC[nm], t))
    return out


def anchors(key, nm):
    adr, words = set(), set()
    base = re.sub(r'/\d+$', '', nm)
    for side in ('d', 't'):
        k = side + key
        L, S, F = LOADS[k], SECS[k], FIRST[k]

        def bnd(b):
            m = re.match(r'PT_LOAD(\d+)\.(lo|hi|plo|phi)$', b)
            if m:
                va, mz, fz, al = L[int(m.group(1))]
                lo, hi = va, va + mz
                return {'lo': lo, 'hi': hi, 'plo': lo & ~0xfff, 'phi': (hi + 0xfff) & ~0xfff}[m.group(2)]
            m = re.match(r'(.*)\.(lo|hi)$', b)
            if m and m.group(1) in S:
                return S[m.group(1)][0 if m.group(2) == 'lo' else 1]
            return None
        m = re.match(r'PT_LOAD(\d+)\.(memsz|filesz|pagelen)$', base)
        if m:
            va, mz, fz, al = L[int(m.group(1))]
            adr |= {va, va + mz, va + fz, va & ~0xfff, (va + mz + 0xfff) & ~0xfff}
            continue
        m = re.match(r'span\(([^,]+),([^)]+)\)$', base)
        if m:
            adr |= {x for x in map(bnd, m.groups()) if x is not None}
            continue
        m = re.match(r'sym\((.+)\)\.(size|extent)$', base)
        if m:
            words.add(m.group(1))
            if m.group(1) in F:
                a, sz, _ = F[m.group(1)]
                adr |= {a, a + sz}
            continue
        m = re.match(r'run\((.+)\+(\d+)\.\.(.+)\)\.extent$', base)
        if m:
            words |= {m.group(1), m.group(3)}
            if m.group(1) in F:
                adr.add(F[m.group(1)][0] + int(m.group(2)))
            if m.group(3) in F:
                adr.add(F[m.group(3)][0])
            continue
        m = re.match(r'(\..+)\.size$', base)
        if m:
            words.add(m.group(1).lstrip('.'))
            adr |= set(S.get(m.group(1), ()))
            continue
        if base.startswith('image.'):
            adr.add(max((va + mz + 0xfff) & ~0xfff for va, mz, fz, al in L))
    w2 = set()
    for w in words:
        w2.add(w)
        if '.' in w:
            w2 |= set(w.split('.'))
    return adr, {w for w in w2 if len(w) >= 3 and w != 'rel'}


def anchors_of(key, dis):
    a, w = set(), set()
    for nm, c, t in dis:
        x, y = anchors(key, nm)
        a |= x
        w |= y
    return a, w


def dis_text(dis):
    if not dis:
        return 'no differing name'
    parts = [f'{nm} (fuzz_command {hex(t) if t is not None else "none"})' for nm, c, t in dis if not nm.startswith('span')]
    ns = sum(1 for nm, c, t in dis if nm.startswith('span'))
    return '; '.join(parts[:3]) + (f' +{len(parts) - 3}' if len(parts) > 3 else '') + (f' +{ns} spans' if ns else '')

# ---------------------------------------------------------------- rule helpers
TOK = re.compile(r"0x[0-9a-fA-F]+|\d+|[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*|\S")
IDT = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*")
TABLE_WORDS = re.compile(r'(_len|_cnt|_count|_size|_sz|_bytes|_pad|_padding|_entries|_entry|_tab|_table|_words|'
                         r'_nwords|_nelem|_rows|_slots|_classes|len|count|size|words)\b', re.I)
IMGID = re.compile(r'^((tfib|src0|cmd|cgif)_[AB]_\w+|\w*(IMG|img|SEG|seg|Seg|_rw|rw_|ro_|RO_|RW_|_len|extent|EXTENT|top|'
                   r'TOP|PT_LOAD|rodata|RODATA|text_lo|text_hi|bss|BSS|data_lo|data_hi|got|GOT|relro|RELRO)\w*)$')


def is_pow2(x):
    return x > 0 and x & (x - 1) == 0


def table_role(b):
    bt = b.rstrip()
    m = re.search(r'Definition\s+(\w+)\s*(?::[^=]*)?:=\s*$', bt)
    if m and TABLE_WORDS.search(m.group(1)):
        return f'Definition {m.group(1)} := N'
    if re.search(r'\b(length|Z\.of_nat\s*\(\s*length)\b[^=<>]*(=|<=|<)\s*$', bt):
        return 'length .. = N'
    if re.search(r'\bseg\s+\w+\s+\d+\s*$', bt) or re.search(r'\bseg\s+\w+\s*$', bt):
        return 'seg TABLE OFFSET LENGTH'
    if re.search(r'\b(firstn|skipn|nth|nth_error|seq|zseq|repeat)\s*$', bt):
        return 'list slice / index'
    if re.search(r'\bCImg\s*$', bt):
        return 'image chunk word count'
    return None


def not_quantity(v, b, a, snums, sids, adr, words, divisors):
    hits = sorted(x for x in snums if x in adr)
    wh = sorted(words & sids)
    if hits or wh:
        return False, 'TIE: sentence holds ' + ', '.join([hex(x) for x in hits] + wh)
    tr = table_role(b)
    if tr:
        return False, 'TABLE role: ' + tr
    near = TOK.findall(b)[-3:] + TOK.findall(a)[:3]
    for t in near:
        if t[0].isalpha() or t[0] == '_':
            if IMGID.match(t):
                return False, f'image identifier next to it: {t}'
        elif t[0].isdigit():
            x = int(t, 16) if t.startswith('0x') else int(t)
            if IMG_LO <= x < IMG_HI and (t.startswith('0x') or not is_pow2(x)):
                return False, f'image-address literal next to it: {t}'
    for k in divisors:
        if re.search(rf'(\b{k}\s*\*\s*\(?|/\s*{k}\b[^,;]{{0,12}})$', b.rstrip()) or re.match(rf'\s*\)?\s*(\*|/)\s*{k}\b', a):
            return False, f'scaled by {k} next to it'
        if k == 4096 and re.search(r'page', ' '.join(near), re.I):
            return False, 'page word next to it'
    return True, ('the sentence holds no bound address or object name of the differing quantities (cgif or '
                  'fuzz_command), no table/length/slice role, no image identifier or image-address literal within two '
                  'tokens' + (f', not scaled by {"/".join(map(str, divisors))} next to it' if divisors else ''))


ARITH = re.compile(r'^[\d\s+\-*/()^]+$|^[\d\s+\-*/()^]*\bmod\b[\d\s+\-*/()^]*$')


def ev(expr, side):
    s = re.sub(r'Z\.of_(N|nat)\s+(\d+)', r'\2', expr)
    s = re.sub(r'%(Z|N|nat)', '', s)
    for _ in range(2):
        s = re.sub(r'Z\.of_(N|nat)\s*\(([^()]*)\)', r'(\2)', s)
    s = re.sub(r"[A-Za-z_][\w']*", lambda m: m.group(0) if m.group(0) == 'mod' else
               str(UD[side][m.group(0)]) if m.group(0) in UD[side] else m.group(0), s).strip()
    if not s or not ARITH.match(s) or not re.search(r'\d', s):
        return None
    try:
        x = eval(s.replace('^', '**').replace('mod', '%').replace('/', '//'), {'__builtins__': {}}, {})
    except Exception:
        return None
    return x if isinstance(x, int) else None


def arith_eq(v, bt, at, side):
    for pat in (r'\b(?:replace|change)\s*\(([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*)\)\s*with\s*\(?$',
                r'\b(?:replace|change)\s+([^\s()]+)\s+with\s*\(?$'):
        m = re.search(pat, bt)
        if m and ev(m.group(1), side) == v:
            return f'`{m.group(0).strip()} N`: the expression evaluates to N (unit definitions substituted)'
    m = re.match(r'\s*\)?\s*with\s*\(([^()]*(?:\([^()]*\)[^()]*)*)\)', at)
    if m and re.search(r'\b(?:replace|change)\s*\(?$', bt) and ev(m.group(1), side) == v:
        return f'`replace N {m.group(0).strip()}`: the expression evaluates to N'
    # an operand of a literal identity the same sentence states: `replace (E1) with (E2)` / `E1 = E2`, both closed
    return None


def literal_identity(v, sent, side):
    """the sentence is `replace (E1) with (E2) [in H] by ...` or `change (E1) with (E2)` and E1 = E2 is an arithmetic
    identity in which N is an operand: unit definitions substituted, every other name given the same random integer on
    both sides, three draws equal (the proof's lia / zlia / reflexivity, or change's conversion, checks the same)"""
    import random
    E = r'(\((?:[^()]|\([^()]*(?:\([^()]*\)[^()]*)*\))*\)|[^\s();.]+)'
    cands = [m for m in re.finditer(r'\breplace\s*' + E + r'\s+with\s*' + E + r'\s+(?:in\s+\S+\s+)?by\b', sent, re.S)] + \
            [m for m in re.finditer(r'\bchange\s*' + E + r'\s+with\s*' + E, sent, re.S)]
    for m in cands:
        if not re.search(rf'(?<![\w.]){v}(?![\w])', m.group(1) + ' ' + m.group(2)):
            continue
        names = set(re.findall(r"[A-Za-z_][\w']*", m.group(1) + ' ' + m.group(2))) - {'mod'} - set(UD[side])
        rnd = random.Random(v)
        ok = True
        for _ in range(3):
            env = {n: str(rnd.randrange(1, 1 << 20)) for n in names}
            sub = lambda e: re.sub(r"[A-Za-z_][\w']*", lambda x: env.get(x.group(0), x.group(0)), e)
            x, y = ev(sub(m.group(1)), side), ev(sub(m.group(2)), side)
            if x is None or x != y:
                ok = False
                break
        if ok:
            return f'`{m.group(0)[:100].strip()}` is an arithmetic identity (both sides equal for three random values of ' \
                   f'{", ".join(sorted(names)) or "no variable"}) in which N is an operand'
    return None


IDXPAT = re.compile(r"(\b(ew|rho_of|rho|U_atom)\s+\w+'?|\bgetr\s+\w+|\(ss_regs\s+\w+\)|\bHEn\w*|\bHregs|\bSOff|\bAF|"
                    r"\bewset\s+\w+|\bst_ok_abs_chunk\s+\w+|\bsv_atoms_lt_mono(\s+\d+)?|\bHE\d+|\bHR\d*|\bBV\d+|"
                    r"\bmemv\s+\w+|\bCA\s+\d+|\bagree_step\s+\d+|\bPG|\bhavoc\s+\w+|\bjunk_regs\s+\w+|\bAFo\s+\w+|"
                    r"\bG|\bWPRES|\bltHAV|\bEn\d+\s+_\s+_|\brho\s+\w+|\bheadcJ|\bcondZ\s+\w+\s+\w+|"
                    r"\bmkRegion\s*\(\s*Some|\bSome|\bCK\s+\d+%nat|\bchunk_atom\s+_\s+_\s+\d+|\bupg|\bepg|"
                    r"\bvf_after_icpt|\bvo\d_r07\s+\w+|\bvd\d_r07\s+\w+|\bvu\d_r07\s+\w+)\s*\(?\s*$")
BYTE256 = re.compile(r'(\b256\s*\*|\*\s*256\b|\bmod\s+256\b|/\s*256\b|<\s*256\b|2\s*\^\s*8\b|Z\.of_N\s+8|8\s*\*\s*Z\.of_nat|'
                     r'bv_modulus\s+8|\b255\b|\bbyte|\bbytes\b|le_byte|\bhb\d*\b|\bb\d\b|\bc\d\b|\bzb\b|zdig|\blit8\b|'
                     r'Z_to_bv\s+8|\bbv\s+8\b|\b128\b|cellval|sbyte|mod256|seq\s+0\s+256|zseq\s+0\s+256|bv_unsigned\s+c\b)')
RT_BASES = {
    'ly_C ly': 'the C zone of the allocator layout record ly (zone3_intro, lib/A/AF0x.v:66-67, proves a zone disjoint '
               'from the image range ly_img ly)',
    'T': 'ly_T ly, the thread object of the allocator layout (Local Notation T := (ly_T ly))',
    'C': 'a run-time zone of the allocator layout (lib/A/AFl4.v: zone3 C)',
    'sp0': 'the stack pointer at entry (Let sp0 := bv_unsigned (getr regs0 2))', 'spZ regs': 'a stack pointer',
    'usp': 'the user stack pointer', 'SMv': 'an allocator map base of the run', 'QSv': 'the run\'s pointer-array grant base',
    'MSv': 'an allocator map size of the run', 'NDv': 'an allocator variable of the run',
    'R8v': 'an allocator variable of the run', 'CEIL_MAX': 'the ASan allocator ceiling (run-time memory map)',
    'kHighMemBeg': 'ASan high-memory start (memory map)', 'kLowShadowBeg': 'ASan low-shadow start (memory map)',
    'kUserMapSize': 'ASan user-map size (lib/Reusable/YG00.v:13)', 'MALLOC_MAX': 'the allocator size maximum',
    'CTX': 'the context block of the Reusable allocator model', 'then CTX': 'the context block of the Reusable model',
    'ms_ctx B': 'the context block of the Reusable allocator model', 'ms_debruijn B': 'the de Bruijn table pointer of '
    'the Reusable model state', 'TFIB_TP': 'the thread pointer of the run (lib/A/AF0m.v:13, inside builtin_tls)',
    't_stats': 'a field offset of the thread object', 't_cache': 'a field offset of the thread object',
    'RGv': 'a region-info record of the allocator space (RGv := SB + kRegionInfoOff + 128 * c)',
    'sh': 'a shadow address', 'sha': 'a shadow address', 'shf': 'a shadow address', 'lst': 'an allocator variable',
    'coff': 'a batch offset of the run (Let coff := last l 0)', 'x': 'an offset of the run (x := off - region_off c)',
    'xb': 'an offset of the run', 'q': 'a quotient variable', 'p': 'a quotient variable', 'a': 'an address variable',
    'cfg_model c1': 'the run-time model of a configuration', 'eager_used mdV': 'the run-time eager-memory counter',
    'S kBatchClass': 'a run-time allocator region', 'as_tp B': 'the thread pointer of the Reusable model',
    'bv_unsigned a': 'a run-time address', 'am_mem an': 'a run-time map', 'am_mem aq': 'a run-time map',
    'M64': '2^64 (bit-vector arithmetic)', 'bv_unsigned b1': 'a byte value', 'bv_unsigned b': 'a byte value',
    'E rT': 'a register value', 'as_inst B': 'the instance block of the Reusable model',
    'A_ALLOCATOR': 'the allocator object (a field offset into it)', 'TFIB_INST': 'the instance object (a field offset)',
}
RT_NAMES = {'LLVMF_STK', 'DIAG_STK', 'FP_WIN', 'VP_WIN', 'VF_STK', 'ASTACK', 'ESTACK', 'DSTACK', 'STDOUT_BSZ', 'GFRAME',
            'kBatchClass', 'kPtrArrayCommit', 'FPI_STK', 'VPI_STK', 'STRNLEN_STK', 'kFakeFramesOff', 'NREG',
            'kThreadObjSize', 'kUserMapSize', 'kFreeArrayMapSize'}


def base_ident(b):
    bt = b.rstrip()
    m = re.search(r"([A-Za-z_][\w']*(?:\s+[A-Za-z_][\w']*)?)\s*\)?\s*([+-])\s*\(?\s*-?\s*$", bt)
    if m:
        return m.group(1)
    m = re.search(r"\(\s*([A-Za-z_][\w']*(?:\s+[A-Za-z_][\w']*)?)\s*,\s*$", bt)
    return m.group(1) if m else None


def family(v, b, a, sent, side):
    """(rule, evidence) of a positive role, else None"""
    bt, at = b.rstrip(), a.lstrip()
    snip = f'`{bt[-40:].strip()} N {at[:20].strip()}`'
    if re.search(r'\bEVar\s*\(?$', bt) or re.search(r'\bV$', bt) or re.search(r'\bEVar\s+\w+\)\s*$', bt):
        return 'VAR_INDEX', 'the numeral is the index of a symbolic variable: ' + snip
    if v < 256 and IDXPAT.search(bt):
        return 'INDEX', 'the numeral is a register / atom / slot / step index (< 256): ' + snip
    if v < 256 and re.search(r'\(\s*$', bt) and re.match(r'%nat\s*,\s*mkAF', at):
        return 'INDEX', 'the numeral is the atom index of an mkAF fact: ' + snip
    if v < 256 and re.search(r'Definition\s+\w+\s*:\s*nat\s*:=\s*$', bt):
        return 'INDEX', 'the numeral is a nat index constant: ' + snip
    if re.search(r'\^\s*\(?$', bt):
        return 'EXPONENT', 'the numeral is an exponent: ' + snip
    if v == PAGE and not (re.search(r'\b2\s*\*\s*\(?$', bt) or re.match(r'(/|\*)\s*2\b', at)):
        return 'PAGE_SIZE', ('4096 = p_align of every PT_LOAD of fuzz_command.asan c0661b96b5bd, fuzz_command.asan-ubsan '
                             'bbe55d24d096 and both cgif builds (program headers); used as the page size, not halved: ' + snip)
    if v == 256 and BYTE256.search(sent):
        return 'BYTE_ARITH', '256 = 2^8 in a sentence doing 8-bit arithmetic: ' + snip
    e = arith_eq(v, bt, at, side) or literal_identity(v, sent, side)
    if e:
        return 'ARITH_EQ', e
    bi = base_ident(b)
    if bi and bi in RT_BASES:
        return 'RT_OFFSET', f'offset / size from {bi}: {RT_BASES[bi]}: ' + snip
    m = re.search(r'\b([A-Za-z_]\w*)\s*=\s*$', bt) or re.search(r'Definition\s+([A-Za-z_]\w*)\s*:\s*Z\s*:=\s*$', bt) \
        or re.search(r'class_size\s+(\w+)\s*=\s*$', bt)
    if m and m.group(1) in RT_NAMES:
        return 'RT_CONST', f'the value of the run-time constant {m.group(1)}: ' + snip
    if re.search(r'\b(SLit|ELit|escale|w64)\s*\(?\s*-?\s*$', bt) and (v < IMG_LO or is_pow2(v)):
        return 'SYMLIT', 'a literal of a symbolic register / expression value, below the image base or a power of two: ' + snip
    return None


# ---------------------------------------------------------------- hand-family handlers (each measures)
def h_func(v, b, a, side):
    D = ROWDEF[side]
    k = TIMG[side]
    m = re.search(r'\b((?:tfib|src0)_A_\w+)\s*\+\s*$', b.rstrip())
    if not (m and m.group(1) in D):
        return None
    sym = m.group(1)
    base, end = D[sym], D.get(sym.replace('_A_', '_E_', 1))
    addr = base + v
    fs = containing(k, addr)
    inside = end is not None and base <= addr < end and fs is not None and fs[1] == base
    w = re.match(r'\s*\)\s*\)\s*=\s*Some\s*\(\s*(0x[0-9a-fA-F]+)%bv', a)
    if w:
        want, got = int(w.group(1), 16), read_word(k, addr)
        ok = got == want and inside
        return ('FETCH_WORD_AT', f'{sym} = {hex(base)} (row table of lib/{side}); the word of {ROLE[k]} at '
                f'{hex(addr)} is {hex(got) if got is not None else "none"}, the stated word is {hex(want)}; '
                f'{hex(addr)} is inside {fs[0] if fs else "?"} [{hex(base)}, {hex(end) if end else "?"})', ok)
    return ('FUNC_OFFSET', f'{sym} = {hex(base)} (row table of lib/{side}, end {hex(end) if end else "?"}); {hex(addr)} '
            f'is inside the function {fs[0] if fs else "?"} of {ROLE[k]} (.symtab)', inside)


def h_build(v, b, a, side):
    m = re.search(r'\bbuild_table\s+\w+\s+(0x[0-9a-fA-F]+)\s*$', b.rstrip())
    if not (m and re.match(r'\s*%nat', a)):
        return None
    k = TIMG[side]
    st = int(m.group(1), 16)
    end = st + 4 * v
    last = containing(k, end - 4)
    ok = st in FSTART[k] and (end in FEND[k] or end in FSTART[k])
    return ('BUILD_TABLE_RANGE', f'build_table from {hex(st)} (a function start of {ROLE[k]}) over {v} words ends at '
            f'{hex(end)}, the end of {last[0] if last else "?"} (.symtab)', ok)


def h_cell(v, b, a, side, fn):
    m = re.search(r'z8\s*\(ANum\s+(0x[0-9a-fA-F]+)\)\s*$', b.rstrip())
    if not (m and fn in ('AF0m.v', 'YF0m.v')):
        return None
    addr = int(m.group(1), 16)
    coll = 'AB01.v' if side == 'A' else 'YB01.v'
    t = text(side, coll)
    mm = re.search(rf'a_off := {addr} \|\}} (\d+) \(ELit (\d+)\)', t)
    ok = mm is not None and int(mm.group(2)) == v
    return ('CELL_STARTUP', f'start-up cell {hex(addr)}: lib/{side}/{coll} (collected start-up state) writes '
            f'`a_off := {addr} |}} {mm.group(1) if mm else "?"} (ELit {mm.group(2) if mm else "?"})` = N; the cell is '
            f'inside {containing(TIMG[side], addr, ("STT_OBJECT",))[0] if containing(TIMG[side], addr, ("STT_OBJECT",)) else "?"}', ok)


def h_layout_buf(v, b, a, side, sent):
    """1024 = the stdout buffer: `buf` of 1032 bytes (BUFSIZ + UNGET) whose data area starts 8 bytes in"""
    if v != 1024:
        return None
    k = TIMG[side]
    bufs = {x + 8 for x, n, sz, t in SYMS[k] if n == 'buf' and sz == 1032}
    m = re.search(r'(0x[0-9a-fA-F]+)\s*\+\s*$', b.rstrip())
    if m and int(m.group(1), 16) in bufs:
        bufa = int(m.group(1), 16)
    elif 'STDOUT_BUFA' in sent or '6311080' in sent:
        bufa = UD[side].get('STDOUT_BUFA')
    else:
        return None
    ok = bufa in bufs
    return ('LAYOUT_MEASURED', f'the stdout data area at {hex(bufa) if bufa else "?"}: {ROLE[k]} .symtab has `buf` at '
            f'{hex(bufa - 8) if bufa else "?"} size 1032 (BUFSIZ 1024 + UNGET 8), so the area is 1024 bytes', ok)


def h_ctx_chunk(v, b, a, side, sent):
    k = TIMG[side]
    if re.search(r'Definition\s+CTX_SIZE\s*:\s*Z\s*:=\s*$', b.rstrip()):
        sz = {s for x, n, s, t in SYMS[k] if n == '__malloc_context'}
        return ('LAYOUT_MEASURED', f'CTX_SIZE = the size of __malloc_context in {ROLE[k]} .symtab ({sorted(sz)})', v in sz)
    m = re.search(r'chunk_bytes\s+\w+\s+\w+\s+(\d+|0x[0-9a-fA-F]+)\s*\(CImg\s*$', b.rstrip())
    if m:
        lo = int(m.group(1), 0)
        offs = [int(x) - lo for x in re.findall(r'\((\d+)\s*-\s*' + str(lo) + r'\)', sent)]
        seg = next(((va, va + fz) for va, mz, fz, al in LOADS[k] if va <= lo < va + fz), None)
        ok = seg is not None and lo + v <= seg[1] and all(0 <= o < v for o in offs)
        return ('CHUNK_IN_SEGMENT', f'an image chunk of {v} bytes at {hex(lo)}: [{hex(lo)}, {hex(lo + v)}) lies in the file '
                f'bytes of {ROLE[k]}\'s segment {tuple(hex(x) for x in seg) if seg else "?"} (program headers) and the '
                f'offsets the sentence reads ({offs}) lie inside it; a chunk length, not the segment length', ok)
    return None


def h_atexit(v, b, a, side, sent):
    if not ('0x604168' in sent and v == 0x130):
        return None
    rel = {}
    for k in ('dB', 'tB'):
        f = FIRST[k]['finished_atexit'][0]
        rel[k] = [(n, x - f, sz) for x, n, sz, t in SYMS[k] if f <= x < f + 0x130 and t == 'STT_OBJECT']
    ok = rel['dB'] == rel['tB'] and FIRST['tB']['finished_atexit'][0] == 0x604168
    return ('LAYOUT_MEASURED', f'[0x604168, +0x130) starts at finished_atexit in {ROLE["tB"]}; the objects in it and '
            f'their offsets are the same in cgif ({rel["tB"]}), so the extent is the same musl atexit layout', ok)


def h_zone(v, b, a, sent):
    if v == 256 and re.search(r'\b(zone3_intro\s+ly\s+(\(ly_C ly\)|C)|zone3\s+(\(ly_C ly\)|C)|zone_of\s+\(ly_C ly\)|'
                              r'okr\s+\(ly_C ly\)|HI\s+\(ly_C ly\)|ly_C ly\)\s*\(?)\s*$', b.rstrip()):
        return ('RT_OFFSET', 'the length of the allocator layout\'s C zone (ly_C ly, 256): zone3_intro ly x sz requires '
                '(x, sz) disjoint from ly_img ly, the image range (lib/A/AF0x.v:66-67), so the zone is outside the image', True)
    return None


def h_ranges(v, b, a, fn, sent):
    if fn == 'AB05.v' and 'startup_plan_tfib_ranges' in sent and re.match(r'\s*%nat', a):
        return ('RANGE_HINT', 'startup_plan_tfib_ranges (lib/A/AB05.v) only feeds IT0 := mk_itab_ranges TSEGS '
                'startup_plan_tfib_ranges, and IT0_ok is `apply mk_itab_ranges_sound` (lib/A/AB1m.v:27-29), sound for any '
                'list; 2076 is the range length in four entries of both cgif and fuzz_command while every start moved', True)
    return None


def h_tp(v, b, a, sent, side):
    if v == 88 and ('ATp (-88)' in sent or 'TFIB_TP' in sent):
        tp = UD[side].get('TFIB_TP')
        return ('RT_OFFSET', f'-88 from the thread pointer: TFIB_TP = {hex(tp) if tp else "?"} (lib/A/AF0m.v:13); the '
                'sentence states the same offset as ATp (-88), the thread-pointer-relative model address', True)
    return None


def h_kernel(sent, file_text, y):
    """the statement holding the numeral is closed by `vm_compute. reflexivity.` (or repeat split; reflexivity)"""
    pos = file_text.find(sent[:60])
    seg = file_text[pos:pos + len(sent) + 200] if pos >= 0 else ''
    if re.search(r'Proof\.\s*(vm_compute\.\s*(repeat split;\s*)?reflexivity|reflexivity)\.\s*Qed\.', seg) or \
            re.search(r'by\s*\(?\s*(vm_compute;\s*)?reflexivity\s*\)?\s*\.', sent):
        return ('KERNEL_CHECKED', 'the statement is closed by a kernel computation (`vm_compute. reflexivity.` / `by '
                'reflexivity`): the kernel computes it from the unit\'s definitions, a wrong value fails the build', True)
    return None


def h_img_regions(v, sent, side):
    if v == 37 and ('IMG_REGIONS' in sent and 'skipn' in sent):
        n = len(re.search(r'Definition IMG_REGIONS : smem := \[([^\]]*)\]', text(side, 'AD2j.v' if side == 'A' else 'YD2j.v'))
                .group(1).split(';'))
        return ('COUNT_MEASURED', f'IMG_REGIONS has {n} regions (lib/{side}/{"AD2j.v" if side == "A" else "YD2j.v"}); the '
                f'region after the 4 head regions and IMG_REGIONS is at index 4 + {n} = {4 + n}', 4 + n == v)
    return None


SPECIAL = [  # (rule, condition on value / sentence / context, evidence): one-family readings, measured by the text
    ('RT_CONST', lambda v, s, b, a: v == 0x20000 and re.search(r'\bQSv\b|kPtrArray|grant_md|pru17|page_round_up_Z|w64 131072|'
                                                               r'getr regs 11 = Z_to_bv 64 131072', s),
     'the pointer-array commit of the run: 131072 = kPtrArrayCommit (lib/Reusable/YG00.v:22), the grant length at QSv '
     '(its length argument in register a1 = x11)'),
    ('RT_CONST', lambda v, s, b, a: v == 0x20000 and re.search(r'kn_zero|KZ\s+_\s+500', s),
     'the length of a zeroed run-time block at a symbolic base (EMd M_MUL (ELit 512) (EVar 500)): a run-time mapping'),
    ('RT_CONST', lambda v, s, b, a: v == 0x20000 and re.search(r'rCSZ|mkAF 16', s),
     'the bound of the size-class atom rCSZ (mkAF 16 131072 4): an allocator size bound'),
    ('RT_CONST', lambda v, s, b, a: v == 0x20000 and re.search(r'MMAP_THRESHOLD|page_round|mp_rq|dlen|total_arg_bytes|rw_bytes_max|Haimg|bv_unsigned a \+|<= len', s),
     'musl\'s mmap threshold / request bound of the Reusable allocator model (lib/Reusable/YO0b.v:660: addw 0x20000 (-20) = '
     'MMAP_THRESHOLD); where the sentence states image bounds, 0x10000 and 0x55000, they are fuzz_command.plain\'s first '
     'and last page bounds (program headers of a20873dc7f0e)'),
    ('ABSTRACT_GOAL', lambda v, s, b, a: re.search(r'\bGoal\b.*fetch_word segs|stepjr F D', s) is not None,
     'an aborted smoke goal over an abstract segment map `segs` (lib/Reusable/YK1a.v): its numerals name no image'),
    ('RT_CONST', lambda v, s, b, a: v == 0x20000 and re.search(r'grow then', s),
     'the grant length added when the pointer array grows (131072 = kPtrArrayCommit, lib/Reusable/YG00.v:22)'),
    ('RT_CONST', lambda v, s, b, a: v in (0x4000, 0x8000) and re.search(r'nd_hi', s),
     'an arm of nd_hi, the node-level size table of the allocator model (3 => 4096 | 4 => 16384 | 5 => 32768 | 6 => 65536)'),
    ('RT_CONST', lambda v, s, b, a: v == 0x8000 and re.search(r'memset_stretch3|shadow_addr|SHBv|262144', s),
     'the shadow of a 262144-byte user map (kUserMapSize = 262144, lib/Reusable/YG00.v:13; 262144 / 8 = 32768)'),
    ('RT_CONST', lambda v, s, b, a: v == 0x8000 and re.search(r'config_len', s),
     'config_len := cfg_word mod 32768 (lib/Reusable/YO05.v:40): the bound holds by construction'),
    ('RT_CONST', lambda v, s, b, a: v == 0x4000 and re.search(r'all_batches|vis_cost|8 \* 16384|PSec', s),
     'a fuel / cost / size bound of the Reusable allocator model (library constant)'),
    ('RT_CONST', lambda v, s, b, a: v == 0x400 and re.search(r'N8D / 8|CNTv len|w \* 512', s),
     'shadow arithmetic of the allocator model: 1024 = 8192 / 8 (len = 8 * CNTv len, the 8192-byte batch)'),
    ('RT_CONST', lambda v, s, b, a: v == 0x800 and re.search(r'rz_size n = 2048|ck_rz', s),
     'the chunk redzone of the run: the same sentence states rz_size n = 2048'),
    ('RT_CONST', lambda v, s, b, a: v == 0x1000 and re.search(r'2 \*\s*$', b.rstrip()) and 'mkAF' in s,
     'two pages (2 * 4096; 4096 = p_align of every PT_LOAD) in an allocator fact bound'),
    ('RT_CONST', lambda v, s, b, a: v == 0x100 and re.search(r'length ev|src0_A_main', s) is not None,
     'an argument-count bound of the Reusable driver model (length ev <= 256) / an offset into main (see FUNC_OFFSET)'),
    ('CODE_SITE_CONST', lambda v, s, b, a: v == 0x100 and re.search(r's_memsetR', s) is not None,
     'the memset length of the call at the stated pc (lib/A: 0x34a08, lib/B: 0x34a54), inside __asan::Allocator::Allocate '
     '(.symtab of both twins; the function has the same size, 2440, in cgif and fuzz_command)'),
    ('RT_CONST', lambda v, s, b, a: v == 0x100 and re.search(r'fill_spec', s) is not None,
     'the fill-byte bound of the imemset fill spec (the premise in lib/A/AB1p.v:72 reads `bv_unsigned c < 256`)'),
    ('KERNEL_CHECKED', lambda v, s, b, a: v == 37 and re.search(r'PM_pieces|RU_\d|REG0U2', s) is not None,
     'a list length closed by `vm_compute. reflexivity.` (lib/A/AD2e.v:73, lib/A/AFks.v): the kernel computes it'),
    # Reusable sentences the plain-keyed extra run flags
    ('RT_CONST', lambda v, s, b, a: v == 0x1000 and re.search(r'\b2\s*\*\s*$', b.rstrip()) is not None,
     'two pages (2 * 4096; 4096 = p_align of every PT_LOAD of the images) above a run-time bound (brk / allocation)'),
    ('RT_CONST', lambda v, s, b, a: v == 0x2000 and re.search(r'(alloc_ceiling|CEIL)\s*\+\s*$', b.rstrip()) is not None,
     'a two-page gap (8192 = 2 * 4096) between the allocation ceiling and the stack pointer of the Reusable model'),
    ('ARITH_EQ', lambda v, s, b, a: v == 0x2000 and re.search(r'SHADOW_OFF|ly_F ly - 65536', s) is not None,
     'the shadow offset of the image base: 8192 = 0x10000 / 8, and every image here (cgif and fuzz_command, all builds) '
     'starts its first PT_LOAD at 0x10000 (program headers)'),
    ('RT_CONST', lambda v, s, b, a: v == 0x400 and re.search(r'8\s*\*\s*$', b.rstrip()) and re.match(r'\s*\*\s*1024', a),
     'the 8 MiB stack size 8 * 1024 * 1024 of the Reusable model'),
    ('RT_CONST', lambda v, s, b, a: v == 0x400 and re.search(r'length av', s) is not None,
     'the argument-count bound of the Reusable driver model (length av <= 1024)'),
    ('INDEX', lambda v, s, b, a: re.search(r'\b(junk_regs_ok\s+\w+\s+\w+|region_ok_agree\s+\w+|st_ok_set_regs\s+\w+)\s*$',
                                           b.rstrip()) is not None,
     'the atom-count bound of an environment (junk_regs_ok / region_ok_agree / st_ok_set_regs take the number of atoms)'),
]


def settle(run, v, fn, y, s, file_text):
    """(rule, measurement, ok) for one occurrence y (Num) of the row's numeral, judged with value v"""
    side = SIDE[run]
    key = RUNKEY[run]
    b, a = ctx(y)
    sent = s[5]
    for h in (lambda: h_func(v, b, a, side), lambda: h_build(v, b, a, side), lambda: h_cell(v, b, a, side, fn),
              lambda: h_layout_buf(v, b, a, side, sent), lambda: h_atexit(v, b, a, side, sent),
              lambda: h_zone(v, b, a, sent), lambda: h_ranges(v, b, a, fn, sent), lambda: h_tp(v, b, a, sent, side),
              lambda: h_img_regions(v, sent, side), lambda: h_ctx_chunk(v, b, a, side, sent)):
        r = h()
        if r:
            return r
    f = family(v, b, a, sent, side)
    if f:
        return f[0], f[1], True
    for rule, cond, why in SPECIAL:
        if cond(v, sent, b, a):
            return rule, why + f'; text `{b.rstrip()[-40:].strip()} N {a.lstrip()[:20].strip()}`', True
    why = 'no rule (value at or above the image base)'
    if v < IMG_LO:
        dis = differing(key, v)
        adr, words = anchors_of(key, dis)
        divs = sorted({int(m.group(1)) for nm, c, t in dis for m in [re.search(r'/(\d+)$', nm)] if m})
        ok, why = not_quantity(v, b, a, {z.v for z in s[4] if z.kind != 'ident'} - {v}, set(IDT.findall(sent)),
                               adr, words, divs)
        if ok:
            return 'NOT_FLAGGED_QTY', why, True
    k = h_kernel(sent, file_text, y)
    if k:
        return k
    return 'UNSETTLED', why, False


# ---------------------------------------------------------------- rows
def full_rows(run):
    out = collections.defaultdict(list)
    for l in gzip.open(os.path.join(getattr(A, 'in'), run + '.full.tsv.gz'), 'rt', encoding='utf-8', errors='replace'):
        if l.startswith('#') or l.startswith('verdict\t'):
            continue
        f = l.rstrip('\n').split('\t')
        f += [''] * (16 - len(f))
        out[(f[5], f[6], f[3], f[4], f[7], f[8], f[9])].append(f[:16])
    return out


RUNS = [('rc-A', 'RA'), ('mv-A', 'RA'), ('rc-B', 'RB'), ('mv-B', 'RB'), ('rc-U', 'RU'), ('mv-U', 'RU'), ('rc-UP', 'RU'),
        ('mv-UP', 'RU')]
FULL = {}
results = []
for run, tsv in RUNS:
    p = os.path.join(A.main, run + '.tsv')
    if os.path.exists(p + '.gz'):
        fh = gzip.open(p + '.gz', 'rt')
    elif os.path.exists(p):
        fh = open(p)
    else:
        continue
    if tsv not in FULL:
        FULL[tsv] = full_rows(tsv)
    for g in [l.rstrip('\n').split('\t') for l in fh][1:]:
        if g[0] == 'SAME':
            continue
        dfile, dline = g[3].rsplit(':', 1)
        sfile, sline = g[4].rsplit(':', 1)
        cands = FULL[tsv][(dfile, dline, sfile, sline, g[5], g[6], g[7])]
        moved = run.startswith('mv')
        frow = next((c for c in cands if int(c[10], 16) == int(g[8], 16)), cands[0] if cands else None)
        results.append((run, g, frow))

rows_out, OCCS = [], []
for run, g, f in results:
    side = SIDE[run]
    key = RUNKEY[run]
    v = int(g[8], 16)
    moved = run.startswith('mv')
    dis = differing(key, v, moved)
    fn, ln = f[5], int(f[6])
    base = fn.split('.')[0]
    occ = []
    if base in COLLECTED:
        hdr = [l for l in text(side, fn).split('\n')[:4] if 'collected for' in l]
        rule, meas, ok = 'COLLECTED_STATE', ('file header: ' + (hdr[0].strip()[3:150] if hdr else '?') +
                                             ' ...; the whole file is the collector\'s output over the image'), bool(hdr)
    elif moved:
        tv = int(f[11], 16)
        T = GEO['t' + key][0]
        agree = [nm for nm, c, t in dis if T.get(nm) == tv and c == 'segment']
        rule, meas, ok = 'MOVED_TO_SEGMENT', (f'the port changed {hex(v)} to {hex(tv)} = {ROLE[TIMG[side]]}\'s '
                                              f'{", ".join(agree) or "?"} (program headers)'), bool(agree)
    else:
        S = sents(side, fn)
        occ = [(s, y) for s in S for y in s[4] if y.line == ln and y.v == v and y.kind != 'ident']
        named = [(s, y) for s, y in occ if s[1] == g[5]]
        idx = int(g[6]) if g[6] else -1
        exact = [(s, y) for s in S if s[1] == g[5] for j, y in enumerate(s[4]) if j == idx and y.line == ln and y.v == v]
        occ = exact or named or occ
        if not occ:
            rule, meas, ok = 'UNSETTLED', 'numeral not located', False
        else:
            res = [settle(run, v, fn, y, s, text(side, fn)) for s, y in occ]
            bad = [r for r in res if not r[2]]
            rule, meas, ok = (bad[0] if bad else res[0])
            if len(occ) > 1 and not bad:
                meas = f'{len(occ)} occurrences of {v} on this line, each settled: ' + meas
    rows_out.append((run, g, f, rule, meas, ok, dis))
    OCCS.append(occ)

HDR = pac.COLS + ['reason', 'measurement', 'result', 'finding_kind', 'new_value', 'read_by', 'gate_run', 'v2_status',
                  'v2_class', 'v2_value', 'differing_names']
for name, runs in (('rows.tsv', ('rc-A', 'mv-A', 'rc-B', 'mv-B', 'rc-U', 'mv-U')), ('rows_UP.tsv', ('rc-UP', 'mv-UP'))):
    with open(os.path.join(OUT, name), 'w') as o:
        o.write('\t'.join(HDR) + '\n')
        for run, g, f, rule, meas, ok, dis in rows_out:
            if run in runs:
                o.write('\t'.join(f + [rule, meas.replace('\t', ' ').replace('\n', ' '), 'OK' if ok else 'UNSETTLED',
                                       '-', '-', '-', run, g[0], g[9], g[8], dis_text(dis)]) + '\n')
cnt = collections.Counter((run, rule, ok) for run, g, f, rule, meas, ok, dis in rows_out)
with open(os.path.join(OUT, 'rows.summary'), 'w') as o:
    o.write(f'# rows {len(rows_out)}\n')
    for key_ in ('A', 'B', 'P'):
        n, same, diff = CODE_ID[key_]
        o.write(f'# code identity {key_}: functions in both images under one name {n}, same size {same}, differ {diff}\n')
    for (run, rule, ok), c in sorted(cnt.items()):
        o.write(f'{run}\t{rule}\t{"OK" if ok else "UNSETTLED"}\t{c}\n')
print(open(os.path.join(OUT, 'rows.summary')).read())

# ---------------------------------------------------------------- known-answer controls of the rules
# (1) PERTURBATION: re-judge every settled non-collected row with value+4 and with value := the fuzz_command value of
#     its first differing name (what the numeral would be if it were that quantity, correctly ported). A rule that
#     measures the value refuses both; a rule that reads only the numeral's role does not (reported as such).
# (2) KNOWN GEOMETRY: rows of the value gate's own full TSVs that it classed as image geometry (SAME-GEOMETRY,
#     IMAGE-EXTENT-SAME, GEOMETRY-CHANGED, IMAGE-EXTENT-CHANGED) where the port changed a donor quantity to fuzz_command's
#     counterpart, outside the collected-state files: re-judged with the donor value put back (a kept donor quantity).
#     Every rule must refuse them (KERNEL_CHECKED accepts by design: those statements fail the build).
# (3) PLANTS: the planted positions of the gate controls (lib/A AB13.v:119, AB1h.v:49, AB01.v:188, AD1k.v:260,
#     AB01.v:107; lib/B YB13.v:120, YB01.v:225), judged with the planted donor value.
pert = collections.Counter()
for (run, g, f, rule, meas, ok, dis), occ in zip(rows_out, OCCS):
    if not ok or not occ:
        continue
    side, v, fn = SIDE[run], int(g[8], 16), f[5]
    cp = next((t for nm, c, t in dis if t is not None), None)
    for tag, nv in (('v+4', v + 4), ('counterpart', cp)):
        if nv is None:
            pert[(rule, tag, 'n/a')] += 1
            continue
        rr = [settle(run, nv, fn, y, s, text(side, fn)) for s, y in occ]
        same = all(r[2] and r[0] == rule for r in rr)
        anyr = all(r[2] for r in rr)
        pert[(rule, tag, 'same rule accepts' if same else 'same rule refuses' + (' (another rule accepts)' if anyr
                                                                                   else ''))] += 1
geo_v = {'SAME-GEOMETRY', 'IMAGE-EXTENT-SAME', 'GEOMETRY-CHANGED', 'IMAGE-EXTENT-CHANGED'}
geo = collections.Counter()
geo_ex = collections.defaultdict(list)
for run, tsv in (('rc-A', 'RA'), ('rc-B', 'RB'), ('rc-U', 'RU')):
    side = SIDE[run]
    key = RUNKEY[run]
    T = GEO['t' + key][0]
    for (dfile, dline, *_), lst in FULL[tsv].items():
        for fr in lst:
            if fr[0] not in geo_v or fr[9] == 'ident' or fr[2] != key or dfile.split('.')[0] in COLLECTED:
                continue
            try:
                sv, tv = int(fr[10], 16), int(fr[11], 16)
            except ValueError:
                continue
            if sv == tv or not any(T.get(nm) == tv for nm in INV[key].get(sv, [])):
                continue
            occ = [(s, y) for s in sents(side, dfile) for y in s[4] if y.line == int(dline) and y.v == tv and y.kind != 'ident']
            if not occ:
                geo[('unlocated',)] += 1
                continue
            s, y = occ[0]
            r = settle(run, sv, dfile, y, s, text(side, dfile))
            geo[(r[0], 'accepted' if r[2] else 'refused')] += 1
            if r[2] and r[0] != 'KERNEL_CHECKED':
                geo_ex[r[0]].append(f'{side}/{dfile}:{dline} {hex(sv)}')
PLANTS = [('rc-A', 'AB13.v', 119, 143360, 0x20000), ('rc-A', 'AB1h.v', 49, 0x72000, 0x6d000), ('rc-A', 'AB01.v', 188, 1215, 214),
          ('rc-A', 'AD1k.v', 260, 631, 67), ('rc-A', 'AB01.v', 107, 1091, 88), ('rc-B', 'YB13.v', 120, 143360, 0x20000),
          ('rc-B', 'YB01.v', 225, 1127, 126)]
plant_res = []
for run, fn, ln, old, new in PLANTS:
    side = SIDE[run]
    occ = [(s, y) for s in sents(side, fn) for y in s[4] if y.line == ln and y.v == old and y.kind != 'ident']
    rr = [settle(run, new, fn, y, s, text(side, fn)) for s, y in occ]
    coll = fn.split('.')[0] in COLLECTED
    plant_res.append((f'{side}/{fn}:{ln}', hex(new), '; '.join(f'{r[0]}:{"accepted" if r[2] else "refused"}' for r in rr),
                      'file is a collected-state file: COLLECTED_STATE would accept it by provenance' if coll else ''))
with open(os.path.join(OUT, 'triage_controls.tsv'), 'w') as o:
    o.write('control\trule\tcase\tresult\tcount\n')
    for (rule, tag, res), c in sorted(pert.items()):
        o.write(f'perturbation\t{rule}\t{tag}\t{res}\t{c}\n')
    for k_, c in sorted(geo.items()):
        o.write(f'known_geometry\t{k_[0]}\tvalue := donor\t{k_[1] if len(k_) > 1 else ""}\t{c}\n')
    for rule, ex in sorted(geo_ex.items()):
        o.write(f'known_geometry_accepted_examples\t{rule}\t\t\t{"; ".join(ex[:8])}\n')
    for pos, nv, res, note in plant_res:
        o.write(f'plant\t{res}\t{pos} := {nv}\t{note}\t1\n')
print(open(os.path.join(OUT, 'triage_controls.tsv')).read())
