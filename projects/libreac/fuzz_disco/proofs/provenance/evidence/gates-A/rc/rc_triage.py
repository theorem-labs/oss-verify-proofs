#!/usr/bin/env python3
"""rc_triage.py -- triage every non-SAME row of a roundconst v2 (by-value kept-donor-geometry gate) run over lib/A.

Kind: measurement; proves no function. Image A = fuzz_disco.asan; donor = cgif_file_fuzzer.asan.

Usage: rc_triage.py --rc RC.tsv --lib LIB --pin PIN --twin TWIN --cgif-pin CGIF_PIN --cgif-twin CGIF_TWIN
                    --hand HAND.tsv --out TRIAGE.tsv
  RC.tsv     the gate's output table (columns status, verdict, key, dst, src, sentence, idx, kind, value, class, ..)
  LIB        the checked tree (lib/ of the series base; lib/A and lib/Reusable are read)
  PIN, TWIN  image A and its unstripped twin (symbols from the twin, bytes from the pin)
  CGIF_PIN, CGIF_TWIN   the donor image and its unstripped twin (object sizes, p_align)
  HAND.tsv   hand rows (hand-triage.tsv beside this script)    TRIAGE.tsv  the output table (written)

A non-SAME row says only that a numeral the port kept equals some cgif image quantity (a span between two bounds, a
section or segment size, an object size or extent, possibly / 2, 4, 8, 4096) whose fuzz_disco counterpart differs. This
script decides what each such numeral is.

Method.
1. Rows: every row of RC.tsv whose status is not SAME. Rows are grouped by (dst file, dst line, value, kind).
2. Occurrences: the dst line is read with comments (* .. *) (nested, across lines) blanked; an occurrence is a numeral
   token (hex 0x.. or decimal, not part of an identifier) of the row's kind whose value equals the row's value. The
   row's idx is not a position on the line, so EVERY occurrence of the group is classified. If a group has more rows
   than occurrences, the script refuses. If rows = occurrences, each occurrence takes one row; if there are more
   occurrences than rows, all occurrences must share one class (else refusal) and the rows take it.
3. Classes: the hand table first (a row there names the group); else, for a start-up file, GENERATED; else the first
   rule below that answers, in this order. A measured rule whose measurement fails gives DEFECT where it says so, else
   no answer (the next rule is tried; a group no rule answers is a refusal until the hand table names it).
4. Output: one line per (file, line, value, kind, class) with n (rows), the statuses, the gate's class column, the
   triage class, the verdict (right / DEFECT) and evidence (the occurrence's text window, then the measurement or
   role). Sorted; no timestamps, no absolute paths. Exit 1 on any refusal (a row with no class, more rows than
   occurrences, a failed or unevaluable hand check, a hand row that matches no group) or any DEFECT row.

A "clause" (used by the last rules) is the smallest parenthesised group, conjunct (/\\, \\/, ->, =>, :=) or list item
(; , |) around the numeral. It "names an image address" when it holds an image name (TFIB_.., tfib_.., IMG_..,
YImgTop.., A_.., F_STD.., STDOUT_BUFA, STDERR_BUF, Asan_seg.., x2_..), a hex literal in [IMG_LO, IMG_TOP), or a decimal
in that range that is a twin symbol start, a pin section bound, a page-rounded segment bound or a named address (not a
power of two). IMG_LO / IMG_TOP: the pin's lowest / highest PT_LOAD bound rounded to a page.

The run-time classes (STRUCT-OFFSET, MODEL-CONSTANT, ALIGN, BOUND, RT-ARITH, STATE-VALUE, RT-CELL) answer only when the
sanitizer runtime is one build in both images. Measured: every sanitizer FUNC / OBJECT name (_ZN<k>__asan.., _ZZN..,
__asan_.., __sanitizer_.., __interceptor_.., lsan / ubsan alike) that both twins carry has the same size in both (counts
printed). Then a field offset, constant or bound of the runtime's structures is the same number in both builds.

Rules (classes), in order of evaluation:
GENERATED     the file is a start-up file (AB01 AB03 AB05 AB12 AD1k AD2i AD2j AF0m ACej AE3i) whose header lines 3-6
              carry the statement of how it was made from fuzz_disco.asan (checked). The role is read from the text
              (4096 * EVar k page-scaled variable, EVar / SOff / KRange (EVar k) variable index, a_off access offset,
              am_len map length, (ELit n) entry length, word value, (base, length) pair length, constant added to a
              symbolic term, KRange value / bound, seg slice, PHandoff index, ATp (-k) thread-pointer offset, an AF0m
              const cell zW (ANum A) V; else the first rule below that answers). Re-checks named per occurrence: gate 3
              codeptr checks every hex literal and every decimal >= 0x10000 of the nine files against the pin; gate 4
              ifchk checks AF0m's TFIB_CONST cells against each of AB01's 50 states; gate 5 cellcheck checks AF0m's
              file-backed cells against the pin (also measured here: a differing file-backed cell is a DEFECT). A
              decimal below 0x10000 no gate re-checks: it is the collector's own symbolic-state field (AB01, AB03), the
              planner's own field (AB05) or the generator's own text, and the evidence says so.
INSN-OFFSET   `(tfib_A_f + N)`: tfib_A_f / tfib_E_f of AB1w.v are the start and end of one twin FUNC, 0 <= N < its
              size, N even; where the line states the fetched word (`= Some (0x..%bv`), the pin's word at tfib_A_f + N
              equals it (else DEFECT).
DECODE-IMM    the last field of `decode_any W = Some (Jal|Branch|Lui|Load ..)`: the immediate field decoded here from
              W (literal, or `Definition W_x : bv 32 := ..`) equals it and the opcode matches; where the file fetches W
              (`fetch_word .. (A : word) = Some W_x`, `fetch_word .. (tfib_A_f + k) = Some (W%bv ..)`), the pin's word
              there is W (else DEFECT).
TABLE-COUNT   N of `build_table tfibsegs PC N%nat`: [PC, PC + 4N) is a run of whole twin FUNCs, each starting where the
              one before ends, the first at PC, the last ending at PC + 4N (else DEFECT): N is fuzz_disco's own size / 4.
OBJECT-FIELD  an offset from a named image address B: `B + N`, `B - N`, `B + -N`, `ATp (-N)` (B a name the file or
              AF0m.v / AFl1.v / AE3m.v / AE2p.v defines, as_inst B = A_ALLOCATOR, or a hex / named decimal literal),
              `B + k * N`, `v - B <= k * N`, or the offset of an (offset, width, value) triple of a stdout / stderr
              field list: B lies in a named twin object, B +/- k*N (+ width) stays inside it (its end bound allowed),
              and cgif's twin has a same-named object of the same size.
IMAGE-CELL    the value N of a cell at an image address A (`val_mem .. A w N`, `litW A N`, `flitW A N`,
              `region_ok_lit .. A w N`, an AE37.v x2_rodata triple): the pin's w file bytes at A equal N, or, past the
              file bytes, AF0m.v's const cell zW (ANum A) holds N.
RT-CELL       the same forms at an image address A past the file bytes for which AF0m.v has no const cell, inside a
              named twin object that cgif's twin has with the same size: a word the code writes at run time (a state
              after an allocation), not a start-up or image quantity.
STDOUT-BUFSIZE  STDOUT_BSZ (`Definition STDOUT_BSZ : Z := N`, `STDOUT_BSZ = N`, `store_ok_all .. N (Z_to_bv 64
              STDOUT_BUFA)`): the pin's 8 bytes at F_STDOUT + 96 (musl FILE.buf_size) equal N and the twin object
              holding STDOUT_BUFA is N + 8 bytes with STDOUT_BUFA = its start + 8 (else DEFECT).
DERIVED       inside `change E with F` / `replace E with F` and E = F re-evaluated here (Z.shiftl a b as a * 2^b,
              zcanon as the identity, an application `f x` as one unknown): exactly when closed, else at four sample
              points (every unknown 0; 65536; the k-th (k+3) * 2^20; the k-th (7k+11) * 2^23). Not for a numeral that
              is an argument of an application.
IMAGE-SHADOW  `2147450880 + N` / `0x7fff8000 + N` / `SHADOW_OFF + N` with N = IMG_LO / 8 or IMG_TOP / 8.
MODEL-CONSTANT  a named constant of the run-time model where it is defined or unfolded: class_size kBatchClass, FS_N,
              ck_rz / rz_size, ESTACK, STRNLEN_STK, path_max, page_size, req_size N, kMaxSize / 8.
STACK-OFFSET  a distance below a stack pointer: `sp0 - N`, `spZ regs - N`, `sp0 (- N)`, `(getr regs 2) - N`,
              `SOff 2 (-N)`, a saved-register slot `(SOff r 0, -N)` / `(SOff r 0) (-N)` / `saved HS (-N)`, a stack
              region of base variable 2, `mkChunk (-N)`, `wl_after .. 0 (-N)`, `ch 0 2 (-N)`, or a stack-window
              constant (FP_WIN, VP_WIN, RSTACK, DRSTACK).
LIST-SLICE    `firstn N`, `skipn N`, `dropAt / insAt / replAt N`, `seg l i N`, `length .. = N`: a position or length in
              the proof's own lists.
VAR-INDEX     an index of the proof's symbolic state: `SOff k`, `EVar k`, `epg k`, `ew E k`, `U_atom E k`,
              `rho_of E k`, `havoc E k`, `HEn k`, `Definition x : nat := k`, a `list nat` of indices, `(j < k)%nat`,
              `env_agree k`, the fresh-variable counter of vf_after_icpt / ss_after_call / `.. k RA_FX OSP_FX`, any
              `k%nat` with k < 4096, or a `(k, ..)` pair between `(k-1, ..)` and `(k+1, ..)`.
POW2-EXPONENT `2 ^ N`.
FACT-RANGE    inside the arguments of a value fact `mkAF lo hi k`, or lo / hi of `st_ok_add_fact .. k lo hi`.
PAGE          4096 (the page size: every PT_LOAD of the pin, the twin and the cgif pin has p_align 0x1000, measured)
              in a clause that names no image address.
STATE-VALUE   `ELit N`, `SLit N`, `CVal w (SLit N)`, `uE_litv E N`, `val_mem .. A w N` at a run-time address, in a
              clause that names no image address (the evidence says whether AB01.v holds the same ELit N).
STRUCT-OFFSET an offset from a named run-time base or model name (`T + N`, `T + t_cache + N`, `RGv + N`, `SMv + N`,
              `kHighMemBeg + N`, `SOff v N`, ..), a field offset or bound of a symbolic region (`mkRegion r ..`,
              `mkChunk N`, `(Some r, lo, hi)`), `AF N`, `at_ base N`, `o < N`, in a clause that names no image address.
ALIGN         1024, 2048, 8192 or 32768 as a modulus, alignment or factor (`x mod N`, `AL N x`, `mod0_factor x k N`,
              `zone3 x N`, `q * N`, `N * q`, a divisibility witness `exists (..)`).
BOUND         the numeral alone is one side of a comparison (`N <= v`, `v <= N`, `v < N`, `n <=? N`) in a clause that
              names no image address.
RT-ARITH      an operand of +, -, *, / or mod in a clause that names no image address.
DEFECT        a measured rule whose measurement fails where the rule says so, or a hand row with verdict DEFECT.
Hand rows (HAND.tsv: file, line, value, kind, class, verdict, check, reason) name one group each; `check` is a Python
expression over the pin, the twin, cgif's twin and the checked files, evaluated here, and must hold.
"""
import argparse, collections, csv, hashlib, os, re, sys

from elftools.elf.elffile import ELFFile

ap = argparse.ArgumentParser()
for k in ('rc', 'lib', 'pin', 'twin', 'cgif-pin', 'cgif-twin', 'hand', 'out'):
    ap.add_argument('--' + k, required=True)
a = ap.parse_args()


def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


print(f'rc table sha256 {sha(a.rc)}')
print(f'pin sha256 {sha(a.pin)}; twin sha256 {sha(a.twin)}')
print(f'cgif pin sha256 {sha(a.cgif_pin)}; cgif twin sha256 {sha(a.cgif_twin)}')

# ------------------------------------------------------------------------------------------------ the gate's rows
csv.field_size_limit(1 << 30)
with open(a.rc, newline='') as f:
    rd = csv.reader(f, delimiter='\t')
    head = next(rd)
    col = {c: i for i, c in enumerate(head)}
    rows = [r for r in rd if r[col['status']] != 'SAME']
print(f'non-SAME rows {len(rows)}: ' + ', '.join(f'{k} {v}' for k, v in sorted(collections.Counter(r[col["status"]] for r in rows).items())))

# ------------------------------------------------------------------------------------------------ image facts


class Image:
    def __init__(self, path):
        self.raw = open(path, 'rb').read()
        self.elf = ELFFile(open(path, 'rb'))
        self.loads = [s for s in self.elf.iter_segments() if s['p_type'] == 'PT_LOAD']
        self.funcs, self.objs = [], collections.defaultdict(list)
        st = self.elf.get_section_by_name('.symtab')
        if st is not None:
            for s in st.iter_symbols():
                t = s['st_info']['type']
                if t == 'STT_FUNC' and s.name:
                    self.funcs.append((s['st_value'], s['st_size'], s.name))
                elif t == 'STT_OBJECT' and s.name:
                    self.objs[s.name].append((s['st_value'], s['st_size']))
        self.fstart = collections.defaultdict(list)
        for x, sz, n in self.funcs:
            self.fstart[x].append((sz, n))
        self.olist = sorted((x, sz, n) for n, v in self.objs.items() for x, sz in v)

    def filebytes(self, addr, n):
        for s in self.loads:
            if s['p_vaddr'] <= addr and addr + n <= s['p_vaddr'] + s['p_filesz']:
                o = s['p_offset'] + addr - s['p_vaddr']
                return self.raw[o:o + n]
        return None

    def word(self, addr, n=4):
        b = self.filebytes(addr, n)
        return int.from_bytes(b, 'little') if b is not None else None

    def obj_at(self, addr):   # the named object of the image that holds addr (the smallest one)
        c = [(sz, x, n) for x, sz, n in self.olist if x <= addr < x + sz]
        return min(c) if c else None


PIN, TWIN, CPIN, CTWIN = Image(a.pin), Image(a.twin), Image(a.cgif_pin), Image(a.cgif_twin)
ALIGN = {k: sorted({s['p_align'] for s in im.loads}) for k, im in (('pin', PIN), ('twin', TWIN), ('cgif pin', CPIN))}
PAGE_OK = all(v == [0x1000] for v in ALIGN.values())
print('PT_LOAD p_align: ' + '; '.join(f'{k} {[hex(x) for x in v]}' for k, v in ALIGN.items()) + f' -> page size 4096 in both builds: {PAGE_OK}')
RT_NAME = re.compile(r'_ZZ?N\d+__(?:asan|sanitizer|lsan|ubsan)|__(?:asan|sanitizer|lsan|ubsan|interceptor)')


def rt_sizes(im):   # sizes of the sanitizer runtime's FUNC / OBJECT symbols, by (type, name)
    d = collections.defaultdict(set)
    for x, sz, n in im.funcs:
        if RT_NAME.match(n):
            d[('F', n)].add(sz)
    for n, v in im.objs.items():
        if RT_NAME.match(n):
            d[('O', n)].update(sz for _, sz in v)
    return d


RT_A, RT_C = rt_sizes(TWIN), rt_sizes(CTWIN)
RT_COMMON = set(RT_A) & set(RT_C)
RT_EQ = sum(1 for k in RT_COMMON if RT_A[k] == RT_C[k])
RT_SAME = bool(RT_COMMON) and RT_EQ == len(RT_COMMON)
print(f'sanitizer runtime: {len(RT_COMMON)} FUNC / OBJECT names in both twins ({len(RT_A)} in the twin, {len(RT_C)} in '
      f'cgif\'s), {RT_EQ} of them the same size in both -> one runtime build: {RT_SAME}')

# ------------------------------------------------------------------------------------------------ the checked files


def strip_comments(t):   # (* *) comments (nested) to blanks, newlines kept, strings left alone; same length
    out, i, n, depth, instr = [], 0, len(t), 0, False
    while i < n:
        c = t[i]
        if depth == 0 and instr:
            out.append(c)
            if c == '"':
                if t.startswith('""', i):
                    out.append('"')
                    i += 2
                    continue
                instr = False
            i += 1
        elif t.startswith('(*', i):
            depth += 1
            out.append('  ')
            i += 2
        elif depth and t.startswith('*)', i):
            depth -= 1
            out.append('  ')
            i += 2
        elif depth:
            out.append('\n' if c == '\n' else ' ')
            i += 1
        else:
            instr = c == '"'
            out.append(c)
            i += 1
    return ''.join(out)


_files = {}


def lines_of(f):   # (raw lines, comment-stripped lines) of a lib file
    if f not in _files:
        raw = open(os.path.join(a.lib, f)).read()
        _files[f] = (raw.split('\n'), strip_comments(raw).split('\n'))
    return _files[f]


def defs_of(f):    # Definition NAME : Z := NUMERAL. of a file (comment-stripped)
    return {n: int(v, 0) for n, v in re.findall(r'Definition (\w+) : Z := (-?0x[0-9a-fA-F]+|-?\d+)\.', '\n'.join(lines_of(f)[1]))}


TOK = re.compile(r"(?<![A-Za-z0-9_'])(0[xX][0-9a-fA-F]+|\d+)(?![A-Za-z0-9_'])")

# ------------------------------------------------------------------------------------------------ lib facts the rules read
AB1W = defs_of('A/AB1w.v')                   # tfib_A_<f> / tfib_E_<f>: start / end of each function of the image
NAMED = {k: v for k, v in defs_of('A/AF0m.v').items() if k.startswith('TFIB_')}   # named image addresses
for f, names in (('A/AFl1.v', ('A_ALLOCATOR',)), ('A/AE3m.v', ('F_STDOUT', 'STDOUT_BUFA')), ('A/AE2p.v', ('F_STDERR', 'STDERR_BUF'))):
    d = defs_of(f)
    for n in names:
        NAMED[n] = d[n]
NAMED['as_inst B'] = NAMED['A_ALLOCATOR']     # AFfc.v, AFfi.v, AFfr.v: Lemma AINST : as_inst B = A_ALLOCATOR
MODEL = {}
for f in ('Reusable/YG00.v', 'Reusable/YG0d.v', 'Reusable/YG0f.v'):
    MODEL.update(defs_of(f))
AF0M_TEXT = '\n'.join(lines_of('A/AF0m.v')[1])
print('named addresses: ' + ', '.join(f'{k} {v:#x}' for k, v in sorted(NAMED.items())))


def enclosing_def(f, ln):   # the name of the last Definition / Lemma / Theorem opened at or above line ln
    st = lines_of(f)[1]
    for i in range(ln - 1, -1, -1):
        m = re.match(r'\s*(?:Definition|Lemma|Theorem|Fixpoint|Hypothesis)\s+(\w+)', st[i])
        if m:
            return m.group(1)
    return ''


def af0m_cell(addr, w):    # AF0m.v's const cell zW (ANum addr) V, or None
    m = re.findall(r'z%d \(ANum (?:%s|%s)\) (0x[0-9a-fA-F]+|\d+)' % (w, hex(addr), hex(addr).upper().replace('0X', '0x')), AF0M_TEXT)
    return int(m[0], 0) if len(m) == 1 else None


def imm_field(op, w):      # (opcode matches, raw immediate field) as decode_any reports it
    return {'Jal': (w & 0x7f == 0x6f, (w >> 31 & 1) << 20 | (w >> 12 & 0xff) << 12 | (w >> 20 & 1) << 11 | (w >> 21 & 0x3ff) << 1),
            'Branch': (w & 0x7f == 0x63, (w >> 31 & 1) << 12 | (w >> 7 & 1) << 11 | (w >> 25 & 0x3f) << 5 | (w >> 8 & 0xf) << 1),
            'Lui': (w & 0x7f == 0x37, w >> 12),
            'Load': (w & 0x7f == 0x03, w >> 20)}[op]


# ------------------------------------------------------------------------------------------------ occurrences
class Occ:
    def __init__(self, f, ln, s, m):
        self.f, self.ln, self.s = f, ln, s
        self.pos, self.end, self.tok = m.start(1), m.end(1), m.group(1)
        self.kind = 'hex' if self.tok[:2].lower() == '0x' else 'dec'
        self.val = int(self.tok, 16) if self.kind == 'hex' else int(self.tok, 10)
        self.L, self.R = s[:self.pos], s[self.end:]

    def win(self, w=30):
        t = self.s[max(0, self.pos - w):self.pos] + '<' + self.tok + '>' + self.s[self.end:self.end + w]
        return re.sub(r'\s+', ' ', t).strip()


def occurrences(f, ln, val, kind):
    s = lines_of(f)[1][ln - 1]
    return [o for o in (Occ(f, ln, s, m) for m in TOK.finditer(s)) if o.kind == kind and o.val == val]


def endsw(o, pat, n=240):
    return re.search('(?:' + pat + r')$', o.L[-n:])


def startsw(o, pat, n=240):
    return re.match('(?:' + pat + ')', o.R[:n])


# ------------------------------------------------------------------------------------------------ the rules
RULES = collections.OrderedDict()   # class -> its rule (the docstring states the same text)
CHECKS = []                         # (class, function): first function that answers gives the occurrence its class


def rule(cls, text=None):
    def deco(fn):
        if text:
            RULES[cls] = text
        CHECKS.append((cls, fn))
        return fn
    return deco


def regex_rule(cls, text, L=None, R=None, vals=None, line=None):
    def fn(o):
        if vals is not None and o.val not in vals:
            return None
        if L and not endsw(o, L):
            return None
        if R and not startsw(o, R):
            return None
        if line and not re.search(line, o.s):
            return None
        return ''
    rule(cls, text)(fn)


@rule('INSN-OFFSET', 'the numeral N is written `(tfib_A_<f> + N)` (an instruction address inside function f). Measured: '
                     'tfib_A_<f> / tfib_E_<f> of AB1w.v are the start and end of one FUNC symbol of the twin, 0 <= N < its '
                     'size, N even; where the line states the word fetched there (`= Some (0x..%bv`), the pin\'s word at '
                     'tfib_A_<f> + N equals it')
def r_insn(o):
    m = endsw(o, r'\(tfib_A_(\w+) \+ ')
    if not m:
        return None
    n = m.group(1)
    A, E = AB1W.get('tfib_A_' + n), AB1W.get('tfib_E_' + n)
    if A is None or E is None:
        return ('DEFECT', f'tfib_A_{n} / tfib_E_{n} not both defined in AB1w.v')
    fn = sorted(nm for sz, nm in TWIN.fstart.get(A, []) if sz == E - A)
    ok = bool(fn) and 0 <= o.val < E - A and o.val % 2 == 0
    ev = f'tfib_A_{n} {A:#x}, tfib_E_{n} {E:#x} = twin FUNC {fn[0] if fn else "(none)"} (size {E - A:#x}); +{o.val:#x} inside'
    w = startsw(o, r'\)\) = Some \((0x[0-9a-fA-F]+)%bv')
    if w:
        pw, sw = PIN.word(A + o.val), int(w.group(1), 16)
        ok = ok and pw == sw
        ev += f'; pin word at {A + o.val:#x} = {pw:#010x}' + (' = stated' if pw == sw else f' != stated {sw:#010x}')
    return ev if ok else ('DEFECT', ev)


DEC = re.compile(r'decode_any (?:\((0x[0-9a-fA-F]+)%bv : bv 32\)|(W_[0-9a-fA-F]+)) = Some \((Jal|Branch|Lui|Load) ([^(),]*), 4%Z\)')


@rule('DECODE-IMM', 'the numeral is the last field (the immediate) of `decode_any W = Some (Jal|Branch|Lui|Load ..)`. '
                    'Measured: the field decoded here from W (literal, or `Definition W_x : bv 32 := ..` of the file) equals '
                    'it and the opcode matches; where the file fetches W (`fetch_word .. (A : word) = Some W_x`, or '
                    '`fetch_word .. (tfib_A_f + k) = Some (W%bv ..)`), the pin\'s word at that address is W')
def r_decode(o):
    for m in DEC.finditer(o.s):
        if not (m.start(4) <= o.pos and o.end == m.end(4)):
            continue
        txt = '\n'.join(lines_of(o.f)[1])
        if m.group(1):
            W = int(m.group(1), 16)
            fx = [(AB1W.get('tfib_A_' + fn, -1 << 40) + int(k, 16)) for fn, k, ww in re.findall(
                r'fetch_word \w+ \(Z_to_bv 64 \(tfib_A_(\w+) \+ (0x[0-9a-fA-F]+)\)\) = Some \((0x[0-9a-fA-F]+)%bv', txt)
                if int(ww, 16) == W]
        else:
            d = re.findall(r'Definition %s : bv 32 := (0x[0-9a-fA-F]+)\.' % m.group(2), txt)
            if len(d) != 1:
                return ('DEFECT', f'{m.group(2)} not defined once in the file')
            W = int(d[0], 16)
            fx = [int(x, 16) for x in re.findall(r'fetch_word [\w.]+ \((0x[0-9a-fA-F]+) : word\) = Some %s\b' % m.group(2), txt)]
        op = m.group(3)
        okop, fld = imm_field(op, W)
        ok = okop and fld == o.val
        ev = f'{op} immediate field of {W:#010x} = {fld}'
        for x in sorted(set(fx))[:1]:
            pw = PIN.word(x)
            ok = ok and pw == W
            ev += f'; fetched at {x:#x}: pin word {pw:#010x}' + (' = W' if pw == W else ' != W')
        if not fx:
            ev += '; (the word is not fetched in this file)'
        return ev if ok else ('DEFECT', ev)
    return None


@rule('TABLE-COUNT', 'the numeral N is the word count of `build_table tfibsegs PC N%nat` (decode N words from PC). '
                     'Measured: [PC, PC + 4N) is a run of whole FUNC symbols of the twin, each starting where the one '
                     'before ends, the first at PC and the last ending at PC + 4N, so N is fuzz_disco.asan\'s own range size / 4')
def r_table(o):
    m = endsw(o, r'build_table tfibsegs (0x[0-9a-fA-F]+) ')
    if not m or not startsw(o, '%nat'):
        return None
    pc = int(m.group(1), 16)
    end, cur, k = pc + 4 * o.val, pc, 0
    while cur < end:
        c = [sz for sz, _ in TWIN.fstart.get(cur, []) if sz > 0]
        if not c:
            break
        cur += max(c)
        k += 1
    ev = f'[{pc:#x}, {end:#x}) = {k} contiguous twin FUNCs, run ends at {cur:#x}'
    return ev if cur == end else ('DEFECT', ev)


def addr_of(f, b):   # a hex literal, a decimal literal equal to a named address, or a name the file / NAMED defines
    if re.fullmatch(r'0x[0-9a-fA-F]+', b):
        return int(b, 16)
    if b.isdigit():
        return int(b) if int(b) in NAMED.values() else None
    m = re.fullmatch(r'\(?([A-Za-z_]\w*) \+ (0x[0-9a-fA-F]+|\d+|[A-Za-z_]\w*)\)?', b)
    if m:
        x, k = addr_of(f, m.group(1)), m.group(2)
        k = int(k, 16) if k.startswith('0x') else int(k) if k.isdigit() else defs_of(f).get(k, MODEL.get(k))
        return None if x is None or k is None else x + k
    return defs_of(f).get(b, NAMED.get(b))


OBJ_P = [r"(?<![\w.'])(?P<b>as_inst B|[A-Za-z_][\w']*|\d{5,}) (?P<op>\+ -|\+ |- )\(?",
         r'\b(?P<b>ATp) \((?P<op>-)',
         r'(?P<b>0x[0-9a-fA-F]{5,}) (?P<op>\+|<=) (?P<mul>\d+) \* ']


@rule('OBJECT-FIELD', 'the numeral is an offset from a named image address B: `B + N`, `B - N`, `B + -N`, `ATp (-N)` (B a '
                      'name the file or AF0m.v / AFl1.v / AE3m.v / AE2p.v defines as an address, e.g. TFIB_INST, A_ALLOCATOR '
                      '(= as_inst B), TFIB_TP, TP, F_STDOUT, or a hex / decimal literal equal to one), `B + k * N` / '
                      '`v - B <= k * N`, or the offset of an (offset, width, value) triple of a stdout / stderr field list. '
                      'Measured: B lies in a named object of the twin, B +/- k*N (+ width) stays inside that object, and '
                      'cgif\'s twin has the same-named object of the same size (the same layout, so the field offset is '
                      'not a quantity that moved between the builds)')
def r_object(o):
    base = op = None
    mul, width = 1, 1
    for pat in OBJ_P:
        m = endsw(o, pat)
        if m:
            bname = m.group('b')
            base = NAMED['TFIB_TP'] if bname == 'ATp' else addr_of(o.f, bname)
            op = m.group('op').strip()
            mul = int(m.group('mul')) if m.groupdict().get('mul') else 1
            if base is not None and TWIN.obj_at(base) is not None:
                break
            base = None
    if base is None:
        fl = startsw(o, r', (\d+)%N, ')
        dn = enclosing_def(o.f, o.ln)
        if not (fl and endsw(o, r'(?:^|[\[;] ?)\(') and re.match(r'(stdout|stderr)_fields', dn)):
            return None
        bname = 'F_STDOUT' if dn.startswith('stdout') else 'F_STDERR'
        base, op, width = NAMED[bname], '+', int(fl.group(1))
    off = -o.val * mul if op in ('-', '+ -') else o.val * mul
    sz, x, nm = TWIN.obj_at(base)
    tgt = base + off
    csz = sorted(s for _, s in CTWIN.objs.get(nm, []))
    ok = x <= tgt and tgt + (width if width > 1 else 0) <= x + sz and sz in csz
    short = nm if len(nm) <= 40 else nm[:37] + '...'
    ev = (f'{bname} {base:#x} = {short} + {base - x:#x} (twin, size {sz}); {"-" if off < 0 else "+"}{abs(off):#x} -> '
          f'+{tgt - x:#x}' + (' (the end bound)' if tgt == x + sz else ' inside') +
          f'; cgif object sizes {csz}' + (' (same)' if sz in csz else ''))
    return ev if ok else None


CELL_P = (r"(?:\bval_mem [\w.]+ (?:\([^()]*(?:\([^()]*\))?[^()]*\)|[\w']+) |\bregion_ok_lit \w+ [\w']+ |\b(?:f?lit|z)(?P<w1>\d) "
          r'(?:\(ANum )?)(?P<a>\([A-Za-z_]\w* \+ (?:0x[0-9a-fA-F]+|\d+|[A-Za-z_]\w*)\)|0x[0-9a-fA-F]+|[A-Za-z_]\w*)\)?(?: (?P<w2>\d+))? ')


@rule('IMAGE-CELL', 'the numeral is the value of a cell at an image address: `val_mem .. A w N`, `litW A N` / `flitW A N`, '
                    '`region_ok_lit .. A w N`, or an (address, width, [(offset, width, value)]) cell of AE37.v x2_rodata. '
                    'Measured: the pin\'s w file bytes at A equal N, or, past the file bytes, AF0m.v\'s const cell zW (ANum A) '
                    'holds N (gate 4 ifchk checks those cells against each of AB01\'s 50 states)')
def r_cell(o):
    m = endsw(o, r'\((0x[0-9a-fA-F]+), \d+, \[(?:\(\d+, \d+%N, [^()]*\); )*\((\d+), (\d+)%N, ')
    if m and o.f == 'A/AE37.v':
        ad, w = int(m.group(1), 16) + int(m.group(2)), int(m.group(3))
    else:
        m = endsw(o, CELL_P)
        if not m or not (m.group('w1') or m.group('w2')):
            return None
        ad = addr_of(o.f, m.group('a'))
        if ad is None or TWIN.obj_at(ad) is None and PIN.filebytes(ad, 1) is None:
            return None
        w = int(m.group('w2') or m.group('w1'))
    pv = PIN.word(ad, w)
    if pv is not None:
        return f'pin bytes at {ad:#x} ({w}) = {pv:#x}' if pv == o.val else None
    cv = af0m_cell(ad, w)
    return f'{ad:#x} is past the file bytes; AF0m z{w} (ANum {ad:#x}) = {cv:#x}' if cv == o.val else None


@rule('RT-CELL', 'the numeral is the value of `val_mem .. A w N` / `litW A N` at an image address A that the start-up state '
                 'does not fix: A is past the file bytes (.bss) and AF0m.v has no const cell zW (ANum A), so the claim is '
                 'about a word the code writes at run time (a hypothesis or result about the state after an allocation), '
                 'not a start-up or image quantity. Measured: A past the file bytes, no AF0m cell, A inside a named twin '
                 'object that cgif\'s twin has with the same size')
def r_rtcell(o):
    m = endsw(o, CELL_P)
    if not m or not (m.group('w1') or m.group('w2')):
        return None
    ad = addr_of(o.f, m.group('a'))
    w = int(m.group('w2') or m.group('w1'))
    ob = TWIN.obj_at(ad) if ad is not None else None
    if ob is None or PIN.filebytes(ad, w) is not None or af0m_cell(ad, w) is not None:
        return None
    csz = sorted(s for _, s in CTWIN.objs.get(ob[2], []))
    if ob[0] not in csz:
        return None
    nm = ob[2] if len(ob[2]) <= 40 else ob[2][:37] + '...'
    return f'{m.group("a")} {ad:#x} = {nm} + {ad - ob[1]:#x} (size {ob[0]}, same in cgif); no file bytes, no AF0m z{w} cell'


@rule('STDOUT-BUFSIZE', 'the numeral is STDOUT_BSZ (`Definition STDOUT_BSZ : Z := N`, `STDOUT_BSZ = N`, or the length of '
                        '`store_ok_all .. N (Z_to_bv 64 STDOUT_BUFA)`). Measured: the pin\'s 8 bytes at F_STDOUT + 96 (musl '
                        'FILE.buf_size) equal N, and the twin object holding STDOUT_BUFA is N + 8 bytes (musl buf[BUFSIZ + '
                        'UNGET], STDOUT_BUFA = its start + 8)')
def r_bsz(o):
    if not (endsw(o, r'Definition STDOUT_BSZ : Z := |\bSTDOUT_BSZ = ') or
            (endsw(o, r'\bstore_ok_all \w+ \w+ ') and startsw(o, r' \(Z_to_bv 64 STDOUT_BUFA\)'))):
        return None
    v = PIN.word(NAMED['F_STDOUT'] + 96, 8)
    ob = TWIN.obj_at(NAMED['STDOUT_BUFA'])
    ok = v == o.val and ob is not None and ob[0] == o.val + 8 and NAMED['STDOUT_BUFA'] == ob[1] + 8
    ev = f'pin u64 at F_STDOUT + 96 = {v}; STDOUT_BUFA = {ob[2] if ob else "?"} + 8, object size {ob[0] if ob else "?"}'
    return ev if ok else ('DEFECT', ev)


def _atoms(e):   # tokens of an arithmetic side; an application `f x y` (names / numerals after a name) is one atom
    t = re.sub(r'%(?:Z|nat)\b', '', e)
    t = re.sub(r'\bZ\.shiftl (\w+) (\w+)', r'(\1 * 2 ^ \2)', t)
    t = re.sub(r'\bzcanon\b', '', t)
    toks = re.findall(r"0x[0-9a-fA-F]+|\d+|[A-Za-z_][\w'.]*|[-+*/^()]|\S", t)
    out = []
    for k in toks:
        isname = bool(re.fullmatch(r"[A-Za-z_][\w'.]*", k)) and k != 'mod'
        isnum = bool(re.fullmatch(r'0x[0-9a-fA-F]+|\d+', k))
        if out and out[-1][0] == 'v' and (isname or isnum):
            out[-1] = ('v', out[-1][1] + ' ' + k)
        elif isname:
            out.append(('v', k))
        else:
            out.append(('o', k))
    return out


def _closed_eval(e, env):
    py = []
    for typ, k in _atoms(e):
        if typ == 'v':
            if '.' in k:
                raise ValueError(k)
            py.append(str(env(k)))
        elif re.fullmatch(r'0x[0-9a-fA-F]+', k):
            py.append(str(int(k, 16)))
        elif k.isdigit():
            py.append(str(int(k, 10)))
        elif k in ('^', '/', 'mod'):
            py.append({'^': '**', '/': '//', 'mod': '%'}[k])
        elif k in '+-*()':
            py.append(k)
        else:
            raise ValueError(k)
    for x, y in zip(py, py[1:]):   # two operands side by side (an application the atoms did not merge): unreadable
        if (x == ')' or x[0].isdigit()) and (y == '(' or y[0].isdigit()):
            raise ValueError(x + ' ' + y)
    return eval(' '.join(py), {'__builtins__': {}})


def _side(s, i):   # one argument at s[i]: a balanced ( .. ) or one atom; (start, end) or None
    if i < len(s) and s[i] == '(':
        d = 0
        for j in range(i, len(s)):
            d += {'(': 1, ')': -1}.get(s[j], 0)
            if d == 0:
                return i, j + 1
        return None
    m = re.match(r"-?[\w'%]+(?:\.[A-Za-z_][\w']*)*", s[i:])
    return (i, i + m.end()) if m else None


@rule('DERIVED', 'the numeral is inside `change E with F` or `replace E with F` (a step the kernel checks) and E = F holds '
                 'when re-evaluated here (Z.shiftl a b read as a * 2^b, zcanon as the identity): exactly when both sides '
                 'are closed, else at four sample points (every name 0; every name 65536; the k-th name (k+3) * 2^20; the '
                 'k-th name (7k+11) * 2^23): the numeral is fixed by the other literals of the identity')
def r_derived(o):
    m = endsw(o, r"(?<![\w'.])([A-Za-z_][\w'.]*) ")
    if m and m.group(1) not in ('mod', 'with', 'change', 'replace'):
        return None    # an argument of an application `f N`: the identity does not fix it
    for m in re.finditer(r'\b(?:change|replace) ', o.s):
        a1 = _side(o.s, m.end())
        if not a1 or not o.s.startswith(' with ', a1[1]):
            continue
        a2 = _side(o.s, a1[1] + 6)
        if not a2 or not (a1[0] <= o.pos < a1[1] or a2[0] <= o.pos < a2[1]):
            continue
        e1, e2 = o.s[a1[0]:a1[1]], o.s[a2[0]:a2[1]]
        try:
            names = sorted({k for typ, k in _atoms(e1) + _atoms(e2) if typ == 'v'})
        except Exception:   # noqa: BLE001
            continue
        if any('.' in n for n in names):
            continue
        pts = [lambda n: 0, lambda n: 65536, lambda n: (names.index(n) + 3) << 20, lambda n: (7 * names.index(n) + 11) << 23]
        try:
            vals = [(_closed_eval(e1, p), _closed_eval(e2, p)) for p in (pts[:1] if not names else pts)]
        except Exception:   # noqa: BLE001 - a side the evaluator cannot read gives this rule no answer
            continue
        if all(x == y for x, y in vals):
            e = re.sub(r'\s+', ' ', f'{e1} = {e2}')
            return (e if len(e) <= 90 else e[:87] + '...') + (f' (= {vals[0][0]})' if not names else ' at 4 sample points')
    return None


SEGS = sorted((s['p_vaddr'] & ~0xfff, (s['p_vaddr'] + s['p_memsz'] + 0xfff) & ~0xfff) for s in PIN.loads)
IMG_LO, IMG_TOP = SEGS[0][0], SEGS[-1][1]
print(f'image bounds (pin PT_LOADs, page-rounded): IMG_LO {IMG_LO:#x}, IMG_TOP {IMG_TOP:#x}')


@rule('IMAGE-SHADOW', 'the numeral N follows the shadow offset (`2147450880 + N`, 0x7fff8000 + N) and N = IMG_LO / 8 or '
                      'IMG_TOP / 8, the shadow of the image bounds. Measured: IMG_LO / IMG_TOP = the pin\'s lowest / highest '
                      'PT_LOAD bound rounded to a page')
def r_shadow(o):
    if not endsw(o, r'\b(?:2147450880|0x7fff8000|SHADOW_OFF) \+ '):
        return None
    if o.val in (IMG_LO // 8, IMG_TOP // 8):
        return f'{o.val} = {"IMG_LO" if o.val == IMG_LO // 8 else "IMG_TOP"} {IMG_LO if o.val == IMG_LO // 8 else IMG_TOP:#x} / 8'
    return None


regex_rule('MODEL-CONSTANT', 'the numeral is the value of a named constant of the run-time model, stated where the name is '
                             'defined or unfolded: `class_size kBatchClass = N` (Reusable YG00 kBatchBytes), `FS_N`, '
                             '`ck_rz ..` / `rz_size ..` (a chunk redzone), `ESTACK`, `STRNLEN_STK`, `path_max`, `req_size N`, '
                             '`kMaxSize / 8`: a constant of the sanitizer allocator / fake stack / C library model, not a '
                             'quantity of the image',
           L=r'\b(?:class_size kBatchClass|FS_N|ck_rz \w+|rz_size \w+|ESTACK|STRNLEN_STK) :?= |Definition FS_N : Z := |'
             r'\breq_size \(?|change (?:\((?:class_size kBatchClass|kMaxSize / 8|req_size \d+)\)|path_max|page_size) with |'
             r'\((?:HN|CS) : (?:FS_N|class_size kBatchClass) = ')

STACK_L = (r'\bsp\w*(?: regs)? - \(?|\bsp\w* \(- ?|\bsp\w* - \d+ \+ |\(getr regs\w* 2\) - |\bSOff 2 \(-|\(SOff \d+ 0\)?,? \(?-|'
           r'\bch 0 2 \(-|\bwl_after \w+ 0 \(-|mkRegion \(Some 2%nat\) \(- (?:\d+\) -?\d+ \(- )?|\(Some 2%nat, -|mkChunk \(-|'
           r'\bsaved \w+ \(-|Definition (?:FP_WIN|VP_WIN|RSTACK|DRSTACK) : Z := |\(H\w+ : (?:FP_WIN|VP_WIN) = ')
regex_rule('STACK-OFFSET', 'the numeral is a distance below a stack pointer: `sp0 - N`, `spZ regs - N`, `sp0 (- N)`, '
                           '`(getr regs 2) - N` / `SOff 2 (-N)` (x2 = sp), a saved-register slot `(SOff r 0, -N)` / `(SOff r 0) '
                           '(-N)` / `saved HS (-N)`, a stack region of base variable 2 (`mkRegion (Some 2%nat) (- N) ..`, '
                           '`(Some 2%nat, -N, ..)`), a negative chunk offset `mkChunk (-N)`, a stack window `wl_after .. 0 '
                           '(-N)`, or a stack-window constant (FP_WIN, VP_WIN, RSTACK, DRSTACK): a frame offset, not a '
                           'quantity of the image', L=STACK_L)

regex_rule('LIST-SLICE', 'the numeral is a position or length in one of the proof\'s own lists: `firstn N`, `skipn N`, '
                         '`dropAt N`, `seg l i N`, `length .. = N%nat` (vm_compute steps the kernel checks)',
           L=r'\b(?:firstn|skipn|dropAt|insAt|replAt) \(?|\bseg \w+ (?:\d+ )?|\blength [^=]*= ')
VAR_L = (r"\b(?:SOff|EVar|epg|U_atom \w+|ew \w+'?|rho_of \w+|havoc \w+|memvo? \w+(?: \d+%nat)?|vf_after_icpt|"
         r"ss_after_call \w+ \w+|st_ok_after_call \w+|xafterD|HEn\w*|ltHAV|upg|st_ok_forget_reg _ _ _ \w+%bv|ss_atoms_lt|"
         r"env_agree|st_ok_set_regs_mem \w+|st_ok_agree \w+|V|PG|AF|AFo \w+|G|BV\w*|CA \d+|OB \d+%bv|CK\d* \d+%nat|WPRES|"
         r"chunk_atom\w*(?: [\w']+)*|condZ \w+ BC_\w+|vf_add_fact \w+|st_ok_add_fact \w+ \w+ _) \(?|"
         r"Definition \w+ : nat := |\(j < |\benv_agree\w* .*\] |apresent_off \(w_H W\) \w+ _ _ |: list nat := \[(?:\d+; )*")
regex_rule('VAR-INDEX', 'the numeral is an index of the proof\'s own symbolic state: a variable / slot / fact index '
                        '(`SOff k ..`, `EVar k`, `epg k`, `ew E k`, `U_atom E k ..`, `rho_of E k`, `havoc E k`, `HEn k%nat`, a '
                        '`k%nat` argument, `Definition x : nat := k`, a `list nat` of indices, `(j < k)%nat`, `env_agree k`, '
                        'a `(k, ..)` pair numbered between k-1 and k+1, the fresh-variable counter of vf_after_icpt / '
                        'ss_after_call / an after-intercept lemma `.. k RA_FX OSP_FX`), not a quantity of the image', L=VAR_L)
regex_rule('VAR-INDEX', None, R=r'%nat\b|\s+RA_FX OSP_FX\b', vals=set(range(0, 4096)))


@rule('VAR-INDEX')
def r_slot(o):   # (k, off) in a list whose neighbouring pairs are numbered k-1 / k+1
    if not (endsw(o, r'(?:\[|; )\(') and startsw(o, r', -?\d+\)')):
        return None
    if f'({o.val - 1}, ' in o.L[-40:] or o.R.find(f'; ({o.val + 1}, ') in range(0, 30):
        return f'pair ({o.val}, ..) between ({o.val - 1}, ..) / ({o.val + 1}, ..)'
    return None


regex_rule('POW2-EXPONENT', 'the numeral is an exponent `2 ^ N` (2^37 = 32 * 2^32, a bound of the allocator model\'s '
                            'space): a power of two, not a quantity of the image', L=r'\b2 ?\^ ?\(?')


@rule('FACT-RANGE', 'the numeral is inside the arguments of a value fact `mkAF lo hi k` (the run-time value lies in [lo, '
                    'hi] and is a multiple of 2^k) or the lo / hi argument of `st_ok_add_fact .. k lo hi`: a range of a '
                    'run-time value the proof records (a pointer above the first page, a size under a ceiling), not an '
                    'image quantity')
def r_fact(o):
    if endsw(o, r'\bst_ok_add_fact \w+ \w+ _ \d+ (?:\d+ )?'):
        return ''
    for m in reversed(list(re.finditer(r'\bmkAF ', o.L))):
        i = m.end()
        for _ in range(3):
            sp = _side(o.s, i)
            if not sp:
                break
            if sp[0] <= o.pos < sp[1]:
                return ''
            i = sp[1] + 1
    return None


IMGNAME = re.compile(r"\b(?:TFIB_\w+|tfib_\w+|IMG_\w+|YImgTop\.\w+|A_\w+|F_STD\w+|STDOUT_BUFA|STDERR_BUF|Asan_seg\w*|"
                     r"x2_\w+|[A-Z]_[0-9a-f]{5,})\b")
IMG_POINTS = ({x for x, _, _ in TWIN.funcs} | {x for x, _, _ in TWIN.olist} | set(NAMED.values()) | set(AB1W.values()) |
              {s['sh_addr'] + k * s['sh_size'] for s in PIN.elf.iter_sections() if s['sh_addr'] for k in (0, 1)} |
              {b for seg in SEGS for b in seg})
SEP2 = ('/\\', '\\/', '->', '<-', '=>', ':=')


def clause(o):   # the text of the smallest parenthesised group or conjunct / list item around the numeral
    s, i, j, d = o.s, o.pos, o.end, 0
    while i > 0:
        c = s[i - 1]
        if c == ')':
            d += 1
        elif c == '(':
            if d == 0:
                break
            d -= 1
        elif d == 0 and (c in ';,|[' or s[i - 2:i] in SEP2):
            break
        i -= 1
    d = 0
    while j < len(s):
        c = s[j]
        if c == '(':
            d += 1
        elif c == ')':
            if d == 0:
                break
            d -= 1
        elif d == 0 and (c in ';,|]' or s[j:j + 2] in SEP2 or (c == '.' and (j + 1 == len(s) or s[j + 1] == ' '))):
            break
        j += 1
    return s[i:j]


def image_named(o):   # the numeral's clause names an image address: an image name, or a literal of the image
    t = clause(o)
    if IMGNAME.search(t):
        return True
    for m in TOK.finditer(t):
        k = m.group(1)
        v = int(k, 16) if k[:2].lower() == '0x' else int(k, 10)
        if IMG_LO <= v < IMG_TOP and (k[:2].lower() == '0x' or (v in IMG_POINTS and v & (v - 1))):
            return True
    return False


@rule('PAGE', 'the numeral is 4096 = 2^12, the page size (measured: every PT_LOAD of the pin, the twin and the cgif pin has '
              'p_align 0x1000), in a clause that names no image address: page arithmetic (`mod 4096`, `/ 4096`, `* 4096`, '
              '`4096 *`, `Z.div_mod x 4096`), a page bound or gap (`4096 <= ..`, `x + 4096`, `x - 4096`), a one-page map or '
              'extent (`(base, 4096)`, `mk e 4096 KRW`, `zone3 x 4096`): the same number in both builds')
def r_page(o):
    return '' if PAGE_OK and o.val == 4096 and not image_named(o) else None


STATE_L = (r'\bELit \(?-?|\bSLit \(?-?|\bCVal \d+ \(SLit |\buE_litv \w+ |'
           r'\bval_mem [\w.]+ (?:\([^()]*(?:\([^()]*\))?[^()]*\)|\w+) (?:\([^()]*(?:\([^()]*\))?[^()]*\)|\w+) \d+ ')
AB01_TEXT = '\n'.join(lines_of('A/AB01.v')[1])


@rule('STATE-VALUE', 'the numeral is a value the proof\'s symbolic state holds: `ELit N`, `SLit N`, `CVal w (SLit N)`, '
                     '`uE_litv E N`, or `val_mem .. A w N` at a run-time address A (a map length, a register value, a field '
                     'value of a run-time object), in a clause that names no image address; the evidence says whether '
                     'AB01.v (the collected states of fuzz_disco.asan) holds the same `ELit N`')
def r_state(o):
    if not endsw(o, STATE_L) or image_named(o):
        return None
    return f'AB01 holds ELit {o.val}: {("ELit %d)" % o.val) in AB01_TEXT or ("ELit %d;" % o.val) in AB01_TEXT}'


STRUCT_L = (r"(?<![\w.'])(?!TFIB_|IMG_|tfib_|sp\w*\b)[A-Za-z_][\w']*(?: [A-Za-z_][\w']*)?(?: \+ (?:t_\w+|k\w+|\d+))* \+ \(?|"
            r"\bmkRegion (?:None|\(Some [\w%]+\)) [^\[]*|\bmkChunk \(?(?:[\w']+ \+ )?|\(Some [\w%]+, (?:[^()]*, )?|"
            r"\(None, [^()]*|\(AF \(?|\(AF \d+, |\bat_ \w+ |\bZ_lt_le_dec o |\b\d+ <= d < |"
            r"\(t_\w+ \+ |\bt_\w+ \+ |\bSOff (?!2 )[A-Za-z_]\w*(?:%nat)? \(?-?|\bSOff \d+%nat \(?-?")


@rule('STRUCT-OFFSET', 'the numeral is an offset from a named run-time base or model name (`T + N` an AsanThread, '
                       '`T + t_cache + N`, `RGv + N` a region info, `SMv + N` a shadow map, `kHighMemBeg + N`, `mb + N`, '
                       '`SOff v N` / `SOff v (-N)` symbolic variable v plus N ..), a field offset or bound of a symbolic '
                       'region (`mkRegion r lo hi wlo whi`, `mkChunk N`, `(Some r, lo, hi)`), an offset `AF N` / `at_ base N` '
                       '/ `o < N` into a run-time object, in a clause that names no image address: a field of the sanitizer '
                       'runtime\'s structures, not a distance between image bounds')
def r_struct(o):
    return '' if endsw(o, STRUCT_L) and not image_named(o) else None


ALIGN_L = (r'\bmod \(?|\bAL |\bmod0_factor \w+ \d+ |\bzone3 \w+ |exists \(\(?[^()]*\* |exists \(|\* ')
regex_rule('ALIGN', 'the numeral is a power of two used as a modulus, alignment or factor: `x mod N`, `AL N x`, '
                    '`mod0_factor x k N`, `zone3 x N`, `k * N` / `N * k` in a divisibility witness `exists (..)` or a product '
                    '(8192 = 2^13 the allocator region alignment, 1024 / 2048 / 32768 powers of two of the shadow and '
                    'size-class arithmetic): not a quantity of the image', vals={1024, 2048, 8192, 32768},
           L=ALIGN_L)
regex_rule('ALIGN', None, vals={1024, 2048, 8192}, R=r' \* ')


BOUND_L = r'(?:^|[(\[:,]|/\\|\\/|->|&&|\|\||\bforall [^,]*,)\s*'


@rule('BOUND', 'the numeral alone is one side of a comparison with a run-time value in a hypothesis, a fact or a test '
               '(`N <= v`, `v <= N`, `v < N`, `n <=? N`), in a clause that names no image address: a bound of a run-time '
               'size, length or count of the model (a request size, a redzone, a string length), not a bound of the image')
def r_bound(o):
    if image_named(o):
        return None
    if (endsw(o, BOUND_L) and startsw(o, r'\s*<=?\??\s')) or \
            (endsw(o, r'<=?\??\s*') and startsw(o, r'\s*(?:$|[)\].;,]|/\\|\\/|->|&&|\|\|)')):
        return ''
    return None


@rule('RT-ARITH', 'the numeral is an operand of +, -, *, / or mod (`x + N`, `N - x`, `x / N`, `N * x`, `(..) + N`) in a '
                  'clause that names no image address: a constant of the '
                  'run-time arithmetic of the allocator / shadow model, not a quantity of the image')
def r_arith(o):
    if image_named(o):
        return None
    if endsw(o, r'(?:[-+*/]|\bmod) \(?-?') or startsw(o, r'\)*\s+(?:[-+*/]|mod)\s'):
        return ''
    return None

# ------------------------------------------------------------------------------------------------ the start-up files
GEN = collections.OrderedDict([   # file -> (header text that must be present, generator named from it)
    ('A/AB01.v', ("its 50 hand-off states generated from libreac/fuzz_disco's ASan build", 'the start-up collector (50 hand-off states of fuzz_disco.asan)')),
    ('A/AB03.v', ("its join state generated from libreac/fuzz_disco's ASan build", 'the start-up collector (join state of fuzz_disco.asan)')),
    ('A/AB05.v', ("its start-up plan (body pcs from the binary match, code range by the text rule, 46-pair tail) generated from libreac/fuzz_disco", 'the start-up planner (body pcs, code range, 46-pair tail of fuzz_disco.asan)')),
    ('A/AB12.v', ("TFIB_TEXT_N is fuzz_disco.asan's own .text size / 4", 'atable (the word table of fuzz_disco.asan; TFIB_TEXT_N set to its own .text size / 4)')),
    ('A/AD1k.v', ("the start-up data of this file is generated from fuzz_disco's own asan image", 'the start-up data generator (fuzz_disco.asan and its collected states)')),
    ('A/AD2i.v', ("the start-up data of this file is generated from fuzz_disco's own asan image", 'the start-up data generator (fuzz_disco.asan and its collected states)')),
    ('A/AD2j.v', ("the start-up data of this file is generated from fuzz_disco's own asan image", 'the start-up data generator (fuzz_disco.asan and its collected states)')),
    ('A/AF0m.v', ("its addresses moved to libreac/fuzz_disco's ASan build", 'the AF0m cell set (header: its addresses moved to fuzz_disco.asan; its cells re-checked by gates 4 and 5)')),
    ('A/ACej.v', ("the call contexts and allocation traces are libreac/fuzz_disco's, read from fuzz_disco.asan", 'the call-context reader (fuzz_disco.asan)')),
    ('A/AE3i.v', ("its addresses moved to libreac/fuzz_disco's ASan build", 'the regenerated chunk list (header: its addresses moved to fuzz_disco.asan)')),
])
GEN_OK = {}
for f, (needle, _) in GEN.items():
    hd = ' '.join(lines_of(f)[0][2:6])
    GEN_OK[f] = needle in hd
    print(f'start-up file {f}: header names its generator: {GEN_OK[f]}')

GEN_ROLE = [   # (role, regex on the text before the numeral, regex on the text after it or None)
    ('page-scaled variable 4096 * EVar k', r'M_MUL \(ELit \(?-?|\bescale ', None),
    ('symbolic variable index', r'\bEVar |\bKRange \(EVar |\bSOff |\(epg ', None),
    ('access offset a_off', r'\ba_off := -?', None),
    ('map length am_len', r'\bam_len := ELit ', None),
    ('entry length (ELit n) of a KZero / KDisj / KRange / KFill entry', r'\|\} \(ELit ', None),
    ('word value (ELit v) of a KWord / KWr entry', r'\|\} \d+ \(ELit ', None),
    ('length of a (base, length) pair', r', ELit ', r'\)'),
    ('constant added to a symbolic term', r'\)\)? \(ELit ', r'\)'),
    ('value of a KRange (ELit v) lo hi entry', r'\bKRange \(ELit ', None),
    ('bound of a KRange entry', r'\bKRange \([^()]*(?:\([^()]*\))*[^()]*\) (?:\d+ )?', None),
    ('slice start / count of seg', r'\bseg \w+ (?:\d+ )?', None),
    ('hand-off index of PHandoff', r'\bPHandoff ', None),
    ('thread-pointer offset ATp (-k) of a TFIB_CONST cell', r'\bATp \(-', None),
]


RT_CLASSES = {'STRUCT-OFFSET', 'MODEL-CONSTANT', 'ALIGN', 'BOUND', 'RT-ARITH', 'STATE-VALUE', 'RT-CELL'}   # need RT_SAME
OWN = {'A/AB01.v': "the collector's own symbolic-state field", 'A/AB03.v': "the collector's own symbolic-state field",
       'A/AB05.v': "the planner's own field"}


def gen_class(o):   # ('GEN', generator, role, re-check) for an occurrence in a start-up file, ('DEFECT', ev), or None
    gen, role, dn = GEN[o.f][1], None, enclosing_def(o.f, o.ln)
    m = endsw(o, r'\bz(\d) \(ANum (0x[0-9a-fA-F]+)\) ')
    cell = None
    if o.f == 'A/AF0m.v' and m:
        w, cell = int(m.group(1)), int(m.group(2), 16)
        pv = PIN.word(cell, w)
        role = f'const cell z{w} (ANum {cell:#x}) of {dn}'
        if pv is not None and pv != o.val:
            return ('DEFECT', f'{role}: pin bytes {pv:#x} != value')
        role += f', file-backed, pin bytes {pv:#x} = value' if pv is not None else ', past the file bytes'
    else:
        for r, lp, rp in GEN_ROLE:
            if endsw(o, lp) and (rp is None or startsw(o, rp)):
                role = r
                break
    if role is None:
        for cls, fn in CHECKS:
            ev = None if cls in RT_CLASSES and not RT_SAME else fn(o)
            if ev is not None:
                if isinstance(ev, tuple):
                    return ev
                role = cls.lower() + (f' ({ev})' if ev else '')
                break
    if role is None:
        return None
    if o.f == 'A/AF0m.v' and dn.startswith('Tfib_const'):
        cov = f'gate 4 ifchk re-checks this {dn} cell against each of AB01\'s 50 states'
        if cell is not None and PIN.filebytes(cell, 1) is not None:
            cov += ', gate 5 cellcheck against the pin'
    elif o.kind == 'hex' or o.val >= 0x10000:
        cov = 'gate 3 codeptr re-checks it against the pin'
    else:
        cov = 'no gate re-checks it (a decimal below 0x10000): ' + OWN.get(o.f, "the generator's own text")
    return ('GEN', gen, role, cov)


RULES['GENERATED'] = ('the file is a start-up file written from fuzz_disco.asan by a generator (AB01 AB03 AB05 AB12 AD1k AD2i '
                      'AD2j AF0m ACej AE3i; header lines 3-6 must carry the generator\'s statement, checked here), so its '
                      'pairing with cgif\'s file says nothing about a kept value. The role is read from the text (a '
                      'page-scaled variable 4096 * EVar k, a variable index, an access offset a_off, a map or entry length, '
                      'a cell value, ..; else the first non-start-up rule that answers). Re-checks: gate 3 codeptr checks '
                      'every hex literal and every decimal >= 0x10000 of the nine files against the pin (0 findings); gate 4 '
                      'ifchk checks AF0m\'s TFIB_CONST cells against each of AB01\'s 50 states; gate 5 cellcheck checks AF0m\'s '
                      'file-backed cells against the pin (measured here too: a file-backed AF0m cell whose pin bytes differ '
                      'is a DEFECT). A decimal below 0x10000 of a collected state no gate re-checks: it is the collector\'s '
                      'own symbolic-state field, and the evidence says so')
RULES['DEFECT'] = ('a measured rule whose measurement fails, or a hand row with verdict DEFECT: a numeral that is a cgif '
                   'quantity kept where fuzz_disco.asan\'s own differs')


def classify(o):
    if o.f in GEN:
        if not GEN_OK[o.f]:
            return None, ''
        ev = gen_class(o)
        if ev is None:
            return None, ''
        return ('GENERATED', ev[1:]) if ev[0] == 'GEN' else ('DEFECT', ev[1])
    for cls, fn in CHECKS:
        ev = None if cls in RT_CLASSES and not RT_SAME else fn(o)
        if ev is not None:
            return ('DEFECT', ev[1]) if isinstance(ev, tuple) else (cls, ev)
    return None, ''


# ------------------------------------------------------------------------------------------------ the hand table
HKEY = ('file', 'line', 'value', 'kind')
hand = list(csv.DictReader((l for l in open(a.hand) if not l.startswith('#')), delimiter='\t'))
ENV = dict(word=PIN.word, obj=lambda n: sorted(TWIN.objs.get(n, [])), cobj=lambda n: sorted(CTWIN.objs.get(n, [])),
           func=lambda x: sorted(TWIN.fstart.get(x, [])), named=NAMED, model=MODEL, ab1w=AB1W, af0m_cell=af0m_cell,
           defs=defs_of, line=lambda f, n: lines_of(f)[1][n - 1], has=lambda f, s: s in '\n'.join(lines_of(f)[1]),
           func_at=lambda a: sorted(n for x, sz, n in TWIN.funcs if x <= a < x + sz), PAGE_OK=PAGE_OK, IMG=(IMG_LO, IMG_TOP))
hidx, bad = {}, []
for h in hand:
    k = tuple(h[c] for c in HKEY)
    try:
        ok = eval(h['check'], {'__builtins__': {'len': len, 'all': all, 'any': any, 'hex': hex, 'int': int}}, ENV)
    except Exception as ex:   # noqa: BLE001 - a check that cannot be evaluated is a failed check
        ok, h['check'] = False, h['check'] + f' [{type(ex).__name__}: {ex}]'
    if not ok:
        bad.append(f'hand check failed: {k}: {h["check"]}')
    if k in hidx:
        bad.append(f'hand row twice: {k}')
    hidx[k] = h

# ------------------------------------------------------------------------------------------------ triage
groups = collections.defaultdict(list)
for r in rows:
    f, ln = r[col['dst']].rsplit(':', 1)
    groups[(f, int(ln), int(r[col['value']], 16), r[col['kind']])].append(r)

out, by_cls, by_status, used = {}, collections.Counter(), collections.Counter(), collections.Counter()
for (f, ln, val, kind), rs in sorted(groups.items()):
    occ = occurrences(f, ln, val, kind)
    hk = (f, str(ln), (hex(val) if kind == 'hex' else str(val)), kind)
    if len(occ) < len(rs):
        bad.append(f'{f}:{ln} {val} {kind}: {len(rs)} rows, {len(occ)} occurrences on the line')
        continue
    if hk in hidx:
        h = hidx[hk]
        used[hk] += 1
        cl = [(h['class'] if h['verdict'] == 'right' else 'DEFECT', 'hand: ' + h['reason'])] * len(occ)
    else:
        cl = [classify(o) for o in occ]
    if len(occ) > len(rs) and len({c for c, _ in cl}) > 1:
        bad.append(f'{f}:{ln} {val} {kind}: {len(rs)} rows over {len(occ)} occurrences of {len({c for c, _ in cl})} classes')
        continue
    # one row per occurrence when the counts agree; otherwise every row takes the one class all occurrences share
    rows_of = collections.defaultdict(list)
    if len(occ) == len(rs):
        for (c, _), r in zip(cl, rs):
            rows_of[c].append(r)
    else:
        rows_of[cl[0][0]] = rs
    for c, crs in rows_of.items():
        oc = [(o, ev) for o, (cc, ev) in zip(occ, cl) if cc == c]
        c = c or 'UNTRIAGED'
        verdict = 'DEFECT' if c == 'DEFECT' else ('-' if c == 'UNTRIAGED' else 'right')
        wins = []
        for o, _ in oc:
            if o.win() not in wins:
                wins.append(o.win())
        if c == 'GENERATED':
            roles = collections.Counter(e[1] for _, e in oc)
            evtxt = ('; '.join(sorted({e[0] for _, e in oc})) + '; role: ' +
                     ', '.join(f'{r} x{k}' for r, k in sorted(roles.items())) + '; ' + '; '.join(sorted({e[2] for _, e in oc})))
        else:
            evs = []
            for _, e in oc:
                if e and e not in evs:
                    evs.append(e)
            evtxt = ' / '.join(evs[:2]) + (f' (+{len(evs) - 2} more)' if len(evs) > 2 else '')
        n = len(crs)
        st = '+'.join(sorted({r[col['status']] for r in crs}))
        rc = ' | '.join(sorted({r[col['class']] for r in crs}))
        ev = ' / '.join(wins[:2]) + (f' (+{len(wins) - 2} more)' if len(wins) > 2 else '')
        if len(occ) != len(rs):
            ev += f' ({len(occ)} occurrences for {len(rs)} rows)'
        ev += f' :: {evtxt}' if evtxt else ''
        out[(f, ln, val, kind, c)] = [f, str(ln), oc[0][0].tok, kind, str(n), st, rc, c, verdict, ev.replace('\t', ' ')]
        by_cls[(c, verdict)] += n
        for r in crs:
            by_status[r[col['status']]] += 1
        if c == 'UNTRIAGED':
            bad.append(f'no class: {f}:{ln} {oc[0][0].tok} {kind} ({n} rows): {wins[0]}')
bad += [f'hand row matches no non-SAME group: {k}' for k in hidx if not used[k]]

with open(a.out, 'w') as fo:
    fo.write('\t'.join(['file', 'line', 'value', 'kind', 'n', 'status', 'rc_class', 'triage', 'verdict', 'evidence']) + '\n')
    for k in sorted(out):
        fo.write('\t'.join(out[k]) + '\n')

for c, t in RULES.items():
    print(f'rule {c}: {t}')
print('rows by status: ' + ', '.join(f'{k} {v}' for k, v in sorted(by_status.items())))
for (c, v), n in sorted(by_cls.items(), key=lambda x: (-x[1], x[0])):
    print(f'triage {c}\t{v}\t{n}')
tot = sum(by_cls.values())
ndef = sum(n for (c, v), n in by_cls.items() if v == 'DEFECT')
print(f'non-SAME rows {len(rows)}, classed {tot}, right {sum(n for (c, v), n in by_cls.items() if v == "right")}, '
      f'DEFECT {ndef}, untriaged {sum(n for (c, v), n in by_cls.items() if c == "UNTRIAGED") + len(rows) - tot}, '
      f'hand rows {len(hand)} (groups matched {sum(used.values())})')
for b in bad:
    print('rc_triage: refusal: ' + b)
if ndef:
    print(f'rc_triage: {ndef} DEFECT rows (see the out table)')
sys.exit(1 if bad or ndef else 0)
