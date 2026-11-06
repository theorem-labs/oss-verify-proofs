#!/usr/bin/env python3
"""count_recompute.py -- find every count in the relocated Reusable/Y*.v files and recompute it from the images.

Proves no function (kind: measurement).

A relocated proof file can keep a count of the donor image (cgif_file_fuzzer): a code-range word count, a table
length, a region count, a segment span, a size. A by-value address check cannot see such a count when its value is
also some right quantity of the target. This script finds the counts by fixed text patterns, gives each one a RULE
that derives it from an image, applies the rule to the fuzz_disco build the file is read against (pin + unstripped
twin: code bytes and headers from the pin, symbols from the twin) and, where the rule has a donor form, to the
paired cgif file and cgif build, and compares the result with the shipped value.

Usage:
  count_recompute.py --lib LIB --cgif-lib CGIF_LIB --pac PAC_TSV[.gz]
                     --pin K=PATH --twin K=PATH --cgif-pin K=PATH --cgif-twin K=PATH   (each for K in A, B, P, U)
                     --out COUNTS.tsv [--accept KEY=CLASS:REASON ...] [--jobs N]
  LIB        the fuzz_disco lib tree (the directory that holds Reusable/); the checked files are LIB/Reusable/Y*.v
  CGIF_LIB   the donor lib tree; LIB/Reusable/Yxxx.v pairs with CGIF_LIB/Yxxx.v when that file exists
  PAC_TSV    a port_addr_check full table of the same file set: column 3 is the image key of the row (`K`, or
             `S->T` when the donor build S and the target build T differ), column 6 the target file. A file is read
             against every target key its rows name. A file with no key there: the key its own
             `fuzz_disco.images Require Import <Asan|AsanUbsan|Plain|Ubsan>` line names; else the keys of the file
             with the same stem (the name without a `_cf` / `_cfw` suffix or a last capital letter); else none.
  K          build keys: A = asan, B = asan-ubsan, P = plain, U = ubsan. The script checks that each twin has the
             pin's PT_LOAD table and the same bytes in PT_LOAD 2..n; exit 1 if not.
  --accept   KEY=CLASS:REASON (repeatable): KEY is a key column value (FILE:LINE, FILE:LINE:TOKEN) or FILE:LINE
             for every row of that line; the DIFFERS rows it names keep verdict DIFFERS and carry `CLASS: REASON`
             in the accept column (a ruling). With CLASS `MEASURED TRUE` it names MEASURED TRUE rows instead and
             records the unit owner's ruling text there. An --accept that names no such row is an error.

Output: one row per count, sorted by file, line and key. Columns: key, form, name/call, shipped, rule, recomputed,
measurement, images, donor shipped, donor recomputed, verdict, status, note, accept. No timestamp, no path: a re-run
on the same inputs gives the same bytes. Verdicts:
  MEASURED TRUE  the rule recomputes the shipped value from the image (on every build the file is read against)
  DIFFERS        the rule gives another value (or the check of a NOT-A-COUNT row fails)
  NOT-A-COUNT    the matched numeral is not an image count; the rule column says what it is and the check run
  UNMEASURED     a pattern matched and no rule applies (exit 1)
status repeats the verdict in the words of the lib/A count table: EQUAL (MEASURED TRUE), TRUE (MEASURED TRUE by the
exact-function-cover rule), NOT-IMAGE (NOT-A-COUNT), DIFFERS, UNRULED (UNMEASURED).
Exit 0 only when every row is MEASURED TRUE or NOT-A-COUNT, or a DIFFERS row that an --accept names; else 1.
The summary on stdout gives the hits of each pattern, the counts by form and verdict, and every DIFFERS row.

Patterns (each match is one row; a line can hold several):
  code     `build_table SEGS 0xPC N%nat`; `(PC, N%nat)` with PC a hex literal or a name with a numeral
           Definition in the file or one value in the tree; `Definition COUNT : nat := N.` where a
           `build_table SEGS START COUNT` of the tree names COUNT and START resolves to a numeral
  def      `Definition NAME [: nat|Z|N] := V.` (V a numeral or + - * ^ of numerals) with NAME ending in _len, _cnt,
           _count, _size, _sz, _bytes, _pad, _padding, _entries, _entry, _tab, _table, _words, _nwords, _nelem,
           _rows, _cols, _slots, _classes, _n, _num, nslots (any case), or TEXT_N, or tfib_n<x> / src0_n<x>
  field    `FIELD := NUMERAL` inside `{| .. |}` with FIELD ending in len, num, ent, res, count or size (opt. _z)
  seg      `seg LIST I N` in a file that defines seg (the start-up hand-off lists)
  slice    `firstn N ARG` / `skipn N ARG`, N a numeral
  length   `length EXPR OP N` and `Z.of_nat (length EXPR) OP N` (OP = =, =?, <=, <=?, <, <?, >=, >; not N ^ ..)
  extent   `mkRegion None LO (LO + N)`; `mkChunk ADDR (CImg N)` (form cimg); `(0xADDR, N, [cells])` (form rotab)
  segspan  segment geometry in a file that names `<Image>_seg_bytes_<i>` or a `segments_reserved` list:
           `scanN / zscanN <Image>_seg_bytes_<i> W OFF N`, `PrimString.length <Image>_seg_bytes_<i>) / 2) = N%N`,
           `segment_byte_at_some1 _ N`, `scanN_sound _ W 0 N`, `(B <=? x) && (x + 1 <=? B + N)`,
           `Z.to_N (x - B) <? N`, `(OFF + Z.to_N (x - BSS))%N`, `(Z_to_bv 64 B, Z_to_bv 64 N)` pairs of
           `segments_reserved .. = [..]`, `sum_sizes (segments_reserved ..) = N`
Comments are blanked before matching (line numbers kept). Donor pairing: a count pairs with the count of the same
form and context (the matched text with its numerals blanked) that has the same order in the donor file.

Rules (the rule column states the one applied with its values; `measurement` gives symbol, start, end, size):
  Code ranges, read on the twin's STT_FUNC symbols (per start the largest st_size):
    text         PC = .text start: N = .text size / 4; TEXT_N definitions with TEXT_LO = .text start the same.
    text-tail    tfibmusl_text_count: N = (.text end - PC) / 4.
    donor structure  the paired donor range read on the cgif twin as "function S + s to function E + e" must start
                 at a function named S here at + s: N = (start of E here + e - PC) / 4, e = E's st_size here when
                 the donor range ends at E's end. A shipped N that is the exact cover of whole functions from PC
                 ending where E starts, where the donor range was its own exact cover plus k words of E: MEASURED
                 TRUE (note: the donor's +k words not taken). Any other N: DIFFERS (the note says over- or
                 under-cover and by how many words).
    no donor range  whole functions: PC is a function start and PC + 4N is the end of the function that holds
                 the last word; else prefix through the first exit (the first ret / j / jr, jal / jalr rd = x0, of
                 the function at PC); else the same (PC, N) is a donor-structure row elsewhere in the tree.
                 Else DIFFERS with the whole-functions value.
  Segment geometry (PT_LOAD i of the pin; span = page_up(p_vaddr + p_memsz) - page_down(p_vaddr), the bytes of
    `<Image>_seg_bytes_<i>`): every N above is span(i) of the segment named (by seg_bytes index, by the
    tfib_hex<i> / tfib_len<i> lemma the line uses, or by the page base B); the zero scan OFF = filesz end - base,
    its N = span - OFF; a sum_sizes = the sum of the spans; n_res = the number of PT_LOAD (= length of
    segments_reserved, res_len_ok); rw_len = span of the last PT_LOAD; ph_ent_z / ph_num_z = ELF e_phentsize /
    e_phnum.
  Definitions by name: tfib_A_X / tfib_E_X / tfib_D_X (src0_ alike) are addresses: start / end of twin FUNC X /
    start of twin OBJECT X, with gen_symtab's naming (non-identifier characters as _, a _<k> / _libc suffix, the
    last identifier of a mangled name, musl's __malloc_ aliases); src0_D_str_<words>: the pin's C string at the
    address spells <words>. *_ENTRY: an entry PC inside a twin function; tfib_entry / tfib_at_a_entry = ELF e_entry.
    AF_<p>_X = twin FUNC X - twin FUNC B, B the function whose AF_<p>_ is 0 in the file. RA_X: the word before it
    is a `jal ra` to a twin function. tfib_n<x> = the number of `| k%nat =>` arms (0..n-1) of the next tfib_<y> (k
    : nat) match. src0_debruijn_len = the de Bruijn table extent: the pin's bytes from src0_D_debruijn32 to the next
    object are a permutation of 0..31. CTX_SIZE = twin OBJECT __malloc_context st_size. FILE_SZ = twin OBJECT
    __stdout_FILE st_size.
    NOT-A-COUNT with a check: FS_N = 2^(14 - CID) (ASan FakeStack frames per class), SH_N = FS_B / 8, FILL_N =
    SH_N / 8; BST_SIZE, META_SIZE, MAX_DICT_LEN, d_tab_words, MG_SLOTS (runtime / program / model constants: equal
    to the donor's); CGIF_SIZE / FRAME_SIZE / RAW_SIZE = end of the last field of the file's LAY_ table rounded up
    to its widest field; AMETA_SIZE = page_up(AMETA_BUCKETS * AMETA_BUCKET); STACK_LEN = 2^47; atom indices (used as
    SOff NAME); CTX_ / o_ field offsets (below CTX_SIZE / a struct offset); tfib_at_sniff_tab = 0 with no twin
    symbol *sniff*; SEC_LIVE_N, rg_len (model constants); seg_size of a synthetic test segment = its seg_bytes hex
    length / 2.
  Slices and lengths:
    image regions  in a file that names IMG_REGIONS / IMG_B / IMG_E / IMG_L / IMG_LC / IMG_X / IMG_XL and pairs
                 with a donor file, a count over a region list with donor count Kc; R / Rc = the regions of
                 IMG_REGIONS in each tree's YD2j.v: Kc >= Rc reaches past the image block: K = Kc + R - Rc; Kc <=
                 4: K = Kc (regions in front of the block or its first regions, same names); else K = the index
                 here of the region named at index Kc in cgif's IMG_REGIONS.
    strings      length of a message = strlen at its img_msg_chk address in the pin (also through `set (m := if b
                 then X else Y)`); length of (strB "..") or of a Definition := strB ".." [++ nlB] = the literal's
                 length (+ 1), with the check that its bytes occur in the pin; a printf message whose literal is
                 not in the pin: the pin's format with %u / %d for the literal's number (format length - conversion
                 + digits).
    trace depth  a trace bound 30 (29 = 30 - 1) = YF0m.v's const cell at tfib_D_malloc_context_size.
    states       length HS_tfib_list = the number of `Definition HS_tfib_<k> : acs` in the file.
    seg slices   YB01.v's hand-off state lists are written as slices of HS_tfib_0_kn plus changed entries: an
                 encoding of list entries, NOT-A-COUNT; check: I + N <= the base list's length (computed from the
                 file) and the slices of each list ascend without overlap.
    NOT-A-COUNT  the classes of NOTCOUNT below, each with its reason (word / field byte widths, register file,
                 mallocng arrays, page / path bounds, state region lists of files that name no image region list,
                 model bounds, proof-local lists); a class with a check names it.
  Extents: `mkRegion None LO (LO + N)`: N = strlen at LO + 1 in the pin; or = twin OBJECT __stdout_FILE - LO; or
    = the extent of the region's CVal cells, each cell equal to the pin's bytes. `mkChunk ADDR (CImg N)` in YD28.v
    = __stdout_FILE - ADDR; in a generated file (its header names the pin's sha256) N = the collector's image run
    (YB01.v `KImg LO HI` holding ADDR) clipped to the next chunk start or the region hi, the region inside the pin's
    loaded segment spans. A read-only cell table's N = the end of its last cell.
"""
import argparse, bisect, collections, gzip, hashlib, io, os, re, sys
from concurrent.futures import ThreadPoolExecutor

from elftools.elf.elffile import ELFFile

KEYS = 'ABPU'
IMG_MODULE = {'Asan': 'A', 'AsanUbsan': 'B', 'Plain': 'P', 'Ubsan': 'U'}
NUM = r'(?:0x[0-9a-fA-F]+|\d+)'


def kv_list(vals, what):
    out = {}
    for v in vals:
        k, sep, p = v.partition('=')
        if not sep or k not in KEYS:
            sys.exit(f'count_recompute: {what} wants K=PATH with K in {KEYS}: {v}')
        out[k] = p
    for k in KEYS:
        if k not in out:
            sys.exit(f'count_recompute: {what} {k}=PATH missing')
    return out


ap = argparse.ArgumentParser()
for k in ('lib', 'cgif-lib', 'pac', 'out'):
    ap.add_argument('--' + k, required=True)
for k in ('pin', 'twin', 'cgif-pin', 'cgif-twin'):
    ap.add_argument('--' + k, action='append', default=[])
ap.add_argument('--accept', action='append', default=[])
ap.add_argument('--jobs', type=int, default=16)
a = ap.parse_args()
PIN, TWIN = kv_list(a.pin, '--pin'), kv_list(a.twin, '--twin')
CPIN, CTWIN = kv_list(a.cgif_pin, '--cgif-pin'), kv_list(a.cgif_twin, '--cgif-twin')


def read_many(paths, binary=False):  # parallel reads (a remote file system is latency-bound); input order kept
    def rd(p):
        with open(p, 'rb' if binary else 'r') as fh:
            return fh.read()
    with ThreadPoolExecutor(max(1, a.jobs)) as ex:
        return list(ex.map(rd, paths))


# ------------------------------------------------------------------------------------------------ images
def page_down(x):
    return x & ~0xfff


def page_up(x):
    return (x + 0xfff) & ~0xfff


class Image:
    def __init__(self, label, raw, twin_raw):
        self.label, self.raw = label, raw
        self.pin_sha = hashlib.sha256(raw).hexdigest()
        self.twin_sha = hashlib.sha256(twin_raw).hexdigest()
        pe = ELFFile(io.BytesIO(raw))
        self.loads = [(s['p_vaddr'], s['p_offset'], s['p_filesz'], s['p_memsz']) for s in pe.iter_segments()
                      if s['p_type'] == 'PT_LOAD']
        self.phnum, self.phentsize = pe.header['e_phnum'], pe.header['e_phentsize']
        self.sec = {s.name: (s['sh_addr'], s['sh_size']) for s in pe.iter_sections() if s.name and s['sh_addr']}
        # span i: the bytes of the image module's loaded segment i (page-aligned, memsz)
        self.spans = [(page_down(v), page_up(v + mz) - page_down(v), v + fz) for v, o, fz, mz in self.loads]
        self.entry = pe.header['e_entry']
        te = ELFFile(io.BytesIO(twin_raw))
        tl = [(s['p_vaddr'], s['p_offset'], s['p_filesz'], s['p_memsz']) for s in te.iter_segments()
              if s['p_type'] == 'PT_LOAD']
        self.twin_same = (len(tl) == len(self.loads) and all(
            x[0] == y[0] and x[2] == y[2] and x[3] == y[3] for x, y in zip(tl, self.loads)) and all(
            twin_raw[y[1]:y[1] + y[2]] == raw[x[1]:x[1] + x[2]] for x, y in zip(self.loads[1:], tl[1:])))
        self.syms = []
        for s in te.get_section_by_name('.symtab').iter_symbols():
            if s.name and not s.name.startswith('$'):
                self.syms.append((s.name, s['st_value'], s['st_size'], s['st_info']['type']))
        by = {}
        for n, v, sz, t in self.syms:
            if t == 'STT_FUNC':
                e = by.setdefault(v, [0, set()])
                e[0] = max(e[0], sz)
                e[1].add(n)
        self.F = sorted((v, sz, min(ns), frozenset(ns)) for v, (sz, ns) in by.items())
        self.Fst = [f[0] for f in self.F]
        self.byname = collections.defaultdict(list)
        for v, sz, n, ns in self.F:
            for x in ns:
                self.byname[x].append(v)
        self.fsize = {v: sz for v, sz, _, _ in self.F}
        self.fname = {v: n for v, _, n, _ in self.F}
        self.obj = collections.defaultdict(set)
        for n, v, sz, t in self.syms:
            self.obj[n].add((v, sz, t))
        self.ostarts = sorted({v for n, v, sz, t in self.syms if t == 'STT_OBJECT' and v})

    def text(self):
        return self.sec['.text']

    def func_at(self, x):  # the function whose start is the last start <= x
        i = bisect.bisect_right(self.Fst, x) - 1
        return self.F[i] if i >= 0 else None

    def pick(self, name, near):  # the start of the function NAME nearest to `near`
        vs = self.byname.get(name)
        return min(vs, key=lambda v: (abs(v - near), v)) if vs else None

    def raw_at(self, x, n):  # the pin's file bytes [x, x + n), or None
        for v, o, fz, mz in self.loads:
            if v <= x and x + n <= v + fz:
                return self.raw[o + x - v:o + x - v + n]
        return None

    def word(self, x):
        b = self.raw_at(x, 4)
        return int.from_bytes(b, 'little') if b is not None else None

    def cstr(self, x):
        for v, o, fz, mz in self.loads:
            if v <= x < v + fz:
                b = self.raw[o + x - v:o + fz]
                return b[:b.index(b'\0')] if b'\0' in b else None
        return None

    def in_file(self, lo, hi):  # [lo, hi) inside one PT_LOAD's file-backed bytes: its index, else None
        for i, (v, o, fz, mz) in enumerate(self.loads):
            if v <= lo and hi <= v + fz:
                return i
        return None

    def sym1(self, name, types=('STT_FUNC', 'STT_OBJECT')):
        s = {(v, sz) for v, sz, t in self.obj.get(name, ()) if t in types}
        return s.pop() if len(s) == 1 else None

    def span_by_base(self, b):
        for i, (base, n, fe) in enumerate(self.spans):
            if base == b:
                return i
        return None

    def in_spans(self, lo, hi):  # [lo, hi) inside the union of the loaded segment spans
        cur = None
        for b, n, fe in sorted(self.spans):
            if cur and b <= cur[1]:
                cur[1] = max(cur[1], b + n)
            else:
                if cur and cur[0] <= lo and hi <= cur[1]:
                    return True
                cur = [b, b + n]
        return bool(cur) and cur[0] <= lo and hi <= cur[1]


_bins = read_many([PIN[k] for k in KEYS] + [TWIN[k] for k in KEYS] + [CPIN[k] for k in KEYS] +
                  [CTWIN[k] for k in KEYS], binary=True)
LABEL = {'A': 'asan', 'B': 'asan-ubsan', 'P': 'plain', 'U': 'ubsan'}
DI = {k: Image('fuzz_disco.' + LABEL[k], _bins[i], _bins[4 + i]) for i, k in enumerate(KEYS)}
CI = {k: Image('cgif_file_fuzzer.' + LABEL[k], _bins[8 + i], _bins[12 + i]) for i, k in enumerate(KEYS)}
del _bins
bad_twin = False
for k in KEYS:
    for X in (DI[k], CI[k]):
        tx = X.text()
        print(f'{k} {X.label}: pin sha256 {X.pin_sha}; twin sha256 {X.twin_sha}; twin PT_LOAD table equal to the '
              f'pin\'s and PT_LOAD 2..{len(X.loads)} bytes equal: {X.twin_same}; .text [{tx[0]:#x}, {tx[0] + tx[1]:#x}); '
              f'spans ' + ' '.join(f'[{b:#x}+{n:#x}]' for b, n, fe in X.spans) + f'; functions {len(X.F)}')
        bad_twin |= not X.twin_same
if bad_twin:
    print('count_recompute: a twin does not match its pin; its symbols cannot describe the pin')
    sys.exit(1)


# ------------------------------------------------------------------------------------------------ trees
def blank_comments(t):  # (* .. *) nest; strings ".." ("" escapes) are kept; blanked text keeps its newlines
    out, i, n, d = list(t), 0, len(t), 0
    instr = False
    while i < n:
        c = t[i]
        if d == 0 and c == '"':
            instr = not instr
            i += 1
            continue
        if instr:
            i += 1
            continue
        if t.startswith('(*', i):
            d += 1
            out[i] = out[i + 1] = ' '
            i += 2
            continue
        if d and t.startswith('*)', i):
            d -= 1
            out[i] = out[i + 1] = ' '
            i += 2
            continue
        if d and c != '\n':
            out[i] = ' '
        i += 1
    return ''.join(out)


def list_v(root, sub):
    d = os.path.join(root, sub) if sub else root
    return sorted(x for x in os.listdir(d) if x.startswith('Y') and x.endswith('.v'))


_tn = list_v(a.lib, 'Reusable')
_cn = list_v(a.cgif_lib, '')
_txt = read_many([os.path.join(a.lib, 'Reusable', x) for x in _tn] + [os.path.join(a.cgif_lib, x) for x in _cn])
RAW = {'Reusable/' + x: _txt[i] for i, x in enumerate(_tn)}
T = {f: blank_comments(t) for f, t in RAW.items()}
CT = {'Reusable/' + x: blank_comments(_txt[len(_tn) + i]) for i, x in enumerate(_cn)}
del _txt
print(f'files: LIB/Reusable/Y*.v {len(T)}, CGIF_LIB/Y*.v {len(CT)}, paired by name {sum(1 for f in T if f in CT)}')


# ------------------------------------------------------------------------------------------------ images per file
def read_pac(path):
    opener = gzip.open if path.endswith('.gz') else open
    tk, dk = collections.defaultdict(set), collections.defaultdict(set)
    with opener(path, 'rt') as fh:
        for line in fh:
            if line.startswith('#') or line.startswith('verdict\t'):
                continue
            p = line.rstrip('\n').split('\t')
            if len(p) < 6 or not p[5].startswith('Reusable/Y'):
                continue
            img = p[2]
            if img:
                s, _, t = img.partition('->')
                tk[p[5]].add(t or s)
                dk[p[5]].add(s)
            else:
                tk[p[5]]
    return tk, dk


PAC_T, PAC_D = read_pac(a.pac)


def stem(f):
    b = f[len('Reusable/'):-2]
    for s in ('_cfw', '_cf'):
        if b.endswith(s):
            return 'Reusable/' + b[:-len(s)] + '.v'
    if len(b) > 4 and b[-1].isupper():
        return 'Reusable/' + b[:-1] + '.v'
    return None


def own_req(f):
    m = re.findall(r'fuzz_disco\.images Require Import (\w+)', T[f])
    return sorted({IMG_MODULE[x] for x in m if x in IMG_MODULE})


IMGS = {}
for f in T:
    ks = sorted(k for k in PAC_T.get(f, ()) if k in KEYS)
    src = 'pac'
    if not ks:
        ks, src = own_req(f), 'own images Require'
    if not ks and stem(f) in T:
        s = stem(f)
        ks = sorted(k for k in PAC_T.get(s, ()) if k in KEYS) or own_req(s)
        src = 'stem ' + s[len('Reusable/'):]
    if not ks:
        src = '-'
    dks = sorted(k for k in PAC_D.get(f, ()) if k in KEYS)
    IMGS[f] = (ks, src, {k: (dks[0] if len(dks) == 1 else k) for k in ks})


# ------------------------------------------------------------------------------------------------ the patterns
def lineno(t, pos):
    return t.count('\n', 0, pos) + 1


def norm(s):
    return re.sub(r'0x[0-9a-fA-F]+|\b\d+\b', '#', s)


def term_at(t, pos):  # one Coq argument starting at pos: a parenthesised term or one token
    n, i = len(t), pos
    while i < n and t[i] in ' \t\n':
        i += 1
    if i < n and t[i] == '(':
        d = 0
        for j in range(i, n):
            d += t[j] == '('
            d -= t[j] == ')'
            if d == 0:
                return t[i:j + 1]
        return t[i:]
    m = re.match(r'[^\s()\[\];,]+', t[i:])
    return m.group(0) if m else ''


def zeval(e):  # a numeral or + - * ^ ( ) of numerals; None otherwise
    e = e.strip()
    if not e or re.sub(NUM, '', e).strip(' \t\n+-*^()') or re.search(r'[A-Za-z_]\w*\s*$', re.sub(NUM, '', e)):
        return None
    try:
        v = eval(re.sub(r'\^', '**', e), {'__builtins__': {}}, {})
    except Exception:
        return None
    return v if isinstance(v, int) else None


def defs_of(text):  # numeral Definitions of a file
    return {m.group(1): int(m.group(2), 0) for m in
            re.finditer(r'Definition\s+(\w+)\s*:\s*(?:Z|nat|N)\s*:=\s*(' + NUM + r')(?:%nat|%Z|%N)?\s*\.', text)}


def global_defs(tree):
    g = collections.defaultdict(set)
    for t in tree.values():
        for n, v in defs_of(t).items():
            g[n].add(v)
    return {n: v.pop() for n, v in g.items() if len(v) == 1}


def resolve(tree_defs, file_defs, name):
    if re.fullmatch(NUM, name):
        return int(name, 0)
    if name in file_defs:
        return file_defs[name]
    return tree_defs.get(name.split('.')[-1])


COUNT_NAME = re.compile(r'(?i)(?:^|_)(?:len|cnt|count|size|sz|bytes|pad|padding|entries|entry|tab|table|words|'
                        r'nwords|nelem|rows|cols|slots|classes|n|num|nslots)$|TEXT_N$|^(?:tfib|src0)_n[a-z]+$')
FIELD_NAME = re.compile(r'(?:^|_)(?:len|num|ent|res|count|size)(?:_z)?$')


def bt_names(tree):  # COUNT name -> START name of every `build_table SEGS START COUNT` with two names
    out = {}
    for t in tree.values():
        for m in re.finditer(r'build_table\s+\w+\s+([A-Za-z_][\w.]*)\s+([A-Za-z_][\w.]*)\s', t):
            out.setdefault(m.group(2).split('.')[-1], m.group(1).split('.')[-1])
    return out


SEGB = re.compile(r'\b(\w+)_seg_bytes_(\d+)\b')
HITS = collections.Counter()


def extract(f, t, gd, btn):
    out, fd = [], defs_of(t)

    def add(**kw):
        out.append(kw)
        HITS[kw['pat']] += 1

    for m in re.finditer(r'build_table\s+(\w+)\s+(0x[0-9a-fA-F]+)\s+(\d+)%nat', t):
        add(pat='build_table SEGS 0xPC N%nat', kind='code', line=lineno(t, m.start(3)), pc=int(m.group(2), 16),
            val=int(m.group(3)), name=f'build_table {m.group(1)} {m.group(2)} {m.group(3)}%nat', ctx='build_table',
            tok=m.group(2))
    for m in re.finditer(r'\((0x[0-9a-fA-F]+|[A-Za-z_][\w.]*)\s*,\s*(\d+)%nat\)', t):
        add(pat='(PC, N%nat)', kind='code', line=lineno(t, m.start(2)), pc=resolve(gd, fd, m.group(1)),
            pcname=m.group(1), val=int(m.group(2)), name=f'({m.group(1)}, {m.group(2)}%nat)', ctx='tuple',
            tok=m.group(1))
    seen = set()
    for m in re.finditer(r'Definition\s+(\w+)\s*:\s*nat\s*:=\s*(\d+)(?:%nat)?\s*\.', t):
        cn = m.group(1)
        if cn in btn and resolve(gd, fd, btn[cn]) is not None:
            seen.add(cn)
            add(pat='Definition COUNT : nat := N (build_table _ START COUNT)', kind='code', line=lineno(t, m.start(2)),
                cname=cn, pc=resolve(gd, fd, btn[cn]), val=int(m.group(2)),
                name=f'{cn} (build_table _ {btn[cn]} {cn})', ctx='codeN ' + cn, tok=cn)
    for m in re.finditer(r'Definition\s+(\w+)\s*(?::\s*(?:nat|Z|N)\s*)?:=\s*([^.]*?)(?:%nat|%Z|%N)?\s*\.(?=\s)', t):
        nm, v = m.group(1), zeval(m.group(2))
        if v is not None and COUNT_NAME.search(nm) and nm not in seen:
            add(pat='Definition NAME := V (count name)', kind='def', line=lineno(t, m.start(2)), val=v, name=nm,
                ctx='def ' + nm, tok=nm)
    for m in re.finditer(r'\{\|(.*?)\|\}', t, re.S):
        for g in re.finditer(r'(\w+)\s*:=\s*(' + NUM + r')\b(?!\s*[+\-*/^])', m.group(1)):
            if FIELD_NAME.search(g.group(1)):
                add(pat='{| FIELD := N |} (count field)', kind='field', line=lineno(t, m.start(1) + g.start(2)),
                    val=int(g.group(2), 0), name=g.group(1), rec=m.group(1), ctx='field ' + g.group(1),
                    tok=g.group(1))
    if re.search(r'Definition seg\b', t):
        for m in re.finditer(r'\bseg\s+(\w+)\s+(\d+)\s+(\d+)', t):
            add(pat='seg LIST I N', kind='seg', line=lineno(t, m.start()), val=int(m.group(3)), i=int(m.group(2)),
                lst=m.group(1), name=f'seg {m.group(1)} {m.group(2)} {m.group(3)}', ctx='seg', pos=m.start(),
                tok=f'seg{m.group(2)}')
    for m in re.finditer(r'\b(firstn|skipn)\s+(\(?)(\d+)(%nat)?(\)?)', t):
        if m.group(2) and not m.group(5):
            continue
        arg = term_at(t, m.end())
        add(pat='firstn / skipn N ARG', kind='slice', line=lineno(t, m.start(3)), val=int(m.group(3)), fn=m.group(1),
            arg=arg, name=f'{m.group(1)} {m.group(3)} {arg}', ctx=f'{m.group(1)} {norm(arg)}',
            tok=f'{m.group(1)}{m.group(3)}')
    for m in re.finditer(r'(Z\.of_nat\s*\(\s*)?length\s+(\((?:[^()]|\([^()]*\))*\)|[\w.\']+)\s*(\)\s*)?'
                         r'(=\??|<=\??|<\??|>=|>)\s*(\d+)(%nat)?(?!\s*\^)(?!\w)(?!\.\d)', t):
        if bool(m.group(1)) != bool(m.group(3)):
            continue
        z = 'Z.of_nat (length ' if m.group(1) else 'length '
        add(pat='length EXPR OP N / Z.of_nat (length EXPR) OP N', kind='length', line=lineno(t, m.start(5)),
            val=int(m.group(5)), arg=m.group(2), op=m.group(4),
            name=f'{z}{m.group(2)}{")" if m.group(1) else ""} {m.group(4)} {m.group(5)}',
            ctx=f'length {norm(m.group(2))} {m.group(4)}', tok='len:' + m.group(2))
    for m in re.finditer(r'mkRegion\s+None\s+(' + NUM + r')\s+\(\s*\1\s*\+\s*(\d+)\s*\)', t):
        i = t.find('[', m.end())
        j = t.find(']', i) if i >= 0 else -1
        add(pat='mkRegion None LO (LO + N)', kind='extent', line=lineno(t, m.start(2)), val=int(m.group(2)),
            lo=int(m.group(1), 0), chunks=t[i:j + 1] if 0 <= i < m.end() + 200 and j > i else '',
            name=f'mkRegion None {m.group(1)} ({m.group(1)} + {m.group(2)})', ctx='extent', tok='ext' + m.group(1))
    for m in re.finditer(r'mkChunk\s+(' + NUM + r')\s+\(CImg\s+(\d+)\)', t):
        add(pat='mkChunk ADDR (CImg N)', kind='cimg', line=lineno(t, m.start(2)), val=int(m.group(2)),
            lo=int(m.group(1), 0), name=f'mkChunk {m.group(1)} (CImg {m.group(2)})', ctx='cimg',
            tok='cimg' + m.group(1))
    for m in re.finditer(r'\((0x[0-9a-fA-F]+),\s*(\d+),\s*\[', t):
        j = t.index(']', m.end())
        cells = [(int(o), int(w)) for o, w in re.findall(r'\((\d+),\s*(\d+)%N,', t[m.end():j])]
        add(pat='(0xADDR, N, [cells])', kind='rotab', line=lineno(t, m.start(2)), val=int(m.group(2)),
            lo=int(m.group(1), 16), cells=cells, name=f'({m.group(1)}, {m.group(2)}, [..])', ctx='rotab',
            tok=m.group(1))
    if SEGB.search(t) or re.search(r'segments_reserved\s+\w+\s*=\s*\[', t):
        extract_segspan(t, add)
    for i, c in enumerate(out):
        c['ord'] = i
    return out


def extract_segspan(t, add):
    P = 'segspan: '
    for m in re.finditer(r'\b(scanN|zscanN)\s+\w+_seg_bytes_(\d+)\s+\d+\s+(\d+)\s+(\d+)', t):
        i, off, n = int(m.group(2)), int(m.group(3)), int(m.group(4))
        if m.group(1) == 'zscanN':
            add(pat=P + 'zscanN seg_bytes_i W OFF N', kind='segspan', line=lineno(t, m.start(3)), val=off,
                seg=i, what='zoff', name=f'zscanN seg_bytes_{m.group(2)} _ {off} _ (OFF)', ctx='zoff',
                tok=f'zoff{m.group(2)}')
            add(pat=P + 'zscanN seg_bytes_i W OFF N', kind='segspan', line=lineno(t, m.start(4)), val=n, seg=i,
                what='zlen', off=off, name=f'zscanN seg_bytes_{m.group(2)} _ {off} {n} (N)', ctx='zlen',
                tok=f'zlen{m.group(2)}')
        elif off == 0:
            add(pat=P + 'scanN seg_bytes_i W 0 N', kind='segspan', line=lineno(t, m.start(4)), val=n, seg=i,
                what='span', name=f'scanN seg_bytes_{m.group(2)} _ 0 {n}', ctx='scan', tok=f'scan{m.group(2)}')
    for m in re.finditer(r'PrimString\.length\s+\w+_seg_bytes_(\d+)\s*\)\s*/\s*2\s*\)\s*=\s*(\d+)%N', t):
        add(pat=P + 'PrimString.length seg_bytes_i / 2 = N%N', kind='segspan', line=lineno(t, m.start(2)),
            val=int(m.group(2)), seg=int(m.group(1)), what='span', name=f'length seg_bytes_{m.group(1)} / 2 = '
            f'{m.group(2)}%N', ctx='plen', tok=f'plen{m.group(1)}')
    for m in re.finditer(r'segment_byte_at_some1\s+_\s+(\d+)\)[^\n]*?tfib_(?:hex|len)(\d+)', t):
        add(pat=P + 'segment_byte_at_some1 _ N', kind='segspan', line=lineno(t, m.start(1)), val=int(m.group(1)),
            seg=int(m.group(2)), what='span', name=f'segment_byte_at_some1 _ {m.group(1)} (tfib_hex{m.group(2)})',
            ctx='sbas', tok=f'sbas{m.group(2)}')
    for m in re.finditer(r'scanN_sound\s+_\s+\d+\s+0\s+(\d+)\s+tfib_hex(\d+)', t):
        add(pat=P + 'scanN_sound _ W 0 N tfib_hex<i>', kind='segspan', line=lineno(t, m.start(1)),
            val=int(m.group(1)), seg=int(m.group(2)), what='span', name=f'scanN_sound _ _ 0 {m.group(1)} '
            f'tfib_hex{m.group(2)}', ctx='sound', tok=f'sound{m.group(2)}')
    for m in re.finditer(r'\((\d+)\s*<=\?\s*x\)\s*&&\s*\(x\s*\+\s*1\s*<=\?\s*(\d+)\s*\+\s*(\d+)\)', t):
        if m.group(1) != m.group(2):
            continue
        add(pat=P + '(B <=? x) && (x + 1 <=? B + N)', kind='segspan', line=lineno(t, m.start(3)),
            val=int(m.group(3)), base=int(m.group(1)), what='span_b', name=f'(x + 1 <=? {m.group(2)} + {m.group(3)})',
            ctx='inb', tok=f'inb{m.group(1)}')
    for m in re.finditer(r'Z\.to_N\s*\(x\s*-\s*(\d+)\)\s*<\?\s*(\d+)', t):
        add(pat=P + 'Z.to_N (x - B) <? N', kind='segspan', line=lineno(t, m.start(2)), val=int(m.group(2)),
            base=int(m.group(1)), what='span_b', name=f'Z.to_N (x - {m.group(1)}) <? {m.group(2)}', ctx='ltb',
            tok=f'ltb{m.group(1)}')
    for m in re.finditer(r'Z\.to_N\s*\(x\s*-\s*(0x[0-9a-fA-F]+)\)\)\s*with\s*\((\d+)\s*\+\s*Z\.to_N\s*\(x\s*-\s*'
                         r'(0x[0-9a-fA-F]+)\)\)%N', t):
        add(pat=P + '(OFF + Z.to_N (x - BSS))%N', kind='segspan', line=lineno(t, m.start(2)), val=int(m.group(2)),
            base=int(m.group(1), 16), bss=int(m.group(3), 16), what='bssoff',
            name=f'({m.group(2)} + Z.to_N (x - {m.group(3)}))%N', ctx='bssoff', tok=f'bssoff{m.group(1)}')
    for m in re.finditer(r'segments_reserved\s+\w+\s*=\s*\[(.*?)\]', t, re.S):
        for g in re.finditer(r'\(Z_to_bv 64 (' + NUM + r'),\s*Z_to_bv 64 (' + NUM + r')\)', m.group(1)):
            add(pat=P + '(Z_to_bv 64 B, Z_to_bv 64 N) of segments_reserved', kind='segspan',
                line=lineno(t, m.start(1) + g.start(2)), val=int(g.group(2), 0), base=int(g.group(1), 0),
                what='span_b', name=f'(Z_to_bv 64 {g.group(1)}, Z_to_bv 64 {g.group(2)})', ctx='resv',
                tok=f'resv{g.group(1)}')
    for m in re.finditer(r'sum_sizes\s*\(segments_reserved\s+\w+\)\s*=\s*(' + NUM + r')\s*\.', t):
        add(pat=P + 'sum_sizes (segments_reserved ..) = N', kind='segspan', line=lineno(t, m.start(1)),
            val=int(m.group(1), 0), what='sum', name=f'sum_sizes (segments_reserved _) = {m.group(1)}', ctx='sum',
            tok='sum')


GD, CGD = global_defs(T), global_defs(CT)
BTN, CBTN = bt_names(T), bt_names(CT)
EX = {f: extract(f, t, GD, BTN) for f, t in T.items()}
_hits = HITS.copy()
CEX = {f: extract(f, t, CGD, CBTN) for f, t in CT.items() if f in T}
HITS = _hits


def pair(f):  # donor counterpart of each count: same kind and context, same ordinal in the file
    res = {}
    if f not in CEX:
        return res
    od, oc = collections.defaultdict(list), collections.defaultdict(list)
    for c in sorted(EX[f], key=lambda c: (c['line'], c['ord'])):
        od[(c['kind'], c['ctx'])].append(c)
    for c in sorted(CEX[f], key=lambda c: (c['line'], c['ord'])):
        oc[(c['kind'], c['ctx'])].append(c)
    for k, l in od.items():
        for i, c in enumerate(l):
            if i < len(oc.get(k, [])):
                res[id(c)] = oc[k][i]
    return res


PAIRS = {f: pair(f) for f in T}


# ------------------------------------------------------------------------------------------------ rule helpers
class R:  # one rule result
    def __init__(self, rule, rec, meas='-', drec=None, verdict=None, note='', ship=None):
        self.rule, self.rec, self.meas, self.drec, self.note = rule, rec, meas, drec, note
        self.verdict = verdict or ('MEASURED TRUE' if rec is not None and rec == ship else 'DIFFERS')


def T_(rule, rec, ship, meas='-', drec=None, note=''):
    return R(rule, rec, meas, drec, 'MEASURED TRUE' if rec is not None and rec == ship else 'DIFFERS', note)


def NA(reason, ok=True, meas='-', ship=None):  # NOT-A-COUNT with a check
    return R('NOT-A-COUNT: ' + reason, ship if ok else None, meas, None, 'NOT-A-COUNT' if ok else 'DIFFERS')


def fname_at(X, x):
    f = X.func_at(x)
    return f'{f[2]} [{f[0]:#x}, {f[0] + f[1]:#x}) size {f[1]}' if f else '-'


def off_vaddr(X, off):  # the vaddr of a pin file offset
    for v, o, fz, mz in X.loads:
        if o <= off < o + fz:
            return f'{v + off - o:#x}'
    return f'file offset {off:#x}'


# ------------------------------------------------------------------------------------------------ code ranges
def is_exit(w):
    return w is not None and (w & 0x7f) in (0x6f, 0x67) and ((w >> 7) & 31) == 0


def desc(X, pc, n):  # (start fn, offset), (end fn, end offset, end fn size, end fn start), on X's twin
    fs, fe = X.func_at(pc), X.func_at(pc + 4 * n - 4)
    if not fs or not fe or pc - fs[0] >= max(fs[1], 4) and fs[1] or pc + 4 * n - fe[0] > fe[1]:
        return None
    return (fs[2], pc - fs[0]), (fe[2], pc + 4 * n - fe[0], fe[1], fe[0])


def whole_cover(X, pc, n):  # (end of the function holding the last word - pc) / 4, if pc is a function start
    fe, fs = X.func_at(pc + 4 * n - 4), X.func_at(pc)
    if not fe or not fs or fs[0] != pc:
        return None, None
    return (fe[0] + fe[1] - pc) // 4, fe


def first_exit(X, pc):
    fs = X.func_at(pc)
    if not fs or fs[0] != pc:
        return None
    for x in range(pc, pc + fs[1], 4):
        if is_exit(X.word(x)):
            return (x + 4 - pc) // 4
    return None


TEXT_TAIL = {'tfibmusl_text_count'}
SIBLING = {}


def code_rule(c, dc, f, k, dk):
    D, C = DI[k], CI[dk]
    pc, n = c['pc'], c['val']
    if pc is None:
        return R('no start address: the PC name resolves to no numeral', None, verdict='UNMEASURED')
    dpc, dn = (dc['pc'], dc['val']) if dc and dc.get('pc') is not None else (None, None)
    tlo, tsz = D.text()
    if c.get('cname') in TEXT_TAIL:
        rec = (tlo + tsz - pc) // 4
        drec = (C.text()[0] + C.text()[1] - dpc) // 4 if dpc is not None else None
        return T_(f'text-tail: (.text end {tlo + tsz:#x} - start {pc:#x}) / 4', rec, n,
                  f'.text [{tlo:#x}, {tlo + tsz:#x}); start in {fname_at(D, pc)}', drec)
    if pc == tlo:
        return T_(f'text: start = .text start {tlo:#x}, N = .text size {tsz:#x} / 4', tsz // 4, n,
                  f'.text [{tlo:#x}, {tlo + tsz:#x}) size {tsz:#x}', C.text()[1] // 4)
    if dpc is not None:
        dd = desc(C, dpc, dn)
        if dd:
            (sn, so), (en, eo, esz, est) = dd
            vs = D.pick(sn, pc)
            if vs is not None and vs + so == pc:
                ve = D.pick(en, pc)
                if ve is not None:
                    sz = D.fsize[ve]
                    if eo == esz:
                        rec, how = (ve + sz - pc) // 4, f'to the end of {en}'
                    else:
                        rec, how = (ve + eo - pc) // 4, f'to {en} + {eo}'
                        if sz != esz:
                            how += f' (size {sz} here, {esz} in cgif)'
                    rule = (f'donor structure: cgif range {dpc:#x} + 4*{dn} = {sn} + {so} {how}; here (twin {en} '
                            f'{ve:#x}' + (f' + {eo}' if eo != esz else f' + st_size {sz}') + f' - {pc:#x}) / 4')
                    meas = (f'start {pc:#x} = {sn} + {so}; {en} [{ve:#x}, {ve + sz:#x}) size {sz}; shipped end '
                            f'{pc + 4 * n:#x}')
                    if rec == n:
                        return R(rule, rec, meas, dn, 'MEASURED TRUE')
                    wc, we = whole_cover(D, pc, n)
                    cf = C.func_at(est - 4)
                    if eo != esz and eo % 4 == 0 and wc == n and pc + 4 * n == ve and cf and cf[0] + cf[1] == est:
                        kk = eo // 4
                        return R(f'exact function cover: twin FUNC {we[2]} ends at {pc + 4 * n:#x} = start of {en} '
                                 f'(whole functions from {pc:#x}); the donor range = its own exact cover (to the start '
                                 f'of {en}) plus {kk} word(s) of {en}', n, meas, dn - kk, 'MEASURED TRUE',
                                 f"exact function cover; the donor's +{kk} word(s) not taken")
                    over = pc + 4 * n - (ve + (sz if eo == esz else eo))
                    note = (f'over-cover: the shipped range runs {over // 4} word(s) past {how[3:]}' if over > 0 else
                            f'under-cover by {-over // 4} word(s)')
                    return R(rule, rec, meas, dn, 'DIFFERS', note)
    wc, we = whole_cover(D, pc, n)
    if wc == n:
        fs = D.func_at(pc)
        return R(f'whole functions (twin, no donor range): {fs[2]} .. {we[2]}: (end of {we[2]} - {pc:#x}) / 4', wc,
                 f'{fs[2]} [{fs[0]:#x}..); {we[2]} [{we[0]:#x}, {we[0] + we[1]:#x}); next {fname_at(D, we[0] + we[1])}',
                 None, 'MEASURED TRUE')
    fx = first_exit(D, pc)
    if fx == n:
        return R(f'prefix through the first exit (twin, no donor range): {D.fname[pc]} from {pc:#x} through its first '
                 f'ret / j / jr at {pc + 4 * n - 4:#x}', fx, fname_at(D, pc), None, 'MEASURED TRUE')
    sib = SIBLING.get((k, pc, n))
    if sib:
        fs = D.func_at(pc)
        return R(f'prefix of {fs[2]} + {pc - fs[0]} to + {pc + 4 * n - fs[0]} (twin, no donor range): the same range '
                 f'as {sib}, recomputed there by the donor structure rule', n, fname_at(D, pc), None, 'MEASURED TRUE')
    return R(f'whole functions (twin, no donor range): (end of the function holding the last word - {pc:#x}) / 4',
             wc, fname_at(D, pc), None, 'DIFFERS')


# ------------------------------------------------------------------------------------------------ definitions / fields
def last_ident(n):  # the last source identifier of an Itanium-mangled name
    out, i = None, 2
    if not n.startswith('_Z'):
        return None
    while i < len(n):
        m = re.match(r'(\d+)', n[i:])
        if m:
            k = int(m.group(1))
            s = i + len(m.group(1))
            out = n[s:s + k]
            i = s + k
        else:
            i += 1
    return out


def sym_addr(X, kind, name):  # gen_symtab's naming: non-identifier characters as _, a _<k> / _libc suffix
    san = lambda n: re.sub(r'[^A-Za-z0-9_]', '_', n)
    cands = {name, re.sub(r'_\d+$', '', name), re.sub(r'_libc$', '', name)}
    out = set()
    for n, v, sz, t in X.syms:
        if kind in 'AE' and t == 'STT_FUNC' and san(n) in cands:
            out.add(v if kind == 'A' else (v + sz if sz else X.Fst[bisect.bisect_right(X.Fst, v)]))
        elif kind == 'D' and t == 'STT_OBJECT' and (san(n) in cands or last_ident(n) in cands or
                                                     n.startswith('__malloc_') and n[len('__malloc_'):] in cands):
            out.add(v)
    return out


def str_name(s):  # the generator's name of a C string: '\n' as n, words joined by _
    return '_'.join(re.findall(r'[A-Za-z0-9]+', s.decode('latin-1').replace('\n', ' n ')))


def jal_target(X, ret):  # the target of the jal ra just before `ret`, or None
    w = X.word(ret - 4)
    if w is None or (w & 0x7f) != 0x6f or ((w >> 7) & 31) != 1:
        return None
    imm = ((w >> 31) & 1) << 20 | ((w >> 12) & 0xff) << 12 | ((w >> 20) & 1) << 11 | ((w >> 21) & 0x3ff) << 1
    return ret - 4 + (imm - (1 << 21) if imm >> 20 else imm)


def match_arms(t, name):  # the `| k%nat =>` arms of `Definition name (x : nat) : Z := match x with ..`
    m = re.search(r'Definition\s+' + re.escape(name) + r'\s*\((\w+)\s*:\s*nat\)\s*:\s*Z\s*:=\s*match\s+\1\s+with(.*?)'
                  r'\bend\s*\.', t, re.S)
    return [int(x) for x in re.findall(r'\|\s*(\d+)%nat\s*=>', m.group(2))] if m else None


def page_spans_text(X):
    return '; '.join(f'PT_LOAD {i}: base {b:#x} span {n:#x} filesz end {fe:#x}' for i, (b, n, fe) in enumerate(X.spans))


def def_rule(c, dc, f, k, dk):
    D, C = DI[k], CI[dk]
    nm, v, t = c['name'], c['val'], T[f]
    dv = dc['val'] if dc else None
    fd = defs_of(t)
    m = re.match(r'(?:tfib|src0)_([AED])_(\w+)$', nm)
    if m:
        kd, x = m.group(1), m.group(2)
        if kd == 'D' and x.startswith('str_'):
            s = D.cstr(v)
            ok = s is not None and 'str_' + str_name(s) == x
            return NA(f'an address, not a count: the pin\'s C string at {v:#x} spells the name ({s!r})', ok,
                      f'cstr at {v:#x} = {s!r}', v)
        s = sym_addr(D, kd, x)
        what = {'A': 'st_value', 'E': 'st_value + st_size', 'D': 'st_value (OBJECT)'}[kd]
        return NA(f'an address, not a count: twin {"OBJECT" if kd == "D" else "FUNC"} {x} {what}', v in s,
                  'twin ' + ' '.join(f'{z:#x}' for z in sorted(s)), v)
    m = re.match(r'AF_(\w+?)_(\w+)$', nm)
    if m:
        base_nm = [n for n, z in fd.items() if z == 0 and n.startswith(f'AF_{m.group(1)}_')]
        bfn = base_nm[0][len(f'AF_{m.group(1)}_'):] if len(base_nm) == 1 else None
        b, s = D.sym1(bfn, ('STT_FUNC',)) if bfn else None, D.sym1(m.group(2), ('STT_FUNC',))
        rec = s[0] - b[0] if s and b else None
        return NA(f'an offset, not a count: twin FUNC {m.group(2)} - twin FUNC {bfn} (the AF_ that is 0)',
                  rec == v, f'{m.group(2)} {s[0] if s else 0:#x} - {bfn} {b[0] if b else 0:#x}', v)
    if nm.startswith('RA_'):
        tg = jal_target(D, v)
        ok = tg is not None and tg in D.fname
        return NA(f'an address, not a count: a return point; the word before it is a jal ra to a twin function', ok,
                  f'{fname_at(D, v)}; jal ra -> {D.fname.get(tg, "-")}', v)
    if nm.endswith('TEXT_N'):
        lo = fd.get(nm[:-1] + 'LO')
        tlo, tsz = D.text()
        return T_(f'text: {nm[:-1]}LO = .text start {tlo:#x} ({lo == tlo}), N = .text size {tsz:#x} / 4',
                  tsz // 4 if lo == tlo else None, v, f'.text [{tlo:#x}, {tlo + tsz:#x})', C.text()[1] // 4)
    if nm in ('tfib_at_rw_len', 'src0_at_rw_len'):
        b, n, fe = D.spans[-1]
        return T_('RW segment length: span of the last PT_LOAD (page_up(vaddr + memsz) - page_down(vaddr))', n, v,
                  page_spans_text(D), CI[dk].spans[-1][1])
    if nm in ('tfib_at_n_res', 'src0_at_n_res'):
        return T_('reserved segments: the number of PT_LOAD (res_len_ok: length (segments_reserved segs) = n_res)',
                  len(D.loads), v, f'{len(D.loads)} PT_LOAD', len(C.loads))
    if nm in ('tfib_at_ph_ent_z', 'tfib_at_ph_num_z'):
        rec = D.phentsize if nm.endswith('ent_z') else D.phnum
        return T_('ELF header e_phentsize / e_phnum of the pin', rec, v, f'e_phentsize {D.phentsize} e_phnum {D.phnum}')
    m = re.match(r'(tfib|src0)_n(\w+)$', nm)
    if m:
        after = t[t.find('Definition ' + nm):]
        mm = re.search(r'Definition\s+(\w+)\s*\(\w+\s*:\s*nat\)', after)
        arms = match_arms(t, mm.group(1)) if mm else None
        ok = arms is not None and sorted(arms) == list(range(len(arms)))
        rec = len(arms) if ok else None
        return T_(f'table length: the `| k%nat =>` arms of {mm.group(1) if mm else "-"} (0 .. n-1)', rec, v,
                  f'{len(arms) if arms else 0} arms, contiguous {ok}')
    if nm == 'src0_debruijn_len':
        base = GD.get('src0_D_debruijn32')
        nxt = D.ostarts[bisect.bisect_right(D.ostarts, base)] if base is not None and D.ostarts else None
        ext = nxt - base if nxt else None
        b = D.raw_at(base, ext) if ext else None
        perm = b is not None and sorted(b) == list(range(len(b)))
        return T_(f'de Bruijn table extent: next object after src0_D_debruijn32 {base:#x} minus it; check: the pin\'s '
                  f'bytes there are a permutation of 0..n-1 ({perm})', ext if perm else None, v,
                  f'[{base:#x}, {nxt:#x}) next object at {nxt:#x}')
    if nm == 'CTX_SIZE':
        s = D.sym1('__malloc_context', ('STT_OBJECT',))
        return T_('sizeof(struct malloc_context) = twin OBJECT __malloc_context st_size', s[1] if s else None, v,
                  f'__malloc_context {s[0]:#x} size {s[1]}' if s else '-')
    if nm == 'FS_N' and 'CID' in fd:
        return NA(f'ASan FakeStack frames of class CID={fd["CID"]}: 2^(14 - CID) (runtime constant)',
                  v == 2 ** (14 - fd['CID']), f'2^(14-{fd["CID"]}) = {2 ** (14 - fd["CID"])}', v)
    if nm == 'SH_N' and 'FS_B' in fd:
        return NA('shadow bytes of one fake frame: FS_B / 8 (runtime constant)', v == fd['FS_B'] // 8, '-', v)
    if nm == 'FILL_N' and 'SH_N' in fd:
        return NA('8-byte shadow stores of one fake frame: SH_N / 8 (runtime constant)', v == fd['SH_N'] // 8, '-', v)
    if nm in ('BST_SIZE', 'META_SIZE', 'MAX_DICT_LEN'):
        what = {'BST_SIZE': 'sizeof(__sanitizer::BufferedStackTrace) of the sanitizer runtime both images link',
                'META_SIZE': 'sizeof(struct meta) of musl mallocng (5 words) both images link',
                'MAX_DICT_LEN': 'a C program constant of the model'}[nm]
        return NA(f'{what}; check: the donor file has the same value', dv == v, f'donor {dv}', v)
    if nm in ('CGIF_SIZE', 'FRAME_SIZE', 'RAW_SIZE'):
        lay = {'CGIF_SIZE': 'LAY_CGIF', 'FRAME_SIZE': 'LAY_Frame', 'RAW_SIZE': 'LAY_Raw'}[nm]
        fields = lay_fields(t, lay)
        if fields:
            end, al = max(o + w for o, w in fields), max(w for o, w in fields)
            rec = (end + al - 1) // al * al
        else:
            rec = None
        return NA(f'a C struct size of the program data model: end of the last field of {lay} rounded up to its '
                  f'widest field', rec == v, f'{lay}: {len(fields or [])} fields, rec {rec}', v)
    if nm == 'AMETA_SIZE' and {'AMETA_BUCKETS', 'AMETA_BUCKET'} <= set(fd):
        rec = page_up(fd['AMETA_BUCKETS'] * fd['AMETA_BUCKET'])
        return NA('a runtime allocator metadata area: page_up(AMETA_BUCKETS * AMETA_BUCKET) (the file\'s own '
                  'constants)', rec == v, f'page_up({fd["AMETA_BUCKETS"]} * {fd["AMETA_BUCKET"]}) = {rec}', v)
    if nm == 'STACK_LEN':
        return NA('the stack window of the process model: 2^47 (the user address space top)', v == 2 ** 47, '-', v)
    if re.fullmatch(r'A_\w+', nm) and re.search(r'SOff ' + nm + r'\b', t):
        return NA(f'a symbolic atom index (used as SOff {nm} in the file)', True, '-', v)
    if nm.startswith('CTX_') and 'CTX_SIZE' in fd:
        return NA('a field offset in struct malloc_context (the CTX_ offset table); check: below CTX_SIZE',
                  0 <= v < fd['CTX_SIZE'], f'CTX_SIZE {fd["CTX_SIZE"]}', v)
    if nm.startswith('o_'):
        return NA('a field offset of a runtime struct (o_ offset table of the file)', True, '-', v)
    if nm == 'SEC_LIVE_N':
        return NA('a model bound on the live secondary extents (the proof\'s own constant)', True, '-', v)
    if re.search(r'(?i)_entry$', nm) and nm not in ('tfib_entry', 'tfib_at_a_entry'):
        fs = D.func_at(v)
        ok = fs is not None and fs[0] <= v < fs[0] + max(fs[1], 4) and D.word(v) is not None
        return NA('an address, not a count: an entry PC; check: inside a twin function of the pin', ok,
                  f'{fname_at(D, v)}' + (' (its start)' if fs and fs[0] == v else ''), v)
    if nm in ('tfib_entry', 'tfib_at_a_entry'):
        return NA(f'an address, not a count: the ELF entry point; check: = e_entry {D.entry:#x}', v == D.entry,
                  f'e_entry {D.entry:#x}', v)
    if nm == 'tfib_at_sniff_tab':
        ok = v == 0 and not any('sniff' in n.lower() for n, _, _, _ in D.syms)
        return NA('an atable address field; 0 = the image has no sniff table; check: value 0 and no twin symbol '
                  'named *sniff*', ok, '-', v)
    if nm == 'FILE_SZ':
        s = D.sym1('__stdout_FILE', ('STT_OBJECT',))
        return T_('sizeof(FILE) = twin OBJECT __stdout_FILE st_size', s[1] if s else None, v,
                  f'__stdout_FILE {s[0]:#x} size {s[1]}' if s else '-')
    if nm in ('d_tab_words', 'MG_SLOTS'):
        what = {'d_tab_words': 'the sanitizer StackDepot table size 2^20 words (runtime constant)',
                'MG_SLOTS': 'a slot bound 2^15 of the mallocng model (the proof\'s own constant)'}[nm]
        return NA(f'{what}; check: the donor file has the same value', dv == v, f'donor {dv}', v)
    return None


def lay_fields(t, lay):  # the (offset, width) fields of `Definition LAY : layout_t := [..] [++ OTHER ++ [..]]`
    m = re.search(r'Definition\s+' + re.escape(lay) + r'\s*:\s*layout_t\s*:=\s*(.*?)\.\s', t, re.S)
    if not m:
        return None
    out = []
    for part in re.split(r'\+\+', m.group(1)):
        part = part.strip()
        if part.startswith('['):
            out += [(int(o), int(w)) for o, w in re.findall(r'\((\d+),\s*(\d+)%N\)', part)]
        elif re.fullmatch(r'\w+', part):
            sub = lay_fields(t, part)
            if sub is None:
                return None
            out += sub
    return out


def field_rule(c, dc, f, k, dk):
    D, C = DI[k], CI[dk]
    nm, v = c['name'], c['val']
    if nm == 'rw_len':
        return T_('RW segment length: span of the last PT_LOAD (page_up(vaddr + memsz) - page_down(vaddr))',
                  D.spans[-1][1], v, page_spans_text(D), C.spans[-1][1])
    if nm == 'ph_ent_z':
        return T_('ELF header e_phentsize of the pin', D.phentsize, v, f'e_phentsize {D.phentsize}', C.phentsize)
    if nm == 'ph_num_z':
        return T_('ELF header e_phnum of the pin', D.phnum, v, f'e_phnum {D.phnum}', C.phnum)
    if nm == 'n_res':
        return T_('reserved segments: the number of PT_LOAD (res_len_ok: length (segments_reserved segs) = n_res)',
                  len(D.loads), v, f'{len(D.loads)} PT_LOAD', len(C.loads))
    if nm == 'seg_size':
        mm = re.search(r'seg_size\s*:=\s*' + str(v) + r'\s*;\s*seg_perms\s*:=\s*"[^"]*"%string\s*;\s*seg_bytes\s*:=\s*'
                       r'\["([0-9a-fA-F]*)"%pstring\]', c['rec'])
        ok = mm is not None and len(mm.group(1)) // 2 == v
        return NA('the size of a synthetic test segment (not an image): its seg_bytes hex length / 2', ok,
                  f'seg_bytes {mm.group(1) if mm else "-"}', v)
    if nm == 'rg_len' and v == 0:
        return NA('the default record of a runtime-model region lookup (rg_len := 0 when absent)', True, '-', v)
    return None


# ------------------------------------------------------------------------------------------------ segment geometry
def segspan_rule(c, dc, f, k, dk):
    D, C = DI[k], CI[dk]
    v, w = c['val'], c['what']
    pt = page_spans_text(D)
    if w in ('span', 'zoff', 'zlen'):
        i = c['seg']
        if i >= len(D.spans):
            return R(f'segment {i}: no such PT_LOAD', None, pt, None, 'DIFFERS')
        b, n, fe = D.spans[i]
        if w == 'span':
            return T_(f'span of PT_LOAD {i} (seg_bytes_{i:03d}): page_up({D.loads[i][0]:#x} + {D.loads[i][3]:#x}) - '
                      f'{b:#x}', n, v, pt, C.spans[i][1] if i < len(C.spans) else None)
        off = fe - b
        if w == 'zoff':
            return T_(f'zero scan start in PT_LOAD {i}: filesz end {fe:#x} - base {b:#x}', off, v, pt,
                      C.spans[i][2] - C.spans[i][0] if i < len(C.spans) else None)
        return T_(f'zero scan length in PT_LOAD {i}: span {n:#x} - (filesz end {fe:#x} - base {b:#x})', n - off, v, pt,
                  C.spans[i][1] - (C.spans[i][2] - C.spans[i][0]) if i < len(C.spans) else None)
    if w == 'span_b':
        i = D.span_by_base(c['base'])
        if i is None:
            return R(f'no PT_LOAD with page base {c["base"]:#x}', None, pt, None, 'DIFFERS')
        return T_(f'span of PT_LOAD {i} (page base {c["base"]:#x})', D.spans[i][1], v, pt)
    if w == 'bssoff':
        i = D.span_by_base(c['base'])
        ok = i is not None and D.spans[i][2] == c['bss']
        return T_(f'BSS offset in PT_LOAD {i}: BSS {c["bss"]:#x} - base {c["base"]:#x}; check: BSS = filesz end '
                  f'({ok})', c['bss'] - c['base'] if ok else None, v, pt)
    if w == 'sum':
        return T_('sum of the PT_LOAD spans (segments_reserved)', sum(n for b, n, fe in D.spans), v, pt,
                  sum(n for b, n, fe in C.spans))
    return None


# ------------------------------------------------------------------------------------------------ slices and lengths
IMGLIST = re.compile(r'\b(IMG_REGIONS|IMG_B|IMG_E|IMG_L|IMG_LC|IMG_X|IMG_XL)\b')
REGLIST = re.compile(r'ss_mem|\bIMG_\w+|_mem\b|L_pieces|\brs_\w+|\brs[A-Z]\w*|PM_\w+|\bmem\b|^m$')


def regions_list(text):  # the region names of YD2j.v's IMG_REGIONS, in order
    m = re.search(r'Definition IMG_REGIONS\s*:\s*smem\s*:=\s*\[(.*?)\]\.', text, re.S)
    return [x.strip() for x in m.group(1).split(';')] if m else []


RD, RC = regions_list(T.get('Reusable/YD2j.v', '')), regions_list(CT.get('Reusable/YD2j.v', ''))
print(f'IMG_REGIONS in YD2j.v: fuzz_disco {len(RD)} regions, cgif {len(RC)} regions')


def imgreg_rule(c, dc):
    if not dc:
        return None
    kc, kk = dc['val'], c['val']
    R_, Rc = len(RD), len(RC)
    meas = f'IMG_REGIONS: fuzz_disco {R_}, cgif {Rc}'
    if kc >= Rc:
        return T_(f'image regions: reaches past the image block: cgif {kc} + (regions {R_} - {Rc})', kc + R_ - Rc, kk,
                  meas, kc)
    if kc <= 4:
        return T_(f'image regions: {kc} region(s) in front of the image block or at its start (same names in both '
                  f'trees): cgif {kc}', kc, kk, meas, kc)
    nm = RC[kc]
    rec = RD.index(nm) if nm in RD else None
    return T_(f'image regions: index of {nm} in YD2j IMG_REGIONS (cgif index {kc})', rec, kk, meas, kc)


def cell(addr):  # YF0m.v's const cell value at addr (width 4 or 8), or None
    m = re.findall(r'z[48] \(ANum %s\) (0x[0-9a-fA-F]+|\d+)' % hex(addr), T.get('Reusable/YF0m.v', ''))
    return int(m[0], 0) if len(m) == 1 else None


_STRDEF = collections.defaultdict(set)
for _t in T.values():
    for _m in re.finditer(r'Definition\s+(\w+)\s*:\s*list byte\s*:=\s*strB\s+"([^"]*)"(?:%string)?(\s*\+\+\s*nlB)?'
                          r'\s*\.', _t):
        _STRDEF[_m.group(1)].add(_m.group(2).encode() + (b'\n' if _m.group(3) else b''))


def strdef(name):  # the bytes of the one `Definition NAME : list byte := strB ".." [++ nlB].` of the tree, or None
    s = _STRDEF.get(name.split('.')[-1], ())
    return next(iter(s)) if len(s) == 1 else None


def yb01_lengths():  # length of each `list kentry` Definition of YB01.v: literal lists and ++ of seg slices
    t = T.get('Reusable/YB01.v', '')
    L, segs = {}, collections.defaultdict(list)
    for m in re.finditer(r'Definition (\w+) : list kentry :=\s*(.*?)\.\n', t, re.S):
        n = 0
        for part in split_top(m.group(2), '++'):
            part = part.strip()
            s = re.fullmatch(r'seg (\w+) (\d+) (\d+)', part)
            if s:
                n += max(0, min(int(s.group(3)), L.get(s.group(1), 0) - int(s.group(2))))
                segs[m.group(1)].append((int(s.group(2)), int(s.group(3))))
            elif part.startswith('['):
                n += len([x for x in split_top(part[1:-1], ';') if x.strip()])
        L[m.group(1)] = n
    return L, segs


def split_top(s, sep):
    out, d, cur, i = [], 0, [], 0
    while i < len(s):
        ch = s[i]
        if ch in '([{':
            d += 1
        elif ch in ')]}':
            d -= 1
        if d == 0 and s.startswith(sep, i):
            out.append(''.join(cur))
            cur = []
            i += len(sep)
            continue
        cur.append(ch)
        i += 1
    out.append(''.join(cur))
    return out


YB01L, YB01S = yb01_lengths()
# the collector's image runs in the hand-off states: `KImg LO HI` (bytes [LO, HI) still hold the image's bytes)
KIMG = sorted({(int(x), int(y)) for x, y in re.findall(r'\bKImg (\d+) (\d+)', T.get('Reusable/YB01.v', ''))})


def ctx_arrays():  # mallocng array lengths from YO0f.v's CTX_ offsets
    fd = defs_of(T.get('Reusable/YO0f.v', ''))
    try:
        return {48: ((fd['CTX_usage'] - fd['CTX_active']) // 8, (fd['CTX_unmap_seq'] - fd['CTX_usage']) // 8),
                32: (fd['CTX_bounces'] - fd['CTX_unmap_seq'], fd['CTX_seq'] - fd['CTX_bounces'])}
    except KeyError:
        return {}


CTXA = ctx_arrays()

# (regex over `FILE NAME`, reason, check) for slices / lengths that are not image counts; first match wins.
# A check is a function (c, f) -> bool, or None (the reason is the evidence).
NOTCOUNT = [
    (r' (firstn|skipn) 0 ', 'firstn / skipn 0: the empty or the whole list (a proof step)', lambda c, f: c['val'] == 0),
    (r'length \(?(st_active|st_usage)\b.*=\?? 48$|length l = 48$',
     'mallocng struct malloc_context arrays active[48] / usage_by_class[48]; check: YO0f CTX_ offsets give 48',
     lambda c, f: CTXA.get(48) == (48, 48)),
    (r'length \(?(st_unmap_seq|st_bounces)\b.*=\?? 32$|YN13(_cf)?\.v length b = 32$|'
     r'YO0s\.v length (l|\(zset k v l\)|\(repeat 0 32\)) = 32$|'
     r'length \(?useq(_of A\))? = 32$',
     'mallocng struct malloc_context arrays unmap_seq[32] / bounces[32]; check: YO0f CTX_ offsets give 32',
     lambda c, f: CTXA.get(32) == (32, 32)),
    (r'length \(?(st_cache|st_regions|init_caches)\b.*= 32$',
     'the allocator model\'s per-class cache / region arrays: 32 entries (wf_len_cache / wf_len_regions of the '
     'model; Z.to_nat c < 32)', None),
    (r'\bsr_atoms\b', 'index into the 32 symbolic register atoms; check: N <= 32', lambda c, f: c['val'] <= 32),
    (r'length \(?(s_regs|ts\b)', 'the 32 RISC-V integer registers; check: N = 32', lambda c, f: c['val'] == 32),
    (r'length (p|path|str|LM|LI|bs) (<|<=) ?(4096|4095)$|firstn 4096 (p|path)\b|length \(firstn 4096 (p|path)\) = '
     r'4096$|YI0t\.v length (LM|LI) = 4096$|YK0p\.v length bs = 4096$',
     'the 4096-byte PATH_MAX / page bound of a string read (Linux constant)', lambda c, f: c['val'] in (4095, 4096)),
    (r'(SEALED_BYTES|strncpy_sealed_bytes)\b',
     'the sealed strncpy copy: 8 sealed bytes + 4087 zeros = the 4095-byte strncpy length (the file\'s own '
     'definition); check: value 4095 or the 8 sealed bytes',
     lambda c, f: c['val'] in (8, 4095)),
    (r'YO0[78]\.v ', 'a byte offset / slice of the GIF / dictionary program data model (C object layout, proof-local)',
     None),
    (r'(firstn|skipn) \d+ \((x :: t|b :: bs)\)$', 'a proof-local list (a lemma\'s own list argument)', None),
    (r'length \(?(word_to_le_bytes 8 (v|\(Z_to_bv 64 \w+\))|word_le8 v)\)? = 8$|'
     r'length (l|l1|l2|w|x|bs|bs\'|bytes|bsb) (=|<=) [1-8]$|'
     r'(firstn|skipn) [1-8] \(skipn .* (bs|\(pf_bytes c s k\)|\(word_to_le_bytes w V\))\)$|'
     r'(firstn|skipn) [1-8] \(skipn \d+ rb\)$|'
     r'length \((canary_bytes rb|hwcap_bytes hw|uid_bytes uid)\) = 8$|length \(rand_bytes rnd\) = 16$|'
     r'(firstn|skipn) [1-8] (w|x\.|post|rb)$',
     'a byte width of a machine word / an auxv or canary field (1..8 bytes; AT_RANDOM 16)',
     lambda c, f: c['val'] in (1, 2, 3, 4, 5, 6, 7, 8, 16)),
    (r'(firstn|skipn) \d+ \(?r_chunks', 'chunks of one model region (a proof-local list)', None),
    (r'YB01\.v length HS_tfib_list', None, None),  # measured below
    (r'length (tr|acc|acc\'|\(unwind_of_chain|\(Y\w+\.tr\b)|firstn 30 \(acc', None, None),  # measured below
    (r'length \(?(musl_maps ch|fog|extra)\)? <=|length \(?(maps_subtract|iv_subtract)\b|skipn 3 \(a_maps ch\)',
     'a bound on the start-up\'s anonymous maps / holes of the runtime model (the first 3 maps of a_maps are the '
     'runtime\'s reservations)', None),
    (r'length \(segments_reserved src0segs\) <= 8$',
     'a bound on the reserved segments; check: every build has <= 8 PT_LOAD',
     lambda c, f: all(len(DI[k].loads) <= 8 for k in KEYS)),
    (r'length ivs <= (84|120)$', 'a bound on the interval list of the allocator model (the proof\'s own bound)', None),
    (r'length (av|ev) <= (1024|256)$|length \(?nth k av|length \(auxv_words [^)]*\) = 20$|length \(udecZ? v\) <= 20$',
     'a bound of the start-up stack model (argv / envp counts, 20 decimal digits of a u64, 20 auxv words)', None),
    (r'length \(?(qc_list|P)\b.*< 100000$|length .* =\?? 0$',
     'an empty-list test (length = 0) or a fuel bound of the model', None),
    (r'length data <\?? \d+$|\bconfig_len\b',
     'a byte count of the harness input (the fuzzer\'s data bytes against the harness header size)', None),
    (r'length \(nested_at ', 'a proof-local test of the mallocng model (one nested slot)', None),
    (r'length \(ly_tr0 ly\) <= 31$|length \(ly_extra ly\) <= 8$|length TBLS[0F] = 31$',
     'a bound of the allocator layout model (31 size-class tables, 8 extra regions; the model\'s own lists)', None),
    (r'YL0l\.v length rl = 17$', 'the 17 junk registers of the harness model (k - 29 for k >= 29)', None),
    (r'length \(fs_hint \(st_fs s\)\) = 11$', 'the 11 file-system hints of the runtime model (wf_fs)', None),
    (r'(firstn|skipn) \d+ (l|\(x :: t\)|\(skipn i l\)|r)$|firstn 1 \(skipn i l\)|length argv = 1$',
     'a proof-local list (a lemma\'s own list argument)', None),
    (r'(firstn|skipn) \d+ \(?(ss_mem|REG0|REG0K)\b|length \(?(ss_mem|REG0U\d|MREG0|MKREG0|SREG0)\b|'
     r'length \(firstn \d+ \(ss_mem|skipn \d+ mem_NR|(firstn|skipn) \d+ \(skipn .*\bREG0K?\)$',
     'index into / length of the region list of a symbolic state of the allocator / stack model; check: the file '
     'names no image region list', lambda c, f: IMGLIST.search(T[f]) is None),
    (r'length \(?(st_depot|st_chunks|all_batches|pc_chunks|st_sec_arr|st_areas|lazy_zones|blocked_all)\b|'
     r'length (obs|L|listing|data|esi|bs2|y|\(snd ab\)|ivs|bsb|bs|bytes|l|s0|str|p)\b.*(<=|<) (2|25|257|16|16384|'
     r'54000|4096|131071|34359736320|2240000)$|length \(build_stack_bytes [^)]*\) <=? (2|2240000)$|'
     r'length \(nth \d+ argv \[\]\) <= 66$|length path <= (60|62)$',
     'a bound of the runtime / start-up model (the proof\'s own bound, not an image extent)', None),
]


def slice_len_rule(c, dc, f, k, dk):
    D = DI[k]
    t, v = T[f], c['val']
    arg = c.get('arg', '')
    dv = dc['val'] if dc else None
    base = f[len("Reusable/"):]
    key = f'{base} length {arg} {c["op"]} {v}' if c['kind'] == 'length' else f'{base} {c["name"]}'
    if c['kind'] == 'seg':
        L = YB01L.get(c['lst'])
        ok = L is not None and c['i'] + v <= L
        return NA(f'an encoding slice of the collector\'s hand-off state lists (YB01 writes each state as slices of '
                  f'{c["lst"]} plus changed entries; it counts list entries, not image words); check: {c["i"]} + {v} '
                  f'<= length {c["lst"]} = {L} and the slices of each list ascend without overlap', ok and SEG_ORDER_OK,
                  f'length {c["lst"]} = {L}', v)
    if c['kind'] == 'length':
        al = re.search(r'set \(' + re.escape(arg) + r' := if \w+ then (\w+) else (\w+)\)', t)
        names = [al.group(1), al.group(2)] if al else [arg]
        adr = [re.search(r'img_msg_chk (0x[0-9a-fA-F]+) ' + re.escape(x) + r'\b', t) for x in names]
        if all(adr):
            ls = {len(D.cstr(int(m.group(1), 16)) or b'') for m in adr}
            rec = ls.pop() if len(ls) == 1 else None
            return T_('string length in the pin: strlen at the img_msg_chk address of ' +
                      ' / '.join(f'{x} ({m.group(1)})' for x, m in zip(names, adr)), rec, v,
                      '; '.join(f'cstr {m.group(1)} = {D.cstr(int(m.group(1), 16))!r}' for m in adr), dv)
        m = re.fullmatch(r'\(strB "([^"]*)"%string( \+\+ nlB)?\)', arg)
        s = m.group(1).encode() + (b'\n' if m.group(2) else b'') if m else strdef(arg)
        if s is not None:
            if s in D.raw:
                return T_(f'string literal length {len(s)}; check: the bytes occur in the pin: True', len(s), v,
                          f'{s!r}', dv)
            for dm in re.finditer(rb'\d+', s):  # a printf message: the pin holds its format with %u / %d
                for conv in (b'%u', b'%d', b'%lu', b'%zu', b'%llu'):
                    fmt_ = s[:dm.start()] + conv + s[dm.end():]
                    at = D.raw.find(fmt_ + b'\0')
                    if at >= 0:
                        rec = len(fmt_) - len(conv) + len(dm.group(0))
                        return T_(f'formatted message length: the pin\'s format {fmt_!r} with {conv.decode()} = '
                                  f'{dm.group(0).decode()}: {len(fmt_)} - {len(conv)} + {len(dm.group(0))}', rec, v,
                                  f'format at {off_vaddr(D, at)}', dv)
            return R(f'string literal length {len(s)}; check: the bytes occur in the pin: False', None, f'{s!r}', dv,
                     'DIFFERS')
        if arg == 'nlB':
            return T_('one newline byte (nlB = [10])', 1, v, '-', dv)
        if arg == 'HS_tfib_list':
            n = len(re.findall(r'Definition HS_tfib_\d+ : acs', t))
            return T_(f'the collector hand-off states: Definitions HS_tfib_<k> : acs in the file ({n})', n, v,
                      f'{n} HS_tfib_<k> : acs', dv)
    if re.search(r'\btr\b|\bacc\b|\bacc\'|unwind_of_chain|\.tr\b', arg) and v in (29, 30) and c['kind'] in ('length',
                                                                                                   'slice'):
        mc = GD.get('tfib_D_malloc_context_size')
        cv = cell(mc) if mc is not None else None
        return T_(f'stack trace depth malloc_context_size: YF0m.v const cell at tfib_D_malloc_context_size '
                  f'{mc:#x} = {cv}' + (' (minus the frame added after the check)' if v == 29 else ''),
                  cv - (30 - v) if cv else None, v, f'YF0m cell {mc:#x} = {cv}', dv)
    img_file = IMGLIST.search(t) is not None
    if img_file and f in CT and REGLIST.search(arg) and not re.search(r'\b(data|p|bs|buf|src|cs)\b', arg):
        r = imgreg_rule(c, dc)
        if r:
            return r
    for rx, why, chk in NOTCOUNT:
        if why and re.search(rx, key):
            return NA(why, chk(c, f) if chk else True, '-', v)
    return None


def seg_order_ok():
    for lst, ss in YB01S.items():
        pos = -1
        for i, n in ss:
            if i < pos:
                return False
            pos = i + n
    return True


SEG_ORDER_OK = seg_order_ok()


# ------------------------------------------------------------------------------------------------ extents
def extent_rule(c, dc, f, k, dk):
    D = DI[k]
    v = c['val']
    dv = dc['val'] if dc else None
    if c['kind'] == 'extent':
        s = D.cstr(c['lo'])
        if s is not None and len(s) + 1 == v:
            return T_(f'string region: strlen at {c["lo"]:#x} + 1 (the NUL) in the pin', len(s) + 1, v, f'{s!r}', dv)
        so = D.sym1('__stdout_FILE', ('STT_OBJECT',))
        if so and so[0] - c['lo'] == v:
            return T_(f'region clipped at the stdout FILE: twin OBJECT __stdout_FILE {so[0]:#x} - {c["lo"]:#x}',
                      so[0] - c['lo'], v, f'__stdout_FILE {so[0]:#x}', dv)
        cells = re.findall(r'mkChunk\s+(' + NUM + r')\s+\(CVal\s+(\d+)\s+\(SLit\s+(' + NUM + r')\)\)', c['chunks'])
        cells = [(int(x, 0), int(w), int(y, 0)) for x, w, y in cells]
        pos, ok = c['lo'], bool(cells)
        for x, w, y in cells:
            b = D.raw_at(x, w)
            ok = ok and x == pos and b is not None and int.from_bytes(b, 'little') == y
            pos = x + w
        if ok:
            return T_(f'object cells: the region is its cells [{c["lo"]:#x}, {pos:#x}), each cell equal to the pin\'s '
                      f'bytes', pos - c['lo'], v, f'{len(cells)} cell(s)', dv)
        return R('string / object region: no rule reproduces it', None, f'cstr {s!r}', dv, 'DIFFERS')
    if c['kind'] == 'cimg':
        if f == 'Reusable/YD28.v':
            so = D.sym1('__stdout_FILE', ('STT_OBJECT',))
            rec = so[0] - c['lo'] if so else None
            return T_(f'region clipped at the stdout FILE: twin OBJECT __stdout_FILE - {c["lo"]:#x}', rec, v,
                      f'__stdout_FILE {so[0]:#x}' if so else '-', dv)
        gen = D.pin_sha in '\n'.join(RAW[f].split('\n')[:8])
        reg = None
        for lo, hi, l0, l1, chunks in regions_of(f):
            if l0 <= c['line'] <= l1 and ('mkChunk %d (CImg %d)' % (c['lo'], v)) in chunks:
                starts = sorted(int(x, 0) for x in re.findall(r'mkChunk\s+(' + NUM + r')\s', chunks))
                reg = (lo, hi, starts)
        if reg is None:
            return R('a CImg chunk outside a literal region: no rule', None, '-', dv, 'UNMEASURED')
        lo, hi, starts = reg
        nxt = min([x for x in starts if x > c['lo']] + [hi])
        runs = [(x, y) for x, y in KIMG if x <= c['lo'] < y]
        run = min(runs, key=lambda r: (r[0] != c['lo'], r)) if runs else None
        end = min(run[1], nxt) if run else None
        inside = lo <= c['lo'] < hi and D.in_spans(lo, hi)
        ok = gen and inside and run is not None
        return T_(f'generated region extent: the collector\'s image run (YB01 `KImg LO HI` holding the chunk start) '
                  f'clipped to the next chunk start / the region hi; check: the header names the pin sha256 ({gen}) and '
                  f'the region lies in the pin\'s loaded segment spans ({inside})', end - c['lo'] if ok else None, v,
                  f'region [{lo:#x}, {hi:#x}), {len(starts)} chunk(s); KImg ' +
                  (f'[{run[0]:#x}, {run[1]:#x})' if run else '-') + f'; next {nxt:#x}', dv)
    if c['kind'] == 'rotab':
        end = max((o + w for o, w in c['cells']), default=None)
        return T_('read-only cell table: the end of its last cell (offset + width)', end, v, f'{len(c["cells"])} '
                  f'cell(s)', dv)
    return None


_REG = {}


def regions_of(f):  # (lo, hi, first line, last line, chunk text) of every literal `mkRegion None LO HI _ _ [..]` of f
    if f not in _REG:
        t = T[f]
        _REG[f] = [(int(m.group(1)), int(m.group(2)), lineno(t, m.start()), lineno(t, m.end()), m.group(3))
                   for m in re.finditer(r'mkRegion None (\d+) (\d+) \d+ \d+\s*\[([^\]]*)\]', t)]
    return _REG[f]


# ------------------------------------------------------------------------------------------------ apply
RULES = {'code': code_rule, 'def': def_rule, 'field': field_rule, 'seg': slice_len_rule, 'slice': slice_len_rule,
         'length': slice_len_rule, 'extent': extent_rule, 'cimg': extent_rule, 'rotab': extent_rule,
         'segspan': segspan_rule}
NO_IMAGE = R('no build key for this file (not in the table, no images Require, no stem file)', None,
             verdict='UNMEASURED')


def apply(f, c, dc):
    ks, src, dmap = IMGS[f]
    if not ks:
        return NO_IMAGE, []
    res = []
    for k in ks:
        r = RULES[c['kind']](c, dc, f, k, dmap[k])
        res.append(r if r is not None else R('no rule', None, verdict='UNMEASURED'))
    return res[0], res


# donor-structure code rows first: they give the sibling table for ranges with no donor range
for f in sorted(T):
    ks, src, dmap = IMGS[f]
    for c in EX[f]:
        if c['kind'] == 'code' and c['pc'] is not None:
            for k in ks:
                r = code_rule(c, PAIRS[f].get(id(c)), f, k, dmap[k])
                if r.verdict == 'MEASURED TRUE' and r.rule.startswith('donor structure'):
                    SIBLING.setdefault((k, c['pc'], c['val']), f'{f}:{c["line"]}')

fmt = lambda x: '-' if x is None else str(x)
one = lambda s: re.sub(r'\s+', ' ', str(s)).strip()
out = []
for f in sorted(T):
    for c in EX[f]:
        dc = PAIRS[f].get(id(c))
        r0, res = apply(f, c, dc)
        ks, src, dmap = IMGS[f]
        if len(res) > 1:
            vs = {r.verdict for r in res}
            verdict = ('MEASURED TRUE' if vs == {'MEASURED TRUE'} else 'NOT-A-COUNT' if vs == {'NOT-A-COUNT'} else
                       'UNMEASURED' if 'UNMEASURED' in vs else 'DIFFERS')
            recs = [fmt(r.rec) for r in res]
            rec = recs[0] if len(set(recs)) == 1 else ' '.join(f'{k}:{x}' for k, x in zip(ks, recs))
            meas = ' | '.join(f'{k}: {one(r.meas)}' for k, r in zip(ks, res))
            drs = [fmt(r.drec) for r in res]
            drec = drs[0] if len(set(drs)) == 1 else ' '.join(f'{k}:{x}' for k, x in zip(ks, drs))
            notes = sorted({r.note for r in res if r.note})
            r0 = R(r0.rule, None, meas, None, verdict, '; '.join(notes))
            recf, drecf = rec, drec
        else:
            recf, drecf = fmt(r0.rec), fmt(r0.drec)
        imgs = (','.join(ks) or '-') + f' ({src})' + (
            ' donor ' + ','.join(dmap[k] for k in ks) if any(dmap[k] != k for k in ks) else '')
        out.append([f'{f}:{c["line"]}', c['kind'], one(c['name']), str(c['val']), one(r0.rule), recf, one(r0.meas),
                    imgs, fmt(dc['val'] if dc else None), drecf, r0.verdict, one(r0.note), '', c['ord'],
                    c.get('tok', ''), c['pat']])

# keys: FILE:LINE, plus :TOKEN when the line holds more than one count; #i when a token repeats on a line
per_line = collections.Counter(o[0] for o in out)
for o in out:
    if per_line[o[0]] > 1:
        o[0] = f'{o[0]}:{one(o[14])}'
keys = collections.Counter(o[0] for o in out)
for kk in sorted(k for k, n in keys.items() if n > 1):
    for i, o in enumerate(sorted((o for o in out if o[0] == kk), key=lambda o: o[13]), 1):
        o[0] = f'{kk}#{i}'

bad = []
acc = {}
for x in a.accept:
    kk, sep, txt = x.partition('=')
    if not sep or ':' not in txt:
        bad.append(f'--accept wants KEY=CLASS:REASON: {x}')
        continue
    acc[kk] = txt
for kk, txt in sorted(acc.items()):
    cl, _, why = txt.partition(':')
    want = 'MEASURED TRUE' if cl == 'MEASURED TRUE' else 'DIFFERS'
    hit = [o for o in out if (o[0] == kk or o[0].startswith(kk + ':')) and o[10] == want]
    if not hit:
        bad.append(f'--accept {kk} names no {want} row')
    for o in hit:
        o[12] = one(f'{cl}: {why}')


def sort_key(o):
    f, rest = o[0].split(':', 1)
    return f, int(re.match(r'\d+', rest).group(0)), o[0]


out.sort(key=sort_key)
COLS = ['key', 'form', 'name/call', 'shipped', 'rule', 'recomputed', 'measurement', 'images', 'donor shipped',
        'donor recomputed', 'verdict', 'status', 'note', 'accept']


def status(o):  # the gates-A slice's status words for the same verdict
    if o[10] == 'MEASURED TRUE':
        return 'TRUE' if o[11].startswith('exact function cover') else 'EQUAL'
    return {'NOT-A-COUNT': 'NOT-IMAGE', 'DIFFERS': 'DIFFERS', 'UNMEASURED': 'UNRULED'}[o[10]]


with open(a.out, 'w') as fh:
    fh.write('\t'.join(COLS) + '\n')
    for o in out:
        fh.write('\t'.join(o[:11] + [status(o)] + o[11:13]) + '\n')

st = collections.Counter(o[10] for o in out)
for p_, n in sorted(HITS.items()):
    print(f'pattern hits\t{p_}\t{n}')
for (kd, s), n in sorted(collections.Counter((o[1], o[10]) for o in out).items()):
    print(f'form {kd}\tverdict {s}\t{n}')
for s in sorted(st):
    print(f'verdict {s}\t{st[s]}')
dif = [o for o in out if o[10] == 'DIFFERS']
accd = sum(1 for o in dif if o[12])
print(f'rows {len(out)}; DIFFERS {len(dif)} (accepted {accd}, not accepted {len(dif) - accd}); UNMEASURED '
      f'{st["UNMEASURED"]}')
for o in out:
    if o[10] in ('DIFFERS', 'UNMEASURED'):
        print(o[10] + '\t' + '\t'.join(o[:10]) + ('\t' + o[11] if o[11] else '') + ('\taccept: ' + o[12] if o[12] else ''))
for b in bad:
    print('count_recompute: ' + b)
sys.exit(1 if bad or st['UNMEASURED'] or len(dif) > accd else 0)
