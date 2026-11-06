#!/usr/bin/env python3
"""count_recompute.py -- find every image-derived count in lib/A (image A, fuzz_disco.asan) and recompute it.

Proves no function (kind: measurement).

A relocated proof file can keep a count of the donor image (cgif_file_fuzzer.asan): a word count, a table length, a
region count, a size. A by-value check cannot see such a count when its value is also some right quantity of the
target image. This script finds the counts by fixed text patterns, gives each one a RULE that derives it from an
image, applies the rule to fuzz_disco.asan's pin and unstripped twin (the recomputed value) and to cgif's pin and twin
(the donor recomputed value), and compares.

Usage: count_recompute.py --lib LIB --pin PIN --twin TWIN --cgif-lib CGIF_LIB --cgif-pin CGIF_PIN
                          --cgif-twin CGIF_TWIN --out COUNTS.tsv [--ruling KEY=TEXT ...]
  LIB, CGIF_LIB    the checked tree and the donor tree (each the directory that holds A/); a file of LIB/A pairs with
                   the file of CGIF_LIB/A at the same relative path, if there is one
  PIN, TWIN        fuzz_disco.asan and its unstripped twin; bytes are read from the pin, symbols from the twin
  CGIF_PIN/TWIN    the same for cgif_file_fuzzer.asan
  --ruling KEY=TEXT  (repeatable) put TEXT in the ruling column of the DIFFERS row whose key column is KEY; the row
                   keeps status DIFFERS. KEY is FILE:LINE when that line holds one counted item, else
                   FILE:LINE:TOKEN, TOKEN being the range's PC as written (e.g. A/AE34.v:26:0x429c4), the definition
                   or field name, seg<I>, firstn<N> / skipn<N>, len:<EXPR>, ext<LO>, cimg<ADDR>; a token that occurs
                   twice on a line gets #1, #2 in text order. The key column of the output shows the exact form.

Output: one row per count, sorted by file, line and key; columns key, name/call, shipped, rule, recomputed, donor
shipped (the paired donor count, `-` if none), donor recomputed (the rule applied to cgif's images, `-` if the rule
has no donor form), status, note, ruling. No timestamp, no absolute path: a re-run gives the same bytes.
Statuses: EQUAL (the rule recomputes the shipped value from the image), TRUE (see the code rules), DIFFERS (the
rule gives another value), GENERATED (written from this pin by a start-up generator; only bounds are checked),
NOT-IMAGE (not an image quantity: the rule says what it counts, with a check where one is cheap), UNRULED (a pattern
matched, no rule applies). The summary prints the counts by pattern and status, `DIFFERS n (ruled r, unruled u)`, and
every DIFFERS / TRUE / UNRULED row. Exit 1 when a twin does not match its pin (PT_LOAD table, and PT_LOAD 2.. bytes),
a row is UNRULED, u > 0, or a ruling matches no DIFFERS row; else 0.

Patterns (each match is one count; a line can hold several):
  P1 code range     `build_table SEGS PC N%nat` (PC a hex literal)
  P2 code range     `(PC, N%nat)` (PC a hex literal, or a name with a `Definition NAME : Z := NUMERAL.` in the same
                    file or a single such value in the tree)
  P3 code range     `Definition COUNT : nat := N.` where some `build_table SEGS START COUNT` of the tree names COUNT
                    and START resolves to a numeral Definition
  P4 definition     `Definition NAME : nat|Z|N := NUMERAL.` with NAME ending in _len, _cnt, _count, _size, _bytes,
                    _pad, _entries, _words, _n, _num or nslots (any case), or in TEXT_N (P3 rows excluded)
  P5 record field   `FIELD := NUMERAL` inside `{| .. |}` with FIELD ending in len, num, ent, res, count or size
                    (an optional _z suffix)
  P6 slice          `seg LIST I N` in a file that defines seg
  P7 slice          `firstn N ARG` / `skipn N ARG` with N a numeral
  P8 length         `length EXPR (=|=?|<=|<|>=|>) N`
  P9 extent         `mkRegion None LO (LO + N)`; `mkChunk ADDR (CImg N)`; `(ADDR, N, [` (a read-only cell table)
Donor pairing: a count pairs with the count of the same pattern and the same context (the matched text with its
numerals blanked) that has the same order in the donor file at the same path.

Rules (the rule column states the one applied and its values):
  Code ranges (P1-P3) are read on the twin's function symbols (STT_FUNC; per start address the largest st_size):
    text          PC = .text start: N = .text size / 4 (also TEXT_N definitions, with their TEXT_LO = .text start).
    text-tail     per-name rule of tfibmusl_text_count: N = (.text end - PC) / 4.
    donor structure  the paired donor range, read on cgif's twin as "function S + s to function E + e", must start
                  at a function of the same name S as here; N = (start of E here + e - PC) / 4, with e = E's
                  st_size here when the donor range ends exactly at E's end, else the donor's e. If that differs
                  from the shipped N but the shipped N is the exact cover of whole functions from PC, ending where
                  E starts, and the donor range was its own exact cover plus k words of E: TRUE, note `exact
                  function cover; the donor's +k word(s) not taken`, rule `twin FUNC <name> st_size / 4`.
    no donor range  whole functions: PC is a function start and N = (end of the function holding the last word -
                  PC) / 4; else prefix through the first exit: the range ends right after the first ret / j / jr
                  (jal or jalr with rd = x0) of the function at PC; else the same (PC, N) is an EQUAL donor-structure
                  row of the tree (named in the rule). Else DIFFERS with the whole-functions value.
  Definitions and fields (P4, P5), by name: tfib_A_X / tfib_E_X / tfib_D_X are addresses, not counts: the start /
    end of twin FUNC X / the start of twin OBJECT X (names as the symbol-table generator writes them: non-identifier
    characters as _, a _<k> or _libc suffix, the last identifier of a mangled name); AF_X = twin FUNC X - disco_text;
    RA_X = a return point: the word before it is a `jal ra` to a twin function; tfib_at_rw_len and rw_len = page-
    rounded size of the last PT_LOAD; ph_ent_z / ph_num_z = ELF e_phentsize / e_phnum; cp_size = st_size of the twin
    function at the record's cp_disco. NOT-IMAGE: FS_N = 2^(14 - CID) (ASan FakeStack frames per class), SH_N =
    FS_B / 8, FILL_N = SH_N / 8 (runtime constants, checked against the file's own CID / FS_B / SH_N); A_X used as
    `SOff A_X` (an atom index); BST_SIZE and n_res (runtime constants, checked equal to the cgif file's); DFRAME_SIZE
    (the harness model frame).
  Slices and lengths (P6-P8):
    image regions  in a file that names IMG_REGIONS, IMG_B, IMG_E, IMG_L, IMG_LC, IMG_X or IMG_XL and pairs with a
                  donor file, a count over a region list (ss_mem, IMG_*, *_mem, L_pieces, rs*, PM_*, mem, m) with
                  donor count Kc, R / Rc = the regions of IMG_REGIONS in each tree's AD2j.v: Kc >= Rc reaches past
                  the image block: K = Kc + R - Rc; Kc <= 4: K = Kc (regions in front of the block, or its first
                  regions, same names in both trees); else K = the index here of the region with index Kc in
                  cgif's IMG_REGIONS.
    strings       length of a message = strlen at its img_msg_chk address in the pin (also through a
                  `set (m := if b then X else Y)` alias, both equal); length of (strB "..") = the literal's length,
                  with the check that its bytes occur in the pin.
    trace depth   a trace length bound 30 (29 = 30 - 1) over tr / acc / unwind_of_chain = AF0m.v's const cell at
                  tfib_D_malloc_context_size.
    states        length HS_tfib_list = the number of `Definition HS_tfib_<k> : acs` in the file.
    NOT-IMAGE     seg slices of AB01.v's hand-off state lists (check: I + N <= the sliced list's length, the
                  lengths computed from the file); firstn / skipn 0; sr_atoms indices (check N <= 32); counts in a
                  file that names no image region list (the rule says which: program data model under Prog/, byte
                  library, string / memory routines, allocator / stack model regions, proof-local lists); page
                  bound 4096, the sealed strncpy length, start-up map bounds, line0, harness input offsets.
  Extents (P9): `mkRegion None LO (LO + N)`: N = strlen at LO + 1 in the pin; or = twin OBJECT __stdout_FILE - LO;
    or = the extent of the region's CVal cells, each cell equal to the pin's bytes. AD28.v's CImg = __stdout_FILE -
    ADDR. AD2j.v's CImg chunks are GENERATED: the file header names the pin's sha256 (measured) and the chunk lies
    in its region and in [IMG_LO, IMG_TOP). A read-only cell table's N = the end of its last cell (offset + width).
"""
import argparse, bisect, collections, glob, hashlib, os, re, sys

from elftools.elf.elffile import ELFFile

ap = argparse.ArgumentParser()
for k in ('lib', 'pin', 'twin', 'cgif-lib', 'cgif-pin', 'cgif-twin', 'out'):
    ap.add_argument('--' + k, required=True)
ap.add_argument('--ruling', action='append', default=[])
a = ap.parse_args()
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()


# ------------------------------------------------------------------------------------------------ images
class Image:
    def __init__(self, label, pin, twin):
        self.label, self.pin_sha, self.twin_sha = label, sha(pin), sha(twin)
        self.raw = open(pin, 'rb').read()
        pe = ELFFile(open(pin, 'rb'))
        self.loads = [(s['p_vaddr'], s['p_offset'], s['p_filesz'], s['p_memsz']) for s in pe.iter_segments()
                      if s['p_type'] == 'PT_LOAD']
        self.phnum, self.phentsize = pe.header['e_phnum'], pe.header['e_phentsize']
        self.sec = {s.name: (s['sh_addr'], s['sh_size']) for s in pe.iter_sections() if s.name and s['sh_addr']}
        self.img_lo = self.loads[0][0] & ~0xfff
        self.img_top = (self.loads[-1][0] + self.loads[-1][3] + 0xfff) & ~0xfff
        v, o, fz, mz = self.loads[-1]
        self.rw_len = ((v + mz + 0xfff) & ~0xfff) - (v & ~0xfff)
        te = ELFFile(open(twin, 'rb'))
        twin_raw = open(twin, 'rb').read()
        tl = [(s['p_vaddr'], s['p_offset'], s['p_filesz'], s['p_memsz']) for s in te.iter_segments()
              if s['p_type'] == 'PT_LOAD']
        self.twin_same = (len(tl) == len(self.loads) and all(
            x[0] == y[0] and x[2] == y[2] and x[3] == y[3] for x, y in zip(tl, self.loads)) and all(
            twin_raw[y[1]:y[1] + y[2]] == self.raw[x[1]:x[1] + x[2]] for x, y in zip(self.loads[1:], tl[1:])))
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

    def text(self):
        return self.sec['.text']

    def func_at(self, x):  # the function whose start is the last start <= x
        i = bisect.bisect_right(self.Fst, x) - 1
        return self.F[i] if i >= 0 else None

    def pick(self, name, near):  # the start of the function NAME nearest to `near`
        vs = self.byname.get(name)
        return min(vs, key=lambda v: (abs(v - near), v)) if vs else None

    def word(self, x):
        for v, o, fz, mz in self.loads:
            if v <= x and x + 4 <= v + fz:
                return int.from_bytes(self.raw[o + x - v:o + x - v + 4], 'little')
        return None

    def cstr(self, x):
        for v, o, fz, mz in self.loads:
            if v <= x < v + fz:
                b = self.raw[o + x - v:o + fz]
                return b[:b.index(b'\0')] if b'\0' in b else None
        return None

    def raw_at(self, x, n):  # the pin's file bytes [x, x + n), or None
        for v, o, fz, mz in self.loads:
            if v <= x and x + n <= v + fz:
                return self.raw[o + x - v:o + x - v + n]
        return None

    def contains(self, needle):
        return needle in self.raw

    def sym1(self, name, types=('STT_FUNC', 'STT_OBJECT')):
        s = {(v, sz) for v, sz, t in self.obj.get(name, ()) if t in types}
        return s.pop() if len(s) == 1 else None


D = Image('fuzz_disco.asan', a.pin, a.twin)
C = Image('cgif_file_fuzzer.asan', a.cgif_pin, a.cgif_twin)
for X in (D, C):
    print(f'{X.label}: pin sha256 {X.pin_sha}; twin sha256 {X.twin_sha}; twin PT_LOAD table equal to the pin\'s and '
          f'PT_LOAD 2..{len(X.loads)} bytes equal: {X.twin_same}')
    print(f'{X.label}: .text [{X.text()[0]:#x}, {X.text()[0] + X.text()[1]:#x}) size {X.text()[1]:#x}; '
          f'image [{X.img_lo:#x}, {X.img_top:#x}); RW segment page-rounded size {X.rw_len:#x}; e_phnum {X.phnum}, '
          f'e_phentsize {X.phentsize}; functions {len(X.F)}')
if not (D.twin_same and C.twin_same):
    print('count_recompute: a twin does not match its pin; its symbols cannot describe the pin')
    sys.exit(1)


# ------------------------------------------------------------------------------------------------ trees
def read_tree(root):
    out = {}
    for p in sorted(glob.glob(os.path.join(root, 'A', '**', '*.v'), recursive=True)):
        out[os.path.relpath(p, root)] = open(p).read()
    return out


T, CT = read_tree(a.lib), read_tree(a.cgif_lib)
print(f'files: LIB/A {len(T)}, CGIF_LIB/A {len(CT)}, paired by path {sum(1 for f in T if f in CT)}')
NUM = r'(?:0x[0-9a-fA-F]+|\d+)'


def defs_of(text):
    return {m.group(1): int(m.group(2), 0) for m in
            re.finditer(r'Definition\s+(\w+)\s*:\s*(?:Z|nat|N)\s*:=\s*(' + NUM + r')(?:%nat|%Z)?\s*\.', text)}


def global_defs(tree):
    g = collections.defaultdict(set)
    for t in tree.values():
        for n, v in defs_of(t).items():
            g[n].add(v)
    return {n: v.pop() for n, v in g.items() if len(v) == 1}


GD, CGD = global_defs(T), global_defs(CT)


def resolve(tree_defs, file_defs, name):
    if re.fullmatch(NUM, name):
        return int(name, 0)
    if name in file_defs:
        return file_defs[name]
    return tree_defs.get(name.split('.')[-1])


def regions_list(text):  # the region names of AD2j.v's IMG_REGIONS, in order
    m = re.search(r'Definition IMG_REGIONS\s*:\s*smem\s*:=\s*\[(.*?)\]\.', text, re.S)
    return [x.strip() for x in m.group(1).split(';')] if m else []


RD, RC = regions_list(T.get('A/AD2j.v', '')), regions_list(CT.get('A/AD2j.v', ''))
print(f'IMG_REGIONS in AD2j.v: fuzz_disco {len(RD)} regions, cgif {len(RC)} regions')


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


COUNT_NAME = re.compile(r'(?i)(?:^|_)(?:len|cnt|count|size|bytes|pad|entries|words|n|num|nslots)$|TEXT_N$')
FIELD_NAME = re.compile(r'(?:^|_)(?:len|num|ent|res|count|size)(?:_z)?$')


def bt_names(tree):  # COUNT name -> START name of every `build_table SEGS START COUNT` with two names
    out = {}
    for t in tree.values():
        for m in re.finditer(r'build_table\s+\w+\s+([A-Za-z_][\w.]*)\s+([A-Za-z_][\w.]*)\s', t):
            out.setdefault(m.group(2).split('.')[-1], m.group(1).split('.')[-1])
    return out


def extract(t, gd, btn):
    out, fd = [], defs_of(t)
    for m in re.finditer(r'build_table\s+(\w+)\s+(0x[0-9a-fA-F]+)\s+(\d+)%nat', t):
        out.append(dict(kind='code', line=lineno(t, m.start(3)), pc=int(m.group(2), 16), val=int(m.group(3)),
                        name=f'build_table {m.group(1)} {m.group(2)} {m.group(3)}%nat', ctx='build_table',
                        tok=m.group(2)))
    for m in re.finditer(r'\((0x[0-9a-fA-F]+|[A-Za-z_][\w.]*)\s*,\s*(\d+)%nat\)', t):
        pc = resolve(gd, fd, m.group(1))
        out.append(dict(kind='code', line=lineno(t, m.start(2)), pc=pc, pcname=m.group(1), val=int(m.group(2)),
                        name=f'({m.group(1)}, {m.group(2)}%nat)', ctx='tuple', tok=m.group(1)))
    seen = set()
    for m in re.finditer(r'Definition\s+(\w+)\s*:\s*nat\s*:=\s*(\d+)(?:%nat)?\s*\.', t):
        cn = m.group(1)
        if cn in btn and resolve(gd, fd, btn[cn]) is not None:
            seen.add(cn)
            out.append(dict(kind='codeN', line=lineno(t, m.start(2)), cname=cn, sname=btn[cn],
                            pc=resolve(gd, fd, btn[cn]), val=int(m.group(2)),
                            name=f'{cn} (build_table _ {btn[cn]} {cn})', ctx='codeN ' + cn, tok=cn))
    for m in re.finditer(r'Definition\s+(\w+)\s*:\s*(nat|Z|N)\s*:=\s*(' + NUM + r')(?:%nat)?\s*\.', t):
        if COUNT_NAME.search(m.group(1)) and m.group(1) not in seen:
            out.append(dict(kind='def', line=lineno(t, m.start(3)), val=int(m.group(3), 0), name=m.group(1),
                            ctx='def ' + m.group(1), tok=m.group(1)))
    for m in re.finditer(r'\{\|(.*?)\|\}', t, re.S):
        for g in re.finditer(r'(\w+)\s*:=\s*(' + NUM + r')\b', m.group(1)):
            if FIELD_NAME.search(g.group(1)):
                out.append(dict(kind='field', line=lineno(t, m.start(1) + g.start(2)), val=int(g.group(2), 0),
                                name=g.group(1), rec=m.group(1), ctx='field ' + g.group(1), tok=g.group(1)))
    if re.search(r'Definition seg\b', t):
        for m in re.finditer(r'\bseg\s+(\w+)\s+(\d+)\s+(\d+)', t):
            out.append(dict(kind='seg', line=lineno(t, m.start()), val=int(m.group(3)), i=int(m.group(2)),
                            lst=m.group(1), name=f'seg {m.group(1)} {m.group(2)} {m.group(3)}', ctx='seg',
                            tok=f'seg{m.group(2)}'))
    for m in re.finditer(r'\b(firstn|skipn)\s+(\(?)(\d+)(%nat)?(\)?)', t):
        if m.group(2) and not m.group(5):
            continue
        arg = term_at(t, m.end())
        out.append(dict(kind='slice', line=lineno(t, m.start(3)), val=int(m.group(3)), fn=m.group(1), arg=arg,
                        name=f'{m.group(1)} {m.group(3)} {arg}', ctx=f'{m.group(1)} {norm(arg)}',
                        tok=f'{m.group(1)}{m.group(3)}'))
    for m in re.finditer(r'length\s+(\((?:[^()]|\([^()]*\))*\)|[\w.\']+)\s*(=\??|<=\??|<\??|>=|>)\s*(\d+)(%nat)?', t):
        out.append(dict(kind='length', line=lineno(t, m.start(3)), val=int(m.group(3)), arg=m.group(1),
                        op=m.group(2), name=f'length {m.group(1)} {m.group(2)} {m.group(3)}',
                        ctx=f'length {norm(m.group(1))} {m.group(2)}', tok='len:' + m.group(1)))
    for m in re.finditer(r'mkRegion\s+None\s+(' + NUM + r')\s+\(\s*\1\s*\+\s*(\d+)\s*\)', t):
        i = t.find('[', m.end())
        j = t.find(']', i) if i >= 0 else -1
        out.append(dict(kind='extent', line=lineno(t, m.start(2)), val=int(m.group(2)), lo=int(m.group(1), 0),
                        chunks=t[i:j + 1] if 0 <= i < m.end() + 200 and j > i else '',
                        name=f'mkRegion None {m.group(1)} ({m.group(1)} + {m.group(2)})', ctx='extent',
                        tok='ext' + m.group(1)))
    for m in re.finditer(r'mkChunk\s+(' + NUM + r')\s+\(CImg\s+(\d+)\)', t):
        out.append(dict(kind='cimg', line=lineno(t, m.start(2)), val=int(m.group(2)), lo=int(m.group(1), 0),
                        name=f'mkChunk {m.group(1)} (CImg {m.group(2)})', ctx='cimg', tok='cimg' + m.group(1)))
    for m in re.finditer(r'\((0x[0-9a-fA-F]+),\s*(\d+),\s*\[', t):
        j = t.index(']', m.end())
        cells = [(int(o), int(w)) for o, w in re.findall(r'\((\d+),\s*(\d+)%N,', t[m.end():j])]
        out.append(dict(kind='rotab', line=lineno(t, m.start(2)), val=int(m.group(2)), lo=int(m.group(1), 16),
                        cells=cells, name=f'({m.group(1)}, {m.group(2)}, [..])', ctx='rotab', tok=m.group(1)))
    for i, c in enumerate(out):
        c['pos'] = i
    return out


BTN, CBTN = bt_names(T), bt_names(CT)
EX = {f: extract(t, GD, BTN) for f, t in T.items()}
CEX = {f: extract(t, CGD, CBTN) for f, t in CT.items()}
_REG = {}


def REGIONS_OF(f):  # (lo, hi, first line, last line, chunk text) of every literal `mkRegion None LO HI _ _ [..]` of f
    if f not in _REG:
        t = T[f]
        _REG[f] = [(int(m.group(1)), int(m.group(2)), lineno(t, m.start()), lineno(t, m.end()), m.group(3))
                   for m in re.finditer(r'mkRegion None (\d+) (\d+) \d+ \d+\s*\[([^\]]*)\]', t)]
    return _REG[f]


def pair(f):  # donor counterpart of each count: same kind and context, same ordinal in the file
    res = {}
    if f not in CEX:
        return res
    od, oc = collections.defaultdict(list), collections.defaultdict(list)
    for c in sorted(EX[f], key=lambda c: (c['line'], c['pos'])):
        od[(c['kind'], c['ctx'])].append(c)
    for c in sorted(CEX[f], key=lambda c: (c['line'], c['pos'])):
        oc[(c['kind'], c['ctx'])].append(c)
    for k, l in od.items():
        for i, c in enumerate(l):
            if i < len(oc.get(k, [])):
                res[id(c)] = oc[k][i]
    return res


# ------------------------------------------------------------------------------------------------ code-range rules
def is_exit(w):
    return w is not None and (w & 0x7f) in (0x6f, 0x67) and ((w >> 7) & 31) == 0


def desc(X, pc, n):  # (start fn, offset), (end fn start, end offset, end fn size), on X's twin
    fs, fe = X.func_at(pc), X.func_at(pc + 4 * n - 4)
    if not fs or not fe or pc - fs[0] >= max(fs[1], 4) and fs[1] or pc + 4 * n - fe[0] > fe[1]:
        return None
    return (fs[2], pc - fs[0]), (fe[2], pc + 4 * n - fe[0], fe[1], fe[0])


def whole_cover(X, pc, n):  # (end of the function holding the last word - pc) / 4
    fe = X.func_at(pc + 4 * n - 4)
    fs = X.func_at(pc)
    if not fe or not fs or fs[0] != pc:
        return None, None
    return (fe[0] + fe[1] - pc) // 4, fe[2]


def first_exit(X, pc):
    fs = X.func_at(pc)
    if not fs or fs[0] != pc:
        return None
    for x in range(pc, pc + fs[1], 4):
        if is_exit(X.word(x)):
            return (x + 4 - pc) // 4
    return None


def code_rule(c, dc, f):
    pc, n = c['pc'], c['val']
    if pc is None:
        return None
    dpc, dn = (dc['pc'], dc['val']) if dc and dc.get('pc') is not None else (None, None)
    tlo, tsz = D.text()
    if c.get('rulename') == 'text-tail':
        rec = (tlo + tsz - pc) // 4
        drec = (C.text()[0] + C.text()[1] - dpc) // 4 if dpc is not None else None
        return (f'text-tail: (.text end {tlo + tsz:#x} - start {pc:#x}) / 4', rec, dn, drec,
                'EQUAL' if rec == n else 'DIFFERS', '')
    if pc == tlo:
        drec = C.text()[1] // 4
        return (f'text: start = .text start {tlo:#x}, N = .text size {tsz:#x} / 4', tsz // 4, dn, drec,
                'EQUAL' if tsz // 4 == n else 'DIFFERS', '')
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
                    rule = (f'donor structure: cgif range {dpc:#x} + 4*{dn} = {sn} + {so} {how}; '
                            f'here (twin {en} {ve:#x}' + (f' + {eo}' if eo != esz else f' + st_size {sz}') +
                            f' - {pc:#x}) / 4')
                    if rec == n:
                        return rule, rec, dn, dn, 'EQUAL', ''
                    # TRUE: the shipped count is fuzz_disco's exact cover of whole functions and the donor's range
                    # was its own exact cover plus k words into the next function
                    wc, wn = whole_cover(D, pc, n)
                    if eo != esz and eo % 4 == 0 and wc == n and pc + 4 * n == ve and C.func_at(est - 4)[0] + \
                            C.func_at(est - 4)[1] == est:
                        k = eo // 4
                        return (f'exact function cover: twin FUNC {wn} st_size / 4 (whole functions from {pc:#x}); '
                                f'the donor range = its own exact cover (to the start of {en}) plus {k} word(s) of {en}',
                                n, dn, dn - k, 'TRUE', f"exact function cover; the donor's +{k} word(s) not taken")
                    return rule, rec, dn, dn, 'DIFFERS', ''
    wc, wn = whole_cover(D, pc, n)
    if wc == n:
        fs = D.func_at(pc)
        return (f'whole functions (twin, no donor range): {fs[2]} .. {wn}: (end of {wn} - {pc:#x}) / 4', wc, dn,
                None, 'EQUAL', '')
    fx = first_exit(D, pc)
    if fx == n:
        return (f'prefix through the first exit (twin, no donor range): {D.fname[pc]} from {pc:#x} through its first '
                f'ret / j / jr at {pc + 4 * n - 4:#x}', fx, dn, None, 'EQUAL', '')
    sib = SIBLING.get((pc, n))
    if sib:
        fs = D.func_at(pc)
        return (f'prefix of {fs[2]} + {pc - fs[0]} to + {pc + 4 * n - fs[0]} (twin, no donor range): the same range '
                f'as {sib}, recomputed there by the donor structure rule', n, dn, None, 'EQUAL', '')
    return (f'whole functions (twin, no donor range): (end of the function holding the last word - {pc:#x}) / 4',
            wc, dn, None, 'DIFFERS', '')


# ------------------------------------------------------------------------------------------------ named rules
IMGLIST = re.compile(r'\b(IMG_REGIONS|IMG_B|IMG_E|IMG_L|IMG_LC|IMG_X|IMG_XL)\b')
REGLIST = re.compile(r'ss_mem|\bIMG_\w+|_mem\b|L_pieces|\brs_\w+|\brs[A-Z]\w*|PM_\w+|\bmem\b|^m$')


def cell(addr):  # AF0m.v's const cell value at addr (width 4 or 8), or None
    m = re.findall(r'z[48] \(ANum %s\) (0x[0-9a-fA-F]+|\d+)' % hex(addr), T.get('A/AF0m.v', ''))
    return int(m[0], 0) if len(m) == 1 else None


def last_ident(n):  # the last source identifier of an Itanium-mangled name (_ZN6__asanL19malloc_context_sizeE)
    ids = re.findall(r'(\d+)', n)
    out, i = None, 0
    if n.startswith('_Z'):
        i = 2
        while i < len(n):
            m = re.match(r'(\d+)', n[i:])
            if m:
                k = int(m.group(1))
                s = i + len(m.group(1))
                out = n[s:s + k]
                i = s + k
            else:
                i += 1
    return out if ids else None


def sym_addr(X, kind, name):  # gen_symtab's naming: non-identifier characters as _, a _<k> / _libc suffix
    san = lambda n: re.sub(r'[^A-Za-z0-9_]', '_', n)
    cands = {name, re.sub(r'_\d+$', '', name), re.sub(r'_libc$', '', name)}
    out = set()
    for n, v, sz, t in X.syms:
        if kind in 'AE' and t == 'STT_FUNC' and san(n) in cands:
            out.add(v if kind == 'A' else (v + sz if sz else X.Fst[bisect.bisect_right(X.Fst, v)]))
        elif kind == 'D' and t == 'STT_OBJECT' and (san(n) in cands or last_ident(n) in cands):
            out.add(v)
    return out


def jal_target(X, ret):  # the target of the jal ra just before `ret`, or None
    w = X.word(ret - 4)
    if w is None or (w & 0x7f) != 0x6f or ((w >> 7) & 31) != 1:
        return None
    imm = ((w >> 31) & 1) << 20 | ((w >> 12) & 0xff) << 12 | ((w >> 20) & 1) << 11 | ((w >> 21) & 0x3ff) << 1
    return ret - 4 + (imm - (1 << 21) if imm >> 20 else imm)


def def_rule(c, dc, f):
    nm, v = c['name'], c['val']
    dv = dc['val'] if dc else None
    m = re.match(r'tfib_([AED])_(\w+)$', nm)
    if m:
        s = sym_addr(D, m.group(1), m.group(2))
        what = {'A': 'st_value', 'E': 'st_value + st_size', 'D': 'st_value (OBJECT)'}[m.group(1)]
        ds = sym_addr(C, m.group(1), m.group(2))
        return (f'an address, not a count: twin FUNC/OBJECT {m.group(2)} {what}', v if v in s else min(s, default=None),
                dv, (dv if dv in ds else min(ds, default=None)), 'EQUAL' if v in s else 'DIFFERS', '')
    if nm == 'tfib_at_rw_len':
        return ('RW segment length: page-rounded size of the last PT_LOAD', D.rw_len, dv, C.rw_len,
                'EQUAL' if v == D.rw_len else 'DIFFERS', '')
    m = re.match(r'AF_(\w+)$', nm)
    if m:
        base = GD.get('disco_text')
        s = D.sym1(m.group(1), ('STT_FUNC',))
        rec = s[0] - base if s and base is not None else None
        return (f'an offset, not a count: twin FUNC {m.group(1)} st_value - disco_text {base:#x}', rec, dv, None,
                'EQUAL' if rec == v else 'DIFFERS', '')
    if nm.startswith('RA_'):
        tg = jal_target(D, v)
        ok = tg is not None and tg in D.fname
        fs = D.func_at(v)
        return ((f'an address, not a count: the return point in twin FUNC {fs[2]} after `jal ra, {D.fname[tg]}` '
                 f'({tg:#x}) at {v - 4:#x}') if ok else 'an address, not a count: no `jal ra` to a function before it',
                v if ok else None, dv, None, 'EQUAL' if ok else 'DIFFERS', '')
    if nm.endswith('TEXT_N'):
        lo = defs_of(T[f]).get(nm[:-1] + 'LO')
        tlo, tsz = D.text()
        ok = lo == tlo
        return (f'text: {nm[:-1]}LO = .text start {tlo:#x} ({ok}), N = .text size {tsz:#x} / 4', tsz // 4, dv,
                C.text()[1] // 4, 'EQUAL' if ok and v == tsz // 4 else 'DIFFERS', '')
    fd = defs_of(T[f])
    if nm == 'FS_N' and 'CID' in fd:
        ok = v == 2 ** (14 - fd['CID'])
        return (f'NOT-IMAGE: ASan FakeStack frames of class CID={fd["CID"]}: 2^(14 - CID) (runtime constant)',
                2 ** (14 - fd['CID']), dv, None, 'NOT-IMAGE' if ok else 'DIFFERS', '')
    if nm == 'SH_N' and 'FS_B' in fd:
        ok = v == fd['FS_B'] // 8
        return ('NOT-IMAGE: shadow bytes of one fake frame: FS_B / 8 (runtime constant)', fd['FS_B'] // 8, dv, None,
                'NOT-IMAGE' if ok else 'DIFFERS', '')
    if nm == 'FILL_N' and 'SH_N' in fd:
        ok = v == fd['SH_N'] // 8
        return ('NOT-IMAGE: 8-byte shadow stores of one fake frame: SH_N / 8 (runtime constant)', fd['SH_N'] // 8,
                dv, None, 'NOT-IMAGE' if ok else 'DIFFERS', '')
    if re.fullmatch(r'A_\w+', nm) and re.search(r'SOff ' + nm + r'\b', T[f]):
        return ('NOT-IMAGE: a symbolic atom index (used as SOff ' + nm + ' in the file), not a count', v, dv, None,
                'NOT-IMAGE', '')
    if nm == 'BST_SIZE':
        return ('NOT-IMAGE: sizeof(__sanitizer::BufferedStackTrace) of the runtime both images link; check: the '
                'cgif file has the same value', v if dv == v else None, dv, None,
                'NOT-IMAGE' if dv == v else 'DIFFERS', '')
    if nm == 'DFRAME_SIZE':
        return ('NOT-IMAGE: the frame size of the harness model region (a proof constant); check: used only as the '
                'high bound of that region in the file', v, dv, None, 'NOT-IMAGE', '')
    return None


def field_rule(c, dc, f):
    nm, v = c['name'], c['val']
    dv = dc['val'] if dc else None
    if nm == 'rw_len':
        return ('RW segment length: page-rounded size of the last PT_LOAD', D.rw_len, dv, C.rw_len,
                'EQUAL' if v == D.rw_len else 'DIFFERS', '')
    if nm == 'ph_ent_z':
        return ('ELF header e_phentsize of the pin', D.phentsize, dv, C.phentsize,
                'EQUAL' if v == D.phentsize else 'DIFFERS', '')
    if nm == 'ph_num_z':
        return ('ELF header e_phnum of the pin', D.phnum, dv, C.phnum, 'EQUAL' if v == D.phnum else 'DIFFERS', '')
    if nm == 'n_res':
        return ('NOT-IMAGE: the start-up\'s reserved mappings of the runtime (n_res, added to the map count); check: '
                'the cgif file has the same value', v if dv == v else None, dv, None,
                'NOT-IMAGE' if dv == v else 'DIFFERS', '')
    if nm == 'cp_size':
        m = re.search(r'cp_disco\s*:=\s*(' + NUM + ')', c['rec'])
        x = int(m.group(1), 0) if m else None
        fs = D.func_at(x) if x is not None else None
        rec = fs[1] if fs and fs[0] == x else None
        return (f'twin FUNC at cp_disco {x:#x} ({fs[2] if fs else "-"}) st_size', rec, dv, None,
                'EQUAL' if rec == v else 'DIFFERS', '')
    return None


def ab01_lengths():  # length of each list Definition of AB01.v: literal lists and ++ of seg slices
    t = T.get('A/AB01.v', '')
    L = {}
    for m in re.finditer(r'Definition (\w+) : list kentry :=\s*(.*?)\.\n', t, re.S):
        n = 0
        for part in split_top(m.group(2), '++'):
            part = part.strip()
            s = re.fullmatch(r'seg (\w+) (\d+) (\d+)', part)
            if s:
                n += max(0, min(int(s.group(3)), L.get(s.group(1), 0) - int(s.group(2))))
            elif part.startswith('['):
                n += len([x for x in split_top(part[1:-1], ';') if x.strip()])
        L[m.group(1)] = n
    return L


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


AB01L = ab01_lengths()


def imgreg_rule(c, dc):  # a count in a symbolic memory region list that holds IMG_REGIONS
    if not dc:
        return None
    kc, k = dc['val'], c['val']
    R, Rc = len(RD), len(RC)
    if kc >= Rc:
        rec = kc + R - Rc
        return (f'image regions: reaches past the image block: cgif {kc} + (regions {R} - {Rc})', rec, kc, kc,
                'EQUAL' if rec == k else 'DIFFERS', '')
    if kc <= 4:
        return (f'image regions: {kc} region(s) in front of the image block or at its start (same names in both '
                f'trees): cgif {kc}', kc, kc, kc, 'EQUAL' if kc == k else 'DIFFERS', '')
    nm = RC[kc]
    rec = RD.index(nm) if nm in RD else None
    return (f'image regions: index of {nm} in AD2j IMG_REGIONS (cgif index {kc})', rec, kc, kc,
            'EQUAL' if rec == k else 'DIFFERS', '')


def slice_len_rule(c, dc, f):
    t, v = T[f], c['val']
    arg = c.get('arg', '')
    dv = dc['val'] if dc else None
    if c['kind'] == 'seg':
        L = AB01L.get(c['lst'])
        ok = L is not None and c['i'] + v <= L
        return (f'NOT-IMAGE: a slice of the collector hand-off state list {c["lst"]} (length {L}); check: '
                f'{c["i"]} + {v} <= {L}', v if ok else None, dv, None, 'NOT-IMAGE' if ok else 'DIFFERS', '')
    if c['kind'] == 'length':
        al = re.search(r'set \(' + re.escape(arg) + r' := if \w+ then (\w+) else (\w+)\)', t)
        names = [al.group(1), al.group(2)] if al else [arg]
        adr = [re.search(r'img_msg_chk (0x[0-9a-fA-F]+) ' + re.escape(x) + r'\b', t) for x in names]
        if all(adr):
            ls = {len(D.cstr(int(m.group(1), 16)) or b'') for m in adr}
            rec = ls.pop() if len(ls) == 1 else None
            return (f'string length in the pin: strlen at the img_msg_chk address of ' +
                    ' / '.join(f'{x} ({m.group(1)})' for x, m in zip(names, adr)), rec, dv, None,
                    'EQUAL' if rec == v else 'DIFFERS', '')
        m = re.fullmatch(r'\(strB "([^"]*)"%string( \+\+ nlB)?\)', arg)
        if m:
            s = m.group(1).encode() + (b'\n' if m.group(2) else b'')
            ok = D.contains(s)
            return (f'string literal length {len(s)}; check: the bytes occur in the pin: {ok}', len(s), dv, None,
                    'EQUAL' if ok and len(s) == v else 'DIFFERS', '')
        if arg == 'nlB':
            return ('NOT-IMAGE: one newline byte', 1, dv, None, 'NOT-IMAGE' if v == 1 else 'DIFFERS', '')
        if arg == 'HS_tfib_list':
            n = len(re.findall(r'Definition HS_tfib_\d+ : acs', t))
            return (f'the collector hand-off states: Definitions HS_tfib_<k> : acs in the file ({n})', n, dv, None,
                    'EQUAL' if n == v else 'DIFFERS', '')
    if re.search(r'\btr\b|\bacc\b|unwind_of_chain', arg) and v in (29, 30) and c['kind'] in ('length', 'slice'):
        mc = GD.get('tfib_D_malloc_context_size')
        cv = cell(mc) if mc is not None else None
        return (f'stack trace depth malloc_context_size: AF0m.v const cell at tfib_D_malloc_context_size {mc:#x} = '
                f'{cv}' + (' (minus the frame added after the check)' if v == 29 else ''),
                cv - (30 - v) if cv else None, dv, None,
                'EQUAL' if cv is not None and cv - (30 - v) == v else 'DIFFERS', '')
    if c['kind'] == 'slice' and v == 0:
        return ('NOT-IMAGE: firstn / skipn 0 (the empty or the whole list, a proof step)', 0, dv, None, 'NOT-IMAGE',
                '')
    if c['kind'] == 'slice' and re.search(r'\bsr_atoms\b', arg):
        return ('NOT-IMAGE: index into the 32 symbolic register atoms; check: N <= 32', v if v <= 32 else None, dv,
                None, 'NOT-IMAGE' if v <= 32 else 'DIFFERS', '')
    img_file = IMGLIST.search(t) is not None
    if img_file and f in CT and REGLIST.search(arg) and not re.search(r'\b(data|p|bs|buf|src|cs)\b', arg):
        r = imgreg_rule(c, dc)
        if r:
            return r
    if not img_file:
        for rx, what in NOTIMAGE:
            if re.search(rx, f + ' ' + c['name']):
                return (f'NOT-IMAGE: {what}; check: the file names no image region list (IMG_REGIONS / IMG_B / '
                        f'IMG_E / IMG_L / IMG_LC / IMG_X)', v, dv, None, 'NOT-IMAGE', '')
    for rx, what in NOTIMAGE_ANY:
        if re.search(rx, f + ' ' + c['name']):
            return (f'NOT-IMAGE: {what}', v, dv, None, 'NOT-IMAGE', '')
    return None


# (file + matched text regex, what the count counts): counts in files that name no image region list
NOTIMAGE = [
    (r'^A/Prog/', 'a byte offset / length / index in the C objects of the harness and libreac (program data model)'),
    (r'^A/(Bz|Strw|Spec)/', 'a byte count of the byte / word library lemmas (word widths, string scans)'),
    (r'^A/(FM|R_|RT_|Rt/)', 'a byte count of the string / memory routine lemmas (word widths, buffers)'),
    (r'(REG0|ss_mem|TBLS|st_regions|st_cache|MREG0|MKREG0|SREG0|REG0U\d|R3_U|RU_\d|B_Q|fB\b|S_TE0|ss_mem S_N)',
     'a region of the allocator / stack model of a symbolic state (no image region in the list)'),
    (r'(\bl\b|\bl\)|length l\)|\(l\)|xs\)|ws\)|bs\)|src\)|\bbs\b|chunk|\bw\b|word_to_le_bytes|qc_list|TOPS|'
     r'skipn \(i \+ p\) bs|junk|\bacc|\btr\b|unwind_of_chain|seq)', 'a proof-local list (bytes of a word, a scan '
     'buffer, a trace or queue bound of the runtime model)'),
]
# (regex, what) for counts in any file
NOTIMAGE_ANY = [
    (r'length p < 4096|firstn 4096 p', 'the 4096-byte page / path bound of the loader\'s string reads'),
    (r'strncpy_sealed_bytes', 'the strncpy length argument 4095 of the sealed copy (8 sealed bytes + 4087 zeros, '
     'the file\'s own definition)'),
    (r'length \(?musl_maps ch\)? <=|length fog <=|length extra <=', 'a bound on the start-up\'s anonymous maps / '
     'holes of the runtime model'),
    (r'length line0 = 2', 'the two bytes "0\\n" of an output line (line0 = [48; 10] in the proof)'),
    (r'firstn 4096 p|length \(firstn 4096 p\)', 'the 4096-byte page bound of a string read'),
    (r'\bdata\b|config_len', 'an offset in the harness input bytes'),
    (r'\ba_maps\b', 'the start-up\'s map list (the first 3 maps are the runtime\'s reservations, the model\'s own '
     'layout)'),
    (r'(firstn|skipn) \d+ \(?(ss_mem (MS_AC|H518|MK_AC|K518|MS_CALL|MK_CALL|MS_F|SS_F|MK_F|KS_F))',
     'a region of the allocator model state (stack window and allocator regions)'),
]


def extent_rule(c, dc, f):
    v = c['val']
    dv = dc['val'] if dc else None
    if c['kind'] == 'extent':
        s = D.cstr(c['lo'])
        if s is not None and len(s) + 1 == v:
            return (f'string region: strlen at {c["lo"]:#x} + 1 (the NUL) in the pin', len(s) + 1, dv, None, 'EQUAL',
                    '')
        so = D.sym1('__stdout_FILE', ('STT_OBJECT',))
        if so and so[0] - c['lo'] == v:
            return (f'region clipped at the stdout FILE: twin OBJECT __stdout_FILE {so[0]:#x} - {c["lo"]:#x}',
                    so[0] - c['lo'], dv, None, 'EQUAL', '')
        cells = re.findall(r'mkChunk\s+(' + NUM + r')\s+\(CVal\s+(\d+)\s+\(SLit\s+(' + NUM + r')\)\)', c['chunks'])
        cells = [(int(x, 0), int(w), int(y, 0)) for x, w, y in cells]
        pos, ok = c['lo'], bool(cells)
        for x, w, y in cells:
            b = D.raw_at(x, w)
            ok = ok and x == pos and b is not None and int.from_bytes(b, 'little') == y
            pos = x + w
        if ok:
            return (f'object cells: the region is its cells [{c["lo"]:#x}, {pos:#x}), each cell equal to the pin\'s '
                    f'bytes', pos - c['lo'], dv, None, 'EQUAL' if pos - c['lo'] == v else 'DIFFERS', '')
        return ('string / object region: no rule reproduces it', None, dv, None, 'DIFFERS', '')
    if c['kind'] == 'cimg':
        if f == 'A/AD28.v':
            so = D.sym1('__stdout_FILE', ('STT_OBJECT',))
            rec = so[0] - c['lo'] if so else None
            return (f'region clipped at the stdout FILE: twin OBJECT __stdout_FILE {so[0]:#x} - {c["lo"]:#x}', rec,
                    dv, None, 'EQUAL' if rec == v else 'DIFFERS', '')
        gen = D.pin_sha in '\n'.join(T[f].split('\n')[:8])
        reg = None
        for lo, hi, l0, l1, chunks in REGIONS_OF(f):
            if l0 <= c['line'] <= l1 and ('mkChunk %d (CImg %d)' % (c['lo'], v)) in chunks:
                reg = (lo, hi)
        ok = gen and reg is not None and reg[0] <= c['lo'] and c['lo'] + v <= reg[1] and D.img_lo <= c['lo'] and \
            c['lo'] + v <= D.img_top
        return (f'generated from the pin by the start-up generator (the header names the pin sha256: {gen}); check: '
                f'[{c["lo"]:#x}, {c["lo"] + v:#x}) in its region ' + (f'[{reg[0]:#x}, {reg[1]:#x})' if reg else '-') +
                ' and in the image', v if ok else None, dv, None, 'GENERATED' if ok else 'DIFFERS', '')
    if c['kind'] == 'rotab':
        end = max((o + w for o, w in c['cells']), default=None)
        return ('read-only cell table: the end of its last cell (offset + width)', end, dv, None,
                'EQUAL' if end == v else 'DIFFERS', '')
    return None


# ------------------------------------------------------------------------------------------------ apply
RULE_NAME = {'tfibmusl_text_count': 'text-tail'}
rows = []
pairs = {f: pair(f) for f in T}
# code ranges first: the donor-structure rows give the sibling table for ranges with no donor range
SIBLING = {}
CODE = []
for f in sorted(T):
    for c in EX[f]:
        if c['kind'] in ('code', 'codeN'):
            if c['kind'] == 'codeN':
                c['rulename'] = RULE_NAME.get(c['cname'])
            CODE.append((f, c))
SIBLING_PASS = []
for f, c in CODE:
    dc = pairs[f].get(id(c))
    r = code_rule(c, dc, f) if c['pc'] is not None else None
    SIBLING_PASS.append((f, c, dc, r))
    if r and r[4] == 'EQUAL' and r[0].startswith('donor structure'):
        SIBLING.setdefault((c['pc'], c['val']), f'{f}:{c["line"]}')
for f, c, dc, r in SIBLING_PASS:
    if r and r[4] == 'DIFFERS' and r[0].startswith('whole functions'):
        r = code_rule(c, dc, f)
    rows.append((f, c, dc, r))
for f in sorted(T):
    for c in EX[f]:
        if c['kind'] in ('code', 'codeN'):
            continue
        dc = pairs[f].get(id(c))
        if c['kind'] == 'def':
            r = def_rule(c, dc, f)
        elif c['kind'] == 'field':
            r = field_rule(c, dc, f)
        elif c['kind'] in ('seg', 'slice', 'length'):
            r = slice_len_rule(c, dc, f)
        else:
            r = extent_rule(c, dc, f)
        rows.append((f, c, dc, r))

# keys: FILE:LINE, plus :TOKEN when the line holds more than one counted item
per_line = collections.Counter((f, c['line']) for f, c, _, _ in rows)
fmt = lambda x: '-' if x is None else str(x)
one = lambda s: re.sub(r'\s+', ' ', s).strip()
out = []
for f, c, dc, r in rows:
    key = f'{f}:{c["line"]}' + (f':{one(c["tok"])}' if per_line[(f, c['line'])] > 1 else '')
    if r is None:
        r = ('no rule', None, dc['val'] if dc else None, None, 'UNRULED', '')
    rule, rec, dship, drec, status, note = r
    out.append([key, one(c['name']), fmt(c['val']), one(rule), fmt(rec), fmt(dship), fmt(drec), status, note, '',
                c['kind'], c['pos']])
keys = collections.Counter(o[0] for o in out)
for k in sorted(k for k, n in keys.items() if n > 1):  # one token twice on a line: number them in text order
    i = 0
    for o in sorted((o for o in out if o[0] == k), key=lambda o: o[11]):
        i += 1
        o[0] = f'{k}#{i}'

bad = []
rulings = {}
for r in a.ruling:
    k, sep, txt = r.partition('=')
    if not sep:
        bad.append(f'--ruling without =: {r}')
        continue
    rulings[k] = txt
for k, txt in sorted(rulings.items()):
    hit = [o for o in out if o[0] == k and o[7] == 'DIFFERS']
    if not hit:
        bad.append(f'--ruling {k} matches no DIFFERS row')
    for o in hit:
        o[9] = one(txt)


def sort_key(o):
    f, rest = o[0].split(':', 1)
    ln = re.match(r'\d+', rest).group(0)
    return f, int(ln), o[0]


out.sort(key=sort_key)
with open(a.out, 'w') as fh:
    fh.write('\t'.join(['key', 'name/call', 'shipped', 'rule', 'recomputed', 'donor shipped', 'donor recomputed',
                        'status', 'note', 'ruling']) + '\n')
    for o in out:
        fh.write('\t'.join(o[:10]) + '\n')

st = collections.Counter(o[7] for o in out)
for (k, s), n in sorted(collections.Counter((o[10], o[7]) for o in out).items()):
    print(f'pattern {k}\tstatus {s}\t{n}')
for s in sorted(st):
    print(f'status {s}\t{st[s]}')
dif = [o for o in out if o[7] == 'DIFFERS']
ruled = sum(1 for o in dif if o[9])
print(f'rows {len(out)}; DIFFERS {len(dif)} (ruled {ruled}, unruled {len(dif) - ruled}); UNRULED {st["UNRULED"]}; '
      f'TRUE {st["TRUE"]}')
for o in out:
    if o[7] in ('DIFFERS', 'TRUE'):
        print(o[7] + '\t' + '\t'.join(o[:7]) + ('\t' + o[8] if o[8] else '') + ('\truling: ' + o[9] if o[9] else ''))
for o in out:
    if o[7] == 'UNRULED':
        print('UNRULED\t' + '\t'.join(o[:3]))
for b in bad:
    print('count_recompute: ' + b)
sys.exit(1 if bad or st['UNRULED'] or len(dif) > ruled else 0)
