#!/usr/bin/env python3
"""addr_triage.py -- triage EVERY flagged row of a port_addr_check run over lib/A (image A, fuzz_disco.asan).

Reads the checker's row TSV and the flag classes the checker itself prints (`--list-flag-classes`), and gives each
flagged row one triage class, `right` or `DEFECT`, and a per-row detail. A class is a rule; every rule that names a
property of the image MEASURES it here (from the pin, its unstripped twin, cgif's symbol list, or the checked files)
before any row is given that class, and the measurement is printed. Rows no rule covers must be named in the hand table
(HAND, one row per flagged row or group of identical rows, each with a `check` expression evaluated here); a hand row
that matches no flagged row, a failed check, or a flagged row left with no class is a refusal (exit 1).

Usage: addr_triage.py --rows ROWS.tsv --flags FLAGS.txt --lib LIB --cgif-lib CGIF_LIB --pin PIN --twin TWIN
                      --cgif-nm NM --hand HAND.tsv --out TRIAGE.tsv [--also MOVED.tsv]
  ROWS.tsv   the checker's --out table      FLAGS.txt  the checker's --list-flag-classes output
  LIB        the checked tree (BASE:proofs/libreac/fuzz_disco/lib; gate 10: SERIES:proofs/libreac/fuzz_disco/lib)
  CGIF_LIB   the donor tree (cgif's released lib)    PIN / TWIN image A and its unstripped twin
  NM         cgif asan's symbol list (nm text)    HAND.tsv  the hand rows (hand-triage.tsv beside this script;
             gate 10: hand-triage-series.tsv)
  MOVED.tsv  optional: rows whose verdict moved from an older checker version (run_diff.py --moved-out); each one
             that is not a finding is triaged too, by the same rules, and appended to TRIAGE.tsv
"""
import argparse, bisect, collections, csv, hashlib, os, re, struct, sys

from elftools.elf.elffile import ELFFile

ap = argparse.ArgumentParser()
for k in ('rows', 'flags', 'lib', 'cgif-lib', 'pin', 'twin', 'cgif-nm', 'hand', 'out'):
    ap.add_argument('--' + k, required=True)
ap.add_argument('--also')
a = ap.parse_args()
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
print(f'pin sha256 {sha(a.pin)}; twin sha256 {sha(a.twin)}; cgif symbol list sha256 {sha(a.cgif_nm)}')

# ------------------------------------------------------------------------------------------------ the checker's rows
FLAGS = {l.strip() for l in open(a.flags) if l.strip()}
rows = list(csv.DictReader((l for l in open(a.rows) if not l.startswith('#')), delimiter='\t'))
fl = [r for r in rows if r['verdict'] in FLAGS]
fkey = lambda r: r['dst_file'] or r['src_file']
print(f'checker rows {len(rows)}; flag classes {len(FLAGS)}; flagged rows {len(fl)}')

# ------------------------------------------------------------------------------------------------ image facts
pin_raw = open(a.pin, 'rb').read()
pe = ELFFile(open(a.pin, 'rb'))
loads = [s for s in pe.iter_segments() if s['p_type'] == 'PT_LOAD']
SEG = [(s['p_vaddr'] & ~0xfff, (s['p_vaddr'] + s['p_memsz'] + 0xfff) & ~0xfff) for s in loads]
SEG = [(lo, hi, hi - lo) for lo, hi in SEG]
TOP = SEG[-1][1]
SEC = {s.name: (s['sh_addr'], s['sh_addr'] + s['sh_size']) for s in pe.iter_sections() if s.name}
print('page-rounded segments: ' + ', '.join(f'[{lo:#x}, {hi:#x}) size {sz:#x}' for lo, hi, sz in SEG) + f'; IMG_TOP {TOP:#x}')


def filebytes(addr, n):
    for s in loads:
        if s['p_vaddr'] <= addr and addr + n <= s['p_vaddr'] + s['p_filesz']:
            o = s['p_offset'] + addr - s['p_vaddr']
            return pin_raw[o:o + n]
    return None


te = ELFFile(open(a.twin, 'rb'))
SYMS = collections.defaultdict(list)
FUNCS = []
for s in te.get_section_by_name('.symtab').iter_symbols():
    if s.name:
        SYMS[s.name].append((s['st_value'], s['st_size']))
        if s['st_info']['type'] == 'STT_FUNC':
            FUNCS.append((s['st_value'], s['st_size'], s.name))
CSYMS = {}
for l in open(a.cgif_nm):
    p = l.split()
    if len(p) >= 4 and not l.startswith('#'):
        CSYMS.setdefault(p[3], int(p[0], 16))


def sym(n):
    v = {x for x, _ in SYMS[n]}
    assert len(v) == 1, f'{n}: {len(v)} addresses in the twin'
    return v.pop()


csym = lambda n: CSYMS[n]
text = lambda f: open(os.path.join(a.lib, f)).read()
AF0M = text('A/AF0m.v')
AF0M_DEFS = {n: int(v, 0) for n, v in re.findall(r'Definition (\w+) : Z := (0x[0-9a-fA-F]+|\d+)\.', AF0M)}
af0m = lambda n: AF0M_DEFS[n]


def af0m_cell(addr, w):
    m = re.findall(r'z%d \(ANum %s\) (0x[0-9a-fA-F]+|\d+)' % (w, hex(addr)), AF0M)
    return int(m[0], 0) if len(m) == 1 else None


def regions():   # the number of regions in AD2j.v's IMG_REGIONS list, each one a mkRegion definition of the file
    t = text('A/AD2j.v')
    i = t.index('Definition IMG_REGIONS'); j = t.index('].', i)
    names = [x.strip() for x in t[t.index('[', i) + 1:j].split(';') if x.strip()]
    assert all(re.search(r'Definition %s\b[^.]*:=\s*mkRegion' % re.escape(n), t) for n in names), 'a region is no mkRegion'
    return len(names)


def word(addr):
    b = filebytes(addr, 4)
    return int.from_bytes(b, 'little') if b else None


def jal_imm(w):   # the raw 21-bit J-type immediate field, as decode_any reports it
    return ((w >> 31) & 1) << 20 | ((w >> 12) & 0xff) << 12 | ((w >> 20) & 1) << 11 | ((w >> 21) & 0x3ff) << 1


def has(f, s, side='dst'):   # the checked file (dst) or cgif's own file (src) holds the text s
    return s in (text(f) if side == 'dst' else open(os.path.join(a.cgif_lib, f)).read())


seg = lambda i: SEG[i]
sec = lambda n: SEC[n]

# ------------------------------------------------------------------------------------------------ block measurements
MEAS = {}

# (1) AB1w.v: every tfib_A_<n> / tfib_E_<n> is the start / end of a FUNC symbol of the twin named n, read with
#     gen_symtab's naming (non-identifier characters as `_`, a repeated name with a _<k> suffix, a reused libc name with a
#     _libc suffix, a zero-size symbol ending at the next function start); the section rows are the section bounds.
san = lambda n: re.sub(r'[^A-Za-z0-9_]', '_', n)
BYNAME = collections.defaultdict(set)
for x, sz, n in FUNCS:
    BYNAME[san(n)].add((x, sz))
STARTS = sorted({x for x, _, _ in FUNCS})
nxt = lambda x: STARTS[bisect.bisect_right(STARTS, x)]
SECROW = {'rodata': '.rodata', 'text': '.text', 'init_array': '.init_array', 'fini_array': '.fini_array',
          'preinit_array': '.preinit_array', 'data_rel_ro': '.data.rel.ro', 'got': '.got', 'data': '.data',
          'asan_globals': 'asan_globals', 'bss': '.bss', 'tbss': '.tbss'}


def b1w_expect(name):
    m = re.match(r'tfib_([AE])_(.+)$', name)
    if m:
        n = m.group(2)
        c = set()
        for k in {n, re.sub(r'_\d+$', '', n), re.sub(r'_libc$', '', n)}:
            c |= BYNAME.get(k, set())
        if m.group(1) == 'A':
            return {x for x, _ in c}
        return {x + sz for x, sz in c if sz} | {nxt(x) for x, sz in c if not sz}
    m = re.match(r'tfib_(\w+)_(lo|hi)$', name)
    if m and m.group(1) in SECROW:
        return {SEC[SECROW[m.group(1)]][0 if m.group(2) == 'lo' else 1]}
    if name == 'tfib_at_ph_addr_z':
        return {SEG[0][0] + pe.header['e_phoff']}
    return None


b1w = dict(re.findall(r'Definition (tfib_\w+) : Z := (0x[0-9a-fA-F]+|\d+)\.', text('A/AB1w.v')))
b1w_ok = {n for n, v in b1w.items() if (b1w_expect(n) or set()) & {int(v, 0)}}
b1w_fn = [n for n in b1w if re.match(r'tfib_[AE]_', n)]
MEAS['AB1w'] = (f'AB1w.v: {sum(1 for n in b1w_fn if n in b1w_ok)} of {len(b1w_fn)} function rows equal the twin symbol '
                f'start / end; section rows equal to the pin\'s section bounds: '
                f'{sum(1 for n in b1w if n in b1w_ok and n not in b1w_fn)}')

# (2) AE37.v x2_rodata: every (addr, len, [(off, w, value) ..]) tuple. A file-backed cell must be the pin's file bytes at
#     addr+off; a cell past the file bytes (.bss, a start-up value) must be AF0m.v's const cell of the same address and
#     width with the same value (gate 4, ifchk, checks those against every collected state)
t37 = text('A/AE37.v')
blk = t37[t37.index('Definition x2_rodata'):]
blk = blk[:blk.index('].\n') + 2]
tup = re.findall(r'\((0x[0-9a-fA-F]+), (\d+), \[(.*?)\]\)', blk, re.S)
n_cells = n_bss = bad_cells = 0
for base, ln, cells in tup:
    for off, w, v in re.findall(r'\((\d+), (\d+)%N, (0x[0-9a-fA-F]+|\d+)\)', cells):
        n_cells += 1
        ad, w, v = int(base, 16) + int(off), int(w), int(v, 0) & ((1 << (8 * int(w))) - 1)
        b = filebytes(ad, w)
        if b is None:
            n_bss += 1
            bad_cells += af0m_cell(ad, w) != v
        elif int.from_bytes(b, 'little') != v:
            bad_cells += 1
x2_ok = bad_cells == 0 and n_cells > 0
MEAS['AE37-x2_rodata'] = (f'AE37.v x2_rodata: {len(tup)} regions, {n_cells} cells ({n_cells - n_bss} file-backed, '
                          f'{n_bss} start-up cells past the file bytes), {bad_cells} differ from the pin\'s bytes / AF0m\'s cell')

# (3) the start-up shadow of the registered globals (as shadowcheck computes it from asan_globals) against the shadow
#     write sets AE23.v XW2 and AE37.v x2_shw: each must cover every nonzero shadow byte, and every other byte it holds
#     must be the shadow of a granule inside a registered global (a byte written 0)
ag = pe.get_section_by_name('asan_globals')
gd = ag.data()
objs = [struct.unpack_from('<3Q', gd, 64 * i) for i in range(len(gd) // 64)]
shadow = {g: 0xF9 for g in range(ag['sh_addr'] // 8 * 8, ag['sh_addr'] + ag['sh_size'], 8)}
for beg, size, szr in objs:
    for g in range(beg // 8 * 8, beg + szr, 8):
        shadow[g] = 0 if g + 8 <= beg + size else (beg + size - g if g < beg + size else 0xF9)
NZ = {0x7FFF8000 + g // 8 for g, v in shadow.items() if v}


def shadow_set_ok(byteset):
    extra = byteset - NZ
    inobj = all(any(b <= (s - 0x7FFF8000) * 8 < b + sz for b, sz, _ in objs) for s in extra)
    return NZ <= byteset and inobj, len(byteset), len(extra)


xw2 = re.search(r'Definition XW2 \(a : Z\) : Prop :=(.*?)\.\n', text('A/AE23.v'), re.S).group(1)
xw2b = {x for lo, hi in re.findall(r'\((0x[0-9a-f]+) <= a < (0x[0-9a-f]+)\)', xw2) if int(lo, 16) >= 0x7FFF8000
        for x in range(int(lo, 16), int(hi, 16))}
shw = re.search(r'Definition x2_shw : list \(Z \* Z\) :=(.*?)\]\.', t37, re.S).group(1)
shw_r = [(int(lo, 16), int(n)) for lo, n in re.findall(r'\((0x[0-9a-f]+), (\d+)\)', shw)]
shwb = {x for lo, n in shw_r for x in range(lo, lo + n)}
xw2_ok, xw2_n, xw2_x = shadow_set_ok(xw2b)
shw_ok, shw_n, shw_x = shadow_set_ok(shwb)
shw_hull = (min(lo for lo, _ in shw_r), max(lo + n for lo, n in shw_r))
MEAS['shadow-set'] = (f'registered globals {len(objs)}, nonzero start-up shadow bytes {len(NZ)}; AE23 XW2 shadow part '
                      f'{xw2_n} bytes ({xw2_x} more, each inside a registered global: {xw2_ok}); AE37 x2_shw {shw_n} bytes '
                      f'({shw_x} more: {shw_ok}), hull [{shw_hull[0]:#x}, {shw_hull[1]:#x})')

# (4) AE3i.v img_ro_chunks = [IMG_RO_LO, IMG_RO_HI) minus AF0m's owned rows there, IMG_RO_HI = PT_LOAD 1's end
t3i = text('A/AE3i.v')
lo3 = int(re.search(r'IMG_RO_LO : Z := (0x[0-9a-f]+)', t3i).group(1), 16)
hi3 = int(re.search(r'IMG_RO_HI : Z := (0x[0-9a-f]+)', t3i).group(1), 16)
num3 = lambda s: hi3 if s == 'IMG_RO_HI' else int(s, 16)
blk3 = t3i[t3i.index('Definition img_ro_chunks'):]
blk3 = blk3[:blk3.index('].')]
ch = [(int(x, 16), num3(y), int(z, 16)) for x, y, z in
      re.findall(r'mkChunk (0x[0-9a-f]+) \(CImg \((0x[0-9a-f]+|IMG_RO_HI) - (0x[0-9a-f]+)\)\)', blk3)]
ch_all = blk3.count('mkChunk ')
own = AF0M[AF0M.index('Definition Tfib_owned_static'):]
own = own[:own.index('].')]
owned = set()
for x, y in re.findall(r'\((0x[0-9a-f]+), ([^)]+)\)', own):
    lo, n = int(x, 16), int(eval(y))
    owned |= set(range(lo, lo + n))
cov = set()
for c, e, s in ch:
    cov |= set(range(c, c + (e - s)))
want = {x for x in range(lo3, hi3) if x not in owned}
ae3i_ok = (len(ch) == ch_all and cov == want and hi3 == loads[0]['p_vaddr'] + loads[0]['p_filesz']
           and all(s == c for c, e, s in ch))
MEAS['AE3i'] = (f'AE3i.v: {len(ch)} chunks cover {len(cov)} bytes = [{lo3:#x}, {hi3:#x}) minus AF0m owned rows '
                f'({len(want)} bytes): {cov == want}; IMG_RO_HI = PT_LOAD 1 end {loads[0]["p_vaddr"] + loads[0]["p_filesz"]:#x}: '
                f'{hi3 == loads[0]["p_vaddr"] + loads[0]["p_filesz"]}')


def ydef(f, n):   # the value of `Definition n : Z := <numerals joined by +>.` in lib/Reusable/f.v
    m = re.findall(r'Definition %s : Z := ((?:0x[0-9a-fA-F]+|\d+)(?: \+ (?:0x[0-9a-fA-F]+|\d+))*)\.' % n,
                   text(f'Reusable/{f}.v'))
    return sum(int(x, 0) for x in m[0].split(' + ')) if len(m) == 1 else None


def line_of(f, n):
    return text(f).split('\n')[int(n) - 1]


# (5) the sanitizer allocator's map size: Reusable/YG00.v's kUserMapSize and kFreeArrayMapSize, and every place the
#     pin's code forms that number as an immediate (`lui rd, size >> 12`), with the twin function that holds it
MAPSZ, FAMSZ = ydef('YG00', 'kUserMapSize'), ydef('YG00', 'kFreeArrayMapSize')
txt = pe.get_section_by_name('.text')
td, t0 = txt.data(), txt['sh_addr']
fn_at = lambda x: ([n for s, sz, n in FUNCS if s <= x < s + sz] or ['-'])[0]
LUI = [(t0 + o, (w >> 7) & 31, fn_at(t0 + o)) for o in range(0, len(td) - 3, 4)
       for w in [int.from_bytes(td[o:o + 4], 'little')] if MAPSZ and w & 0x7f == 0x37 and w >> 12 == MAPSZ >> 12]
lui_in = lambda *parts: any(all(p in n for p in parts) for _, _, n in LUI)
mapsz_ok = bool(MAPSZ) and MAPSZ == FAMSZ and MAPSZ & 0xfff == 0 and lui_in('SizeClassAllocator64', 'PopulateFreeArray') \
    and lui_in('SizeClassAllocator64', 'EnsureFreeArraySpace')
MEAS['map-size'] = (f'Reusable/YG00.v kUserMapSize {MAPSZ} = kFreeArrayMapSize {FAMSZ}: {MAPSZ == FAMSZ}; the pin forms '
                    f'{MAPSZ} as `lui rd, {(MAPSZ or 0) >> 12:#x}` at {len(LUI)} sites: '
                    + '; '.join(f'{x:#x} x{rd} in {n}' for x, rd, n in LUI))

# (6) the ASan fake stack: a frame region of size class CID starts kFakeFramesOff + (CID << kStackSizeLog) into the
#     fake stack (Reusable/YG0f.v, YG00.v)
FFO, SSL = ydef('YG0f', 'kFakeFramesOff'), ydef('YG00', 'kStackSizeLog')
fake_ok = FFO is not None and SSL is not None


def cid(f):
    m = re.findall(r'Definition CID : Z := (\d+)\.', text(f))
    return int(m[0]) if len(m) == 1 else None


MEAS['fake-stack'] = (f'Reusable/YG0f.v kFakeFramesOff {FFO}, Reusable/YG00.v kStackSizeLog {SSL}' + (
    f': the frame region of class 1 at {FFO + (1 << SSL):#x}, class 2 at {FFO + (2 << SSL):#x}' if fake_ok else ''))

# (7) AE2y.v icpt_rodata, the list Lemma entD_ro bounds: the largest end (address + length) of an entry, and kHighMemBeg
t2y = text('A/AE2y.v')
blk2y = t2y[t2y.index('Definition icpt_rodata'):]
blk2y = blk2y[:blk2y.index('].')]
ent2y = [(int(x, 16), int(n)) for x, n in re.findall(r'\((0x[0-9a-f]+), (\d+), \[', blk2y)]
ROEND = max(x + n for x, n in ent2y)
HIMEM = ydef('YG0f', 'kHighMemBeg')
bound_ok = len(ent2y) == blk2y.count(', [') and HIMEM is not None
MEAS['icpt_rodata'] = (f'AE2y.v icpt_rodata: {len(ent2y)} entries, largest end {ROEND:#x}; Reusable/YG0f.v kHighMemBeg '
                       f'{HIMEM if HIMEM is None else hex(HIMEM)}')

# (8) port_addr_check 205a90fd19b8 reads a page-aligned value as a SIZE only in a closed list of slots, and says so in the
#     row's note (`a size in a bound slot ...`). The rules of (8) read only rows that carry that note, so the per-row
#     triage of an older checker version's table is unchanged. Measured here: kImgLo of Reusable/YG0f.v against the
#     pin's first page-rounded segment, the image span, and the named Z constants of the allocator model files.
SIZE_SLOT = re.compile(r'a size in an? ([a-z-]+) slot')
IMG_LO = ydef('YG0f', 'kImgLo')
imglo_ok = IMG_LO is not None and IMG_LO == SEG[0][0] == 1 << 16
YCONST = collections.defaultdict(list)
for yf in ('YG00', 'YG0f', 'YG01'):
    for n, x in re.findall(r'Definition (\w+) : Z := (0x[0-9a-fA-F]+|\d+)\.', text(f'Reusable/{yf}.v')):
        YCONST[int(x, 0)].append(f'{n} (Reusable/{yf}.v)')
SEGTEST = (re.compile(r'\((\d+) <=\? x\) && \(x \+ 1 <=\? (\d+) \+ (\d+)\)'),     # B <= x < B + S (B twice)
           re.compile(r'\(Z\.to_N \(x - (\d+)\) <\? (\d+)\)%N'),                    # x - B < S
           re.compile(r'forall x, (0x[0-9a-f]+) <= x < (0x[0-9a-f]+) ->'))         # B <= x < B + S


def seg_geometry(sent, line, v):   # v as a bound / size of a page-rounded segment test of the line, or the image span
    tests = [(int(b), int(s)) for b, b2, s in SEGTEST[0].findall(line) if b == b2]
    tests += [(int(b), int(s)) for b, s in SEGTEST[1].findall(line)]
    tests += [(int(b, 16), int(e, 16) - int(b, 16)) for b, e in SEGTEST[2].findall(line)]
    for i, (lo, hi, sz) in enumerate(SEG):
        if (lo, sz) in tests and v in (lo, sz, hi):
            return (f'segment {i} [{lo:#x}, {hi:#x}) of the pin: {v:#x} is its '
                    + ('low' if v == lo else 'size' if v == sz else 'end'))
    if (sent == 'Lemma static_img_chk' and v in (SEG[0][0], TOP - SEG[0][0])
            and f'({SEG[0][0]:#x} <=? fst r) && (fst r + snd r <=? {SEG[0][0]:#x} + {TOP - SEG[0][0]:#x})' in line):
        return f'the image [{SEG[0][0]:#x}, IMG_TOP {TOP:#x}): {v:#x} is its ' + ('low' if v == SEG[0][0] else 'span')
    return None


# how a 2^16 = kImgLo numeral is used, read at each of its occurrences on the line: the occurrence is `@` with 40
# characters on each side, and the first pattern that matches gives its use (each list read by hand over the rows of
# gate 10); a line with two uses is given both, and an occurrence no pattern matches leaves the row without a class
LOW16 = (('IMAGE-LOW', r'@ <=\?? (?:a|x|y|lo|a\')\b[^>]*?(?:->[^>]*?)?(?:IMG_TOP|TFIB_INST|0x30000|0x9f000|6283264)'
                       r'|@ <= \?x < _'
                       r'|\(@ <=\? (?:a|fst r|fst iv|r_lo r|YP09\.c_off c)\)|IMG_TOP -> @ <= lo|<= @ \\/ YImgTop\.IMG_TOP'
                       r'|\(@ / 8\)|\(\(@ \+ \d+\) / 8\)|\(\(\d+ - @\) / 8\)|/ 8 <= @ / 8|@ <= fst r'),
         ('WINDOW-64K', r'(?:usp|sp0|\(ew E 0\)|sp_window_lo) - @|(?<!\|)-\s?@ <=|= -@|whi <= @|stk <= @|usp \+ @'
                        r'|win_check \(ss_mem ss\) a @|\(Z\.to_nat @\)|a \+ @ <= 2 \^ 47'),
         ('BYTES-2^16', r'@ \* (?:\(|b\d|h\b|byteZ)|(?:256 \* b\d|b\d) \+ @|v / @\)|\) / @ = b2|\(b2 \+ 256 \* b3\) \* @'
                        r'|b2 \* @|\* hi\) \* @'),
         ('SIZE-BOUND-64K', r'@ < n\b|<= @|@ <= (?:cap|CNTv)|cap = @|cap mod @|=> @|SLit @|16 \* @ < 2 \^ 64'),
         ('RANGE-16BIT', r'< @'),
         ('ALIGN-64K', r'mod @|\b(?:q|p|c|qa|qf|q\')\s\*\s@|eSp1 \+ @|eP \+ @|@ \+ o(?:ff)?\b|mod \d+ \+ @|1 \* @\)'))
LOW16_AT = re.compile(r'(?<![0-9A-Za-z_])(?:0x10000|65536)(?![0-9A-Za-z_])')


def low16_uses(line):
    occ = [line[max(0, x.start() - 40):x.start()] + '@' + line[x.end():x.end() + 40] for x in LOW16_AT.finditer(line)]
    uses = [next((c for c, rx in LOW16 if re.search(rx, o)), None) for o in occ]
    return '/'.join(dict.fromkeys(uses)) if occ and None not in uses else None


MEAS['size-slot'] = (f'Reusable/YG0f.v kImgLo {IMG_LO if IMG_LO is None else hex(IMG_LO)}, the pin\'s first page-rounded '
                     f'segment low {SEG[0][0]:#x}; image span IMG_TOP - kImgLo = {TOP - SEG[0][0]:#x}; named Z constants of '
                     f'Reusable/YG00.v, YG0f.v, YG01.v: {sum(len(x) for x in YCONST.values())}')
for k, v in MEAS.items():
    print(f'measured {k}: {v}')
for k, ok in (('AB1w', all(n in b1w_ok for n in b1w_fn)), ('AE37-x2_rodata', x2_ok), ('shadow-set', xw2_ok and shw_ok),
              ('AE3i', ae3i_ok), ('map-size', mapsz_ok), ('fake-stack', fake_ok), ('icpt_rodata', bound_ok),
              ('size-slot', imglo_ok)):
    if not ok:
        print(f'addr_triage: measurement {k} FAILED; its rule gives no row a class')

# ------------------------------------------------------------------------------------------------ the rules
GENERATED = {'A/AB01.v', 'A/AB03.v', 'A/ACej.v', 'A/AD2j.v', 'A/AF0m.v'}      # the checker's own generated-file list
STARTUP = GENERATED | {'A/AB05.v', 'A/AB12.v', 'A/AD1k.v', 'A/AD2i.v'}
RULES = collections.OrderedDict([
    ('STARTUP', 'a start-up file written from fuzz_disco.asan by its generator (the checker lists AB01 AB03 ACej AD2j '
                'AF0m as generated; AB05 AB12 AD1k AD2i are the plantail, atable, gen_ad1k and gen_ad2 outputs), so a '
                'pairing with the donor file says nothing; gate 3 (codeptr) checks every literal >= 0x10000 of these nine '
                'files against fuzz_disco.asan and the donor file (0 findings), gates 4 and 5 check every AF0m cell'),
    ('AE3I', 'AE3i.v img_ro_chunks: measured = [IMG_RO_LO, IMG_RO_HI) minus AF0m.v\'s owned rows, IMG_RO_HI = the end '
             'of PT_LOAD 1 (ae3i\'s rule); the donor pairing of a regenerated chunk list is an artefact'),
    ('SYMTAB', 'AB1w.v, the symbol table written from the twin: the row\'s definition measured equal to the twin\'s '
               'function start / end or the pin\'s section bound'),
    ('IMAGE-BYTES', 'AE37.v x2_rodata: every (address, width, value) cell measured equal to the pin\'s file bytes'),
    ('SHADOW-SET', 'a shadow write set (AE23 XW2, AE37 x2_shw and its hull in shw_ok): measured to cover every nonzero '
                   'start-up shadow byte of the registered globals and only shadow bytes of registered globals'),
    ('IDENT', 'a hex run inside an identifier (kind ident): a name, never an address (the checker\'s IDENT-NAME reading)'),
    ('NO-PORTED-VALUE', 'a donor numeral with no ported partner: the port holds no value in its place (the sentence '
                        'was restated or removed); a donor value carried elsewhere is its own row'),
    ('SMALL-QUANTITY', 'a ported numeral with no donor partner, below the image base (an index, count, length or '
                       'fuel of a restated proof step): not an address, nothing to relocate'),
    ('MAP-SIZE', 'a decimal equal to the sanitizer allocator\'s map size, kUserMapSize = kFreeArrayMapSize of '
                 'Reusable/YG00.v (measured), in a file that requires YG00: a byte count (a mapping length, an alignment, '
                 'a memset length of the internal allocator), never a pointer; the pin\'s own code forms that number as '
                 'a `lui` immediate in SizeClassAllocator64::PopulateFreeArray and ::EnsureFreeArraySpace (measured '
                 'sites), so it is the target\'s own quantity. A checker that reads a decimal inside a function as a code '
                 'address names the function that happens to cover it'),
    ('FAKESTACK-OFFSET', 'a `Definition FS_FROFF` equal to kFakeFramesOff + (CID << kStackSizeLog) with the file\'s own '
                         'CID (Reusable/YG0f.v, YG00.v; measured): the offset of size class CID\'s frame region inside an '
                         'ASan fake stack, which the file\'s Lemma frame_addr_cid adds to the fake-stack base '
                         '(frame_addr = ly_F + FS_FROFF + pos * FS_B); an offset, not an image address'),
    ('LOOSE-BOUND', 'Lemma entD_ro\'s bound `fst (fst e) + snd (fst e) <= V` over every entry of AE2y.v icpt_rodata, '
                    'proved entry by entry in the lemma and used to keep each entry below kHighMemBeg: measured V >= the '
                    'largest entry end and V < kHighMemBeg, so V is right as a bound whatever object it falls in'),
    ('AF0M-CELL', 'a `flit8 ADDR V` cell whose V equals AF0m.v\'s const cell at ADDR, width 8 (measured); gate 4 '
                  '(ifchk) checks every AF0m const cell in every collected state'),
    ('SEGMENT-GEOMETRY', '(only rows 205a90fd19b8 reads as a size) the low, size or end of a page-rounded segment of the pin '
                         'in that segment\'s own membership test (`(B <=? x) && (x + 1 <=? B + S)`, `x - B <? S`, '
                         '`forall x, B <= x < B + S`), or the image low / span in Lemma static_img_chk, measured equal to '
                         'the pin\'s own segment table: the target\'s own geometry, which differs from the donor\'s where '
                         'the two images differ, so the checker\'s `expected <donor value>` does not apply'),
    ('IMAGE-LOW', '(only rows 205a90fd19b8 reads as a size, value equal on both sides) 0x10000 = kImgLo of '
                  'Reusable/YG0f.v = the low of the pin\'s first page-rounded segment (measured), used as the low end of '
                  'an image address range (`0x10000 <= a < IMG_TOP`, the shadow of [kImgLo, IMG_TOP), the low of a '
                  'region with no base): the image start, an address that is the same in both images'),
    ('WINDOW-64K', '(as IMAGE-LOW for the value) 2^16 as the length of a 64 KiB window: below the user stack pointer '
                   '(`usp - 65536 <= a < usp`, a stack-relative region bound -65536) or the read window of win_check'),
    ('BYTES-2^16', '(as IMAGE-LOW for the value) 2^16 as the weight of byte 2 in a little-endian word '
                   '(`b0 + 256 * b1 + 65536 * b2 + ...`, `(v / 65536) mod 256`)'),
    ('SIZE-BOUND-64K', '(as IMAGE-LOW for the value) 2^16 as a size bound or length of the program or allocator model: '
                       'buffer capacity (`65536 <= cap <= 2 ^ 26`), request length (`1 <= want <= 65536`, a malloc / read '
                       'length register `SLit 65536`), kMaxSize of Reusable/YG00.v (`65536 < n -> from_primary n = false`, '
                       'needed size plus redzone <= 65536)'),
    ('RANGE-16BIT', '(as IMAGE-LOW for the value) 2^16 as the exclusive bound of a 16-bit value (`0 <= v < 65536`)'),
    ('ALIGN-64K', '(as IMAGE-LOW for the value) 2^16 as an alignment or granule of an address (`SB mod 65536 = 0`, '
                  '`q * 65536`, the stack top rounded to 64 KiB `u eSp1 + 65536`)'),
    ('NAMED-SIZE', '(only rows 205a90fd19b8 reads as a size, value equal on both sides) the value of exactly one named Z '
                   'constant of the allocator model files Reusable/YG00.v, YG0f.v, YG01.v (measured), which the detail '
                   'names: an image-independent quantity of the sanitizer runtime'),
    ('KERNEL', 'inside a fail-loud vm_compute / fetch_word fact over the image (checker column kernel_checked = yes): '
               'a wrong value fails the build; lib/A at the base is lib/A of the shipped merge (git diff empty)'),
])


def rule(r):
    f, sent = fkey(r), r['sentence'].split(' / ')[0]
    dname = sent.split()[-1] if sent else ''
    if f in STARTUP:
        return 'STARTUP', ''
    if f == 'A/AE3i.v' and ae3i_ok:
        return 'AE3I', ''
    if r['kind'] == 'ident':
        return 'IDENT', ''
    if r['verdict'] == 'UNPAIRED-SOURCE':
        return 'NO-PORTED-VALUE', ''
    if f == 'A/AB1w.v' and dname in b1w_ok and r['dst_value'] and int(r['dst_value'], 16) in (b1w_expect(dname) or ()):
        return 'SYMTAB', f'{dname} = {r["dst_value"]}'
    if f == 'A/AE37.v' and sent == 'Definition x2_rodata' and x2_ok:
        return 'IMAGE-BYTES', ''
    if xw2_ok and shw_ok and ((f == 'A/AE23.v' and sent == 'Definition XW2') or
                              (f == 'A/AE37.v' and sent in ('Definition x2_shw', 'Lemma shw_ok'))):
        v = int(r['dst_value'], 16)
        if v in xw2b | shwb | set(shw_hull) or v - 1 in xw2b | shwb or v < 0x10000:
            return 'SHADOW-SET', ''
    if r['verdict'] == 'UNPAIRED-PORTED' and r['src_class'] == 'NONADDR' and int(r['dst_value'], 16) < SEG[0][0]:
        return 'SMALL-QUANTITY', ''
    v = int(r['dst_value'], 16) if r['dst_value'] else None
    if mapsz_ok and v == MAPSZ and r['kind'] == 'dec' and re.search(r'Require(?: Import| Export)?\s[^.]*\bYG00\b', text(f)):
        return 'MAP-SIZE', f'{v} = kUserMapSize'
    k = cid(f) if fake_ok and sent == 'Definition FS_FROFF' and 'Lemma frame_addr_cid' in text(f) else None
    if k is not None and v == FFO + (k << SSL):
        return 'FAKESTACK-OFFSET', f'CID {k}: {FFO:#x} + ({k} << {SSL}) = {v:#x}'
    if (bound_ok and sent == 'Lemma entD_ro' and r['dst_line'] and re.search(r'\bAE2y\b', text(f))
            and f'fst (fst e) + snd (fst e) <= {r["dst_value"]})' in line_of(f, r['dst_line']) and ROEND <= v < HIMEM):
        return 'LOOSE-BOUND', f'largest entry end {ROEND:#x} <= {v:#x} < kHighMemBeg'
    if v is not None and r['dst_line']:
        hit = [int(x, 16) for x, y in re.findall(r'flit8 (0x[0-9a-fA-F]+) (0x[0-9a-fA-F]+|\d+)\b', line_of(f, r['dst_line']))
               if int(y, 0) == v]
        if hit and all(af0m_cell(x, 8) == v for x in hit):
            return 'AF0M-CELL', f'{", ".join(hex(x) for x in hit)} = {v:#x} in AF0m.v'
    m = SIZE_SLOT.search(r.get('note') or '')
    if m and v is not None and r['dst_line']:
        ln = line_of(f, r['dst_line'])
        g = seg_geometry(sent, ln, v)
        if g:
            return 'SEGMENT-GEOMETRY', f'{m.group(1)} slot; {g}'
        if r['verdict'] == 'NON-ADDRESS-SAME' and r['src_value'] == r['dst_value']:
            c = low16_uses(ln) if imglo_ok and v == IMG_LO else None
            if c:
                return c, f'{m.group(1)} slot; {v:#x} = 2^16 = kImgLo'
            if len(YCONST.get(v, [])) == 1:
                return 'NAMED-SIZE', f'{m.group(1)} slot; {v:#x} = {YCONST[v][0]}'
    if r['kernel_checked'] == 'yes':
        return 'KERNEL', ''
    return None, ''


# ------------------------------------------------------------------------------------------------ the hand table
KEY = ('verdict', 'file', 'src_line', 'dst_line', 'idx', 'kind', 'src_value', 'dst_value')
hand = list(csv.DictReader((l for l in open(a.hand) if not l.startswith('#')), delimiter='\t'))
ENV = dict(seg=seg, sec=sec, sym=sym, csym=csym, af0m=af0m, af0m_cell=af0m_cell, regions=regions, word=word,
           jal_imm=jal_imm, has=has, TOP=TOP, SYMS=SYMS)
hidx, bad = {}, []
for h in hand:
    k = tuple(h[c] for c in KEY)
    try:
        ok = eval(h['check'], {'__builtins__': {'len': len, 'all': all, 'any': any}}, ENV)
    except Exception as ex:          # noqa: BLE001 - a check that cannot be evaluated is a failed check
        ok, h['check'] = False, h['check'] + f' [{type(ex).__name__}: {ex}]'
    if not ok:
        bad.append(f'hand check failed: {k}: {h["check"]}')
    hidx[k] = h
used = collections.Counter()


def triage(r):   # one row: its key, class, right / DEFECT and detail (the hand table first, then the rules)
    k = tuple(x or '-' for x in (r['verdict'], fkey(r), r['src_line'], r['dst_line'], r['idx'], r['kind'],
                                 r['src_value'], r['dst_value']))
    if k in hidx:
        h = hidx[k]
        used[k] += 1
        return k, h['class'], h['verdict_of_row'], h['reason']
    c, detail = rule(r)
    if c is None:
        bad.append(f'no class: {k}')
        return k, 'UNTRIAGED', '-', detail
    return k, c, 'right', detail


def outrow(r, c, verdict, detail):
    return [r['verdict'], r['kernel_checked'], fkey(r), r['src_line'] or '-', r['dst_line'] or '-', r['sentence'][:90],
            r['idx'] or '-', r['kind'], r['src_value'] or '-', r['dst_value'] or '-', c, verdict, detail]


out, cls, res = [], collections.Counter(), {}
for r in fl:
    k, c, verdict, detail = triage(r)
    cls[(c, verdict)] += 1
    res[k] = (c, verdict)
    out.append(outrow(r, c, verdict, detail))
# rows whose verdict moved from an older checker version: a finding among them is triaged above; the rest here
mcls = collections.Counter()
for r in (csv.DictReader((l for l in open(a.also) if not l.startswith('#')), delimiter='\t') if a.also else ()):
    if r['verdict'] in FLAGS:
        k = tuple(x or '-' for x in (r['verdict'], fkey(r), r['src_line'], r['dst_line'], r['idx'], r['kind'],
                                     r['src_value'], r['dst_value']))
        c, verdict = res.get(k, ('UNTRIAGED', '-'))
    else:
        k, c, verdict, detail = triage(r)
        out.append(outrow(r, c, verdict, f'not a finding; verdict moved from {r["old_verdict"]}'
                          + (f'; {detail}' if detail else '')))
    mcls[(r['verdict'] in FLAGS, c, verdict)] += 1
bad += [f'hand row matches no flagged row: {k}' for k in hidx if not used[k]]
with open(a.out, 'w') as f:
    f.write('\t'.join(['verdict', 'kernel', 'file', 'src_line', 'dst_line', 'sentence', 'idx', 'kind', 'src_value',
                       'dst_value', 'triage', 'right_or_defect', 'detail']) + '\n')
    for o in out:
        f.write('\t'.join(o) + '\n')
for (c, v), n in sorted(cls.items(), key=lambda x: (-x[1], x[0])):
    print(f'triage {c}\t{v}\t{n}')
for c, t in RULES.items():
    print(f'rule {c}: {t}')
print(f'flagged {len(fl)}, triaged {sum(n for (c, v), n in cls.items() if c != "UNTRIAGED")}, '
      f'right {sum(n for (c, v), n in cls.items() if v == "right")}, '
      f'DEFECT {sum(n for (c, v), n in cls.items() if v == "DEFECT")}, hand rows {len(hand)} matching {sum(used.values())}')
if a.also:
    for (finding, c, v), n in sorted(mcls.items(), key=lambda x: (-x[1], x[0])):
        print(f'moved {"finding" if finding else "not a finding"}\t{c}\t{v}\t{n}')
    print(f'moved {sum(mcls.values())} (findings {sum(n for (x, _, _), n in mcls.items() if x)}, not findings '
          f'{sum(n for (x, _, _), n in mcls.items() if not x)}), triaged '
          f'{sum(n for (_, c, _), n in mcls.items() if c != "UNTRIAGED")}, right '
          f'{sum(n for (_, _, v), n in mcls.items() if v == "right")}, DEFECT '
          f'{sum(n for (_, _, v), n in mcls.items() if v == "DEFECT")}')
for b in bad:
    print('addr_triage: ' + b)
sys.exit(1 if bad else 0)
