#!/usr/bin/env python3
"""numerals-smB.py: the per-numeral table of reac-repacer/fuzz_wire's image-B __asan_stack_malloc_0 / _1 files
(lib/B/Rt/StackMalloc0.v, StackMalloc0Tbl.v, YF0r.v, YF0s.v, lib/Reusable/YF0v.v).

Every numeral that differs from the donor's, or that lies in an address range of either image ([lowest PT_LOAD start,
page-rounded end of the last PT_LOAD] of fuzz_grant.asan-ubsan or fuzz_wire.asan-ubsan), is one row. Its value is decided
BY ROLE on fuzz_wire's own image, with the same rule run on fuzz_grant's image as the control (it must give the donor's
own value); a row whose role no rule below measures is UNMEASURED (a STOP). No relocation tool's output decides a row:
the table compares what the files say with what the rule measures.

  CODE         a pc: the donor value lies in a sized FUNC symbol F of fuzz_grant's twin at offset o; the value is
               F' + o, F' fuzz_wire's FUNC of the same name (NAME{STT_FILE} for a local name several functions carry)
               and the same size, F a pair of the body compare (gates/bodycmp-smB.py; its verdict is printed).
               A bit-vector literal of a probe point (FS_FOUND) is the same rule.
  INSN         the instruction word of a fetch_word lemma: the 4 bytes at that pc of the image (the pc evaluated from the
               file's own definitions); a decode_any lemma's word must be its fetch lemma's.
  GOT          a .got cell: the 8-byte word(s) in the cell, read from the image, name a target: a symbol + offset (the
               smallest sized FUNC / OBJECT symbol holding the word), a general-dynamic tls_index {module 1, offset -
               0x800} by the STT_TLS symbol at that offset, or an initial-exec TP offset by the STT_TLS symbol at it; the
               value is the ONE .got cell of fuzz_wire whose word(s) name the same target. The code that loads the cell
               (an auipc pair in a function of the code table) is printed for both images.
  DATA         a data object: the donor value is symbol S + o (sized OBJECT); the value is fuzz_wire's S + o, S of the
               same size there. A cell's later fields are listed with the symbol each lies in.
  WORD         a value a cell holds: the word read from fuzz_wire's image at the relocated cell (address + field
               offset, the field's width), and it must name the same target as the donor's word in fuzz_grant.
  TLS          from the program headers and musl's static TLS layout (src/env/__init_tls.c static_init_tls and
               __copy_tls, TLS_ABOVE_TP, GAP_ABOVE_TP 0, sizeof(struct pthread) 200, MIN_TLS_ALIGN 8, DTP_OFFSET 0x800;
               mem = builtin_tls): TP, dtv (held at TP - 8), the dtv[1] slot and its value TP + 0x800.
  IMG          from the program headers: IMG_TOP = the end of the last PT_LOAD rounded up to 4096; IMG_TOP / 8;
               kLowShadowBeg + IMG_TOP / 8 (kLowShadowBeg 0x7fff7000, lib/Reusable/YG0f.v).
  MODEL        a constant of the model, unchanged: its formula over the kernel constants the unit's lib states
               (kStackSizeLog, kFakeStackSize, kFakeFramesOff), and, for a frame offset, the immediate in the target's
               code that builds it (a lui of the class's __asan_stack_malloc_N).

  usage: numerals-smB.py LIB DON BODYCMP_FUNCTIONS_OUT TSV_OUT
  env:   P (libreac's pinned image tree), R (reac-repacer's)
Prints the counts and every row that is not OK; exit 1 on any WRONG or UNMEASURED row."""
import collections, difflib, os, re, sys
from elftools.elf.elffile import ELFFile

LIB, DON, BCMP, OUT = sys.argv[1:5]
P, R = os.environ['P'], os.environ['R']
FILES = [('B/Rt/StackMalloc0.v', 'Rt/StackMalloc0.v'), ('B/Rt/StackMalloc0Tbl.v', 'Rt/StackMalloc0Tbl.v'),
         ('B/Rt/YF0r.v', 'Rt/YF0r.v'), ('B/Rt/YF0s.v', 'Rt/YF0s.v'), ('Reusable/YF0v.v', 'YF0v.v')]
K_LOW_SHADOW_BEG = 0x7fff7000
PTHREAD, MIN_TLS_ALIGN, DTP_OFFSET = 200, 8, 0x800


class Img:
    def __init__(self, tag, pin, twin):
        self.tag = tag
        self.data = open(pin, 'rb').read()
        e = ELFFile(open(pin, 'rb'))
        self.loads = [(p['p_vaddr'], p['p_memsz'], p['p_offset'], p['p_filesz']) for p in e.iter_segments() if p['p_type'] == 'PT_LOAD']
        self.tls = [(p['p_vaddr'], p['p_filesz'], p['p_memsz'], p['p_align']) for p in e.iter_segments() if p['p_type'] == 'PT_TLS']
        self.secs = [(s.name, s['sh_addr'], s['sh_size'], s['sh_flags']) for s in e.iter_sections() if s['sh_addr']]
        t = ELFFile(open(twin, 'rb'))
        self.syms, self.tlss = [], []
        cur = None
        for s in t.get_section_by_name('.symtab').iter_symbols():
            ty = s['st_info']['type']
            if ty == 'STT_FILE':
                cur = s.name
            elif ty == 'STT_TLS':
                self.tlss.append((s['st_value'], s['st_size'], s.name))
            elif ty in ('STT_FUNC', 'STT_OBJECT') and s['st_size'] > 0:
                self.syms.append((s['st_value'], s['st_size'], s.name, ty, cur if s['st_info']['bind'] == 'STB_LOCAL' else None))
        self.copies = collections.defaultdict(set)
        for v, z, n, ty, f in self.syms:
            self.copies[n].add((v, z))
        lo = min(v for v, m, o, f in self.loads)
        hi = max(v + m for v, m, o, f in self.loads)
        self.lo, self.end, self.top = lo, hi, (hi + 0xfff) & ~0xfff

    def word(self, a, n=8):
        for v, m, o, f in self.loads:
            if v <= a and a + n <= v + f:
                return int.from_bytes(self.data[o + a - v:o + a - v + n], 'little')
        return None

    def sec(self, a):
        return next((n for n, v, z, fl in self.secs if v <= a < v + z), None)

    def qn(self, n, f):
        return n if len(self.copies[n]) == 1 else '%s{%s}' % (n, f)

    def holder(self, a, kinds=('STT_FUNC', 'STT_OBJECT')):
        c = sorted((z, v, n, ty, f) for v, z, n, ty, f in self.syms if v <= a < v + z and ty in kinds)
        if not c:
            return None
        z, v, n, ty, f = c[0]
        return self.qn(n, f), v, z, ty, a - v

    def byq(self, q, ty):
        n = q.split('{')[0]
        c = [(v, z) for v, z, nm, t, f in self.syms if nm == n and t == ty and self.qn(nm, f) == q]
        return c[0] if len(c) == 1 else None

    def tlsname(self, off):
        c = [(v, z, n) for v, z, n in self.tlss if v <= off < v + max(z, 1)]
        return '%s+%#x@tls' % (c[0][2], off - c[0][0]) if len(c) == 1 else None

    def tls_layout(self):
        """musl static_init_tls + __copy_tls (TLS_ABOVE_TP, one module, mem = builtin_tls) -> (tp, dtv, dtv[1])"""
        image, filesz, memsz, align = self.tls[0]
        size = memsz + ((-memsz - image) & (align - 1))
        offset = image & (align - 1)
        align = max(align, MIN_TLS_ALIGN)
        tls_size = (2 * 8 + PTHREAD + offset + size + align + MIN_TLS_ALIGN - 1) & -MIN_TLS_ALIGN
        bt = [(v, z) for v, z, n, ty, f in self.syms if n == 'builtin_tls']
        assert len(bt) == 1 and tls_size <= bt[0][1]
        mem = bt[0][0]
        dtv = mem + tls_size - 2 * 8
        tp = mem + ((-(mem + PTHREAD)) & (align - 1)) + PTHREAD
        return tp, dtv, tp + offset + DTP_OFFSET, bt[0]


G = Img('G', P + '/bin/fuzz_grant/fuzz_grant.asan-ubsan', P + '/unstripped/fuzz_grant/fuzz_grant.asan-ubsan')
W = Img('W', R + '/result/bin/fuzz_wire/fuzz_wire.asan-ubsan', R + '/result/unstripped/fuzz_wire/fuzz_wire.asan-ubsan')
LO, HI = min(G.lo, W.lo), max(G.top, W.top)

# the body compare's verdict per function pair
VERD = {}
for line in open(BCMP):
    f = line.rstrip('\n').split('\t')
    if len(f) > 11 and f[1] == 'W:G':
        VERD[f[0]] = '%s, %s target differences' % (f[6], f[11] if f[11] == '0' else len(eval(f[11])))
for line in open(BCMP):
    f = line.rstrip('\n').split('\t')
    if f[0] == 'JUDGED' and f[1] in VERD:
        VERD[f[1]] += ' (JUDGED in bodycmp-functions.out: the differing target lies outside the bytes the code table decodes)'


def verd_ok(q):
    v = VERD.get(q, 'NOT COMPARED')
    return v.startswith(('EQUAL,', 'EQUAL-mod-pcrel,')) and v.endswith(' 0 target differences') or 'JUDGED' in v


def words16(b):
    i, out = 0, []
    while i + 2 <= len(b):
        lo = b[i] | (b[i + 1] << 8)
        if lo & 3 == 3:
            out.append((i, int.from_bytes(b[i:i + 4], 'little'), 4)); i += 4
        else:
            out.append((i, lo, 2)); i += 2
    return out


def sx(x, n):
    return x - (1 << n) if x & (1 << (n - 1)) else x


def refs(I, v, z):
    """auipc pairs of one function: (offset of the consumer, kind, address); a register's auipc value is dropped at
    any later write to it"""
    b = bytes(I.data[next(o + v - lv for lv, m, o, f in I.loads if lv <= v < lv + f):][:z])
    st, out = {}, []
    for off, x, n in words16(b):
        if n == 2:
            q, f3 = x & 3, x >> 13
            if q == 0 and f3 in (2, 3):   # c.lw / c.ld rd', off(rs1')
                rs1 = 8 + ((x >> 7) & 7)
                if rs1 in st:
                    imm = (((x >> 10) & 7) << 3) | (((x >> 6) & 1) << 2) | (((x >> 5) & 1) << 6) if f3 == 2 else \
                          (((x >> 10) & 7) << 3) | (((x >> 5) & 3) << 6)
                    out.append((off, 'c.l%s' % ('w' if f3 == 2 else 'd'), st[rs1] + imm))
                st.pop(8 + ((x >> 2) & 7), None)
            else:
                rd = (x >> 7) & 31 if q in (1, 2) else 8 + ((x >> 2) & 7)
                st.pop(rd, None)
            continue
        op, rd, f3, rs1 = x & 0x7f, (x >> 7) & 31, (x >> 12) & 7, (x >> 15) & 31
        if op == 0x17:
            st[rd] = v + off + sx(x & 0xfffff000, 32)
            continue
        if op in (0x03, 0x13, 0x1b, 0x67) and rs1 in st:
            out.append((off, {0x03: 'load', 0x13: 'addi', 0x1b: 'addiw', 0x67: 'jalr'}[op], st[rs1] + sx(x >> 20, 12)))
        if op in (0x23, 0x27) and rs1 in st:
            out.append((off, 'store', st[rs1] + sx(((x >> 25) << 5) | ((x >> 7) & 31), 12)))
        if op in (0x33, 0x3b, 0x13, 0x1b, 0x03, 0x67, 0x6f, 0x37, 0x17, 0x73, 0x2f):
            st.pop(rd, None)
    return out


def table_fns(I, ranges):
    out = []
    for a, n in ranges:
        h = I.holder(a, ('STT_FUNC',))
        if h:
            out.append((h[0], h[1], h[2]))
    return list(dict.fromkeys(out))


def fs_ranges(text):
    m = re.search(r'Definition fs_ranges : list \(Z \* nat\) :=\s*\[(.*?)\]\.', text, re.S)
    return [(int(a, 16), int(n)) for a, n in re.findall(r'\((0x[0-9a-f]+), (\d+)%nat\)', m.group(1))] if m else []


def defs(text):
    return {k: int(v, 0) for k, v in re.findall(r'Definition (\w+) : Z := (0x[0-9a-fA-F]+|\d+)\.', text)}


def model_consts():
    t = open(os.path.join(LIB, 'Reusable/YG00.v')).read() + open(os.path.join(LIB, 'Reusable/YG0f.v')).read()
    k = {}
    for name in ('kStackSizeLog', 'kFakeStackSize', 'kFakeFramesOff'):
        m = re.search(r'Definition %s : Z := ([^.]+)\.' % name, t)
        k[name] = eval(m.group(1))
    return k


MC = model_consts()
MODEL = {
    1 << MC['kStackSizeLog']: ('Z.shiftl 1 kStackSizeLog', 1 << MC['kStackSizeLog'], None),
    (MC['kFakeStackSize'] - MC['kFakeFramesOff']) // 8: ('(kFakeStackSize - kFakeFramesOff) / 8',
                                                         (MC['kFakeStackSize'] - MC['kFakeFramesOff']) // 8, None),
    MC['kFakeFramesOff'] + (1 << MC['kStackSizeLog']): ('fs_frame_off 1 0 = kFakeFramesOff + 1 * Z.shiftl 1 kStackSizeLog',
                                                         MC['kFakeFramesOff'] + (1 << MC['kStackSizeLog']), '__asan_stack_malloc_1'),
}


def fn_imms(I, fn):
    """the immediates of fn's non-pc-relative OP-IMM / OP-IMM-32 / LUI words and compressed li / lui / slli, by offset
    (an addi on a register an auipc set is a pc-relative pair and is left out)"""
    v, z = I.byq(fn, 'STT_FUNC')
    b = bytes(I.data[next(o + v - lv for lv, m, o, f in I.loads if lv <= v < lv + f):][:z])
    out, au = [], set()
    for off, x, n in words16(b):
        if n == 4:
            op, rd, f3, rs1 = x & 0x7f, (x >> 7) & 31, (x >> 12) & 7, (x >> 15) & 31
            if op == 0x17:
                au.add(rd); continue
            if op in (0x13, 0x1b) and rs1 not in au:
                out.append((off, 'op-imm f3=%d' % f3, sx(x >> 20, 12) if f3 in (0, 2, 3, 4, 6, 7) else (x >> 20) & 63))
            elif op == 0x37:
                out.append((off, 'lui', (x >> 12) << 12))
            au.discard(rd)
        else:
            q, f3, rd = x & 3, x >> 13, (x >> 7) & 31
            if q == 1 and f3 in (2, 3) and rd not in (0, 2):
                out.append((off, 'c.li' if f3 == 2 else 'c.lui', sx((((x >> 12) & 1) << 5) | ((x >> 2) & 31), 6)))
            elif q == 2 and f3 == 0:
                out.append((off, 'c.slli', (((x >> 12) & 1) << 5) | ((x >> 2) & 31)))
            au.discard(rd)
    return out


NUM = re.compile(r"(?<![A-Za-z0-9_'])(0x[0-9a-fA-F]+|[0-9]+)(?![A-Za-z0-9_'])")


def val(t):
    return int(t, 16) if t.lower().startswith('0x') else int(t)


def mask(l):
    return NUM.sub('#', l)


def name_word(I, w, cell=None):
    """the target an 8-byte word names: symbol + offset, or (for a TLS-shaped cell) a TLS symbol"""
    h = I.holder(w)
    if h:
        return '%s+%#x' % (h[0], h[4])
    return None


def got_target(I, a):
    """the named target of the .got cell at a"""
    w0, w1 = I.word(a), I.word(a + 8)
    if w0 == 1 and w1 is not None and I.tlsname((w1 + DTP_OFFSET) & (2 ** 64 - 1)) and (w1 + DTP_OFFSET) & (2 ** 64 - 1) < 0x1000:
        return 'tls_index{1, %s}' % I.tlsname((w1 + DTP_OFFSET) & (2 ** 64 - 1)), 16
    n = name_word(I, w0)
    if n:
        return n, 8
    if w0 is not None and I.tlsname(w0):
        return 'tp-offset %s' % I.tlsname(w0), 8
    return None, 8


def got_cells(I):
    s = [(v, z) for n, v, z, fl in I.secs if n == '.got'][0]
    return range(s[0], s[0] + s[1], 8)


def find_got(I, target):
    return [a for a in got_cells(I) if got_target(I, a)[0] == target]


rows = []
TBL = {}


def row(tf, ln, dln, dt, tt, role, exp, ev, verdict=None):
    dv, tv = val(dt), val(tt)
    if verdict is None:
        verdict = 'UNMEASURED' if exp is None else ('OK' if exp == tv else 'WRONG')
    rows.append((tf, ln, dln, dt, tt, role, '' if exp is None else hex(exp), verdict, ev))


CELL = re.compile(r'\(((?:0x[0-9a-f]+)|(?:TP - \d+)), (\d+), \[([^\]]*)\]\)')
FIELD = re.compile(r'\((\d+), (\d+)%N, (0x[0-9a-f]+|\d+|TSD)\)')


def cell_of(line, pos):
    """(cell index, field index or None) of the numeral starting at pos: None for a field means the cell's address"""
    for ci, cm in enumerate(CELL.finditer(line)):
        if cm.start(1) == pos:
            return ci, None
        for fi, fm in enumerate(FIELD.finditer(cm.group(3))):
            if cm.start(3) + fm.start(3) == pos:
                return ci, fi
    return None


def cell_addr(cm, defs_):
    a = cm.group(1)
    return defs_['TP'] - int(a.split('-')[1]) if a.startswith('TP') else int(a, 16)


def decide(tf, ln, dln, k, tline, dline, tdefs, ddefs):
    tm, dm = list(NUM.finditer(tline))[k], list(NUM.finditer(dline))[k]
    tt, dt = tm.group(1), dm.group(1)
    dv, tv = val(dt), val(tt)
    # instruction words of fetch / decode lemmas
    m = re.search(r'Lemma F_(\w+) : fetch_word tfibsegs \(Z_to_bv 64 \((\w+) \+ (0x[0-9a-f]+)\)\) = Some \((0x[0-9a-f]+)%bv', tline)
    if m and m.start(4) == tm.start(1):
        pt, pd = tdefs[m.group(2)] + int(m.group(3), 16), ddefs[m.group(2)] + int(m.group(3), 16)
        e, c = W.word(pt, 4), G.word(pd, 4)
        TBL[(tf, m.group(1))] = tv
        if c != dv:
            e = None
        return row(tf, ln, dln, dt, tt, 'INSN', e, 'the 4 bytes at %s + %s = %#x of the image (control: grant %#x holds %#x, the donor word)'
                   % (m.group(2), m.group(3), pt, pd, c))
    m = re.search(r'Lemma D_(\w+) : decode_any \((0x[0-9a-f]+)%bv', tline)
    if m and m.start(2) == tm.start(1):
        return row(tf, ln, dln, dt, tt, 'INSN', TBL.get((tf, m.group(1))), 'the word of fetch lemma F_%s of this file' % m.group(1))
    # TLS layout
    gtp, gdtv, gdtv1, gbt = G.tls_layout()
    wtp, wdtv, wdtv1, wbt = W.tls_layout()
    tl = {gtp: ('TP', wtp), gdtv: ('dtv (the word at TP - 8)', wdtv), gdtv + 8: ('the dtv[1] slot (dtv + 8)', wdtv + 8),
          gdtv1: ('dtv[1] = TP + 0x800 (module 1, DTP_OFFSET)', wdtv1)}
    if dv in tl:
        what, e = tl[dv]
        if RTP != wtp or RDTV != wdtv:
            e = None
        return row(tf, ln, dln, dt, tt, 'TLS', e, '%s; PT_TLS (vaddr, filesz, memsz, align) %s, builtin_tls %#x size %d (control: grant %s, '
                   'builtin_tls %#x: the rule gives the donor value); the record lib/B/YF0m.v: TFIB_TP %#x, (ATp (-8)) %s'
                   % (what, [hex(x) for x in W.tls[0]], wbt[0], wbt[1], [hex(x) for x in G.tls[0]], gbt[0], RTP, hex(RDTV) if RDTV else None))
    # image end
    img = {G.top: ('IMG_TOP', W.top), G.top // 8: ('IMG_TOP / 8', W.top // 8),
           K_LOW_SHADOW_BEG + G.top // 8: ('kLowShadowBeg + IMG_TOP / 8', K_LOW_SHADOW_BEG + W.top // 8)}
    if dv in img:
        what, e = img[dv]
        return row(tf, ln, dln, dt, tt, 'IMG', e, '%s: last PT_LOAD end %#x -> IMG_TOP %#x (control: grant end %#x -> %#x: the rule gives the donor value)'
                   % (what, W.end, W.top, G.end, G.top))
    # model constants
    if dv in MODEL and dv == tv:
        f, e, fn = MODEL[dv]
        ev = '%s with %s (lib/Reusable/YG00.v, YG0f.v)' % (f, ', '.join('%s = %#x' % kv for kv in MC.items()))
        if fn:
            iw, ig = fn_imms(W, fn), fn_imms(G, fn)
            vd = VERD.get(fn, 'NOT COMPARED')
            ev += ('; %s computes it from the stack size log (no literal %#x): its %d immediates (%s) are the same in both images, '
                   'and its body compare is %s' % (fn, e, len(iw), ' '.join('+%#x %s %s' % (o, k, i) for o, k, i in iw), vd)
                   if iw == ig else '; the immediates of %s DIFFER between the images' % fn)
            if iw != ig or not verd_ok(fn):
                e = None
        return row(tf, ln, dln, dt, tt, 'MODEL', e, ev)
    sec = G.sec(dv)
    tc, dc = cell_of(tline, tm.start(1)), cell_of(dline, dm.start(1))
    # a word a cell holds: the field's bytes of the image at the relocated cell
    if tc and tc[1] is not None and dc == tc:
        tcm, dcm = list(CELL.finditer(tline))[tc[0]], list(CELL.finditer(dline))[tc[0]]
        tfm, dfm = list(FIELD.finditer(tcm.group(3)))[tc[1]], list(FIELD.finditer(dcm.group(3)))[tc[1]]
        cellt, celld, off, wd = cell_addr(tcm, tdefs), cell_addr(dcm, ddefs), int(tfm.group(1)), int(tfm.group(2))
        e, c = W.word(cellt + off, wd), G.word(celld + off, wd)
        ne, nc = (name_word(W, e) if e is not None else None), (name_word(G, c) if c is not None else None)
        ev = 'the %d-byte word at cell %#x + %d of the image, naming %s (control: grant cell %#x + %d holds %s naming %s)' % (
            wd, cellt, off, ne, celld, off, hex(c) if c is not None else None, nc)
        if e is None and c is None:
            # a cell of memory no file byte backs (.bss / TLS): the value is the role's (TLS layout above) or a STOP
            return row(tf, ln, dln, dt, tt, 'UNMEASURED', None, 'a field of a cell in no file-backed byte: ' + ev)
        if c != dv or ne != nc:
            e = None
        return row(tf, ln, dln, dt, tt, 'WORD', e, ev)
    # .got cells
    if sec == '.got':
        tg, n = got_target(G, dv)
        cand = find_got(W, tg) if tg else []
        e = cand[0] if len(cand) == 1 else None
        wt = got_target(W, tv)[0]
        fw_, fg_ = table_fns(W, FSR['W']), table_fns(G, FSR['G'])
        shared = {q for q, v, z in fw_} & {q for q, v, z in fg_}
        sites_g = [(q, o, kd) for q, v, z in fg_ for o, kd, a in refs(G, v, z) if a == dv]
        sites_w = [(q, o, kd) for q, v, z in fw_ for o, kd, a in refs(W, v, z) if a == tv]
        ev = 'the grant cell names %s; the fuzz_wire .got cells naming it: %s; the written cell names %s; the code-table code that loads it: grant %s, wire %s' % (
            tg, ','.join(hex(c) for c in cand) or 'NONE', wt, ','.join('%s+%#x %s' % s for s in sites_g) or 'none',
            ','.join('%s+%#x %s' % s for s in sites_w) or 'none')
        extra = [s for s in sites_g if s[0] not in shared]
        if extra:
            ev += ' (grant sites in functions of the dropped code-table rows, which fuzz_wire does not link: %s)' % ','.join('%s+%#x' % s[:2] for s in extra)
        if [s for s in sites_g if s[0] in shared] != sites_w or wt != tg:
            e = None
            ev += ' (LOAD SITES OR TARGET DIFFER)'
        return row(tf, ln, dln, dt, tt, 'GOT', e, ev)
    # code
    if sec == '.text':
        h = G.holder(dv, ('STT_FUNC',))
        if h:
            q, v, z, ty, o = h
            t = W.byq(q, 'STT_FUNC')
            e = t[0] + o if t and t[1] == z else None
            vd = VERD.get(q, 'NOT COMPARED')
            if not verd_ok(q):
                e = None
            return row(tf, ln, dln, dt, tt, 'CODE', e, '%s+%#x (grant %#x size %d; wire %s size %s); body compare: %s'
                       % (q, o, v, z, hex(t[0]) if t else None, t[1] if t else None, vd))
    # data objects
    h = G.holder(dv, ('STT_OBJECT',))
    if h:
        q, v, z, ty, o = h
        t = W.byq(q, 'STT_OBJECT')
        e = t[0] + o if t and t[1] == z else None
        ev = '%s+%#x (grant %#x size %d; wire %s size %s)' % (q, o, v, z, hex(t[0]) if t else None, t[1] if t else None)
        if tc and tc[1] is None:
            fl = []
            tcm = list(CELL.finditer(tline))[tc[0]]
            for fm in FIELD.finditer(tcm.group(3)):
                fo = int(fm.group(1))
                hw, hg = W.holder(tv + fo, ('STT_OBJECT',)), G.holder(dv + fo, ('STT_OBJECT',))
                fl.append('+%d in wire %s, grant %s' % (fo, hw and '%s+%#x size %d' % (hw[0], hw[4], hw[2]),
                                                       hg and '%s+%#x size %d' % (hg[0], hg[4], hg[2])))
                if not hw or not hg or (hw[0], hw[4], hw[2]) != (hg[0], hg[4], hg[2]):
                    e = None
            ev += '; the cell fields ' + '; '.join(fl)
        if q == 'builtin_tls':
            # a thread-object cell the start-up record states (T + 48 / T + 56)
            ev += '; the record lib/B/YF0m.v Tfib_const_sym: %s' % (('z8 (%s) %#x' % (RECORD_VALUES[tv], tv)) if tv in RECORD_VALUES else 'NOT STATED')
            if tv not in RECORD_VALUES:
                e = None
        return row(tf, ln, dln, dt, tt, 'DATA', e, ev)
    return row(tf, ln, dln, dt, tt, 'UNMEASURED', None, 'no rule measures this value (section %s)' % sec)


yf0m = open(os.path.join(LIB, 'B/YF0m.v')).read()
RECORD_VALUES = {int(v, 16): k for k, v in re.findall(r'z8 \((AT \d+)\) (0x[0-9a-f]+)', yf0m)}
RTP = int(re.search(r'Definition TFIB_TP : Z := (0x[0-9a-f]+)\.', yf0m).group(1), 16)
_m = re.search(r'z8 \(ATp \(-8\)\) (0x[0-9a-f]+)', yf0m)
RDTV = int(_m.group(1), 16) if _m else None

texts = {tf: open(os.path.join(LIB, tf)).read() for tf, df in FILES}
dtexts = {tf: open(os.path.join(DON, df)).read() for tf, df in FILES}
FSR = {'W': fs_ranges(texts['B/Rt/YF0r.v']), 'G': fs_ranges(dtexts['B/Rt/YF0r.v'])}
unaligned = []
LICENCE = re.compile(r'^\(\* (Copyright |SPDX-License-Identifier: |Modified by ).*\*\)$')
# the lines B-smB.patch writes (its '+' lines): a numeral the patch adds is a row of its own
PATCHED = {l[1:] for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'B-smB.patch')).read().split('\n')
           if l.startswith('+') and not l.startswith('+++')}
for tf, df in FILES:
    T, D = texts[tf].split('\n'), dtexts[tf].split('\n')
    # the donor's leading licence lines are not in the target (apply-smB.sh removes them; applied.txt counts them)
    skip = 0
    while skip < len(D) and LICENCE.match(D[skip]):
        skip += 1
    tdefs, ddefs = defs(texts[tf]), defs(dtexts[tf])
    sm = difflib.SequenceMatcher(None, [mask(l) for l in D[skip:]], [mask(l) for l in T], autojunk=False)
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        i1, i2 = i1 + skip, i2 + skip
        pairs = []
        if op == 'equal' or (op == 'replace' and i2 - i1 == j2 - j1):
            pairs = [(i1 + k, j1 + k) for k in range(i2 - i1)]
        else:
            for i in range(i1, i2):
                unaligned.append((tf, op, i + 1, j1 + 1, D[i][:120]))
            for j in range(j1, j2):
                unaligned.append((tf, op + '-target', i1 + 1, j + 1, T[j][:120]))
            continue
        for i, j in pairs:
            dl, tl_ = D[i], T[j]
            dn, tn = NUM.findall(dl), NUM.findall(tl_)
            if tl_.startswith('[(') and 'fs_ranges' in T[j - 1]:
                continue  # the code table: its own rows below
            if len(dn) != len(tn):
                if tl_ not in PATCHED:
                    unaligned.append((tf, 'numeral-count', i + 1, j + 1, tl_[:120])); continue
                # a patched line here adds numerals only: the donor line holds none, every numeral is a PATCH row
                if dn:
                    unaligned.append((tf, 'patched line keeps donor numerals', i + 1, j + 1, tl_[:120])); continue
                for t in tn:
                    rows.append((tf, j + 1, i + 1, '-', t, 'PATCH', hex(val(t)), 'OK' if not (LO <= val(t) <= HI) else 'UNMEASURED',
                                 'added by B-smB.patch (one of its + lines): the test `=? %s` of lib/Reusable/YG0f.v owned_extents '
                                 '(`ly_NB ly =? 0`, `ly_SB ly =? 0`); no image value' % t))
                continue
            for k, (d, t) in enumerate(zip(dn, tn)):
                if val(d) != val(t) or LO <= val(d) <= HI or LO <= val(t) <= HI:
                    decide(tf, j + 1, i + 1, k, tl_, dl, tdefs, ddefs)

# the code table rows, paired by function and offset
gk = {}
for a, n in FSR['G']:
    h = G.holder(a, ('STT_FUNC',))
    gk[(h[0], h[4])] = (a, n, h)
tln = next(i + 1 for i, l in enumerate(texts['B/Rt/YF0r.v'].split('\n')) if l.startswith('[(') and 'fs_ranges' in texts['B/Rt/YF0r.v'].split('\n')[i - 1])
dln = next(i + 1 for i, l in enumerate(dtexts['B/Rt/YF0r.v'].split('\n')) if l.startswith('[(') and 'fs_ranges' in dtexts['B/Rt/YF0r.v'].split('\n')[i - 1])
for a, n in FSR['W']:
    h = W.holder(a, ('STT_FUNC',))
    d = gk.pop((h[0], h[4]), None) if h else None
    if d is None:
        row('B/Rt/YF0r.v', tln, dln, '0', hex(a), 'UNMEASURED', None, 'code-table row with no donor row of that function and offset'); continue
    vd = VERD.get(h[0], 'NOT COMPARED')
    e = a if (W.byq(h[0], 'STT_FUNC') or (0, 0))[1] == d[2][2] and verd_ok(h[0]) else None
    row('B/Rt/YF0r.v', tln, dln, hex(d[0]), hex(a), 'CODE', e, 'code-table row %s+%#x, %d words (grant row %#x, %d words; function size %d both); body compare: %s'
        % (h[0], h[4], n, d[0], d[1], h[2], vd))
    if n != d[1]:
        row('B/Rt/YF0r.v', tln, dln, str(d[1]), str(n), 'CODE', None, 'word count differs')
for (q, o), (a, n, h) in gk.items():
    rows.append(('B/Rt/YF0r.v', tln, dln, hex(a), '(row removed)', 'CODE', '', 'DROPPED',
                 'grant row %s+%#x, %d words: fuzz_wire twin has %s symbol %s (B-smB.patch removes it)'
                 % (q, o, n, 'a' if q.split('{')[0] in W.copies else 'no', q)))

with open(OUT, 'w') as f:
    f.write('# numerals-smB.py: one row per numeral of the relocated files that differs from the donor or lies in [%#x, %#x]\n' % (LO, HI))
    f.write('# images: fuzz_grant.asan-ubsan (pin fde52226dc48, twin 5a5ee7c02b4e), fuzz_wire.asan-ubsan (pin af4534831a45, twin 51eb4bef2425)\n')
    f.write('file\tline\tdonor_line\tdonor\ttarget\trole\tmeasured\tverdict\tevidence\n')
    for r in rows:
        f.write('\t'.join(str(x) for x in r) + '\n')
cnt = collections.Counter(r[7] for r in rows)
roles = collections.Counter((r[5], r[7]) for r in rows)
print('numerals-smB: %d rows; verdicts %s; by role %s; unaligned donor lines %d' % (len(rows), dict(cnt), dict(roles), len(unaligned)))
for u in unaligned:
    print('UNALIGNED\t%s\t%s\tdonor %d\ttarget %d\t%s' % u)
for r in rows:
    if r[7] not in ('OK', 'DROPPED'):
        print('\t'.join(str(x) for x in r))
sys.exit(1 if any(r[7] not in ('OK', 'DROPPED') for r in rows) or unaligned else 0)
