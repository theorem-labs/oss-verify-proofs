"""atable.py: emit cgif_file_fuzzer's per-image atable file (AB12.v for the asan side 'A', YB12.v for asan-ubsan 'B')
for any unit, from the unit's own pinned image and a symbol source.

The atable record is cgif's YK09.v:21 (`atable`); cgif's values are lib/A/AB12.v and lib/YB12.v at commit
c8557374ad2e. Every value here is computed from the given image: image fields from its ELF program headers, code
fields as (symbol + offset), the sealed-flag string by a byte search. Nothing is copied from another unit.

symsrc is either
  - a symbol extract of an unstripped twin of the image, written by extract_twin_syms.py: one tab-separated line
    `<name> 0x<start> <size>` per STT_FUNC symbol of the twin that this script looks up, below `#` header
    lines that name the twin's and the image's sha256. extract_twin_syms.py checks that the twin's PT_LOAD file bytes
    equal the image's; this script checks that the image's sha256 is the image sha256 the extract names; or
  - a cgif-form function table lib/A/AB1w.v / lib/YB1w.v (text with `Definition tfib_A_<name> : Z := 0x..` and
    `tfib_E_<name>` pairs), used for cgif itself, which has no twin.

This version differs from the frozen atable.py b9aa677211b7 only there: b9aa677211b7 read the twin ELF itself and made
the PT_LOAD check here; this version reads the twin's symbols from the extract. The emitted text is the same.

Python 3 stdlib only.
"""
import hashlib
import re
import struct

# field -> (ELF symbol of the twin, AB1w name, offset in bytes from the symbol's start). The offsets were measured
# on cgif_file_fuzzer (asan and asan-ubsan alike) and hold for every image whose runtime function is the same code
# up to address immediates; emit() checks the offset lies inside the symbol and that the word there is an
# instruction of the RV64 base opcodes.
CODE_SPEC = [
    ('a_entry', '_start', 'start', 0),
    ('x_imemset', '__sanitizer_internal_memset', 'internal_memset', 0),
    ('x_imemcpy', '__sanitizer_internal_memcpy', 'internal_memcpy', 0),
    ('x_memset', 'memset', 'musl_memset', 0),
    ('x_memcpy', 'memcpy', 'musl_memcpy', 0),
    ('x_memiszero', '_ZN11__sanitizer11mem_is_zeroEPKcm', 'mem_is_zero', 0),
    ('x_istrncpy', '_ZN11__sanitizer16internal_strncpyEPcPKcm', 'internal_strncpy', 0),
    ('x_popfree', '_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17Populate'
                  'FreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm',
     'SizeClassAllocator64_PopulateFreeArray', 444),
    ('x_envscan', '__init_libc', 'init_libc', 56),
    ('x_envscan_k', '__init_libc', 'init_libc', 68),
    ('x_pnscan', '__init_libc', 'init_libc', 252),
    ('x_pnscan_k', '__init_libc', 'init_libc', 264),
]
# stops_more, in cgif's order.
STOP_SPEC = [
    ('_ZN11__sanitizer29SealedHangOnAllocationFailureEv', 'DieOnMapFailure_sealed', 36),
    ('_ZN11__sanitizer15QuarantineCacheIN6__asan18QuarantineCallbackEE7EnqueueES2_Pvm', 'QuarantineCache_Enqueue', 400),
    ('_ZN6__asan12PoisonShadowEmmh', 'PoisonShadow', 1188),
    ('_ZN6__asan19SealedReserveShadowEv', 'ReserveShadowMemoryRanges_sealed_early_shadow_re', 432),
    ('_ZN6__asan19SealedReserveShadowEv', 'ReserveShadowMemoryRanges_sealed_early_shadow_re', 452),
    ('_ZN6__asan19SealedReserveShadowEv', 'ReserveShadowMemoryRanges_sealed_early_shadow_re', 472),
    ('_ZN11__sanitizer23ReportMmapFailureAndDieEmPKcS1_ib', 'ReportMmapFailureAndDie', 48),
    ('_ZN11__sanitizer25ReportMunmapFailureAndDieEPvmib', 'ReportMunmapFailureAndDie', 40),
    ('_ZN11__sanitizer16MapDynamicShadowEmmmRmm', 'MapDynamicShadow_MmapAlignedOrDieOnFatalError', 344),
    ('_ZN11__sanitizer18MmapFixedNoReserveEmmPKc', 'MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve', 196),
    ('_ZN11__sanitizer20ReservedAddressRange4InitEmPKcm', 'MmapNoAccess_ReservedAddressRange_Init', 196),
    ('_ZN11__sanitizer18InternalSymbolizer5FlushEv', 'thunk_77ab0', 0),
]
SEALED = b'<sealed>\x00'            # x_sealed: the rodata string the sealed-runtime flag parser compares against
SHADOW_OFF = 0x7fff8000             # the ASan RV64 shadow offset (runtime constant)
RV_OPCODES = {0x03, 0x07, 0x0f, 0x13, 0x17, 0x1b, 0x23, 0x27, 0x2f, 0x33, 0x37, 0x3b, 0x43, 0x47, 0x4b, 0x4f, 0x53,
              0x63, 0x67, 0x6f, 0x73}


class Elf:
    def __init__(self, path):
        self.path = path
        self.b = open(path, 'rb').read()
        b = self.b
        if b[:4] != b'\x7fELF' or b[4] != 2 or b[5] != 1:
            raise ValueError(f'{path}: not an ELF64 little-endian file')
        self.entry, self.phoff, self.shoff = struct.unpack_from('<QQQ', b, 0x18)
        self.phentsize, self.phnum, self.shentsize, self.shnum, self.shstrndx = struct.unpack_from('<HHHHH', b, 0x36)
        self.loads = []
        for i in range(self.phnum):
            pt, pf, off, va, pa, fs, ms, al = struct.unpack_from('<IIQQQQQQ', b, self.phoff + i * self.phentsize)
            if pt == 1:
                self.loads.append((va, off, fs, ms, pf))
        self.sections = {}
        raw = []
        if self.shnum:
            raw = [struct.unpack_from('<IIQQQQIIQQ', b, self.shoff + i * self.shentsize) for i in range(self.shnum)]
            so = raw[self.shstrndx][4]
            for r in raw:
                name = b[so + r[0]:b.index(b'\0', so + r[0])].decode()
                self.sections.setdefault(name, r)
        self.symbols = {}
        if '.symtab' in self.sections:
            st = self.sections['.symtab']
            strtab = raw[st[6]]                                     # sh_link: the symbol table's string table
            for j in range(st[5] // 24):
                nm, info, oth, shn, val, sz = struct.unpack_from('<IBBHQQ', b, st[4] + j * 24)
                if (info & 0xf) == 2 and val:                       # STT_FUNC
                    n = b[strtab[4] + nm:b.index(b'\0', strtab[4] + nm)].decode()
                    self.symbols.setdefault(n, (val, sz))

    def read(self, va, n):
        for v0, off, fs, ms, pf in self.loads:
            if v0 <= va and va + n <= v0 + fs:
                return self.b[off + va - v0:off + va - v0 + n]
        return None

    def va_of_offset(self, off):
        for v0, o, fs, ms, pf in self.loads:
            if o <= off < o + fs:
                return v0 + off - o
        return None

    def load_bytes(self):
        """PT_LOAD file bytes with the ELF header (its section-table fields change on strip) and the GNU build-id
        note masked: a stripped image and its unstripped twin must agree everywhere else."""
        b = bytearray(self.b)
        b[0:64] = bytes(64)
        note = self.sections.get('.note.gnu.build-id')
        if note is not None:
            b[note[4]:note[4] + note[5]] = bytes(note[5])
        return [bytes(b[off:off + fs]) for v0, off, fs, ms, pf in self.loads]


def _ab1w_table(text):
    a, e = {}, {}
    for k, n, v in re.findall(r'Definition tfib_([AE])_(\w+) : Z := (0x[0-9a-fA-F]+)\.', text):
        (a if k == 'A' else e)[n] = int(v, 16)
    return {n: (a[n], e[n] - a[n]) for n in a if n in e}


def _extract_table(text):
    """(image sha256, {name: (start, size)}) of a symbol extract written by extract_twin_syms.py."""
    pin, table = None, {}
    for line in text.splitlines():
        if line.startswith('#'):
            m = re.fullmatch(r'# pin sha256 ([0-9a-f]{64})', line)
            if m:
                pin = m.group(1)
            continue
        n, start, size = line.split('\t')
        table.setdefault(n, (int(start, 16), int(size)))
    if pin is None:
        raise ValueError('symbol extract: no "# pin sha256" header line')
    return pin, table


class SymSource:
    """Symbol lookup: name -> (start, size), from a twin's symbol extract or a cgif-form AB1w.v text."""

    def __init__(self, symsrc, image):
        if symsrc.endswith('.v'):
            self.kind = 'ab1w'
            self.table = _ab1w_table(open(symsrc).read())
            self.desc = symsrc
        else:
            pin, table = _extract_table(open(symsrc).read())
            if pin != hashlib.sha256(image.b).hexdigest():
                raise ValueError(f'symbol extract {symsrc}: it names image sha256 {pin}, not that of {image.path}')
            self.kind = 'extract'
            self.table = table
            self.desc = symsrc

    def lookup(self, elfname, ab1wname):
        name = ab1wname if self.kind == 'ab1w' else elfname
        if name not in self.table:
            raise KeyError(f'symbol {name!r} not in {self.desc}')
        return name, self.table[name]


def _page_up(x):
    return (x + 0xfff) & ~0xfff

# TFIB_TEXT_LO / TFIB_TEXT_N: the word range the donor's released atable states, carried into this image.
# It is NOT the whole .text: cgif's own A/AB12.v states 111012 words from 0x302dc (end 0x9c96c) where
# cgif_file_fuzzer.asan's .text holds 111048 (end 0x9c9fc), and its YB12.v states 111037 from 0x3030c (end
# 0x9ca00) where .text holds 111193 (end 0x9cc70) - two different tails, so no section-derived rule reproduces
# the donor's two numbers. The rule that does: the END is the donor's end address RELOCATED into this image by
# the code around it, and N = (that address - TFIB_TEXT_LO) / 4.
TEXT_KMIN = 8                       # words of context that must still agree at the matched end
TEXT_KMAX = 64


def _norm_word(w):
    """A text word with its pc-relative immediate masked out: jal / branch / auipc / lui keep only their
    opcode and destination (or funct3 + registers), so the same instruction at a different address compares
    equal between two images."""
    op = w & 0x7f
    if op in (0x6f, 0x17, 0x37):                    # jal, auipc, lui: keep rd
        return op | (w & 0xf80)
    if op == 0x63:                                  # branch: keep funct3, rs1, rs2
        return op | (w & 0x1ff8000) | (w & 0x7000)
    return w


def _text_words(img):
    """(lo, [words]) of the image's executable range: .text, or the executable PT_LOAD when stripped of
    section headers."""
    sec = img.sections.get('.text')
    if sec is not None:
        lo, off, size = sec[3], sec[4], sec[5]
    else:
        exe = [l for l in img.loads if l[4] & 1]
        if len(exe) != 1:
            raise ValueError(f'{img.path}: expected exactly one executable PT_LOAD, found {len(exe)}')
        lo, off, size = exe[0][0], exe[0][1], exe[0][2]
    if size % 4 or lo % 4:
        raise ValueError(f'{img.path}: text range {lo:#x}+{size:#x} is not word-aligned')
    return lo, [struct.unpack_from('<I', img.b, off + i)[0] for i in range(0, size, 4)]


def text_range(img, donor):
    """((TFIB_TEXT_LO, source), (TFIB_TEXT_N, source)) for this image, anchored on the donor's released pair.
    donor = (donor image path, donor TFIB_TEXT_LO, donor TFIB_TEXT_N). The donor's end address is located in
    this image by matching the K words before it with their pc-relative immediates masked; the match must be
    unique at some K in [TEXT_KMIN, TEXT_KMAX] and present at every shorter K, else the run REFUSES. Run on
    the donor's own image the rule is the identity."""
    lo, words = _text_words(img)
    if lo != img.entry:
        raise ValueError(f'{img.path}: text start {lo:#x} differs from e_entry {img.entry:#x}')
    if donor is None:
        raise ValueError('TFIB_TEXT_N needs --donor-image and the donor pair (--donor-atable or '
                         '--donor-text): the donor value is not a function of this image alone')
    dpath, dlo, dn = donor
    dimg = Elf(dpath)
    dtlo, dwords = _text_words(dimg)
    if dlo != dtlo:
        raise ValueError(f'donor TFIB_TEXT_LO {dlo:#x} is not {dpath}\'s text start {dtlo:#x}')
    dend = dlo + 4 * dn
    if not dlo < dend <= dtlo + 4 * len(dwords):
        raise ValueError(f'donor end {dend:#x} is outside {dpath}\'s text')
    di = (dend - dtlo) // 4
    seq = [_norm_word(w) for w in words]
    pat = [_norm_word(w) for w in dwords[:di]]
    hits = {}
    for k in range(TEXT_KMIN, min(TEXT_KMAX, di) + 1):
        p = pat[di - k:]
        hits[k] = [lo + 4 * (i + k) for i in range(len(seq) - k + 1) if seq[i:i + k] == p]
    unique = [k for k in hits if len(hits[k]) == 1]
    if not unique:
        raise ValueError(f'donor text end {dend:#x} does not match {img.path} uniquely at any context of '
                         f'{TEXT_KMIN}..{TEXT_KMAX} words (hits: '
                         f'{ {k: [hex(h) for h in v] for k, v in hits.items()} })')
    kstar = max(unique)
    end = hits[kstar][0]
    for k in range(TEXT_KMIN, kstar + 1):
        if end not in hits[k]:
            raise ValueError(f'the match at {end:#x} ({kstar} words of context) is not a match at {k} words')
    if (end - lo) % 4:
        raise ValueError(f'matched end {end:#x} is not {lo:#x} + 4k')
    src = (f'donor {dpath.rsplit("/", 1)[-1]} end {dend:#x} relocated to {end:#x} '
           f'({kstar} words of masked context, unique)')
    return (lo, 'text start (= e_entry)'), ((end - lo) // 4, f'({end:#x} - {lo:#x}) / 4; {src}')


def fields(image_path, symsrc, donor=None):
    """Every atable value with its source: {field: (value, source text)}; 'stops_more' maps to a list of pairs.
    donor: (donor image path, donor TFIB_TEXT_LO, donor TFIB_TEXT_N) - REQUIRED for TFIB_TEXT_LO / TFIB_TEXT_N
    (see text_range)."""
    img = Elf(image_path)
    syms = SymSource(symsrc, img)
    if len(img.loads) < 2:
        raise ValueError('expected at least two PT_LOAD segments')
    first, last = img.loads[0], img.loads[-1]
    img_lo = first[0]
    img_hi = _page_up(last[0] + last[3])
    rw_lo = last[0] & ~0xfff
    out = {
        'img_lo': (img_lo, 'first PT_LOAD vaddr'),
        'img_hi': (img_hi, 'page_up(last PT_LOAD vaddr + memsz)'),
        'n_res': (len(img.loads), 'number of PT_LOAD'),
        'shadow_off': (SHADOW_OFF, 'ASan RV64 shadow offset'),
        'rw_lo': (rw_lo, 'page_down(last PT_LOAD vaddr)'),
        'rw_len': (img_hi - rw_lo, 'img_hi - rw_lo'),
        'ph_addr_z': (img_lo + img.phoff, 'img_lo + e_phoff'),
        'ph_ent_z': (img.phentsize, 'e_phentsize'),
        'ph_num_z': (img.phnum, 'e_phnum'),
    }
    for f, elfn, ab1wn, off in CODE_SPEC:
        out[f] = _code(img, syms, elfn, ab1wn, off)
    if out['a_entry'][0] != img.entry:
        raise ValueError(f"a_entry {out['a_entry'][0]:#x} (from the symbol) differs from e_entry {img.entry:#x}")
    hits = [m.start() for m in re.finditer(re.escape(SEALED), img.b)]
    if len(hits) != 1:
        raise ValueError(f'expected exactly one {SEALED!r} in the image, found {len(hits)}')
    out['x_sealed'] = (img.va_of_offset(hits[0]), 'rodata string "<sealed>\\0" (byte search, unique)')
    for f in ('x_sniff', 'sniff_tab', 'sniff_cell'):
        out[f] = (0, 'no sniff summary for this image (cgif form: 0)')
    out['stops_more'] = [_code(img, syms, elfn, ab1wn, off) for elfn, ab1wn, off in STOP_SPEC]
    out['TFIB_TEXT_LO'], out['TFIB_TEXT_N'] = text_range(img, donor)
    return out


def _code(img, syms, elfn, ab1wn, off):
    name, (start, size) = syms.lookup(elfn, ab1wn)
    if size and not (0 <= off < size):
        raise ValueError(f'{name}+{off}: offset outside the symbol (size {size})')
    w = img.read(start + off, 4)
    if w is None:
        raise ValueError(f'{name}+{off} = {start + off:#x} is not in a loaded segment')
    word = int.from_bytes(w, 'little')
    if (word & 3) != 3 or (word & 0x7f) not in RV_OPCODES:
        raise ValueError(f'{name}+{off} = {start + off:#x}: word {word:#010x} is not an RV64 base instruction')
    return start + off, f'{name}+{off}'


def _hx(v):
    return f'{v:#x}'


def emit(image, symsrc, side, unit, donor=None):
    """The whole AB12.v (side 'A') / YB12.v (side 'B') text. unit: {'prefix': 'OssFuzzTheorems.Proofs.<p>.<h>.lib',
    'header': [comment lines, each a full line], 'reusable': '' or '.Reusable' (where YZ00 / YK09 live),
    optional 'img_names': (LO, TOP), qualified names of the unit's image range (e.g. ('YImgTop.IMG_LO',
    'YImgTop.IMG_TOP'), defined in <lib>.<module of the names>): img_lo / img_hi are then written as those names, and two
    lemmas check by reflexivity that the names equal the values computed from this image. Without it: literals.}"""
    if side not in ('A', 'B'):
        raise ValueError("side must be 'A' or 'B'")
    f = fields(image, symsrc, donor)
    lib = unit['prefix'] + unit.get('reusable', '')
    v = {k: x[0] for k, x in f.items() if k != 'stops_more'}
    stops = '; '.join(_hx(s[0]) for s in f['stops_more'])
    names = unit.get('img_names')
    lo_txt, hi_txt = (names if names else (_hx(v['img_lo']), _hx(v['img_hi'])))
    lines = list(unit.get('header', []))
    lines += [
        f'From {lib} Require YZ00.',
        'From Stdlib Require Import ZArith List.',
        f'From {lib} Require Import YK09.',
    ]
    if names:
        mods = sorted({n.rsplit('.', 1)[0] for n in names})
        lines.append(f"From {lib} Require {' '.join(mods)}.")
    lines += [
        'Unset Lia Cache. Unset Nia Cache.',
        'Import ListNotations. Import APC.',
        'Open Scope Z_scope.',
        'Definition TFIB : atable :=',
        f"{{| img_lo := {lo_txt}; img_hi := {hi_txt}; n_res := {v['n_res']}; "
        f"shadow_off := {_hx(v['shadow_off'])};",
        f"a_entry := {_hx(v['a_entry'])}; rw_lo := {_hx(v['rw_lo'])}; rw_len := {_hx(v['rw_len'])}; "
        f"ph_addr_z := {_hx(v['ph_addr_z'])}; ph_ent_z := {v['ph_ent_z']}; ph_num_z := {v['ph_num_z']};",
        f"x_imemset := {_hx(v['x_imemset'])}; x_imemcpy := {_hx(v['x_imemcpy'])}; x_memset := {_hx(v['x_memset'])}; "
        f"x_memcpy := {_hx(v['x_memcpy'])}; x_memiszero := {_hx(v['x_memiszero'])};",
        f"x_istrncpy := {_hx(v['x_istrncpy'])}; x_sealed := {_hx(v['x_sealed'])}; x_popfree := {_hx(v['x_popfree'])};",
        f"x_sniff := {v['x_sniff']}; sniff_tab := {v['sniff_tab']}; sniff_cell := {v['sniff_cell']};",
        f"x_envscan := {_hx(v['x_envscan'])}; x_envscan_k := {_hx(v['x_envscan_k'])}; "
        f"x_pnscan := {_hx(v['x_pnscan'])}; x_pnscan_k := {_hx(v['x_pnscan_k'])};",
        f'stops_more := [{stops}]',
        '|}.',
        f"Definition TFIB_TEXT_LO : Z := {_hx(v['TFIB_TEXT_LO'])}.",
        f"Definition TFIB_TEXT_N : nat := {v['TFIB_TEXT_N']}.",
    ]
    if names:
        lines += [
            f"Lemma TFIB_img_lo_val : img_lo TFIB = {_hx(v['img_lo'])}.",
            'Proof. reflexivity. Qed.',
            f"Lemma TFIB_img_hi_val : img_hi TFIB = {_hx(v['img_hi'])}.",
            'Proof. reflexivity. Qed.',
        ]
    return '\n'.join(lines) + '\n'


def _donor_pair(atable_path):
    """(TFIB_TEXT_LO, TFIB_TEXT_N) read from a released donor AB12.v / YB12.v."""
    t = open(atable_path).read()
    lo = re.search(r'Definition TFIB_TEXT_LO : Z := (0x[0-9a-fA-F]+)\.', t)
    n = re.search(r'Definition TFIB_TEXT_N : nat := (\d+)\.', t)
    if not lo or not n:
        raise ValueError(f'{atable_path}: no TFIB_TEXT_LO / TFIB_TEXT_N')
    return int(lo.group(1), 16), int(n.group(1))


if __name__ == '__main__':
    import argparse
    import json
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('image')
    ap.add_argument('symsrc')
    ap.add_argument('--side', choices=['A', 'B'], default='A')
    ap.add_argument('--prefix', required=True, help='e.g. OssFuzzTheorems.Proofs.libreac.fuzz_knock.lib')
    ap.add_argument('--reusable', default='', help="'.Reusable' when YZ00 / YK09 live under lib/Reusable")
    ap.add_argument('--fields', action='store_true', help='print the field table (value + source) as JSON instead')
    ap.add_argument('--img-names', default='', help="LO,TOP: write img_lo / img_hi as these qualified names "
                    "(e.g. YImgTop.IMG_LO,YImgTop.IMG_TOP), with reflexivity checks against the image's values")
    ap.add_argument('--donor-image', required=True, help="the donor's own pinned image (cgif_file_fuzzer.asan "
                    'for side A, .asan-ubsan for side B): TFIB_TEXT_N is its released end relocated here')
    ap.add_argument('--donor-atable', help="the donor's released AB12.v / YB12.v (its TFIB_TEXT_LO / _N)")
    ap.add_argument('--donor-text', help='LO,N instead of --donor-atable (LO hex, N decimal)')
    ap.add_argument('--header', help='a file whose lines are written above the Requires (the provenance comments)')
    a = ap.parse_args()
    if a.donor_atable:
        dlo, dn = _donor_pair(a.donor_atable)
    elif a.donor_text:
        s_lo, s_n = a.donor_text.split(',')
        dlo, dn = int(s_lo, 16), int(s_n)
    else:
        ap.error('--donor-atable or --donor-text is required with --donor-image')
    donor = (a.donor_image, dlo, dn)
    if a.fields:
        fs = fields(a.image, a.symsrc, donor)
        print(json.dumps({k: ([[_hx(x), s] for x, s in v] if k == 'stops_more' else [v[0] if isinstance(v[0], int)
                          and v[0] < 4096 else _hx(v[0]), v[1]]) for k, v in fs.items()}, indent=1))
    else:
        unit = {'prefix': a.prefix, 'reusable': a.reusable}
        if a.img_names:
            unit['img_names'] = tuple(a.img_names.split(','))
        if a.header:
            unit['header'] = open(a.header).read().splitlines()
        print(emit(a.image, a.symsrc, a.side, unit, donor), end='')
