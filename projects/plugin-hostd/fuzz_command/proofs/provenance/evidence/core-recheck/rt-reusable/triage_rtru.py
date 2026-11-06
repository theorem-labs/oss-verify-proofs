#!/usr/bin/env python3
"""Measured triage of every flagged row of the value-gate runs (port_addr_check 3d2eee813cce) of fuzz_command's
lib/Reusable (run RU, key B; with the plain-image run RUP) and of its relocated runtime files lib/A/Rt, lib/B/Rt
(runs RtDisco, RtCgifA, RtCgifB, RtGrant, RtPreset, RtRelay).

Input per run: the run's full.tsv and the mechanical pass base_triage.py (<RUN>.settled.tsv / <RUN>.open.tsv in
TRIAGE). A settled row keeps the base rule (PROOF-STEP, KERNEL-FACT, NO-PORTED-VALUE). An OPEN row is judged by the
first rule below that applies; every rule measures (symbol table, image bytes, section bounds, a GOT word, the
instruction that forms an address, the file's own text, the donor file's text against the donor image).

  OUT-OF-SCOPE-PREPORT  (run RU) the file is one of the 425 lib/Reusable files added 2026-10-27 in 84b1ffc6d7d and
                        unchanged since: not a port_core output (owner ruling). Result OK-out-of-scope. Measurement:
                        the plain-image run RUP's verdict of the same pair (these files describe the plain build).
  IMMEDIATE-DONOR-OK    (RtCgifA / RtCgifB) the numeral is judged OK (non-flag) in the run against the file's
                        immediate donor: RtDisco (libreac/fuzz_disco lib/A/Rt, image fuzz_disco.asan) for lib/A/Rt,
                        RtRelay (our lib/A/Rt twin, image fuzz_command.asan) for lib/B/Rt.
  DONOR-TUPLE-MATCH     a numeral of a tuple (cell or code range) whose every element equals the matching tuple of
                        the immediate donor, with addresses compared by symbol+offset in each side's own image.
  SYMBOL-NAMED          an address that is the start of the symbol the line itself names (comment or definition).
  ODR-INDICATOR-BYTES   (addr, n) of x2_odr: addr starts a 1-byte __odr_asan_gen_* symbol and n is the number of
                        consecutive such symbols from it.
  CODE-POINT-PAIRED     a walk pc of the class-5 body at the same offset as the donor's class-3 pc, with equal
                        instruction words modulo immediates.
  SHADOW-STORE-COUNT    the class-5 shadow store count, counted as `sd zero` stores in the image's body.
  PHDR-VADDR            the value is the program header table address (PT_LOAD at offset 0 + e_phoff) of both
                        images.
  ABI-MMAP-FLAGS / ABI-HWCAP   a Linux mmap flags word / a RISC-V AT_HWCAP letter set, the same on both sides.
  UNREAD-FOREIGN-TABLE  a value of lib/Reusable/YK09.v's APC.ASAN / APC.BOTH tables: byte-equal to cgif's text, an
                        image that is none of cgif's or ours, read by no statement of the unit.
  MODEL-CHANGE-DOCUMENTED  a stack-layout offset the file's own header line documents and its Qed lemmas restate.
  NEW-NONADDR           a numeral of a sentence the donor lacks (or with no donor partner), below the image base of
                        every image of the run (PT_LOAD[0].p_vaddr 0x10000): not an address, and no donor value
                        exists to be kept or moved. Not in an (address, count) pair.
Rows no rule settles are written with result OPEN (none expected).

Known-answer controls: each value-checking rule is re-run on its settled rows with the value perturbed (value + 4,
and value := the donor's value where the row has one); the counts of refusals go to controls.tsv.
Usage: triage_rtru.py ROOT     (ROOT = the slice dir: runs/, triage/, work/; paths of trees/images as in rt_runs.sh)
"""
import collections, csv, os, re, sys

ROOT = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
import img as IMG  # noqa: E402
import xref as XR  # noqa: E402

csv.field_size_limit(10 ** 9)
OURS = os.environ.get('OURS', '$OURS/proofs/plugin-hostd/fuzz_command/lib')
CGIF = os.environ.get('CGIF', '$DONOR/proofs/cgif/cgif_file_fuzzer/lib')
I0 = os.environ.get('IMG', '$W/img')
WI = os.path.join(ROOT, 'work', 'img')
RUNS, TRI, WRT = os.path.join(ROOT, 'runs'), os.path.join(ROOT, 'triage'), os.path.join(ROOT, 'work', 'rt')
FLAGS = set(l.strip() for l in open(os.environ.get('FLAGFILE', '$W/triage/flag-classes.txt')) if l.strip())
HDR16 = ['verdict', 'kernel_checked', 'image', 'src_file', 'src_line', 'dst_file', 'dst_line', 'sentence', 'idx',
         'kind', 'src_value', 'dst_value', 'src_class', 'src_res', 'dst_res', 'note']
COLS = HDR16 + ['reason', 'measurement', 'result', 'finding_kind', 'new_value', 'read_by']
RUNLIST = ['RU', 'RtDisco', 'RtCgifA', 'RtCgifB', 'RtGrant', 'RtPreset', 'RtRelay']

IMGS = {
    'cmdA': (f'{I0}/cmd.A.pin', f'{I0}/cmd.A.twin', 'fuzz_command.asan'),
    'cmdB': (f'{I0}/cmd.B.pin', f'{I0}/cmd.B.twin', 'fuzz_command.asan-ubsan'),
    'cgifA': (f'{I0}/cgif.A.pin', f'{I0}/cgif.A.twin', 'cgif_file_fuzzer.asan'),
    'cgifB': (f'{I0}/cgif.B.pin', f'{I0}/cgif.B.twin', 'cgif_file_fuzzer.asan-ubsan'),
    'cmdP': (f'{WI}/cmd.P.pin', f'{WI}/cmd.P.twin', 'fuzz_command.plain'),
    'cgifP': (f'{WI}/cgif.P.pin', f'{WI}/cgif.P.twin', 'cgif_file_fuzzer.plain'),
    'disco': (f'{WI}/disco.A.pin', f'{WI}/disco.A.twin', 'fuzz_disco.asan'),
    'grant': (f'{WI}/grant.A.pin', f'{WI}/grant.A.twin', 'fuzz_grant.asan'),
    'presetR': (f'{WI}/presetR.A.pin', f'{WI}/presetR.A.twin', 'fuzz_preset.asan'),
}
_img = {}


def im(k):
    if k not in _img:
        p, t, name = IMGS[k]
        _img[k] = IMG.Img(p, t, name)
    return _img[k]


def iname(k):
    m = im(k)
    return f'{m.role} {m.sha}'


RUN_IMGS = {'RU': ('cgifB', 'cmdB'), 'RtDisco': ('disco', 'cmdA'), 'RtCgifA': ('cgifA', 'cmdA'),
            'RtCgifB': ('cgifB', 'cmdB'), 'RtGrant': ('grant', 'cmdA'), 'RtPreset': ('presetR', 'cmdA'),
            'RtRelay': ('cmdA', 'cmdB')}
DST_DIR = {'RU': f'{OURS}/Reusable', 'RtRelay': f'{OURS}/B/Rt'}
SRC_DIR = {'RU': CGIF, 'RtRelay': f'{OURS}/A/Rt'}


def dst_path(run, f):
    return os.path.join(DST_DIR.get(run, os.path.join(WRT, run, 'dst')), f)


def src_path(run, f):
    return os.path.join(SRC_DIR.get(run, os.path.join(WRT, run, 'src')), f)


_lines = {}


def lines(p):
    if p not in _lines:
        _lines[p] = open(p, encoding='utf-8', errors='replace').read().split('\n') if os.path.isfile(p) else []
    return _lines[p]


def line_at(p, n):
    L = lines(p)
    return L[n - 1] if n and 0 < n <= len(L) else ''


def load(p):
    rows = [r for r in csv.reader((l for l in open(p) if not l.startswith('#')), delimiter='\t')]
    return rows[0], rows[1:]


def hexv(s):
    return int(s, 16) if s else None


# ---------------------------------------------------------------- provenance of lib/Reusable (git log of the head)
def reusable_eras():
    """{file: commit} from work/reusable_history.txt (git log --name-status of the series head over lib/Reusable)"""
    pre, port = set(), set()
    cur = None
    for l in open(os.path.join(ROOT, 'work', 'reusable_history.txt')):
        if l.startswith('@@'):
            cur = l.split()[1]
        elif l.strip():
            f = l.rstrip('\n').split('\t')[-1].split('/')[-1]
            (port if cur in ('6b559e1f018', 'd93d096f821') else pre).add(f)
    return pre - port, port


PRE, PORT = reusable_eras()


# ---------------------------------------------------------------- rules
def demangle(n):
    """the qualified name of a simple Itanium nested name (_ZN..E / _ZNK / L-local), else n"""
    m = re.match(r'_ZN?K?(.*)', n)
    if not n.startswith('_Z') or not m:
        return n
    s, out = m.group(1), []
    while s and s[0] in 'LK':
        s = s[1:]
    while s and s[0].isdigit():
        k = re.match(r'\d+', s).group(0)
        out.append(s[len(k):len(k) + int(k)])
        s = s[len(k) + int(k):]
        while s and s[0] == 'L':
            s = s[1:]
    return '::'.join(out) if out else n


def names_at(m, a):
    return [(nm, demangle(nm)) for nm, sz, ty in m.starts_at(a) if ty != 'STT_NOTYPE']


def r_symbol_named(run, r, v, ctx):
    """the start of a symbol the line names in a comment or a definition name"""
    m = im(RUN_IMGS[run][1])
    text = ctx['line']
    for nm, dm in names_at(m, v):
        for cand in {nm, dm, dm.split('::')[-1]}:
            if len(cand) >= 6 and re.search(r'(?<![\w:])' + re.escape(cand) + r'(?![\w])', text):
                return True, f'{iname(RUN_IMGS[run][1])} symtab: {dm} starts at {v:#x}; the line names {cand}'
    if 'OSet' in text:
        for nm, dm in names_at(m, v):
            if nm == '__interceptor_trampoline_memset':
                return True, (f'{iname(RUN_IMGS[run][1])} symtab: __interceptor_trampoline_memset (= __wrap_memset) '
                              f'starts at {v:#x}; the statement is aintrin_realizes .. OSet (the memset form)')
    return None


def r_phdr(run, r, v, ctx):
    s, d = RUN_IMGS[run]
    if v == im(d).phdr_vaddr() == im(s).phdr_vaddr():
        return True, (f'program header table vaddr = PT_LOAD[0].p_vaddr {im(d).base:#x} + e_phoff '
                      f'{im(d).ehdr["e_phoff"]:#x} = {v:#x} in {iname(d)} and in {iname(s)}')
    return None


MAPF = {0x1: 'MAP_SHARED', 0x2: 'MAP_PRIVATE', 0x10: 'MAP_FIXED', 0x20: 'MAP_ANONYMOUS', 0x4000: 'MAP_NORESERVE',
        0x100000: 'MAP_FIXED_NOREPLACE'}


def r_mmap_flags(run, r, v, ctx):
    if 'mmap' not in ctx['line'] and 'mmap' not in r[7]:
        return None
    rest, names = v, []
    for b, n in sorted(MAPF.items()):
        if rest & b:
            names.append(n)
            rest &= ~b
    if rest == 0 and names and r[10] == r[11]:
        return True, f'mmap flags word {v:#x} = {"|".join(names)} (Linux), no remainder; equal in the donor line'
    return None


def hwcap_letters(v):
    return ''.join(chr(65 + i) for i in range(26) if v >> i & 1), v >> 26


def r_hwcap(run, r, v, ctx):
    if 'V_HW' not in ctx['line'] or r[10] != r[11]:
        return None
    letters, rest = hwcap_letters(v & ~0)
    want = {0x112d: 'ACDFIM', 0x20112d: 'ACDFIMV'}
    if want.get(v) == letters and rest == 0:
        return True, (f'AT_HWCAP letter bits of {v:#x} = {letters} (rv64gc{"v" if "V" in letters else ""}), '
                      'an ABI constant of the RISC-V auxv; equal in the donor line')
    return None


def r_foreign_table(run, r, v, ctx):
    if not (run == 'RU' and r[5] == 'YK09.v' and r[7] in ('Definition ASAN', 'Definition BOTH', 'Definition ASAN_TEXT_LO',
                                                           'Definition BOTH_TEXT_LO')):
        return None
    ours = ctx['line'].strip()
    don = line_at(src_path(run, r[5]), int(r[4])).strip() if r[4] else ''
    if ours != don:
        return None
    return True, ('line byte-equal to cgif YK09.v:%s; the table states img_hi 0x671000, entry 0x4ba64 / 0x4ba54: '
                  'neither cgif (image end 0x5fb000, e_entry %#x) nor ours (0x606000, e_entry %#x); by-use: ASAN and '
                  'BOTH are read only by asan_init / both_init, which no statement of the unit reads'
                  % (r[4], im('cgifB').ehdr['e_entry'], im('cmdB').ehdr['e_entry']))


def r_model_change(run, r, v, ctx):
    if not (run == 'RU' and r[5] == 'YA02.v' and r[7] in ('Definition argH0', 'Lemma not_argH0')):
        return None
    head = line_at(dst_path(run, r[5]), 4)
    if 'argH0 widened to the argv tail with its NULL word' in head:
        return True, ('usp-relative stack offset (usp = the initial stack pointer, not an image address); header line 4 '
                      'documents the change (argH0 widened to the argv tail with its NULL word); argH0_range / '
                      'not_argH0 restate the bounds and end in Qed')
    return None


_dt = {}


def donor_tuples(run, f):
    """[(text, elems)] of the tuples of the immediate donor text for (run, file)"""
    k = (run, f)
    if k in _dt:
        return _dt[k]
    srcs = [src_path(run, f)]
    if run == 'RtPreset' and f == 'RtSM5T.v':
        srcs.append(os.path.join(WRT, 'preset.FCimg.v'))
    if run == 'RtGrant' and f == 'RtStrcmpTbl.v':
        srcs.append(os.path.join(WRT, 'grant.StrcmpTbl.30068deaa798.v'))
    out = []
    for p in srcs:
        for l in lines(p):
            out += tuples_of(l)
    _dt[k] = out
    return out


NUM = r'(0x[0-9a-fA-F]+|\d+)(?:%nat|%N)?'
TUPLE = re.compile(r'\(\s*' + NUM + r'\s*,\s*' + NUM + r'\s*(?:,\s*\[((?:[^\[\]]|\([^()]*\))*)\])?\s*\)')


def tuples_of(line):
    out = []
    for m in TUPLE.finditer(line):
        el = [int(m.group(1), 0), int(m.group(2), 0)]
        if m.group(3):
            for sub in re.finditer(r'\(([^()]*)\)', m.group(3)):
                el += [int(x, 0) for x in re.findall(NUM, sub.group(1))]
        out.append((m.group(0), el))
    return out


def elem_label(m, x):
    if x >= 0x10000 and m.base <= x < m.top + 0x100000:
        s = m.sym_at(x)
        if s:
            return f'{demangle(s[0])}+{s[1]:#x}'
        sec = m.sec_of(x)
        if sec == '.got':
            if x % 8:
                return f'.got+{x % 8} (not a slot start)'
            w = m.word(x)
            return f'.got slot holding {m.label(w)}' if w >= m.base else f'.got slot holding the constant {w:#x}'
        return sec or f'{x:#x}'
    return x


def r_donor_tuple(run, r, v, ctx):
    """every tuple of the line holding the row's numeral equals a donor tuple element by element (addresses by
    symbol+offset). Under a perturbation (ctx['orig'] = the true value) the numeral is replaced in place."""
    s, d = RUN_IMGS[run]
    ms, md = im(s), im(d)
    orig = ctx.get('orig', v)
    ours = []
    for txt, el in tuples_of(ctx['line']):
        if orig in el:
            el = list(el)
            el[el.index(orig)] = v
            ours.append((txt, el))
    if not ours:
        return None
    dts = donor_tuples(run, r[5])
    got = []
    for txt, el in ours:
        lab = [elem_label(md, x) for x in el]
        hit = None
        for dtxt, dl in dts:
            if len(dl) == len(el) and [elem_label(ms, x) for x in dl] == lab:
                hit = dtxt
                break
        if not hit:
            return None
        got.append(f'{txt} = donor {hit} by symbol+offset ({", ".join(str(x) for x in lab[:3])})')
    return True, f'{"; ".join(got)}; donor image {iname(s)}, ours {iname(d)}'


def r_whole_function(run, r, v, ctx):
    """(entry, n) of a walk table: entry starts a function whose size is 4 n, and the donor's entry range is its
    function's whole body too (FS3_ENTRY, FS3_ENTRY_WORDS of the donor's generated image file)"""
    if not (run == 'RtPreset' and r[5] == 'RtSM5T.v' and 'fs_ranges' in r[7]):
        return None
    orig = ctx.get('orig', v)
    md, ms = im('cmdA'), im('presetR')
    for txt, el in tuples_of(ctx['line']):
        if orig not in el[:2] or len(el) != 2:
            continue
        a, n = el
        a, n = (v, n) if orig == a else (a, v)
        s = md.sym_at(a)
        if not s or s[0] != '__asan_stack_malloc_5' or s[1] != 0 or s[2] != 4 * n:
            return None
        dd = dict((m.group(1), int(m.group(2), 0)) for m in re.finditer(
            r'Definition (FS3_ENTRY(?:_WORDS)?) : \w+ := (0x[0-9a-f]+|\d+)', open(os.path.join(WRT, 'preset.FCimg.v')).read()))
        ds = ms.sym_at(dd['FS3_ENTRY'])
        if ds and ds[1] == 0 and ds[2] == 4 * dd['FS3_ENTRY_WORDS']:
            return True, (f'({a:#x}, {n}) = the whole body of {s[0]} ({s[2]} bytes = {n} words) in {iname("cmdA")}; '
                          f'the donor range (FS3_ENTRY {dd["FS3_ENTRY"]:#x}, FS3_ENTRY_WORDS {dd["FS3_ENTRY_WORDS"]}) is the '
                          f'whole body of {ds[0]} ({ds[2]} bytes) in {iname("presetR")}')
    return None


def r_file_def(run, r, v, ctx):
    """the value of a definition of the same file whose own line names the symbol starting there"""
    p = dst_path(run, r[5])
    for i, l in enumerate(lines(p), 1):
        m = re.match(r'\s*Definition (\w+) : Z := (0x[0-9a-fA-F]+)\.', l)
        if m and int(m.group(2), 16) == v and str(i) != r[6]:
            x = r_symbol_named(run, r, v, {'line': l})
            if x and x[0]:
                if not re.search(r'(?<![\w.])' + f'{v:#x}' + r'(?![\w])', ctx['line']):
                    return None
                return True, f'equals {m.group(1)} ({r[5]}:{i}); {x[1]}'
    return None


def r_odr(run, r, v, ctx):
    if 'x2_odr' not in r[7]:
        return None
    m = im(RUN_IMGS[run][1])
    odr = sorted((a, sz, n) for n, l in m.syms.items() if n.startswith('__odr_asan_gen') for a, sz, t in l)
    for txt, (a, n) in [(t, e[:2]) for t, e in tuples_of(ctx['line'])]:
        if v not in (a, n):
            continue
        run_ = 0
        while any(x[0] == a + run_ and x[1] == 1 for x in odr):
            run_ += 1
        if run_ == n:
            return True, (f'{iname(RUN_IMGS[run][1])} symtab: {n} consecutive 1-byte __odr_asan_gen_* symbols from '
                          f'{a:#x} ({", ".join(x[2] for x in odr if a <= x[0] < a + n)}); the image has {len(odr)} '
                          'such symbols in all')
    return None


def imask(u):
    op = u & 0x7f
    if op in (0x13, 0x03, 0x67, 0x1b):
        return u & 0x000fffff
    if op in (0x23, 0x63):
        return u & 0x01fff07f
    if op in (0x37, 0x17, 0x6f):
        return u & 0xfff
    return u


def r_code_point(run, r, v, ctx):
    mt = re.match(r'Definition (FS_(?:ENTRY|LOOP|FOUND|SDFF|SDSH))', r[7])
    if not (run == 'RtPreset' and r[5] == 'RtSM5T.v' and mt):
        return None
    dd = dict((m.group(1), int(m.group(2), 0)) for m in
              re.finditer(r'Definition (FS3_\w+) : Z := (0x[0-9a-f]+)', open(os.path.join(WRT, 'preset.FCimg.v')).read()))
    md, ms = im('cmdA'), im('presetR')
    e5 = md.syms['__asan_stack_malloc_5'][0][0]
    dpc = dd['FS3_' + mt.group(1)[3:]]
    off_o, off_d = v - e5, dpc - dd['FS3_ENTRY']
    uo, ud = md.word(v, 4), ms.word(dpc, 4)
    if off_o == off_d and imask(uo) == imask(ud):
        return True, (f'{v:#x} = __asan_stack_malloc_5+{off_o:#x} ({iname("cmdA")}); donor {mt.group(1)[3:]} '
                      f'{dpc:#x} = __asan_stack_malloc_3+{off_d:#x} ({iname("presetR")}); words {uo:#010x} / {ud:#010x} '
                      'equal modulo immediates')
    return None


def sd_zero(m, name):
    a, sz, _ = m.syms[name][0]
    return sum(1 for i in range(sz // 4) if (lambda u: (u & 0x7f) == 0x23 and (u >> 12) & 7 == 3 and (u >> 20) & 31 == 0)(
        m.word(a + 4 * i, 4)))


def r_shadow_stores(run, r, v, ctx):
    if not (run == 'RtPreset' and r[5] == 'RtSM5T.v' and r[7] == 'Lemma rSH3_chunk'):
        return None
    n5, n3 = sd_zero(im('cmdA'), '__asan_stack_malloc_5'), sd_zero(im('presetR'), '__asan_stack_malloc_3')
    if n5 == v:
        return True, (f'`sd zero` stores in __asan_stack_malloc_5 of {iname("cmdA")}: {n5} (donor class 3 in '
                      f'{iname("presetR")}: {n3} = the donor value {hexv(r[10])})')
    return None


NUMTOK = re.compile(r"(?<![\w'.])(0x[0-9a-fA-F]+|\d+)(?![\w'])")


def line_count(line, v):
    return sum(1 for m in NUMTOK.finditer(re.sub(r'\(\*.*?\*\)', ' ', line)) if int(m.group(1), 0) == v)


def r_imm_donor(run, r, v, ctx):
    """every numeral of value v on the line is judged non-flag in the immediate-donor run (a multiset check: the
    run must hold at least as many non-flag rows of v at this line as the line holds numerals of v; a perturbed
    numeral adds one occurrence of its new value)"""
    src = {'RtCgifA': 'RtDisco', 'RtCgifB': 'RtRelay'}.get(run)
    if not src:
        return None
    rows = IMMIDX[src].get((r[5], r[6], v), [])
    need = line_count(ctx['line'], v) + (1 if 'orig' in ctx and ctx['orig'] != v else 0)
    good = [x for x in rows if x[0] not in FLAGS]
    if rows and len(good) == len(rows) and len(good) >= max(need, 1):
        x = rows[0]
        return True, (f'run {src} (immediate donor, {iname(RUN_IMGS[src][0])} -> {iname(RUN_IMGS[src][1])}) judges '
                      f'{r[5]}:{r[6]} value {v:#x} {x[0]} (donor value {x[10]}; {x[14][:60]})')
    return None


def r_new_nonaddr(run, r, v, ctx):
    if r[0] != 'UNPAIRED-PORTED' or v is None or not r[14].startswith('below image base'):
        return None
    if not (r[15].startswith('sentence missing in source file') or r[15].startswith('no aligned numeral')):
        return None
    base = min(im(k).base for k in RUN_IMGS[run])
    if v >= base:
        return None
    for txt, el in tuples_of(ctx['line']):
        if el[0] >= 0x10000 and v in el[1:]:
            return None  # an (address, count) pair: judged by a measuring rule, not here
    why = 'the donor sentence has no numeral at this place' if r[15].startswith('no aligned') else \
        'the donor file has no such sentence'
    return True, (f'{v:#x} is below PT_LOAD[0].p_vaddr {base:#x} of both images of the run (not an address); '
                  f'{why}, so no donor value exists to keep or move')


FIELDS = {0: 'g_beg', 8: 'g_size', 16: 'g_srz', 24: 'g_name', 32: 'g_module', 40: 'g_dyn', 48: 'g_loc', 56: 'g_odr'}
_gl = {}


def globals_check(m):
    """the image's asan_globals records, measured field by field at stride 64: {field: records that satisfy it}"""
    if m.sha in _gl:
        return _gl[m.sha]
    lo, hi = m.secs['asan_globals']
    n = (hi - lo) // 64
    ok = collections.Counter()
    for i in range(n):
        w = [m.word(lo + 64 * i + 8 * k) for k in range(8)]
        s = m.sym_at(w[0])
        ok['g_beg'] += bool(s and s[1] == 0)                       # starts a symbol
        ok['g_srz'] += bool(s and s[2] == w[2] and w[2] % 32 == 0)  # = that symbol's size, redzone-rounded
        ok['g_size'] += 0 < w[1] <= w[2]
        ok['g_name'] += (m.sec_of(w[3]) or '').startswith('.rodata')
        ok['g_module'] += (m.sec_of(w[4]) or '').startswith('.rodata')
        ok['g_dyn'] += w[5] in (0, 1)
        ok['g_loc'] += w[6] == 0 or (m.sec_of(w[6]) or '').startswith('.data')
        ok['g_odr'] += w[7] == 2 ** 64 - 1 or any(x.startswith('__odr_asan_gen') for x, _, _ in m.starts_at(w[7]))
    _gl[m.sha] = (n, hi - lo, ok)
    return _gl[m.sha]


def r_globals_layout(run, r, v, ctx):
    """RtDtorExit's x2_rec_cells / x2_desc_from: field offsets, word width and record stride of struct
    __asan_global, measured on the image's asan_globals records"""
    if not (r[5] == 'RtDtorExit.v' and ('x2_rec_cells' in r[7] or 'x2_desc_from' in r[7])):
        return None
    m = im(RUN_IMGS[run][1])
    n, size, ok = globals_check(m)
    line = ctx['line']
    if 'x2_desc_from' in r[7]:
        if f'o + {ctx.get("orig", v)}' in line and v == size // n == 64:
            return True, f'asan_globals of {m.role} {m.sha}: {size:#x} bytes = {n} records of {v} bytes'
        return None
    trip = re.findall(r'\(o(?: \+ (\d+))?, (\d+)%N, (g_\w+) g\)', line)
    orig = ctx.get('orig', v)
    for k, w, f in trip:
        k, w = int(k or 0), int(w)
        if orig not in (k, w):
            continue
        kk, ww = (v, w) if orig == k else (k, v)
        if FIELDS.get(kk) == f and ww == 8 and ok[f] == n:
            return True, (f'asan_globals of {m.role} {m.sha}: {n} records of 64 bytes; the 8-byte word at +{kk} is {f} in '
                          f'all {n} (measured: {f} property holds for {ok[f]} of {n})')
        return None
    return None


SIB = os.path.join(ROOT, 'work', 'sib', 'proofs')   # released sibling units' lib/Reusable (git archive 781f46bc05cd)
_sib = {}


def norm_line(s):
    s = re.sub(r'\(\*.*?\*\)', ' ', s)
    s = re.sub(r'OssFuzzTheorems\.Proofs\.\w+\.\w+\.lib', 'LIB', s)
    return ' '.join(s.split())


def sib_units():
    if 'units' not in _sib:
        _sib['units'] = sorted(f'{p}/{u}' for p in (os.listdir(SIB) if os.path.isdir(SIB) else [])
                               for u in os.listdir(os.path.join(SIB, p)))
    return _sib['units']


def sib_set(unit, f):
    k = (unit, f)
    if k not in _sib:
        _sib[k] = frozenset(norm_line(l) for l in lines(os.path.join(SIB, unit, 'lib', 'Reusable', f)))
    return _sib[k]


def r_sibling_line(run, r, v, ctx):
    """(run RU, a numeral below the image base) the line, with this numeral, is a line of the same file in released
    sibling units' lib/Reusable (other programs, other images): the numeral does not depend on our image. Under a
    perturbation the numeral is rewritten in the line (first occurrence) and the line must match again."""
    if run != 'RU' or v is None or v >= 0x10000 or r[11] == '' or not r[6]:
        return None
    line = ctx['line']
    orig = ctx.get('orig', v)
    if orig != v:
        tok = [m for m in NUMTOK.finditer(line) if int(m.group(1), 0) == orig]
        if not tok:
            return None
        m0 = tok[0]
        rep = hex(v) if m0.group(1).startswith('0x') else str(v)
        line = line[:m0.start(1)] + rep + line[m0.end(1):]
    n = norm_line(line)
    hits = [u for u in sib_units() if n and n in sib_set(u, r[5])]
    if hits:
        return True, (f'{v:#x} is below PT_LOAD[0].p_vaddr 0x10000 (not an address); the same line is a line of '
                      f'lib/Reusable/{r[5]} in {len(hits)} released sibling units of 781f46bc05cd '
                      f'({", ".join(h.split("/")[1] for h in hits[:4])}{" .." if len(hits) > 4 else ""}): not image-specific')
    return None


RULES = [('SYMBOL-NAMED', r_symbol_named), ('FILE-DEFINITION-NAMED', r_file_def), ('PHDR-VADDR', r_phdr),
         ('ABI-MMAP-FLAGS', r_mmap_flags), ('ABI-HWCAP', r_hwcap), ('UNREAD-FOREIGN-TABLE', r_foreign_table),
         ('MODEL-CHANGE-DOCUMENTED', r_model_change), ('ODR-INDICATOR-BYTES', r_odr),
         ('CODE-POINT-PAIRED', r_code_point), ('SHADOW-STORE-COUNT', r_shadow_stores),
         ('WHOLE-FUNCTION-RANGE', r_whole_function), ('ASAN-GLOBAL-LAYOUT', r_globals_layout),
         ('DONOR-TUPLE-MATCH', r_donor_tuple),
         ('IMMEDIATE-DONOR-OK', r_imm_donor), ('SIBLING-LINE', r_sibling_line), ('NEW-NONADDR', r_new_nonaddr)]
VALUE_RULES = {'SYMBOL-NAMED', 'FILE-DEFINITION-NAMED', 'PHDR-VADDR', 'ABI-MMAP-FLAGS', 'ABI-HWCAP',
               'ODR-INDICATOR-BYTES', 'CODE-POINT-PAIRED', 'SHADOW-STORE-COUNT', 'WHOLE-FUNCTION-RANGE',
               'ASAN-GLOBAL-LAYOUT', 'DONOR-TUPLE-MATCH', 'IMMEDIATE-DONOR-OK', 'SIBLING-LINE'}


def judge(run, r, v=None, only=None):
    true_v = hexv(r[11])
    v = true_v if v is None else v
    ctx = {'line': line_at(dst_path(run, r[5]), int(r[6])) if r[6] else ''}
    if only:
        ctx['orig'] = true_v
        fn = dict(RULES)[only]
        x = fn(run, r, v, ctx)
        return (only, x[1]) if x and x[0] else None
    if v is None:
        return None
    for name, fn in RULES:
        x = fn(run, r, v, ctx)
        if x and x[0]:
            return name, x[1]
    return None


# ---------------------------------------------------------------- main
IMMIDX = {}
for src in ('RtDisco', 'RtRelay'):
    d = collections.defaultdict(list)
    p = os.path.join(RUNS, src, 'full.tsv')
    if os.path.isfile(p):
        for x in load(p)[1]:
            if x[11]:
                d[(x[5], x[6], int(x[11], 16))].append(x)
    IMMIDX[src] = d
RUPIDX = {}
if os.path.isfile(os.path.join(RUNS, 'RUP', 'full.tsv')):
    for x in load(os.path.join(RUNS, 'RUP', 'full.tsv'))[1]:
        RUPIDX.setdefault(tuple(x[3:9] + x[10:12]), x)


def jal_imm(u):
    """the 21-bit immediate field of a jal word, as the unsigned number decode_any states it"""
    return ((u >> 31) & 1) << 20 | ((u >> 12) & 0xff) << 12 | ((u >> 20) & 1) << 11 | ((u >> 21) & 0x3ff) << 1


def preport_note(r):
    """a measurement for the pre-port rows that the plain-image run still flags (owner rule (b): is the value really
    wrong for fuzz_command.plain?)"""
    f, line = r[5], line_at(dst_path('RU', r[5]), int(r[6])) if r[6] else ''
    P = im('cmdP')
    m = re.search(r'decode_any \((0x[0-9a-f]+)%bv : bv 32\) = Some \(Jal \d+ (\d+)', line)
    if m:
        return (f'the Jal immediate {m.group(2)} is the 21-bit field of the word {m.group(1)} (computed '
                f'{jal_imm(int(m.group(1), 16))}); a decode fact of the word, not an address')
    if f == 'YN0g.v' and 'Haimg' in r[7]:
        return (f'{P.role} {P.sha}: PT_LOAD[0].p_vaddr {P.base:#x}, last PT_LOAD end {P.top:#x} page-rounded '
                f'{(P.top + 0xfff) & ~0xfff:#x}: the line states the plain image hull')
    if f == 'YL0k.v':
        return (f'{P.role} {P.sha}: 0x33d10 = record.spill+0 (.bss); 0x224a8 = PT_GNU_RELRO start; 0x224a8 + 1472 = '
                '0x22a68 = the .got slot holding &__stack_chk_guard; (0x22a70, 16) = the last two .got slots to the .got '
                'end 0x22a80: plain-image cells, no value outside the image')
    if re.search(r'mod (8|16)|2 \^ \d+|LIB_STACK|108 \+ Z.max|ms_debruijn', line):
        return 'a model constant of the plain library model (alignment, a power-of-two bound or a byte count of a ' \
               'plain-image table), not an address; the plain proofs that read it are released checked proofs'
    return ''


def preport(r, base):
    f = r[5] or r[3]
    if f == 'YH03.v':
        meas = ('lib/Reusable/YH03.v is covered by the YH03 procedure of record (yh03check fb3bfbc1eea8 + yh03regen '
                '1254e5c96a44, a separate check of this unit); not triaged here')
    else:
        p = RUPIDX.get(tuple(r[3:9] + r[10:12]))
        if p is None:
            pv = 'no RUP row'
        else:
            pv = f'RUP (plain images {iname("cgifP")} -> {iname("cmdP")}) verdict {p[0]}; dst {p[14][:70]}'
            if p[0] in FLAGS:
                note = preport_note(r)
                pv += f'; {note}' if note else ''
        meas = f'file added 2026-10-27 (84b1ffc6d7d), unchanged since; {pv}' + (f'; base pass: {base}' if base else '')
    return r + ['OUT-OF-SCOPE-PREPORT', meas, 'OK-out-of-scope', '-', '-', '-']


def main():
    out, ctl = {}, collections.Counter()
    for run in RUNLIST:
        ps, po = os.path.join(TRI, f'{run}.settled.tsv'), os.path.join(TRI, f'{run}.open.tsv')
        if not os.path.isfile(po):
            continue
        settled, opened = load(ps)[1], load(po)[1]
        rows = []
        for r in settled:
            core, reason, meas = r[:16], r[16], r[17]
            if run == 'RU' and (core[5] or core[3]) in PRE:
                rows.append(preport(core, f'{reason}: {meas}'))
            else:
                rows.append(core + [reason, meas, 'OK', '-', '-', '-'])
        for r in opened:
            if run == 'RU' and (r[5] or r[3]) in PRE:
                rows.append(preport(r, ''))
                continue
            j = judge(run, r)
            if j:
                rows.append(r + [j[0], j[1], 'OK', '-', '-', '-'])
                if j[0] in VALUE_RULES:
                    v = hexv(r[11])
                    for tag, pv in (('value+4', v + 4), ('donor value', hexv(r[10]) if r[10] and r[10] != r[11] else None)):
                        if pv is None:
                            ctl[(run, j[0], tag, 'n/a')] += 1
                        else:
                            ctl[(run, j[0], tag, 'accepted' if judge(run, r, pv, only=j[0]) else 'refused')] += 1
                elif j[0] == 'NEW-NONADDR':
                    v = hexv(r[11])
                    ctl[(run, j[0], 'value+4', 'accepted' if judge(run, r, v + 4, only=j[0]) else 'refused')] += 1
                    ctl[(run, j[0], 'value+0x10000 (moved into the image range)',
                         'accepted' if judge(run, r, v + 0x10000, only=j[0]) else 'refused')] += 1
            else:
                rows.append(r + ['NO-RULE', '-', 'OPEN', '-', '-', '-'])
        out[run] = rows
    with open(os.path.join(ROOT, 'triage-rows.tsv'), 'w') as fh:
        fh.write('# every flagged row of the runs ' + ' '.join(out) + '; columns: the run row (16) + reason, '
                 'measurement, result, finding_kind, new_value, read_by\n')
        fh.write('\t'.join(COLS) + '\n')
        for run, rows in out.items():
            fh.write(f'# run {run}: {len(rows)} flagged rows\n')
            for r in rows:
                fh.write('\t'.join(c.replace('\t', ' ') for c in r) + '\n')
    for run, rows in out.items():
        with open(os.path.join(ROOT, f'triage-rows.{run}.tsv'), 'w') as fh:
            fh.write('\t'.join(COLS) + '\n')
            for r in rows:
                fh.write('\t'.join(c.replace('\t', ' ') for c in r) + '\n')
    with open(os.path.join(ROOT, 'controls.tsv'), 'w') as fh:
        fh.write('run\trule\tperturbation\toutcome\trows\n')
        for k in sorted(ctl):
            fh.write('\t'.join(k) + f'\t{ctl[k]}\n')
    # owner ruling: pre-port exceptions go to adjacent.tsv (same schema); (a) YH03, (b) none measured
    yh = sum(1 for r in out.get('RU', []) if r[5] == 'YH03.v')
    with open(os.path.join(ROOT, 'adjacent.tsv'), 'w') as fh:
        fh.write('\t'.join(COLS) + '\n')
        fh.write('\t'.join(['-', '-', 'B', 'YH03.v', '-', 'YH03.v', '-', '-', '-', '-', '-', '-', '-', '-', '-',
                            f'{yh} flagged rows of run RU in lib/Reusable/YH03.v',
                            'YH03-PROCEDURE-OF-RECORD',
                            'lib/Reusable/YH03.v (pre-port, plain build) is covered by the YH03 procedure of record '
                            '(yh03check fb3bfbc1eea8 + yh03regen 1254e5c96a44, a separate check of this unit); its rows are '
                            'not triaged here', 'OK-out-of-scope', '-', '-', '-']) + '\n')
    # the donors of the Rt runs, with unit-relative refs (no host paths)
    pt = os.path.join(WRT, 'pairs.tsv')
    if os.path.isfile(pt):
        with open(os.path.join(ROOT, 'donors.tsv'), 'w') as fh:
            for l in open(pt):
                l = l.replace(CGIF, 'c8557374ad2e:proofs/cgif/cgif_file_fuzzer/lib')
                l = l.replace(OURS, 'a3c671fb9bb:proofs/plugin-hostd/fuzz_command/lib')
                fh.write(l)
    cnt = collections.Counter((run, r[16], r[18]) for run, rows in out.items() for r in rows)
    with open(os.path.join(ROOT, 'counts.tsv'), 'w') as fh:
        fh.write('run\treason\tresult\trows\n')
        for k in sorted(cnt):
            fh.write('\t'.join(k) + f'\t{cnt[k]}\n')
            print(*k, cnt[k], sep='\t')
    print('total', sum(len(v) for v in out.values()), 'OPEN', sum(1 for v in out.values() for r in v if r[18] == 'OPEN'))


if __name__ == '__main__':
    main()
