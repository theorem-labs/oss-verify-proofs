#!/usr/bin/env python3
"""repin_check.py -- independent check of a PSnp* restatement/re-pin (commit 17a8581f30c) against the fm restatement
(commit 7e395de08f5).  Read-only.

Inputs: ./repin/{pre/{A,AU,Reusable},fm/A,fmimg/A,preimg/{A,Reusable}} = `git show <sha>:<path>` copies of the files (see
REPIN-CHECK.md), the three unstripped twins below, and ./bytecmp.py (its load / words / cmp / auipc_states are
reused, not its main: the auipc pairing is bytecmp's MUST dataflow, with no distance window).
Prints: sha256 checks, the pin table (every image-range numeral of the PSnp files -> symbol + offset on its image and on
fm.asan), the per-function byte compare, the statement residues (pre vs fm after the AR -> ARx renames), the leaf diffs.
Usage: python3 repin_check.py [pins|funcs|stmts|leaves|all]"""
import sys, os, re, glob, bisect, hashlib, difflib
from elftools.elf.elffile import ELFFile

HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, 'repin')
IMG = {'A': os.environ.get('REPIN_IMG_A', ''),  # unstripped omx-clap-core fuzz_preset.asan
       'B': os.environ.get('REPIN_IMG_B', ''),  # unstripped omx-clap-core fuzz_preset.asan-ubsan
       'F': os.environ.get('REPIN_IMG_F', '')}  # unstripped omx-clap-core fuzz_manifest.asan
PIN = {'A': (os.environ.get('REPIN_PIN_A', ''), 'd83eb25d', 'f0d2e8d40c7e3ed0'),  # pinned fuzz_preset.asan
       'B': (os.environ.get('REPIN_PIN_B', ''), 'f8f98a95', '3b5e1a099b535acf'),  # pinned fuzz_preset.asan-ubsan
       'F': (os.environ.get('REPIN_PIN_F', ''), '0ba7e169', 'fc92e86bee065b5d')}  # pinned fuzz_manifest.asan

# ---- bytecmp.py's load / words / cmp, without running its main ----
_src = open(os.path.join(HERE, 'bytecmp.py')).read().split('\n')
_bc = {}
exec('\n'.join(_src[:[i for i, l in enumerate(_src) if l.startswith('base = {')][0]]), _bc)
bc_words, bc_cmp = _bc['words'], _bc['cmp']
bc_states = _bc['auipc_states']   # the MUST dataflow of bytecmp.py (fbe79ced3ea2): shared, so both agree

# ---- images ----
class Img:
    def __init__(s, p):
        s.e = ELFFile(open(p, 'rb'))
        s.syms = sorted((y['st_value'], y['st_size'], y.name, y['st_info']['type'])
                        for y in s.e.get_section_by_name('.symtab').iter_symbols()
                        if y.name and y['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT', 'STT_NOTYPE', 'STT_TLS')
                        and y['st_value'] > 0 and y['st_shndx'] != 'SHN_UNDEF')
        s.addrs = [x[0] for x in s.syms]
        s.secs = [(x.name, x['sh_addr'], x['sh_size']) for x in s.e.iter_sections() if x['sh_addr'] > 0]
        s.segs = [(g['p_vaddr'], g['p_filesz'], g.data()) for g in s.e.iter_segments() if g['p_type'] == 'PT_LOAD']
        s.byname = {}
        for v, z, n, t in s.syms: s.byname.setdefault(n, []).append((v, z, t))
    def sec(s, a):
        return next((n for n, v, z in s.secs if v <= a < v + z), None)
    def rd(s, a, n):
        return next((d[a - v:a - v + n] for v, fz, d in s.segs if v <= a and a + n <= v + fz), None)
    def res(s, a):
        """symbol + offset: the smallest FUNC/OBJECT containing a; else '(section)'"""
        i = bisect.bisect_right(s.addrs, a); cont = []
        for j in range(i - 1, max(-1, i - 400), -1):
            v, z, n, t = s.syms[j]
            if v <= a < v + z and t in ('STT_FUNC', 'STT_OBJECT', 'STT_TLS'): cont.append((z, v, n))
        if cont:
            z0 = min(c[0] for c in cont); v0 = [c[1] for c in cont if c[0] == z0][0]
            return '%s+%#x' % ('/'.join(sorted({c[2] for c in cont if c[0] == z0 and c[1] == v0})), a - v0)
        return '(%s)' % s.sec(a)
    def fsym(s, n):
        c = [(v, z) for v, z, t in s.byname.get(n, []) if t == 'STT_FUNC' and z > 0]
        return c[0] if c else None

def shas():
    for k, p in IMG.items():
        h = hashlib.sha256(open(p, 'rb').read()).hexdigest()
        pp, pin, twin = PIN[k]
        hp = hashlib.sha256(open(pp, 'rb').read()).hexdigest()
        a = [(g['p_vaddr'], g.data()) for g in ELFFile(open(pp, 'rb')).iter_segments() if g['p_type'] == 'PT_LOAD']
        b = [(g['p_vaddr'], g.data()) for g in ELFFile(open(p, 'rb')).iter_segments() if g['p_type'] == 'PT_LOAD']
        nd = [(hex(v1 + i)) for (v1, d1), (v2, d2) in zip(a, b) for i in range(len(d1)) if d1[i] != d2[i]]
        print('%s twin %s (want %s..) %s | pin %s (want %s) %s | loadable bytes differ at %d bytes, all in the ELF header '
              '[0x10000,0x10040) or .note.gnu.build-id [0x102a8,0x102cc): %s'
              % (k, h[:16], twin, 'OK' if h.startswith(twin) else 'BAD', hp[:8], pin, 'OK' if hp.startswith(pin) else 'BAD',
                 len(nd), all(0x10000 <= int(x, 16) < 0x10040 or 0x102a8 <= int(x, 16) < 0x102cc for x in nd)))

# ---- Coq text ----
def strip_comments(t):
    out = []; i = 0; depth = 0; n = len(t); instr = False
    while i < n:
        if depth == 0 and t[i] == '"': instr = not instr; out.append(t[i]); i += 1; continue
        if not instr and t.startswith('(*', i): depth += 1; out.append('  '); i += 2; continue
        if depth > 0 and t.startswith('*)', i): depth -= 1; out.append('  '); i += 2; continue
        out.append(('\n' if t[i] == '\n' else ' ') if depth > 0 else t[i]); i += 1
    return ''.join(out)
TOK = re.compile(r"0x[0-9a-fA-F]+|[0-9]+|[A-Za-z_][A-Za-z0-9_'.]*[A-Za-z0-9_']|[A-Za-z_]|\S")
def tl(s): return TOK.findall(s)
def cl(p): return strip_comments(open(p).read()).split('\n')
NUMRE = re.compile(r'(?<![A-Za-z0-9_.\'])(0x[0-9a-fA-F]+|\d+)(?![A-Za-z0-9_\'])')
def numerals(p, lo=0x10000, hi=0x700000):
    return [(ln, m.group(1), int(m.group(1), 0)) for ln, line in enumerate(cl(p), 1) for m in NUMRE.finditer(line)
            if lo <= int(m.group(1), 0) < hi]
def sentences(p):
    t = strip_comments(open(p).read()); res = []; buf = []; line = 1; st = None
    for i, c in enumerate(t):
        if c == '\n': line += 1
        if st is None and not c.isspace(): st = line
        buf.append(c)
        if c == '.' and (i + 1 == len(t) or t[i + 1].isspace()):
            s = ''.join(buf).strip()
            if s: res.append((st, s))
            buf = []; st = None
    return res
STMT = ('Definition', 'Fixpoint', 'Inductive', 'Record', 'Lemma', 'Theorem', 'Corollary', 'Fact', 'Remark', 'Let')
CTX = ('Section', 'End', 'Hypothesis', 'Hypotheses', 'Variable', 'Variables', 'Context')
def decls(p):
    out = []
    for ln, s in sentences(p):
        w = s.split()
        if w[0] in STMT: out.append((re.match(r"[A-Za-z0-9_']+", w[1]).group(0), w[0], ln, s))
        elif w[0] in CTX: out.append(('@' + w[0], w[0], ln, s))
    return out

# pre file -> fm file(s) it restates
FMMAP = {'PSnpSnp': ['FMsnprintfSnp'], 'PSnpSvsni': ['FMsnprintfSvsni'], 'PSnpSvsn': ['FMsnprintfSvsn'], 'PSnpSvfi': ['FMsnprintfSvfi'],
         'PSnpGk': ['FMsnprintfGk'], 'PSnpGkit': ['FMsnprintfGk'], 'PSnpGvfi': ['FMsnprintfGvfi'], 'PSnpGvfikit': ['FMsnprintfGvfi'],
         'PSnpGvsn': ['FMsnprintfGvsn'], 'PSnpGvsnkit': ['FMsnprintfGvsn'], 'PSnpGvsni': ['FMsnprintfGvsni'], 'PSnpGvsnikit': ['FMsnprintfGvsni'],
         'PSnpGwrc': ['FMsnprintfGwrc'], 'PSnpGwrcT': ['FMsnprintfGwrcT'], 'PSnpI': ['FMH_Base', 'FMsnprintfI', 'FMsnprintfGI'],
         'PSnpK': ['FMsnprintfK', 'FMsnprintfSk'], 'PSnpVa': ['FMsnprintfVa'], 'PSnpG': ['FMsnprintfG'], 'PSnpGt': ['FMsnprintfGt'],
         'PSnpShared': ['FMsnprintfShared'], 'PSnpSk': ['FMsnprintfSk'], 'PSnpSx': ['FMsnprintfSx'], 'PSnpLeaves': [], 'PSnpRodata': []}
def fmpath(n):
    for d in ('fm/A', 'fmimg/A'):
        p = os.path.join(D, d, n + '.v')
        if os.path.exists(p): return p
IMAGE_FILES = ['PSnpGk', 'PSnpGvfi', 'PSnpGvsn', 'PSnpGvsni', 'PSnpGwrc', 'PSnpGwrcT', 'PSnpI', 'PSnpK', 'PSnpRodata', 'PSnpSnp',
               'PSnpSvfi', 'PSnpSvsn', 'PSnpSvsni', 'PSnpVa']

def align_numbers(fa, fb_lines):
    """numeral pairs (a_val -> b_val) between file a and line list b, by line diff then token diff inside changed hunks"""
    a = cl(fa); b = fb_lines; pairs = {}
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if tag == 'equal':
            for k in range(i1, i2):
                for m in NUMRE.finditer(a[k]):
                    v = int(m.group(1), 0)
                    if 0x10000 <= v < 0x700000: pairs.setdefault(v, set()).add(v)
            continue
        ta = tl(' '.join(a[i1:i2])); tb = tl(' '.join(b[j1:j2]))
        for t2, k1, k2, l1, l2 in difflib.SequenceMatcher(None, ta, tb, autojunk=False).get_opcodes():
            for q in range(k1, k2):
                if re.fullmatch(r'0x[0-9a-fA-F]+|\d+', ta[q]) and 0x10000 <= int(ta[q], 0) < 0x700000:
                    if t2 == 'equal': pairs.setdefault(int(ta[q], 0), set()).add(int(ta[q], 0))
                    elif t2 == 'replace' and k2 - k1 == l2 - l1 and re.fullmatch(r'0x[0-9a-fA-F]+|\d+', tb[l1 + q - k1]):
                        pairs.setdefault(int(ta[q], 0), set()).add(int(tb[l1 + q - k1], 0))
    return pairs

NOT_ADDR = {0x98023: 'instruction word sb zero,0(s3) (622627)', 0x73703: 'instruction word ld a4,0(a4) (472835)',
            0x7b783: 'instruction word ld a5,0(a5) (505731)', 0x140000: "ro_low's bound r_hi <= 0x140000"}
# pairs the line alignment cannot see (declarations moved between files): checked by name in stmts()
EXTRA_FM = {0xa2758: 0x9a638, 0x5fd910: 0x5f4db0, 0x42cc4: 0x41314, 0x46578: 0x45c90, 0x46188: 0x458a0, 0x4560c: 0x44d24,
            0x460d4: 0x457ec, 0x9a63c: 0x91f0c, 0x950a0: 0x8ede0, 0x95250: 0x8ef90, 0x94ce0: 0x8ea20, 0x9a708: 0x91fd8,
            0x5234c: 0x51a64, 0x52348: 0x51a60, 0x42c88: 0x412cc, 0x42cb8: 0x41308, 0x95108: 0x8ee48, 0x951a8: 0x8eee8,
            0x951c8: 0x8ef08}

def pins(I):
    vmap = dict(EXTRA_FM)
    for n in IMAGE_FILES:
        fl = [l for f in FMMAP[n] for l in cl(fmpath(f))]
        for a, s in align_numbers(os.path.join(D, 'pre/A', n + '.v'), fl).items():
            if a in NOT_ADDR: continue
            s = {x for x in s if x != a} or s
            if len(s) == 1:
                fv = next(iter(s))
                if a in vmap and vmap[a] != fv and a not in EXTRA_FM: print('CONFLICT', hex(a), hex(vmap[a]), hex(fv))
                vmap.setdefault(a, fv)
    abmap = {}
    for n in IMAGE_FILES:
        for a, s in align_numbers(os.path.join(D, 'pre/A', n + '.v'), cl(os.path.join(D, 'pre/AU', n + '.v'))).items():
            abmap.setdefault(a, set()).update(s)
    bad = 0
    print('image\tfile:line\tvalue\tpreset sym+off\tfm value\tfm sym+off\tverdict')
    for img, pimg in (('A', 'A'), ('AU', 'B')):
        for n in IMAGE_FILES:
            for ln, s, v in numerals(os.path.join(D, 'pre', img, n + '.v')):
                av = v if img == 'A' else next(k for k, x in abmap.items() if v in x and len(x) == 1)
                if av in NOT_ADDR:
                    print('%s\tlib/%s/%s.v:%d\t%s\t%s\t(same at fm)\t\tOK' % (img, img, n, ln, s, NOT_ADDR[av])); continue
                fv = vmap[av]; r1 = I[pimg].res(v); r2 = I['F'].res(fv)
                if I[pimg].sec(v) == '.got':
                    r1 = '.got cell -> ' + I[pimg].res(int.from_bytes(I[pimg].rd(v, 8), 'little'))
                    r2 = '.got cell -> ' + I['F'].res(int.from_bytes(I['F'].rd(fv, 8), 'little'))
                if av == 0x600000:
                    end = lambda k: (max(g[0] + g[1] for g in [(x['p_vaddr'], x['p_memsz']) for x in I[k].e.iter_segments() if x['p_type'] == 'PT_LOAD']) + 0xfff) & ~0xfff
                    r1 = 'page end of last PT_LOAD = %#x' % end(pimg); r2 = 'page end of last PT_LOAD = %#x' % end('F')
                    ok = end(pimg) == v and end('F') == fv
                else: ok = r1 == r2
                bad += not ok
                print('%s\tlib/%s/%s.v:%d\t%s\t%s\t%#x\t%s\t%s' % (img, img, n, ln, s, r1, fv, r2, 'OK' if ok else 'MISMATCH'))
    print('# mismatches:', bad)

def sx(v, b): return v - (1 << b) if v & (1 << (b - 1)) else v
def targets(base, b):
    """pc-relative targets per word index: jal, and auipc + lo12 (I/S type) whose binding bytecmp's MUST dataflow proves
    (`auipc_states`: a pairing run ends at j / jr / ret and at a branch, a binding reaches a branch target only when every
    path into it carries it, an RVC parcel clears the state, a call clobbers the caller-saved set, no distance window).
    A word that only an indirect jump reaches gets no target: bytecmp's cmp reports such a difference as UNMEASURED."""
    w = bc_words(b); out = {}; st = bc_states(w)
    for i, (o, x, n) in enumerate(w):
        if n != 4: continue
        op = x & 0x7f; rd = (x >> 7) & 31; rs1 = (x >> 15) & 31
        if op == 0x6f:
            out[i] = ('jal', base + o + sx(((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11 | ((x >> 21) & 0x3ff) << 1, 21))
            continue
        if op == 0x17 or st[i] is None or rs1 not in st[i]:
            continue
        hi_i = st[i][rs1]; ho, hx, _ = w[hi_i]
        hi = base + ho + sx(hx >> 12, 20) * 4096
        if op in (0x13, 0x03, 0x67, 0x07):
            out[i] = ('lo12', hi + sx(x >> 20, 12))
        elif op in (0x23, 0x27):
            out[i] = ('lo12s', hi + sx(((x >> 25) << 5) | ((x >> 7) & 31), 12))
    return out
def tcmp(I, i1, a1, i2, a2, n):
    b1 = I[i1].rd(a1, n); b2 = I[i2].rd(a2, n)
    v, c = bc_cmp(b1, b2); t1 = targets(a1, b1); t2 = targets(a2, b2); diff = []; rod = jtab = const = 0
    for i in sorted(set(t1) & set(t2)):
        x1, x2 = t1[i][1], t2[i][1]
        r1, r2 = I[i1].res(x1), I[i2].res(x2)
        if I[i1].sec(x1) == I[i2].sec(x2) == '.got':
            r1 = I[i1].res(int.from_bytes(I[i1].rd(x1, 8), 'little')); r2 = I[i2].res(int.from_bytes(I[i2].rd(x2, 8), 'little'))
        if r1 == r2 and not r1.startswith('('): continue   # same symbol + offset
        # no symbol there (.rodata strings / tables): compare the bytes at the two targets instead
        s1 = I[i1].rd(x1, 96) or b''; s2 = I[i2].rd(x2, 96) or b''
        s1 = s1[:s1.find(b'\0')] if b'\0' in s1 else s1; s2 = s2[:s2.find(b'\0')] if b'\0' in s2 else s2
        if s1 == s2 and s1: rod += 1; continue
        # a jump table of 4-byte entries relative to its base: same function + offset for the first 8 entries. A target in
        # .bss or past the file bytes reads as None (that used to raise); such a target is only
        # compared by symbol, above, and otherwise reported.
        def ent(I_, x, k):
            d = I_.rd(x + 4 * k, 4)
            return None if d is None else I_.res(x + int.from_bytes(d, 'little', signed=True))
        j1 = [ent(I[i1], x1, k) for k in range(8)]
        j2 = [ent(I[i2], x2, k) for k in range(8)]
        if j1 == j2 and None not in j1 and not j1[0].startswith('('): jtab += 1; continue
        # an 8-byte constant (fmt_fp's doubles): equal bytes
        c1, c2 = I[i1].rd(x1, 8), I[i2].rd(x2, 8)
        if c1 is not None and c1 == c2: const += 1; continue
        diff.append((hex(w_off(b1, i)), r1, r2, s1[:24], s2[:24]))
    return v, c, (rod, jtab, const), diff
def w_off(b, i): return bc_words(b)[i][0]
CHAIN = ['__interceptor_trampoline_snprintf', '__interceptor_trampoline_vfprintf', '__interceptor_trampoline_strnlen',
         '__interceptor_trampoline_memset', '__interceptor_trampoline_memcpy', '___interceptor_snprintf', '___interceptor_vsnprintf',
         '___interceptor_vfprintf', '_ZN6__asan18TryAsanInitFromRtlEv', '_ZN6__asan10AsanInitedEv', '_ZL13printf_commonPvPKcS_',
         'vsnprintf', 'sn_write', 'vfprintf', 'printf_core', '__fwritex', 'pop_arg', 'pad', 'fmt_fp', 'memset', 'memcpy',
         '__asan_region_is_poisoned', '_ZN6__asanL11MemToShadowEm']
def funcs(I):
    # the chain, the 36 trampolines, and every function in preset A's AE34 icpt_ranges + musl_sel_ranges + the vsnprintf
    # interceptor (tbl_vsn's base table, A/AE34.v at 17a8581f30c)
    ranges = [(0x8f01c, 71), (0x946ec, 25), (0x94750, 87), (0x9455c, 435), (0x950a0, 1146), (0x9a620, 47), (0x9b944, 10),
              (0xa039c, 69), (0x42c84, 38), (0x42fa8, 165), (0x43a54, 549), (0x442e8, 94), (0x44460, 180), (0x449a8, 156),
              (0x44c18, 157), (0x45570, 729), (0x460d4, 45), (0x464a0, 54), (0x487d0, 102), (0x52348, 1009), (0x54d88, 79),
              (0x55214, 209), (0x59798, 6), (0x5a6a8, 40), (0x64ad8, 13), (0x64b78, 7), (0x64ddc, 12), (0x46188, 198), (0x46578, 28)]
    names = list(CHAIN) + sorted({n for v, z, n, t in I['A'].syms if n.startswith('__interceptor_trampoline_') and 0x42c84 <= v < 0x42d14})
    for s, nw in ranges:
        for v, z, n, t in I['A'].syms:
            if t == 'STT_FUNC' and z > 0 and s <= v < s + 4 * nw and n not in names: names.append(n)
    for n in names:
        f, a, b = I['F'].fsym(n), I['A'].fsym(n), I['B'].fsym(n)
        if not (f and a and b): print('%s\tABSENT in %s' % (n, [k for k, x in (('F', f), ('A', a), ('B', b)) if not x])); continue
        row = [n, hex(f[0]), hex(a[0]), hex(b[0]), str(f[1])]
        for (k1, s1), (k2, s2) in ((('F', f), ('A', a)), (('F', f), ('B', b)), (('A', a), ('B', b))):
            if s1[1] != s2[1]: row.append('SIZE'); continue
            v, c, (rod, jtab, const), diff = tcmp(I, k1, s1[0], k2, s2[0], s1[1])
            row.append('%s pcrel=%d real=%d tgt: rodata-str-eq=%d jumptab-eq=%d const-eq=%d differ=%s'
                       % (v, c[0], c[1], rod, jtab, const, diff if diff else 0))
        print('\t'.join(row))

def stmts():
    """pre-vs-fm residue per declaration after: U -> Hp, ARU segs B -> ARx, ecall_preU segs B -> ecall_pre_x segs B ARx,
    aintrin_realizesU B -> aintrin_realizes_x tfibsegs B ARx, contract suffixes U/Uz/Ua/Ux -> _x/_xz/_xa/_xx (+ ARx arg),
    FM_GOT_canary/FM_canary -> A_GOT_canary/A_canary.  Prints every non-empty residue, then the Section-context diff."""
    fmdecl = {}
    for n in {x for v in FMMAP.values() for x in v} | {'FMupoison'}:
        for nm, k, ln, s in decls(fmpath(n)):
            if not nm.startswith('@'): fmdecl.setdefault(nm, []).append((n, k, ln, s))
    def fmname(nm):
        for a, b in (('_xz', 'Uz'), ('_xa', 'Ua'), ('_xx', 'Ux'), ('_xT', 'UT')):
            if nm.endswith(a): return nm[:-3] + b
        if nm.endswith('_x') and nm[:-2] + 'U' in fmdecl: return nm[:-2] + 'U'
        if nm == 'stack_zero_shadow_x': return 'stack_zero_shadow'
        return nm
    inv = {'FM_GOT_canary': 'A_GOT_canary', 'FM_canary': 'A_canary'}
    pre = []
    for img in ('A', 'Reusable'):
        for p in sorted(glob.glob(os.path.join(D, 'pre', img, '*.v'))):
            b = os.path.basename(p)[:-2]
            for nm, k, ln, s in decls(p):
                if not nm.startswith('@'): pre.append((img, b, nm, k, ln, s))
                if fmname(nm) != nm: inv[fmname(nm)] = nm
    def norm(t):
        o = []; i = 0
        while i < len(t):
            x = t[i]
            if x == 'ARU' and i + 2 < len(t) and t[i + 2] == 'B': o.append('ARx'); i += 3; continue
            if x == 'ecall_preU' and i + 2 < len(t) and t[i + 2] == 'B': o += ['ecall_pre_x', t[i + 1], 'B', 'ARx']; i += 3; continue
            if x == 'aintrin_realizesU' and t[i + 1:i + 2] == ['B']: o += ['aintrin_realizes_x', 'tfibsegs', 'B', 'ARx']; i += 2; continue
            if t[i:i + 9] == ['(', 'U', ':', 'list', '(', 'Z', '*', 'Z', ')']: o += ['(', 'Hp', ':', 'list', 'Z']; i += 9; continue
            if x == 'U': o.append('Hp'); i += 1; continue
            y = x.split('.')[-1]
            o.append(inv.get(y, x) if y in inv and y != x.split('.')[0] or y in inv else x); i += 1
        r = []; j = 0
        while j < len(o):
            r.append(o[j])
            if o[j].startswith('sh_') and o[j] in inv.values() and o[j + 2:j + 3] == ['B'] and o[j + 3:j + 4] != ['ARx']:
                r += [o[j + 1], 'B', 'ARx']; j += 3; continue
            j += 1
        return r
    for img, b, nm, k, ln, s in pre:
        c = fmdecl.get(fmname(nm), [])
        c = [x for x in c if x[0] in FMMAP.get(b, [])] or c
        if not c: print('NEW\t%s/%s.v:%d\t%s %s' % (img, b, ln, k, nm)); continue
        a = tl(s); f = norm(tl(c[0][3]))
        r = [(t, ' '.join(a[i1:i2]), ' '.join(f[j1:j2])) for t, i1, i2, j1, j2 in
             difflib.SequenceMatcher(None, a, f, autojunk=False).get_opcodes() if t != 'equal']
        if r: print('RESIDUE\t%s/%s.v:%d %s %s <- %s.v:%d\t%s' % (img, b, ln, k, nm, c[0][0], c[0][2], r))
    for img, b in [(i, os.path.basename(p)[:-2]) for i in ('A', 'Reusable') for p in sorted(glob.glob(os.path.join(D, 'pre', i, '*.v')))]:
        if not FMMAP.get(b): continue
        a = [' '.join(s.split()) for nm, k, ln, s in decls(os.path.join(D, 'pre', img, b + '.v')) if k in CTX]
        f = [' '.join(s.split()) for n in FMMAP[b] for nm, k, ln, s in decls(fmpath(n)) if k in CTX]
        for t, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, f, autojunk=False).get_opcodes():
            if t != 'equal': print('CTX\t%s/%s\t%s\tPRE %s\n\t\t\tFM  %s' % (img, b, t, a[i1:i2], f[j1:j2]))

def leaves():
    L = {nm: s for nm, k, ln, s in decls(os.path.join(D, 'pre/Reusable/PSnpLeaves.v'))}
    T = {}
    for p in [os.path.join(D, 'pre/Reusable', f) for f in ('PSnpShared.v', 'PSnpSx.v')] + [os.path.join(D, 'preimg/Reusable/YGcallMx.v')]:
        for nm, k, ln, s in decls(p): T.setdefault(nm, s)
    for lf, t in (('top_snprintf', 'sh_asnprintf_realizes_x'), ('link_vsni', 'sh_avsnprintf_icpt_realizes_xa'),
                  ('link_vsn', 'sh_avsnprintf_realizes_xa'), ('leaf_pcommon', 'sh_apcommon_realizes_xz'),
                  ('leaf_vfprintf', 'sh_avfprintf_icpt_realizes_xx'), ('leaf_memset', 'aintrin_realizes_x')):
        a = tl(L[lf]); b = tl(T[t])
        print('%s vs %s:' % (lf, t), [(x, ' '.join(a[i1:i2]), ' '.join(b[j1:j2])) for x, i1, i2, j1, j2 in
                                      difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes() if x != 'equal'])

if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if what in ('pins', 'funcs', 'all'):
        shas(); I = {k: Img(p) for k, p in IMG.items()}
        if what in ('pins', 'all'): pins(I)
        if what in ('funcs', 'all'): funcs(I)
    if what in ('stmts', 'all'): stmts()
    if what in ('leaves', 'all'): leaves()
