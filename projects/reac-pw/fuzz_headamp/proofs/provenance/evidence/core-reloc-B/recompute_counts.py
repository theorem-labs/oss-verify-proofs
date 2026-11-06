#!/usr/bin/env python3
"""Recompute every image-derived count of reac-pw/fuzz_headamp's image-B ASan core (lib/AU, step B3) from the
fuzz_headamp.asan-ubsan pin (and its unstripped twin for symbol addresses), and compare each with the numeral the
derived file states. One row per (file, line, quantity): the formula, the value measured on the pin, the value in the
file, OK / DIFFERS. Read-only.

usage: recompute_counts.py PIN TWIN LIBDIR [--images IMGDIR] > image-derived-counts.tsv
  LIBDIR = proofs/reac-pw/fuzz_headamp/lib (reads AU/*.v); IMGDIR = the checker's elf-snapshot of the pin
  (AsanUbsan.v + AsanUbsan_seg_*.hex), optional: its segment table is compared with the PT_LOAD page-rounding too.
"""
import re, sys, os
from elftools.elf.elffile import ELFFile

pin, twin, lib = sys.argv[1:4]
imgdir = sys.argv[sys.argv.index('--images') + 1] if '--images' in sys.argv else None
E = ELFFile(open(pin, 'rb'))
T = ELFFile(open(twin, 'rb'))
loads = [(s['p_vaddr'], s['p_memsz'], s['p_filesz']) for s in E.iter_segments() if s['p_type'] == 'PT_LOAD']
secs = {s.name: (s['sh_addr'], s['sh_size']) for s in E.iter_sections() if s['sh_addr']}
syms = {}
for s in T.get_section_by_name('.symtab').iter_symbols():
    if s['st_shndx'] != 'SHN_UNDEF' and s.name and not s.name.startswith('$'):
        syms.setdefault(s.name, (s['st_value'], s['st_size']))
# twin == pin for loaded bytes (checked: same PT_LOAD table and allocated sections)
tl = [(s['p_vaddr'], s['p_memsz'], s['p_filesz']) for s in T.iter_segments() if s['p_type'] == 'PT_LOAD']
assert tl == loads, 'twin PT_LOAD table differs from the pin'
pg = lambda a: a & ~0xfff
pgu = lambda a: (a + 0xfff) & ~0xfff
segs = [(pg(v), pgu(v + m) - pg(v)) for v, m, f in loads]
top = max(b + s for b, s in segs)
lo = segs[0][0]
A = lambda n: syms[n][0]
SZ = lambda n: syms[n][1]
sh = lambda a: (a >> 3) + 0x7fff8000
asan_lo = secs['asan_globals'][0]
ndesc = secs['asan_globals'][1] // 64
data = open(pin, 'rb').read()
def u(a, n=8):
    for (v, m, f), ph in zip(loads, [s for s in E.iter_segments() if s['p_type'] == 'PT_LOAD']):
        if v <= a and a + n <= v + f:
            o = ph['p_offset'] + a - v
            return int.from_bytes(data[o:o + n], 'little')
desc = [[u(asan_lo + 64 * i + 8 * k) for k in range(8)] for i in range(ndesc)]
runs = []
for b, e in sorted((d[0], d[0] + d[2]) for d in desc):
    if runs and b <= runs[-1][1]: runs[-1][1] = max(runs[-1][1], e)
    else: runs.append([b, e])
windows = [(sh(b), (e - b) // 8) for b, e in runs] + [(sh(asan_lo), ndesc * 64 // 8)]
def hull(a, n): return sh(a) & ~7, (sh(a + n - 1) + 1 + 7) & ~7
def yd2j():
    t = open(os.path.join(lib, 'AU/YD2j.v')).read()
    regs = re.findall(r'Definition (R_\w+)\s*:\s*\w+\s*:=\s*mkRegion\s+None\s+(\d+)\s+(\d+)', t)
    order = re.search(r'Definition IMG_REGIONS[^:]*:[^=]*:=\s*\[(.*?)\]\s*\.', t, re.S).group(1)
    return {n: (int(a), int(b)) for n, a, b in regs}, [x.strip() for x in order.split(';')]
R, ORDER = yd2j()
def f0m_index(addr):
    t = open(os.path.join(lib, 'AU/YF0m.v')).read()
    s = t.index('Tfib_const_abs'); s = t.index(':=', s); e = t.index('].', s)
    items = re.findall(r'(?:z8|z4|z2|z1)\s*\(ANum\s+(0x[0-9a-fA-F]+|\d+)\)', t[s:e])
    return [int(x, 0) for x in items].index(addr)
FMT = {}
for f in ('YE2t', 'YE2u', 'YE2v', 'YE2w', 'YE35'):
    t = open(os.path.join(lib, f'AU/{f}.v')).read()
    FMT[f] = int(re.search(r'Definition FMT : Z := (0x[0-9a-f]+)\.', t).group(1), 16)
FMTLEN = {'YE2t': 20, 'YE2u': 22, 'YE2v': 32, 'YE2w': 16, 'YE35': 3}
def strlen_at(a):
    n = 0
    while u(a + n, 1) != 0: n += 1
    return n
# (file, regex with one group per checked numeral, [ (quantity name, formula text, value) ... ])
seg3_file_end = loads[3][0] + loads[3][2] - segs[3][0]
Q = [
 ('YB13', r'scanN \w+_seg_bytes_000 64 0 (\d+)', [('seg0 size', 'PT_LOAD0 page-rounded length', segs[0][1])]),
 ('YB13', r'scanN \w+_seg_bytes_001 64 0 (\d+)', [('seg1 size', 'PT_LOAD1 page-rounded length', segs[1][1])]),
 ('YB13', r'scanN \w+_seg_bytes_002 64 0 (\d+)', [('seg2 size', 'PT_LOAD2 page-rounded length', segs[2][1])]),
 ('YB13', r'scanN \w+_seg_bytes_003 64 0 (\d+)', [('seg3 size', 'PT_LOAD3 page-rounded length', segs[3][1])]),
 ('YB13', r'zscanN \w+_seg_bytes_003 64 (\d+) (\d+)', [('seg3 file-backed end offset', 'PT_LOAD3 vaddr+filesz - seg3 base', seg3_file_end), ('seg3 zero tail', 'seg3 size - file-backed end offset', segs[3][1] - seg3_file_end)]),
 ('YB13', r'with \((\d+) \+ Z\.to_N \(x - (0x[0-9a-f]+)\)\)', [('seg3 file-backed end offset', 'PT_LOAD3 vaddr+filesz - seg3 base', seg3_file_end), ('seg3 file-backed end', 'PT_LOAD3 vaddr+filesz (= __stop_asan_globals)', loads[3][0] + loads[3][2])]),
 ('YB13', r'\(\((\d+) <=\? x\) && \(x \+ 1 <=\? \d+ \+ (\d+)\)\)%bool with true by \(symmetry; apply andb_true_iff; split; apply Z\.leb_le; lia\)\)\.\s*\n?\s*replace \(Z\.to_N \(x - \d+\) <\? \d+\)%N with true', []),
 ('YB1h', r'segments_reserved TSEGS = \[\(Z_to_bv 64 (0x[0-9a-f]+), Z_to_bv 64 (0x[0-9a-f]+)\); \(Z_to_bv 64 (0x[0-9a-f]+), Z_to_bv 64 (0x[0-9a-f]+)\);\s*\(Z_to_bv 64 (0x[0-9a-f]+), Z_to_bv 64 (0x[0-9a-f]+)\); \(Z_to_bv 64 (0x[0-9a-f]+), Z_to_bv 64 (0x[0-9a-f]+)\)\]',
   [(f'seg{i} {k}', f'PT_LOAD{i} page-rounded {k}', segs[i][0 if k == "base" else 1]) for i in range(4) for k in ('base', 'size')]),
 ('YB1h', r'sum_sizes \(segments_reserved TSEGS\) = (0x[0-9a-f]+)', [('sum of segment sizes', 'sum of PT_LOAD page-rounded lengths', sum(s for _, s in segs))]),
 ('YFia', r'= \[\((\d+), (\d+)\); \((\d+), (\d+)\); \((\d+), (\d+)\); \((\d+), (\d+)\)\]', [(f'seg{i} {k}', f'PT_LOAD{i} page-rounded {k}', segs[i][0 if k == "base" else 1]) for i in range(4) for k in ('base', 'size')]),
 ('YB1v', r'tfibmusl_text_count : nat := (\d+)', [('sysconf .. .text end, words', '(.text end - sysconf) / 4', (secs['.text'][0] + secs['.text'][1] - A('sysconf')) // 4)]),
 ('YB1v', r'tfibmusl_text_start : Z := (0x[0-9a-f]+)', [('sysconf', 'st_value sysconf', A('sysconf'))]),
 ('YB1v', r'tfibguard_start : Z := (0x[0-9a-f]+)', [('oft_exit_guard', 'st_value oft_exit_guard', A('oft_exit_guard'))]),
 ('YB1v', r'tfibguard_count : nat := (\d+)', [('oft_exit_guard prefix the table decodes (walk parameter, not an image quantity)', 'N <= st_size oft_exit_guard / 4: printed as N when it holds', None)]),
 ('YCef', r'tfib_lib_count : nat := (\d+)', [('main .. __extenddftf2, words', '(__extenddftf2 - main) / 4', (A('__extenddftf2') - A('main')) // 4)]),
 ('YD1g', r'change (\d+) with \((\d+) \* 4096\)', [('image hull span', 'image top - image base', top - lo), ('image hull pages', '(image top - image base) / 4096', (top - lo) // 4096)]),
 ('YD28', r'R_A3[^\n]*?(\d{3})\b', []),
 ('YE22', r'nth_error_In Tfib_const_abs (\d+)\)', [('YF0m Tfib_const_abs row of the __stack_chk_guard .got word', 'index of z8 (ANum <.got slot holding __stack_chk_guard>)', f0m_index([a for a in range(secs['.got'][0], secs['.got'][0] + secs['.got'][1], 8) if u(a) == A('__stack_chk_guard')][0]))]),
 ('YE37', r'Definition x2_shw : list \(Z \* Z\) := \[\((0x[0-9a-f]+), (\d+)\); \((0x[0-9a-f]+), (\d+)\); \((0x[0-9a-f]+), (\d+)\); \((0x[0-9a-f]+), (\d+)\)\]',
   [(x, y, v) for i, (w, n) in enumerate(windows) for (x, y, v) in ((f'shadow window {i} start', 'shadow of descriptor run start (asan_globals array last)', w), (f'shadow window {i} cells', 'run length / 8', n))]),
 ('YE37', r'\((0x[0-9a-f]+), (\d+), \[\(0, 8%N, 0x[0-9a-f]+\); \(8, 8%N, 0x[0-9a-f]+\); \(16, 8%N, 0x20\);', [('asan_globals', 'section start', asan_lo), ('descriptor table bytes', 'asan_globals size (= 64 * descriptors)', ndesc * 64)]),
 ('YE37', r'assert \(Hr : (0x[0-9a-f]+) <= lo /\\ lo \+ n <= (0x[0-9a-f]+)', [('lowest shadow window start', 'min window start', min(w for w, _ in windows)), ('shadow end of the descriptor array', 'shadow(asan_globals) + size/8', sh(asan_lo) + ndesc * 8)]),
 ('YE23', r'\((0x7fff[0-9a-f]+) <= a < (0x7fff[0-9a-f]+)\) \\/ \((0x7fff[0-9a-f]+) <= a < (0x7fff[0-9a-f]+)\) \\/ \((0x8000[0-9a-f]+) <= a < (0x8000[0-9a-f]+)\) \\/ \((0x8000[0-9a-f]+) <= a < (0x8000[0-9a-f]+)\)',
   [(x, y, v) for i, (w, n) in enumerate(windows) for (x, y, v) in ((f'shadow window {i} lo', 'shadow of run start', w), (f'shadow window {i} hi', 'lo + run length / 8', w + n))]),
 ('YD1o', r'change \((0x[0-9a-f]+) / 8\) with (\d+) in L1\. change \(\((0x[0-9a-f]+) - 1\) / 8\) with (\d+) in L2', [('(source) address', 'as written', None), ('its /8', 'value / 8 (checked below)', None), ('image top', 'image top page', top), ('(top - 1) / 8', '(image top - 1) / 8', (top - 1) // 8)]),
 ('YD1o', r'change \((\d+) / 8\) with (\d+)\. change \(\((\d+) - (\d+)\) / 8\) with (\d+)\.', [('__stop_asan_globals', 'asan_globals end', asan_lo + ndesc * 64), ('its /8', '__stop_asan_globals / 8', (asan_lo + ndesc * 64) // 8), ('image top', 'image top page', top), ('__stop_asan_globals', 'asan_globals end', asan_lo + ndesc * 64), ('(top - stop) / 8', '(image top - __stop_asan_globals) / 8', (top - asan_lo - ndesc * 64) // 8)]),
 ('YFem', r'exists \((\d+) \+ bkt\)', [('theDepot / 4', 'st_value _ZN11__sanitizerL8theDepotE / 4', A('_ZN11__sanitizerL8theDepotE') // 4)]),
 ('YD1f', r'kn_vis TFIB ch \(ELit 0\) (0x[0-9a-f]+) (0x[0-9a-f]+)\) HS_tfib_list', [('shadow of image base', 'shadow(image base)', sh(lo)), ('image span / 8', '(image top - image base) / 8', (top - lo) // 8)]),
]
for f, n in FMTLEN.items():
    a = FMT[f]
    assert strlen_at(a) + 1 >= n
    lo_, hi_ = hull(a, n)
    Q.append((f, r'Definition SH_LO : Z := (0x[0-9a-f]+)\.\s+Definition SH_HI : Z := (0x[0-9a-f]+)\.', [('FMT shadow hull lo', f'shadow({a:#x}) & ~7', lo_), ('FMT shadow hull hi', f'(shadow({a:#x}+{n}-1)+1) rounded up to 8', hi_)]))
print('\t'.join(['file', 'line', 'quantity', 'formula on the pin', 'pin value', 'file value', 'verdict']))
n_ok = n_bad = 0
for f, rx, qs in Q:
    p = os.path.join(lib, f'AU/{f}.v')
    t = open(p).read()
    ms = list(re.finditer(rx, t))
    if not ms or not qs:
        continue
    for m in ms:
        line = t.count('\n', 0, m.start()) + 1
        vals = [int(g, 0) for g in m.groups()]
        for (q, form, v), fvv in zip(qs, vals):
            if v is None:
                continue
            ok = (v == fvv)
            n_ok += ok; n_bad += (not ok)
            print('\t'.join([f'AU/{f}.v', str(line), q, form, hex(v) if v > 0xffff else str(v), hex(fvv) if fvv > 0xffff else str(fvv), 'OK' if ok else 'DIFFERS']))
# region table: count, R_A3 bounds (anchor symbols), positions used by the core
r3 = R['R_A3']
for q, form, v, fvv in [('YD2j regions', 'len IMG_REGIONS', len(ORDER), 73), ('R_A3 lo', 'st_value oft_arg0', A('oft_arg0'), r3[0]), ('R_A3 hi', 'asan_globals start', asan_lo, r3[1]),
                        ('R_A3 length', 'asan_globals - oft_arg0', asan_lo - A('oft_arg0'), r3[1] - r3[0]), ('descriptors', 'asan_globals size / 64', ndesc, 43)]:
    ok = v == fvv; n_ok += ok; n_bad += (not ok)
    print('\t'.join(['AU/YD2j.v', '-', q, form, str(v), str(fvv), 'OK' if ok else 'DIFFERS']))
for f in ('YD28', 'YD2d'):
    t = open(os.path.join(lib, f'AU/{f}.v')).read()
    for m in re.finditer(r'\b832\b', t):
        line = t.count('\n', 0, m.start()) + 1
        v = asan_lo - A('oft_arg0'); ok = v == 832; n_ok += ok; n_bad += (not ok)
        print('\t'.join([f'AU/{f}.v', str(line), 'R_A3 length', 'asan_globals - oft_arg0', str(v), '832', 'OK' if ok else 'DIFFERS']))
if imgdir:
    t = open(os.path.join(imgdir, 'AsanUbsan.v')).read()
    ss = re.findall(r'seg_base\s*:=\s*(0x[0-9a-f]+)%N;\s*seg_size\s*:=\s*(0x[0-9a-f]+)%N', t)
    for i, (b, s) in enumerate(ss):
        for q, v, fvv in ((f'proof image seg{i} base', segs[i][0], int(b, 16)), (f'proof image seg{i} size', segs[i][1], int(s, 16))):
            ok = v == fvv; n_ok += ok; n_bad += (not ok)
            print('\t'.join(['images/AsanUbsan.v', '-', q, 'PT_LOAD page rounding', hex(v), hex(fvv), 'OK' if ok else 'DIFFERS']))
print(f'# rows {n_ok + n_bad}: OK {n_ok}, DIFFERS {n_bad}', file=sys.stderr)
