#!/usr/bin/env python3
"""triage-B.py CHECK_TSV OUT_TSV: one line per FLAGGED row of a port_addr_check run (cb0e067e3bae --fail-on-flags) over the
fuzz_uci image-B core, with the measured reason that accepts it. A row no rule below accepts is printed as UNEXPLAINED and
the script exits 1. Reasons were measured on fuzz_grant.asan-ubsan / fuzz_uci.asan-ubsan (gates-B.md)."""
import re, sys

FLAGGED = {'ARITH-MISMATCH', 'DIFFERENT-SYMBOL', 'FLAGS-NOT-DECOMPOSABLE', 'GEOMETRY-CHANGED', 'GP-NOT-GLOBAL-POINTER',
           'HASH-UNCHANGED', 'IMAGE-EXTENT-CHANGED', 'IMAGE-EXTENT-STALE-ABOVE', 'IMAGE-EXTENT-STALE-BELOW', 'INSN-CHANGED',
           'KIND-CHANGED', 'LABEL-COMPARED-WITH-PC', 'LABEL-MIXED', 'NO-COUNTERPART', 'NON-ADDRESS-CHANGED',
           'SAME-VALUE-DIFFERENT-OBJECT', 'SLID-TO-NEIGHBOUR', 'STALE-DERIVED-QUOTIENT', 'STALE-DONOR-CODE-POINTER',
           'STALE-DONOR-DATA-POINTER', 'STALE-DONOR-ROUNDED', 'TARGET-DIFFERENT-SYMBOL', 'TARGET-OUTSIDE', 'UNPAIRED-FILE',
           'UNPAIRED-PORTED', 'UNPAIRED-SOURCE', 'UNRESOLVED',
           'GENERATOR-FILL'}   # the last is REPORTED, not a finding; triaged because it can hide a wrong duplicate pointer
PATCHED = {'B/YFex.v', 'B/YFf0.v', 'B/YFf3.v', 'B/YFf4.v', 'B/YFfl.v', 'B/YFjy.v', 'B/YFim.v', 'B/YFin.v', 'B/YD1q.v'}
REGION_FILES = {'B/YD1x.v', 'B/YD22.v', 'B/YD27.v', 'B/YD28.v', 'B/YD2d.v', 'B/YD2e.v', 'B/YD2f.v', 'B/YD2h.v'}
SYM = re.compile(r'([\w:.$~<>]+\+0x[0-9a-f]+)')


def reason(d):
    v, f = d['verdict'], d['src_file'] or d['dst_file']
    sv, dv, sr, dr = d['src_value'], d['dst_value'], d['src_res'], d['dst_res']
    if v in ('NON-ADDRESS-CHANGED', 'GENERATOR-FILL') and f in REGION_FILES and sv.startswith('0x') and dv.startswith('0x') \
            and int(sv, 16) - int(dv, 16) == 2 and int(sv, 16) < 0x40:
        return ('region count / index of the unit IMG_REGIONS (port_core region-count rule): grant B lib/B/YD2j.v has 33 '
                'regions (R_A5a at 24, R_A7b at 28), fuzz_uci B lib/B/YD2j.v 31 (22, 26; no R_A1l / R_A1m): N + c -> N - 2 + c')
    if v == 'GENERATOR-FILL':
        # REPORTED, not a finding in the checker; triaged anyway: a wrong pointer that repeats another value of its sentence
        # is classed GENERATOR-FILL (measured: plant YF0l pc_wrap_memcpy -> 0x50674 = pc_asan_memcpy's value)
        s1, s2 = re.search(r'str:"([^"]*)"\+(\d+)', sr), re.search(r'str:"([^"]*)"\+(\d+)', dr)
        if s1 and s2 and s1.groups() == s2.groups():
            return f'GENERATOR-FILL (reported): same string + offset in both images ("{s1.group(1)[:30]}"+{s1.group(2)})'
        a, b = SYM.findall(sr), SYM.findall(dr)
        if a and b and a[0] == b[0]:
            return f'GENERATOR-FILL (reported): same symbol + offset in both images ({a[0]})'
        return None
    if v == 'NON-ADDRESS-CHANGED' and f == 'B/YE22.v' and sv == '0x111' and dv == '0xc1':
        return ('index of the .got canary cell in lib/B/YF0m.v Tfib_const_abs, 273 -> 193 (overrides-B.tsv row 48, '
                'measure-B.py: the donor 273 of 361, image A 273 of 290, image B 193 of 217)')
    if v in ('UNPAIRED-SOURCE', 'UNPAIRED-PORTED'):
        if f == 'B/YB1w.v':
            return 'AB1w function table emitted for fuzz_uci: grant-only rows dropped (bcmp, stack classes 0/2/4/6), uci program functions added'
        if f in PATCHED:
            return 'sentence rewritten by a B-*.patch (image A core patches re-cut for B: zero-shadow-forallb, cell-lookup, ad1q-shape)'
        if f == 'B/YF0l.v':
            return 'AF0l class map emitted from fuzz_uci.asan-ubsan __asan_stack_malloc_N symbols: class 1 only (0x3c1b8)'
        if f in ('B/YCbq.v', 'B/YCe5.v'):
            return 'image bounds stated through B/YImgTop.v IMG_LO / IMG_TOP (port_core YImgTop rule), numerals become names'
    if v in ('STALE-DONOR-CODE-POINTER', 'NO-COUNTERPART') and f == 'B/YB1w.v' and 'thunk_95368' in d['sentence']:
        return 'grant row thunk_95368 = bcmp, dropped (uci links no bcmp); the checker pairs tfib_*_thunk_<hex> by name wildcard with thunk_96f9c'
    if v == 'GEOMETRY-CHANGED' and sv == dv and sv in ('0x2000', '0x20000'):
        return f'allocator constant {int(sv, 16)} unchanged (2^13 kBatchClass size / 2^17 mmap length), not segment geometry'
    if v == 'NON-ADDRESS-CHANGED' and f in ('B/YFim.v', 'B/YFin.v') and sv == '0x3c':
        return 'Tfib_const index 60 of nth_error_In replaced by YF0x.cell_lookup_In (B-cell-lookup.patch); the pairing reads 60 vs the 1 of (ANum (TFIB_OOM + 1)) 1'
    if v == 'NON-ADDRESS-CHANGED':
        a, b = SYM.findall(sr), SYM.findall(dr)
        if a and b and a[0] == b[0]:
            return f'same symbol + offset in both images ({a[0]})'
        s1, s2 = re.search(r'str:"([^"]*)"\+(\d+)', sr), re.search(r'str:"([^"]*)"\+(\d+)', dr)
        if s1 and s2 and s1.groups() == s2.groups():
            return f'same string + offset in both images ("{s1.group(1)[:30]}"+{s1.group(2)})'
        q = {'0x1445c': '(.bss+0x20) / 8', '0xbf5ff': '(IMG_TOP - 1) / 8', '0xab1a8': '(IMG_TOP - TFIB_BSS) / 8',
             '0x14478': '(__asan::instance + 0xa8) / 8', '0x61e16': 'theDepot / 4', '0x14d70': 'internal_alloc_placeholder / 8'}
        if sv in q:
            return f'quotient {q[sv]} of the moved address (measure-B.out / gates-B.md)'
        if f == 'B/YE34.v':
            return 'icpt_ranges (start, count) word counts of the twin runs (port_core range splitting; uci links fewer interceptors)'
        if f in ('B/YE2t.v', 'B/YE2v.v', 'B/YE2w.v', 'B/YE35.v', 'B/YE2u.v'):
            return 'driver format shadow window [floor8(shadow(FMT)), floor8(shadow(FMT+len))+8) (measure-B.out)'
    if v == 'KIND-CHANGED':
        if f == 'B/YF0l.v':
            return 'absent entry = 0: fuzz_uci.asan-ubsan links no __asan_memset / __interceptor_trampoline_bcmp (override, knock precedent)'
        if f in ('B/YE2v.v', 'B/YE2w.v', 'B/YE35.v', 'B/YE2u.v', 'B/YE2t.v'):
            return 'driver format shadow window (rule / override, measure-B.out)'
    if v == 'UNRESOLVED':
        if 'set_thread_area' in d['sentence']:
            return 'end of __set_thread_area = __unmapself start in both images'
        if 'tfib_at_ph_addr_z' in d['sentence']:
            return 'program headers at ELF header + 0x40 = 0x10040 in both images'
        if sv == '0x800b32e0':
            return 'shadow of builtin_tls+0xeb8 in both images (grant 0x5d9700, uci 0x5d2e80)'
        if f in ('B/YE2u.v', 'B/YD2f.v', 'B/YE2t.v', 'B/YE2w.v', 'B/YE35.v'):
            return 'window end / stdin buf end by role (override, measure-B.out)'
    if v == 'DIFFERENT-SYMBOL' and f in ('B/YFk1.v', 'B/YFk2.v'):
        return 'RELATIVE jump-table entry (base + entry): sysconf+0x208 / VSNPrintf+0x350 in both images; cell bytes read from uci'
    if v == 'SAME-VALUE-DIFFERENT-OBJECT' and sv == dv == '0x104022':
        return 'mmap flags MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE|MAP_FIXED_NOREPLACE, never relocated'
    return None


rows, hdr = [], None
for line in open(sys.argv[1]):
    if line.startswith('#'):
        continue
    r = line.rstrip('\n').split('\t')
    if hdr is None:
        hdr = r
        continue
    d = dict(zip(hdr, r))
    if d['verdict'] in FLAGGED:
        rows.append(d)
bad = 0
with open(sys.argv[2], 'w') as fh:
    fh.write('verdict\tfile:line\tsource\twritten\treason\n')
    for d in rows:
        why = reason(d)
        bad += why is None
        loc = f"{d['src_file'] or d['dst_file']}:{d['src_line'] or d['dst_line']}"
        fh.write(f"{d['verdict']}\t{loc}\t{d['src_value']}\t{d['dst_value']}\t{why or 'UNEXPLAINED ' + d['note'][:160]}\n")
print(f'{len(rows)} flagged rows, {len(rows) - bad} explained, {bad} UNEXPLAINED -> {sys.argv[2]}')
sys.exit(1 if bad else 0)
