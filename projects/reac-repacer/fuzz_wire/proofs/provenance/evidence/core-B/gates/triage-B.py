#!/usr/bin/env python3
"""triage-B.py CHECK_TSV OUT_TSV: one line per FLAGGED row of a port_addr_check run (e165063a0081 --fail-on-flags) over the
fuzz_wire image-B core, with the measured reason that accepts it. A row no rule below accepts is printed as UNEXPLAINED and
the script exits 1. Reasons were measured on fuzz_grant.asan-ubsan / fuzz_wire.asan-ubsan (GATES.md)."""
import os, re, sys

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
# the cells yb1w-drop-unread.py removed from the committed B/YB1w.v (its records yb1w-drop.tsv, yb1w-drop-v4.tsv,
# yb1w-drop-v52.tsv): cell -> (record, class)
_EVD = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
DROPPED = {r[0]: (rec, r[2]) for rec in ('yb1w-drop.tsv', 'yb1w-drop-v4.tsv', 'yb1w-drop-v52.tsv')
           if os.path.exists(os.path.join(_EVD, rec))
           for r in (l.rstrip('\n').split('\t') for l in open(os.path.join(_EVD, rec))) if not r[0].startswith('#')}


def reason(d):
    v, f = d['verdict'], d['src_file'] or d['dst_file']
    sv, dv, sr, dr = d['src_value'], d['dst_value'], d['src_res'], d['dst_res']
    if v in ('NON-ADDRESS-CHANGED', 'GENERATOR-FILL') and f in REGION_FILES and sv.startswith('0x') and dv.startswith('0x') \
            and int(sv, 16) - int(dv, 16) == 3 and int(sv, 16) < 0x40:
        return ('region count / index of the unit IMG_REGIONS (port_core region-count rule): grant B lib/B/YD2j.v has 33 '
                'regions (R_A5a at 24, R_A7b at 28), fuzz_wire B lib/B/YD2j.v 30 (21, 25; no R_A1d / R_A1l / R_A1m / R_A1n, '
                'R_A1p added): N + c -> N - 3 + c')
    if v == 'DIFFERENT-SYMBOL' and sv == '0xa22c0' and dv == '0x10000' and f in ('B/YD1o.v', 'B/YD25.v'):
        return ('TFIB_BSS = the start of the last range of the unit\'s lib/B/YF0m.v Tfib_zero_shadow, whose membership the '
                'lemma states: fuzz_grant B (0xa22c0, ...) of 15 ranges (the donor value); fuzz_wire B has ONE range '
                '(0x10000, 0x5f6000 - 0x10000), no ASan global. The checker expects the donor\'s symbol position (.bss start '
                '0x9d140), which is not a range of the table (measure-B.out; overrides-B.tsv)')
    if v == 'GEOMETRY-CHANGED' and f == 'B/YD1o.v' and sv == '0x14458' and dv == '0x2000':
        return 'TFIB_BSS / 8 = 0x10000 / 8 = 8192 (the quotient of the TFIB_BSS row above; donor 0xa22c0 / 8 = 83032)'
    if v == 'UNPAIRED-PORTED' and f == 'B/YE34.v' and dv in ('0x129', '0x51420'):
        return ('icpt_ranges: fuzz_grant B\'s range (0x51b80, 1009 words) = 2 trampolines + __asan_memcpy + __asan_memset + '
                '__interceptor_memset + __interceptor_memcpy (4036 bytes); in fuzz_wire B __asan_memmove (not walked) sits where '
                '__asan_memset was, so the range splits: (0x50c0c, 297) = trampolines + __asan_memcpy (1188 bytes), '
                '(0x51420, 568) = __interceptor_memset + __interceptor_memcpy (2272 bytes)')
    if v == 'KIND-CHANGED' and f == 'B/YFfg.v' and sv == dv == '0x40248':
        return ('do_stretch length operand 262728, unchanged (a length, not an address; the checker classes the same number '
                'as a code offset in one image and a return site in the other)')
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
        return ('index of the .got canary cell in lib/B/YF0m.v Tfib_const_abs, 273 -> 193 (overrides-B.tsv, measure-B.py: '
                'the donor 273 of 361, image A 273 of 288, image B 193 of 215)')
    if v in ('UNPAIRED-SOURCE', 'UNPAIRED-PORTED'):
        cell = d['sentence'].split(' ')[1] if d['sentence'].startswith('Definition ') else None
        if v == 'UNPAIRED-SOURCE' and f == 'B/YB1w.v' and cell in DROPPED:
            return (f'cell removed from the committed YB1w.v by yb1w-drop-unread.py ({DROPPED[cell][0]}, 0 readers): '
                    f'{DROPPED[cell][1]}')
        if f == 'B/YB1w.v':
            return ('AB1w function table emitted for fuzz_wire.asan-ubsan by port_core: 27 donor pairs dropped (functions '
                    'fuzz_wire does not link), 20 target functions added')
        if f in PATCHED:
            return 'sentence rewritten by a B-*.patch (image A core patches re-cut for B: zero-shadow-forallb, cell-lookup, ad1q-shape)'
        if f == 'B/YF0l.v':
            return ('AF0l stack-class map emitted from fuzz_wire.asan-ubsan\'s own __asan_stack_malloc_N symbols: classes 0 = '
                    '0x3c524 and 1 = 0x3c698; fuzz_grant B\'s other classes are not linked')
        if f in ('B/YCbq.v', 'B/YCe5.v'):
            return 'image bounds stated through B/YImgTop.v IMG_LO / IMG_TOP (port_core YImgTop rule), numerals become names'
    if v == 'GEOMETRY-CHANGED' and sv == dv and sv in ('0x2000', '0x20000'):
        return f'allocator constant {int(sv, 16)} unchanged (2^13 kBatchClass size / 2^17 mmap length), not segment geometry'
    if v == 'NON-ADDRESS-CHANGED' and f in ('B/YFim.v', 'B/YFin.v') and sv == '0x3c':
        return 'Tfib_const index 60 of nth_error_In replaced by YF0x.cell_lookup_In (B-cell-lookup.patch); the pairing reads 60 vs the 1 of (ANum (TFIB_OOM + 1)) 1'
    if v == 'NON-ADDRESS-CHANGED' and f == 'B/YD1g.v' and sv == '0x5eb000' and dv == '0x5e6000':
        return ('the span of THIS image, IMG_TOP - 0x10000 (static_img_chk: fst r + snd r <= 0x10000 + span): grant B '
                '0x10000..0x5fb000, fuzz_wire B 0x10000..0x5f6000; a size moved by role (port_addr_check 205a90fd19b8 '
                'reads it in a size-name slot)')
    if v == 'NON-ADDRESS-CHANGED':
        a, b = SYM.findall(sr), SYM.findall(dr)
        if a and b and a[0] == b[0]:
            return f'same symbol + offset in both images ({a[0]})'
        s1, s2 = re.search(r'str:"([^"]*)"\+(\d+)', sr), re.search(r'str:"([^"]*)"\+(\d+)', dr)
        if s1 and s2 and s1.groups() == s2.groups():
            return f'same string + offset in both images ("{s1.group(1)[:30]}"+{s1.group(2)})'
        # quotients of moved addresses, each with fuzz_wire B's own value (measured: symtab of the unstripped twin)
        q = {'0x1445c': ('(.bss + 0x20) / 8 = 0x9d160 / 8', '0x13a2c'),
             '0xbf5ff': ('(IMG_TOP - 1) / 8 = (0x5f6000 - 1) / 8', '0xbebff'),
             '0xab1a8': ('(IMG_TOP - TFIB_BSS) / 8 = (0x5f6000 - 0x10000) / 8', '0xbcc00'),
             '0x14478': ('(__asan::instance + 0xa8) / 8 = (0x9d198 + 0xa8) / 8', '0x13a48'),
             '0x61e16': ('theDepot / 4', '0x609b6'),
             '0x14d70': ('internal_alloc_placeholder / 8', '0x14340')}
        if sv in q and dv == q[sv][1]:
            return f'quotient {q[sv][0]} = {q[sv][1]} in fuzz_wire B'
        if f == 'B/YE34.v' and sv == '0x3f1' and dv == '0x238':
            return 'icpt_ranges word count 1009 -> 568: the donor range splits at __asan_memmove (see the UNPAIRED rows of B/YE34.v)'
        if f in ('B/YE2t.v', 'B/YE2v.v', 'B/YE2w.v', 'B/YE35.v', 'B/YE2u.v'):
            return 'driver format shadow window [floor8(shadow(FMT)), floor8(shadow(FMT+len))+8) (measure-B.out)'
    if v == 'KIND-CHANGED':
        if f == 'B/YF0l.v' and sv == '0x52024' and dv == '0x0':
            return 'absent entry = 0: fuzz_wire.asan-ubsan links no __asan_memset (its bcmp trampoline IS linked and relocated)'
        if f in ('B/YE2v.v', 'B/YE2w.v', 'B/YE35.v', 'B/YE2u.v', 'B/YE2t.v'):
            return 'driver format shadow window (rule / override, measure-B.out)'
    if v == 'UNRESOLVED':
        if 'set_thread_area' in d['sentence'] and dv == '0x941dc':
            return 'end of __set_thread_area (0x941d0) = __unmapself start 0x941dc in fuzz_wire B'
        if 'tfib_at_ph_addr_z' in d['sentence'] and dv == '0x10040':
            return 'program headers at ELF header + 0x40 = 0x10040 in both images'
        if sv == '0x800b32e0' and dv == '0x800b28b0':
            return 'shadow of builtin_tls + 0xeb8: grant 0x5d9700, fuzz_wire B 0x5d36c8 + 0xeb8 = 0x5d4580 -> 0x800b28b0'
        if f in ('B/YE2u.v', 'B/YD2f.v', 'B/YE2t.v', 'B/YE2w.v', 'B/YE35.v'):
            return 'window end / stdin buf end by role (override, measure-B.out)'
    if v == 'DIFFERENT-SYMBOL' and f in ('B/YFk1.v', 'B/YFk2.v'):
        return 'RELATIVE jump-table entry (base + entry); cell bytes read from fuzz_wire B'
    if v == 'SAME-VALUE-DIFFERENT-OBJECT' and sv == dv == '0x104022':
        return 'mmap flags MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE|MAP_FIXED_NOREPLACE, never relocated'
    # checker 0d24592683b6's named-definition rule: a tfib_A_ / tfib_E_ row named after a libc or ASan entry point holds,
    # in the donor lineage, the interceptor trampoline / neighbour boundary of that name; it is the same symbol + offset
    # in both images, so the row is relocated, not stale
    if v == 'DIFFERENT-SYMBOL' and f == 'B/YB1w.v' and sr and sr == dr:
        return f'YB1w row name is the donor lineage\'s name for this entry; same symbol + offset in both images ({sr[:60]})'
    if v == 'STALE-DONOR-CODE-POINTER' and sv == dv == '0x40000' and f in ('B/YFk8.v', 'B/YFk9.v', 'B/YFkn.v'):
        return ('SLit 262144 = the mmap length argument (with prot 3 and flags 50 in the next registers): kUserMapSize '
                '2^18, a length, not a pc')
    if v == 'SAME-VALUE-DIFFERENT-OBJECT' and sv == dv == '0x200000' and f in ('B/YE30.v', 'B/YE6k.v'):
        return 'bound fst e + snd e <= 0x200000 on a table entry\'s (offset, length): a 2 MiB size bound, not an address'
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
