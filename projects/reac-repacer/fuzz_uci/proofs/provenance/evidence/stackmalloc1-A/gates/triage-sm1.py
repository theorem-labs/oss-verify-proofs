#!/usr/bin/env python3
"""triage-sm1.py CHECK_TSV OUT_TSV: one line per FLAGGED or GENERATOR-FILL row of a port_addr_check --fail-on-flags run
(efa19b81e92b of record; e165063a0081 beside it) over this slice's files (donor = the run's stage/, renamed fuzz_grant
text; ported = the committed lib/A/Rt/AF0r.v, AF0s.v, lib/Reusable/YF0v.v), with the measured reason that accepts it. A
row no rule below accepts is printed as UNEXPLAINED and the script exits 1. Each rule names the exact file, donor line
and values it accepts. The image-B record's script with the image-A rows."""
import sys

FLAGGED = {'ARITH-MISMATCH', 'DIFFERENT-SYMBOL', 'FLAGS-NOT-DECOMPOSABLE', 'GEOMETRY-CHANGED', 'GP-NOT-GLOBAL-POINTER',
           'HASH-UNCHANGED', 'IMAGE-EXTENT-CHANGED', 'IMAGE-EXTENT-STALE-ABOVE', 'IMAGE-EXTENT-STALE-BELOW', 'INSN-CHANGED',
           'KIND-CHANGED', 'LABEL-COMPARED-WITH-PC', 'LABEL-MIXED', 'NO-COUNTERPART', 'NON-ADDRESS-CHANGED',
           'SAME-VALUE-DIFFERENT-OBJECT', 'SLID-TO-NEIGHBOUR', 'STALE-DERIVED-QUOTIENT', 'STALE-DONOR-CODE-POINTER',
           'STALE-DONOR-DATA-POINTER', 'STALE-DONOR-ROUNDED', 'TARGET-DIFFERENT-SYMBOL', 'TARGET-OUTSIDE', 'UNPAIRED-FILE',
           'UNPAIRED-PORTED', 'UNPAIRED-SOURCE', 'UNRESOLVED',
           'GENERATOR-FILL'}   # the last is REPORTED, not a finding; triaged because it can hide a wrong duplicate pointer
# fuzz_grant's fs_ranges rows the patch drops, and the row the checker then pairs by position (AF0r.v donor line 41)
DROPPED = {'0x3cda4', '0x5d', '0x3d0a8', '0x67', '0x3d244', '0x73'}


def reason(d):
    v, f, ln = d['verdict'], d['src_file'] or d['dst_file'], d['src_line']
    sv, dv = d['src_value'], d['dst_value']
    if f == 'A/Rt/AF0r.v' and ln == '41' and v == 'STALE-DONOR-CODE-POINTER' and sv == '0x3cda4' and dv == '0x3c1b8':
        return ('A-fs-ranges.patch drops fuzz_grant\'s __asan_stack_malloc_0 / _2 / _4 rows (fuzz_uci links class 1 only: '
                'keyset classes = {1}, sites.py; BYTECMP.md), so the checker pairs donor row 0 (stack_malloc_0 0x3cda4) with '
                'target row 0, 0x3c1b8 = __asan_stack_malloc_1+0x0, the twin of donor row 1 (0x3cf18, 100) (range-table check)')
    if f == 'A/Rt/AF0r.v' and ln == '41' and v == 'UNPAIRED-SOURCE' and (sv in DROPPED or sv == '0x3cf18'):
        return ('fs_ranges position shift of A-fs-ranges.patch: a dropped row of class 0 / 2 / 4 (0x3cda4, 93), '
                '(0x3d0a8, 103), (0x3d244, 115), or donor row 1\'s start 0x3cf18, whose twin 0x3c1b8 is target row 0')
    if v == 'UNRESOLVED' and f == 'A/Rt/AF0s.v' and ln == '253' and sv == dv == '0x800b2400':
        return ('the donor\'s low-shadow lower bound 2148213760, left unchanged: it is at most kLowShadowBeg + IMG_TOP / 8 on '
                'both images (fuzz_grant.asan 0x800b6400, fuzz_uci.asan 0x800b5800; measure-sm1.py), so the lia step that '
                'proves it holds on fuzz_uci.asan (the build); the checker reads it as the shadow of a .bss address, a role '
                'it does not have')
    return None


def main():
    lines = open(sys.argv[1]).read().splitlines()
    h = next(i for i, l in enumerate(lines) if l.startswith('verdict\t'))
    cols = lines[h].split('\t')
    out, bad = [], 0
    for l in lines[h + 1:]:
        d = dict(zip(cols, l.split('\t')))
        if d.get('verdict') not in FLAGGED:
            continue
        r = reason(d)
        if r is None:
            bad += 1
            r = 'UNEXPLAINED'
            print(f"UNEXPLAINED {d['verdict']} {d['src_file'] or d['dst_file']}:{d['src_line']}/{d['dst_line']} "
                  f"{d['src_value']} -> {d['dst_value']} ({d.get('note', '')[:160]})")
        out.append((d['verdict'], d['src_file'], d['src_line'], d['dst_file'], d['dst_line'], d['src_value'], d['dst_value'], r))
    with open(sys.argv[2], 'w') as fh:
        fh.write('verdict\tsrc_file\tsrc_line\tdst_file\tdst_line\tsrc_value\tdst_value\treason\n')
        for row in out:
            fh.write('\t'.join(row) + '\n')
    print(f'triage-sm1: {len(out)} flagged / GENERATOR-FILL rows, {len(out) - bad} explained, {bad} unexplained')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
