#!/usr/bin/env python3
"""triage-sm1.py CHECK_TSV OUT_TSV: one line per FLAGGED or GENERATOR-FILL row of a port_addr_check e165063a0081
--fail-on-flags run over this slice's files (donor = the run's stage/, renamed fuzz_grant text; ported = the committed
lib/B/Rt/YF0r.v, YF0s.v, lib/Reusable/YF0v.v), with the measured reason that accepts it. A row no rule below accepts is
printed as UNEXPLAINED and the script exits 1. Each rule names the exact file, donor line and values it accepts."""
import sys

FLAGGED = {'ARITH-MISMATCH', 'DIFFERENT-SYMBOL', 'FLAGS-NOT-DECOMPOSABLE', 'GEOMETRY-CHANGED', 'GP-NOT-GLOBAL-POINTER',
           'HASH-UNCHANGED', 'IMAGE-EXTENT-CHANGED', 'IMAGE-EXTENT-STALE-ABOVE', 'IMAGE-EXTENT-STALE-BELOW', 'INSN-CHANGED',
           'KIND-CHANGED', 'LABEL-COMPARED-WITH-PC', 'LABEL-MIXED', 'NO-COUNTERPART', 'NON-ADDRESS-CHANGED',
           'SAME-VALUE-DIFFERENT-OBJECT', 'SLID-TO-NEIGHBOUR', 'STALE-DERIVED-QUOTIENT', 'STALE-DONOR-CODE-POINTER',
           'STALE-DONOR-DATA-POINTER', 'STALE-DONOR-ROUNDED', 'TARGET-DIFFERENT-SYMBOL', 'TARGET-OUTSIDE', 'UNPAIRED-FILE',
           'UNPAIRED-PORTED', 'UNPAIRED-SOURCE', 'UNRESOLVED',
           'GENERATOR-FILL'}   # the last is REPORTED, not a finding; triaged because it can hide a wrong duplicate pointer
FS_N_LINES = {('B/Rt/YF0r.v', '35'), ('B/Rt/YF0r.v', '249'), ('B/Rt/YF0s.v', '56')}
# fuzz_grant's fs_ranges rows the patch drops, and the row the checker then pairs by position (YF0r.v donor line 43)
DROPPED = {'0x3cf4c', '0x5d', '0x3d250', '0x67', '0x3d3ec', '0x73'}


def reason(d):
    v, f, ln = d['verdict'], d['src_file'] or d['dst_file'], d['src_line']
    sv, dv = d['src_value'], d['dst_value']
    if v == 'GEOMETRY-CHANGED' and (f, ln) in FS_N_LINES and sv == dv == '0x2000':
        return ('FS_N = 8192, the number of class-1 fake frames (YF0r.v fs_frames_cid : fs_frames CID = FS_N, Qed by '
                'vm_compute): a model constant, not image geometry; the same in both images')
    if f == 'B/Rt/YF0r.v' and ln == '43' and v == 'STALE-DONOR-CODE-POINTER' and sv == '0x3cf4c' and dv == '0x3c1b8':
        return ('B-fs-ranges.patch drops fuzz_grant\'s __asan_stack_malloc_0 / _2 / _4 rows (fuzz_uci links class 1 only: '
                'keyset classes = {1}; BYTECMP.md), so the checker pairs donor row 0 (stack_malloc_0 0x3cf4c) with target '
                'row 0, 0x3c1b8 = __asan_stack_malloc_1+0x0, the twin of donor row 1 (0x3d0c0, 100) (range-table check)')
    if f == 'B/Rt/YF0r.v' and ln == '43' and v == 'UNPAIRED-SOURCE' and (sv in DROPPED or sv == '0x3d0c0'):
        return ('fs_ranges position shift of B-fs-ranges.patch: a dropped row of class 0 / 2 / 4 (0x3cf4c, 93), '
                '(0x3d250, 103), (0x3d3ec, 115), or donor row 1\'s start 0x3d0c0, whose twin 0x3c1b8 is target row 0')
    if v == 'UNRESOLVED' and f == 'B/Rt/YF0s.v' and ln == '255' and sv == '0x800b6600' and dv == '0x800b5800':
        return ('the override of overrides-sm1.tsv: kLowShadowBeg + IMG_TOP / 8 = 0x7fff7000 + 0x5f4000 / 8 (measure-sm1.py; '
                'the same rule on fuzz_grant prints the donor\'s 0x800b6600); the checker reads it as the shadow of a .bss '
                'address, a role it does not have')
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
