#!/usr/bin/env python3
"""triage-mm.py CHECK_TSV OUT_TSV WHY_TXT: the triage of a port_addr_check efa19b81e92b --fail-on-flags run over this
row's five files (donor = fuzz_pcap's released lib/B/Rt/Memmove*.v at recipes 5098883da0b with module paths renamed;
ported = the committed lib/B/Rt/{MemmoveDef,MemmoveIm,MemmoveK,MemmovePaths,Memmove}.v).

1. Every FLAGGED or GENERATOR-FILL row needs a measured reason. The run of record has none, so this script accepts
   none: any such row is printed UNEXPLAINED and the script exits 1 (the two planted pointers are caught this way).
2. The expected classes: the 60 numerals the relocation decided by hand (WHY_TXT = provenance/evidence/memmove-reloc/
   asan-resolve-B.why.txt, each `B/Rt/MemmovePaths.v:<line> <donor decimal>: <reason>`) are looked up in the run and
   each must carry the verdict its measured reason predicts:
     345540 (24 rows) the return address __asan_region_is_poisoned+0x174: SAME-SYMBOL, donor 0x545c4 -> 0x53a34
                      (342580), both sides resolved `decimal return site: __asan_region_is_poisoned+0x174`;
     538627, 571523   (18 rows each) the instruction words ld x16, 0(x16) = 0x83803 and ld x17, 0(x17) = 0x8b883:
                      NON-ADDRESS-SAME, the value kept.
   A row missing or with another verdict is printed EXPECTED-CLASS-MISMATCH and the script exits 1.
OUT_TSV gets one line per flagged row (reason or UNEXPLAINED) and one line per expected-class row."""
import re
import sys

FLAGGED = {'ARITH-MISMATCH', 'DIFFERENT-SYMBOL', 'FLAGS-NOT-DECOMPOSABLE', 'GEOMETRY-CHANGED', 'GP-NOT-GLOBAL-POINTER',
           'HASH-UNCHANGED', 'IMAGE-EXTENT-CHANGED', 'IMAGE-EXTENT-STALE-ABOVE', 'IMAGE-EXTENT-STALE-BELOW', 'INSN-CHANGED',
           'KIND-CHANGED', 'LABEL-COMPARED-WITH-PC', 'LABEL-MIXED', 'NO-COUNTERPART', 'NON-ADDRESS-CHANGED',
           'SAME-VALUE-DIFFERENT-OBJECT', 'SLID-TO-NEIGHBOUR', 'STALE-DERIVED-QUOTIENT', 'STALE-DONOR-CODE-POINTER',
           'STALE-DONOR-DATA-POINTER', 'STALE-DONOR-ROUNDED', 'TARGET-DIFFERENT-SYMBOL', 'TARGET-OUTSIDE', 'UNPAIRED-FILE',
           'UNPAIRED-PORTED', 'UNPAIRED-SOURCE', 'UNRESOLVED',
           'GENERATOR-FILL'}   # the last is REPORTED, not a finding; triaged because it can hide a wrong duplicate pointer
RA = 'decimal return site: __asan_region_is_poisoned+0x174'
# donor decimal -> (verdict, src_value, dst_value, src_res, dst_res) the measured reason predicts (None = not compared)
EXPECT = {345540: ('SAME-SYMBOL', '0x545c4', '0x53a34', RA, RA),
          538627: ('NON-ADDRESS-SAME', '0x83803', '0x83803', None, None),
          571523: ('NON-ADDRESS-SAME', '0x8b883', '0x8b883', None, None)}


def main():
    tsv, out_tsv, why = sys.argv[1:4]
    lines = open(tsv).read().splitlines()
    h = next(i for i, l in enumerate(lines) if l.startswith('verdict\t'))
    cols = lines[h].split('\t')
    rows = [dict(zip(cols, l.split('\t'))) for l in lines[h + 1:]]
    out, bad = [], 0
    for d in rows:
        if d.get('verdict') not in FLAGGED:
            continue
        bad += 1
        print(f"UNEXPLAINED {d['verdict']} {d['src_file'] or d['dst_file']}:{d['src_line']}/{d['dst_line']} "
              f"{d['src_value']} -> {d['dst_value']} ({d.get('note', '')[:160]})")
        out.append(('flagged', d['verdict'], d['src_file'], d['src_line'], d['dst_file'], d['dst_line'], d['src_value'],
                    d['dst_value'], 'UNEXPLAINED'))
    miss = 0
    seen = {}
    for l in open(why):
        m = re.match(r'(B/Rt/\S+\.v):(\d+) (\d+): (.*)', l.strip())
        if not m:
            continue
        f, ln, dv, reason = m.group(1), m.group(2), int(m.group(3)), m.group(4)
        verdict, sv, tv, sres, tres = EXPECT[dv]
        hit = [d for d in rows if d['dst_file'] == f and d['dst_line'] == ln and d['src_value'] == sv]
        ok = len(hit) == 1 and hit[0]['verdict'] == verdict and hit[0]['dst_value'] == tv and \
            (sres is None or (hit[0]['src_res'] == sres and hit[0]['dst_res'] == tres))
        got = (f"{hit[0]['verdict']} {hit[0]['src_value']} -> {hit[0]['dst_value']} [{hit[0]['src_res']} | {hit[0]['dst_res']}]"
               if len(hit) == 1 else f'{len(hit)} rows')
        if not ok:
            miss += 1
            print(f'EXPECTED-CLASS-MISMATCH {f}:{ln} {dv}: expected {verdict} {sv} -> {tv}, got {got}')
        seen[(dv, verdict if ok else 'MISMATCH')] = seen.get((dv, verdict if ok else 'MISMATCH'), 0) + 1
        out.append(('expected-class', hit[0]['verdict'] if len(hit) == 1 else '-', f, ln, f, ln, sv,
                    hit[0]['dst_value'] if len(hit) == 1 else '-', ('OK: ' if ok else 'MISMATCH: ') + reason))
    with open(out_tsv, 'w') as fh:
        fh.write('kind\tverdict\tsrc_file\tsrc_line\tdst_file\tdst_line\tsrc_value\tdst_value\treason\n')
        for row in out:
            fh.write('\t'.join(row) + '\n')
    print(f'triage-mm: {bad} flagged / GENERATOR-FILL rows, 0 explained, {bad} unexplained')
    print('triage-mm: expected classes of the 60 resolved rows: ' +
          ', '.join(f'{dv} {v} x{n}' for (dv, v), n in sorted(seen.items())) + f'; {miss} mismatched')
    sys.exit(1 if bad or miss else 0)


if __name__ == '__main__':
    main()
