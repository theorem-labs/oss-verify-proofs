#!/usr/bin/env python3
"""feq_controls.py -- planted controls for feq_check.py.

Each plant edits ONE line of an in-memory copy of one ported file (the files on disk are never written) so that the
gate's own comparison still calls the row equal, and shows that feq_check flags it:

  P1  jal in a fetch fact     lib/A/AE3e.v:282  jal x1 word: same opcode and rd, another target
  P2  j in a word definition  lib/A/AB1u.v:154  j word (Definition W_.. : bv 32): same opcode and rd, another target
  P3  SAME-CONTENT            lib/A/AFih.v:67   the NUL of "memory at address %p" (+20) replaced by the NUL of
                                                another string: the bytes from the value to its NUL are equal
                                                (both empty) and the 1-byte cell the line states reads 0 there too

The unplanted rows are run first (negative control: OK expected).
Usage: feq_controls.py --base COPYROOT --out controls.txt
"""
import argparse, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import feq_lib as L      # noqa: E402
import feq_check as C    # noqa: E402


def enc_jal(rd, imm):
    imm &= (1 << 21) - 1
    return (((imm >> 20) & 1) << 31) | (((imm >> 1) & 0x3ff) << 21) | (((imm >> 11) & 1) << 20) | \
           (((imm >> 12) & 0xff) << 12) | (rd << 7) | 0x6f


def gate_row(gates, run, dst_file, dst_line, verdict, tv=None):
    for g in gates[run]:
        if g['dst_file'] == dst_file and g['dst_line'] == dst_line and g['verdict'] == verdict and \
                (tv is None or g['tv'] == tv):
            r = dict(g)
            r['src_file'] = C.RUNS[run][0] + g['src_file']
            r['dst_file'] = C.RUNS[run][1] + g['dst_file']
            return r
    raise SystemExit(f'no gate row {run} {dst_file}:{dst_line} {verdict}')


def fresh(DST):
    return C.Side(DST.name, DST.T, DST.imgs)


def plant_line(DST, rel, ln, old, new):
    T = DST.T
    raw = '\n'.join(T.lines[rel])
    lines = raw.split('\n')
    assert old in lines[ln - 1], (rel, ln, old)
    lines[ln - 1] = lines[ln - 1].replace(old, new, 1)
    T.override(rel, '\n'.join(lines))
    return raw


def run_controls(gates, SRC, DST):
    out = []
    img = DST.imgs['A']

    def show(tag, run, row, D):
        st, meas = C.check_row(run, row, SRC, D)
        text = re.sub(r'(?<![\w/])(A|B|Reusable)/(\w+\.v)', r'lib/\1/\2', ' | '.join(meas))
        out.append(f'{tag}\t{run}\tlib/{row["dst_file"]}:{row["dst_line"]}\tsv={row["sv"]}\ttv={row["tv"]}\t'
                   f'status={st}\t' + text)
        return st

    # --- P1: jal in a fetch fact
    r1 = gate_row(gates, 'RA', 'AE3e.v', 282, 'INSN-SAME')
    w = int(r1['tv'], 16)
    pc = 0x9a8ac
    assert img.word(pc) == w
    tgt = [v for v, sz, n, t, b in img.syms if n == 'memcpy'][0]
    p1 = enc_jal((w >> 7) & 31, tgt - pc)
    assert p1 & 0xfff == int(r1['sv'], 16) & 0xfff        # the gate's coarse() keeps opcode + rd of a jal
    # --- P2: j in a word definition
    r2 = gate_row(gates, 'RA', 'AB1u.v', 154, 'INSN-SAME')
    w2 = int(r2['tv'], 16)
    pc2 = 0x9ebac
    assert img.word(pc2) == w2
    tgt2 = [v for v, sz, n, t, b in img.syms if n == 'memset'][0]
    p2 = enc_jal(0, tgt2 - pc2)
    assert p2 & 0xfff == int(r2['sv'], 16) & 0xfff
    # --- P3: SAME-CONTENT
    r3 = gate_row(gates, 'RA', 'AFih.v', 67, 'SAME-CONTENT', tv='0x1cf36')
    s, b, off = img.cstr(0x15512)
    p3 = s + len(b)                                   # the NUL that ends another string
    assert img.read(p3, 1) == b'\0' and img.read(0x1cf36, 1) == b'\0'

    out.append('# negative control: the unplanted rows')
    for tag, row in (('N1', r1), ('N2', r2), ('N3', r3)):
        show(tag, 'RA', row, fresh(DST))

    out.append('# planted rows (the gate compares a jal by opcode + rd only, and a string by its bytes up to the '
               'NUL: both plants keep what it compares)')
    raw = plant_line(DST, r1['dst_file'], r1['dst_line'], f'0x{w:08x}', f'0x{p1:08x}')
    st1 = show('P1', 'RA', dict(r1, tv=hex(p1)), fresh(DST))
    DST.T.override(r1['dst_file'], raw)
    raw = plant_line(DST, r2['dst_file'], r2['dst_line'], f'0x{w2:08x}', f'0x{p2:08x}')
    st2 = show('P2', 'RA', dict(r2, tv=hex(p2)), fresh(DST))
    DST.T.override(r2['dst_file'], raw)
    raw = plant_line(DST, r3['dst_file'], r3['dst_line'], 'mkChunk 0x1cf36', f'mkChunk {p3:#x}')
    st3 = show('P3', 'RA', dict(r3, tv=hex(p3)), fresh(DST))
    DST.T.override(r3['dst_file'], raw)
    out.append(f'# result: P1 {st1}, P2 {st2}, P3 {st3} (each must be other than OK); planted words '
               f'P1 {p1:#010x} (jal x{(w >> 7) & 31} to memcpy), P2 {p2:#010x} (j to memset), P3 value {p3:#x} '
               f'(the NUL of {b.decode()!r} at {s:#x})')
    return out, (st1, st2, st3)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--base', required=True)
    ap.add_argument('--out', required=True)
    a = ap.parse_args()
    SRC, DST = C.load(a.base)
    gates = {r: C.read_gate(os.path.join(a.base, f'runs/{r}/full.tsv')) for r in C.RUNS}
    out, sts = run_controls(gates, SRC, DST)
    with open(a.out, 'w') as f:
        f.write('\n'.join(out) + '\n')
    sys.exit(0 if all(s != 'OK' for s in sts) else 1)


if __name__ == '__main__':
    main()
