#!/usr/bin/env python3
"""nameonly.py -- every NAME-ONLY acceptance of strictcmp3 (rule 2: two compiler string labels `.str.N` whose bytes are
equal through the first NUL inside the object but whose labels differ, accepted without a difference) in this record's
compare set (out/strictcmp3-cmp.out and the ACCEPT lines of out/closure_strict3.out), RE-MEASURED by address: for each,
the bytes at the two target addresses are read from both images (up to 256 bytes) and the string through its first NUL
must be equal. Writes out/nameonly.tsv and prints the count. usage: nameonly.py"""
import lzma, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common

PAT = re.compile(r"NAME-ONLY\+(0x[0-9a-f]+)\[(0x[0-9a-f]+)\|(0x[0-9a-f]+)\]=(\S+)")


def text(name):
    p = os.path.join(common.OUT, name)
    return open(p).read() if os.path.exists(p) else lzma.open(p + '.xz', 'rt').read()


def main():
    sc = common.kit_module(common.CMP_PY)
    C, D = sc.Img(common.CGIF_B_TWIN), sc.Img(common.DECODE_B_TWIN)
    found = set()
    for l in text(common.CLOSURE_OUT).split('\n'):
        m = re.match(r'^   ACCEPT (\S+) @(0x[0-9a-f]+)/(0x[0-9a-f]+): (.*)$', l)
        if m:
            for t in PAT.finditer(m.group(4)):
                found.add((m.group(1), t.group(1), int(t.group(2), 16), int(t.group(3), 16), t.group(4)))
    for l in text(common.CMP_OUT).split('\n'):
        c = l.split('\t')
        if len(c) > 12 and c[1] == 'C:D' and c[0] != 'CSTR':
            for t in PAT.finditer(c[12]):
                found.add((c[0], t.group(1), int(t.group(2), 16), int(t.group(3), 16), t.group(4)))
    rows = []
    for fn, off, x, y, labels in sorted(found):
        hx, hy = C.home(x) if hasattr(C, 'home') else None, None
        bx, by = sc.frd(C, x, 256), sc.frd(D, y, 256)
        sx_ = bx[:bx.index(b'\0') + 1] if bx and b'\0' in bx else None
        sy_ = by[:by.index(b'\0') + 1] if by and b'\0' in by else None
        rows.append((fn, off, '%#x' % x, '%#x' % y, labels, repr(sx_), 'EQUAL' if sx_ is not None and sx_ == sy_ else 'DIFFERS'))
    with open(os.path.join(common.OUT, 'nameonly.tsv'), 'w') as f:
        f.write('function\tword\tX target\tY target\tlabels\tstring (through the NUL)\tre-measured\n')
        for r in rows:
            f.write('\t'.join(r) + '\n')
    print('NAME-ONLY acceptances in the compare set: %d; re-measured EQUAL %d, DIFFERS %d' % (
        len(rows), sum(r[6] == 'EQUAL' for r in rows), sum(r[6] == 'DIFFERS' for r in rows)))


if __name__ == '__main__':
    main()
