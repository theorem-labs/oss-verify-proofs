#!/usr/bin/env python3
"""resolve_imgtop.py IN IMGTOP OUT -- a copy of the Rocq file IN in which each citation `YImgTop.NAME` inside a
definition is replaced by the numeral that IMGTOP (lib/Reusable/YImgTop.v) defines for NAME (`Definition NAME : Z :=
<numeral>.`). `From` / `Require` lines and Ltac hook lines are copied unchanged.

Why: the start-up set's gen_ad1k.py reads the owned-static table (AF0m.v) with an evaluator that takes numerals and
`+` / `-` only, and fuzz_disco's AF0m.v writes the end of its last zero-shadow range as `YImgTop.IMG_TOP - 0xa5a00`.
gen_ad1k uses only the first zero-shadow range and the owned cells; this copy gives it the same values with the
citation resolved. Exit 1 when IN cites a NAME that IMGTOP does not define.
"""
import re
import sys


def main():
    if len(sys.argv) != 4:
        sys.exit('usage: resolve_imgtop.py IN IMGTOP OUT')
    src, imgtop, out = sys.argv[1:]
    defs = dict(re.findall(r'^Definition (\w+) : Z := (0x[0-9a-fA-F]+|\d+)\.$', open(imgtop).read(), re.M))
    n = 0
    lines = open(src).read().split('\n')
    for k, line in enumerate(lines):
        if line.startswith(('From ', 'Require ', '#[')):
            continue
        for name in re.findall(r'\bYImgTop\.(\w+)\b', line):
            if name not in defs:
                sys.exit('resolve_imgtop: %s line %d cites YImgTop.%s, which %s does not define' % (src, k + 1, name, imgtop))
        line2, c = re.subn(r'\bYImgTop\.(\w+)\b', lambda m: defs[m.group(1)], line)
        lines[k], n = line2, n + c
    open(out, 'w').write('\n'.join(lines))
    print('resolve_imgtop: %s -> %s (%d citation(s) resolved)' % (src, out, n))


if __name__ == '__main__':
    main()
