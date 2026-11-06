#!/usr/bin/env python3
"""compare.py OUT SHIPPED -- the comparison record of a regenerated file OUT with the shipped file SHIPPED, on stdout.

Byte-equal files give the header line alone. Otherwise one line per differing hunk of lines (difflib, no junk
heuristic): the line ranges in OUT and in SHIPPED (1-based, inclusive; `-` for none), the sha256 (first 16 hex digits)
of each side's lines, and the numerals (0x... and decimals of 3 or more digits) that occur on one side of the hunk
only. A hunk whose two numeral columns are `-` changes no numeral. The record names no line text, so it can be shipped
for files whose text names things a record may not; the line ranges point into SHIPPED, where a reader reads them.
"""
import difflib
import hashlib
import os
import re
import sys

NUM = re.compile(r'(?<![\w.])(?:0x[0-9a-fA-F]+|\d{3,})(?![\w])')


def sha(lines):
    return hashlib.sha256(''.join(lines).encode()).hexdigest()[:16] if lines else '-'


def rng(lo, hi):
    return '%d-%d' % (lo + 1, hi) if hi > lo else '-'


def only(a, b):
    ca, cb = {}, {}
    for x in NUM.findall(''.join(a)):
        ca[x] = ca.get(x, 0) + 1
    for x in NUM.findall(''.join(b)):
        cb[x] = cb.get(x, 0) + 1
    out = []
    for x in sorted(ca, key=lambda s: (len(s), s)):
        out += [x] * max(0, ca[x] - cb.get(x, 0))
    return ','.join(out) or '-'


def main():
    if len(sys.argv) != 3:
        sys.exit('usage: compare.py OUT SHIPPED')
    out, shipped = sys.argv[1:]
    a, b = open(out).readlines(), open(shipped).readlines()
    ops = [o for o in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes() if o[0] != 'equal']
    ha = hashlib.sha256(open(out, 'rb').read()).hexdigest()
    hb = hashlib.sha256(open(shipped, 'rb').read()).hexdigest()
    print('# %s (sha256 %s) vs shipped %s (sha256 %s): %s' % (
        os.path.basename(out), ha, os.path.basename(shipped), hb,
        'byte-equal' if ha == hb else '%d differing hunk(s)' % len(ops)))
    if ha == hb:
        return
    print('hunk\tout_lines\tshipped_lines\tout_sha256\tshipped_sha256\tnumerals_only_in_out\tnumerals_only_in_shipped')
    for k, (tag, i1, i2, j1, j2) in enumerate(ops, 1):
        print('%d\t%s\t%s\t%s\t%s\t%s\t%s' % (k, rng(i1, i2), rng(j1, j2), sha(a[i1:i2]), sha(b[j1:j2]),
                                          only(a[i1:i2], b[j1:j2]), only(b[j1:j2], a[i1:i2])))


if __name__ == '__main__':
    main()
