#!/usr/bin/env python3
"""reported.py -- writes out/closure-reported.txt: every closure member the closure script REPORTED (its `   <name> @<addr>: ...`
lines, which list each member that is not EQUAL / EQUAL-mod-pcrel-with-every-target-equal), once, in first-seen order, as
`<name>\t<X address>`. Reads out/<closure>.out (or .out.xz). usage: reported.py"""
import lzma, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common


def main():
    p = os.path.join(common.OUT, common.CLOSURE_OUT)
    text = open(p).read() if os.path.exists(p) else lzma.open(p + '.xz', 'rt').read()
    rows = {}
    for l in text.split('\n'):
        m = re.match(r'^   (\S+) @(0x[0-9a-f]+): ', l)
        if m and not l.startswith('   ACCEPT '):
            rows.setdefault(m.group(1), m.group(2))
    with open(os.path.join(common.OUT, common.REPORTED), 'w') as f:
        f.write(''.join('%s\t%s\n' % kv for kv in rows.items()))
    print('reported members: %d' % len(rows))


if __name__ == '__main__':
    main()
