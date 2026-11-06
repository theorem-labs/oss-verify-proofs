#!/usr/bin/env python3
"""luitargets.py -- the lui targets of this record's compare set, from the kit's own output (out/closure_strict3.out and
out/strictcmp3-cmp.out): every `lui-in-section` differing target (a lui-built absolute value inside a section, rule 8 of
strictcmp3) -> scans/lui-targets.tsv; every `lui-const` acceptance (the kit's dataflow settled it as a constant) ->
scans/luiconst-targets.tsv. One row per (member, X address, word): `member, X addr, word, values` with values
`<x> in <section> | <y> in <section>`. Prints the counts. usage: luitargets.py"""
import ast, collections, lzma, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common


def text(name):
    p = os.path.join(common.OUT, name)
    return open(p).read() if os.path.exists(p) else lzma.open(p + '.xz', 'rt').read()


def main():
    lui, const = set(), set()
    # the closure: reported members carry their full differing-target list; ACCEPT lines carry lui-const acceptances
    for l in text(common.CLOSURE_OUT).split('\n'):
        m = re.match(r'^   (\S+) @(0x[0-9a-f]+): (.*)$', l)
        if m and not l.startswith('   ACCEPT '):
            v = m.group(3)
            i, j = v.find('[('), v.rfind(')]')
            if i >= 0:
                for t in ast.literal_eval(v[i:j + 2]):
                    if t[3] == 'lui-in-section':
                        lui.add((m.group(1), m.group(2), t[0], t[4][0]))
        m = re.match(r'^   ACCEPT (\S+) @(0x[0-9a-f]+)/(0x[0-9a-f]+): (.*)$', l)
        if m:
            for t in re.finditer(r'lui-const\+(0x[0-9a-f]+)\[(0x[0-9a-f]+)\|(0x[0-9a-f]+)\]=dataflow: (\S+) \| (\S+)', m.group(4)):
                const.add((m.group(1), m.group(2), t.group(1), '%s in %s | %s in %s' % (t.group(2), t.group(4), t.group(3), t.group(5))))
    # the 8 roots (strictcmp3 cmp): their target-differ column, and their lui-const acceptances
    for l in text(common.CMP_OUT).split('\n'):
        c = l.split('\t')
        if len(c) > 12 and c[1] == 'C:D' and c[0] != 'CSTR' and c[4].isdigit():
            if c[11].startswith('['):
                for t in ast.literal_eval(c[11]):
                    if t[3] == 'lui-in-section':
                        lui.add((c[0], c[2], t[0], t[4][0]))
            for t in re.finditer(r'lui-const\+(0x[0-9a-f]+)\[(0x[0-9a-f]+)\|(0x[0-9a-f]+)\]=dataflow: (\S+) \| (\S+)', c[12]):
                const.add((c[0], c[2], t.group(1), '%s in %s | %s in %s' % (t.group(2), t.group(4), t.group(3), t.group(5))))
    for name, rows in (('lui-targets.tsv', lui), ('luiconst-targets.tsv', const)):
        with open(os.path.join(common.SCANS, name), 'w') as f:
            f.write('member\tX addr\tword\tvalues\n')
            for r in sorted(rows):
                f.write('\t'.join(r) + '\n')
    print('lui-in-section targets %d in %d members; lui-const acceptances %d in %d members' % (
        len(lui), len({r[:2] for r in lui}), len(const), len({r[:2] for r in const})))


if __name__ == '__main__':
    main()
