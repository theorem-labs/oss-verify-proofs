#!/usr/bin/env python3
"""d1w_close.py [--image A|B] LIB -- supply the closed as_const_g2 pair to the two D1W_ok abbreviations that lack it.

D1W_ok (A/AFix.v, A/AFjb.v) takes the Section Variable `as_const_g2` and the Hypothesis `as_const_g2_def` right after
`Hgp`. A/AFj2.v writes its abbreviation with the closed pair `AD3j.as_const_g2f AD3j.as_const_g2f_def`; A/AFjg.v
passes the same pair at its one application. A/AFj1.v and A/AFjf.v abbreviate D1W_ok without the pair (knock's text
is the same; neither file applies the abbreviation). This rule writes the same closed pair into those two
abbreviations, so no abbreviation of D1W_ok leaves the Section variable open (review of AF0w, condition (d), item 2).

LIB is the unit's lib directory (the one holding A/ or B/). --image B maps lib/A -> lib/B and the file / module
names A<x> -> Y<x>. Each site must match exactly once, else the script fails and writes nothing.
"""
import os, sys

SITES = [
    # (file, abbreviation head, last Section argument before the pair)
    ('AFj1.v', 'Local Abbreviation D1W_ok := (@AFix.D1W_ok ', ' Hgp).'),
    ('AFjf.v', 'Local Abbreviation D1W_ok := (@AFjb.D1W_ok ', ' Hgp).'),
]
PAIR = ' AD3j.as_const_g2f AD3j.as_const_g2f_def'


def side(name, image):
    return name if image == 'A' else 'Y' + name[1:]


def main():
    args = sys.argv[1:]
    image = 'A'
    if args[:1] == ['--image']:
        image = args[1]
        args = args[2:]
    if image not in ('A', 'B') or len(args) != 1:
        sys.exit(__doc__)
    sub = os.path.join(args[0], image)
    out = {}
    for f, head, tail in SITES:
        f_, head_ = side(f, image), head.replace('@AFix.', '@%s.' % side('AFix', image)).replace('@AFjb.', '@%s.' % side('AFjb', image))
        pair = PAIR.replace('AD3j.', '%s.' % side('AD3j', image))
        p = os.path.join(sub, f_)
        lines = open(p, encoding='utf-8').read().split('\n')
        hits = [i for i, l in enumerate(lines) if l.startswith(head_)]
        if len(hits) != 1:
            sys.exit('d1w_close: FAIL %s: %d abbreviation line(s) of D1W_ok' % (f_, len(hits)))
        i = hits[0]
        if pair.strip() in lines[i]:
            print('d1w_close: %s:%d already closed' % (f_, i + 1))
            continue
        if not lines[i].endswith(tail) or lines[i].count(tail) != 1:
            sys.exit('d1w_close: FAIL %s:%d does not end with %r' % (f_, i + 1, tail))
        new = lines[i][:-len(tail)] + tail[:-2] + pair + ').'
        out[p] = (lines, i, new)
        print('d1w_close: %s:%d: ...%s  ->  ...%s' % (f_, i + 1, lines[i][-30:], new[-70:]))
    for p, (lines, i, new) in out.items():
        lines[i] = new
        open(p, 'w', encoding='utf-8').write('\n'.join(lines))
    print('d1w_close: %d site(s) written' % len(out))


if __name__ == '__main__':
    main()
