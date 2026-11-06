#!/usr/bin/env python3
"""consumer_classify.py GRANT_A KNOCK_A FILE... -- for each lib/A FILE, the difference between fuzz_grant's released text
(GRANT_A = proofs/libreac/fuzz_grant/lib/A at 4f87de75d67) and libreac/fuzz_knock's released text (KNOCK_A = its lib/A at
88154566652a), with knock reduced to depot_has_trace = true exactly as depot_classify.py does, comments removed, module
paths / record names mapped, and every numeral replaced by NUM (the two cores are relocated onto different images, so
addresses differ by construction). The residue is what knock's consumer changes beyond the depot switch and the image.
Prints per file: switch constructs in knock's text, residue token count (punctuation-only residue counted apart), and
the first residue pieces."""
import difflib, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from depot_classify import tokens, reduce, drop_empty_requires, PUNCT  # noqa: E402

NUM = re.compile(r'^(?:0x[0-9a-fA-F]+|\d+|x[0-9a-fA-F]+)$')
KN = re.compile(r'^(?:KnBlockExt|KnLayoutGle|YC85)$')


def norm(ts):
    return [('NUM' if NUM.match(t) else t, ln) for t, ln in ts]


def main():
    ga, ka = sys.argv[1:3]
    for f in sys.argv[3:]:
        gp, kp = os.path.join(ga, f), os.path.join(ka, f)
        if not os.path.exists(kp):
            print('%s\tno knock counterpart' % f)
            continue
        if not os.path.exists(gp):
            print('%s\tno grant text' % f)
            continue
        kt = open(kp).read()
        nsw = len(re.findall(r'depot_pick|depot_has_trace', kt))
        g = norm(tokens(open(gp).read()))
        k = norm(drop_empty_requires(reduce(tokens(kt), [])))
        k = [x for x in k if not KN.match(x[0])]
        res = []
        for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, [t for t, _ in g], [t for t, _ in k], autojunk=False).get_opcodes():
            if tag != 'equal':
                res.append((g[i1:i2], k[j1:j2]))
        sub = [r for r in res if any(t not in PUNCT for t, _ in r[0] + r[1])]
        print('%s\tswitch constructs %d\tresidue pieces %d (punctuation-only %d)\t%s' % (
            f, nsw, len(sub), len(res) - len(sub),
            ' || '.join('grant:%d[%s] knock:%d[%s]' % (r[0][0][1] if r[0] else 0, ' '.join(t for t, _ in r[0])[:80],
                                                      r[1][0][1] if r[1] else 0, ' '.join(t for t, _ in r[1])[:80])
                        for r in sub[:3])))


if __name__ == '__main__':
    main()
