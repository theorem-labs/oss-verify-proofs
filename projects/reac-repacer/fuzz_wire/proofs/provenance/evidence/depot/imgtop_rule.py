#!/usr/bin/env python3
"""imgtop_rule.py -- the one lineage rule for YImgTop (ruling (A) / (E1)), shared by depot_apply.py --imgtop-unfold and
closure_glue.py.

libreac/fuzz_knock's kernel defines `Definition IMG_LO : Z := ...` / `IMG_TOP` in Reusable/YImgTop.v, and its proofs
`unfold YImgTop.IMG_LO, YImgTop.IMG_TOP`; this unit keeps fuzz_grant's lineage, where YImgTop.v states them as
parsing-only Notations (a numeral after parsing), which `unfold` refuses (`Cannot coerce Zpos to an evaluable
reference`). Every other use of the two names (in a term) is the same number in both lineages. So the rule removes the
two names from the argument lists of `unfold` and nothing else: an `unfold` left with no argument is removed together
with the `;` or the `.` (and the space) after it; any other context refuses (exit). Code only (comments are not touched); a line keeps its
other text byte for byte.
"""
import re
import sys

UNFOLD = re.compile(r"\bunfold\s+(?P<args>[\w']+(?:\.[\w']+)*(?:\s*,\s*[\w']+(?:\.[\w']+)*)*)(?P<in>\s+in\s+(?:\*|[\w']+(?:\s*,\s*[\w']+)*)"
                    r"(?:\s*\|-\s*\*)?)?")
NAMES = ('YImgTop.IMG_LO', 'YImgTop.IMG_TOP')


def strip_imgtop_unfold(line):
    """(new line, number of names removed) for one line of code (the caller passes code lines only)"""
    out, last, n = [], 0, 0
    for m in UNFOLD.finditer(line):
        args = [a.strip() for a in m.group('args').split(',')]
        keep = [a for a in args if a not in NAMES]
        if len(keep) == len(args):
            continue
        n += len(args) - len(keep)
        out.append(line[last:m.start()])
        if keep:
            out.append('unfold ' + ', '.join(keep) + (m.group('in') or ''))
            last = m.end()
        else:
            rest = line[m.end():]
            k = re.match(r'\s*;\s*', rest) or re.match(r'\s*\.(?:\s+|$)', rest)
            if k:
                last = m.end() + k.end()
            else:
                sys.exit('imgtop_rule: an emptied `unfold` ends neither in `;` nor `.`: %r' % line)
    out.append(line[last:])
    return ''.join(out), n


if __name__ == '__main__':
    tests = [('unfold TFIB_IMG_END, YImgTop.IMG_TOP; lia', 'unfold TFIB_IMG_END; lia'),
             ('ltac:(unfold YImgTop.IMG_TOP; lia)', 'ltac:(lia)'),
             ('unfold a, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. lia.', 'unfold a in *. lia.'),
             ('unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; zdiv', 'zdiv'),
             ('- unfold YImgTop.IMG_TOP. lia.', '- lia.'),
             ('exact (f (YImgTop.IMG_TOP - YImgTop.IMG_LO, 3)).', 'exact (f (YImgTop.IMG_TOP - YImgTop.IMG_LO, 3)).')]
    bad = [(a, strip_imgtop_unfold(a)[0], b) for a, b in tests if strip_imgtop_unfold(a)[0] != b]
    print('imgtop_rule self-test: %d of %d' % (len(tests) - len(bad), len(tests)), bad)
    sys.exit(1 if bad else 0)
