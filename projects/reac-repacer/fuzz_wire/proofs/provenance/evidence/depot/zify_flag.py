#!/usr/bin/env python3
"""zify_flag.py [--image A|B] LIB FILE... -- glue rule E6: write ONE line,
    Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
directly after the last Require line of each named lib file (LIB/<side>/FILE).

Why (measured): in fuzz_grant's released order these grant-text files see the Zify flag FALSE; in this unit their
Require closure also loads knock's AFis text, which Requires AD3j (A/AFis.v:22), whose closure loads Reusable/YA02, whose
last top-level line sets the flag TRUE, so their lia calls change behaviour (A/AFk5.v / A/AFko.v hang). The line is Local,
so nothing leaks to importers; nothing else in the file changes. A file that already holds the line is left as is; a
file whose leading Require block cannot be found fails the run (nothing is written).
--e7: glue rule E7, the mirror case: the files named see the flag TRUE in fuzz_grant's released order and FALSE in
this unit's closure (Reusable/YA09 / YA08, last setting false, now load after YA02); the line written is the same with
constr:(true). A file never holds both lines (the run fails).
--image B maps lib/A -> lib/B and A<x> -> Y<x>."""
import os, re, sys

LINE = 'Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).'
LINE_E7 = 'Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).'


def main():
    args = sys.argv[1:]
    side, line, other = 'A', LINE, LINE_E7
    while args[:1] in (['--image'], ['--e7']):
        if args[0] == '--image':
            side, args = args[1], args[2:]
        else:
            line, other, args = LINE_E7, LINE, args[1:]
    if len(args) < 2:
        sys.exit(__doc__)
    lib, files = args[0], args[1:]
    todo = []
    for f in files:
        f_ = f if side == 'A' else 'Y' + f[1:]
        p = os.path.join(lib, side, f_)
        t = open(p, encoding='utf-8').read().split('\n')
        if other in t:
            sys.exit('zify_flag: FAIL %s already holds the other rule\'s line' % f_)
        if line in t:
            print('zify_flag: %s already holds the line' % f_)
            continue
        req = [k for k, l in enumerate(t[:120]) if re.search(r'\bRequire\b', l)]
        if not req:
            sys.exit('zify_flag: FAIL %s: no Require line in its first 120 lines' % f_)
        e = req[-1]
        while e < len(t) and not t[e].rstrip().endswith('.'):
            e += 1
        if e >= len(t):
            sys.exit('zify_flag: FAIL %s: the last Require sentence does not end' % f_)
        todo.append((p, t, e))
        print('zify_flag: %s: after line %d (%s)' % (f_, e + 1, t[e].strip()[:90]))
    for p, t, e in todo:
        open(p, 'w', encoding='utf-8').write('\n'.join(t[:e + 1] + [line] + t[e + 1:]))
    print('zify_flag: %d file(s) written' % len(todo))


if __name__ == '__main__':
    main()
