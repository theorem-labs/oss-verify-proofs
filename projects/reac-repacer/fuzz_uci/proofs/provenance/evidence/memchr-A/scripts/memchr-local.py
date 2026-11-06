#!/usr/bin/env python3
"""memchr-local.py LIB [--check]: make every `Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= ...` in
fuzz_uci's ported memchr walk files lib/{A,B}/Rt/{Memchr,MemchrChk}.v `Local`, so no file that imports them inherits
the redefinition (the form of core-B/reusable-local.py for YA09 / YA0e).

Why: the walk is ported from fuzz_boxreg's released lib/{A,B}/Rt/Memchr.v and MemchrChk.v (recipes 88154566652a),
where the redefinition is global; global_settings v10 (439f8e3bd463) reports each as ESCAPES TACTIC (4 in these four
files). A `Local` tactic redefinition still holds for the rest of its own file, so the file's own proofs see the same
tactic; only importers stop inheriting it, and the build of both images is the check that none relied on it.

CHECK (exit 1 on failure): for each file, its code with comments removed equals its input with every such
redefinition written `Local`, so the only change is that word; `--check` changes nothing and fails while a global one
remains."""
import re, sys

LIB = sys.argv[1]
CHECK = '--check' in sys.argv[2:]
FLAG = 'Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::='
GLOBAL = re.compile(r'(?<!Local )' + re.escape(FLAG))
FILES = ['A/Rt/Memchr.v', 'A/Rt/MemchrChk.v', 'B/Rt/Memchr.v', 'B/Rt/MemchrChk.v']


def strip_comments(t):
    out, i, depth, n = [], 0, 0, len(t)
    while i < n:
        if t.startswith('(*', i):
            depth += 1; i += 2; continue
        if depth and t.startswith('*)', i):
            depth -= 1; i += 2; continue
        if depth == 0:
            out.append(t[i])
        i += 1
    return ''.join(out)


bad = 0
for f in FILES:
    p = '%s/%s' % (LIB, f)
    t = open(p).read()
    u, n = GLOBAL.subn('Local ' + FLAG, t)
    local = t.count('Local ' + FLAG)
    same = ' '.join(strip_comments(u).split()) == ' '.join(strip_comments(GLOBAL.sub('Local ' + FLAG, t)).split())
    if CHECK:
        print('lib/%s: %d global, %d Local redefinition(s)' % (f, n, local))
        bad += 1 if n else 0
        continue
    print('lib/%s: %d global redefinition(s) made Local; only that word changed: %s' % (f, n, same))
    if not same:
        bad += 1
        continue
    open(p, 'w').write(u)
sys.exit(1 if bad else 0)
