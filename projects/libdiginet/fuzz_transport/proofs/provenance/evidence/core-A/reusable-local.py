#!/usr/bin/env python3
"""reusable-local.py LIB GRANTLIB: make every `Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= ...` in
the shared lib/Reusable/YA09.v and YA0e.v `Local`, so no file that imports them inherits the redefinition.

Measured with global_settings v10 439f8e3bd463: the two files carry 53 + 72 such GLOBAL redefinitions inside proofs
(ESCAPES 125, the same as fuzz_grant's released lib/Reusable copies); fuzz_grant's released lib/B copies make only 4 + 2
of them Local (ESCAPES 119). With all of them Local: ESCAPES 0. A `Local` tactic redefinition still holds for the rest
of its own file, so the file's own proofs see the same tactic; only importers stop inheriting it, and the build of
both images is the check that none relied on it.

CHECK (exit 1 on failure): each file's code (comments removed, module prefix and Require sentences normalised) equals
the RELEASED lib/B copy (GRANTLIB = fuzz_grant's released lib, recipes 4f87de75d67) once every such redefinition in
both is written `Local`: the only change against released text is that word."""
import re, sys

LIB, GL = sys.argv[1], sys.argv[2]
FLAG = 'Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::='
GLOBAL = re.compile(r'(?<!Local )' + re.escape(FLAG))


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


def code(t):
    t = strip_comments(t)
    t = re.sub(r'OssFuzzTheorems\.Proofs\.[\w]+\.[\w]+\.lib\.(?:B|Reusable)\b', 'LIB', t)
    reqs = []
    t = re.sub(r'From\s+(\S+)\s+Require\s+(Import\s+|Export\s+)?([^.]*)\.',
               lambda m: reqs.append((m.group(1), frozenset(m.group(3).split()))) or '', t)
    mods = set().union(*[s for _, s in reqs]) if reqs else set()
    return ' '.join(t.split()), mods


def local_all(t):
    return GLOBAL.subn('Local ' + FLAG, t)


bad = 0
for f in ('YA09.v', 'YA0e.v'):
    p = f'{LIB}/Reusable/{f}'
    u, n = local_all(open(p).read())
    ref, m = local_all(open(f'{GL}/B/{f}').read())
    same = code(u) == code(ref)
    print(f'Reusable/{f}: {n} global redefinitions made Local (released lib/B/{f} needs {m}); '
          f'code equals released lib/B/{f} with all Local: {same}')
    if not same:
        bad += 1
        continue
    open(p, 'w').write(u)
sys.exit(1 if bad else 0)
