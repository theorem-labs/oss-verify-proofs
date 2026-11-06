#!/usr/bin/env python3
"""loadorder.py LIB TOP -- the order in which `rocq compile` loads the lib modules TOP Requires (each module's own
Requires first, in their textual order; a module loads once), and every loaded module that redefines
Zify.zify_convert_to_euclidean_division_equations_flag, with the value of its last top-level redefinition.
The flag TOP sees is set by the LAST redefining module loaded. LIB holds A/ and Reusable/ (or the flat grant layout).
A `Local Ltac` redefinition is not stored in the .vo, so it is not counted. This is a static ILLUSTRATION of the load
order only; the values of record are measured by flag_probe.py."""
import os, re, sys


def mods(lib):
    m = {}
    for d in ('A', 'Reusable', '.'):
        p = os.path.join(lib, d)
        if os.path.isdir(p):
            for f in os.listdir(p):
                if f.endswith('.v'):
                    m.setdefault(f[:-2], os.path.join(p, f))
    return m


def decomment(t):
    out, d, i = [], 0, 0
    while i < len(t):
        if t.startswith('(*', i):
            d, i = d + 1, i + 2
            continue
        if d and t.startswith('*)', i):
            d, i = d - 1, i + 2
            continue
        if not d:
            out.append(t[i])
        i += 1
    return ''.join(out)


REQ = re.compile(r'(?:From\s+\S+\s+)?Require(?:\s+(?:Import|Export))?\s+([^.]+?)\s*\.(?=\s|$)', re.S)
FL = re.compile(r'(?<!Local )(?<!Local\s)Ltac\s+Zify\.zify_convert_to_euclidean_division_equations_flag\s*::=\s*constr:\((true|false)\)')


def deps(path, M):
    out = []
    for m in REQ.finditer(decomment(open(path).read())):
        for n in m.group(1).split():
            b = n.split('.')[-1]
            if b in M:
                out.append(b)
    return out


def main():
    lib, top = sys.argv[1:3]
    M = mods(lib)
    seen, s = [], set()

    def visit(x):
        if x in s:
            return
        s.add(x)
        for y in deps(M[x], M):
            visit(y)
        seen.append(x)
    for y in deps(M[top], M):
        visit(y)
    red = []
    for x in seen:
        v = FL.findall(decomment(open(M[x]).read()))
        if v:
            red.append('%s(%s)' % (x, v[-1]))
    print('%s: %d lib modules loaded; flag redefiners in load order: %s' % (top, len(seen), ' '.join(red)))
    print('%s: load order: %s' % (top, ' '.join(seen)))


if __name__ == '__main__':
    main()
