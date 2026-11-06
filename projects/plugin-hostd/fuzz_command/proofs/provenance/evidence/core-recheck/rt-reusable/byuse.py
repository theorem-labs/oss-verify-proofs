#!/usr/bin/env python3
"""By-use grep over a unit's lib/: where is a defined name READ?

A use is an identifier token equal to NAME (or a qualified token whose last component is NAME) outside comments, in
any .v file under LIB, other than the defining sentence itself. For each use the enclosing sentence head is printed
(the nearest line at or above the use that starts with a vernacular keyword), so a reader sees which statement or
definition reads the name.

Usage: byuse.py LIB NAME [DEF_FILE:DEF_LINE]   (DEF_FILE relative to LIB; that line is skipped)
As a module: uses(lib, name, skip=None) -> list of (file, line, head)."""
import os, re, sys

KW = re.compile(r'^\s*(?:#\[[^\]]*\]\s*)?(?:Local\s+|Global\s+|Program\s+)?(Definition|Fixpoint|Lemma|Theorem|Corollary|'
                r'Proposition|Fact|Remark|Example|Record|Structure|Inductive|Class|Instance|Existing|Notation|'
                r'Hypothesis|Hypotheses|Variable|Variables|Context|Axiom|Parameter|Let|Ltac|Section|Module|End|'
                r'Goal|Proof|Qed|Defined|Require|From|Import|Export)\b')
_cache = {}


def strip(text):
    """blank comments (nested) and string literals, keeping line structure"""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith('(*', i):
            depth += 1; out.append('  '); i += 2; continue
        if depth and text.startswith('*)', i):
            depth -= 1; out.append('  '); i += 2; continue
        c = text[i]
        if depth:
            out.append('\n' if c == '\n' else ' ')
        elif c == '"':
            j = text.find('"', i + 1)
            j = n - 1 if j < 0 else j
            out.append(re.sub(r'[^\n]', ' ', text[i:j + 1])); i = j + 1; continue
        else:
            out.append(c)
        i += 1
    return ''.join(out)


def files(lib):
    if lib not in _cache:
        res = []
        for root, _, fs in os.walk(lib):
            for f in sorted(fs):
                if f.endswith('.v'):
                    p = os.path.join(root, f)
                    res.append((os.path.relpath(p, lib), strip(open(p, encoding='utf-8', errors='replace').read()).split('\n')))
        _cache[lib] = sorted(res)
    return _cache[lib]


def uses(lib, name, skip=None):
    tok = re.compile(r"(?<![\w'.])(?:[A-Za-z_][\w']*\.)*" + re.escape(name) + r"(?![\w'])")
    res = []
    for rel, lines in files(lib):
        for i, line in enumerate(lines, 1):
            if skip and (rel, i) == skip:
                continue
            if tok.search(line):
                head = i
                while head > 1 and not KW.match(lines[head - 1]):
                    head -= 1
                h = lines[head - 1].strip()
                if re.match(r'\s*(Require|From|Import|Export)\b', h):
                    continue
                res.append((rel, i, h[:120]))
    return res


if __name__ == '__main__':
    lib, name = sys.argv[1], sys.argv[2]
    skip = None
    if len(sys.argv) > 3:
        f, l = sys.argv[3].rsplit(':', 1)
        skip = (f, int(l))
    for rel, i, h in uses(lib, name, skip):
        print(f'{rel}:{i}\t{h}')
