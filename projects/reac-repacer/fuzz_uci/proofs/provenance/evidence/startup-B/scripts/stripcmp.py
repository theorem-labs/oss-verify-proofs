#!/usr/bin/env python3
"""stripcmp.py OLD.v NEW.v -- prints the number of differing lines between the two files once every Coq comment
`(* ... *)` (nested, multi-line) is removed (comment bytes dropped, newlines inside a comment kept so lines align).
Exit 0 iff 0 lines differ and the line counts are equal."""
import difflib, sys


def strip(t):
    out, depth, i = [], 0, 0
    while i < len(t):
        two = t[i:i + 2]
        if two == '(*':
            depth += 1
            i += 2
            continue
        if two == '*)' and depth:
            depth -= 1
            i += 2
            continue
        if depth == 0 or t[i] == '\n':
            out.append(t[i])
        i += 1
    return ''.join(out).split('\n')


a, b = strip(open(sys.argv[1]).read()), strip(open(sys.argv[2]).read())
d = [l for l in difflib.unified_diff(a, b, lineterm='', n=0) if l[:1] in '+-' and not l.startswith(('+++', '---'))]
print('stripcmp %s: %d / %d lines, comment-stripped diff lines %d' % (sys.argv[2].split('/')[-1], len(a), len(b), len(d)))
sys.exit(0 if not d and len(a) == len(b) else 1)
