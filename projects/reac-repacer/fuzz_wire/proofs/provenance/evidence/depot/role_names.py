#!/usr/bin/env python3
"""role_names.py ROOT FILE=N... [--apply] -- cite each ruling by ROLE and time, never by the session that gave it.

Each word token of FILE (relative to ROOT) whose sha256 is a key of ROLES is a session name; it is rewritten to its
role phrase, by the form it stands in:
  NAME's          -> ROLE's
  NAME HH:MMZ     -> ROLE's ruling, HH:MMZ
  NAME            -> ROLE
(the names are keyed by sha256, so this file carries none of them). N is the number of hits the scanner of record
reported in FILE (its roster names): the run REFUSES (exit 1, nothing written) if FILE holds a different number of
roster-name tokens, if a token
of a .py file stands outside its comments and docstrings, or if a rewritten .py file's code (its AST without
docstrings) differs from the original. Without --apply it prints the per-file counts only."""
import ast, hashlib, re, sys

ROLES = {  # sha256(name)[:16] -> (role phrase, the name is on the scanner's roster)
    '4534039fb075cc24': ('the unit owner', True),
    'e8eb065d641b272d': ('the publication owner', False),
    'e6686bd0896453c2': ('the publish tool', False),
}
TOKEN = re.compile(r"[A-Za-z][A-Za-z0-9-]*[A-Za-z0-9]")
TIME = re.compile(r' (\d\d:\d\dZ)')


def key(w):
    return hashlib.sha256(w.encode()).hexdigest()[:16]


def code_ast(src):
    t = ast.parse(src)
    for n in ast.walk(t):
        b = getattr(n, 'body', None)
        if isinstance(b, list) and b and isinstance(b[0], ast.Expr) and isinstance(getattr(b[0], 'value', None), ast.Constant) \
                and isinstance(b[0].value.value, str):
            b.pop(0)
    return ast.dump(t)


def doc_and_comment_spans(src):
    """character spans of the comments and docstrings of a Python source"""
    import io, tokenize
    lines = src.splitlines(True)
    off = [0]
    for l in lines:
        off.append(off[-1] + len(l))
    spans = []
    for tk in tokenize.generate_tokens(io.StringIO(src).readline):
        if tk.type in (tokenize.COMMENT, tokenize.STRING):
            s = off[tk.start[0] - 1] + tk.start[1]
            e = off[tk.end[0] - 1] + tk.end[1]
            if tk.type == tokenize.COMMENT or src[s:e].lstrip('rbuRBU').startswith(('"""', "'''")):
                spans.append((s, e))
    return spans


def rewrite(t):
    out, last, n, other, where = [], 0, 0, 0, []
    for m in TOKEN.finditer(t):
        hit = ROLES.get(key(m.group(0)))
        if hit is None:
            continue
        role, roster = hit
        s, e = m.span()
        rest = t[e:e + 8]
        if rest.startswith("'s"):
            rep = role
        else:
            tm = TIME.match(t, e)
            if tm:
                rep, e = "%s's ruling, %s" % (role, tm.group(1)), tm.end()
            else:
                rep = role
        out.append(t[last:s]); out.append(rep); last = e; n += roster; other += not roster; where.append(s)
    out.append(t[last:])
    return ''.join(out), n, other, where


def main():
    root = sys.argv[1]
    apply = '--apply' in sys.argv[2:]
    jobs = [a.split('=') for a in sys.argv[2:] if a != '--apply']
    bad, new = [], {}
    for f, want in jobs:
        t = open('%s/%s' % (root, f), encoding='utf-8').read()
        r, n, other, where = rewrite(t)
        msg = '%s: %d roster-name token(s), %s expected; %d other name token(s)' % (f, n, want, other)
        if n != int(want):
            bad.append(msg)
        if f.endswith('.py'):
            spans = doc_and_comment_spans(t)
            if any(not any(s <= w < e for s, e in spans) for w in where):
                bad.append('%s: a name stands in code, not in a comment or docstring' % f)
            elif code_ast(t) != code_ast(r):
                bad.append('%s: the code (AST without docstrings) would change' % f)
        print(msg)
        new[f] = r
    if bad:
        sys.exit('role_names: REFUSED, nothing written: ' + '; '.join(bad))
    if apply:
        for f, r in new.items():
            open('%s/%s' % (root, f), 'w', encoding='utf-8').write(r)
        print('role_names: %d file(s) rewritten' % len(new))


if __name__ == '__main__':
    main()
