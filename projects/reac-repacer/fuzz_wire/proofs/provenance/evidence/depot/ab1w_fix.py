#!/usr/bin/env python3
"""ab1w_fix.py remove|rename LIB LIST.tsv -- the two AB1w edits ruled on the clause-2 check (ab1w_clause2.py).

LIB is the unit's lib directory (LIB/A/AB1w.v and every LIB/**/*.v is searched for readers).
remove: LIST.tsv rows `cell<TAB>value<TAB>symbol at value`. Each cell must have NO reader in any lib .v file (word
  match, its own Definition excluded), else the run refuses and writes nothing. Its sentence `Definition <cell> : Z :=
  <value>.` is cut from its AB1w line (the partner A / E definition on the same line stays); a line left empty goes.
rename: LIST.tsv rows `cell<TAB>value<TAB>symbol at value<TAB>new name`. Every cell and every word-match reader of it
  in the lib .v files is renamed in ONE pass (through unique placeholders, so swapped or cyclic pairs rename
  correctly). Refuses if a new name already names a cell that is not itself renamed away.
Both modes check that every cell VALUE kept in AB1w.v is byte-equal before and after, and print each change."""
import glob, os, re, sys

mode, lib, lst = sys.argv[1:4]
ab = os.path.join(lib, 'A', 'AB1w.v')
rows = [l.split('\t') for l in open(lst).read().splitlines()[1:] if l.strip()]
files = sorted(glob.glob(os.path.join(lib, '**', '*.v'), recursive=True))
text = {p: open(p, encoding='utf-8').read() for p in files}
DEF = re.compile(r'Definition (tfib_\w+?)\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+|\d+)\s*\.')  # every named Z cell of the table


def values(t):
    return {m.group(1): m.group(2) for m in DEF.finditer(t)}


before = values(text[ab])


def readers(name):
    w = re.compile(r"(?<![\w'])%s(?![\w'])" % re.escape(name))
    d = re.compile(r'Definition %s\b' % re.escape(name))
    out = []
    for p, t in text.items():
        for i, l in enumerate(t.split('\n')):
            if w.search(l) and not (p == ab and d.search(l) and len(w.findall(l)) == 1):
                out.append('%s:%d' % (os.path.relpath(p, lib), i + 1))
    return out


if mode == 'remove':
    bad = {c: readers(c) for c, *_ in rows if readers(c)}
    if bad:
        sys.exit('ab1w_fix: REFUSED, readers found: %s' % bad)
    lines = text[ab].split('\n')
    for c, v, sym, *_ in rows:
        if before.get(c) != v:
            sys.exit('ab1w_fix: REFUSED, %s value %s is not %s' % (c, before.get(c), v))
        pat = re.compile(r'[ \t]*Definition %s\s*:\s*Z\s*:=\s*%s\s*\.' % (re.escape(c), re.escape(v)))
        hit = [i for i, l in enumerate(lines) if l is not None and pat.search(l)]
        if len(hit) != 1 or len(pat.findall(lines[hit[0]])) != 1:
            sys.exit('ab1w_fix: REFUSED, %s sentence found on %d line(s)' % (c, len(hit)))
        i = hit[0]
        lines[i] = pat.sub('', lines[i]).rstrip()
        if not lines[i].strip():
            lines[i] = None
        print('ab1w_fix remove: AB1w.v:%d %s = %s (holds %s); readers: 0' % (i + 1, c, v, sym))
    text[ab] = '\n'.join(l for l in lines if l is not None)
elif mode == 'rename':
    ren = {c: n for c, v, sym, n in rows}
    for c, v, sym, n in rows:
        if before.get(c) != v:
            sys.exit('ab1w_fix: REFUSED, %s value %s is not %s' % (c, before.get(c), v))
        if n in before and n not in ren:
            sys.exit('ab1w_fix: REFUSED, new name %s already names a kept cell' % n)
    rd = {c: readers(c) for c in ren}
    for p in files:
        t = text[p]
        for k, c in enumerate(ren):
            t = re.sub(r"(?<![\w'])%s(?![\w'])" % re.escape(c), '@@AB1W_REN_%d@@' % k, t)
        for k, c in enumerate(ren):
            t = t.replace('@@AB1W_REN_%d@@' % k, ren[c])
        text[p] = t
    for c, v, sym, n in rows:
        print('ab1w_fix rename: %s -> %s = %s (holds %s); readers renamed: %s' % (c, n, v, sym, ', '.join(rd[c]) or 'none'))
else:
    sys.exit(__doc__)

after = values(text[ab])
gone = {c for c, *_ in rows} if mode == 'remove' else set()
ren = {r[0]: r[3] for r in rows} if mode == 'rename' else {}
for c, v in before.items():
    if c in gone:
        if c in after:
            sys.exit('ab1w_fix: FAIL, %s still defined' % c)
        continue
    n = ren.get(c, c)
    if after.get(n) != v:
        sys.exit('ab1w_fix: FAIL, %s (now %s) value %s -> %s' % (c, n, v, after.get(n)))
for p in files:
    if text[p] != open(p, encoding='utf-8').read():
        open(p, 'w', encoding='utf-8').write(text[p])
print('ab1w_fix %s: %d cell(s); every kept value byte-equal (%d cells checked)' % (mode, len(rows), len(after)))
