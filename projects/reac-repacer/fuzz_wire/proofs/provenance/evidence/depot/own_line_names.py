#!/usr/bin/env python3
"""own_line_names.py LIB DONOR_A -- rewrite a working-branch name to its bare commit in comment lines that are OURS.

A line is ours when it is not byte-equal to any line of the donor's released file of the same name (DONOR_A/<F>.v):
here the knock run's record-name rename (TfibSyms -> WireSyms, port_core 7a74e72920e6) changed two knock comment lines,
so they are no longer inherited text. In such a line `cold/<branch> <sha>` becomes `commit <sha>` (a record is named by
its commit, never by a working branch). Inherited lines (byte-equal to the donor's release) are not touched.
Every rewritten line must lie inside a comment (the comment-stripped token stream of the file is unchanged); the run
refuses otherwise, and prints each change."""
import os, re, sys

lib, donor = sys.argv[1:3]
SITES = ('AD3a.v', 'AD3b.v')
BR = re.compile(r'cold/[A-Za-z0-9][\w./-]*\s+([0-9a-f]{7,40})\b')


def strip(t):
    o, d, i = [], 0, 0
    while i < len(t):
        if t.startswith('(*', i):
            d, i = d + 1, i + 2
            continue
        if d and t.startswith('*)', i):
            d, i = d - 1, i + 2
            continue
        if not d:
            o.append(t[i])
        i += 1
    return re.findall(r"[\w.']+|[^\s\w]", ''.join(o))


HOST_DIRS = ('home', 'mnt', 'tmp', 'dev/shm')  # top-level host directories a record must not name
DIRTY = re.compile(r'\bh-[a-z]+-[a-z0-9]+\b|\bcold/(?=[A-Za-z0-9])|/(?:%s)/' % '|'.join(HOST_DIRS))  # lane / worker / branch / host text
total, pending = 0, []
for f in SITES:
    p = os.path.join(lib, 'A', f)
    t = open(p, encoding='utf-8').read()
    inh = set(open(os.path.join(donor, f), encoding='utf-8').read().split('\n'))
    lines = t.split('\n')
    n = 0
    for i, l in enumerate(lines):
        if l in inh or not BR.search(l):
            continue
        new = BR.sub(lambda m: 'commit ' + m.group(1), l)
        # fail closed: a line this step writes must not keep any lane / worker name, working branch or host path
        m = DIRTY.search(new)
        if m:
            sys.exit('own_line_names: REFUSED A/%s:%d: the rewritten line still carries %r; nothing written'
                     % (f, i + 1, m.group(0)))
        print('own_line_names: A/%s:%d (ours: not in the donor release)\n  - %s\n  + %s' % (f, i + 1, l.strip(), new.strip()))
        lines[i] = new
        n += 1
    out = '\n'.join(lines)
    if strip(out) != strip(t):
        sys.exit('own_line_names: FAIL A/%s: a change outside a comment; nothing written' % f)
    if n:
        pending.append((p, out))
    total += n
for p, out in pending:                       # written only after every site passed
    open(p, 'w', encoding='utf-8').write(out)
print('own_line_names: %d line(s) rewritten; comment-stripped token streams unchanged' % total)
