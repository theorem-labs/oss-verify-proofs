#!/usr/bin/env python3
"""hdrscan.py FILE... -- counts, in the Coq COMMENTS of each file, what the committed-header rule forbids (with its
licence amendment): host paths, agent / lane / session names, cold or named branches, dates. Prints one
line per hit (file:line class token) and a per-class total; exit 1 if any hit. Comments are `(* ... *)`, nested, any
line span; strings are not special (none of the scanned files has a string literal holding `(*`).

  hdrscan.py [--quiet] FILE...
"""
import re, sys

CLASSES = [
    # the same five alternatives as before (home, mnt, tmp and root dirs, and the home tilde), factored so that this
    # file holds no literal host path
    ('host-path', re.compile(r'(?<![\w.])(?:/(?:home|mnt|tmp|root)/|~/)\S*')),
    ('agent/lane', re.compile(r'\b(?:h-(?:decbox|grant|rw|reader|box|rw-box|rw-dec|rw-man)[-\w]*|r-decbox|c-ship|port-reply|'
                              r'port-grant|UciStart\w*|UciB\w*Lane|pau-pipeline[-\w]*|h-decbox-a\d+|Omp-Session|session \w{8,}|'
                              r'lane\b|stream lead)\b', re.I)),
    ('branch', re.compile(r'\b(?:origin/[\w./-]+|cold/[\w./-]+|ossv/recipes|refs/heads/\S+)')),
    ('date', re.compile(r'\b20\d\d-\d\d(?:-\d\d)?\b|\b20\d\d\d\d\d\dT\d{4,6}Z?\b|\b\d\d:\d\dZ\b')),
]


def comments(text):
    """yield (line_number, comment_text) for every comment, nested comments included in their outer span."""
    i, n, depth, start = 0, len(text), 0, None
    while i < n - 1:
        two = text[i:i + 2]
        if two == '(*':
            if depth == 0:
                start = i
            depth += 1
            i += 2
            continue
        if two == '*)' and depth:
            depth -= 1
            i += 2
            if depth == 0:
                yield text.count('\n', 0, start) + 1, text[start:i]
            continue
        i += 1


def scan(path):
    hits = []
    t = open(path).read()
    for ln, c in comments(t):
        for cls, rx in CLASSES:
            for m in rx.finditer(c):
                hits.append((path, ln + c.count('\n', 0, m.start()), cls, m.group(0)))
    return hits


def main():
    quiet = '--quiet' in sys.argv
    files = [a for a in sys.argv[1:] if a != '--quiet']
    tot, allh = {c: 0 for c, _ in CLASSES}, []
    for f in files:
        h = scan(f)
        allh += h
        for _, _, c, _ in h:
            tot[c] += 1
        if not quiet:
            for p, ln, c, tok in h:
                print('%s:%d %s %s' % (p.split('/')[-1], ln, c, tok[:80]))
    per = {}
    for p, _, _, _ in allh:
        per[p.split('/')[-1]] = per.get(p.split('/')[-1], 0) + 1
    print('hdrscan: %d files, %d hits: %s; files with hits %d: %s' % (len(files), len(allh), tot, len(per),
                                                                     ' '.join('%s=%d' % kv for kv in sorted(per.items()))))
    sys.exit(1 if allh else 0)


main()
