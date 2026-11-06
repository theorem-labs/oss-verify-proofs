#!/usr/bin/env python3
"""header_rule.py [--check] PATH... -- apply the unit's header rule to Rocq files, rewriting comments only.

PATH is a .v file or a directory (every .v file under it). rule 24: proves no function.

The rule (the unit owner's header rule): a committed file names no host path, no agent or session, no date and no
lane branch; it keeps the donor's Copyright and SPDX lines and an UNDATED modification notice naming no agent
(Apache-2.0 s.4(b)). This script makes two rewrites, both inside Rocq comments `(* ... *)` only (nested comments and
string literals are lexed as Rocq lexes them; text outside comments is never touched, and the script refuses to write
a file whose comment-stripped text would change):

  1. `Modified by <NAME>, <YYYY-MM[-DD]>:`  ->  `Modified by <NAME>:`  (every notice is kept, only its date goes)
  2. an absolute path that reaches a repository file  ->  the repository-relative path (`.../proofs/x/y.v` -> `proofs/x/y.v`)

Then every comment of the result is checked against the rule's patterns (RULE below); a match is printed and the
script exits 2 without writing that file. --check writes nothing and exits 1 if a file would change or 2 if a file
breaks the rule after the rewrite.

Used by run.sh (beside this file) on port_core's WORK/stage-out, and by the start-up layer's writers on their
outputs, after each writer's own controls have compared its raw output with the donor's released text.
"""
import os
import re
import sys

# Patterns the header rule refuses (written so that this file does not match them itself).
RULE = [
    ('host path', re.compile(r'(?<![\w.~-])/(?:home|mnt|tmp|data|srv|root|Users)/[\w.@+-]+|(?<![\w.])~[/]')),
    ('agent or session name', re.compile(
        r'\b[hrc]-[a-z][a-z0-9]*(?:-[a-z0-9]+)+\b|\b[rc]-[a-z]{3,}\b|\bport-[a-z][a-z0-9-]*'
        r'|\bpau-pipe(?:line)|\buci-s[g]\b|\buci-core[A]|cgif[d]onor|\br[b]uild\b|Omp-Sess[i]on|ReallocPrim[a]ry'
        r'|\bUci(?!Syms\b|Shape\b|B\b)[A-Z][A-Za-z0-9]+|\bopen-u\d+|\bca-rp\d+|\bagent-open\d+')),
    ('date', re.compile(r'\b(?:19|20)\d\d-[01]\d\b|\b[0-2]\d:[0-5]\dZ\b|\b20\d{6}T\d{4,6}Z?')),
    ('lane branch', re.compile(r'\bcold[/]')),
]

NOTICE = re.compile(r'(Modified by [^,:*()\n]+?), (?:19|20)\d\d-[01]\d(?:-[0-3]\d)?:')
ABS_TO_REPO = re.compile(r'(?<![\w.~-])/(?:home|mnt|tmp|data|srv|root|Users)/[\w.@+/-]*?/(proofs/[\w.@+/-]+)')


def comment_spans(text):
    """[(start, end)] of the top-level comments of a Rocq text, end exclusive."""
    spans, i, n, depth, start, in_str = [], 0, len(text), 0, 0, False
    while i < n:
        c = text[i]
        if in_str:
            if c == '"':
                if i + 1 < n and text[i + 1] == '"':
                    i += 2
                    continue
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True
            i += 1
            continue
        if text.startswith('(*', i):
            if depth == 0:
                start = i
            depth += 1
            i += 2
            continue
        if depth and text.startswith('*)', i):
            depth -= 1
            i += 2
            if depth == 0:
                spans.append((start, i))
            continue
        i += 1
    if depth or in_str:
        raise ValueError('unterminated comment or string')
    return spans


def strip_comments(text):
    out, last = [], 0
    for s, e in comment_spans(text):
        out.append(text[last:s])
        last = e
    out.append(text[last:])
    return ''.join(out)


def rewrite_comment(c):
    c = NOTICE.sub(r'\1:', c)
    return ABS_TO_REPO.sub(r'\1', c)


def violations(text):
    found = []
    for s, e in comment_spans(text):
        for what, rx in RULE:
            for m in rx.finditer(text, s, e):
                found.append((text.count('\n', 0, m.start()) + 1, what, m.group()))
    return found


def apply(text):
    out, last = [], 0
    for s, e in comment_spans(text):
        out.append(text[last:s])
        out.append(rewrite_comment(text[s:e]))
        last = e
    out.append(text[last:])
    new = ''.join(out)
    if strip_comments(new) != strip_comments(text):
        raise AssertionError('a rewrite reached text outside comments')
    return new


def files(paths):
    for p in paths:
        if os.path.isdir(p):
            for root, dirs, fs in os.walk(p):
                dirs.sort()
                for f in sorted(fs):
                    if f.endswith('.v'):
                        yield os.path.join(root, f)
        else:
            yield p


def main(argv):
    check = argv[:1] == ['--check']
    paths = argv[1:] if check else argv
    if not paths:
        sys.exit(__doc__)
    changed = bad = total = 0
    for f in files(paths):
        total += 1
        text = open(f, encoding='utf-8').read()
        new = apply(text)
        v = violations(new)
        if v:
            bad += 1
            for line, what, m in v:
                print('header_rule: %s:%d: %s %r' % (f, line, what, m))
            continue
        if new != text:
            changed += 1
            if not check:
                with open(f, 'w', encoding='utf-8') as w:
                    w.write(new)
    print('header_rule: %d file(s), %d %s, %d breaking the rule after the rewrite'
          % (total, changed, 'to change' if check else 'rewritten', bad))
    if bad:
        return 2
    return 1 if check and changed else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
