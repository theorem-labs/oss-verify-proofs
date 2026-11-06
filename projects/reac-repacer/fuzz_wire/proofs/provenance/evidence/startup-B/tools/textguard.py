#!/usr/bin/env python3
"""textguard.py -- the refusal check of the writers of this start-up set (fail closed on their inputs). A writer calls
refuse(text, what) on the text it is about to write, before it writes anything: a host path, a worker / owner / porting-
lane / workspace name, a named branch, a session trailer, a VM or tailnet host name, a private address, a date or a clock
time in that text stops the writer with exit 2, and nothing is written. So text that arrives through an option value or
a copied header (a donor's header, a plan's comments, a record copied into the slice) cannot reach a written file.

The name classes match by SHAPE and list no name (a list of the names seen so far misses the next one and ships the
names it forbids): the worker / owner, porting-lane, workspace and sub-lane shapes of the fuzz_uci image-B lane's
hdrscan.py (commit 12d2d13d7957, scripts/hdrscan.py, sha256 37612c2bd237), applied to the whole text, not only its
comments. The one date form a notice may carry, the month of a `(* Modified by Theorem Labs, YYYY-MM: ` head, is exempt,
as in the lane's hdrcheck.py; every other date is refused.

  python3 textguard.py FILE...     prints FILE:LINE:CLASS:TEXT per hit; exit 1 on any hit, else 0
"""
import re
import sys

# Each pattern is written so that this file's own text does not hold the token it refuses (e.g. `col[d]/`), because
# this file ships with the slice and is scanned like any other.
CLASSES = [
    ('host-path', re.compile(r'(?<![\w.])(?:/(?:home(?!/opam)|mnt|data|srv|Users|root|tmp|var/tmp)/|~[/])')),
    ('worker-name', re.compile(r'\b[hrc]-[a-z][a-z0-9]+(?:-[a-z0-9]+)*\b')),
    ('lane-name', re.compile(r'\bport-[a-z][a-z0-9]*(?:-[a-z0-9]+)*\b|\b[a-z][a-z0-9]*-pipeline(?:-[a-z0-9]+)*\b|'
                             r'\b\w+Lane\b|(?i:\bOmp-Session\b)')),
    ('branch', re.compile(r'\bcol[d]/|\borigi[n]/|\brefs/head[s]/')),
    ('host-name', re.compile(r'\b(?:open-[a-z]\d+|agent-?open\d*|agent[v]m\w*|decbox-a\d+-v\d+)\b|ts\.net', re.I)),
    ('private-ip', re.compile(r'\b(?:10\.\d+\.\d+\.\d+|192\.168\.\d+\.\d+|172\.(?:1[6-9]|2\d|3[01])\.\d+\.\d+|'
                              r'169\.254\.\d+\.\d+|100\.(?:6[4-9]|[7-9]\d|1[01]\d|12[0-7])\.\d+\.\d+)\b')),
    ('date', re.compile(r'\b20\d\d-[01]\d(?:-[0-3]\d)?\b')),
    ('clock', re.compile(r'\b[0-2]\d:[0-5][0-9xX]Z\b')),
]
NOTICE_MONTH = re.compile(r'^(\s*\(\* Modified by Theorem Labs), \d{4}-(?:0[1-9]|1[0-2]):')


def hits(text):
    """[(line, class, matched text)] for every forbidden token of text."""
    out = []
    for i, line in enumerate(text.split('\n'), 1):
        probe = NOTICE_MONTH.sub(r'\1:', line)
        for name, rx in CLASSES:
            for m in rx.finditer(probe):
                out.append((i, name, m.group(0)))
    return out


def refuse(text, what):
    """exit 2 before anything is written when text holds a forbidden token; return None otherwise."""
    h = hits(text)
    if h:
        for i, name, tok in h[:20]:
            sys.stderr.write('textguard: %s:%d: %s %r: refused, nothing written\n' % (what, i, name, tok))
        sys.stderr.write('textguard: %s: %d forbidden token(s): refused, nothing written\n' % (what, len(h)))
        raise SystemExit(2)


def main():
    bad = 0
    for p in sys.argv[1:]:
        for i, name, tok in hits(open(p, errors='replace').read()):
            bad += 1
            print('%s:%d:%s:%s' % (p, i, name, tok))
    print('textguard: %d file(s), %d hit(s)' % (len(sys.argv) - 1, bad))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
