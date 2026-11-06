#!/usr/bin/env python3
"""scrub.py --scanner SCANNER --repo REPO --orig-sha256 SHA ORIGINAL COPY RECORD RULE [RULE ...]

Writes a CLEANED COPY of an input that stays outside git because the name and path scanner flags some of its bytes,
for an input whose flagged bytes lie in a part that the tool reading it does not read. COPY and RECORD are paths
relative to REPO (the checkout the copy is committed in). Every byte of ORIGINAL is copied unchanged except the spans
that the RULEs select:
  line:N        line N, which must be one whole Rocq comment `(* ... *)`, becomes `(* <redacted> *)`
  json-str:KEY  the string value of the one `"KEY": "..."` member becomes "<redacted>"
RECORD is the diff ORIGINAL -> COPY: the sha256 and size of both, and for each span its line, its byte range in each
file, the removed text shown only as `<redacted>`, and the text written in its place.
Before it writes, ORIGINAL must have the sha256 SHA. After it writes, it runs SCANNER (the scanner of record) from
REPO on COPY and RECORD; when the scanner exits non-zero or reports a file with an uncleared flag-tier hit, both files
are removed and the script exits 1, so a copy that still holds a scanner needle is never left behind.
"""
import argparse
import hashlib
import os
import re
import subprocess
import sys
import tempfile

MARK = b'<redacted>'


def spans(data, rule):
    """[(start, end, replacement)] of one RULE over DATA"""
    kind, _, arg = rule.partition(':')
    if kind == 'line':
        n = int(arg)
        lines = data.split(b'\n')
        if not 1 <= n <= len(lines):
            sys.exit('scrub: line %d: the file has %d lines' % (n, len(lines)))
        start = sum(len(l) + 1 for l in lines[:n - 1])
        line = lines[n - 1]
        if not (line.startswith(b'(*') and line.endswith(b'*)')):
            sys.exit('scrub: line %d is not one whole Rocq comment' % n)
        return [(start, start + len(line), b'(* ' + MARK + b' *)')]
    if kind == 'json-str':
        pat = re.compile(b'"' + re.escape(arg.encode()) + b'": ("(?:[^"\\\\]|\\\\.)*")')
        found = list(pat.finditer(data))
        if len(found) != 1:
            sys.exit('scrub: json-str:%s matches %d members (need exactly one)' % (arg, len(found)))
        return [(found[0].start(1), found[0].end(1), b'"' + MARK + b'"')]
    sys.exit('scrub: unknown rule %r' % rule)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--scanner', required=True)
    ap.add_argument('--repo', required=True)
    ap.add_argument('--orig-sha256', required=True)
    ap.add_argument('original')
    ap.add_argument('copy')
    ap.add_argument('record')
    ap.add_argument('rules', nargs='+')
    a = ap.parse_args()
    data = open(a.original, 'rb').read()
    osha = hashlib.sha256(data).hexdigest()
    if osha != a.orig_sha256:
        sys.exit('scrub: the original has sha256 %s, not %s' % (osha, a.orig_sha256))
    sp = sorted(s for r in a.rules for s in spans(data, r))
    for (s0, e0, _), (s1, _, _) in zip(sp, sp[1:]):
        if s1 < e0:
            sys.exit('scrub: two rules select overlapping bytes')
    out, rec, pos = [], [], 0
    for s, e, rep in sp:
        out.append(data[pos:s])
        cs = sum(len(x) for x in out)
        out.append(rep)
        rec.append('@@ line %d: original bytes [%d, %d) -> copy bytes [%d, %d)\n-%s\n+%s\n'
                   % (data[:s].count(b'\n') + 1, s, e, cs, cs + len(rep), MARK.decode(), rep.decode()))
        pos = e
    out.append(data[pos:])
    copy = b''.join(out)
    head = ('scrub.py record: %s, a cleaned copy of an input outside git\n'
            'original sha256 %s (%d bytes)\n'
            'copy     sha256 %s (%d bytes)\n'
            'rules: %s\n'
            'Every byte outside the spans below is copied unchanged; removed text is shown only as %s.\n'
            % (a.copy, osha, len(data), hashlib.sha256(copy).hexdigest(), len(copy), ' '.join(a.rules),
               MARK.decode()))
    paths = [os.path.join(a.repo, a.copy), os.path.join(a.repo, a.record)]
    for p in paths:
        os.makedirs(os.path.dirname(p), exist_ok=True)
    open(paths[0], 'wb').write(copy)
    open(paths[1], 'w').write(head + ''.join(rec))
    with tempfile.TemporaryDirectory() as td:
        r = subprocess.run([a.scanner, os.path.join(td, 'scan'), a.copy, a.record], cwd=a.repo,
                           capture_output=True, text=True)
    if r.returncode != 0 or 'files with an uncleared flag-tier hit: 0\n' not in r.stdout:
        for p in paths:
            os.remove(p)
        sys.exit('scrub: REFUSED: the scanner flags the copy or its record (exit %d); both removed\n%s'
                 % (r.returncode, r.stdout[-2000:]))
    print('scrub: %s: original %s -> copy %s, %d span(s); scanner: 0 uncleared hits'
          % (a.copy, osha, hashlib.sha256(copy).hexdigest(), len(sp)))


if __name__ == '__main__':
    main()
