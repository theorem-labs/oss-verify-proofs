#!/usr/bin/env python3
"""scrub_input.py -- the one writer of a cleaned copy of a recorded input. Read-only on ORIG; writes OUT and
OUT.scrub.diff, nothing else.

A recorded input whose bytes fail the scanner is committed as a cleaned copy: named spans are replaced by UPPER_CASE
tokens, every other byte is copied.
  json  each --field KEY.PATH TOKEN names a string value of the JSON document; the bytes `"KEY": "VALUE"` must occur
        exactly once in ORIG, and the quoted VALUE becomes "TOKEN". The copy must parse to the original document with
        exactly those values set to their tokens.
  text  each --line-field N PREFIX TOKEN: line N (1-based) must start with PREFIX; the span after PREFIX up to the first
        `,` (or the end of the line) becomes TOKEN.
ORIG must have the sha256 given with --sha256 (the recorded bytes). OUT.scrub.diff is the diff ORIG -> OUT, one hunk
per changed line, with every removed span shown as <redacted>: the record holds none of the removed text.

It refuses its own output (exit 1; OUT and OUT.scrub.diff are left as they were) when the scanner given with
--scanner reports any hit (cleared or not, any tier) in OUT or OUT.scrub.diff, or when a removed span's bytes still
occur in either. The scanner is run on the two files under their own names, from a temporary directory; this file
holds no needle list.
usage: scrub_input.py {json,text} ORIG OUT --sha256 HEX --scanner PATH (--field KEY.PATH TOKEN | --line-field N PREFIX TOKEN)..."""
import argparse, csv, hashlib, json, os, re, subprocess, sys, tempfile

TOKEN = re.compile(r'[A-Z][A-Z0-9_]*')


def refuse(msg):
    sys.exit('scrub_input: REFUSED: ' + msg)


def json_edits(data, fields):
    """[(start, end, token)] of the quoted values the fields name, and the document they must give"""
    doc = json.loads(data)
    want, edits = json.loads(data), []
    for path, tok in fields:
        keys = path.split('.')
        node, tnode = doc, want
        for k in keys[:-1]:
            node, tnode = node[k], tnode[k]
        val = node[keys[-1]]
        if not isinstance(val, str):
            refuse('%s is not a string value' % path)
        tnode[keys[-1]] = tok
        lit = (json.dumps(keys[-1]) + ': ').encode()
        q = json.dumps(val).encode()
        n = data.count(lit + q)
        if n != 1:
            refuse('%s: its key and value occur %d times in ORIG, not once' % (path, n))
        s = data.index(lit + q) + len(lit)
        edits.append((s + 1, s + len(q) - 1, tok))      # inside the quotes
    return edits, want


def text_edits(data, line_fields):
    starts = [0] + [i + 1 for i, c in enumerate(data) if c == 0x0a]
    edits = []
    for n, prefix, tok in line_fields:
        n = int(n)
        if not 1 <= n <= len(starts):
            refuse('line %d is not in ORIG' % n)
        ls = starts[n - 1]
        le = data.find(b'\n', ls)
        le = len(data) if le < 0 else le
        p = prefix.encode()
        if not data[ls:le].startswith(p):
            refuse('line %d does not start with the given prefix' % n)
        s = ls + len(p)
        c = data.find(b',', s, le)
        e = le if c < 0 else c
        if e == s:
            refuse('line %d: the field after the prefix is empty' % n)
        edits.append((s, e, tok))
    return edits


def apply(data, edits):
    out, at = [], 0
    for s, e, tok in sorted(edits):
        if s < at:
            refuse('two named spans overlap')
        out += [data[at:s], tok.encode()]
        at = e
    return b''.join(out + [data[at:]])


def redacted_diff(data, new, edits, orig_sha, out_name, out_sha):
    """one hunk per changed line: `-` the original line with each removed span as <redacted>, `+` the copy's line"""
    starts = [0] + [i + 1 for i, c in enumerate(data) if c == 0x0a]
    nstarts = [0] + [i + 1 for i, c in enumerate(new) if c == 0x0a]
    by_line = {}
    for s, e, tok in sorted(edits):
        ln = max(i for i, st in enumerate(starts) if st <= s)
        by_line.setdefault(ln, []).append((s, e))
    rows = ['# written by scrub_input.py: every removed span is shown as <redacted>; nothing else differs',
            '--- original (sha256 %s)' % orig_sha, '+++ %s (sha256 %s)' % (out_name, out_sha)]
    for ln in sorted(by_line):
        ls = starts[ln]
        le = data.find(b'\n', ls)
        le = len(data) if le < 0 else le
        parts, at = [], ls
        for s, e in by_line[ln]:
            parts += [data[at:s], b'<redacted>']
            at = e
        minus = b''.join(parts + [data[at:le]])
        ns = nstarts[ln]
        ne = new.find(b'\n', ns)
        ne = len(new) if ne < 0 else ne
        rows += ['@@ -%d,1 +%d,1 @@' % (ln + 1, ln + 1), '-' + minus.decode(), '+' + new[ns:ne].decode()]
    return ('\n'.join(rows) + '\n').encode()


def scanner_hits(scanner, files):
    """every hits.tsv row the scanner writes for FILES (scanned under their base names), and its exit code"""
    with tempfile.TemporaryDirectory(prefix='scrub_input.') as d:
        names = []
        for name, b in files:
            open(os.path.join(d, name), 'wb').write(b)
            names.append(name)
        r = subprocess.run([scanner, os.path.join(d, 'scan')] + names, cwd=d, capture_output=True, text=True)
        tsv = os.path.join(d, 'scan', 'hits.tsv')
        if not os.path.isfile(tsv):
            refuse('the scanner wrote no hits.tsv (exit %d): %s' % (r.returncode, r.stderr.strip()[-300:]))
        rows = list(csv.reader(open(tsv, newline=''), delimiter='\t'))[1:]
        return r.returncode, [(row[0], row[3], row[2], row[4]) for row in rows if row]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['json', 'text'])
    ap.add_argument('orig')
    ap.add_argument('out')
    ap.add_argument('--sha256', required=True)
    ap.add_argument('--scanner', required=True)
    ap.add_argument('--field', nargs=2, action='append', default=[], metavar=('KEY.PATH', 'TOKEN'))
    ap.add_argument('--line-field', nargs=3, action='append', default=[], metavar=('N', 'PREFIX', 'TOKEN'))
    a = ap.parse_args()
    named = a.field if a.mode == 'json' else a.line_field
    if not named or (a.field and a.line_field):
        refuse('json takes --field only, text takes --line-field only, and at least one')
    for row in named:
        if not TOKEN.fullmatch(row[-1]):
            refuse('token %r is not UPPER_CASE' % row[-1])
    data = open(a.orig, 'rb').read()
    orig_sha = hashlib.sha256(data).hexdigest()
    if orig_sha != a.sha256:
        refuse('ORIG has sha256 %s, not the recorded %s' % (orig_sha, a.sha256))
    if a.mode == 'json':
        edits, want = json_edits(data, a.field)
    else:
        edits, want = text_edits(data, a.line_field), None
    new = apply(data, edits)
    if want is not None and json.loads(new) != want:
        refuse('the copy does not parse to the original document with only the named values replaced')
    out_name = os.path.basename(a.out)
    new_sha = hashlib.sha256(new).hexdigest()
    diff = redacted_diff(data, new, edits, orig_sha, out_name, new_sha)
    bad = []
    for s, e, _ in edits:
        span = data[s:e]
        for label, b in ((out_name, new), (out_name + '.scrub.diff', diff)):
            if span in b:
                bad.append('a removed span (%d bytes at offset %d) still occurs in %s' % (e - s, s, label))
    rc, hits = scanner_hits(a.scanner, [(out_name, new), (out_name + '.scrub.diff', diff)])
    bad += ['%s: scanner hit, needle %s (%s tier) at offset %s' % h for h in hits]
    if rc != 0 and not hits:
        bad.append('the scanner exited %d' % rc)
    if bad:
        for b in bad:
            print('scrub_input: REFUSED: ' + b, file=sys.stderr)
        sys.exit(1)
    os.makedirs(os.path.dirname(os.path.abspath(a.out)), exist_ok=True)
    for path, b in ((a.out, new), (a.out + '.scrub.diff', diff)):
        tmp = path + '.tmp'
        open(tmp, 'wb').write(b)
        os.replace(tmp, path)
    print('scrub_input: %s: %d spans replaced; original sha256 %s; copy sha256 %s; diff sha256 %s; scanner: 0 hits'
          % (out_name, len(edits), orig_sha, new_sha, hashlib.sha256(diff).hexdigest()))


if __name__ == '__main__':
    main()
