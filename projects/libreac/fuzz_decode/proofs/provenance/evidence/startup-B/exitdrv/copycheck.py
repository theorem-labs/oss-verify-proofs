#!/usr/bin/env python3
"""copycheck.py -- proves that the record files in this directory are the exit-driver record of libreac/fuzz_decode
with named tokens put in, and nothing else.

The original is the directory DIR at commit ORIG (below) of the hub repository. Each file of this directory that is
not a file of this check (NEW) is a copy of the one file of DIR at ORIG that, with the copy's spans put in, is the
copy, byte for byte (found by its bytes, so a copy may carry another name than its original). copy-edits.tsv
beside this file lists every replaced span: file (the copy's name), line, byte offset, length, sha256 of the removed
bytes, class, token. This checker holds none of the removed text and needs none: it reads the original from git and
checks, failing on the first breach:
  1. each copy has exactly one original in DIR at ORIG and that original's mode; COPY.md's file table is, row for row,
     the table that --write-table writes: every file of this directory (COPY.md and SHA256SUMS aside, as each names
     the other's sha256) with, for a copy, the first 12 hex digits of its original's file sha256 as read from git (a
     file of this check has `-`), the sha256 of its bytes on disk and the number of its spans;
  2. each span of copy-edits.tsv: inside its file and on its listed line, no newline in it, no overlap, removed bytes
     with the listed sha256, a whole token (the bytes on either side cannot extend it; a WORKDIR span is a directory
     stem, so the byte after it is `/`), of the form its class allows, with an UPPER_CASE token of that class; no
     removed span holds a number (0x..., three or more digits, or eight or more hex digits; a WORKFILE span's compact
     date-time stamp, 8 digits T 6 digits Z, is its only allowed run of digits): no value, address, verdict or count is
     in a removed span;
  3. one token per removed text, in every class, and one removed text per token in every class but WORKDIR (WORKDIR
     stands for any directory of a worker's own work tree, so it replaces several stems);
  4. the original with exactly these spans replaced by their tokens is this directory's file, byte for byte; a file
     without a span is byte-identical to the original;
  5. no removed span's bytes occur as a whole token (with the boundaries of its class) in any file of this directory;
  6. COPY.diff is the redacted diff the spans give (one hunk per changed line: `-` the original line with every
     removed span as <redacted>, `+` the copy's line), byte for byte;
  7. SHA256SUMS lists every file of this directory but itself, each with the sha256 of its bytes (sha256sum format);
  8. with --scanner PATH (the scanner of record): the scanner exits 0 on this directory's files with no blocking hit,
     and every blocking hit it reports in the original lies inside a replaced span.
usage: copycheck.py REPO [--scanner PATH] [--write-diff] [--write-table]   (--write-diff writes COPY.diff and
--write-table writes COPY.md's file table, instead of comparing them)
The scanner runs in a temporary directory (tempfile: $TMPDIR when set)."""
import argparse, collections, csv, hashlib, os, re, subprocess, sys, tempfile

ORIG = 'fadeeb148437a4303c8c69628e82fb04c844c523'
DIR = 'proofs/libreac/fuzz_decode/provenance/startup-gen/A/exitdrv'
HERE = os.path.dirname(os.path.abspath(__file__))
NEW = ('COPY.md', 'COPY.diff', 'copycheck.py', 'copy-edits.tsv', 'SHA256SUMS', 'README.md')
CLASS = {   # class: (form of the removed bytes, tokens of the class)
    'PATH': (rb'/[A-Za-z0-9._+/-]+', {'HUB'}),
    'NAME': (rb'[a-z][a-z0-9]*(?:-[a-z0-9]+)+', {'OWNER_WORKER', 'PORTER_WORKER'}),
    'TOOL': (rb'[a-z][a-z0-9]*(?:-[a-z0-9]+)*', {'MAP_TOOL', 'MAP_KIT'}),
    'LANE': (rb'[A-Z][a-z0-9]+(?:[A-Z][a-z0-9]+)+|[a-z][a-z0-9]*(?:-[a-z0-9]+)+', {'LANE_1', 'LANE_2', 'LANE_3'}),
    'WORKDIR': (rb'[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)*', {'WORKDIR'}),
    'WORKFILE': (rb'[A-Za-z0-9_-]+\.(?:md|log)', {'WORKDIR_NOTE_1', 'WORKDIR_NOTE_2', 'WORKDIR_LOG'}),
}
MANY = {'WORKDIR'}   # classes whose token may replace more than one text
STAMP = re.compile(rb'\d{8}T\d{6}Z')
NUMBER = re.compile(rb'0x|\d{3}|[0-9a-f]{8}')
HEAD = ['| file | original file sha256 (12 hex) | sha256 as shipped | spans |', '|---|---|---|---|']


def fail(msg):
    sys.exit('copycheck: FAIL: ' + msg)


def git(repo, *a):
    return subprocess.run(['git', '-C', repo] + list(a), check=True, capture_output=True).stdout


def originals(repo):
    """{name: (mode, bytes)}: every file of DIR at ORIG, as read from git"""
    out = {}
    for ln in git(repo, 'ls-tree', '-z', ORIG + ':' + DIR).split(b'\0'):
        if not ln: continue
        meta, name = ln.split(b'\t', 1)
        mode, kind, obj = meta.split()
        if kind == b'blob': out[name.decode()] = (mode.decode(), git(repo, 'cat-file', 'blob', obj.decode()))
    return out


def shipped():
    out = {}
    for root, dirs, files in os.walk(HERE):
        dirs[:] = [d for d in dirs if d != '__pycache__']
        for f in files:
            p = os.path.join(root, f)
            out[os.path.relpath(p, HERE)] = (os.stat(p).st_mode, open(p, 'rb').read())
    return out


def edits():
    rows = list(csv.DictReader(open(os.path.join(HERE, 'copy-edits.tsv'), newline=''), delimiter='\t'))
    by = collections.defaultdict(list)
    for r in rows:
        by[r['file']].append((int(r['offset']), int(r['length']), r['removed_sha256'], r['class'], r['token'],
                              int(r['line'])))
    return by, len(rows)


def check_span(rel, data, s, n, sha, cls, tok, line):
    e = s + n
    where = '%s line %d offset %d' % (rel, line, s)
    if not (0 <= s < e <= len(data)): fail('%s: span outside the file' % where)
    span = data[s:e]
    if data.count(b'\n', 0, s) + 1 != line: fail('%s: span is not on its listed line' % where)
    if b'\n' in span: fail('%s: span holds a newline' % where)
    if hashlib.sha256(span).hexdigest() != sha: fail('%s: removed bytes do not have the listed sha256' % where)
    if cls not in CLASS: fail('%s: unknown class %s' % (where, cls))
    form, toks = CLASS[cls]
    if not re.fullmatch(form, span): fail('%s: removed bytes are not of class %s' % (where, cls))
    if tok not in toks: fail('%s: token %s is not a %s token' % (where, tok, cls))
    prev, nxt = data[s - 1:s], data[e:e + 1]
    if cls == 'PATH':
        if re.fullmatch(rb'[A-Za-z0-9._/]', prev): fail('%s: the byte before the path extends it' % where)
        if re.fullmatch(rb'[A-Za-z0-9._+/-]', nxt): fail('%s: the byte after the path extends it' % where)
    elif cls == 'WORKDIR':
        if re.fullmatch(rb'[A-Za-z0-9._/-]', prev): fail('%s: the byte before the stem extends it' % where)
        if nxt != b'/': fail('%s: a directory stem must be followed by /' % where)
    elif re.fullmatch(rb'[A-Za-z0-9_/-]', prev) or re.fullmatch(rb'[A-Za-z0-9_-]', nxt):
        fail('%s: the bytes beside the span extend it' % where)
    if NUMBER.search(STAMP.sub(b'', span) if cls == 'WORKFILE' else span):
        fail('%s: a removed span holds a number' % where)
    return span


def apply(data, spans):
    out, at = [], 0
    for s, n, sha, cls, tok, line in spans:
        if s < at: fail('two spans overlap')
        out += [data[at:s], tok.encode()]
        at = s + n
    return b''.join(out + [data[at:]])


def rebuild(data, spans):
    """DATA with SPANS replaced by their tokens, or None when a span does not fit DATA (it lies outside DATA, or its
    removed bytes do not have the listed sha256)"""
    for s, n, sha, *_ in spans:
        if not 0 <= s < s + n <= len(data) or hashlib.sha256(data[s:s + n]).hexdigest() != sha: return None
    return apply(data, spans)


def redacted_diff(files):
    rows = ['# written by copycheck.py: every removed span is shown as <redacted>; nothing else differs']
    for rel, data, new, spans in files:
        rows += ['--- original/%s (sha256 %s)' % (rel, hashlib.sha256(data).hexdigest()),
                 '+++ copy/%s (sha256 %s)' % (rel, hashlib.sha256(new).hexdigest())]
        starts = [0] + [i + 1 for i, c in enumerate(data) if c == 0x0a]
        nstarts = [0] + [i + 1 for i, c in enumerate(new) if c == 0x0a]
        by_line = collections.defaultdict(list)
        for s, n, *_ in spans:
            by_line[data.count(b'\n', 0, s)].append((s, s + n))
        for ln in sorted(by_line):
            ls = starts[ln]; le = data.find(b'\n', ls); le = len(data) if le < 0 else le
            parts, at = [], ls
            for s, e in by_line[ln]:
                parts += [data[at:s], b'<redacted>']; at = e
            ns = nstarts[ln]; ne = new.find(b'\n', ns); ne = len(new) if ne < 0 else ne
            rows += ['@@ -%d,1 +%d,1 @@' % (ln + 1, ln + 1), '-' + b''.join(parts + [data[at:le]]).decode(),
                     '+' + new[ns:ne].decode()]
    return ('\n'.join(rows) + '\n').encode()


def file_table(ship, orig, by):
    """the lines of COPY.md's file table: every file here but COPY.md and SHA256SUMS, with its original's file sha256
    (12 hex; `-` for a file of this check), the sha256 of its bytes and its number of spans"""
    rows = list(HEAD)
    for rel in sorted(set(ship) - {'COPY.md', 'SHA256SUMS'}):
        o = '`%s`' % hashlib.sha256(orig[rel][1]).hexdigest()[:12] if rel in orig else '-'
        rows.append('| `%s` | %s | `%s` | %d |' % (rel, o, hashlib.sha256(ship[rel][1]).hexdigest(), len(by.get(rel, []))))
    return rows


def scan(scanner, files):
    """exit code and hits.tsv rows (file, tier, offset, blocking) the scanner writes for FILES, scanned under their
    relative names; a row is blocking when its cleared_by column is `-`"""
    with tempfile.TemporaryDirectory(prefix='copycheck.') as d:
        names = []
        for rel, b in files:
            p = os.path.join(d, 'in', rel); os.makedirs(os.path.dirname(p), exist_ok=True)
            open(p, 'wb').write(b); names.append(os.path.join('in', rel))
        r = subprocess.run([scanner, os.path.join(d, 'scan')] + names, cwd=d, capture_output=True, text=True)
        tsv = os.path.join(d, 'scan', 'hits.tsv')
        if not os.path.isfile(tsv): fail('the scanner wrote no hits.tsv (exit %d)' % r.returncode)
        rows = [x for x in csv.reader(open(tsv, newline=''), delimiter='\t')][1:]
        return r.returncode, [(os.path.relpath(x[0], 'in'), x[2], int(x[4]) if x[4].lstrip('-').isdigit() else -1,
                               x[6] == '-') for x in rows if x]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('repo')
    ap.add_argument('--scanner')
    ap.add_argument('--write-diff', action='store_true')
    ap.add_argument('--write-table', action='store_true')
    a = ap.parse_args()
    ship, src = shipped(), originals(a.repo)
    by, nrows = edits()
    copied = sorted(set(ship) - set(NEW))
    if set(by) - set(copied): fail('copy-edits.tsv names a file that is not a copied file')
    orig = {}   # copy name: (mode, bytes) of its original
    for rel in copied:
        spans = sorted(by.get(rel, []))
        hit = [o for o in sorted(src) if rebuild(src[o][1], spans) == ship[rel][1]]
        if len(hit) != 1: fail('%s: %d files of %s at %s give this file with its spans put in, not exactly one'
                               % (rel, len(hit), DIR, ORIG[:12]))
        orig[rel] = src[hit[0]]
    removed, tokbytes, bytestok, diffs = [], collections.defaultdict(set), collections.defaultdict(set), []
    for rel in copied:
        mode, data = orig[rel]
        smode, new = ship[rel]
        if bool(smode & 0o111) != (mode == '100755'): fail('%s: mode differs from the original %s' % (rel, mode))
        spans = sorted(by.get(rel, []))
        for s, n, sha, cls, tok, line in spans:
            span = check_span(rel, data, s, n, sha, cls, tok, line)
            removed.append((span, cls))
            if cls not in MANY: tokbytes[tok].add(sha)
            bytestok[sha].add(tok)
        if spans: diffs.append((rel, data, new, spans))
    for tok, s in tokbytes.items():
        if len(s) != 1: fail('token %s replaces %d different texts' % (tok, len(s)))
    for sha, t in bytestok.items():
        if len(t) != 1: fail('one removed text is replaced by %d tokens' % len(t))
    diff = redacted_diff(diffs)
    if a.write_diff:
        open(os.path.join(HERE, 'COPY.diff'), 'wb').write(diff)
        ship['COPY.diff'] = (ship.get('COPY.diff', (0o644, b''))[0], diff)
        print('copycheck: wrote COPY.diff sha256 %s' % hashlib.sha256(diff).hexdigest())
    elif ship.get('COPY.diff', (0, None))[1] != diff:
        fail('COPY.diff is not the redacted diff of the spans')
    rows = file_table(ship, orig, by)
    md = ship['COPY.md'][1].decode('utf-8').split('\n')
    heads = [i for i, ln in enumerate(md) if ln.startswith('| file |')]
    if len(heads) != 1: fail('COPY.md has %d file tables, not one' % len(heads))
    i = j = heads[0]
    while j < len(md) and md[j].startswith('|'): j += 1
    if a.write_table:
        new = '\n'.join(md[:i] + rows + md[j:]).encode('utf-8')
        open(os.path.join(HERE, 'COPY.md'), 'wb').write(new)
        ship['COPY.md'] = (ship['COPY.md'][0], new)
        print('copycheck: wrote the file table of COPY.md, %d rows' % (len(rows) - 2))
    elif md[i:j] != rows:
        k = next(k for k in range(max(j - i, len(rows))) if md[i:j][k:k + 1] != rows[k:k + 1])
        fail('COPY.md file table line %d is %r, not %r' % (i + k + 1, ''.join(md[i:j][k:k + 1]), ''.join(rows[k:k + 1])))
    # a removed text left as a whole token (the boundaries of its class) anywhere here is a breach
    edge = {'PATH': (rb'(?<![A-Za-z0-9._/])', rb'(?![A-Za-z0-9._+/-])'), 'WORKDIR': (rb'(?<![A-Za-z0-9._/-])', rb'(?=/)')}
    for rel, (_, b) in ship.items():
        for span, cls in removed:
            pre, post = edge.get(cls, (rb'(?<![A-Za-z0-9_/-])', rb'(?![A-Za-z0-9_-])'))
            if re.search(pre + re.escape(span) + post, b): fail('a removed span still occurs in %s' % rel)
    sums = {}
    for ln in ship['SHA256SUMS'][1].decode().splitlines():
        m = re.fullmatch(r'([0-9a-f]{64}) [ *](\S+)', ln)
        if not m: fail('SHA256SUMS: line %r is not sha256sum format' % ln)
        sums[m.group(2)] = m.group(1)
    if set(sums) != set(ship) - {'SHA256SUMS'}: fail('SHA256SUMS does not list exactly the files here but itself')
    for rel, h in sums.items():
        if hashlib.sha256(ship[rel][1]).hexdigest() != h: fail('SHA256SUMS: %s sha256 is not its bytes' % rel)
    cls_n = collections.Counter(r[3] for v in by.values() for r in v)
    print('copycheck: original %s %s: %d files copied (%s); %d spans in %d files %s; every other byte identical; '
          'COPY.diff, COPY.md file table and SHA256SUMS match'
          % (ORIG[:12], DIR, len(orig), ', '.join(copied), nrows, len(by), dict(sorted(cls_n.items()))))
    if a.scanner:
        rc, hits = scan(a.scanner, [(rel, b) for rel, (_, b) in sorted(ship.items())])
        block = [h for h in hits if h[3]]
        if rc != 0 or block: fail('the scanner exits %d with %d blocking hits in this directory' % (rc, len(block)))
        print('copycheck: scanner on the %d files here: exit 0, 0 blocking hits; listed, non-blocking, per file: %s'
              % (len(ship), dict(sorted(collections.Counter(h[0] for h in hits).items()))))
        rc, hits = scan(a.scanner, [(rel, v[1]) for rel, v in sorted(orig.items())])
        covered = set()
        for rel, tier, off, blocking in hits:
            sp = [(s, n) for s, n, *_ in by.get(rel, []) if s <= off < s + n]
            if blocking and not sp:
                fail('a blocking scanner hit in the original (%s, %s tier, offset %d) lies in no replaced span' % (rel, tier, off))
            if sp: covered.add((rel, sp[0][0]))
        free = collections.Counter(r[3] for rel, v in by.items() for r in v if (rel, r[0]) not in covered)
        print('copycheck: scanner on the original: %d blocking hits, every one inside a replaced span (%d listed, '
              'non-blocking); %d of %d spans hold a hit; spans that hold none, by class: %s'
              % (sum(h[3] for h in hits), sum(not h[3] for h in hits), len(covered), nrows, dict(sorted(free.items()))))


if __name__ == '__main__':
    main()
