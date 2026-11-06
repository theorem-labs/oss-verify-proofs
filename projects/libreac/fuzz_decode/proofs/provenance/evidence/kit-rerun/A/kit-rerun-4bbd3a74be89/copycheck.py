#!/usr/bin/env python3
"""copycheck.py -- proves that this directory is the original record with named tokens put in, and nothing else.

The original is the directory DIR at commit ORIG (below) of the hub repository, the last of CHAIN: each commit of CHAIN
is the parent of the next, and every file of DIR at STABLE (the re-run and its scans) is unchanged at ORIG; the later
commits only add or change the hand-trace files. copy-edits.tsv beside this file lists
every replaced span of it: file, line, byte offset, length, sha256 of the removed bytes, class, token. This checker
holds none of the removed text and needs none: it reads the original from git and checks, failing on the first breach:
  1. CHAIN is linear (each commit the first parent of the next), every file of DIR at STABLE has the same blob at
     ORIG, and the files each commit adds, changes or deletes in DIR are printed; every file of the original is here
     under its name, with its mode, and no other file but this check's; and COPY.md's file table is, row for row, the
     table that --write-table writes: every file of this directory (COPY.md aside) with, for a file of the original,
     the first 12 hex digits of its original's file sha256 as read from git (a file of this check has `-`), the
     sha256 of its bytes on disk and the number of its spans;
  2. each span of copy-edits.tsv: inside its file and on its line, no newline in it, no overlap, removed bytes with the
     listed sha256, a whole token (the bytes on either side cannot extend it), of the form its class allows, with an
     UPPER_CASE token of that class; outside DATE / TIME no removed span holds a number (0x..., three or more digits,
     or eight or more hex digits): no value, address, verdict or count is in a removed span;
  3. one token per removed path and one removed path per token (so each token names one input, as the one literal did);
  4. the original with exactly these spans replaced by their tokens is this directory's file, byte for byte; a file
     without a span is byte-identical to the original;
  5. no removed span's bytes occur in any file of this directory;
  6. COPY.diff is the redacted diff the spans give (one hunk per changed line: `-` the original line with every
     removed span as <redacted>, `+` the copy's line), byte for byte;
  7. with --scanner PATH (the scanner of record): the scanner exits 0 on this directory's files and reports no
     blocking hit there (a listed, non-blocking hit, such as a needle's letters inside a sha256 hex string, is counted
     per file); every blocking hit it reports in the original lies inside a replaced span; the
     spans that hold no scanner hit are counted by class (dates, times, agent / lane names: the proofs-file rule, not a
     scanner needle).
usage: copycheck.py REPO [--scanner PATH] [--write-diff] [--write-table]   (--write-diff writes COPY.diff and
--write-table writes COPY.md's file table, instead of comparing them)"""
import argparse, collections, csv, hashlib, os, re, subprocess, sys, tempfile

CHAIN = ['d0b5ec3b38ca202ebd76c624bca307a2c514481c', 'e88411a3576009538f387d6bea45d5f5ba19cd8d',
         'f39105e6ace872928bb0cb44707c40b71822f31c', '4870be5440a6470d8c338db4552e7ccfa7104cb5',
         '8d5e07101db592c6f20d8d8452606176fe31ad9a', '944f3f95abda831bdc057fa548fcadb2ad261f28',
         '032f7ba55aca1c578c2075cd175367f42a79a38d', '295eb9e170dfa52f16e5fed35383cec7cebb25dd',
         'f3ebf71c45fb01af7ea3e3a891faa6c6f649177b', '23ce03c3683cbf5d61abee50ff5c8d81674a8b24',
         'ed324b3a30a3f60c7b5b86df6e485ac8714979d9', 'ec63ec6c4edeb4e7ee2360980dbd3f1070504c41']
ORIG = CHAIN[-1]
STABLE = CHAIN[1]   # the re-run (d0b5ec3b38ca) and its cmpkit 86da41d3ef68 scans (e88411a35760)
DIR = 'proofs/libreac/fuzz_decode/provenance/alloc-reloc/A/kit-rerun-4bbd3a74be89'
HERE = os.path.dirname(os.path.abspath(__file__))
NEW = ('COPY.md', 'COPY.diff', 'copycheck.py', 'copy-edits.tsv')
PATHCH, PATHSTART = rb'[A-Za-z0-9._+/-]', rb'[A-Za-z0-9._/]'
CLASS = {   # class: (form of the removed bytes, tokens of the class)
    'PATH': (rb'/[A-Za-z0-9._+/-]+', {'DONOR_TWIN', 'DECODE_A_TWIN', 'DECODE_PLAIN_TWIN', 'FRAME_TWIN', 'DECODE_A_PIN',
                                       'HUB', 'OLD_RECORD'}),
    'PATH_PREFIX': (rb'/[A-Za-z0-9._+/-]+', {'KIT_PARENT', 'OLD_RECORD', 'NEGCTL_ROOT', 'DEPOT_DIR', 'REVIEW_DIR',
                                              'REVIEW_DIR3', 'REVIEW_DIR4', 'REVIEW_DIR6'}),
    'BRANCH': (rb'[a-z][a-z0-9-]*(?:/[a-z0-9][a-z0-9-]*)*', {'BRANCH'}),
    'NAME': (rb'[A-Za-z][A-Za-z0-9]*(?:-[A-Za-z0-9]+)*', {'WORKER', 'AGENT', 'LANE', 'DEPOT_NAME'}),
    'DATE': (rb'(?:\d{4}-)?\d\d-\d\d', {'DATE'}),
    'TIME': (rb'\d\d:\d\dZ', {'TIME'}),
}
NUMBER = re.compile(rb'0x|\d{3}|[0-9a-f]{8}')
HEAD = ['| file | original file sha256 (12 hex) | sha256 as shipped | spans |', '|---|---|---|---|']


def fail(msg):
    sys.exit('copycheck: FAIL: ' + msg)


def git(repo, *a):
    return subprocess.run(['git', '-C', repo] + list(a), check=True, capture_output=True).stdout


def tree(repo, commit):
    """{relative path: (mode, blob id)} of DIR at commit"""
    out = {}
    for ln in git(repo, 'ls-tree', '-r', '-z', commit + ':' + DIR).split(b'\0'):
        if not ln: continue
        meta, path = ln.split(b'\t', 1)
        mode, kind, blob = meta.split()
        out[path.decode()] = (mode.decode(), blob.decode())
    return out


def original(repo):
    """{relative path: (mode, blob id, bytes)} of DIR at ORIG"""
    out = {}
    for ln in git(repo, 'ls-tree', '-r', '-z', ORIG + ':' + DIR).split(b'\0'):
        if not ln: continue
        meta, path = ln.split(b'\t', 1)
        mode, kind, blob = meta.split()
        if kind != b'blob': fail('%s is not a blob' % path.decode())
        data = git(repo, 'cat-file', 'blob', blob.decode())
        if hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest() != blob.decode():
            fail('%s: git blob id does not match its bytes' % path.decode())
        out[path.decode()] = (mode.decode(), blob.decode(), data)
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
    if cls in ('PATH', 'PATH_PREFIX'):
        if re.fullmatch(PATHSTART, prev): fail('%s: the byte before the path extends it' % where)
        if cls == 'PATH' and re.fullmatch(PATHCH, nxt): fail('%s: the byte after the path extends it' % where)
        if cls == 'PATH_PREFIX' and nxt != b'/': fail('%s: a path prefix must be followed by /' % where)
    else:
        if re.fullmatch(rb'[A-Za-z0-9/-]', prev) or re.fullmatch(rb'[A-Za-z0-9-]', nxt):
            fail('%s: the bytes beside the span extend it' % where)
    if cls not in ('DATE', 'TIME') and NUMBER.search(span): fail('%s: a removed span holds a number' % where)
    return span


def apply(data, spans):
    out, at = [], 0
    for s, n, sha, cls, tok, line in spans:
        if s < at: fail('two spans overlap')
        out += [data[at:s], tok.encode()]
        at = s + n
    return b''.join(out + [data[at:]])


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
    """the lines of COPY.md's file table: every file here but COPY.md, with its original's file sha256 (12 hex; `-`
    for a file of this check), the sha256 of its bytes and its number of spans"""
    rows = list(HEAD)
    for rel in sorted(set(ship) - {'COPY.md'}):
        o = '`%s`' % hashlib.sha256(orig[rel][2]).hexdigest()[:12] if rel in orig else '-'
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
    orig, ship = original(a.repo), shipped()
    added = []
    for old, new in zip(CHAIN, CHAIN[1:]):
        if git(a.repo, 'rev-parse', new + '^1').decode().strip() != old: fail('%s is not the parent of %s' % (old, new))
        t0, t1 = tree(a.repo, old), tree(a.repo, new)
        ad = sorted(set(t1) - set(t0)); de = sorted(set(t0) - set(t1))
        ch = sorted(r for r in set(t0) & set(t1) if t0[r] != t1[r])
        added.append('%s +%d ~%d -%d' % (new[:12], len(ad), len(ch), len(de)))
    stable = tree(a.repo, STABLE)
    for rel, mb in stable.items():
        if rel not in orig or orig[rel][:2] != mb: fail('%s differs between %s and ORIG' % (rel, STABLE[:12]))
    base = tree(a.repo, CHAIN[0])
    by, nrows = edits()
    if set(by) - set(orig): fail('copy-edits.tsv names a file the original lacks')
    if set(orig) - set(ship): fail('a file of the original is missing here: %s' % sorted(set(orig) - set(ship)))
    extra = set(ship) - set(orig) - set(NEW)
    if extra: fail('files here that are neither in the original nor this check: %s' % sorted(extra))
    removed, tokpath, pathtok, diffs = [], collections.defaultdict(set), collections.defaultdict(set), []
    for rel in sorted(orig):
        mode, blob, data = orig[rel]
        smode, new = ship[rel]
        if bool(smode & 0o111) != (mode == '100755'): fail('%s: mode differs from the original %s' % (rel, mode))
        spans = sorted(by.get(rel, []))
        for s, n, sha, cls, tok, line in spans:
            span = check_span(rel, data, s, n, sha, cls, tok, line)
            removed.append(span)
            if cls in ('PATH', 'PATH_PREFIX'):
                tokpath[tok].add(sha); pathtok[sha].add(tok)
        if apply(data, spans) != new: fail('%s: the original with its spans replaced is not this file' % rel)
        if spans: diffs.append((rel, data, new, spans))
    for tok, s in tokpath.items():
        if len(s) != 1: fail('token %s replaces %d different paths' % (tok, len(s)))
    for sha, t in pathtok.items():
        if len(t) != 1: fail('one path is replaced by %d tokens' % len(t))
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
    for rel, (_, b) in ship.items():
        for span in removed:
            if span in b: fail('a removed span still occurs in %s' % rel)
    cls_n = collections.Counter(r[3] for v in by.values() for r in v)
    print('copycheck: original %s %s: %d files; chain from %s (%d files), files added / changed / deleted per commit: '
          '%s; the %d files of %s unchanged at %s; %d spans in %d files %s; every other byte identical; COPY.diff and '
          'COPY.md file table match'
          % (ORIG[:12], DIR, len(orig), CHAIN[0][:12], len(base), ', '.join(added), len(stable), STABLE[:12],
             ORIG[:12], nrows, len(by), dict(sorted(cls_n.items()))))
    if a.scanner:
        rc, hits = scan(a.scanner, [(rel, b) for rel, (_, b) in sorted(ship.items())])
        block = [h for h in hits if h[3]]
        if rc != 0 or block: fail('the scanner exits %d with %d blocking hits in this directory' % (rc, len(block)))
        print('copycheck: scanner on the %d files here: exit 0, 0 blocking hits; listed, non-blocking, per file: %s'
              % (len(ship), dict(sorted(collections.Counter(h[0] for h in hits).items()))))
        rc, hits = scan(a.scanner, [(rel, v[2]) for rel, v in sorted(orig.items())])
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
