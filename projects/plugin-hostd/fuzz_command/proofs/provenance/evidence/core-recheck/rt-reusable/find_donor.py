#!/usr/bin/env python3
"""Find the donor text a ported file was made from: every distinct version (blob) of a candidate donor path in the
history of a git object store, ranked by the size of its line diff against the ported file.

Usage: find_donor.py GITDIR PORTED_FILE DONOR_PATH [DONOR_PATH ...]
Prints, per candidate path, the blobs sorted by changed-line count (lines removed + lines added, difflib), with the
newest commit that holds each blob. Read-only: git log / git show only."""
import difflib, subprocess, sys

git, ported = sys.argv[1], sys.argv[2]
mine = open(ported, encoding='utf-8', errors='replace').read().splitlines()


def run(*a):
    r = subprocess.run(['git', '-C', git] + list(a), capture_output=True)
    return r.stdout.decode('utf-8', 'replace') if r.returncode == 0 else None


for path in sys.argv[3:]:
    log = run('log', '--all', '--format=%h %cI', '--', path) or ''
    blobs = {}
    for line in log.splitlines():
        c, when = line.split()
        b = run('rev-parse', '--verify', '-q', f'{c}:{path}')
        if not b:
            continue
        b = b.strip()
        if b not in blobs:
            blobs[b] = (c, when)  # git log is newest first: keep the newest commit of each blob
    res = []
    for b, (c, when) in blobs.items():
        text = run('cat-file', 'blob', b).splitlines()
        n = sum(1 for l in difflib.unified_diff(text, mine, n=0, lineterm='')
                if l[:1] in '+-' and not l.startswith(('+++', '---')))
        res.append((n, c, when, b[:12], len(text)))
    res.sort()
    print(f'== {path}: {len(res)} distinct versions')
    for n, c, when, b, ln in res[:5]:
        print(f'   changed_lines={n}\tcommit={c}\t{when}\tblob={b}\tlines={ln}')
