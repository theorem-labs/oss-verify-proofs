#!/usr/bin/env python3
"""mkpatch-B.py A_PATCH STAGE_OUT OUT_PATCH [OLD=NEW ...]: re-cut an image-A structural patch (this unit's image-A core
patch) as its image-B twin against this run's stage-out. File A/A<x>.v -> B/Y<x>.v; module-qualified A names
A<x>.n -> Y<x>.n; each OLD=NEW pair rewrites an image-A value the hunk carries to its image-B value (a whole token, for
context lines such as an image top; each pair is measured, e.g. the image's page-up end, and given on the command line).
Each hunk's removed lines must occur exactly once, contiguously, in the B file; they are replaced by the hunk's added
lines; the output is a fresh unified diff (-p0 from stage-out, zero fuzz), so the B text decides the context."""
import difflib, re, sys

apatch, so, outp = sys.argv[1:4]
VMAP = dict(kv.split('=', 1) for kv in sys.argv[4:])


def tr(s):
    s = re.sub(r'\bA([0-9A-Z][0-9a-z]{2,3})\.', r'Y\1.', s)
    for o, n in VMAP.items():
        s = re.sub(r'(?<![\w])' + re.escape(o) + r'(?![\w])', n, s)
    return s


files, cur, hunk = {}, None, None
for line in open(apatch).read().splitlines():
    if line.startswith('--- '):
        cur = line[4:].split('\t')[0].strip()
        files.setdefault(cur, [])
    elif line.startswith('+++ '):
        continue
    elif line.startswith('@@'):
        hunk = {'old': [], 'new': []}
        files[cur].append(hunk)
    elif hunk is not None and line[:1] in ('-', '+', ' '):
        if line[0] in ('-', ' '):
            hunk['old'].append(line[1:])
        if line[0] in ('+', ' '):
            hunk['new'].append(line[1:])
out = []
for af, hunks in files.items():
    m = re.fullmatch(r'A/A(\w+)\.v', af)
    bf = f'B/Y{m.group(1)}.v'
    text = open(f'{so}/{bf}').read().split('\n')
    new = list(text)
    for h in hunks:
        old = [tr(x) for x in h['old']]
        rep = [tr(x) for x in h['new']]
        hits = [i for i in range(len(new) - len(old) + 1) if new[i:i + len(old)] == old]
        if len(hits) != 1:
            sys.exit(f'{bf}: hunk matches {len(hits)} times (want 1): first old line {old[0][:80]!r}')
        i = hits[0]
        new[i:i + len(old)] = rep
    out += list(difflib.unified_diff([l + '\n' for l in text], [l + '\n' for l in new], fromfile=bf, tofile=bf, n=3))
    print(f'{bf}: {len(hunks)} hunk(s)')
open(outp, 'w').write(''.join(out))
