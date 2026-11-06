#!/usr/bin/env python3
"""header-sm1-restore.py LIB HUB: the post-step after header-sm1.py, for the corrected header rule (docs/adding-a-proof.md
requirement 7).

Per file of this run:
- Every INHERITED licence line is restored from grant's donor blob at the release commit (recipes 4f87de75d67): the
  Copyright line, the SPDX line and every donor `Modified by` line, in the donor's order. Then ONLY the release scrub table is
  applied to them: a working-branch reference becomes `a working branch` (row R27). This puts back the donor's dates, and it
  undoes port_core's rename inside the inherited notice text (for example `TfibSyms renamed GrantSyms`).
- OUR added line (the line naming the donor file at its release commit) gets the head `Modified by Theorem Labs, 2026-10:`.
- Checks: the file's text with all Coq comments removed is byte-identical before and after (no statement or proof changed);
  no working-branch reference, host path or agent name is left in any comment; each inherited line equals the donor's after the
  table. Exit 1 on any failure.
HUB is a git repository holding the release commit."""
import os, re, subprocess, sys

LIB, HUB = sys.argv[1], sys.argv[2]
REL = '4f87de75d67'
DONOR = {'B/Rt/YF0r.v': 'proofs/libreac/fuzz_grant/lib/B/Rt/YF0r.v',
         'B/Rt/YF0s.v': 'proofs/libreac/fuzz_grant/lib/B/Rt/YF0s.v',
         'Reusable/YF0v.v': 'proofs/libreac/fuzz_grant/lib/Reusable/YF0v.v'}
OURS_KEY = 'of the release at recipes'
# A working-branch reference, matched by its SHAPE and naming nothing: a remote ref `origin/<namespace>/<name>`.
BRANCH_REF = re.compile(r'\borigin/[a-z][a-z0-9_-]*/[A-Za-z0-9][\w.-]*(?:/[\w.-]+)*')
TABLE = [(BRANCH_REF, 'a working branch')]
HOST = re.compile(r'/(home|mnt|tmp|scratch|data|srv|root)/')
AGENT = re.compile(r'\b[hrc]-[a-z]{2,}(?:-[a-z0-9]+)+\b')
LICENCE = re.compile(r'^\(\* (Copyright |SPDX-License-Identifier:|Modified by )')


def strip_comments(t):
    out, i, depth, n = [], 0, 0, len(t)
    while i < n:
        if t.startswith('(*', i):
            depth += 1; i += 2; continue
        if depth and t.startswith('*)', i):
            depth -= 1; i += 2; continue
        if depth == 0 and t[i] == '"':
            j = i + 1
            while j < n and not (t[j] == '"' and not t.startswith('""', j)):
                j += 2 if t.startswith('""', j) else 1
            out.append(t[i:j + 1]); i = j + 1; continue
        if depth == 0:
            out.append(t[i])
        i += 1
    return ''.join(out)


def table(line):
    for rx, rep in TABLE:
        line = rx.sub(rep, line)
    return line


bad = 0
for f, dpath in DONOR.items():
    p = os.path.join(LIB, f)
    t = open(p).read()
    donor = subprocess.run(['git', '-C', HUB, 'show', f'{REL}:{dpath}'], capture_output=True, text=True, check=True).stdout
    dhead = [l for l in donor.split('\n')[:20] if LICENCE.match(l)]
    lines = t.split('\n')
    head_idx = [i for i, l in enumerate(lines[:20]) if LICENCE.match(l)]
    ours = [i for i in head_idx if OURS_KEY in lines[i]]
    if len(ours) != 1 or head_idx != list(range(head_idx[0], head_idx[-1] + 1)):
        print(f'{f}: header block not as expected (our line found {len(ours)}x)'); bad += 1; continue
    our = lines[ours[0]]
    our = re.sub(r'^\(\* Modified by Theorem Labs(, 20\d\d-\d\d)?:', '(* Modified by Theorem Labs, 2026-10:', our)
    inherited = [table(l) for l in dhead]
    new_lines = lines[:head_idx[0]] + inherited + [our] + lines[head_idx[-1] + 1:]
    u = '\n'.join(new_lines)
    if strip_comments(t) != strip_comments(u):
        print(f'CODE CHANGED: {f}'); bad += 1; continue
    com = re.findall(r'\(\*.*?\*\)', u, re.S)
    left = {'working branch': sum(len(BRANCH_REF.findall(c)) for c in com),
            'host path': sum(len(HOST.findall(c)) for c in com),
            'agent name': sum(len(AGENT.findall(c)) for c in com)}
    changed = sum(1 for a, b in zip(dhead, inherited) if a != b)
    print(f'{f}: {len(dhead)} inherited lines restored from {REL}:{dpath} ({changed} rewritten by the table), '
          f'our line dated; comments left {left}')
    if sum(left.values()):
        bad += 1
    open(p, 'w').write(u)
sys.exit(1 if bad else 0)
