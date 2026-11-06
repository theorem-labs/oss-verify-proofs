#!/usr/bin/env python3
"""header-sm1.py LIB DON: the comments-only step after apply-sm1.sh, for the three files of this run (applied.txt).

Per file: every inherited header line (the donor's Copyright, SPDX and every donor `Modified by` line) stays byte for
byte the donor's (docs/adding-a-proof.md req. 7), and the donor line that port_core's rename GrantSyms -> UciSyms reached
is given back its own words (`TfibSyms renamed GrantSyms`); port_core's own provenance line is replaced by ONE line
`(* Modified by Theorem Labs, 2026-10: ... *)` naming the donor file at its release commit, the donor image, the target
image and what changed. Then it CHECKS that every file's text with all Coq comments removed is byte-identical before
and after (no statement or proof changed), that the inherited lines equal the donor file's header lines in DON (the
normalised donor lib of mkdon-sm1.sh) byte for byte, and counts what the text rule forbids in comments (day-level dates,
host paths, agent / lane names, cold branch names). Exit 1 if a code byte changed, an inherited line differs, a
forbidden match is left, or an expected line is not found."""
import os, re, sys

LIB, DON = sys.argv[1], sys.argv[2]
HOSTDIRS = ('home', 'mnt', 'tmp', 'scratch', 'data', 'srv', 'root')
FORBID = {'day-level date': re.compile(r'\b20\d\d-\d\d-\d\d\b'), 'host path': re.compile('|'.join('/%s/' % d for d in HOSTDIRS)),
          'agent/lane': re.compile(r'\b[hrc]-[a-z]{3,}(?:-[a-z0-9]+)*\b|\bagentvm\b|\blane\b'),
          'cold branch': re.compile(r'\bcold/[\w./-]+')}
BRANCH = [('module names; TfibSyms renamed UciSyms.', 'module names; TfibSyms renamed GrantSyms.')]
DONOR = 'fuzz_grant.asan, sha256 c2c7559b29bd; symbols from its unstripped twin 57c26f993615'
TARGET = 'fuzz_uci.asan, sha256 6ea017c24525 = the asan pin of harness.yaml; symbols from its unstripped twin 56822e263d76'
LINES = {
    'A/Rt/AF0r.v': (
        'copied from proofs/libreac/fuzz_grant/lib/A/Rt/AF0r.v',
        '(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/Rt/AF0r.v of the release at recipes commit '
        f'4f87de75d67 (donor image {DONOR}) to reac-repacer/fuzz_uci image A ({TARGET}) by port_core 0e4e065eab9f: module '
        'paths changed and every image value read from image A: the probe points FS_ENTRY 0x3c1b8, FS_LOOP 0x3c24c, FS_FOUND '
        '0x3c2c4 (its bit-vector literal 246468), FS_SDFF 0x3c2f0, FS_SDSH 0x3c30c; TP 0x5d1f90 and TSD 0x5f3338; the code '
        "table's ranges at fuzz_uci's symbols, without fuzz_grant's __asan_stack_malloc_0 / _2 / _4 (fuzz_uci links class 1 "
        'only, and the class-1 code calls none of them); the data cells (0x97d00, 0x98db8 holding 0x90f44, 0x97010 holding '
        '0x130b28 and the flag byte 0x130bb1, 0x97070 holding 0x12ea98, 0x97d10, 0x9e860) and the TLS and thread-object cells '
        '(TP - 8 holding 0x5d1fb0, 0x5d1fb8 holding 0x5d2790, T + 48 / T + 56 holding 0x5d26c8 / 0x5d27a4) are the cells of '
        "fuzz_uci's certificate lib/A/AF0m.v. Every body the proofs step through was compared instruction by instruction with "
        "fuzz_grant's (equal up to relocation). *)"),
    'A/Rt/AF0s.v': (
        'copied from proofs/libreac/fuzz_grant/lib/A/Rt/AF0s.v',
        '(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/Rt/AF0s.v of the release at recipes commit '
        f'4f87de75d67 (donor image {DONOR}) to reac-repacer/fuzz_uci image A ({TARGET}) by port_core 0e4e065eab9f: module '
        'paths changed, GrantSyms renamed UciSyms, and the image values read from image A: the image end IMG_TOP 0x5f4000 = '
        '6242304 of lib/Reusable/YImgTop.v and its eighth 780288; the low-shadow bound 2148213760 is the donor\'s, at most '
        'kLowShadowBeg + 780288 = 2148227072; the thread-object cells T + 48 / T + 56 holding 0x5d26c8 / 0x5d27a4 of '
        "fuzz_uci's certificate lib/A/AF0m.v. The statements are the donor's. *)"),
    'Reusable/YF0v.v': (
        'copied from proofs/libreac/fuzz_grant/lib/YF0v.v',
        '(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/Reusable/YF0v.v of the release at recipes '
        f'commit 4f87de75d67 (donor image {DONOR}) to reac-repacer/fuzz_uci, for image A ({TARGET}) by port_core '
        '0e4e065eab9f: module paths changed, and shadow_apart\'s last step nia replaced by lia (the goal is linear once the '
        'divisions by 8 are rewritten); the file states no image value, so it is shared (lib/Reusable). *)'),
}


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


def comments(t):
    return re.findall(r'\(\*.*?\*\)', t, re.S)


bad = 0
before = {k: 0 for k in FORBID}; after = {k: 0 for k in FORBID}
for f, (key, new) in LINES.items():
    p = os.path.join(LIB, f)
    t = open(p).read()
    lines = t.split('\n')
    hits = [i for i, l in enumerate(lines) if l.startswith('(* Modified by Theorem Labs') and key in l]
    if len(hits) != 1:
        print(f'{f}: port_core line not found exactly once ({len(hits)})'); bad += 1; continue
    lines[hits[0]] = new
    u = '\n'.join(lines)
    for old, rep in BRANCH:
        u = u.replace(old, rep)
    dl = open(os.path.join(DON, f.split('/', 1)[1] if f.startswith('Reusable/') else f)).read().split('\n')
    inh = dl[:next(i for i, l in enumerate(dl) if not l.startswith('(*'))]
    if u.split('\n')[:len(inh)] != inh:
        print(f'{f}: an inherited header line differs from the donor\'s'); bad += 1; continue
    for k, rx in FORBID.items():
        before[k] += sum(len(rx.findall(c)) for c in comments(t))
        after[k] += sum(len(rx.findall(c)) for c in comments(u))
    if strip_comments(t) != strip_comments(u):
        print(f'CODE CHANGED: {f}'); bad += 1; continue
    head = [l for l in u.split('\n')[:12] if l.startswith('(*')]
    print(f'{f}: header {len(head)} comment lines ({len(inh)} inherited, equal to the donor\'s); Modified lines '
          f'{sum(1 for l in head if l.startswith("(* Modified by Theorem Labs"))}')
    open(p, 'w').write(u)
print(f'{len(LINES)} files; forbidden matches in comments before {before}, after {after}')
sys.exit(1 if bad or sum(after.values()) else 0)
