#!/usr/bin/env python3
"""header-sm1.py LIB: the comments-only step after apply-sm1.sh, for the three files of this run (applied.txt).

Per file: the donor's Copyright and SPDX lines stay; the donor's Modified lines stay, undated (core-B/header-clean.py's
rule), with the branch name before the commit they cite removed (it keeps `commit af735a950e2`; BRANCH below), and
`grant's B lane` -> `grant's image B`; port_core's own provenance line is replaced by ONE undated line naming the donor
file at its release commit, the donor image and the target image. Then it CHECKS that every file's text with all Coq
comments removed is byte-identical before and after (no statement or proof changed), and counts what the text rule
forbids in comments (dates, host paths, agent / lane names, cold branch names). Exit 1 if a code byte changed, a
forbidden match is left, or an expected line is not found."""
import os, re, sys

LIB = sys.argv[1]
NOTICE = re.compile(r'\(\* Modified by Theorem Labs, 20\d\d-\d\d(?:-\d\d)?(?=[: \[])')
HOSTDIRS = ('home', 'mnt', 'tmp', 'scratch', 'data', 'srv', 'root')
# A working-branch reference is matched by its SHAPE, naming nothing: a remote ref `origin/<namespace>/<name>`, where
# <namespace> is one path word and <name> is a branch name. The released branch `ossv/recipes` is not a reference this
# step meets in a comment; a release commit is cited by its sha.
BRANCH_REF = re.compile(r'\borigin/[a-z][a-z0-9_-]*/[A-Za-z0-9][\w.-]*(?:/[\w.-]+)*')
FORBID = {'date': re.compile(r'\b20\d\d-\d\d(?:-\d\d)?\b'), 'host path': re.compile('|'.join('/%s/' % d for d in HOSTDIRS)),
          'agent/lane': re.compile(r'\b[hrc]-[a-z]{3,}(?:-[a-z0-9]+)*\b|\blane\b'),
          'working branch': BRANCH_REF}
# One generic rewrite, naming nothing: a branch reference followed by a commit sha is cited as that commit.
BRANCH_SHA = re.compile(BRANCH_REF.pattern + r' ([0-9a-f]{7,40})\b')
TEXT = [("module paths of grant's B lane", "module paths of grant's image B")]
DONOR = 'fuzz_grant.asan-ubsan, sha256 fde52226dc48; symbols from its unstripped twin 5a5ee7c02b4e'
TARGET = 'fuzz_uci.asan-ubsan, sha256 a1b86e424add = the asan-ubsan pin of harness.yaml; symbols from its unstripped twin 8d07ffcf5948'
LINES = {
    'B/Rt/YF0r.v': (
        'copied from proofs/libreac/fuzz_grant/lib/Rt/YF0r.v',
        '(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_grant/lib/B/Rt/YF0r.v of the release at recipes commit '
        f'4f87de75d67 (donor image {DONOR}) to reac-repacer/fuzz_uci image B ({TARGET}) by port_core 0e4e065eab9f: module '
        'paths changed and every image value read from image B: the probe points FS_ENTRY 0x3c1b8, FS_LOOP 0x3c24c, FS_FOUND '
        '0x3c2c4 (its bit-vector literal 246468), FS_SDFF 0x3c2f0, FS_SDSH 0x3c30c; TP 0x5d2090 and TSD 0x5f3438; the code '
        "table's ranges at fuzz_uci's symbols, without fuzz_grant's __asan_stack_malloc_0 / _2 / _4 (fuzz_uci links class 1 "
        'only, and the class-1 code calls none of them); the data cells (0x97e08, 0x98ec0 holding 0x9104c, 0x97118 holding '
        '0x130c28 and the flag byte 0x130cb1, 0x97178 holding 0x12eb98, 0x97e18, 0x9e960) and the TLS and thread-object cells '
        '(TP - 8 holding 0x5d20b0, 0x5d20b8 holding 0x5d2890, T + 48 / T + 56 holding 0x5d27c8 / 0x5d28a4) are the cells of '
        "fuzz_uci's certificate lib/B/YF0m.v. Every body the proofs step through was compared instruction by instruction with "
        "fuzz_grant's (equal up to relocation). *)"),
    'B/Rt/YF0s.v': (
        'copied from proofs/libreac/fuzz_grant/lib/Rt/YF0s.v',
        '(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_grant/lib/B/Rt/YF0s.v of the release at recipes commit '
        f'4f87de75d67 (donor image {DONOR}) to reac-repacer/fuzz_uci image B ({TARGET}) by port_core 0e4e065eab9f: module '
        'paths changed, GrantSyms renamed UciSyms, and the image values read from image B: the image end IMG_TOP 0x5f4000 = '
        '6242304 of lib/B/YImgTop.v, its eighth 780288 and the low-shadow bound kLowShadowBeg + 780288 = 2148227072; the '
        "thread-object cells T + 48 / T + 56 holding 0x5d27c8 / 0x5d28a4 of fuzz_uci's certificate lib/B/YF0m.v. The "
        'statements are the donor\'s. *)'),
    'Reusable/YF0v.v': (
        'copied from proofs/libreac/fuzz_grant/lib/YF0v.v',
        '(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_grant/lib/Reusable/YF0v.v of the release at recipes '
        f'commit 4f87de75d67 (donor image {DONOR}) to reac-repacer/fuzz_uci, for image B ({TARGET}) by port_core '
        '0e4e065eab9f: module paths changed; the file states no image value, so it is shared (lib/Reusable). *)'),
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
    u = NOTICE.sub('(* Modified by Theorem Labs', u)
    u = BRANCH_SHA.sub(lambda m: 'commit ' + m.group(1), u)
    for old, rep in TEXT:
        u = u.replace(old, rep)
    for k, rx in FORBID.items():
        before[k] += sum(len(rx.findall(c)) for c in comments(t))
        after[k] += sum(len(rx.findall(c)) for c in comments(u))
    if strip_comments(t) != strip_comments(u):
        print(f'CODE CHANGED: {f}'); bad += 1; continue
    head = [l for l in u.split('\n')[:12] if l.startswith('(*')]
    print(f'{f}: header {len(head)} comment lines; Modified lines {sum(1 for l in head if l.startswith("(* Modified by Theorem Labs"))}')
    open(p, 'w').write(u)
print(f'{len(LINES)} files; forbidden matches in comments before {before}, after {after}')
sys.exit(1 if bad or sum(after.values()) else 0)
