#!/usr/bin/env python3
"""imgtop-require.py UNIT LIB APPLIED: the image-B core's files must take image B's bounds. port_core 0e4e065eab9f
writes the per-image lib/B/YImgTop.v but, in every staged file whose donor text Requires YImgTop and that its YImgTop rule
does not rewrite, names the module of the shared lib/Reusable/YImgTop.v (image A's bounds). This post-step (after
apply-B.sh) changes exactly that sentence,
    From <mod>.lib.Reusable Require Import YImgTop.  ->  From <mod>.lib.B Require Import YImgTop.
in every file of APPLIED (applied.txt) that holds it, and nothing else. (As a port_core --patch the same change makes
port_core's generated header claim the file's addresses moved, which is false for a file whose only change is this.)
Exit 1 if a file holds the sentence more than once or a file changes in any other line."""
import sys

unit, lib, applied = sys.argv[1:4]
mod = f'OssFuzzTheorems.Proofs.reac_repacer.{unit}.lib'
old = f'From {mod}.Reusable Require Import YImgTop.'
new = f'From {mod}.B Require Import YImgTop.'
changed = []
for rel in (l.strip() for l in open(applied) if l.strip() and not l.startswith('#')):
    p = f'{lib}/{rel}'
    lines = open(p).read().split('\n')
    n = lines.count(old)
    if n == 0:
        continue
    if n != 1:
        sys.exit(f'{rel}: the sentence occurs {n} times')
    out = [new if l == old else l for l in lines]
    if sum(a != b for a, b in zip(lines, out)) != 1:
        sys.exit(f'{rel}: more than one line would change')
    open(p, 'w').write('\n'.join(out))
    changed.append(rel)
print(f'{len(changed)} files: {" ".join(changed)}')
