#!/usr/bin/env python3
"""Add the Zify pre-hook that lets lia see through the image-bound names.

The generated / relocated files name the image bounds YImgTop.IMG_TOP / YImgTop.IMG_LO instead of numerals, and
lia treats a name as an opaque atom. For every given file that Requires YImgTop, the line
  #[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
must sit AFTER the sentence that Requires YImgTop (the name is not in scope before it; four files were found where
it sat above). It is placed right after that Require line and the Import / Open lines that
directly follow it. A hook line that names YImgTop but sits above the Require is MOVED there. Files that do not
Require YImgTop are left alone (YD2j / AD2j). Usage: zifyhook.py FILE..."""
import re
import sys

HOOK = '#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.'
REQ = re.compile(r'^\s*From\s+\S+\s+Require\b[^.]*\bYImgTop\b')
HOOKLINE = re.compile(r'^\s*#\[local\]\s+Ltac\s+Zify\.zify_pre_hook\s*::=.*\bYImgTop\b')

for p in sys.argv[1:]:
    L = open(p).read().split('\n')
    req = next((i for i, l in enumerate(L) if REQ.match(l)), None)
    if req is None:
        print('zifyhook: %s: no YImgTop Require, unchanged' % p)
        continue
    hooks = [i for i, l in enumerate(L) if HOOKLINE.match(l)]
    if any(i > req for i in hooks):
        if any(i < req for i in hooks):
            L = [l for i, l in enumerate(L) if not (i in hooks and i < req)]
            open(p, 'w').write('\n'.join(L))
            print('zifyhook: %s: duplicate hook above the Require removed' % p)
        else:
            print('zifyhook: %s: hook in place, unchanged' % p)
        continue
    L = [l for i, l in enumerate(L) if i not in hooks]
    req = next(i for i, l in enumerate(L) if REQ.match(l))
    at = req + 1
    while at < len(L) and re.match(r'^\s*(Import|Open Scope|Local Open Scope|Export)\b', L[at]):
        at += 1
    L.insert(at, HOOK)
    open(p, 'w').write('\n'.join(L))
    print('zifyhook: %s: hook %s at line %d' % (p, 'moved' if hooks else 'added', at + 1))
