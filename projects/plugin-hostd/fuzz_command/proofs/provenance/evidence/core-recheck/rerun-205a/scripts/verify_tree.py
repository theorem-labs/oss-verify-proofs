#!/usr/bin/env python3
"""Check that a directory holds exactly the files of a git tree, byte for byte.

Usage: verify_tree.py LSTREE.txt DIR
  LSTREE.txt  `git ls-tree -r <ref>:<path>` output (mode SP type SP blob-id TAB path)
  DIR         the directory to check

Each file of DIR is hashed as a git blob (sha1 of "blob <len>\\0" + bytes) and compared with the blob id the tree
names for its path; a path on one side only is reported. Also counts .v files holding a CR byte. Exit 0 only when
every path matches and no extra path exists.
"""
import hashlib
import os
import sys

lst, root = sys.argv[1:3]
want = {}
for line in open(lst, encoding='utf-8'):
    meta, path = line.rstrip('\n').split('\t', 1)
    mode, typ, oid = meta.split()
    if typ == 'blob':
        want[path] = (mode, oid)
have = {}
cr = 0
for dp, _, fs in os.walk(root):
    for f in fs:
        p = os.path.join(dp, f)
        rel = os.path.relpath(p, root)
        b = open(p, 'rb').read()
        if f.endswith('.v') and b'\r' in b:
            cr += 1
        have[rel] = hashlib.sha1(b'blob %d\0' % len(b) + b).hexdigest()
bad = sorted(p for p in want if p in have and have[p] != want[p][1])
miss = sorted(p for p in want if p not in have)
extra = sorted(p for p in have if p not in want)
print(f'{root}: tree paths {len(want)}, files {len(have)}, blob-equal {len(want) - len(bad) - len(miss)}, '
      f'differ {len(bad)}, missing {len(miss)}, extra {len(extra)}, .v files with a CR byte {cr}')
for tag, ps in (('DIFFER', bad), ('MISSING', miss), ('EXTRA', extra)):
    for p in ps[:20]:
        print(f'  {tag} {p}')
sys.exit(0 if not (bad or miss or extra) else 1)
