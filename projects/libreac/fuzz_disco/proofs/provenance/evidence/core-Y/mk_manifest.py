#!/usr/bin/env python3
"""Writes MANIFEST from ROLES.tsv. Run from the slice directory: python3 mk_manifest.py
MANIFEST: one line per file, `<path> <kind> <sha256> <role>`. Refuses (exit 1) a file here that ROLES.tsv does not name,
and a ROLES.tsv row whose file is missing. MANIFEST itself is not listed.
"""
import hashlib, os, sys
roles = {}
for line in open('ROLES.tsv', encoding='utf-8'):
    if not line.strip() or line.startswith('#'):
        continue
    path, kind, role = line.rstrip('\n').split('\t', 2)
    if kind not in ('script', 'input', 'table', 'gate'):
        sys.exit('bad kind %r for %s' % (kind, path))
    roles[path] = (kind, role)
files = sorted(os.path.relpath(os.path.join(d, f), '.') for d, _, fs in os.walk('.') for f in fs)
files = [f for f in files if f != 'MANIFEST']
problems = ['not named in ROLES.tsv: ' + f for f in files if f not in roles]
problems += ['named but missing: ' + p for p in roles if p not in files]
if problems:
    sys.exit('\n'.join(problems))
with open('MANIFEST', 'w', encoding='utf-8') as out:
    out.write('# fuzz_disco evidence, core-Y slice (image B core): path kind sha256 role. Written by mk_manifest.py.\n')
    for p in files:
        h = hashlib.sha256(open(p, 'rb').read()).hexdigest()
        out.write('%s %s %s %s\n' % (p, roles[p][0], h, roles[p][1]))
print('%d files' % len(files))
