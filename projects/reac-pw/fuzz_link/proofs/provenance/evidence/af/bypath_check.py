#!/usr/bin/env python3
"""bypath_check.py: the files this unit took by path from released units are byte-equal to the released text, except
the module prefix (OssFuzzTheorems.Proofs.<project>.<harness>.lib -> OssFuzzTheorems.Proofs.reac_pw.fuzz_link.lib).

Usage: bypath_check.py HUB REF TREE
  HUB  a git checkout that has REF (the released recipes commit); TREE the root of the tree under check.
Prints one line per file (OK / DIFFERS with the first differing line) and RESULT PASS iff all are OK.
"""
import subprocess, sys

hub, ref, tree = sys.argv[1:4]
LINK = 'OssFuzzTheorems.Proofs.reac_pw.fuzz_link.lib'
ROWS = [  # (file in reac-pw/fuzz_link/lib, released unit)
    ('Reusable/AsStackSz.v', 'libreac/fuzz_scene'),
    ('Reusable/StackFreeDef.v', 'libreac/fuzz_disco'),
    ('Reusable/StackFreeJournal.v', 'libreac/fuzz_disco'),
    ('Reusable/StackFreeRaw.v', 'libreac/fuzz_disco'),
    ('Reusable/YA0n.v', 'libreac/fuzz_boxreg'),
    ('Reusable/YFfn.v', 'libreac/fuzz_boxreg'),
    ('Reusable/YG0b.v', 'libreac/fuzz_boxreg'),
    ('Reusable/YA0j.v', 'libreac/fuzz_boxreg'),
    ('Reusable/YWH8.v', 'libreac/fuzz_boxreg'),
]
ok = True
for rel, unit in ROWS:
    path = 'proofs/%s/lib/%s' % (unit, rel)
    blob = subprocess.run(['git', '-C', hub, 'rev-parse', '%s:%s' % (ref, path)], capture_output=True, text=True).stdout.strip()
    rel_txt = subprocess.run(['git', '-C', hub, 'show', '%s:%s' % (ref, path)], capture_output=True).stdout
    proj, harness = unit.split('/')
    donor = 'OssFuzzTheorems.Proofs.%s.%s.lib' % (proj.replace('-', '_'), harness)
    want = rel_txt.replace(donor.encode(), LINK.encode())
    have = open('%s/proofs/reac-pw/fuzz_link/lib/%s' % (tree, rel), 'rb').read()
    if want == have:
        print('OK       %-30s = %s blob %s, prefix %s -> %s' % (rel, path, blob[:12], donor, LINK))
    else:
        ok = False
        w, h = want.split(b'\n'), have.split(b'\n')
        i = next((k for k in range(min(len(w), len(h))) if w[k] != h[k]), min(len(w), len(h)))
        print('DIFFERS  %-30s vs %s blob %s: first difference at line %d' % (rel, path, blob[:12], i + 1))
print('RESULT', 'PASS' if ok else 'FAIL')
sys.exit(0 if ok else 1)
