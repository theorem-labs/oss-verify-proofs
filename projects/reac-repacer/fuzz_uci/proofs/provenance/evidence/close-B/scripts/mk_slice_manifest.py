#!/usr/bin/env python3
"""mk_slice_manifest.py SLICE_DIR -- writes SLICE_DIR/MANIFEST.md: a `# ` title line, then every file of the slice
with its role and sha256 (the role from the file's path, the table ROLES; a file no rule matches is 'other'). The
manifest does not list itself."""
import hashlib
import os
import re
import sys

TITLE = 'provenance/evidence/close-B: fuzz_uci image-B composition lib/B/UciBClose.v'
ROLES = [
    (r'^RECORD\.md$', 'the record: the 18 rows with file:line and status, build, Print Assumptions, measurements'),
    (r'^run\.sh$', 'reruns every measurement and rewrites tables/, records/, RECORD.md and MANIFEST.md'),
    (r'^env\.example\.sh$', 'every variable run.sh reads, without values'),
    (r'^images\.sha256$', 'sha256 of every image read'),
    (r'^scripts/dis_rv64\.py$', 'listings, UBSan trap branches and s0 writes of the six program functions'),
    (r'^scripts/cells\.py$', 'runtime cells, GOT words and REAL values of one image'),
    (r'^scripts/mk_record\.py$', 'writes records/build.txt and RECORD.md'),
    (r'^scripts/mk_slice_manifest\.py$', 'this writer'),
    (r'^tables/dis-[AB]\.txt$', 'listing of the six program functions of one image'),
    (r'^tables/ubsan-traps-[AB]\.txt$', 'branches to UBSan\'s unimp in the six program functions of one image'),
    (r'^tables/s0-writes-[AB]\.txt$', 's0 writes in the three call-context functions of one image'),
    (r'^tables/cells-[AB]\.txt$', 'runtime cells of one image'),
    (r'^records/build\.txt$', 'the build of record: mode, pins, targets, rc, About / Print Assumptions'),
]


def main():
    sl = os.path.abspath(sys.argv[1])
    rows = []
    for dp, _, fs in os.walk(sl):
        for f in fs:
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, sl)
            if rel == 'MANIFEST.md':
                continue
            role = next((r for pat, r in ROLES if re.search(pat, rel)), 'other')
            rows.append((rel, role, hashlib.sha256(open(p, 'rb').read()).hexdigest()))
    out = ['# ' + TITLE, '', 'Written by scripts/mk_slice_manifest.py; not edited by hand. Start with RECORD.md.', '',
           '| path | role | sha256 |', '|---|---|---|'] + ['| `%s` | %s | `%s` |' % r for r in sorted(rows)]
    open(os.path.join(sl, 'MANIFEST.md'), 'w').write('\n'.join(out) + '\n')


if __name__ == '__main__':
    main()
