#!/usr/bin/env python3
"""mk_slice_manifest.py SLICE_DIR TITLE -- writes SLICE_DIR/MANIFEST.md for one malloc / free record slice
(<unit>-b-alloc): a `# TITLE` first line, then every file of the slice with its role and sha256. The role comes from
the file's name only (the table ROLES below); a file no rule matches is listed as 'other' so nothing is left out.
The manifest does not list itself."""
import hashlib, os, re, sys

ROLES = [
    (r'^RECORD\.md$', 'the record: theorems, build, Print Assumptions, bytecmp method, results, controls, limits'),
    (r'(^|/)RECORD\.md$', 'the record of its version directory'),
    (r'^INTERCEPTORS\.md$', 'interceptor / __asan_* inventory of the uci, egress and wire B images'),
    (r'^mk_slice_manifest\.py$', 'this slice\'s manifest writer'),
    (r'^run\.sh$', 'reruns every measurement of the record'),
    (r'(^|/)run\.sh$', 'reruns the measurements of its directory'),
    (r'(^|/)tools\.sha256$', 'sha256 of every script run'),
    (r'^ACCEPTANCES\.tsv$', 'every kit-reported row and target with its named measurement and settled verdict'),
    (r'^REVIEW\.md$', 'the fresh reviewer\'s audit of the acceptances'),
    (r'(^|/)settle\.tsv$', 'per-target settlement output'),
    (r'(^|/)dupcheck\.tsv$', 'names with more than one symbol-table entry, checked by address'),
    (r'(^|/)other-rows\.txt$', 'the kit-reported rows'),
    (r'(^|/)tools/DIFFS\.md$', 'each tool copy: its sha256, the original\'s sha256 and source, and the diff original -> copy'),
    (r'(^|/)images\.sha256$', 'sha256 of every image read'),
    (r'(^|/)tools/[^/]+\.py$', 'measurement script (copied; tools.sha256 names it)'),
    (r'^inventory/[^/]+\.py$', 'inventory script'),
    (r'^inventory/(v[0-9a-f]{12}/)?inventory-.*\.tsv$', 'per-symbol inventory of one image'),
    (r'^inventory/(v[0-9a-f]{12}/)?summary-.*\.out$', 'inventory summary of one image'),
    (r'(^|/)twins\.out$', 'PT_LOAD equality of each unstripped twin and its pin'),
    (r'(^|/)roots-syms\.out$', 'root addresses confirmed from each image\'s symbols'),
    (r'(^|/)roots\.tsv$', 'root-pair bytecmp verdicts'),
    (r'(^|/)closure-.*\.out$', 'by-name closure comparison'),
    (r'(^|/)paircl-.*\.out$', 'paircl closure pairing from one root'),
    (r'(^|/)pairtable-.*\.out$', 'per-function table of a paircl pairing'),
    (r'(^|/)pairs-.*\.tsv$', 'per-pair rows of a paircl pairing'),
    (r'(^|/)jtcheck-members\.txt$', 'jump / constant-table members checked'),
    (r'(^|/)jtcheck-.*\.out$', 'jtcheck results for the table members'),
    (r'(^|/)cietable\.out$', 'parseCIE jump table read entry by entry'),
    (r'(^|/)ctl-.*$', 'control run (identity-B known-equal or planted change)'),
    (r'(^|/)planted/planted\.(sha256|cmp)$', 'planted-control image hashes and the changed word'),
]


def role(rel):
    m = re.search(r'(^|/)v([0-9a-f]{12})/', rel)
    for pat, r in ROLES:
        if re.search(pat, rel):
            return ('earlier run (previous tool version %s): %s' % (m.group(2), r)) if m else r
    return 'other'


def main():
    top, title = os.path.abspath(sys.argv[1]), sys.argv[2]
    rows = []
    for dp, _, fs in os.walk(top):
        for f in fs:
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, top)
            if rel == 'MANIFEST.md':
                continue
            rows.append((rel, role(rel), hashlib.sha256(open(p, 'rb').read()).hexdigest()))
    rows.sort()
    out = ['# ' + title, '',
           'Written by mk_slice_manifest.py (this slice). Start with RECORD.md. The planted-control ELF copies are not '
           'committed: planted/planted.sha256 names them and run.sh regenerates them.', '',
           '| path | role | sha256 |', '|---|---|---|']
    out += ['| `%s` | %s | `%s` |' % r for r in rows]
    open(os.path.join(top, 'MANIFEST.md'), 'w').write('\n'.join(out) + '\n')
    print('mk_slice_manifest: %d files, %d other' % (len(rows), sum(1 for r in rows if r[1] == 'other')))


if __name__ == '__main__':
    main()
