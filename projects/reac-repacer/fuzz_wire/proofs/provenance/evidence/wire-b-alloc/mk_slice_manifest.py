#!/usr/bin/env python3
"""mk_slice_manifest.py SLICE_DIR TITLE -- writes SLICE_DIR/MANIFEST.md for one malloc / free record slice
(<unit>-b-alloc): a `# TITLE` first line, then every file of the slice with its role and sha256. The role comes from
the file's name only (the table ROLES below); a file no rule matches is listed as 'other' so nothing is left out.
The manifest does not list itself."""
import hashlib, os, re, sys

ROLES = [
    (r'^RECORD\.md$', 'the record: verdict, fail-open shapes, criterion, tools, images, kit verdict, acceptances, hand '
                      'traces, exposure scans, controls, limits, unit gates, checks'),
    (r'(^|/)fieldscan\.tsv$', 'every load of each escaped field in both images (whole-image scan)'),
    (r'(^|/)ambiscan\.out$', 'the kit exposure scan for names with several copies'),
    (r'(^|/)luiscan\.tsv$', "the kit's rule-8 (lui) exposure scan, one row per function"),
    (r'(^|/)basescan\.tsv$', 'every load / store / jalr base named as its full address in both images, with its settlement'),
    (r'(^|/)cite(-extra)?\.tsv$', 'pinned-source citations used by the lui settlements'),
    (r'(^|/)cite\.sha256$', 'sha256 of cite.tsv and cite-extra.tsv'),
    (r'(^|/)luirows\.tsv$', "luiscan's exposed functions re-run on strictcmp3's tcmp by address, with every lui-in-section "
                            "target and its uses"),
    (r'(^|/)luitrace\.tsv$', 'the hand trace of every lui word: each use, its class and citation, or NOT CERTIFIED'),
    (r'(^|/)paircl-targets-.*\.tsv$', 'paircl target pairs per root, in full'),
    (r'(^|/)planted/plant_[a-z]_(kit|luitrace)\.out$', 'a planted control: the kit result and the hand-trace result'),
    (r'(^|/)plants\.out$', 'the hand-trace plants (a), (b) and (c): each plant, its rows and its verdict'),
    (r'(^|/)RECORD\.md$', 'the record of its version directory'),
    (r'^INTERCEPTORS\.md$', 'interceptor / __asan_* inventory of the uci, egress and wire B images'),
    (r'^mk_slice_manifest\.py$', 'this slice\'s manifest writer'),
    (r'^run\.sh$', 'reruns every measurement of the record'),
    (r'(^|/)run\.sh$', 'reruns the measurements of its directory'),
    (r'(^|/)tools\.sha256$', 'sha256 of every script run'),
    (r'(^|/)ACCEPTANCES\.tsv$', 'every kit-reported row and target with its named measurement and settled verdict'),
    (r'(^|/)REVIEW\.md$', 'the fresh reviewer\'s audit of the acceptances'),
    (r'(^|/)settle\.tsv$', 'per-target settlement output'),
    (r'(^|/)handtable\.out$', 'the hand settlement of each table jtcheck 226254f48c97 refuses: entries, dispatch and the '
                              'bound by a CFG walk, on both images (tools/handtable.py)'),
    (r'(^|/)dupcheck\.tsv$', 'every function compared by name: its symbol-table entries in X and Y, and the by-address '
                             'check of a name with more than one'),
    (r'(^|/)other-rows\.txt$', "the names of the kit's `other` closure members (one comma-separated line)"),
    (r'(^|/)tools/DIFFS\.md$', 'each tool copy: its sha256, the original\'s sha256 and source, and the diff original -> copy'),
    (r'(^|/)images\.sha256$', 'sha256 of every image read'),
    (r'(^|/)tools/[^/]+\.py$', 'a script of the record (tools.sha256 names it; tools/DIFFS.md gives its source)'),
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
    (r'(^|/)ctl-.*$', 'a control run: a planted change, its untouched baseline, or identity B (known-equal)'),
    (r'(^|/)planted/planted\.(sha256|cmp)$', 'planted-control image hashes and the changed word'),
    (r'(^|/)gate-controls\.txt$', 'the two negative controls of the gates: each must read FAIL'),
    (r'(^|/)gate-[a-z]+\.txt$', "one unit gate: its evidence lines and its `GATE ... VERDICT:` line"),
    (r'^handtable-read\.md$', "an independent reader's decode of the two hand-settled tables, without handtable.py"),
    (r'(^|/)SCRUB\.tsv$', "an archive's own record of its rewrites (role, time of day dropped, forbidden-word loader, "
                          "sha256 pin repair, DIFFS.md note): each file's sha256 as its version ran and as shipped"),
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
