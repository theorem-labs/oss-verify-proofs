#!/usr/bin/env python3
"""mkdiffs.py -- the writer of TOOLS_DIR/DIFFS.md. Read-only on its inputs.

For every *.py in TOOLS_DIR it writes the copy's sha256 and its origin:
  - a copy given with --orig NAME ORIG_FILE: the original's sha256, its source (SOURCES below, by the original's
    sha256; an original with no recorded source is refused) and the unified diff original -> copy, with no context
    lines. In the diff's removed lines, text that names a host path, an internal branch, a lane or a worker is shown as
    <redacted> (REDACT below). The sha256 of the unredacted diff is given too, so that a holder of the original can
    check the diff;
  - a copy that is byte-equal to a recorded original: its source, "unchanged";
  - a script written for these records (OURS): no original.
Any other script is refused (exit 1), and so is a DIFFS.md that would still hold such text (FORBIDDEN below).
usage: mkdiffs.py TOOLS_DIR [--orig NAME ORIG_FILE]..."""
import argparse, difflib, hashlib, os, re, sys

SURVEY = 'image-B donor survey scripts (repacer/B-DONORS.md)'
MEMCPY = 'commit 7af39d3f61c, proofs/reac-repacer/fuzz_uci/provenance/evidence/uci-b-memcpy/'
REG = 'tool registry commit '
SOURCES = {   # original sha256 -> source
    '1480ca2faea075e866800faab4e18aea5fb4a96dcea17ef1fe8981f1bdd0f98f':
        REG + '797e8971d27d, tools/bytecmp/1480ca2faea0/bytecmp.py (its lines 39-151 are insnflow a36c2b82eb44, '
        'tools/insnflow/a36c2b82eb44/insnflow.py at the same commit)',
    '7daa0e2a03d904b973bab1bbb68e57e0e32113d3620950132e296b7a6cc06e24': REG + '797e8971d27d, tools/bytecmp/7daa0e2a03d9/bytecmp.py',
    '9cbc3553c09e71a3687353b0b6995081f8b42660b6b12ecd279757449c6d6e1a':
        REG + '797e8971d27d, tools/repin_check/9cbc3553c09e/repin_check.py (superseded by e5487165abb8)',
    'e5487165abb8dfb7a39518a418fc24a0e815cea74918943bafbf35667c70ed11':
        REG + 'f69e6d74ebe, tools/repin_check/e5487165abb8/repin_check.py (supersedes 9cbc3553c09e: two different '
        'named targets are a difference)',
    '27f7a0e92bb9fdd59033bcdc5e7fcb349a20e97f7c02c43f3f5ffbb55347f89e':
        MEMCPY + 'drvcmp.py (the drvcmp.py of the ' + SURVEY + ' with bytecmp switched to 1480ca2faea0)',
    'fbbdb144ddfc1bbb743ec508071e3396b1f2794528b774d7fbc86d2a1dd366d0': SURVEY + ': drvcmp.py (loads bytecmp 7daa0e2a03d9)',
    'b50998fb3bd3db5ec374b380157492a819044f992c3fd895d3cb2f2764578f77':
        SURVEY + ': closure.py (the same bytes as ' + MEMCPY + 'closure.py)',
    '16e1466be22de053d502d781cae2454b6dd862138a92c0a8c8eaa3b7638de9e4': SURVEY + ': paircl.py (superseded by a88c2822a0f2)',
    '2e2f9c2126b21aa300f44228af1af74298db3c6e196da97b0038c12a3acfebce': SURVEY + ': jtcheck.py',
    'a88c2822a0f2b5fd223a96a5e8dc3bb476a776a2162bf0920786d0e78e3608de':
        REG + 'b73d10eb732, tools/paircl/a88c2822a0f2/paircl.py (supersedes 16e1466be22d: target names are compared '
        'first; Y\'s unstripped twin is its 5th argument)',
}
OURS = {'pairtable.py': 'runs paircl.py via runpy; one TSV row per pair',
        'cietable.py': "reads parseCIE's jump table",
        'syms.py': 'symbol lookup',
        'inventory.py': 'interceptor inventory',
        'scrub_out.py': 'the one writer of the committed slice',
        'mkdiffs.py': 'the writer of this DIFFS.md'}
def _SF(k): return [l.rstrip('\n').split('\t', 1)[1] for l in open(os.environ['SCRUB_FORBIDDEN']) if l.split('\t', 1)[0] == k][0]   # the patterns below: read at run time from SCRUB_FORBIDDEN
REDACT = re.compile(_SF('va88c2822a0f2/tools/mkdiffs.py:47')
                    + _SF('va88c2822a0f2/tools/mkdiffs.py:48')
                    + _SF('va88c2822a0f2/tools/mkdiffs.py:49') + r""
                    r"|(?<![a-z0-9_])[h]-[a-z][a-z0-9]*(?:-[a-z0-9_]+)+"
                    r"|(?<![a-z0-9_])(?:[c]-libc-[a-z0-9_-]*|[p]ort-(?!(?:built|commit|table|slot|license|prefix|hash)\b)"
                    r"[a-z][a-z0-9_-]*)", re.I)
FORBIDDEN = re.compile(_SF('va88c2822a0f2/tools/mkdiffs.py:53'), re.I)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('tools')
    ap.add_argument('--orig', nargs=2, action='append', default=[], metavar=('NAME', 'ORIG_FILE'))
    a = ap.parse_args()
    orig = dict(a.orig)
    names = sorted(n for n in os.listdir(a.tools) if n.endswith('.py'))
    bad = [n for n in orig if n not in names]
    table, sections = [], []
    for n in names:
        cb = open(os.path.join(a.tools, n), 'rb').read(); cs = sha(cb)
        if n in orig:
            ob = open(orig[n], 'rb').read(); os_ = sha(ob)
            if os_ not in SOURCES:
                bad.append('%s: the original has no recorded source' % n); continue
            ol, cl = ob.decode().splitlines(True), cb.decode().splitlines(True)
            full = list(difflib.unified_diff(ol, cl, 'a/' + n, 'b/' + n, n=0))
            shown = [REDACT.sub('<redacted>', ln) if ln.startswith('-') and not ln.startswith('---') else ln
                     for ln in full]
            nrm = sum(1 for ln in full if ln[:1] == '-' and ln[:3] != '---')
            nad = sum(1 for ln in full if ln[:1] == '+' and ln[:3] != '+++')
            table.append((n, cs, os_, SOURCES[os_], '%d removed, %d added (%d lines in, %d lines out)' % (
                nrm, nad, len(ol), len(cl))))
            sections.append('## %s\n\n- copy sha256 `%s`\n- original sha256 `%s`: %s\n- sha256 of the unredacted diff: '
                            '`%s`\n\n```diff\n%s```\n' % (n, cs, os_, SOURCES[os_], sha(''.join(full).encode()),
                                                         ''.join(x if x.endswith('\n') else x + '\n' for x in shown)))
        elif cs in SOURCES:
            table.append((n, cs, cs, SOURCES[cs], 'unchanged'))
        elif n in OURS:
            table.append((n, cs, '-', 'written for these records: ' + OURS[n], '-'))
        else:
            bad.append('%s: not a recorded original, not given with --orig, not written for these records' % n)
    text = ('# Tool copies: sources and changes\n\nWritten by mkdiffs.py. Each copy below is the script these records '
            'ran. A changed copy\'s diff against its original has no context lines and is the whole change; a host '
            'path that a copy now reads from the environment defaults to empty.\n\n'
            '| tool | copy sha256 | original sha256 | source | changed lines |\n|---|---|---|---|---|\n'
            + ''.join('| `%s` | `%s` | %s | %s | %s |\n' % (n, cs, ('`%s`' % os_) if os_ != '-' else '-', src, ch)
                      for n, cs, os_, src, ch in table)
            + '\n' + '\n'.join(sections))
    for m in FORBIDDEN.finditer(text):
        bad.append('DIFFS.md: forbidden text left at offset %d' % m.start())
    if bad:
        for b in bad:
            print('mkdiffs: REFUSED: ' + b, file=sys.stderr)
        sys.exit(1)
    open(os.path.join(a.tools, 'DIFFS.md'), 'w').write(text)
    print('mkdiffs: %d tools, %d changed copies' % (len(table), len(sections)))


if __name__ == '__main__':
    main()
