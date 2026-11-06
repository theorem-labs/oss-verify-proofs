#!/usr/bin/env python3
"""hashlen_sweep.py REPO HEAD BASE MAP.tsv OUT.tsv [--apply] -- the hash-length convention: a commit is cited at 12
hex, a sha256 at 12 hex beside the word `sha256`; the full form stays only in a tool's own output; a line byte-equal
to a line of BASE under projects/ or proofs/ (an inherited released line) is exempt.

HEAD is a commit, or WORKTREE (the index's files read from the worktree; --apply needs WORKTREE). EXEMPT below lists
the tool-output lines and non-shipped files (scope `out`, with the reason).
MAP.tsv rows: FULL<TAB>KIND<TAB>WHAT, KIND commit or sha256, FULL the whole id. Every hex run in the unit's files at
HEAD (projects/reac-repacer/fuzz_wire/proofs, projects/reac-repacer/fuzz_wire) that is a prefix of a FULL id, at least 8 long
and not 12 long, is a case. A case is IN SCOPE when it is in comment text of a .v file (nested `(* *)`) or on a line
of a .md file, and the file is not a tool's own output (PROVENANCE.md, SHA256SUMS) and the line is not inherited.
OUT.tsv: one row per case: file, line, token, length, kind, what, scope (in / out and why), the line text.
With --apply every in-scope case is rewritten to the 12-hex form of its id, comment text only; a .v file whose
comment-stripped token stream would change refuses the run (exit 2); every other byte stays."""
import os, re, subprocess, sys

HEX = re.compile(r'(?<![0-9A-Za-z_])([0-9a-f]{8,64})(?![0-9A-Za-z_])')
# Tool output and non-shipped files (the convention's exemptions, ruling 'a)': (file regex, line regex, scope)
EXEMPT = [
    (r'\.v$', r'^\(\* Read from: ', "out: tool output, the `Read from` line the start-up tools of record write (pins.provenance)"),
    (r'/A/(AD1y|AE23)\.v$', r'^\s*sha256 [0-9a-f]{64} \(values are its BYTES',
     'out: tool output, exitdrv.py formats this sha256 itself (its HDR)'),
    (r'/A/AE37\.v$', r'every image numeral re-derived for',
     "out: writer-hard-coded (ae37gen.py writes ish[:16]); fixed in the writer, not by hand"),
    (r'/provenance/TRUNK\.md$', r'', 'out: not shipped (provenance/TRUNK.md)'),
]


def git(repo, *a):
    return subprocess.run(['git', '-C', repo] + list(a), capture_output=True, text=True, errors='replace').stdout


def comment_spans(t):
    spans, d, i, s0 = [], 0, 0, 0
    while i < len(t):
        if t.startswith('(*', i):
            if d == 0:
                s0 = i
            d += 1; i += 2; continue
        if t.startswith('*)', i) and d:
            d -= 1; i += 2
            if d == 0:
                spans.append((s0, i))
            continue
        i += 1
    return spans


def code_tokens(t):
    keep, last = [], 0
    for s, e in comment_spans(t):
        keep.append(t[last:s]); last = e
    keep.append(t[last:])
    return ''.join(keep).split()


def main():
    repo, head, base, mp, out = sys.argv[1:6]
    apply = '--apply' in sys.argv[6:]
    ids = [l.split('\t') for l in open(mp).read().splitlines() if l.strip() and not l.startswith('#')]
    # HEAD = `WORKTREE`: the files git tracks in the index, read from the worktree (the state --apply edits)
    wt = head == 'WORKTREE'
    own = {os.path.basename(out), os.path.basename(mp)}   # the sweep's own output and its MAP are not measured
    files = [f for f in (git(repo, 'ls-files', '--', 'projects/reac-repacer/fuzz_wire/proofs', 'projects/reac-repacer/fuzz_wire') if wt else
                         git(repo, 'ls-tree', '-r', '--name-only', head, '--', 'projects/reac-repacer/fuzz_wire/proofs',
                             'projects/reac-repacer/fuzz_wire')).split('\n')
             if f and not f.endswith(('.gz', '.tar')) and os.path.basename(f) not in own]
    inh_cache, rows, edits = {}, [], {}

    def inherited(line):
        if line not in inh_cache:
            r = git(repo, 'grep', '-F', '-h', '-e', line, base, '--', 'projects', 'proofs')
            inh_cache[line] = any(x == line for x in r.split('\n'))
        return inh_cache[line]

    for f in files:
        t = (open('%s/%s' % (repo, f), encoding='utf-8', errors='surrogateescape').read() if wt else
             git(repo, 'show', '%s:%s' % (head, f)))
        if '\0' in t:
            continue
        spans = comment_spans(t) if f.endswith('.v') else None
        starts = [0] + [m.end() for m in re.finditer('\n', t)]
        for m in HEX.finditer(t):
            tok = m.group(1)
            hit = [i for i in ids if i[0].startswith(tok)]
            if not hit or len(tok) == 12:
                continue
            full, kind, what = hit[0][:3]
            ln = next(k for k in range(len(starts) - 1, -1, -1) if starts[k] <= m.start()) + 1
            line = t.split('\n')[ln - 1]
            base_name = f.rsplit('/', 1)[-1]
            ex = next((s for fr, lr, s in EXEMPT if re.search(fr, f) and re.search(lr, line)), None)
            if ex:
                scope = ex
            elif base_name in ('PROVENANCE.md', 'SHA256SUMS'):
                scope = 'out: a tool\'s own output'
            elif f.endswith('.v') and not any(s <= m.start() < e for s, e in spans):
                scope = 'out: Rocq code, not comment text'
            elif not (f.endswith('.v') or f.endswith('.md')):
                scope = 'out: not a .v comment or a .md line (a verbatim record or a script)'
            elif inherited(line):
                scope = 'out: inherited line (byte-equal to a released line)'
            else:
                scope = 'in'
            if kind == 'sha256' and scope == 'in' and 'sha256' not in line[max(0, m.start() - starts[ln - 1] - 40):m.start() - starts[ln - 1]]:
                scope = 'in (no `sha256` word before it: add it by hand-free rule? flagged)'
            rows.append((f, ln, tok, len(tok), kind, what, scope, line.strip()[:200]))
            if scope == 'in':
                edits.setdefault(f, []).append((m.start(), m.end(), full[:12]))
    with open(out, 'w') as o:
        o.write('file\tline\ttoken\tlength\tkind\twhat\tscope\tline text\n')
        for r in rows:
            o.write('\t'.join(str(x).replace('\\', '\\\\').replace('\t', '\\t') for x in r) + '\n')
    from collections import Counter
    print('hashlen_sweep: %d case(s); scope %s; files to edit %d' % (len(rows), dict(Counter(r[6] for r in rows)), len(edits)))
    if not apply:
        return
    if not wt:
        sys.exit('hashlen_sweep: --apply edits the worktree; give HEAD as WORKTREE')
    for f, es in edits.items():
        t = open('%s/%s' % (repo, f), encoding='utf-8', errors='surrogateescape').read()
        n = t
        for s, e, rep in sorted(es, reverse=True):
            n = n[:s] + rep + n[e:]
        if f.endswith('.v') and code_tokens(n) != code_tokens(t):
            sys.exit('hashlen_sweep: REFUSED, %s: the code token stream would change' % f)
        open('%s/%s' % (repo, f), 'w', encoding='utf-8', errors='surrogateescape').write(n)
    print('hashlen_sweep: rewrote %d case(s) in %d file(s)' % (sum(len(v) for v in edits.values()), len(edits)))


if __name__ == '__main__':
    main()
