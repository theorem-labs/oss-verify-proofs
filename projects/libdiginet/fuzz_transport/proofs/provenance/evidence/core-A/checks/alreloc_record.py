#!/usr/bin/env python3
"""The generated part of the alreloc cross-check record (libdiginet/fuzz_transport image-A core): counts, classes,
decisions, every WRONG / UNDECIDED row, every disagreement, alreloc's rule-`gap` / rule-`symbol` rows, the planted
control and the pins of every input. Kind: measurement; it proves no function.

  alreloc_record.py WORK LIB OUT > tables.md

OUT is the directory alreloc-xcheck.sh and alreloc-xcheck-control.sh filled (alreloc-crosscheck-rows.tsv, out/,
control/, run-A.log, run-R.log, fixture-commit.txt). Reads only; writes markdown on stdout.
"""
import collections, hashlib, os, re, subprocess, sys

WORK, LIB, OUT = sys.argv[1:4]
HERE = os.path.dirname(os.path.abspath(__file__))


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def tree_sha(d):
    """sha256 over the sorted lines `<sha256>  <relative path>` of every file under d (as `sha256sum` prints them)"""
    lines = []
    for root, _, fs in os.walk(d):
        for f in fs:
            p = os.path.join(root, f)
            lines.append('%s  %s\n' % (sha(p), os.path.relpath(p, d)))
    return hashlib.sha256(''.join(sorted(lines, key=lambda l: l.split('  ', 1)[1])).encode()).hexdigest(), len(lines)


def rows(path):
    L = open(path).read().split('\n')
    h = L[0].split('\t')
    return [dict(zip(h, l.split('\t'))) for l in L[1:] if l]


def lib_rel(f):
    return f.split('/lib/', 1)[-1]


def cut(s, n):
    s = s.replace('|', '/')
    return s if len(s) <= n else s[:n - 3] + '...'


R = rows(os.path.join(OUT, 'alreloc-crosscheck-rows.tsv'))
verdict = lambda r: r['decision'].split(':')[0] if r['decision'] != '-' else '-'
CLASSES = ('agree', 'both-kept', 'disagree', 'alreloc-unmapped', 'alreloc-refused', 'not-covered', 'added')
out = []
w = out.append

# ------------------------------------------------------------------ result
nW = [r for r in R if verdict(r) == 'port_core WRONG']
nU = [r for r in R if verdict(r) == 'UNDECIDED']
nR = [r for r in R if verdict(r) == 'port_core right']
nX = [r for r in R if verdict(r) == '-']
dis = [r for r in R if r['class'] == 'disagree']
w('**Result: port_core is WRONG at %d numeral position%s of WORK/stage-out; %d position%s UNDECIDED.** Of %d numeral '
  'positions, %d were decided against the ELF images (%d `port_core right`, %d `port_core WRONG`); %d are out of scope '
  '(both tools kept the donor\'s value: below 0x10000 with no alreloc rule row, or at / above the image top and outside '
  'the image\'s shadow). alreloc and port_core disagree at %d positions.' % (
      len(nW), '' if len(nW) == 1 else 's', len(nU), ' is' if len(nU) == 1 else 's are', len(R),
      len(nW) + len(nU) + len(nR), len(nR), len(nW), len(nX), len(dis)))
w('')

# ------------------------------------------------------------------ WRONG / UNDECIDED rows
w('## port_core WRONG (%d)' % len(nW))
w('')
if nW:
    w('| file | stage-out line | donor line | tok | written (port_core) | right | alreloc | measurement |')
    w('|---|---|---|---|---|---|---|---|')
    for r in nW:
        m = re.search(r'right value (\S+(?: or \S+)*)', r['decision'])
        w('| %s | %s | %s | %s | %s | %s | %s | %s |' % (r['file'], r['out_line'], r['donor_line'], r['tok'],
                                                         r['port_core'], m.group(1).rstrip('.;,') if m else
                                                         cut(r['decision'], 80), r['alreloc'], cut(r['elf_reading'], 600)))
else:
    w('none')
w('')
w('## UNDECIDED (%d)' % len(nU))
w('')
for r in nU:
    w('- %s:%s (donor line %s) tok %s: donor %s, port_core %s, alreloc %s: %s; %s' % (
        r['file'], r['out_line'], r['donor_line'], r['tok'], r['donor'], r['port_core'], r['alreloc'], r['decision'],
        cut(r['elf_reading'], 400)))
if not nU:
    w('none')
w('')

# ------------------------------------------------------------------ counts
w('## Counts')
w('')
w('| class | positions | decided right | decided WRONG | UNDECIDED | not in scope |')
w('|---|---|---|---|---|---|')
by = collections.defaultdict(collections.Counter)
for r in R:
    by[r['class']][verdict(r)] += 1
tot = collections.Counter()
for cl in CLASSES:
    c = by.get(cl, collections.Counter())
    tot.update(c)
    w('| %s | %d | %d | %d | %d | %d |' % (cl, sum(c.values()), c['port_core right'], c['port_core WRONG'],
                                           c['UNDECIDED'], c['-']))
w('| total | %d | %d | %d | %d | %d |' % (sum(tot.values()), tot['port_core right'], tot['port_core WRONG'],
                                         tot['UNDECIDED'], tot['-']))
w('')
w('agree / disagree / decided, as the brief counts them: %d positions; alreloc and port_core agree at %d (the same value: '
  '%d both moved alike, %d both kept), disagree at %d; alreloc gave no value at %d (flagged %d, refused %d); %d positions '
  'have no donor partner (%d on lines a port_core patch replaced, %d on lines port_core added); decided against the '
  'images: %d.' % (len(R), sum(by['agree'].values()) + sum(by['both-kept'].values()),
                   sum(by['agree'].values()), sum(by['both-kept'].values()), sum(by['disagree'].values()),
                   sum(by['alreloc-unmapped'].values()) + sum(by['alreloc-refused'].values()),
                   sum(by['alreloc-unmapped'].values()), sum(by['alreloc-refused'].values()),
                   sum(by['not-covered'].values()) + sum(by['added'].values()), sum(by['not-covered'].values()),
                   sum(by['added'].values()), len(nW) + len(nU) + len(nR)))
w('')
sc = collections.Counter()
for r in R:
    for s in r['scope'].split(','):
        if s != '-':
            sc[s] += 1
w('Scope reasons (a position can have several): %s.' % ', '.join('%s %d' % kv for kv in sorted(sc.items())))
w('')
w('### Classes (every numeral position of stage-out)')
w('')
w('| class | kind | positions |')
w('|---|---|---|')
ck = collections.Counter((r['class'], r['kind'] or '-') for r in R)
for (cl, k), n in sorted(ck.items(), key=lambda x: (CLASSES.index(x[0][0]), x[0][1])):
    w('| %s | %s | %d |' % (cl, k, n))
w('| total | | %d |' % len(R))
w('')
w('### Decisions by class and group')
w('')
w('| class | group | verdict | positions |')
w('|---|---|---|---|')
cg = collections.Counter((r['class'], r['group'], verdict(r)) for r in R)
for (cl, g, v), n in sorted(cg.items(), key=lambda x: (CLASSES.index(x[0][0]), x[0][1], x[0][2])):
    w('| %s | %s | %s | %d |' % (cl, g, v, n))
w('')

# ------------------------------------------------------------------ alreloc
av = collections.Counter(r['alreloc_verdict'] for r in R if r['decision'] != '-')
w('### alreloc judged by the decisions')
w('')
w('Column alreloc_verdict over the %d decided positions: %s.' % (
    len(nW) + len(nU) + len(nR), ', '.join('%s %d' % kv for kv in sorted(av.items()))))
w('')
for rule, name in (('gap', 'rule `gap` (a .got / gap cell mapped by its OFFSET)'),
                   ('symbol', 'rule `symbol` (low numbers moved to symbol offsets)')):
    rr = [r for r in R if r['alreloc_rule'].split(' (')[0] == rule]
    vc = collections.Counter((r['alreloc_verdict'], verdict(r)) for r in rr)
    w('- %s: %d rows; alreloc verdict / decision: %s.' % (name, len(rr), ', '.join(
        '%s / %s %d' % (a, b, n) for (a, b), n in sorted(vc.items()))))
    for r in rr:
        if r['alreloc_verdict'] == 'WRONG':
            w('  - %s:%s tok %s: donor %s, alreloc %s, port_core %s (%s): %s' % (
                lib_rel(r['file']), r['out_line'], r['tok'], r['donor'], r['alreloc'], r['port_core'], r['group'],
                cut(r['elf_reading'], 260)))
got = [r for r in R if 'got' in r['scope'].split(',')]
w('- rows with a .got value (scope `got`): %d; decisions: %s; alreloc verdicts: %s.' % (
    len(got), ', '.join('%s %d' % kv for kv in sorted(collections.Counter(verdict(r) for r in got).items())),
    ', '.join('%s %d' % kv for kv in sorted(collections.Counter(r['alreloc_verdict'] for r in got).items()))))
w('')

# ------------------------------------------------------------------ every disagreement
w('### Every disagreement (%d rows)' % len(dis))
w('')
w('| file:line (out) | donor | port_core | alreloc | alreloc rule | alreloc verdict | kind | group | verdict | ELF reading |')
w('|---|---|---|---|---|---|---|---|---|---|')
for r in dis:
    w('| %s:%s (%s) | %s | %s | %s | %s | %s | %s | %s | %s | %s |' % (
        lib_rel(r['file']), r['donor_line'], r['out_line'], r['donor'], r['port_core'], r['alreloc'],
        cut(r['alreloc_rule'], 40), r['alreloc_verdict'], r['kind'], r['group'], cut(r['decision'], 60),
        cut(r['elf_reading'], 300)))
w('')

# ------------------------------------------------------------------ control
C = os.path.join(OUT, 'control')
w('## Planted control (`OUT/control/verdict.txt`)')
w('')
if os.path.isfile(os.path.join(C, 'verdict.txt')):
    pl = rows(os.path.join(C, 'plants.tsv'))
    cr = {(lib_rel(r['file']), r['out_line'], r['tok']): r for r in rows(os.path.join(C, 'alreloc-crosscheck-rows.tsv'))}
    w('| plant | position | port_core -> planted | decision on the copy |')
    w('|---|---|---|---|')
    for p in pl:
        r = cr.get((p['file'], p['out_line'], p['tok']))
        w('| %s (%s) | %s:%s tok %s | %s -> %s | %s |' % (p['plant'], p['why'], p['file'], p['out_line'], p['tok'],
                                                        p['port_core'], p['planted'],
                                                        cut(r['decision'], 160) if r else 'no row'))
    w('')
    w('```')
    w(open(os.path.join(C, 'verdict.txt')).read().rstrip('\n'))
    w('```')
else:
    w('the control has not run (no OUT/control/verdict.txt)')
w('')
SW = os.path.join(OUT, 'sweep')
if os.path.isfile(os.path.join(SW, 'verdict.txt')):
    V = open(os.path.join(SW, 'verdict.txt')).read().rstrip('\n').split('\n')
    pl = rows(os.path.join(SW, 'plants.tsv'))
    w('### Plant sweep (`SWEEP="N SEED"`, OUT/sweep/verdict.txt of the last sweep run)')
    w('')
    w('Plants by the base decision\'s group: %s.' % ', '.join(
        '%s %d' % kv for kv in sorted(collections.Counter(p['plant'].split(':', 1)[1] for p in pl).items())))
    w('')
    w('```')
    for l in V:
        if not l.startswith('CAUGHT'):
            w(l)
    w('(%d CAUGHT lines not shown)' % sum(1 for l in V if l.startswith('CAUGHT')))
    w('```')
    w('')

# ------------------------------------------------------------------ pins
w('## Pins of this run')
w('')
w('| what | sha256 |')
w('|---|---|')
for f in sorted(os.listdir(HERE)):
    if f.endswith(('.py', '.sh')):
        w('| script %s | %s |' % (f, sha(os.path.join(HERE, f))))
for d, name in ((os.path.join(WORK, 'stage'), 'WORK/stage'), (os.path.join(WORK, 'stage-out'), 'WORK/stage-out'),
                (LIB, 'LIB')):
    s, n = tree_sha(d)
    w('| %s (%d files; sha256 of the sorted `sha256sum` lines) | %s |' % (name, n, s))
for f in ('alreloc-crosscheck-rows.tsv', 'out/positions.tsv', 'out/counts.tsv', 'out/decided-counts.tsv',
          'fixture-commit.txt'):
    p = os.path.join(OUT, f)
    if os.path.isfile(p):
        w('| OUT/%s | %s |' % (f, sha(p)))
for d in ('report', 'report-R'):
    if os.path.isdir(os.path.join(OUT, d)):
        s, n = tree_sha(os.path.join(OUT, d))
        w('| OUT/%s (alreloc\'s per-numeral reports, %d files) | %s |' % (d, n, s))
w('')
for lg in ('run-A.log', 'run-R.log'):
    p = os.path.join(OUT, lg)
    if os.path.isfile(p):
        L = open(p).read().split('\n')
        w('- alreloc %s: `%s`' % (lg, cut(next((l for l in L if l.startswith('alreloc: ') and ' files checked' in l),
                                                 '-'), 300)))
        w('  `%s`' % cut(next((l for l in L if l.startswith('alreloc: per-numeral report')), '-'), 300))
        w('  `%s`' % (next((l for l in L if l.startswith('rc=')), 'rc not recorded')))
print('\n'.join(out))
