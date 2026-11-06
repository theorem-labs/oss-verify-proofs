#!/usr/bin/env python3
"""Mechanical first pass over the FLAGGED rows of a port_addr_check full TSV.

Reads the run's rows whose verdict is a FLAG class (the tool's own set, given by --list-flag-classes) and settles a row
only by a rule that measures something in the ported file or the row itself:
  NO-PORTED-VALUE   UNPAIRED-SOURCE: the donor numeral has no ported numeral; the ported file holds no value here.
  PROOF-STEP        the ported numeral sits on a line inside a Proof ... Qed block of the ported file (a proof step);
                    the ported file has no Admitted / admit / Abort, so the kernel checks every such step.
  KERNEL-FACT       the tool's kernel_checked column is "yes": the numeral is inside a fail-loud vm_compute /
                    fetch_word fact that the kernel evaluates (not a proof step of a Defined term).
  GENERATED         the ported file is in the generated set given on the command line (routed to its own triage).
Every other flagged row is written as OPEN for measured triage.
Usage: base_triage.py RUN.full.tsv PORTED_DIR FLAG_CLASSES_FILE GENERATED_LIST OUT_PREFIX
Writes OUT_PREFIX.settled.tsv, OUT_PREFIX.open.tsv, OUT_PREFIX.gen.tsv and prints the counts."""
import csv, os, re, sys
from collections import Counter

csv.field_size_limit(10 ** 9)
run, ported, flagfile, genlist, out = sys.argv[1:6]
FLAGS = set(l.strip() for l in open(flagfile) if l.strip() and not l.startswith('#'))
GEN = set(l.strip() for l in open(genlist) if l.strip() and not l.startswith('#'))

_proof_lines = {}


def proof_info(fname):
    """(set of 1-based lines inside Proof..Qed, has_admit) for a ported file."""
    if fname in _proof_lines:
        return _proof_lines[fname]
    p = os.path.join(ported, fname)
    text = open(p, encoding='utf-8', errors='replace').read()
    # blank out comments, keeping line structure
    def blank(m):
        return re.sub(r'[^\n]', ' ', m.group(0))
    code = text
    for _ in range(3):  # nested comments
        code = re.sub(r'\(\*(?:(?!\(\*).)*?\*\)', blank, code, flags=re.S)
    has_admit = bool(re.search(r'\b(Admitted|admit|Abort)\b', code))
    inside = set()
    state = False
    tok = re.compile(r'\b(Proof|Qed|Defined|Admitted)\s*\.')
    for i, line in enumerate(code.split('\n'), 1):
        events = [m.group(1) for m in tok.finditer(line)]
        if state or 'Proof' in events:
            inside.add(i)
        for e in events:
            if e == 'Proof':
                state = True
            elif e == 'Qed':
                state = False
            elif e in ('Defined', 'Admitted'):
                state = False
                inside.discard(i) if e == 'Defined' else None
    # lines of Defined proofs are not kernel-only: remove every block that ends in Defined
    lines = code.split('\n')
    start = None
    for i, line in enumerate(lines, 1):
        events = [m.group(1) for m in tok.finditer(line)]
        for e in events:
            if e == 'Proof':
                start = i
            elif e == 'Defined' and start is not None:
                for j in range(start, i + 1):
                    inside.discard(j)
                start = None
            elif e == 'Qed':
                start = None
    _proof_lines[fname] = (inside, has_admit)
    return _proof_lines[fname]


rows = [r for r in csv.reader((l for l in open(run) if not l.startswith('#')), delimiter='\t')]
hdr, rows = rows[0], rows[1:]
settled, opened, gen = [], [], []
cnt = Counter()
for r in rows:
    v = r[0]
    if v not in FLAGS:
        continue
    f = r[5] or r[3]
    if f in GEN:
        gen.append(r)
        cnt[('GENERATED', v)] += 1
        continue
    if v == 'UNPAIRED-SOURCE':
        settled.append(r + ['NO-PORTED-VALUE', 'donor numeral with no ported numeral (%s)' % r[15][:80]])
        cnt[('NO-PORTED-VALUE', v)] += 1
        continue
    if r[5] and r[6]:
        inside, has_admit = proof_info(r[5])
        if int(r[6]) in inside and not has_admit:
            settled.append(r + ['PROOF-STEP', '%s:%s inside Proof..Qed; file has no Admitted/admit/Abort' % (r[5], r[6])])
            cnt[('PROOF-STEP', v)] += 1
            continue
    if r[1] == 'yes':
        settled.append(r + ['KERNEL-FACT', 'tool kernel_checked=yes (vm_compute / fetch_word fact)'])
        cnt[('KERNEL-FACT', v)] += 1
        continue
    opened.append(r)
    cnt[('OPEN', v)] += 1

H = hdr + ['reason', 'measurement']
for name, data, h in (('settled', settled, H), ('open', opened, hdr), ('gen', gen, hdr)):
    with open(f'{out}.{name}.tsv', 'w') as fh:
        fh.write('\t'.join(h) + '\n')
        for r in data:
            fh.write('\t'.join(r) + '\n')
for k in sorted(cnt):
    print(*k, cnt[k], sep='\t')
print('settled', len(settled), 'open', len(opened), 'generated', len(gen))
