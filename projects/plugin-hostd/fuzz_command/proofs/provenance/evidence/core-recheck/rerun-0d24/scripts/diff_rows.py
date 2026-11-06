#!/usr/bin/env python3
"""Compare two port_addr_check full.tsv row files of one gate, verdict by verdict.

Usage: diff_rows.py OLD.tsv NEW.tsv FLAG_CLASSES.txt OUTDIR

A row is one numeral of a paired file. Rows are matched by their numeral identity: image, source file and line,
ported file and line, sentence, index in the sentence, source value and ported value (the columns that say WHICH
numeral, not what the tool judged of it). A key that occurs more than once is matched in file order. Every row of
each side must find its partner; an unmatched row is written out and makes the exit status 1.

Writes OUTDIR/counts.txt (row counts, same / changed, the transition table) and OUTDIR/changed.tsv (every row
whose verdict changed: old verdict, new verdict, transition kind, then the new row's columns and the old row's
note). FLAG_CLASSES.txt is the output of --list-flag-classes (one class per line): a verdict in it is a finding
class, any other verdict is not.
"""
import collections
import hashlib
import os
import sys

KEY = ('image', 'src_file', 'src_line', 'dst_file', 'dst_line', 'sentence', 'idx', 'src_value', 'dst_value')


def load(path):
    head, rows, cols = [], [], None
    h = hashlib.sha256()
    with open(path, encoding='utf-8', errors='replace', newline='') as f:
        for line in f:
            if line.startswith('#'):
                head.append(line)
                continue
            h.update(line.encode('utf-8', 'replace'))
            parts = line.rstrip('\n').split('\t')
            if cols is None:
                cols = parts
                continue
            rows.append(parts)
    return cols, rows, h.hexdigest(), len(head)


def main():
    old_p, new_p, fc_p, out = sys.argv[1:5]
    flags = {l.strip() for l in open(fc_p) if l.strip()}
    oc, orows, osha, ohead = load(old_p)
    nc, nrows, nsha, nhead = load(new_p)
    if oc != nc:
        sys.exit(f'column sets differ:\n old {oc}\n new {nc}')
    ix = {c: i for i, c in enumerate(oc)}
    for k in KEY + ('verdict',):
        if k not in ix:
            sys.exit(f'no column {k}')
    kidx = [ix[k] for k in KEY]
    V, N = ix['verdict'], ix['note']

    def key(r):
        return tuple(r[i] for i in kidx)

    pool = collections.defaultdict(collections.deque)
    for r in orows:
        pool[key(r)].append(r)
    pairs, new_only = [], []
    for r in nrows:
        q = pool.get(key(r))
        if q:
            pairs.append((q.popleft(), r))
        else:
            new_only.append(r)
    old_only = [r for q in pool.values() for r in q]

    trans = collections.Counter()
    kinds = collections.Counter()
    changed = []
    for o, n in pairs:
        ov, nv = o[V], n[V]
        if ov == nv:
            kinds['same verdict'] += 1
            continue
        of, nf = ov in flags, nv in flags
        k = ('new flag (non-finding -> finding class)' if nf and not of else
             'flag cleared (finding class -> non-finding)' if of and not nf else
             'flag class changed (finding -> other finding class)' if of and nf else
             'non-finding class changed')
        kinds[k] += 1
        trans[(ov, nv, k)] += 1
        changed.append((ov, nv, k, n, o[N]))

    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, 'counts.txt'), 'w') as f:
        w = lambda s='': f.write(s + '\n')
        w(f'old {os.path.basename(os.path.dirname(old_p))}: {len(orows)} rows (+ column line, + {ohead} header lines); '
          f'sha256 of the rows without the # header block {osha[:12]}')
        w(f'new {os.path.basename(os.path.dirname(new_p))}: {len(nrows)} rows (+ column line, + {nhead} header lines); '
          f'sha256 of the rows without the # header block {nsha[:12]}')
        w(f'matched by numeral identity: {len(pairs)}; old rows unmatched: {len(old_only)}; new rows unmatched: {len(new_only)}')
        w(f'flagged rows: old {sum(r[V] in flags for r in orows)}, new {sum(r[V] in flags for r in nrows)}')
        w(f'same verdict: {kinds["same verdict"]}')
        w(f'changed verdict: {len(changed)}')
        for k in ('new flag (non-finding -> finding class)', 'flag cleared (finding class -> non-finding)',
                  'flag class changed (finding -> other finding class)', 'non-finding class changed'):
            w(f'  {k}: {kinds[k]}')
        w()
        w('transitions (old verdict -> new verdict: rows)')
        for (ov, nv, k), c in sorted(trans.items(), key=lambda t: (-t[1], t[0])):
            w(f'  {ov} -> {nv}: {c}  [{k}]')
    with open(os.path.join(out, 'changed.tsv'), 'w') as f:
        f.write('\t'.join(['old_verdict', 'new_verdict', 'change'] + oc + ['old_note']) + '\n')
        for ov, nv, k, n, onote in sorted(changed, key=lambda t: (t[3][ix['dst_file']], int(t[3][ix['dst_line']] or 0), t[3][ix['idx']])):
            f.write('\t'.join([ov, nv, k] + n + [onote]) + '\n')
    if old_only or new_only:
        with open(os.path.join(out, 'unmatched.tsv'), 'w') as f:
            for r in old_only:
                f.write('OLD\t' + '\t'.join(r) + '\n')
            for r in new_only:
                f.write('NEW\t' + '\t'.join(r) + '\n')
        sys.exit(1)


if __name__ == '__main__':
    main()
