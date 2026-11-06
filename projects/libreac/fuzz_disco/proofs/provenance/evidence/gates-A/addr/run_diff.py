#!/usr/bin/env python3
"""run_diff.py -- compare two port_addr_check row tables of the same file set (an older and a newer checker version).

Reads both `--out` tables (comment lines `#` skipped, the header row kept) and aligns the rows by their IDENTITY: the
numeral's place and values (image, src_file, src_line, dst_file, dst_line, sentence, idx, kind, src_value, dst_value),
which no checker version decides. The verdict, the kernel column, the checker's readings (src_class, src_res, dst_res)
and the note may differ. A version may write the rows in another order, so rows are not aligned by position. Rows of
one identity that occur more than once pair first where the whole row is equal, then in table order. It prints:
  - the row count of each table and the verdict counts of each (and whether they are equal);
  - every changed row pair: its file:line, sentence, value, its verdict (`OLD -> NEW` where it moved) and the columns
    whose text differs;
  - rows whose identity is only in the old or only in the new table;
  - per changed column, how many rows differ in it, and per verdict move `OLD -> NEW`, how many rows made it.
The last line is `run_diff: <n> rows differ; <m> verdicts moved; verdicts identical: <yes|no>` (identical: no row's
verdict moved and no row is on one side only).

Usage: run_diff.py OLD.tsv NEW.tsv [--moved-out MOVED.tsv]
  --moved-out   write the NEW table's rows whose verdict moved, with a first column old_verdict
"""
import collections, sys

args = sys.argv[1:]
moved_out = None
if '--moved-out' in args:
    i = args.index('--moved-out')
    moved_out = args[i + 1]
    del args[i:i + 2]
if len(args) != 2:
    sys.exit(__doc__)


def load(p):
    rows = [l.rstrip('\n').split('\t') for l in open(p, encoding='utf-8', errors='replace') if not l.startswith('#')]
    return rows[0], rows[1:]


ho, old = load(args[0])
hn, new = load(args[1])
if ho != hn:
    sys.exit(f'run_diff: REFUSED: the headers differ: {ho} / {hn}')
H = ho
col = {c: i for i, c in enumerate(H)}
IDENT = [col[c] for c in ('image', 'src_file', 'src_line', 'dst_file', 'dst_line', 'sentence', 'idx', 'kind',
                          'src_value', 'dst_value')]
ident = lambda r: tuple(r[i] if i < len(r) else '' for i in IDENT)
V = col['verdict']
vo = collections.Counter(r[V] for r in old)
vn = collections.Counter(r[V] for r in new)
print(f'rows: old {len(old)}, new {len(new)}')
for v in sorted(set(vo) | set(vn)):
    print(f'verdict {v}: old {vo[v]}, new {vn[v]}' + ('' if vo[v] == vn[v] else '  CHANGED'))

by_new = collections.defaultdict(list)
for r in new:
    by_new[ident(r)].append(r)
pairs, only_old = [], []
by_old = collections.defaultdict(list)
for r in old:
    by_old[ident(r)].append(r)
for k, olds in by_old.items():
    news = by_new.pop(k, [])
    rest = []
    for r in olds:
        if r in news:
            news.remove(r)
            pairs.append((r, r))
        else:
            rest.append(r)
    pairs += list(zip(rest, news))
    only_old += rest[len(news):]
    by_new[k] = news[len(rest):]
only_new = [r for rs in by_new.values() for r in rs]
changed = [(a, b) for a, b in pairs if a != b]
# report in the new table's order
pos = {id(r): i for i, r in enumerate(new)}
changed.sort(key=lambda ab: pos[id(ab[1])])

bycol, moves = collections.Counter(), collections.Counter()
for a, b in changed:
    d = [H[i] for i in range(len(H)) if (a[i] if i < len(a) else '') != (b[i] if i < len(b) else '')]
    bycol.update(d)
    v = b[V] if a[V] == b[V] else f'{a[V]} -> {b[V]}'
    if a[V] != b[V]:
        moves[(a[V], b[V])] += 1
    print(f'changed {b[col["dst_file"]] or b[col["src_file"]]}:{b[col["dst_line"]] or b[col["src_line"]]} '
          f'{b[col["sentence"]]} {b[col["dst_value"]] or b[col["src_value"]]} verdict {v}: columns {", ".join(d)}')
for r in only_old:
    print(f'only in old: {r[V]} {r[col["dst_file"]] or r[col["src_file"]]}:{r[col["dst_line"]] or r[col["src_line"]]}')
for r in only_new:
    print(f'only in new: {r[V]} {r[col["dst_file"]] or r[col["src_file"]]}:{r[col["dst_line"]] or r[col["src_line"]]}')
for c, n in sorted(bycol.items()):
    print(f'column {c}: {n} rows differ')
for (x, y), n in sorted(moves.items(), key=lambda m: (-m[1], m[0])):
    print(f'moved {x} -> {y}: {n} rows')
if moved_out:
    with open(moved_out, 'w') as f:
        f.write('\t'.join(['old_verdict'] + H) + '\n')
        for a, b in changed:
            if a[V] != b[V]:
                f.write('\t'.join([a[V]] + b) + '\n')
nmoved = sum(moves.values())
same = nmoved == 0 and not only_old and not only_new
print(f'run_diff: {len(changed) + len(only_old) + len(only_new)} rows differ; {nmoved} verdicts moved; '
      f'verdicts identical: {"yes" if same else "no"}')
