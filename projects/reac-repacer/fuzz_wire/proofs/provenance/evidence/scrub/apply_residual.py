#!/usr/bin/env python3
"""apply_residual.py PROOFS ROWS : apply the residual rows of step (E) to the unit's proofs folder PROOFS.

Each row names one line (file, 1-based line number), the sha256 of the line as the scrub wrote it, and the line it
becomes. All rows are checked first; nothing is written unless every row's line either has the old sha256 (it is
rewritten) or is already the new text (a second run, nothing to do). Any other line refuses the whole run, exit 1.
Only the named lines change; every other byte of each file is kept, line endings included."""
import hashlib, sys

proofs, rows_path = sys.argv[1:3]
rows = []
for raw in open(rows_path, encoding='utf-8'):
    if raw.startswith('#') or raw.startswith('file\t'):
        continue
    f, n, old, new, _cls = raw.rstrip('\n').split('\t')
    if (f, int(n)) in {(r[0], r[1]) for r in rows}:
        sys.exit(f'apply_residual: refused, {f}:{n} has two rows')
    rows.append((f, int(n), old, new))
files, plan, bad = {}, [], []
for f, n, old, new in rows:
    if f not in files:
        files[f] = open(f'{proofs}/{f}', 'rb').read().decode('utf-8', 'surrogateescape').split('\n')
    if not 1 <= n <= len(files[f]):
        bad.append(f'{f}:{n} (no such line)')
        continue
    line = files[f][n - 1]
    if line == new:
        continue
    if hashlib.sha256(line.encode('utf-8', 'surrogateescape')).hexdigest() != old:
        bad.append(f'{f}:{n}')
        continue
    plan.append((f, n, new))
if bad:
    sys.exit('apply_residual: refused, lines differ from the rows: ' + ', '.join(bad))
for f, n, new in plan:
    files[f][n - 1] = new
for f in {p[0] for p in plan}:
    open(f'{proofs}/{f}', 'wb').write('\n'.join(files[f]).encode('utf-8', 'surrogateescape'))
print(f'apply_residual: {len(plan)} line(s) rewritten, {len(rows) - len(plan)} already as the rows say')
