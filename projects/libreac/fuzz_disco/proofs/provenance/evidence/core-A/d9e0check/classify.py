#!/usr/bin/env python3
"""classify.py FILES ABFD_STAGE_OUT D9E0_STAGE_OUT TARGET_LIB OUT_TSV

Compares, file by file, the stage-out of the port_core d9e0589898fd check run with the stage-out of the port_core
abfd17f8b3d2 run of record (../memwalks13/) and with the shipped file, by sha256, and classifies every file whose
d9e0589898fd output differs from the abfd17f8b3d2 output. FILES is ../memwalks13/inputs/files13.txt (lib-relative
paths; '#' lines are comments). Both runs read the same override table and patch (../memwalks13/inputs/), so a line
those set is the unit's value, not the tool's. Each differing line is
  provenance  line 4, the provenance comment the tool writes (the shipped file holds the release's own line there);
  patched     a line the override table or the patch sets (its shipped value comes from that row or hunk);
  VALUE       any other line: the two tool versions give a different value where the shipped file has the tool's.
A file is classed by its worst line (VALUE > patched > provenance); a file with no differing line is `equal`. The last
column compares the d9e0589898fd output with the shipped file line by line (the shipped line 4 is the release's
provenance comment, so `line 4 only` is the expected result).
Writes OUT_TSV (one row per file) and prints the class counts. Exit 1 if any file is VALUE, else 0.
"""
import collections, hashlib, os, re, sys

files_list, abfd_dir, d9e0_dir, target_lib, out_tsv = sys.argv[1:6]
here = os.path.dirname(os.path.abspath(__file__))
inputs = os.path.join(here, '..', 'memwalks13', 'inputs')


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest() if os.path.exists(p) else '-'


def lines(p):
    return open(p, encoding='utf-8', errors='surrogateescape').read().split('\n') if os.path.exists(p) else []


# the lines the unit's patch and override table set, in stage-out coordinates (the overrides are applied first, the
# patch after them, so an override line moves by the lines the patch adds or removes above it)
unit = collections.defaultdict(set)
hunks = collections.defaultdict(list)  # file -> [(old start, old length, new length)]
cur, ln = None, 0
for l in open(os.path.join(inputs, 'patch-abfd17f8b3d2.diff')):
    if l.startswith('+++ '):
        cur = re.sub(r'^b/', '', l[4:].split('\t')[0].strip())
        continue
    if l.startswith('--- '):
        continue
    m = re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', l)
    if m:
        g = [int(x) if x is not None else 1 for x in m.groups()]
        hunks[cur].append((g[0], g[1], g[3]))
        ln = g[2]
    elif cur and l.startswith('+'):
        unit[cur].add(ln)  # a line the patch adds or replaces
        ln += 1
    elif cur and l.startswith(' '):
        ln += 1
for l in open(os.path.join(inputs, 'overrides-abfd17f8b3d2.tsv')):
    f = l.rstrip('\n').split('\t')
    if len(f) >= 4 and not l.startswith('#') and f[1].isdigit():
        # an override line is a donor line; the stage-out has the provenance comment inserted as line 4, and the
        # patch (written against the stage-out) then adds or removes lines above it
        n = int(f[1]) + (1 if int(f[1]) >= 4 else 0)
        unit[f[0]].add(n + sum(nl - ol for os_, ol, nl in hunks[f[0]] if os_ + ol <= n))

rank = {'equal': 0, 'provenance': 1, 'patched': 2, 'VALUE': 3}
count = collections.Counter()
rows = []
for rel in (l.strip() for l in open(files_list)):
    if not rel or rel.startswith('#'):
        continue
    a, d, s = (os.path.join(abfd_dir, rel), os.path.join(d9e0_dir, rel), os.path.join(target_lib, rel))
    ha, hd, hs = sha(a), sha(d), sha(s)
    worst, where = 'equal', []
    if ha != hd:
        la, ld = lines(a), lines(d)
        for i in range(max(len(la), len(ld))):
            x = la[i] if i < len(la) else None
            y = ld[i] if i < len(ld) else None
            if x == y:
                continue
            k = 'provenance' if i + 1 == 4 else 'patched' if i + 1 in unit[rel] else 'VALUE'
            where.append(f'{i + 1}:{k}')
            worst = max(worst, k, key=rank.get)
        if len(la) != len(ld):
            where.append(f'line-count:{len(la)}->{len(ld)}')
            worst = 'VALUE'
    count[worst] += 1
    ls_, ld_ = lines(s), lines(d)
    vs = [i + 1 for i in range(max(len(ls_), len(ld_)))
          if (ls_[i] if i < len(ls_) else None) != (ld_[i] if i < len(ld_) else None)]
    ship = 'equal' if not vs else 'line 4 only (provenance comment)' if vs == [4] else \
        'differs at ' + ' '.join(map(str, vs[:20])) + (' ...' if len(vs) > 20 else '')
    rows.append([rel, hd, ha, hs, 'equal' if ha == hd else 'differs', worst, ' '.join(where) or '-', ship])

with open(out_tsv, 'w') as fh:
    fh.write('# d9e0589898fd check run vs the abfd17f8b3d2 run of record (../memwalks13/) and the shipped file, by '
             'sha256 of each stage-out file; written by classify.py\n')
    fh.write('file\tsha256_d9e0589898fd\tsha256_abfd17f8b3d2\tsha256_shipped\td9e0_vs_abfd\tclass\tdiffering_lines'
             '\td9e0_vs_shipped\n')
    for r in rows:
        fh.write('\t'.join(r) + '\n')
    fh.write('# classes: ' + ', '.join(f'{k} {count[k]}' for k in ('equal', 'provenance', 'patched', 'VALUE')) + '\n')
print('classify: ' + ', '.join(f'{k} {count[k]}' for k in ('equal', 'provenance', 'patched', 'VALUE')) +
      f' ({len(rows)} files)')
sys.exit(1 if count['VALUE'] else 0)
