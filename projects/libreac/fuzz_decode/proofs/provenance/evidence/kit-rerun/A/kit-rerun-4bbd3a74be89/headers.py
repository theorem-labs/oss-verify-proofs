#!/usr/bin/env python3
"""headers.py HUB COMMIT NUMDIFF.TSV NUMERALS.TSV CALLS.TSV -- read-only.

The 47 shipped libreac/fuzz_decode .v headers at COMMIT each say `its N image addresses moved by code-verified
function pairs (M port_addr_check <sha> MAPS predictions, each code one re-derived by funcpair.py; K code pcs the
tool read as sizes, by funcpair.py)` and some add `and C pcs named in comments`. The addresses themselves are the
changed numerals of that file, listed by the relocation's own numdiff table (allocreloc/numdiff.tsv: file, src_line,
src_value, new_value, src_res): the non-comment rows are the N, the `(comment / not read)` rows the C.

This script collects every cited address of every one of the 47 headers and checks it against THIS re-run's set: a
cited address is COVERED when the relocation mapped it through one of the 7 funcpair function pairs, i.e. when
(src_value -> new_value) is a row of the re-run's numerals.tsv for that file (all 417 of which were re-checked on
cmpkit 4bbd3a74be89). Everything else is reported, with what the relocation's own resolution (src_res) calls it.
No .v file is read for editing and none is written."""
import collections, re, subprocess, sys

HUB, COMMIT, NUMDIFF, NUM, CALLS = sys.argv[1:6]


def git(*a):
    return subprocess.run(['git', '-C', HUB] + list(a), capture_output=True, text=True, check=True).stdout


files = sorted(set(l.split(':', 1)[1] for l in
                   git('grep', '-l', 're-derived by funcpair.py', COMMIT, '--',
                       'proofs/libreac/fuzz_decode').splitlines()))
print('# hub', HUB, 'commit', COMMIT)
print('# headers citing "re-derived by funcpair.py":', len(files), '; citations of funcpair.py:',
      sum(int(l.rsplit(':', 1)[1]) for l in
          git('grep', '-c', 'funcpair.py', COMMIT, '--', 'proofs/libreac/fuzz_decode').splitlines()))

cited = collections.defaultdict(list)       # file -> [(src_value, new_value, src_res)] non-comment
comment = collections.Counter()
for l in open(NUMDIFF).read().splitlines()[1:]:
    if not l.strip(): continue
    c = (l.split('\t') + [''] * 7)[:7]
    if 'comment' in c[4]: comment[c[0]] += 1
    else: cited[c[0]].append((c[2], c[3], c[4]))

mapped = collections.defaultdict(set)       # file -> {(donor, placed)} re-checked by this re-run
for l in open(NUM).read().splitlines()[1:]:
    if l.strip():
        c = l.split('\t'); mapped[c[0]].add((c[1], c[2]))
callkind = collections.defaultdict(dict)    # file -> {addr: (kind, mapped-or-raise)}
for l in open(CALLS).read().splitlines()[1:]:
    if l.strip():
        c = l.split('\t'); callkind[c[0]][c[2]] = (c[1], c[-1])

hdr_re = re.compile(r'its (\d+) image addresses moved by code-verified function pairs '
                    r'\((\d+) port_addr_check \w+ MAPS predictions, each code one re-derived by funcpair.py; '
                    r'(\d+) code pcs the tool read as sizes')
cmt_re = re.compile(r'and (\d+) pcs named in comments')
rows, count_mismatch, notin_text, uncov = [], [], [], collections.Counter()
uncov_list = []
tot = collections.Counter()
for f in files:
    txt = git('show', '%s:%s' % (COMMIT, f))
    base = f.rsplit('/', 1)[1][:-2]
    m = hdr_re.search(txt)
    if not m:
        print('NO HEADER MATCH', f); continue
    moved, maps, sizes = (int(m.group(i)) for i in (1, 2, 3))
    cm = cmt_re.search(txt); comments = int(cm.group(1)) if cm else 0
    cit = cited.get(base, [])
    if (moved, comments) != (len(cit), comment[base]):
        count_mismatch.append((base, moved, len(cit), comments, comment[base]))
    cov = [r for r in cit if (r[0], r[1]) in mapped.get(base, set())]
    unc = [r for r in cit if (r[0], r[1]) not in mapped.get(base, set())]
    for s, n, res in unc:
        r0 = res.split(';')[0]
        kind = ('DATA address, relocation resolved it as %s' % r0) if '[data]' in r0 else \
               ('CODE pc, relocation resolved it as %s' % r0[:60]) if '[code]' in r0 else \
               ('segment extent / non-address: %s' % r0)
        call = callkind.get(base, {}).get(s)
        if call and call[0] == 'code': kind += '  [a funcpair call exists for this value: %s, %s]' % call
        uncov[kind] += 1; uncov_list.append((base, s, n, kind))
    bad = sorted({n for _s, n, _r in cov if n not in txt})
    if bad: notin_text.append((f, bad))
    tot['cited'] += len(cit); tot['covered'] += len(cov); tot['uncovered'] += len(unc)
    tot['comment'] += comment[base]
    rows.append((base, moved, maps, sizes, comments, len(cit), len(cov), len(unc), len(bad)))

print('file       hdr_moved maps size_reads hdr_cmt | cited covered uncovered | placed_not_in_file')
for r in rows:
    print('%-10s %6d %6d %6d %7d | %5d %7d %9d | %4d' % r)
print()
print('TOTAL cited addresses in the 47 headers: %d; covered by this re-run: %d; not covered: %d '
      '(comment numerals, not cited as moved by function pairs: %d)'
      % (tot['cited'], tot['covered'], tot['uncovered'], tot['comment']))
print('header counts that disagree with numdiff.tsv (file, hdr_moved, numdiff_noncomment, hdr_cmt, numdiff_comment):',
      count_mismatch or 'none')
print('covered placed values missing from the committed file text:', notin_text or 'none')
print()
print('WHAT THE UNCOVERED CITED ADDRESSES ARE')
for k, n in uncov.most_common():
    print('  %4d  %s' % (n, k))
print()
print('every uncovered cited address (file, src -> new, what it is)')
for r in sorted(set(uncov_list)):
    print('  %-10s %-10s -> %-10s %s' % r)
