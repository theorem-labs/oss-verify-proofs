#!/usr/bin/env python3
"""Role of every MISMATCH / MIXED / NO-COUNTERPART row of the v2 rc-*.tsv, read from the ported line (comments
stripped).

Each row gets the first role whose pattern matches the text immediately around the value (the 60 characters before
it and 20 after). A row that also matches GEO (an image-geometry word next to the value), or matches no role, or is
an image-derived SMALL quantity, is listed for reading by hand.
  TABLE     a table length, an entry count, a padding or a slice bound: `<name>_len|_cnt|_count|_size|_bytes|_pad|
            _padding|_entries|_tab|_table|_words|_n := N`, `seg <list> i n`, `length <tab> = N`, `firstn/skipn N`.
            v2 selects these: below v1's 0x100 floor a kept donor table length is exactly the kept-length defect found
            earlier in this series (src0_debruijn_len 33 where the unit's own table is 32), so these rows are never waved through.
  INSN      an instruction offset / word / decoded immediate: fetch_word / decode_any / Branch / Lui / `+ 0x.. ) ) = Some`
  OFFSET    an offset from a run-time base: `<name> + N`, `<name> - N`, `- N` stack slots, SOff k N, a_off := N,
            mkRegion / mkChunk / (Some k, lo, hi) frame offsets of a region relative to its base
  RUNTIME   a run-time size / count / bound: mmap lengths (w64 / SLit / ELit / KZ / kn_zero / grant_md / page_round_up_Z),
            mkAF field sizes, `n <= N` / `N%nat` counts, loop counts, `2 ^ k` rewrites, escale / PGcKeep page counts
  GEO       an image-geometry word within the window: seg / img / IMG / rw / ro_ / _len / extent / top / PT_LOAD /
            mkSeg / tfib_.._lo|hi / src0_.._lo|hi / segs_ / rodata / text_lo|hi / bss / data_lo
Every row below 0x100 (the quantities v1's floor hid) is listed for reading whatever its role: at that size the
role words alone do not settle whether the numeral is the image's.
usage: roles.py [rc-PREFIX ...] > roles.out      (default: every prefix in ROOT)"""
import collections, os, re, subprocess, sys

# Edited for plugin-hostd/fuzz_command (tree a3c671fb9bb, the series head the value gate read). The only other
# change against roles.py 3bae7181ab01: the git directory comes from $ROLES_GIT (default: the current repository).
U = 'proofs/plugin-hostd/fuzz_command/lib/'
ROOT = {'rc-A': (U + 'A/', 'a3c671fb9bb'), 'mv-A': (U + 'A/', 'a3c671fb9bb'),
        'rc-B': (U + 'B/', 'a3c671fb9bb'), 'mv-B': (U + 'B/', 'a3c671fb9bb'),
        'rc-U': (U + 'Reusable/', 'a3c671fb9bb'), 'mv-U': (U + 'Reusable/', 'a3c671fb9bb')}
GIT = os.environ.get('ROLES_GIT', '.')
SMALL = 0x100
GEO = re.compile(r'\b(seg|segs?_\w*|img\w*|IMG\w*|\w*_rw\w*|rw_\w*|ro_\w*|\w+_len|extent|\w*top\w*|PT_LOAD\w*|mkSeg|'
                 r'tfib_\w+_(lo|hi)|src0_\w+_(lo|hi)|rodata\w*|text_(lo|hi)|bss\w*|data_(lo|hi))\b')
ROLES = [
    ('TABLE', re.compile(r'\b\w*(_len|_cnt|_count|_size|_sz|_bytes|_pad|_padding|_entries|_entry|_tab|_table|_words|'
                         r'_nwords|_nelem|_rows|_cols|_slots|_classes)\b\s*(:?=|:=)?\s*$|'
                         r'\bseg\s+\w+\s+\d*\s*$|\b(firstn|skipn|nth|length|Z\.of_nat\s*\(?length)\s+\S*\s*$|'
                         r'\bdebruijn\w*\s*\S*\s*$|\bsize_classes\b\S*\s*$')),
    ('INSN', re.compile(r'fetch_word|decode_any|Branch|\bLui\b|\bJal\b|\bAuipc\b|\bPW\b|\+ 0x[0-9a-f]+\)\) = Some|ss_pc|'
                        r'Z_to_bv 64 \(src0_A_\w+ \+|Z_to_bv 64 \(tfib_A_\w+ \+|build_table')),
    ('OFFSET', re.compile(r'[A-Za-z_][\w\']*\s*[+-]\s*$|\(-?\s*$|SOff\s+\S+\s+\(?-?\s*$|a_off := -?\s*$|mkRegion\b|mkChunk\b|'
                          r'\(Some \d+%nat,\s*-?\s*$|\(None,\s*[^,]*$|, -?\s*$|\bsp0\b|- $')),
    ('RUNTIME', re.compile(r'w64\s*$|SLit\s*$|ELit\s*$|\bKZ\b|kn_zero|grant_md|page_round_up_Z|mkAF|<=\s*$|<\s*$|'
                           r'span_loop|\^\s*\d+\)? with\s*$|with\s*$|escale|PGcKeep|campaign|gen\b|gen_ans|nd_hi|=>\s*$|'
                           r':=\s*$|=\s*$|mod\s*$|\*\s*$|\(\s*$|\[\s*$|;\s*$|exists|replace|change|zlen|length')),
]
_c = {}


def text(sha, path):
    if (sha, path) not in _c:
        t = subprocess.run(['git', '-C', GIT, 'show', f'{sha}:{path}'], capture_output=True,
                           text=True).stdout
        out, depth, i = [], 0, 0
        while i < len(t):                       # strip (nested) comments, keep newlines
            if t.startswith('(*', i):
                depth, i = depth + 1, i + 2
                continue
            if t.startswith('*)', i) and depth:
                depth, i = depth - 1, i + 2
                continue
            if not depth or t[i] == '\n':
                out.append(t[i])
            i += 1
        _c[(sha, path)] = ''.join(out).split('\n')
    return _c[(sha, path)]


res = collections.Counter()
manual = []
for pre in (sys.argv[1:] or ROOT):
    root, sha = ROOT[pre]
    for r in [l.rstrip('\n').split('\t') for l in open(f'{pre}.tsv')][1:]:
        if r[0] == 'SAME':
            continue
        v = int(r[8], 16)
        f, ln = r[3].rsplit(':', 1)
        L = text(sha, root + f)
        t = L[int(ln) - 1] if int(ln) <= len(L) else ''
        m = None
        for p in (hex(v), str(v)):
            m = re.search(r'(?<![\w.])' + re.escape(p) + r'(?![\w])', t, re.I)
            if m:
                break
        before = t[max(0, m.start() - 60):m.start()] if m else t[:60]
        after = t[m.end():m.end() + 20] if m else ''
        win = before + '@' + after
        role = next((n for n, p in ROLES if p.search(before[-40:]) or (n == 'INSN' and p.search(t))), 'UNCLASSED')
        geo = bool(GEO.search(before[-30:] + after))
        small = v < SMALL
        res[(pre, r[0], r[9], role + ('+GEO' if geo else ''))] += 1
        if geo or small or role in ('UNCLASSED', 'TABLE'):
            manual.append((pre, r[0], role, r[9], r[3], r[8], win.strip()[:120]))
for k, n in sorted(res.items()):
    print('\t'.join(k), n)
print(f'# rows to read by hand (TABLE, GEO, UNCLASSED or value < {SMALL:#x}): {len(manual)}')
for x in manual:
    print('\t'.join(x))
