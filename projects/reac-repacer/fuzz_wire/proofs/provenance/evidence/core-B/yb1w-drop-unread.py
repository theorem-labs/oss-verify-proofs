#!/usr/bin/env python3
"""yb1w-drop-unread.py LIB TWIN TWIN_SHA256 CLASSIFIED.tsv : remove from LIB/B/YB1w.v every cell that the classifier of
record (yb1w_clause2_lockB.py, its v4 yb1w_clause2_v4.py or its v5.2 yb1w_clause2_v5.py; their table CLASSIFIED.tsv)
classes FALSE (trampoline, other, named-other) or unverifiable by symtab (an E cell whose name keys to a symbol of
st_size 0: the symtab gives no end for it), when no file reads it (the publish lead's rule of 2026-10-30 20:58Z and the
units' lead's rulings of 2026-10-31 01:34Z, 01:48Z, 01:57Z, 02:07Z, 03:00Z and 06:25Z).

Each selected row is checked again in the target's own unstripped twin (sha256 TWIN_SHA256) with a second key: the
symbols the name can name are the twin's FUNC / OBJECT symbols whose name without leading underscores, or whose demangled
name with template and call arguments dropped and the namespaces __asan __sanitizer __interception __ubsan __lsan left
out, joined by `_`, is the name (or the name without a trailing _<digits>). The value must not be the start (tfib_A_,
tfib_D_) / start + st_size (tfib_E_) of any of them; an unverifiable row must be an E cell one of whose symbols has
st_size 0 (and every E cell keyed to an st_size-0 symbol must be classed unverifiable). The label name rule (which
labels name the symbol they bound) is the classifier's own, checked by its controls on every run; this script does not
restate it.
Readers are counted three ways, outside lib/A (lib/A is the other image's module, with its own cells of the same names):
the table's count of readers of the B cell, the cell's name as a whole token in every Rocq file of LIB with comments
removed, and `git grep -o -w -F` over LIB's Rocq files; the cell's own definition is not a reader. The script refuses
unless every check passes and every count is 0; then it deletes each `Definition <cell> : Z := 0x... .` sentence (a line
left empty is removed) and prints one record row per cell. It writes no comment."""
import collections, ctypes, ctypes.util, hashlib, os, re, subprocess, sys
from elftools.elf.elffile import ELFFile

lib, twin, pin, classified = sys.argv[1:5]
if hashlib.sha256(open(twin, 'rb').read()).hexdigest() != pin:
    sys.exit('yb1w-drop-unread: twin pin mismatch')
_cxx = ctypes.CDLL(ctypes.util.find_library('stdc++') or 'libstdc++.so.6')
_dem = _cxx.__cxa_demangle
_dem.restype = ctypes.c_void_p
_dem.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.POINTER(ctypes.c_size_t), ctypes.POINTER(ctypes.c_int)]
_libc = ctypes.CDLL(ctypes.util.find_library('c'))
_libc.free.argtypes = [ctypes.c_void_p]


def demangle(s):
    st = ctypes.c_int(0)
    p = _dem(s.encode(), None, None, ctypes.byref(st))
    if st.value or not p:
        return s
    r = ctypes.string_at(p).decode()
    _libc.free(p)
    return r


DROP = {'__asan', '__sanitizer', '__interception', '__ubsan', '__lsan'}


def norm(raw):
    d = demangle(raw).replace('(anonymous namespace)::', '')
    out, depth = [], 0
    for ch in d:
        if ch == '<':
            depth += 1
        elif ch == '>':
            depth -= 1
        elif depth == 0:
            out.append(ch)
    d = ''.join(out).split('(')[0].strip().split(' ')[-1]
    return '_'.join(p for p in d.split('::') if p and p not in DROP).lstrip('_')


by = collections.defaultdict(set)
for s in ELFFile(open(twin, 'rb')).get_section_by_name('.symtab').iter_symbols():
    if s.name and s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT'):
        for k in {s.name.lstrip('_'), norm(s.name)}:
            if k:
                by[k].add((s.name, s['st_value'], s['st_size']))


def strip_comments(t):
    out, i, depth, n = [], 0, 0, len(t)
    while i < n:
        if t.startswith('(*', i):
            depth += 1; i += 2; continue
        if depth and t.startswith('*)', i):
            depth -= 1; i += 2; continue
        if depth == 0:
            out.append(t[i])
        i += 1
    return ''.join(out)


UNVER = 'unverifiable by symtab (st_size 0), unread'
lines = open(classified).read().split('\n')
hdr = lines[0].split('\t')
col = {k: i for i, k in enumerate(hdr)}
KEYS = 'symbol(s) the name keys to [start,end)'
rows = []
for l in lines[1:]:
    if not l.strip():
        continue
    r = l.split('\t')
    cell, val, side, cls, keys = r[0], r[1], r[2], r[col['class']], r[col[KEYS]]
    zero = side == 'E' and any(a == b for a, b in re.findall(r'\[(0x[0-9a-f]+),(0x[0-9a-f]+)\)', keys))
    if zero != cls.startswith('unverifiable'):
        sys.exit(f'yb1w-drop-unread: {cell}: the table classes it {cls}, but E cell keyed to an st_size-0 symbol = {zero}')
    if zero:
        rows.append((cell, val, side, UNVER, r))
    elif cls.startswith('FALSE'):
        rows.append((cell, val, side, cls.split(' / ')[0], r))
yb = os.path.join(lib, 'B', 'YB1w.v')
t = open(yb).read()
cells = [x[0] for x in rows]
code = {}
for dp, _, fs in os.walk(lib):
    if os.path.relpath(dp, lib).split(os.sep)[0] == 'A':
        continue
    for f in fs:
        if f.endswith('.v'):
            raw = open(os.path.join(dp, f)).read()
            if any(n in raw for n in cells):          # only a file that holds a name at all can read it
                code[os.path.join(dp, f)] = strip_comments(raw)
gg = subprocess.run(['git', 'grep', '-o', '-h', '-w', '-F'] + [a for n in cells for a in ('-e', n)] +
                    ['--', '*.v', ':(exclude)A/**'], cwd=lib, capture_output=True, text=True)
if gg.returncode not in (0, 1):
    sys.exit(f'yb1w-drop-unread: git grep failed: {gg.stderr.strip()}')
grep_hits = collections.Counter(gg.stdout.split())
out = []
for cell, val, side, cls, r in rows:
    m = re.search(r'Definition %s : Z := (0x[0-9a-f]+)\.' % re.escape(cell), t)
    if not m or int(m.group(1), 16) != int(val, 0):
        sys.exit(f'yb1w-drop-unread: {cell} is not defined as {val} in {yb}')
    v, x = int(val, 0), cell[7:]
    cand = by.get(x) or by.get(re.sub(r'_\d+$', '', x)) or set()
    start = side in ('A', 'D') or cell.startswith(('tfib_A_', 'tfib_D_'))
    if any((s0 if start else s0 + sz) == v for _, s0, sz in cand):
        sys.exit(f'yb1w-drop-unread: {cell} = {val} is the {"start" if start else "end"} of a symbol it names '
                 f'(second key): not {cls}')
    if cls == UNVER and not any(sz == 0 for _, _, sz in cand):
        sys.exit(f'yb1w-drop-unread: {cell} is classed {cls}, but no symbol it names (second key) has st_size 0')
    pat = re.compile(r'(?<![\w\'])%s(?![\w\'])' % re.escape(cell))
    n0 = int(r[col["readers of this table's cell"]])
    n1 = sum(len(pat.findall(c)) - (p == yb) for p, c in code.items())
    n2 = grep_hits[cell] - 1
    if n0 or n1 or n2:
        sys.exit(f'yb1w-drop-unread: {cell} has readers (table {n0}, token {n1}, git grep {n2}): STOP')
    out.append((cell, val, cls, r[col['what the value is (twin)']], r[col[KEYS]]))
gone = [re.compile(r'Definition %s : Z := 0x[0-9a-f]+\.[ \t]*' % re.escape(o[0])) for o in out]
new_lines = []
for line in t.split('\n'):
    new = line
    for g in gone:
        new = g.sub('', new)
    if new != line and new.strip() == '':
        continue
    new_lines.append(new.rstrip() if new != line else line)
open(yb, 'w').write('\n'.join(new_lines))
print('# cell\tvalue\tclass\twhat the value is (the target twin)\tsymbol(s) the name keys to [start,end)\t'
      'readers (table, token scan, git grep -w)')
for o in out:
    print('\t'.join(o) + '\t0, 0, 0')
print(f'# yb1w-drop-unread: {len(out)} cell(s) removed: ' +
      ', '.join(f'{k} {n}' for k, n in sorted(collections.Counter(o[2] for o in out).items())))
