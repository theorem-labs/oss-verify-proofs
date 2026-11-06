#!/usr/bin/env python3
"""tfibtable-A.py TWIN DONOR_TWIN UNIT DONOR_LIB > tfib-whole-table.tsv: every `Definition tfib_(A|D|E)_<name> : Z :=
<numeral>.` in UNIT/lib/A and UNIT/lib/Reusable, read against the image's unstripped twin TWIN (C++ names demangled with
the C++ runtime's __cxa_demangle). Image B's tfibtable-B.py (sha256 1f1eb92bf82a; internal record) with
lib/B -> lib/A and the HAND column added; the rule is unchanged.

THE SYMBOL AT A VALUE. _A and _D: the symbols starting at it. _E: the symbols whose st_value + st_size is the value,
else the symbols starting at it (a size-0 assembly routine ends where the next one starts). Mapping symbols ($x, $d)
and .L labels are skipped.

CLASSES (in this order).
  OK-EXACT   the name is that symbol's name in the donor's naming: its C++ name with namespaces dropped and `::` -> `_`
             (any number of trailing components; templates and parameters dropped; a class XNoCtor also as X), its
             raw name without leading `_` (and __sanitizer_<x> as <x>), with the donor's `musl_` prefix for libc, or
             one of these plus a descriptive `_...` tail; an _E whose _A partner is a size-0 symbol and whose value is
             the next symbol's start; a _D `GOT_<x>` whose GOT word holds the address of <x>; a _D `REAL_<x>` at
             __interception::real_<x>; a _D at an object whose name is one of the `_`-separated words of the cell's.
  OK-ALIAS   the symbol is an alias of the named function: `__interceptor_trampoline_<x>` / `__wrap_<x>` for <x>
             (or <x>_thunk), `__interceptor_<x>` for icpt_<x>[_...], `__libc_<x>` / `__malloc_<x>` for <x>; or a _D
             at (or a GOT slot holding) the object an accessor returns (common_flags(), __asan::flags()).
  WRONG      the name spells a function that is elsewhere in the image, and no symbol at the value has that name:
             (a) the whole name (or it without `musl_`) is a key of a function symbol at another address; (b) the name
             is <x> with no libc <x> in the image while <x>'s ASan aliases are elsewhere; (c) SWAP: two cells whose
             names' heads (their longest `_`-prefix that is a function's key) spell each other's function; (d) ROTATED,
             the integration owner's decision of 2026-10-31: the neighbouring cells listed in ROTATED, whose labels each name the
             function one place away (by the head, or by the whole name of a function with no symbol) and not the one
             at the cell's value.
  OK-REGION  a region bracket of the donor's documented convention (records/gate-205a90-TRIAGE.md, DS-AB1W-LABEL): the
             _A / _E pair spans the named function AND the next one, so the _E value ends that next function. The two
             pairs of REGION below, each measured. Kept by the integration owner's instruction of 2026-10-31 08:40Z;
             the function-label tests (WRONG, FALSE) do not apply to a bracket cell.
  FALSE      the integration owner's decision of 2026-10-31 11:55Z: the label is spelled as a FUNCTION (a C / C++
             function name, Class_Method, ns_Func), the image has NO symbol of that name at the cell's value (every
             symbol, local and global, demangled), and the value starts (_A) / ends (_E) a DIFFERENT function. Thunk
             labels (thunk_<hex>) and plain descriptions (_helper, _stub_ret, _3_insns, _or_ ...) claim no symbol and
             stay. The FALSE SCREEN below lists every pair whose label names no symbol at its value; the hand rows
             (test FALSE) name the pairs of that list whose label is spelled as a function.
  NO-SYMBOL  anything else: a descriptive label (thunk_<donor address>, stubs, composite names). The note says when the
             label's head spells a function elsewhere.
An _E cell whose value ends the same function as its _A partner's start takes the _A partner's class.

DONOR PAIRING. The same cell in DONOR_LIB/A (the donor's text: the run's WORK/stage) and the symbol at its value in
DONOR_TWIN: `same` when that symbol has a name in common with the target's, else `differs`; `absent` when the donor has
no such cell. A WRONG cell whose donor pairing is `same` is the donor's (inherited) mislabel.

READERS. `git grep -now 'tfib_[ADE]_<word>'` over UNIT/lib: every hit of the cell's name except a Definition of that
name (its own, and an image-B cell of the same name in lib/B). `readers outside lib/B` leaves out lib/B, whose files
read image B's cells.

HAND ROWS (HANDROWS, default tfib-hand-rows.tsv beside this script). The whole-table hand read (the image-A core's writer, row TCA,
2026-10-31) names there every cell pair whose label names a function other than the one at its value and which the
rule above does not catch, with the owner's test (T1 / T2 -> WRONG, FALSE -> FALSE), the function the label names and
where that function really is; the note says which test fired. Every other cell's class is the rule's.

FALSE SCREEN (stderr). Every _A cell not WRONG whose label is no name of a symbol at its value (the whole label, or it
without musl_ / asan_ / sanitizer_ / lsan_ / ubsan_) and has no `_`-aligned part of 3 or more characters that is a name
of a symbol at its value; a symbol's names include the alias forms OK-ALIAS reads (<f> for __interceptor_trampoline_<f>,
__wrap_<f>, __libc_<f>, __malloc_<f>; icpt_<f> for __interceptor_<f>). These are the pairs the FALSE test must read by
hand. Each line gives the class the table gives it."""
import collections, ctypes, hashlib, os, re, struct, subprocess, sys
from elftools.elf.elffile import ELFFile

twin, dtwin, unit, dlib = sys.argv[1:5]

_lib = ctypes.CDLL('libstdc++.so.6')
_dm = _lib.__cxa_demangle
_dm.restype = ctypes.c_void_p
_dm.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.POINTER(ctypes.c_size_t), ctypes.POINTER(ctypes.c_int)]
_free = ctypes.CDLL('libc.so.6').free
_free.argtypes = [ctypes.c_void_p]


def demangle(n):
    if not n.startswith('_Z'):
        return n
    st = ctypes.c_int(0)
    p = _dm(n.encode(), None, None, ctypes.byref(st))
    if not p or st.value:
        return n
    s = ctypes.string_at(p).decode()
    _free(p)
    return s


class Image:
    def __init__(self, path):
        data = open(path, 'rb').read()
        e = ELFFile(open(path, 'rb'))
        self.segs = [(s['p_vaddr'], s['p_filesz'], s['p_offset']) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
        self.data = data
        self.syms, self.start, self.end = [], collections.defaultdict(list), collections.defaultdict(list)
        for s in e.get_section_by_name('.symtab').iter_symbols():
            t = s['st_info']['type']
            if not s.name or s.name in ('$x', '$d') or s.name.startswith('.L') or t in ('STT_SECTION', 'STT_FILE'):
                continue
            if s['st_shndx'] in ('SHN_UNDEF', 0):
                continue
            d = dict(name=s.name, dem=demangle(s.name), value=s['st_value'], size=s['st_size'], type=t)
            self.syms.append(d)
            self.start[d['value']].append(d)
            if d['size']:
                self.end[d['value'] + d['size']].append(d)

    def word(self, a):
        for v, fs, off in self.segs:
            if v <= a and a + 8 <= v + fs:
                return struct.unpack('<Q', self.data[off + a - v:off + a - v + 8])[0]
        return None

    def at(self, kind, v):
        if kind in 'AD':
            return self.start.get(v, []), 'start'
        e = [s for s in self.end.get(v, []) if s['type'] == 'STT_FUNC'] or self.end.get(v, [])
        return (e, 'end') if e else (self.start.get(v, []), 'next-start')


def strip_tmpl(s):
    out, depth = [], 0
    for ch in s:
        depth += ch == '<'
        if depth == 0 and ch != '>':
            out.append(ch)
        depth -= ch == '>' and depth > 0
    return ''.join(out)


def base(sym):
    b = strip_tmpl(sym['dem']).replace('(anonymous namespace)', 'ANON')
    b = b.split('(')[0].strip()
    return b.split(' ')[-1]


def keys(sym):
    parts = [p for p in base(sym).split('::') if p]
    nons = [p for p in parts if not p.startswith('__') and not p.startswith('ANON')]
    ks = set()
    for seq in (parts, nons, [p[:-len('NoCtor')] if p.endswith('NoCtor') else p for p in nons]):
        for k in range(1, len(seq) + 1):
            ks.add('_'.join(seq[-k:]))
    raw = [sym['name']] + ([sym['name'][len('__sanitizer_'):]] if sym['name'].startswith('__sanitizer_') else [])
    for k in list(ks) + raw:
        for v in (k, re.sub(r'\W', '_', k)):
            ks.add(v)
            ks.add(v.lstrip('_'))
    return {k for k in ks if k}


# the object an accessor function returns (common_flags(), flags())
ACCESSOR = {'common_flags': '__sanitizer::common_flags_dont_use', 'flags': '__asan::asan_flags_dont_use_directly'}


def label(ss):
    return ' | '.join(sorted({base(s).replace('ANON', '(anonymous namespace)') + ('' if s['type'] == 'STT_FUNC' else ' [%s]' % s['type'][4:].lower()) for s in ss})) or '-'


T, D = Image(twin), Image(dtwin)
FN = collections.defaultdict(list)
for s in T.syms:
    if s['type'] == 'STT_FUNC':
        for k in keys(s):
            FN[k].append(s)

DEF = re.compile(r'\bDefinition\s+(tfib_([ADE])_(\w+))\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+|\d+)\s*\.')


def cells(root, subs):
    out = []
    for sub in subs:
        for dp, _, fs in os.walk(os.path.join(root, sub)):
            for fn in sorted(fs):
                if fn.endswith('.v'):
                    p = os.path.join(dp, fn)
                    for ln, line in enumerate(open(p, errors='replace'), 1):
                        for m in DEF.finditer(line):
                            out.append(dict(cell=m.group(1), kind=m.group(2), name=m.group(3), val=int(m.group(4), 0),
                                            file=os.path.relpath(p, root), line=ln))
    return out


lib = os.path.join(unit, 'lib')
C = cells(lib, ['A', 'Reusable'])
DC = {c['cell']: c for c in cells(dlib, ['A', 'Reusable'])}


def head(n):
    """the longest `_`-prefix of n (or of n without musl_ / icpt_) that is a function's key: (prefix, symbols)"""
    best = None
    for c in [n] + [n[len(p):] for p in ('musl_', 'icpt_') if n.startswith(p)]:
        toks = c.split('_')
        for k in range(len(toks), 0, -1):
            p = '_'.join(toks[:k])
            if len(p) >= 3 and p in FN:
                if best is None or len(p) > len(best[0]):
                    best = (p, FN[p])
                break
    return best


def classify(c, ss):
    n, kind = c['name'], c['kind']
    if kind == 'D':
        if n.startswith('GOT_'):
            w = T.word(c['val'])
            for s in T.start.get(w, []) if w is not None else []:
                if n[4:] in keys(s):
                    return 'OK-EXACT', 'GOT slot holding &%s' % label([s])
                if ACCESSOR.get(n[4:]) == s['dem']:
                    return 'OK-ALIAS', 'GOT slot holding &%s, the object %s() returns' % (label([s]), n[4:])
        if n.startswith('REAL_') and any(s['dem'] == '__interception::real_' + n[5:] for s in ss):
            return 'OK-EXACT', 'REAL(%s)' % n[5:]
        if n == 'asan_flags_Flags_struct_flags' and any(s['dem'] == ACCESSOR['flags'] for s in ss):
            return 'OK-ALIAS', 'the Flags object __asan::flags() returns'
        for s in ss:
            if s['type'] == 'STT_OBJECT' and re.search(r'(^|_)%s(_|$)' % re.escape(base(s).split('::')[-1]), n):
                return 'OK-EXACT', 'name contains the object name ' + label([s])
    for s in ss:
        ks = keys(s)
        if n in ks or (n.startswith('musl_') and n[5:] in ks):
            return 'OK-EXACT', 'name = ' + label([s])
    for s in ss:
        nm = s['name']
        m = re.match(r'^(?:__interceptor_trampoline_|__wrap_)(.+)$', nm)
        if m and n in (m.group(1), m.group(1).lstrip('_'), m.group(1).lstrip('_') + '_thunk'):
            return 'OK-ALIAS', 'interceptor trampoline / __wrap_ of ' + m.group(1)
        m = re.match(r'^_{2,3}interceptor_(.+)$', nm)
        if m and (n == 'icpt_' + m.group(1).lstrip('_') or n.startswith('icpt_' + m.group(1).lstrip('_') + '_')):
            return 'OK-ALIAS', 'interceptor of ' + m.group(1)
        for pre in ('__libc_', '__malloc_'):
            if nm.startswith(pre) and n == nm[len(pre):]:
                return 'OK-ALIAS', 'libc-internal name %s of %s' % (nm, n)
    for s in ss:
        for k in keys(s):
            if len(k) >= 3 and (n.startswith(k + '_') or (n.startswith('musl_') and n[5:].startswith(k + '_'))):
                return 'OK-EXACT', 'name = %s + descriptive tail' % label([s])
    if kind == 'D':
        w = T.word(c['val'])
        content = ''
        if w is not None:
            txt = struct.pack('<Q', w).split(b'\0')[0]
            content = 'word 0x%016x%s' % (w, (' -> ' + label(T.start[w])) if T.start.get(w) else '')
            if txt and all(32 <= b < 127 for b in txt):
                content += ' (bytes "%s")' % txt.decode()
        return 'NO-SYMBOL', 'data label; ' + (content or 'no file bytes (.bss)')
    here = {s['value'] for s in ss}
    for x in (n, n[5:] if n.startswith('musl_') else None):
        if x and x in FN and not here & {s['value'] for s in FN[x]}:
            return 'WRONG', 'the name spells %s, which is elsewhere' % '; '.join(
                sorted({'%s at %#x' % (label([s]), s['value']) for s in FN[x]}))
    if n not in FN and ss and not any(s['name'] == n for s in T.syms) and all('::' not in s['dem'] for s in ss):
        alias = [s for s in T.syms if s['type'] == 'STT_FUNC' and
                 re.fullmatch(r'(_{2,3}interceptor_(trampoline_)?|__wrap_)' + re.escape(n), s['name'])]
        if alias and not here & {s['value'] for s in alias}:
            return 'WRONG', 'no libc %s in the image; its ASan aliases are elsewhere: %s' % (
                n, '; '.join(sorted('%s at %#x' % (s['name'], s['value']) for s in alias)))
    h = head(n)
    if h and not here & {s['value'] for s in h[1]}:
        return 'NO-SYMBOL', 'label; its head %s spells %s' % (h[0], '; '.join(
            sorted({'%s at %#x' % (label([s]), s['value']) for s in h[1]})))
    return 'NO-SYMBOL', 'label'


rows = []
for c in C:
    ss, how = T.at(c['kind'], c['val'])
    cls, note = classify(c, ss)
    d = DC.get(c['cell'])
    if d:
        dss, _ = D.at(d['kind'], d['val'])
        same = bool({s['name'] for s in ss} & {s['name'] for s in dss}) or (not ss and not dss)
        dp = '%#x %s (%s)' % (d['val'], label(dss), 'same' if same else 'differs')
    else:
        dp = 'absent'
    rows.append(dict(c, ss=ss, how=how, cls=cls, note=note, donor=dp))

by = collections.defaultdict(dict)
for r in rows:
    by[r['name']][r['kind']] = r
for n, d in by.items():
    a, e = d.get('A'), d.get('E')
    if not (a and e):
        continue
    if e['how'] == 'end' and a['val'] in {s['value'] for s in e['ss']}:
        e['cls'], e['note'] = a['cls'], 'ends the function of tfib_A_%s' % n
    elif e['how'] == 'next-start' and a['ss'] and all(s['size'] == 0 for s in a['ss']):
        e['cls'], e['note'] = 'OK-EXACT', 'tfib_A_%s is the size-0 %s; this is the next symbol\'s start' % (n, label(a['ss']))
# (c) SWAP: two A cells whose heads spell each other's function
A = {r['name']: r for r in rows if r['kind'] == 'A' and r['cls'] == 'NO-SYMBOL'}
for n, r in A.items():
    h = head(n)
    if not h:
        continue
    for m, q in A.items():
        if m == n:
            continue
        hq = head(m)
        if hq and q['val'] in {s['value'] for s in h[1]} and r['val'] in {s['value'] for s in hq[1]}:
            for k in 'AE':
                x = by[n].get(k)
                if x:
                    x['cls'] = 'WRONG'
                    x['note'] = 'SWAP with tfib_%s_%s: its head %s spells %s, the function at tfib_A_%s' % (
                        k, m, h[0], label(h[1]), m)
# (d) ROTATED (the integration owner's decision of 2026-10-31): neighbouring labels shifted one function off their values
ROTATED = [('QuarantineCache_MergeBatches_Transfer', 'QuarantineCache_DequeueBatch'),
           ('StackDepotBase_find_bucket_chain_walk', 'StackDepotBase_lock_bucket_spin_lock')]
for pair in ROTATED:
    for n in pair:
        if 'A' not in by.get(n, {}):
            continue
        m = pair[1 - pair.index(n)]
        h = head(n)
        says = ('its head %s spells %s' % (h[0], '; '.join(sorted({'%s at %#x' % (label([s]), s['value']) for s in h[1]})))
                if h else 'its name spells %s, a function with no symbol in the image' % n)
        part = by.get(m, {}).get('A')
        for k in 'AE':
            x = by[n].get(k)
            if x:
                x['cls'] = 'WRONG'
                x['note'] = 'ROTATED with tfib_A_%s%s: %s; this cell is on %s' % (
                    m, ' (on %s)' % label(part['ss']) if part else '', says, label(by[n]['A']['ss']))

# (e) the hand read's rows (HANDROWS, default beside this script): the owner's test, applied per cell (2026-10-31).
# A cell is WRONG when its label NAMES a function the twin has at another address (T1) or names a different function
# from the one at its value (T2: the named one is inlined, so it has no symbol). Each row gives the test, the function
# the label names and where that function really is; the file's own header states the test.
HANDROWS = os.environ.get('HANDROWS') or os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tfib-hand-rows.tsv')
for line in open(HANDROWS):
    if line.startswith('#') or not line.strip():
        continue
    nm, test, named, where = line.rstrip('\n').split('\t')
    for k in 'AE':
        x = by.get(nm, {}).get(k)
        if x:
            x['cls'] = 'FALSE' if test == 'FALSE' else 'WRONG'
            if test == 'FALSE':
                x['note'] = 'FALSE: the label is spelled as the function %s (%s); this cell is on %s, a different function' % (
                    named, where, label(x['ss']))
            else:
                x['note'] = '%s: the label names %s, which is %s; this cell is on %s' % (test, named, where, label(x['ss']))

# REGION: the pairs whose _E value ends the function AFTER the named one (the donor's bracket convention), measured.
# The integration owner's instruction of 2026-10-31 08:40Z keeps such bracket pairs with a comment; the function-label
# tests (WRONG, FALSE) do not apply to a bracket cell, whose _E value ends the next function by that convention.
REGION = {'start': 'the pair [tfib_A_start, tfib_E_start) covers _start (an asm symbol of size 0) and _start_c',
          'target_run': 'the pair [tfib_A_target_run, tfib_E_target_run) covers target_run and oft_exit_guard '
                        '(records/gate-205a90-TRIAGE.md, DS-AB1W-LABEL)'}
for nm, why in REGION.items():
    x = by.get(nm, {}).get('E')
    if x:
        x['cls'] = 'OK-REGION'
        x['note'] = ('region bracket: %s; this value ends %s. A bracket cell: the function-label tests (WRONG, FALSE) '
                     'do not apply' % (why, label(x['ss'])))

# FALSE SCREEN: the pairs whose label names no symbol at its value (see FALSE SCREEN above), to stderr
screen = []
for n, d in by.items():
    a = d.get('A')
    if not a or a['cls'] == 'WRONG':
        continue
    ks = set().union(*[keys(s) for s in a['ss']]) if a['ss'] else set()
    for s in a['ss']:   # the alias forms OK-ALIAS reads: the function a wrapper / interceptor / libc-internal name is of
        m = re.match(r'^(?:__interceptor_trampoline_|__wrap_|__libc_|__malloc_)(.+)$', s['name'])
        if m:
            ks |= {m.group(1), m.group(1).lstrip('_')}
        m = re.match(r'^_{2,3}interceptor_(.+)$', s['name'])
        if m:
            ks.add('icpt_' + m.group(1).lstrip('_'))
    whole = {n} | {n[len(p):] for p in ('musl_', 'asan_', 'sanitizer_', 'lsan_', 'ubsan_') if n.startswith(p)}
    toks = n.split('_')
    part = {'_'.join(toks[i:j]) for i in range(len(toks)) for j in range(i + 1, len(toks) + 1)}
    if whole & ks or any(len(p) >= 3 and p in ks for p in part):
        continue
    screen.append('false screen: tfib_A_%s %#x on %s: %s' % (n, a['val'], label(a['ss']), a['cls']))
sys.stderr.write('false screen: %d pairs whose label names no symbol at its value\n' % len(screen))
sys.stderr.write(''.join(s + '\n' for s in screen))

# readers
out = subprocess.run(['git', 'grep', '-now', r'tfib_[ADE]_[A-Za-z0-9_]*', '--', os.path.relpath(lib, unit)],
                     cwd=unit, capture_output=True, text=True, check=True).stdout
hits = collections.defaultdict(list)
for line in out.splitlines():
    f, ln, tok = line.split(':', 2)
    hits[tok].append((f, int(ln)))
defs = {(os.path.join('lib', c['file']), c['line'], c['cell']) for c in cells(lib, [''])}
for r in rows:
    rd = [(f, ln) for f, ln in hits.get(r['cell'], []) if (f, ln, r['cell']) not in defs]
    rd.sort(key=lambda x: (x[0].startswith('lib/B/'), x))
    r['readers'] = len(rd)
    r['readersB'] = sum(not f.startswith('lib/B/') for f, _ in rd)
    r['where'] = ','.join('%s:%d' % x for x in rd[:6]) + (',...' if len(rd) > 6 else '')

sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
# the lib by content: the sha256 of each file that holds a cell (no commit: the tree may be unreleased)
cellfiles = ', '.join('lib/%s %s' % (f, sha(os.path.join(lib, f))[:12]) for f in sorted({r['file'] for r in rows}))
cnt = collections.Counter(r['cls'] for r in rows)
print('# twin sha256 %s; donor twin sha256 %s; cell files %s; cells %d: %s' % (
    sha(twin), sha(dtwin), cellfiles, len(rows), ', '.join('%s %d' % kv for kv in sorted(cnt.items()))))
print('\t'.join(['cell', 'file:line', 'value', 'symbol at value', 'how', 'class', 'note', 'donor pairing (value, symbol)',
                 'readers', 'readers outside lib/B', 'reading lines']))
for r in rows:
    print('\t'.join([r['cell'], 'lib/%s:%d' % (r['file'], r['line']), '%#x' % r['val'], label(r['ss']), r['how'], r['cls'],
                     r['note'], r['donor'], str(r['readers']), str(r['readersB']), r['where']]))
sys.stderr.write('cells %d  %s\n' % (len(rows), '  '.join('%s %d' % kv for kv in sorted(cnt.items()))))
