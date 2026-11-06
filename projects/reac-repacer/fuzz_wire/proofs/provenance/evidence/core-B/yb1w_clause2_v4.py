#!/usr/bin/env python3
"""yb1w_clause2_lockB.py [options] -- clause 2 of the AB1w / YB1w DIFFERENT-SYMBOL rule (the release reviewer's rule, 20:58Z) over EVERY named
cell (`Definition tfib_A_<X> : Z := v.` / `tfib_E_<X>`) of one start-up function table, with a class, its readers and
whether the donor already held it. Every input is an option: --table, --twin, --donor-table, --donor-twin and --repo
are required; the others default to fuzz_lock's image B (commit ef9486db1b3, donor fuzz_grant B 4f87de75d677), so an
image-A unit runs it unchanged with its own --rev / --lib / --stmt / --module / --other-module:

  --table FILE         the table to classify (a file; e.g. `git show REV:<lib>/B/YB1w.v > FILE`)
  --twin ELF           the image whose symtab judges it (an unstripped twin: released pins carry no symtab)
  --donor-table FILE   the donor's table (for `inherited`)     --donor-twin ELF   the donor image's twin
  --repo DIR --rev REV the git repository and commit whose trees are searched for readers
  --lib PATH           the unit's lib/ inside REPO               --stmt PATH ...   more trees to search (statement dirs)
  --module M           the table's module under lib (B.YB1w)    --other-module M  the other image's table (A.AB1w)
  --out TSV            one row per cell                         (the counts go to stdout)

Clause 2 (ab1w_clause2.py, sha256 7c6f10bf97a8): tfib_A_<X> / tfib_E_<X> is TRUE BY NAME iff
its value is the START (A) / END = start + st_size (E) of a symbol whose key is <X> (or <X> without a trailing
_<digits>) in the twin's own symtab (FUNC / OBJECT symbols). The column `clause-2 verdict (ab1w_clause2.py key)` is
that script's key: the length-prefixed name components before the first template argument or internal-linkage `L`
(_ZN6__asanL16AsanInitInternalEv keys to ''), the __asan / __sanitizer / __lsan / __ubsan / __interception namespaces
dropped. The classes use the same rule on the key from the FULL demangled name (libstdc++'s __cxa_demangle through
ctypes; template arguments and every parenthesised group removed, a local static keeping its function, the same
namespaces dropped, the rest joined by `_`; a plain C name without its leading underscores). Classes, in this order:

  unverifiable by symtab (st_size 0)  an E cell whose named symbol has st_size 0, or whose value is bounded only by
                         size-0 symbols: the symtab gives no end to check (the integration lead's ruling, 02:02Z).
  TRUE                   clause 2 TRUE.
  thunk                  <X> is thunk_<hex>: the name is a donor address, not a symbol name.
  FALSE trampoline       clause 2 FALSE-BY-NAME and the value is the start (A) / end (E) of __interceptor_trampoline_<X>:
                         the cell names the libc function and holds its ASan interceptor trampoline.
  FALSE other            clause 2 FALSE-BY-NAME otherwise: a symbol named <X> exists and the value is not its start/end.
  The NAME RULE v4 (the integration lead's ruling, 02:56Z) decides every class below. L = the tokens of <X> without a trailing _<digits> (the
  cell-name disambiguator clause 2 also drops), split at `_`, case changes and letter/digit changes, lower-cased, NONE
  dropped by length, then normalized by a FIXED map: icpt -> interceptor, and a leading musl token is dropped (musl_ is
  the libc name itself). S = the tokens of the symbol's OWN name: its full qualified name (demangled; template arguments
  and parenthesised groups removed) without the namespace components (__asan __sanitizer __lsan __ubsan __interception,
  anonymous), i.e. class + method for members. <X> NAMES S iff L occurs IN ORDER as case-insensitive substrings of the
  qualified name, OR S occurs in order among the tokens of L, whole tokens (the symbol plus qualifiers; whole tokens so that
  fprintf does not hide in vfprintf). Planted controls, checked before any run:
  FakeStack_Allocate and FakeStack_Destroy do not name __asan::FakeStack::GC; InternalMmapVector_Realloc names
  __sanitizer::InternalMmapVectorNoCtor::Realloc; icpt_memchr names __interceptor_memchr; musl_memcmp names memcmp;
  MemToShadow_checked names __asan::MemToShadow; icpt_vfprintf does not name __interceptor_fprintf; calloc names
  __libc_calloc.
  descriptive-true       clause 2 NO-SYMBOL, the cell's A and E values bound EXACTLY a symbol S that <X> names.
  region label           clause 2 NO-SYMBOL, the value lies in a symbol that <X> names (A: start <= v < end; E: start < v
                         <= end).
  the rest of NO-SYMBOL, by the same rule on a symbol starting (A) / ending (E) at the value:
  descriptive-true (in-order)  <X> names one of them (calloc -> __libc_calloc).
  FALSE named-other      it names none of them: the label names a different function (FakeStack_Allocate -> FakeStack::GC).
  label, undecided       no symbol starts / ends at the value.
FALSE*, unverifiable and label classes carry ` / READ` or ` / UNREAD` (a reader of this table's cell exists or not).

Readers: one `git grep -n -w -E 'tfib_[AE]_[A-Za-z0-9_]+' REV -- LIB STMT...`; a line's own Definitions are not reads.
A reader is placed by the module its file Requires: `T` (--module, it reads this table's cell), `O` (--other-module: a
reader of the other image's cell of the same name), `?` (neither; counted as a reader of this table), with its
enclosing declaration. Inherited: the donor table has a cell of that name with the same class, whose value is the same
symbol + offset in the donor twin as this cell's in the twin."""
import argparse, bisect, collections, ctypes, ctypes.util, re, subprocess, sys
from elftools.elf.elffile import ELFFile

ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0], formatter_class=argparse.RawDescriptionHelpFormatter)
ap.add_argument('--table', required=True)
ap.add_argument('--twin', required=True)
ap.add_argument('--donor-table', required=True)
ap.add_argument('--donor-twin', required=True)
ap.add_argument('--repo', required=True)
ap.add_argument('--rev', default='ef9486db1b3d242cf865bd4a3ef7c25fbc02c6dd')
ap.add_argument('--lib', default='proofs/reac-repacer/fuzz_lock/lib')
ap.add_argument('--stmt', nargs='*', default=['projects/reac-repacer/fuzz_lock'])
ap.add_argument('--module', default='B.YB1w')
ap.add_argument('--other-module', default='A.AB1w')
ap.add_argument('--out', default='yb1w-clause2.tsv')
A = ap.parse_args()
NSN = ('__asan', '__sanitizer', '__lsan', '__ubsan', '__interception')

_cxx = ctypes.CDLL(ctypes.util.find_library('stdc++') or 'libstdc++.so.6')
_cxa = _cxx.__cxa_demangle
_cxa.restype = ctypes.c_void_p
_cxa.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.POINTER(ctypes.c_size_t), ctypes.POINTER(ctypes.c_int)]
_libc = ctypes.CDLL(None)
_libc.free.argtypes = [ctypes.c_void_p]


def demangle(m):
    st = ctypes.c_int(0)
    p = _cxa(m.encode(), None, None, ctypes.byref(st))
    if st.value != 0 or not p:
        return None
    s = ctypes.string_at(p).decode()
    _libc.free(p)
    return s


def qualified(m):
    """the full qualified name: demangled, template arguments and parenthesised groups removed (f()::x -> f::x),
    cv- / ref-qualifiers and a leading return type dropped; a plain C name as it is"""
    d = demangle(m) if m.startswith('_Z') else None
    if d is None:
        return m
    for pat in (r'<[^<>]*>', r'\([^()]*\)'):
        while True:
            d2 = re.sub(pat, '', d)
            if d2 == d:
                break
            d = d2
    d = re.sub(r'\s+(const|volatile|&&|&)(?=\s|$|::)', '', d).strip()
    return re.sub(r'^.*\s', '', d)


def dparts(m):
    if not m.startswith('_Z') or demangle(m) is None:
        return [m.lstrip('_')]
    return [p for p in qualified(m).split('::') if p and p not in NSN] or [m.lstrip('_')]


def dkey(m):
    return '_'.join(dparts(m))


def comps(m):  # ab1w_clause2.py
    if not m.startswith('_Z'):
        return None
    i = 2
    nested = m[i:i + 1] == 'N'
    if nested:
        i += 1
        while i < len(m) and m[i] in 'rVKRO':
            i += 1
    out = []
    while i < len(m) and m[i].isdigit():
        j = i
        while j < len(m) and m[j].isdigit():
            j += 1
        n = int(m[i:j])
        out.append(m[j:j + n])
        i = j + n
        if not nested or (i < len(m) and m[i] == 'I'):
            break
    return out or None


def key(mangled):  # ab1w_clause2.py
    c = comps(mangled)
    if c is None:
        return mangled.lstrip('_')
    while c and c[0] in NSN:
        c = c[1:]
    return '_'.join(c)


class Img:
    def __init__(self, twin):
        e = ELFFile(open(twin, 'rb'))
        self.syms = [(s.name, s['st_value'], s['st_size']) for s in e.get_section_by_name('.symtab').iter_symbols()
                     if s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT') and s['st_value'] and s.name]
        self.size = {}
        self.bykey, self.bydkey = collections.defaultdict(list), collections.defaultdict(list)
        self.starts, self.ends = collections.defaultdict(list), collections.defaultdict(list)
        for n, v, sz in self.syms:
            self.bykey[key(n)].append((n, v, sz))
            self.bydkey[dkey(n)].append((n, v, sz))
            self.starts[v].append(n)
            self.ends[v + sz].append(n)
            self.size.setdefault(n, sz)
        self.sized = sorted((v, sz, n) for n, v, sz in self.syms if sz)
        self.sv = [x[0] for x in self.sized]

    def covering(self, v, side):
        out = []
        i = bisect.bisect_right(self.sv, v)
        for j in range(max(0, i - 400), min(len(self.sized), i + 2)):
            s, sz, n = self.sized[j]
            if (s <= v < s + sz) if side == 'A' else (s < v <= s + sz):
                out.append((n, s, sz))
        return out

    def symoff(self, v, side):
        c = self.covering(v, side)
        if not c:
            return 'none'
        n, s, sz = sorted(c, key=lambda t: (t[2], t[0]))[0]
        return '%s+%#x' % (n, v - s)


def cells(path):
    t = open(path).read()
    return [(full, side, x, int(val, 0)) for full, side, x, val in
            re.findall(r'Definition (tfib_([AE])_(\w+?))\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+|\d+)\s*\.', t)]


def verdict(img, side, x, v, index='bydkey'):
    ix = getattr(img, index)
    cands = ix.get(x) or ix.get(re.sub(r'_\d+$', '', x)) or []
    if not cands:
        return 'NO-SYMBOL', cands
    hit = any((s == v) if side == 'A' else (s + sz == v) for _, s, sz in cands)
    return ('TRUE' if hit else 'FALSE-BY-NAME'), cands


def otoks(s):
    return [t.lower() for t in re.findall(r'[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z]+|[A-Z]+|\d+', s)]


ABBREV = {'icpt': 'interceptor'}   # a FIXED map (the integration lead's ruling, 02:56Z); a leading `musl` token is the libc name itself


def label_toks(x):
    t = [ABBREV.get(w, w) for w in otoks(re.sub(r'_\d+$', '', x))]
    return t[1:] if t[:1] == ['musl'] and len(t) > 1 else t


def own_toks(q):
    """S: the tokens of the symbol's own name, namespaces dropped (class + method for members)"""
    return [t for p in q.split('::') if p and p not in NSN for t in otoks(p)]


def in_order(needle, hay):
    hay, pos = hay.lower(), 0
    for t in needle:
        i = hay.find(t, pos)
        if i < 0:
            return False
        pos = i + len(t)
    return bool(needle)


def subseq_tok(needle, toks):
    it = iter(toks)
    return bool(needle) and all(any(t == h for h in it) for t in needle)


def names_q(x, q):
    """RULE v4: the label (normalized) occurs in order in the qualified name q, OR the symbol's own name occurs in order
    in the label (symbol plus qualifiers)"""
    L = label_toks(x)
    return in_order(L, q) or subseq_tok(own_toks(q), L)


def names(x, n):
    return names_q(x, qualified(n))


for _x, _q, _want in (('FakeStack_Allocate', '__asan::FakeStack::GC', False),
                      ('FakeStack_Destroy', '__asan::FakeStack::GC', False),
                      ('InternalMmapVector_Realloc', '__sanitizer::InternalMmapVectorNoCtor::Realloc', True),
                      ('icpt_memchr', '__interceptor_memchr', True),
                      ('musl_memcmp', 'memcmp', True),
                      ('MemToShadow_checked', '__asan::MemToShadow', True),
                      ('icpt_vfprintf', '__interceptor_fprintf', False),
                      ('calloc', '__libc_calloc', True)):
    if names_q(_x, _q) != _want:
        sys.exit('planted control FAILED: %s -> %s should be %s' % (_x, _q, _want))


def classify(img, vals, side, x, v):
    vd, cands = verdict(img, side, x, v)
    actual = (img.starts if side == 'A' else img.ends).get(v, [])
    if side == 'E' and (any(sz == 0 for _, _, sz in cands)
                        or (vd != 'TRUE' and actual and all(img.size[n] == 0 for n in actual))):
        z = [n for n, _, sz in cands if sz == 0] or actual
        return 'unverifiable by symtab (st_size 0)', vd, '%s has st_size 0; the value bounds %s' % (
            ' '.join(z[:2]), ' '.join(actual[:2]) or img.symoff(v, side))
    if vd == 'TRUE':
        return 'TRUE', vd, '-'
    if re.fullmatch(r'thunk_[0-9a-f]+', x):
        return 'thunk', vd, 'holds ' + img.symoff(v, side)
    if vd == 'FALSE-BY-NAME':
        tr = img.bydkey.get('interceptor_trampoline_' + x) or []
        if any((s == v) if side == 'A' else (s + sz == v) for _, s, sz in tr):
            return 'FALSE trampoline', vd, 'holds __interceptor_trampoline_' + x
        return 'FALSE other', vd, 'holds ' + (' '.join(actual[:2]) or img.symoff(v, side))
    a, e = vals.get('tfib_A_' + x), vals.get('tfib_E_' + x)
    if a is not None and e is not None:
        exact = [n for n in img.starts.get(a, []) if n in img.ends.get(e, []) and names(x, n)]
        if exact:
            return 'descriptive-true', vd, 'bounds exactly %s (%s)' % (exact[0], qualified(exact[0]))
    cov = [n for n, s, sz in img.covering(v, side) if names(x, n)]
    if cov:
        return 'region label', vd, 'in ' + img.symoff(v, side) + ' (named: ' + qualified(cov[0]) + ')'
    if not actual:
        return 'label, undecided', vd, 'no symbol starts / ends at the value; in ' + img.symoff(v, side)
    for n in actual:
        if names(x, n):
            return 'descriptive-true (in-order)', vd, 'bounds %s; label tokens in order in %s' % (n, qualified(n))
    return 'FALSE named-other', vd, 'bounds %s (%s); label tokens not in order in it' % (
        ' '.join(actual[:2]), ' | '.join(qualified(n) for n in actual[:2]))


def git(*a):
    return subprocess.run(['git', '-C', A.repo] + list(a), capture_output=True, text=True).stdout


TREES = [A.lib] + list(A.stmt)
MODRE = {}
for tag, m in (('T', A.module), ('O', A.other_module)):
    pre, name = m.rsplit('.', 1) if '.' in m else ('', m)
    p = re.escape('lib' + ('.' + pre if pre else ''))
    MODRE[tag] = re.compile(r'%s\s+Require(?:\s+Import|\s+Export)?[^.]*\b%s\b|%s\.%s\b' % (p, re.escape(name), p, re.escape(name)))
TEXT, MOD = {}, {}


def text(path):
    if path not in TEXT:
        TEXT[path] = git('show', '%s:%s' % (A.rev, path))
    return TEXT[path]


def module_of(path):
    if path not in MOD:
        t = re.sub(r'\(\*.*?\*\)', '', text(path), flags=re.S)
        MOD[path] = ''.join(tag for tag in ('T', 'O') if MODRE[tag].search(t)) or '?'
    return MOD[path]


DECL = re.compile(r"^\s*(?:#\[[^\]]*\]\s*)?(?:Local\s+|Global\s+|Program\s+)?(Definition|Lemma|Theorem|Corollary|Fact|Remark|"
                  r"Fixpoint|Example|Instance|Let|Notation|Ltac)\s+([A-Za-z_][\w']*)")


def enclosing(path, line):
    ls = text(path).split('\n')
    for i in range(line - 1, -1, -1):
        m = DECL.match(ls[i])
        if m:
            return '%s %s' % m.groups()
    return '-'


USES = collections.defaultdict(list)
for l in git('grep', '-n', '-w', '-E', r'tfib_[AE]_[A-Za-z0-9_]+', A.rev, '--', *TREES).splitlines():
    _, path, n, txt = l.split(':', 3)
    defined = set(re.findall(r'Definition\s+(tfib_[AE]_\w+)\b', txt))
    for w in set(re.findall(r"(?<![A-Za-z0-9_'])(tfib_[AE]_[A-Za-z0-9_]+)(?![A-Za-z0-9_'])", txt)) - defined:
        USES[w].append((path, int(n)))

L, D = Img(A.twin), Img(A.donor_twin)
LC, DC = cells(A.table), cells(A.donor_table)
lval = {full: v for full, side, x, v in LC}
dval = {full: (side, x, v) for full, side, x, v in DC}
dvals = {k: w[2] for k, w in dval.items()}


def inherited(full, side, v, cls):
    if full not in dval:
        return 'no (the donor has no such cell)'
    ds, dx, dv = dval[full]
    dcls = classify(D, dvals, ds, dx, dv)[0]
    lso, dso = L.symoff(v, side), D.symoff(dv, side)
    if dcls == cls and lso == dso:
        return 'yes (donor %#x = %s, class %s)' % (dv, dso, dcls)
    return 'no (donor %#x = %s, class %s)' % (dv, dso, dcls)


rows, cnt = [], collections.Counter()
for full, side, x, v in LC:
    cls, vd, why = classify(L, lval, side, x, v)
    vd0 = verdict(L, side, x, v, 'bykey')[0]
    rd = [(p, n, module_of(p), enclosing(p, n)) for p, n in sorted(USES.get(full, []))]
    rt = [r for r in rd if 'T' in r[2] or r[2] == '?']
    rd_txt = '; '.join('%s:%d [%s] %s' % (p[len(A.lib) + 1:] if p.startswith(A.lib + '/') else p, n, m, d)
                       for p, n, m, d in rd) or '-'
    final = cls
    if cls.startswith(('FALSE', 'label', 'unverifiable')):
        final = cls + (' / READ' if rt else ' / UNREAD')
    cnt[final] += 1
    named = ' '.join('%s[%#x,%#x)' % (n, s, s + sz) for n, s, sz in verdict(L, side, x, v)[1]) or '-'
    rows.append((full, '%#x' % v, side, vd0, vd, final, why, named, str(len(rt)), str(len(rd) - len(rt)), rd_txt,
                 inherited(full, side, v, cls)))
with open(A.out, 'w') as fh:
    fh.write('cell\tvalue\tside\tclause-2 verdict (ab1w_clause2.py key)\tclause-2 verdict (demangled key)\tclass\twhat the '
             'value is (twin)\tsymbol(s) the name keys to [start,end)\treaders of this table\'s cell\treaders of the other '
             'image\'s cell of the same name\treaders (file:line [T this table / O other table / ? neither] enclosing '
             'declaration)\tinherited from the donor\n')
    for r in rows:
        fh.write('\t'.join(r) + '\n')
print('%d named cells' % len(rows))
print('clause 2, ab1w_clause2.py key: ' + ', '.join('%s %d' % kv for kv in sorted(collections.Counter(r[3] for r in rows).items())))
print('clause 2, demangled key:       ' + ', '.join('%s %d' % kv for kv in sorted(collections.Counter(r[4] for r in rows).items())))
for k, n in sorted(cnt.items()):
    print('%-45s %d' % (k, n))
print('inherited (same class, same symbol + offset in the donor): ' + ', '.join('%s: %s %d' % (k[0], k[1], n) for k, n in sorted(
    collections.Counter((r[5], r[11].split(' ')[0]) for r in rows).items())))
