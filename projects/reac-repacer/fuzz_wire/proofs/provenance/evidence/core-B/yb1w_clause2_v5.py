#!/usr/bin/env python3
"""yb1w_clause2_v5.py [options] -- rule v5.2.1 of the AB1w / YB1w start-up table classifier: clause 2 of the
DIFFERENT-SYMBOL rule (ruled 20:58Z), the name rule (ruled 2026-10-31 02:56Z, changed 04:11Z) and the slot / string
test of D cells (ruled 04:35Z, 04:38Z, 05:05Z) over EVERY named cell of one start-up function table (`Definition
tfib_A_<X> : Z := v.`, `tfib_E_<X>`, `tfib_D_<X>`), with a class, its readers and whether
the donor already held it. Every input is an option: --table, --twin, --donor-table, --donor-twin and --repo are
required; the others default to fuzz_lock's image B (commit ef9486db1b3, donor fuzz_grant B 4f87de75d677), so an
image-A unit runs it unchanged with its own --rev / --lib / --stmt / --module / --other-module:

  --table FILE         the table to classify (a file; e.g. `git show REV:<lib>/B/YB1w.v > FILE`)
  --twin ELF           the image whose symtab judges it (an unstripped twin: released pins carry no symtab)
  --donor-table FILE   the donor's table (for `inherited`)     --donor-twin ELF   the donor image's twin
  --repo DIR --rev REV the git repository and commit whose trees are searched for readers
  --lib PATH           the unit's lib/ inside REPO               --stmt PATH ...   more trees to search (statement dirs)
  --module M           the table's module under lib (B.YB1w)    --other-module M  the other image's table (A.AB1w)
  --out TSV            one row per cell                         (the counts go to stdout)

Cells. tfib_A_<X> is the start of a function, tfib_E_<X> its end (start + st_size). tfib_D_<X> is a data address: the
tables write it as one value with no E partner. A D cell that names a .got slot, an .init_array / .fini_array slot or a
string is judged by what the value holds (below); every other D cell is judged like an A cell (the value is the START
of the symbol) against the OBJECT symbols only. Symbols: the FUNC / OBJECT symbols of the twin's .symtab with st_value
!= 0 and a name.
Each symbol is one record (name, start, st_size); every lookup, by address (start, end = start + st_size) or by name,
gives records, so two symbols of the same name (five __asan::MemToShadow) are never mixed.

Clause 2 (ab1w_clause2.py, sha256 7c6f10bf97a8): tfib_A_<X> / tfib_E_<X> / tfib_D_<X> is TRUE BY NAME iff its value is
the START (A, D) / END (E) of a symbol whose key is <X> (or <X> without a trailing _<digits>) in the twin's own symtab.
The column `clause-2 verdict (ab1w_clause2.py key)` is that script's key: the length-prefixed name components before
the first template argument or internal-linkage `L` (_ZN6__asanL16AsanInitInternalEv keys to ''), the __asan /
__sanitizer / __lsan / __ubsan / __interception namespaces dropped. The classes use the same rule on the key from the
FULL demangled name (libstdc++'s __cxa_demangle through ctypes; template arguments and every parenthesised group
removed, a local static keeping its function, the namespaces __asan __sanitizer __lsan __ubsan __interception
libunwind __sancov dropped, the rest joined by `_`; a plain C name without its leading underscores). Classes, in this
order:

  unverifiable by symtab (st_size 0)  decided FIRST (ruled 05:05Z): an E cell whose named symbol has st_size 0, or
                         whose value is bounded only by size-0 symbols: the symtab gives no end to check (ruled 02:02Z);
                         and an E cell whose A value is the start of a size-0 symbol that <X> names (ruled 04:35Z). An
                         A or D cell on a size-0 symbol is checked by its st_value: TRUE is valid there (ruled 04:11Z).
                         No other reason gives this class.
  TRUE                   clause 2 TRUE.
  PRECEDENCE: a label that is the EXACT name (the clause-2 key) of ANOTHER symbol in this image, which does not start
  (A, D) / end (E) at the value, is FALSE, before the name test (ruled 04:11Z):
  FALSE trampoline       the value is the start (A) / end (E) of __interceptor_trampoline_<X>: the cell names the libc
                         function and holds its ASan interceptor trampoline.
  FALSE other            any other value.
  The NAME RULE v5 (ruled 02:56Z; clause 2 changed 04:11Z and 04:39Z) decides every other cell (clause 2 NO-SYMBOL).
  Labels such as thunk_<hex> are not special: a label that names a donor address names no function of this image, and
  the rule decides it. L = the tokens of <X> without a trailing _<digits> (the cell-name disambiguator clause 2 also
  drops), split at `_`, case changes and letter/digit changes, lower-cased, NONE dropped by length, then normalized by
  a FIXED map: icpt -> interceptor, and a leading musl token is dropped (musl_ is the libc name itself). S = the tokens
  of the symbol's OWN name: its full qualified name (demangled; template arguments and parenthesised groups removed)
  without the namespace components above and the anonymous namespace, i.e. class + method for members; for a
  constructor or destructor (Class::Class, Class::~Class) the class tokens ONCE (ruled 04:39Z). <X> NAMES a symbol iff
    (clause 1) L occurs IN ORDER as case-insensitive substrings of the qualified name, OR
    (clause 2) S is a CONTIGUOUS PREFIX of L, as WHOLE tokens: the label is the symbol's name plus qualifiers
    (MemToShadow_checked names __asan::MemToShadow; SleepForSeconds_WaitForDebugger does not name WaitForDebugger;
    whole tokens, so that fprintf does not hide in vfprintf). One allowance (ruled 04:39Z): if the FIRST token of L
    equals a namespace component of the symbol's own qualified name that S drops (asan for __asan::, sanitizer for
    __sanitizer::; no free list: libc or interception on a symbol without that namespace is not skipped), the test
    is also made on L without that token (asan_UnpoisonBeforeMain_ctor names __asan::UnpoisonBeforeMain). Any other
    namespace is part of S, so the prefix test already covers a label that starts with it.
  descriptive-true       the cell's A and E values bound EXACTLY one symbol [A, E) that <X> names.
  descriptive-true (in-order)  otherwise, the value is the start (A, D: of any st_size) / end (E: of a symbol with
                         st_size > 0) of a symbol that <X> names (tfib_D_REAL_read -> __interception::real_read).
  FALSE region label     the value lies inside a symbol that <X> names, not at its start / end (FALSE by the rule,
                         ruled 04:11Z).
  FALSE named-other      symbols start / end at the value and <X> names none of them: the label names a different
                         function (FakeStack_Allocate -> FakeStack::GC).
  FALSE no symbol at the value  no symbol starts / ends at the value (FALSE by the rule, ruled 04:11Z).
FALSE* and unverifiable classes carry ` / READ` or ` / UNREAD` (a reader of this table's cell exists or not).

D cells that name a slot or a string are judged by what the value DENOTES, measured in the twin, never by a name match
(ruled 04:35Z; the array reading 04:38Z), before every class above. The static content of a word is its bytes in the
image with the loader's relocations (SHF_ALLOC SHT_RELA / SHT_REL sections) applied: *_RELATIVE gives the addend, *_64
the symbol + addend; any other relocation type at the word leaves it unknown. A word is 8 bytes in ELF64.
  GOT_<Y>, and <Y>_musl when the value lies in .got:  TRUE (.got slot) iff the value is a word of .got whose static
                         content is the st_value of a symbol <Y> denotes: the FUNC / OBJECT symbols whose demangled key
                         (the clause-2 key) is <Y> (environ_musl: <Y> = environ -> __environ and its aliases), or, for
                         a GOT_<Y> label that names a compiler-rt accessor, the symbol in the FIXED table GOT_SYMBOL
                         (common_flags -> __sanitizer::common_flags_dont_use, flags ->
                         __asan::asan_flags_dont_use_directly: __sanitizer::common_flags() and __asan::flags() return
                         their addresses). GOT_SYMBOL is used ONLY for GOT_<Y> labels: never for <y>_musl, never in the
                         name test (ruled 05:05Z).
  init_array_<i>_<j>, fini_array_<i>_<j>:  TRUE (array slot) iff the value is the section's sh_addr + word * i, i <= j,
                         and j + 1 == sh_size / word: the label's slots i..j run to the section's last slot (the
                         range reading, ruled 04:38Z; i > 0 ruled 05:05Z).
  str_<x>:               TRUE (string) iff the value lies in .rodata (or .rodata.*), STARTS a string (the byte before
                         it is NUL, or it is the section start), and the bytes from the value to the first NUL (no
                         length cap; no NUL before the section end is FALSE) are the bytes <x> denotes: <x> itself,
                         except under the FIXED table STRINGS (str_sealed -> "<sealed>", a measured fact; ruled
                         05:05Z). The bytes read (hex and text) are in the output.
  Otherwise:             FALSE .got slot / FALSE array slot / FALSE string.

Checked on every run, before any cell is classified; the script exits 1 if one fails:
  NAME CONTROLS (label, qualified name, names it?): see CONTROLS below; 41 pairs. They are SYNTHETIC name tests: the
  qualified name is given to the test, not looked up in an image (on fuzz_lock, asan_UnpoisonBeforeMain_ctor bounds the
  file-static UnpoisonBeforeMain, with no namespace, and is FALSE by rule).
  PLANTED CELLS: see PLANTS, D_PLANTS and R_PLANTS below; cells built from the twin's own symbols and sections (an
  anchor symbol's start / end + an offset; the .got word that holds an anchor symbol; a section's sh_addr + an offset;
  the address of a string) and classified by the same code, each with its required class. R_PLANTS also plant one
  loader relocation on a copy of the image, so that the relocation code is tested on images that have none. In
  fuzz_lock's image B the symbol anchors give the same values as the planted tables of the v4 review.

Readers: one `git grep -n -w -E 'tfib_[AED]_[A-Za-z0-9_]+' REV -- LIB STMT...`; a line's own Definitions are not reads.
A reader is placed by the module its file Requires: `T` (--module, it reads this table's cell), `O` (--other-module: a
reader of the other image's cell of the same name), `?` (neither; counted as a reader of this table), with its
enclosing declaration. Inherited: the donor table has a cell of that name with the same class, whose value is the same
symbol + offset in the donor twin as this cell's in the twin."""
import argparse, bisect, collections, copy, ctypes, ctypes.util, re, subprocess, sys
from elftools.elf.descriptions import describe_reloc_type
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
NS_AB1W = ('__asan', '__sanitizer', '__lsan', '__ubsan', '__interception')   # ab1w_clause2.py's own list
NSN = NS_AB1W + ('libunwind', '__sancov')
KINDS = {'A': 'FO', 'E': 'FO', 'D': 'O'}   # F = STT_FUNC, O = STT_OBJECT: the symbols each side is judged against

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
    while c and c[0] in NS_AB1W:
        c = c[1:]
    return '_'.join(c)


class Img:
    """the twin's FUNC / OBJECT symbols as records (name, start, st_size, kind F / O), indexed by key and by address"""
    def __init__(self, twin):
        e = ELFFile(open(twin, 'rb'))
        kind = {'STT_FUNC': 'F', 'STT_OBJECT': 'O'}
        self.syms = [(s.name, s['st_value'], s['st_size'], kind[s['st_info']['type']])
                     for s in e.get_section_by_name('.symtab').iter_symbols()
                     if s['st_info']['type'] in kind and s['st_value'] and s.name]
        self.bykey, self.bydkey = collections.defaultdict(list), collections.defaultdict(list)
        self.starts, self.ends = collections.defaultdict(list), collections.defaultdict(list)
        for r in self.syms:
            self.bykey[key(r[0])].append(r)
            self.bydkey[dkey(r[0])].append(r)
            self.starts[r[1]].append(r)
            self.ends[r[1] + r[2]].append(r)
        self.sized = sorted((v, sz, n, k) for n, v, sz, k in self.syms if sz)
        self.sv = [x[0] for x in self.sized]
        self.secs = [(s['sh_addr'], s['sh_addr'] + s['sh_size'], s.name) for s in e.iter_sections()
                     if s['sh_flags'] & 2 and s['sh_size']]   # SHF_ALLOC
        self.word, self.order = e.elfclass // 8, 'little' if e.little_endian else 'big'
        self.sec = {s.name: (s['sh_addr'], s['sh_size'], b'' if s['sh_type'] == 'SHT_NOBITS' else s.data())
                    for s in e.iter_sections() if s['sh_flags'] & 2}
        self.relocs = {}   # the loader's relocations (SHF_ALLOC SHT_RELA / SHT_REL): r_offset -> (type, S, A or None)
        for s in e.iter_sections():
            if s['sh_type'] in ('SHT_RELA', 'SHT_REL') and s['sh_flags'] & 2:
                st = e.get_section(s['sh_link']) if s['sh_link'] else None
                for r in s.iter_relocations():
                    sym = st.get_symbol(r['r_info_sym']) if st is not None and r['r_info_sym'] else None
                    self.relocs[r['r_offset']] = (describe_reloc_type(r['r_info_type'], e),
                                                  sym['st_value'] if sym is not None else 0,
                                                  r['r_addend'] if r.is_RELA() else None)

    def at(self, v, side):
        """the symbols that start (A, D) / end (E) at v"""
        return [r for r in (self.ends if side == 'E' else self.starts).get(v, []) if r[3] in KINDS[side]]

    def covering(self, v, side):
        out = []
        i = bisect.bisect_right(self.sv, v)
        for j in range(max(0, i - 400), min(len(self.sized), i + 2)):
            s, sz, n, k = self.sized[j]
            if k in KINDS[side] and ((s < v <= s + sz) if side == 'E' else (s <= v < s + sz)):
                out.append((n, s, sz, k))
        return out

    def symoff(self, v, side):
        c = self.covering(v, side)
        if not c:
            return 'none'
        n, s, sz, _ = sorted(c, key=lambda r: (r[2], r[0]))[0]
        return '%s+%#x' % (n, v - s)

    def section(self, v):
        return ' '.join(n for lo, hi, n in self.secs if lo <= v < hi) or 'none'

    def static_word(self, v):
        """the static content of the word at v: its file bytes with a loader relocation applied (value or None, how)"""
        sec = [(n, lo, d) for n, (lo, _, d) in self.sec.items() if lo <= v and v + self.word <= lo + len(d)]
        if not sec:
            return None, 'no file bytes at %#x' % v
        n, lo, d = sec[0]
        b = d[v - lo:v - lo + self.word]
        raw, rel = int.from_bytes(b, self.order), self.relocs.get(v)
        how = '%s %#x: bytes %s' % (n, v, b.hex())
        if rel is None:
            return raw, how + ', no relocation'
        t, S, A = rel
        A = raw if A is None else A
        if t.endswith('_RELATIVE'):
            return A % (1 << 8 * self.word), how + ', %s addend %#x' % (t, A)
        if t.endswith('_64'):
            return (S + A) % (1 << 8 * self.word), how + ', %s symbol %#x + addend %#x' % (t, S, A)
        return None, how + ', relocation %s not applied' % t


def cells(path):
    t = open(path).read()
    return [(full, side, x, int(val, 0)) for full, side, x, val in
            re.findall(r'Definition (tfib_([AED])_(\w+?))\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+|\d+)\s*\.', t)]


def bound(r, side):
    """the address a cell of this side names on symbol record r: its start (A, D) or its end (E)"""
    return r[1] + r[2] if side == 'E' else r[1]


def verdict(img, side, x, v, index='bydkey'):
    ix = getattr(img, index)

    def look(k):
        return [r for r in ix.get(k, []) if r[3] in KINDS[side]]
    cands = look(x) or look(re.sub(r'_\d+$', '', x))
    if not cands:
        return 'NO-SYMBOL', cands
    return ('TRUE' if any(bound(r, side) == v for r in cands) else 'FALSE-BY-NAME'), cands


def otoks(s):
    return [t.lower() for t in re.findall(r'[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z]+|[A-Z]+|\d+', s)]


ABBREV = {'icpt': 'interceptor'}   # a FIXED map (ruled 02:56Z); a leading `musl` token is the libc name itself


def label_toks(x):
    t = [ABBREV.get(w, w) for w in otoks(re.sub(r'_\d+$', '', x))]
    return t[1:] if t[:1] == ['musl'] and len(t) > 1 else t


def own_parts(q):
    """the components of the symbol's own name: namespaces dropped; a constructor / destructor (Class::Class,
    Class::~Class) is its class once"""
    p = [c for c in q.split('::') if c and c not in NSN]
    return p[:-1] if len(p) > 1 and p[-1].lstrip('~') == p[-2] else p


def own_toks(q):
    """S: the tokens of the symbol's own name (class + method for members; the class once for a constructor)"""
    return [t for p in own_parts(q) for t in otoks(p)]


def in_order(needle, hay):
    hay, pos = hay.lower(), 0
    for t in needle:
        i = hay.find(t, pos)
        if i < 0:
            return False
        pos = i + len(t)
    return bool(needle)


def prefix_tok(needle, toks):
    """needle is a contiguous prefix of toks, whole tokens"""
    return bool(needle) and toks[:len(needle)] == needle


def names_q(x, q):
    """RULE v5.1: the label (normalized) occurs in order in the qualified name q, OR the symbol's own name is the start
    of the label (the symbol plus qualifiers), also after a first label token that names a namespace of q that S drops"""
    L, S = label_toks(x), own_toks(q)
    ns = [c.lstrip('_').lower() for c in q.split('::')[:-1] if c in NSN]
    return in_order(L, q) or prefix_tok(S, L) or (L[:1] != [] and L[0] in ns and prefix_tok(S, L[1:]))


def names(x, n):
    return names_q(x, qualified(n))


CONTROLS = (('FakeStack_Allocate', '__asan::FakeStack::GC', False),
            ('FakeStack_Destroy', '__asan::FakeStack::GC', False),
            ('InternalMmapVector_Realloc', '__sanitizer::InternalMmapVectorNoCtor::Realloc', True),
            ('icpt_memchr', '__interceptor_memchr', True),
            ('musl_memcmp', 'memcmp', True),
            ('MemToShadow_checked', '__asan::MemToShadow', True),
            ('icpt_vfprintf', '__interceptor_fprintf', False),
            ('calloc', '__libc_calloc', True),
            ('GC_FakeStack', '__asan::FakeStack::GC', False),
            ('SuppressionContext_ctor', '__sanitizer::SuppressionContext::SuppressionContext', True),
            ('InternalMmapVector_Realloc_2', '__sanitizer::InternalMmapVectorNoCtor::Realloc', True),
            ('dup3', 'dup2', False),
            ('musl_calloc', '__libc_calloc', True),
            ('calloc_musl', '__libc_calloc', False),
            ('icpt_strlen', '__sanitizer::internal_strlen', False),
            ('icpt_strlen_x', '__interceptor_strlen', True),
            ('Foo_2_Bar_x', 'Foo2Bar', True),
            ('GetPageSizeCached', '__sanitizer::GetPageSize', True),
            ('asan_Mem_Shadow', '__asan::MemToShadow', True),
            ('mem_mem', '__libc_mem', False),
            ('printf', 'vfprintf', True),
            ('Stack_Fake', '__asan::FakeStack::GC', False),
            ('GetTid_gettid', '__sanitizer::GetTid', True),
            ('InternalFree_LowLevelAllocator_free_to_freelist', '__sanitizer::internal_allocator', False),
            ('SleepForSeconds_WaitForDebugger', '__sanitizer::WaitForDebugger', False),
            ('CFI_Parser_parseCIE_helper', 'libunwind::CFI_Parser::parseCIE', True),
            ('WriteModuleCoverage_x', '__sancov::::WriteModuleCoverage', True),
            ('asan_UnpoisonBeforeMain_ctor', '__asan::UnpoisonBeforeMain', True),
            ('asan_UnpoisonBeforeMain_ctor', 'UnpoisonBeforeMain', False),     # no namespace: no token skipped
            ('ThreadContextBase_ctor_ThreadRegistry_init_helpe', '__sanitizer::ThreadRegistry::ThreadRegistry', False),
            ('SuppressionContext_dtor', '__sanitizer::SuppressionContext::~SuppressionContext', True),
            ('libc_sigaction_impl', 'sigaction', False),
            ('interception_real_read_impl', '__interception::real_read', True),
            ('asan_inited_x', '__asan::asan_inited', True),
            ('checked_MemToShadow', '__asan::MemToShadow', False),
            ('Quarantine_Quarantine_Put', '__sanitizer::Quarantine::Put', False),   # a class is no namespace
            ('icpt_vfprintf_2', '__interceptor_fprintf', False),
            ('internal_strchrnul', '__sanitizer::internal_strchr', False),
            ('asan_asan_MemToShadow', '__asan::MemToShadow', False),   # ONE namespace token may be skipped
            ('Mem_asan_ToShadow', '__asan::MemToShadow', False),       # only the FIRST token
            ('sanitizer_Foo', 'Foo::__sanitizer::BarBaz', False))      # S a prefix of L, not L a prefix of S
for _x, _q, _want in CONTROLS:
    if names_q(_x, _q) != _want:
        sys.exit('planted control FAILED: %s -> %s should be %s' % (_x, _q, _want))


STRINGS = {'sealed': b'<sealed>'}   # str_<x> -> the bytes it denotes where they are not <x>: a FIXED table, measured
GOT_SYMBOL = {'common_flags': '_ZN11__sanitizer21common_flags_dont_useE',   # __sanitizer::common_flags() returns
              'flags': '_ZN6__asan28asan_flags_dont_use_directlyE'}           # &common_flags_dont_use, __asan::flags()
                                                                               # &asan_flags_dont_use_directly


def d_slot(img, x, v, strings=STRINGS):
    """a D cell that names a .got slot, an .init_array / .fini_array slot or a string, judged by what the value holds:
    (class, what was measured); None for any other label"""
    glo, gsize, _ = img.sec.get('.got', (0, 0, b''))
    in_got = glo <= v < glo + gsize
    m = re.fullmatch(r'GOT_(\w+)', x)
    got_label = m is not None
    if m is None and not re.fullmatch(r'(init|fini)_array_\d+_\d+|str_\w+', x) and in_got:
        m = re.fullmatch(r'(\w+)_musl', x)
    if m:
        y = m.group(1)
        tgt = ([r for r in img.syms if r[0] == GOT_SYMBOL[y]] if got_label and y in GOT_SYMBOL
               else img.bydkey.get(y, []))   # the accessor maps: GOT_<Y> labels only, never <y>_musl
        den = '<Y> = %s denotes %s' % (y, ' '.join(r[0] for r in tgt[:4]) or 'no symbol')
        if not in_got or (v - glo) % img.word:
            return 'FALSE .got slot', 'not a .got word (.got [%#x, %#x)); %s' % (glo, glo + gsize, den)
        c, read = img.static_word(v)
        hit = [r for r in tgt if c is not None and r[1] == c]
        return ('TRUE (.got slot)' if hit else 'FALSE .got slot'), '%s; static content %s; %s%s' % (
            read, 'unknown' if c is None else '%#x' % c, den, ' (st_value %#x)' % hit[0][1] if hit else '')
    m = re.fullmatch(r'(init|fini)_array_(\d+)_(\d+)', x)
    if m:
        name, i, j = '.%s_array' % m.group(1), int(m.group(2)), int(m.group(3))
        if name not in img.sec:
            return 'FALSE array slot', 'the image has no %s' % name
        lo, size, _ = img.sec[name]
        pos = ('slot %d' % ((v - lo) // img.word) if lo <= v < lo + size and (v - lo) % img.word == 0
               else 'not a slot of %s' % name)
        ok = size % img.word == 0 and i <= j and size // img.word == j + 1 and v == lo + img.word * i
        return ('TRUE (array slot)' if ok else 'FALSE array slot'), (
            '%s sh_addr %#x sh_size %#x (%d slots); the value is %s; the label says slot %d of slots 0..%d' % (
                name, lo, size, size // img.word, pos, i, j))
    m = re.fullmatch(r'str_(\w+)', x)
    if m:
        want = strings.get(m.group(1), m.group(1).encode())
        exp = 'expected %s' % repr(want)[1:]
        sec = [(n, lo, d) for n, (lo, _, d) in img.sec.items()
               if (n == '.rodata' or n.startswith('.rodata.')) and lo <= v < lo + len(d)]
        if not sec:
            return 'FALSE string', 'not in .rodata (section %s); %s' % (img.section(v), exp)
        n, lo, d = sec[0]
        end = d.find(b'\0', v - lo)   # to the first NUL or the section end: no length cap
        got = d[v - lo:end + 1 if end >= 0 else len(d)]
        start = v == lo or d[v - lo - 1] == 0
        ok = start and end >= 0 and got[:-1] == want
        return ('TRUE (string)' if ok else 'FALSE string'), '%s %#x: bytes %s = %s%s; %s' % (
            n, v, got.hex(), repr(got)[1:], '' if end >= 0 else ' (no NUL before the section end)',
            exp + ('' if start else '; the byte before the value is %s, not NUL' % d[v - lo - 1:v - lo].hex()))
    return None


def classify(img, vals, side, x, v, strings=STRINGS):
    vd, cands = verdict(img, side, x, v)
    if side == 'D':
        slot = d_slot(img, x, v, strings)
        if slot is not None:
            return slot[0], vd, slot[1]
    at = img.at(v, side)
    a, e = (None, None) if side == 'D' else (vals.get('tfib_A_' + x), vals.get('tfib_E_' + x))
    if side == 'E' and (any(r[2] == 0 for r in cands) or (vd != 'TRUE' and at and all(r[2] == 0 for r in at))):
        z = [r[0] for r in cands if r[2] == 0] or [r[0] for r in at]
        return 'unverifiable by symtab (st_size 0)', vd, '%s has st_size 0; the value bounds %s' % (
            ' '.join(z[:2]), ' '.join(r[0] for r in at[:2]) or img.symoff(v, side))
    if side == 'E' and a is not None:
        z = [r for r in img.starts.get(a, []) if r[2] == 0 and names(x, r[0])]
        if z:
            return 'unverifiable by symtab (st_size 0)', vd, 'the A value %#x starts %s, named, st_size 0' % (a, z[0][0])
    if vd == 'TRUE':
        return 'TRUE', vd, '-'
    if vd == 'FALSE-BY-NAME':
        tr = [r for r in img.bydkey.get('interceptor_trampoline_' + x, []) if r[3] in KINDS[side]]
        if any(bound(r, side) == v for r in tr):
            return 'FALSE trampoline', vd, 'holds __interceptor_trampoline_' + x
        return 'FALSE other', vd, 'holds ' + (' '.join(r[0] for r in at[:2]) or img.symoff(v, side))
    if a is not None and e is not None:
        exact = [r for r in img.starts.get(a, []) if r[2] and r[1] + r[2] == e and names(x, r[0])]
        if exact:
            return 'descriptive-true', vd, 'bounds exactly %s (%s)' % (exact[0][0], qualified(exact[0][0]))
    hit = [r for r in at if (r[2] or side != 'E') and names(x, r[0])]
    if hit:
        return 'descriptive-true (in-order)', vd, '%s %s (%s), st_size %d' % (
            'ends' if side == 'E' else 'starts', hit[0][0], qualified(hit[0][0]), hit[0][2])
    cov = [r for r in img.covering(v, side) if names(x, r[0])]
    if cov:
        return 'FALSE region label', vd, 'in ' + img.symoff(v, side) + ' (named: ' + qualified(cov[0][0]) + ')'
    if at:
        return 'FALSE named-other', vd, 'bounds %s (%s); the label does not name it' % (
            ' '.join(r[0] for r in at[:2]), ' | '.join(qualified(r[0]) for r in at[:2]))
    return 'FALSE no symbol at the value', vd, 'no %s symbol %s at the value; in %s, section %s' % (
        'OBJECT' if side == 'D' else 'FUNC / OBJECT', 'ends' if side == 'E' else 'starts', img.symoff(v, side),
        img.section(v))


STRLEN, STRCMP = '_ZN11__sanitizer15internal_strlenEPKc', '_ZN11__sanitizer15internal_strcmpEPKcS1_'
MEM2SHADOW, TRAMP = '_ZN6__asanL11MemToShadowEm', '__interceptor_trampoline_memcmp'
PLANTS = (  # (label, side, anchor symbol, nth (0 = the first of that name by address), start / end, offset, class)
    ('AsanThread_Create_helper', 'A', STRLEN, 0, 'start', 0, 'FALSE named-other'),          # a wrong NO-SYMBOL pair
    ('AsanThread_Create_helper', 'E', STRLEN, 0, 'end', 0, 'FALSE named-other'),
    ('internal_strnlen_checked', 'A', STRLEN, 0, 'start', 0, 'FALSE named-other'),          # strnlen is not strlen
    ('internal_strnlen_checked', 'E', STRLEN, 0, 'end', 0, 'FALSE named-other'),
    ('AsanThread_Destroy', 'A', STRLEN, 0, 'start', 0, 'FALSE other'),                      # a wrong exact-name pair
    ('AsanThread_Destroy', 'E', STRLEN, 0, 'end', 0, 'FALSE other'),
    ('internal_strlen_fast', 'A', STRLEN, 0, 'start', 0, 'descriptive-true'),
    ('internal_strlen_fast', 'E', STRLEN, 0, 'end', 0, 'descriptive-true'),
    ('internal_strlen_onlyA', 'A', STRLEN, 0, 'start', 0, 'descriptive-true (in-order)'),
    ('internal_strlen_onlyE', 'E', STRLEN, 0, 'end', 0, 'descriptive-true (in-order)'),
    ('internal_strlen_mid', 'A', STRLEN, 0, 'start', 4, 'FALSE region label'),
    ('internal_strlen_mid', 'E', STRLEN, 0, 'end', -4, 'FALSE region label'),
    ('internal_strlen_wrongE', 'A', STRLEN, 0, 'start', 0, 'descriptive-true (in-order)'),
    ('internal_strlen_wrongE', 'E', STRCMP, 0, 'end', 0, 'FALSE named-other'),
    ('set_thread_area_x', 'A', '__set_thread_area', 0, 'start', 0, 'descriptive-true (in-order)'),   # st_size 0
    ('set_thread_area_x', 'E', '__unmapself', 0, 'start', 0, 'unverifiable by symtab (st_size 0)'),
    ('start', 'A', '_start', 0, 'start', 0, 'TRUE'),                                       # _start: st_size 0
    ('start', 'E', '_start_c', 0, 'end', 0, 'unverifiable by symtab (st_size 0)'),
    ('start_x', 'A', '_start', 0, 'start', 0, 'descriptive-true (in-order)'),
    ('start_x', 'E', '_start_c', 0, 'end', 0, 'unverifiable by symtab (st_size 0)'),
    ('nothing_here', 'A', '_start', 0, 'start', 2, 'FALSE no symbol at the value'),
    ('wrap_memcmp_x', 'A', '__wrap_memcmp', 0, 'start', 0, 'descriptive-true'),               # an alias tie: each
    ('wrap_memcmp_x', 'E', '__wrap_memcmp', 0, 'end', 0, 'descriptive-true'),                 # label names one of
    ('interceptor_trampoline_memcmp_x', 'A', TRAMP, 0, 'start', 0, 'descriptive-true'),       # the two symbols
    ('interceptor_trampoline_memcmp_x', 'E', TRAMP, 0, 'end', 0, 'descriptive-true'),
    ('memcmp', 'A', TRAMP, 0, 'start', 0, 'FALSE trampoline'),
    ('memcmp', 'E', TRAMP, 0, 'end', 0, 'FALSE trampoline'),
    ('MemToShadow_split', 'A', MEM2SHADOW, 0, 'start', 0, 'descriptive-true (in-order)'),   # one name, two symbols
    ('MemToShadow_split', 'E', MEM2SHADOW, 1, 'end', 0, 'descriptive-true (in-order)'),
    ('thunk_66008', 'A', '_ZN11__sanitizer9CloseFileEi', 0, 'start', 0, 'FALSE named-other'),
    ('thunk_66008', 'E', '_ZN11__sanitizer9CloseFileEi', 0, 'end', 0, 'FALSE named-other'),
    ('asan_inited', 'D', '_ZN6__asanL11asan_initedE', 0, 'start', 0, 'TRUE'),
    ('REAL_read', 'D', '_ZN14__interception9real_readE', 0, 'start', 0, 'descriptive-true (in-order)'),
    ('internal_strlen', 'D', STRLEN, 0, 'start', 0, 'FALSE no symbol at the value'),         # a FUNC is not data
    ('asan_flags_dont_use_directly_x', 'D', '_ZN6__asan28asan_flags_dont_use_directlyE', 0, 'start', 8,
     'FALSE region label'),
    ('dlsym_x', 'E', 'dlsym', 0, 'start', 0, 'FALSE named-other'),                         # the v5.1 review's six
    ('foo_bar', 'A', '_start', 0, 'start', 0, 'FALSE named-other'),                         # foo_bar: a false case
    ('foo_bar', 'E', '_start_c', 0, 'end', 0, 'FALSE named-other'),                         # of an E on a size-0 start
    ('internal_strlen_2', 'A', STRLEN, 0, 'start', 0, 'TRUE'),
    ('environ_musl', 'D', '__environ', 0, 'start', 0, 'descriptive-true (in-order)'),       # not in .got: a name
    ('start_c', 'A', '_start', 0, 'start', 0, 'FALSE other'),                               # the size-0 rule comes
    ('start_c', 'E', STRLEN, 0, 'end', 0, 'unverifiable by symtab (st_size 0)'),            # before the exact other
    ('start_c_2', 'A', '_start', 0, 'start', 0, 'FALSE other'),                             # name, and before a
    ('start_c_2', 'E', '_start_c', 0, 'end', 0, 'unverifiable by symtab (st_size 0)'),      # clause-2 TRUE (05:05Z)
    ('set_thread_area', 'E', STRLEN, 0, 'end', 0, 'unverifiable by symtab (st_size 0)'),    # E alone: its symbol has
    ('only_size0_end', 'E', '__unmapself', 0, 'start', 0, 'unverifiable by symtab (st_size 0)'))  # st_size 0 / only
                                                                                    # size-0 symbols end at the value
D_PLANTS = (  # (label, anchor kind, anchor, byte offset, class). got: the .got word that holds the anchor symbol's
    # st_value; sec: the section's sh_addr ({last} = its last slot index); str: the .rodata address of the bytes + NUL;
    # strlit / strout: the first NUL-preceded identifier string in / outside .rodata, as {s}; strstart: .rodata's start;
    # strlong: the first NUL-preceded printable .rodata string longer than 256 bytes; strnonul: the last .rodata string,
    # on a copy of the image whose .rodata loses its trailing NULs
    ('GOT_kHighMemEnd', 'got', '_ZN6__asan11kHighMemEndE', 0, 'TRUE (.got slot)'),
    ('GOT_kMidMemBeg', 'got', '_ZN6__asan11kHighMemEndE', 0, 'FALSE .got slot'),
    ('GOT_flags', 'got', '_ZN6__asan28asan_flags_dont_use_directlyE', 0, 'TRUE (.got slot)'),    # GOT_SYMBOL
    ('environ_musl', 'got', '__environ', 0, 'TRUE (.got slot)'),
    ('environ_musl', 'got', '_ZN6__asan11kHighMemEndE', 0, 'FALSE .got slot'),
    ('flags_musl', 'got', '_ZN6__asan28asan_flags_dont_use_directlyE', 0, 'FALSE .got slot'),   # GOT_SYMBOL: GOT_ only
    ('init_array_0_{last}', 'sec', '.init_array', 0, 'TRUE (array slot)'),
    ('init_array_0_{last_1}', 'sec', '.init_array', 0, 'FALSE array slot'),
    ('init_array_1_{last}', 'sec', '.init_array', 8, 'TRUE (array slot)'),
    ('init_array_0_{last}', 'sec', '.init_array', 8, 'FALSE array slot'),
    ('fini_array_0_{last}', 'sec', '.fini_array', 0, 'TRUE (array slot)'),
    ('init_array_1_{last}', 'sec', '.init_array', 0, 'FALSE array slot'),      # i > 0: the value must be slot i
    ('init_array_1_{last_1}', 'sec', '.init_array', 8, 'FALSE array slot'),    # slots i..j must end at the last slot
    ('fini_array_2_{last}', 'sec', '.fini_array', 16, 'FALSE array slot'),     # i <= j
    ('GOT_kMidMem', 'got', '_ZN6__asan10kMidMemBegE', 0, 'FALSE .got slot'),   # <Y> is a key, not a name test
    ('str_sealed', 'str', b'<sealed>', 0, 'TRUE (string)'),
    ('str_sealed', 'str', b'<sealed>', 1, 'FALSE string'),
    ('str_x', 'str', b'<sealed>', 0, 'FALSE string'),
    ('str_seale', 'str', b'<sealed>', 0, 'FALSE string'),   # PLANT_STRINGS: a strict prefix is not the string
    ('str_ealed', 'str', b'<sealed>', 1, 'FALSE string'),   # PLANT_STRINGS: the value must START a string
    ('str_{s}', 'strlit', '', 0, 'TRUE (string)'),          # <x> itself
    ('str_{s}', 'strout', '', 0, 'FALSE string'),           # .rodata only
    ('str_rodata_start', 'strstart', '', 0, 'TRUE (string)'),
    ('str_long', 'strlong', '', 0, 'TRUE (string)'),        # no length cap: the whole string is compared
    ('str_long_x', 'strlong', '', 0, 'FALSE string'),       # its twin: the same bytes but the last one
    ('str_nonul', 'strnonul', '', 0, 'FALSE string'))       # no NUL before the section end
PLANT_STRINGS = dict(STRINGS, seale=b'<seale', ealed=b'sealed>')   # entries for the planted cells only
HIGH, MIDB, MIDE = '_ZN6__asan11kHighMemEndE', '_ZN6__asan10kMidMemBegE', '_ZN6__asan10kMidMemEndE'
R_PLANTS = (  # (label, the .got word holding this symbol, byte offset, one relocation planted there on a copy of the
    # image: (type, S, A), each None (S: 0; A: no addend, REL) / a symbol (its st_value) / (s1, s2) (st_value difference))
    ('GOT_kMidMemEnd', HIGH, 0, ('R_RISCV_RELATIVE', HIGH, MIDE), 'TRUE (.got slot)'),      # RELATIVE: A; S ignored
    ('GOT_kHighMemEnd', HIGH, 0, ('R_RISCV_RELATIVE', HIGH, MIDE), 'FALSE .got slot'),      # the relocation, not bytes
    ('GOT_kMidMemEnd', MIDB, 0, ('R_RISCV_64', MIDB, (MIDE, MIDB)), 'TRUE (.got slot)'),    # _64: S + A
    ('GOT_kHighMemEnd', HIGH, 0, ('R_RISCV_RELATIVE', None, None), 'TRUE (.got slot)'),     # REL: the bytes are A
    ('GOT_kMidMemBeg', MIDB, 0, ('R_RISCV_JUMP_SLOT', None, None), 'FALSE .got slot'),      # other type: unknown
    ('GOT_kHighMemEnd', HIGH, 4, ('R_RISCV_RELATIVE', None, HIGH), 'FALSE .got slot'))      # not a .got word


def got_words(img, sym):
    """the .got words whose static content is the st_value of the first symbol named sym"""
    recs = sorted((r for r in img.syms if r[0] == sym), key=lambda r: r[1])
    lo, size, _ = img.sec.get('.got', (0, 0, b''))
    return [w for w in range(lo, lo + size, img.word) if recs and img.static_word(w)[0] == recs[0][1]]


def check_plants(img):
    built = []   # (side, label, value, class, image, string table)
    for x, side, anchor, nth, point, off, want in PLANTS:
        recs = sorted((r for r in img.syms if r[0] == anchor), key=lambda r: r[1])
        if len(recs) <= nth:
            sys.exit('planted cell tfib_%s_%s: the twin has no symbol %s (copy %d)' % (side, x, anchor, nth))
        built.append((side, x, recs[nth][1] + (recs[nth][2] if point == 'end' else 0) + off, want, img, PLANT_STRINGS))
    for x, kind, anchor, off, want in D_PLANTS:
        strings, pimg = PLANT_STRINGS, img
        rodata = [(n, lo, d) for n, (lo, _, d) in img.sec.items() if n == '.rodata' or n.startswith('.rodata.')]
        if kind == 'got':
            at = got_words(img, anchor)
        elif kind == 'sec':
            lo, size, _ = img.sec.get(anchor, (0, 0, b''))
            x = x.format(last=size // img.word - 1, last_1=size // img.word - 2)
            at = [lo] if size // img.word >= 2 else []
        elif kind == 'str':
            at = [lo + i for n, lo, d in rodata for i in [d.find(anchor + b'\0')] if i >= 0]
        elif kind == 'strstart':
            at = [lo for n, lo, d in rodata[:1] if b'\0' in d]
            strings = dict(PLANT_STRINGS, **{x[4:]: rodata[0][2].split(b'\0')[0]}) if at else strings
        elif kind == 'strlong':
            hits = [(lo + m.start(1), m.group(1)) for n, lo, d in rodata
                    for m in [re.search(rb'(?<=\0)([\x20-\x7e]{257,})\0', d)] if m]
            at = [h[0] for h in hits[:1]]
            if hits:
                s = hits[0][1]
                strings = dict(PLANT_STRINGS, long=s, long_x=s[:-1] + bytes([s[-1] ^ 1]))
        elif kind == 'strnonul':   # on a copy of the image whose .rodata loses its trailing NULs: the last string
            n, lo, d = rodata[0]   # then runs to the section end with no NUL, and is FALSE even with the right bytes
            d2 = d.rstrip(b'\0')
            k = d2.rfind(b'\0') + 1
            at = [lo + k] if 0 < k < len(d2) else []
            pimg = copy.copy(img)
            pimg.sec = dict(img.sec, **{n: (lo, len(d2), d2)})
            strings = dict(PLANT_STRINGS, **{x[4:]: d2[k:]})
        else:
            secs = rodata if kind == 'strlit' else [(n, lo, d) for n, (lo, _, d) in sorted(img.sec.items())
                                                     if not (n == '.rodata' or n.startswith('.rodata.'))]
            hits = [(lo + m.start(1), m.group(1).decode()) for n, lo, d in secs
                    for m in [re.search(rb'(?<=\0)([A-Za-z_][A-Za-z0-9_]{3,})\0', d)] if m]
            at = [h[0] for h in hits[:1]]
            x = x.format(s=hits[0][1]) if hits else x
        if not at:
            sys.exit('planted cell tfib_D_%s: the twin has no %s for %s' % (x, kind, anchor))
        built.append(('D', x, at[0] + off, want, pimg, strings))

    first = {r[0]: r[1] for r in sorted(img.syms, key=lambda r: -r[1])}   # each name's lowest st_value

    def val(spec):
        return 0 if spec is None else first[spec] if isinstance(spec, str) else first[spec[0]] - first[spec[1]]
    for x, holder, off, (t, s, a), want in R_PLANTS:
        at = got_words(img, holder)
        if not at:
            sys.exit('planted cell tfib_D_%s: no .got word holds %s' % (x, holder))
        rimg = copy.copy(img)
        rimg.relocs = dict(img.relocs)
        rimg.relocs[at[0] + off] = (t, val(s), None if a is None else val(a))
        built.append(('D', x, at[0] + off, want, rimg, PLANT_STRINGS))
    vals = {'tfib_%s_%s' % (side, x): v for side, x, v, _, _, _ in built}
    bad = ['tfib_%s_%s = %#x is %s, should be %s' % (side, x, v, got, want) for side, x, v, want, im, st in built
           for got in [classify(im, vals, side, x, v, st)[0]] if got != want]
    if bad:
        sys.exit('planted cell FAILED: ' + '; '.join(bad))
    return len(built)


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


L, D = Img(A.twin), Img(A.donor_twin)
NPLANT = check_plants(L)
USES = collections.defaultdict(list)
for l in git('grep', '-n', '-w', '-E', r'tfib_[AED]_[A-Za-z0-9_]+', A.rev, '--', *TREES).splitlines():
    _, path, n, txt = l.split(':', 3)
    defined = set(re.findall(r'Definition\s+(tfib_[AED]_\w+)\b', txt))
    for w in set(re.findall(r"(?<![A-Za-z0-9_'])(tfib_[AED]_[A-Za-z0-9_]+)(?![A-Za-z0-9_'])", txt)) - defined:
        USES[w].append((path, int(n)))

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
    if cls.startswith(('FALSE', 'unverifiable')):
        final = cls + (' / READ' if rt else ' / UNREAD')
    cnt[final] += 1
    named = ' '.join('%s[%#x,%#x)' % (r[0], r[1], r[1] + r[2]) for r in verdict(L, side, x, v)[1]) or '-'
    rows.append((full, '%#x' % v, side, vd0, vd, final, why, named, str(len(rt)), str(len(rd) - len(rt)), rd_txt,
                 inherited(full, side, v, cls)))
with open(A.out, 'w') as fh:
    fh.write('cell\tvalue\tside\tclause-2 verdict (ab1w_clause2.py key)\tclause-2 verdict (demangled key)\tclass\twhat the '
             'value is (twin)\tsymbol(s) the name keys to [start,end)\treaders of this table\'s cell\treaders of the other '
             'image\'s cell of the same name\treaders (file:line [T this table / O other table / ? neither] enclosing '
             'declaration)\tinherited from the donor\n')
    for r in rows:
        fh.write('\t'.join(r) + '\n')
print('%d name controls and %d planted cells pass' % (len(CONTROLS), NPLANT))
print('%d named cells (%s)' % (len(rows), ', '.join('%s %d' % kv for kv in sorted(collections.Counter(r[2] for r in rows).items()))))
print('clause 2, ab1w_clause2.py key: ' + ', '.join('%s %d' % kv for kv in sorted(collections.Counter(r[3] for r in rows).items())))
print('clause 2, demangled key:       ' + ', '.join('%s %d' % kv for kv in sorted(collections.Counter(r[4] for r in rows).items())))
for k, n in sorted(cnt.items()):
    print('%-45s %d' % (k, n))
print('inherited (same class, same symbol + offset in the donor): ' + ', '.join('%s: %s %d' % (k[0], k[1], n) for k, n in sorted(
    collections.Counter((r[5], r[11].split(' ')[0]) for r in rows).items())))
