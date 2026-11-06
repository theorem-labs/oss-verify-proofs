#!/usr/bin/env python3
"""tfibtable-B.py TWIN DONOR_TWIN UNIT DONOR_LIB > TFIB-TABLE-B.tsv: every `Definition tfib_(A|D|E)_<name> : Z := <numeral>.`
in UNIT/lib/B and UNIT/lib/Reusable, read against the image's unstripped twin TWIN (C++ names demangled with the C++
runtime's __cxa_demangle).

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
             ruled by the unit lead (2026-10-31): the neighbouring cells listed in ROTATED, whose labels each name the
             function one place away (by the head, or by the whole name of a function with no symbol) and not the one
             at the cell's value; (e) TCA's test (the image-A core's row, on image A, 2026-10-31 09:05Z; the unit lead's ruling for
             image B): the label names a function that is in the twin at another address, or names another function
             (with or without a symbol in the twin) than the one at the value, and does not also name the function at
             the value (X_body on X is not WRONG). The cells and the functions their labels name are listed in TCA;
             (f) the release lead's rule (2026-10-31): a label spelled as a function (a C/C++ function name,
             Class_Method, ns_Func) is FALSE when no symbol at the value, of any type or binding, has that name
             (demangled, as for OK-EXACT, with runs of `_` read as one) and the value is the start or end of another
             function. A label is read as that name when the whole label, or the label up to an annotation after a `_`
             (X_gettid on X), is a name of a symbol at the value; the typedefs in TYPEDEF stand for the template
             instance they name. Thunk labels (thunk_<hex>) and plain descriptions (a label with a word of DESC: the
             lead's helper, stub, ret, insns, or, and words of that kind) claim no symbol and stay. By the lead's
             correction (12:07Z), a label for f on f's interceptor or wrapper alias (__interceptor_trampoline_f,
             __wrap_f, ___interceptor_f: the OK-ALIAS cells) is correct and stays.
  NO-SYMBOL  anything else: a thunk label or a plain description (rule (f)), or a label that names the symbol at its
             value under a typedef or with runs of `_` read as one. The note says which, and when the label's head
             spells a function elsewhere.
An _E cell whose value ends the same function as its _A partner's start takes the _A partner's class.

DONOR PAIRING. The same cell in DONOR_LIB/B (the donor's released text) and the symbol at its value in DONOR_TWIN:
`same` when that symbol has a name in common with the target's, else `differs`; `absent` when the donor has no such
cell. A WRONG cell whose donor pairing is `same` is the donor's (inherited) mislabel.

READERS. `git grep -now 'tfib_[ADE]_<word>'` over UNIT/lib: every hit of the cell's name except a Definition of that
name (its own, and image A's own cell of the same name in lib/A/AB1w.v). `readers outside lib/A` leaves out lib/A, whose
files read image A's cells.

ALIAS SCREEN (the release lead's 12:07Z rule, for every WRONG cell). The symbols at the value in the whole symtab, local
and global, demangled (_A: every symbol starting there; _E: every symbol ending there): `own-alias` when one is
__interceptor_trampoline_f, __wrap_f, ___interceptor_f or __interceptor_f, or has a name of f, for f the label's own
function (the label, without the donor's musl_ / icpt_ prefix and a trailing _<n>, or it up to an annotation after a
`_`: tls_get_addr_thunk names tls_get_addr); `other-function-alias` (named) when
the interceptor or wrapper names at the value are of another function; `no-alias` when there are none. An own-alias cell
is correct and must not be deleted."""
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
C = cells(lib, ['B', 'Reusable'])
DC = {c['cell']: c for c in cells(dlib, ['B', 'Reusable'])}


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
# (d) ROTATED (the unit lead's ruling, 2026-10-31): neighbouring labels shifted one function off their values
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

# (e) TCA's test: the label names another function than the one at the value. A list value: the function keys the
# label names, looked up in the twin; a string: a function with no symbol in the twin.
TCA = {
    'AsanChunkView_GetAsanChunk_ptr_helper': '__asan::Allocator::GetAsanChunk',
    'Allocator_SharedInitCode': '__asan::Allocator::SharedInitCode',
    'SizeClassAllocator64_ReturnToAllocator_helper': ['SizeClassAllocator64_ReturnToAllocator'],
    'Allocator_ComputeRZLog': '__asan::Allocator::ComputeRZLog',
    'FakeStack_Allocate': '__asan::FakeStack::Allocate',
    'RoundUpTo_size_CHECK_helper_sanitizer_common_h_C': '__sanitizer::RoundUpTo',
    'asan_globals_RegisterGlobal_vector_push_back': '__asan::RegisterGlobal and InternalMmapVector::push_back',
    'memcmp_2': ['memcmp'],
    'vfprintf_2': ['vfprintf', '__interceptor_trampoline_vfprintf'],
    'icpt_vfprintf_2': ['__interceptor_vfprintf'],
    'InitializeCommonInterceptors': '__asan::InitializeCommonInterceptors',
    'InitializeSignalInterceptors_or_syscall_hooks': 'InitializeSignalInterceptors',
    'icpt_cfree_or_DlsymFree': 'the cfree interceptor and DlsymAlloc::Free',
    'DlsymAlloc_PointerIsMine_internal_allocator_From': '__sanitizer::DlSymAllocator<DlsymAlloc>::PointerIsMine',
    'HeapProfile_Insert_asan_memory_profile': ['HeapProfile_Insert'],
    'asan_poison_stack_memory_PoisonAlignedStackMemor': ['asan_poison_stack_memory'],
    'ScopedInErrorReport_ReportError_helper': '__asan::ScopedInErrorReport::ReportError',
    'AsanInitFromRtl_ENSURE_ASAN_INITED': ['AsanInitFromRtl'],
    'asan_handle_no_return_tiny_rtl_stub_2_insns': ['asan_handle_no_return'],
    'ReserveShadowMemoryRanges_sealed_early_shadow_re': ['ReserveShadowMemoryRange'],
    'AsanStats_Clear_ctor': '__asan::AsanStats::Clear',
    'InternalAlloc_RawInternalAlloc': ['InternalAlloc'],
    'InternalFree_LowLevelAllocator_free_to_freelist': ['InternalFree'],
    'internal_allocator_getter': ['internal_allocator'],
    'LowLevelAllocator_InternalAlloc_bump_allocator': ['InternalAlloc'],
    'OverrideCommonFlags_no_op_flag_hook_2_insns': '__sanitizer::OverrideCommonFlags',
    'FlagParser_ParseString_parse_flags': ['FlagParser_ParseString'],
    'FlagParser_PrintFlagDescriptions_gate_Verbosity': ['FlagParser_PrintFlagDescriptions'],
    'GetNamedMappingFd_ReadProcess_openat_getdents64': ['GetNamedMappingFd'],
    'GetPageSizeCached': '__sanitizer::GetPageSizeCached',
    'internal_sigaction_syscall_wrapper_selector': ['internal_sigaction'],
    'MmapFixedNoAccess_3_insn_arg_shim_0x65c98': ['MmapFixedNoAccess'],
    'MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co': ['MmapFixedSuperNoReserve'],
    'sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a': ['GetTls'],
    'DTLS_Destroy_ForEachDVT_no_op_4_insns': ['DTLS_Destroy'],
    'InternalAllocatorLock_Unlock_or_stats_add_17_ins': '__sanitizer::InternalAllocatorLock / InternalAllocatorUnlock',
    'ThreadContextBase_ctor_ThreadRegistry_init_helpe': ['ThreadContextBase_ThreadContextBase'],
    'GetThreadStackTopAndBottom_caller_ClearShadowFor': ['GetThreadStackTopAndBottom',
                                                         'AsanThread_ClearShadowForThreadStackAndTLS'],
    'InternalMmapVector_push_back': '__sanitizer::InternalMmapVector::push_back',
    'MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser': ['MmapFixedOrDieOnFatalError', 'MmapFixedSuperNoReserve'],
    'MaybeStartBackgroudThread': '__sanitizer::MaybeStartBackgroudThread',
    'Atexit_internal_exit_hook_runner_12_insns_execut': ['Atexit'],
    'StackDepotBase_Get': '__sanitizer::StackDepotBase::Get',
    'Unwind_GetIP_slow_unwind_helper': ['_Unwind_GetIP'],
    'asan_malloc_hook_RunMallocHooks_target_sanitizer': ['RunMallocHooks'],
    'ubsan_MaybeCallUbsanDefaultOptions': '__ubsan::MaybeCallUbsanDefaultOptions',
    'fini_stub_ret': ['_fini'],
    'libc_exit_fini_array_walker_stub': ['__libc_exit_fini'],
    'musl_exit_helper_stub': ['exit'],
    'syscall_cp_c_tail_sccp_9_insns': ['__syscall_cp_c'],
    'lock_unlock_pair_user_futex': ['__lock', '__unlock'],
    'pthread_key_create_body_tsd_init': ['pthread_key_create'],
    'pthread_key_atfork_tsd_table_init_11_insns': "musl's __pthread_key_atfork",
}
for n, named in TCA.items():
    a = by.get(n, {}).get('A')
    if not a or a['cls'] != 'NO-SYMBOL':
        continue
    if isinstance(named, str):
        says = '%s (no symbol in the twin)' % named
    else:
        ss_n = []
        for k in named:
            exact = [s for s in T.syms if s['type'] == 'STT_FUNC' and s['name'] == k]
            ss_n += exact or FN[k]
        here = {s['value'] for s in a['ss']}
        assert ss_n and not here & {s['value'] for s in ss_n}, n
        says = '; '.join(sorted({'%s at %#x' % (label([s]), s['value']) for s in ss_n}))
    for k in 'AE':
        x = by[n].get(k)
        if x:
            x['cls'] = 'WRONG'
            x['note'] = "TCA's test: the label names %s; this cell is on %s" % (says, label(a['ss']))

# (f) the release lead's rule. DESC: the words of a plain description (they name a role, form or size of code, not a
# function). TYPEDEF: a typedef a label uses, with the demangled template instance it stands for
# (compiler-rt sanitizer_allocator_internal.h: InternalAllocator = CombinedAllocator<SizeClassAllocator32<AP32>,
# LargeMmapAllocatorPtrArrayStatic>, whose secondary is LargeMmapAllocator<NoOpMapUnmapCallback, ...PtrArrayStatic>).
DESC = {'helper', 'stub', 'ret', 'insns', 'or', 'body', 'ctor', 'getter', 'check', 'tail', 'entry', 'area', 'fn',
        'growth', 'sealed', 'patch', 'tiny', 'weak', 'default', 'named', 'may', 'die', 'core', 'static', 'background',
        'frame', 'pointer', 'no'}
TYPEDEF = {'InternalAllocator': (
    '__sanitizer::CombinedAllocator<__sanitizer::SizeClassAllocator32<__sanitizer::AP32>, '
    '__sanitizer::LargeMmapAllocatorPtrArrayStatic>::',
    '__sanitizer::LargeMmapAllocator<__sanitizer::NoOpMapUnmapCallback, __sanitizer::LargeMmapAllocatorPtrArrayStatic, '
    '__sanitizer::LocalAddressSpaceView>::')}
one_ = lambda k: re.sub(r'_+', '_', k).strip('_')


def names_value(n, ss):
    """the symbol at the value that the label n, or n up to an annotation, names; None if none"""
    toks = n.split('_')
    for s in ss:
        ks = {one_(k) for k in keys(s)}
        if any(one_('_'.join(toks[:i])) in ks for i in range(len(toks), 0, -1)):
            return s
        for td, insts in TYPEDEF.items():
            if n.startswith(td + '_') and s['dem'].startswith(insts):
                rest = n[len(td) + 1:].split('_')
                if any('_'.join(rest[:i]) in ks for i in range(len(rest), 0, -1)):
                    return s
    return None


for n, d in by.items():
    a = d.get('A')
    if not a or a['cls'] != 'NO-SYMBOL':
        continue
    toks = n.split('_')
    desc = sorted({t for t in toks if t in DESC or t.isdigit()})
    if re.fullmatch(r'thunk_[0-9a-f]+', n):
        note = "rule (f): a thunk label; claims no symbol"
    elif desc:
        note = "rule (f): a plain description (%s); claims no symbol" % ', '.join(desc)
    else:
        s = names_value(n, a['ss'])
        if s is not None:
            note = "rule (f): names %s at the value%s" % (label([s]), ' under the typedef %s' % toks[0]
                                                           if toks[0] in TYPEDEF else ' (runs of `_` read as one)')
        else:
            h = head(n)
            el = (' (its head %s is %s)' % (h[0], '; '.join(sorted({'%s at %#x' % (label([t]), t['value']) for t in h[1]})))
                  if h and not {t['value'] for t in h[1]} & {t['value'] for t in a['ss']} else '')
            for k in 'AE':
                x = d.get(k)
                if x:
                    x['cls'] = 'WRONG'
                    x['note'] = ("rule (f) FALSE: the label is spelled as a function, %s, and no symbol at the value "
                                 "has that name%s; the value is the %s of %s" % (
                                     n, el, 'start' if k == 'A' else 'end', label(a['ss'])))
            continue
    for k in 'AE':
        x = d.get(k)
        if x and x['cls'] == 'NO-SYMBOL':
            x['note'] = note

# the alias screen of each WRONG cell
ALIASF = re.compile(r'^(?:__interceptor_trampoline_|__wrap_|_{2,3}interceptor_)(.+)$')
for r in rows:
    r['screen'] = ''
    if r['cls'] != 'WRONG':
        continue
    at = (T.start if r['kind'] == 'A' else T.end).get(r['val'], [])
    n = r['name']
    own = {n} | {n[len(p):] for p in ('musl_', 'icpt_') if n.startswith(p)}
    own = {one_(re.sub(r'_\d+$', '', x)) for x in own}
    bases = {s['name']: one_(ALIASF.match(s['name']).group(1)) for s in at if ALIASF.match(s['name'])}
    if any(o == b or o.startswith(b + '_') for o in own for b in bases.values()) or \
            any(own & {one_(k) for k in keys(s)} for s in at):
        r['screen'] = 'own-alias (%s)' % ', '.join(sorted(s['name'] for s in at))
    elif bases:
        r['screen'] = 'other-function-alias (%s: of %s)' % (', '.join(sorted(bases)), ', '.join(sorted(set(bases.values()))))
    else:
        r['screen'] = 'no-alias'

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
    rd.sort(key=lambda x: (x[0].startswith('lib/A/'), x))
    r['readers'] = len(rd)
    r['readersB'] = sum(not f.startswith('lib/A/') for f, _ in rd)
    r['where'] = ','.join('%s:%d' % x for x in rd[:6]) + (',...' if len(rd) > 6 else '')

sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
head_c = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=unit, capture_output=True, text=True, check=True).stdout.strip()
dirty = subprocess.run(['git', 'status', '--porcelain', '--', 'lib'], cwd=unit, capture_output=True, text=True,
                       check=True).stdout.strip()
cnt = collections.Counter(r['cls'] for r in rows)
print('# twin sha256 %s; donor twin sha256 %s; tree %s%s; cells %d: %s' % (
    sha(twin), sha(dtwin), head_c[:12], ' (lib modified)' if dirty else '', len(rows),
    ', '.join('%s %d' % kv for kv in sorted(cnt.items()))))
print('\t'.join(['cell', 'file:line', 'value', 'symbol at value', 'how', 'class', 'note', 'donor pairing (value, symbol)',
                 'readers', 'readers outside lib/A', 'reader lines', 'alias-screen']))
for r in rows:
    print('\t'.join([r['cell'], 'lib/%s:%d' % (r['file'], r['line']), '%#x' % r['val'], label(r['ss']), r['how'], r['cls'],
                     r['note'], r['donor'], str(r['readers']), str(r['readersB']), r['where'], r['screen']]))
sys.stderr.write('cells %d  %s\n' % (len(rows), '  '.join('%s %d' % kv for kv in sorted(cnt.items()))))
