#!/usr/bin/env python3
"""The nm lines gen_tbl.py reads, extracted from a full nm table (`nm -S` lines: address, size, type, name).

  nm_extract.py reply|disco NM_TABLE TWIN PIN > extract

reply: the fuzz_reply asan image (the donor side of gen_tbl.py); disco: a fuzz_disco image (A or B).
NM_TABLE: the full nm table of the image. TWIN: the unstripped image the table was made from. PIN: the stripped image
of record (the one gen_tbl.py reads the bytes of).

Checks, each fatal: PT_LOAD 2..4 of TWIN and PIN are byte-equal (address, size, bytes), so every symbol address in code
and data is an address of the pin; the table lists exactly the sized, named .symtab symbols of TWIN (value, size,
name, as a multiset); every name below has a line in the table.

Writes a `#` header (the table's, the twin's and the pin's sha256, the two checks) and then, in table order and
unchanged, every line whose name is in LOOKUP (the names gen_tbl.py looks up by name: FUNCS, the data cells, and for
a fuzz_disco image main and LLVMFuzzerTestOneInput) or in RESOLVED (the other symbols that are the smallest symbol
holding an address gen_tbl.py resolves, sym_of, in fuzz_reply and in both fuzz_disco images; the same 13 names in
the three). Keeping every line of a kept name keeps the name lookups' uniqueness checks and indices, and every
address lookup finds the same smallest symbol (a missing one could only turn a result into None or a larger
symbol).
"""
import hashlib
import os
import sys
from collections import Counter

from elftools.elf.elffile import ELFFile

LOOKUP = [
    '__interceptor_trampoline_memset', '__interceptor_trampoline_memcpy', '__asan_memcpy', '__asan_memset',
    '___interceptor_memset', '___interceptor_memcpy', '_ZN6__asanL11MemToShadowEm', '__asan_region_is_poisoned',
    '_ZN6__asan10AsanInitedEv', '_ZN6__asan18TryAsanInitFromRtlEv', '_ZN11__sanitizer11mem_is_zeroEPKcm', 'memcpy',
    'memset', '__asan_shadow_memory_dynamic_address', '_ZN6__asan21replace_intrin_cachedE',
    '_ZN14__interception11real_memcpyE', '_ZN14__interception11real_memsetE', '_ZN6__asanL11asan_initedE',
    '_ZN6__asan11kHighMemEndE', '_ZN6__asan10kMidMemBegE', '_ZN6__asan10kMidMemEndE',
]
LOOKUP_DISCO = ['main', 'LLVMFuzzerTestOneInput']
RESOLVED = [
    '_ZN11__sanitizer10StackTrace12GetCurrentPcEv', '_ZN11__sanitizer11CheckFailedEPKciS1_yy',
    '_ZN11__sanitizer18BufferedStackTrace10UnwindImplEmmPvbj', '_ZN11__sanitizer21common_flags_dont_useE',
    '_ZN6__asan18ReportGenericErrorEmmmmbmjb', '_ZN6__asan22IsStackTraceSuppressedEPKN11__sanitizer10StackTraceE',
    '_ZN6__asan23IsInterceptorSuppressedEPKc', '_ZN6__asan28asan_flags_dont_use_directlyE',
    '_ZN6__asan31HaveStackTraceBasedSuppressionsEv',
    '_ZN6__asan32ReportStringFunctionSizeOverflowEmmPN11__sanitizer18BufferedStackTraceE',
    '_ZN6__asan39ReportStringFunctionMemoryRangesOverlapEPKcS1_mS1_mPN11__sanitizer18BufferedStackTraceE',
    '__sanitizer_internal_memcpy', '__sanitizer_internal_memset',
]


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def loads(elf):
    return [(g['p_vaddr'], g['p_memsz'], g.data()) for g in elf.iter_segments() if g['p_type'] == 'PT_LOAD']


def main():
    if len(sys.argv) != 5 or sys.argv[1] not in ('reply', 'disco'):
        sys.exit(__doc__)
    role, table, twin, pin = sys.argv[1:]
    names = set(LOOKUP + RESOLVED + (LOOKUP_DISCO if role == 'disco' else []))
    with open(twin, 'rb') as ft, open(pin, 'rb') as fp:
        et, ep = ELFFile(ft), ELFFile(fp)
        lt, lp = loads(et), loads(ep)
        if not (len(lt) >= 4 and len(lp) >= 4 and lt[1:4] == lp[1:4]):
            sys.exit('nm_extract.py: PT_LOAD 2..4 of the twin and the pin differ')
        st = et.get_section_by_name('.symtab')
        if st is None:
            sys.exit('nm_extract.py: the twin has no .symtab')
        syms = Counter((s['st_value'], s['st_size'], s.name) for s in st.iter_symbols() if s['st_size'] and s.name)
    lines = open(table).read().split('\n')
    if lines[-1] == '':
        lines.pop()
    rows = [l.split() for l in lines]
    if any(len(q) != 4 for q in rows):
        sys.exit('nm_extract.py: a table line is not `address size type name`')
    if Counter((int(q[0], 16), int(q[1], 16), q[3]) for q in rows) != syms:
        sys.exit('nm_extract.py: the table is not the symbol list of the twin')
    kept = [l for l, q in zip(lines, rows) if q[3] in names]
    missing = sorted(names - {q[3] for q in rows})
    if missing:
        sys.exit('nm_extract.py: names without a line: %s' % ', '.join(missing))
    head = [
        '# the nm lines gen_tbl.py reads: %d of the %d lines of %s sha256 %s (role %s; %d names)'
        % (len(kept), len(lines), os.path.basename(table), sha(table), role, len(names)),
        '# twin %s sha256 %s; pin %s sha256 %s; PT_LOAD 2..4 of twin and pin byte-equal: yes'
        % (os.path.basename(twin), sha(twin), os.path.basename(pin), sha(pin)),
        '# the table lists exactly the sized, named .symtab symbols of the twin (value, size, name): yes, %d'
        % len(rows),
    ]
    sys.stdout.write('\n'.join(head + kept) + '\n')


if __name__ == '__main__':
    main()
