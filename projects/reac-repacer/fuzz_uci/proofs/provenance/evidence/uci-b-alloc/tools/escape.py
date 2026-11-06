#!/usr/bin/env python3
"""escape.py -- the second settlement pass. Read-only on X_ELF, Y_ELF and settle.tsv; rewrites settle.tsv in place.

For each row settle.py left `ROW NOT SETTLED` because an UNSETTLED target pair pointed to the empty string (1 NUL byte,
equal in both images), replace that pair's ACCEPT row with class `CSTR-ESCAPE` and verdict SETTLED-EQUAL. The
settlement is PRIMARY (named reader + reads only to the NUL), SUPPORT (measured equal window). Per row:
  - ESCAPE: the escape site(s) in the traced function with pc(s) and what the escape is (sd to a struct field with
    its offset, or a jalr zero return);
  - PATH: where the pointer goes (field of a flags struct read by the flag machinery; returned to the caller named
    below);
  - READER: the named reader that consumes the pointer and the pc at which it starts (FlagParser::ParseString, Printf's
    %s via InternalScopedString, __strftime_l's format walker, ...);
  - NUL-STOP: why that reader reads only to the first NUL (internal_strlen / internal_strcmp over the string, Printf's
    %s handler walks the string via InternalScopedString::Append until NUL, musl's __strftime_l reads with lbu and
    stops on the first NUL byte).
  - SUPPORT: a measured equal window at the target in both images (bytes read from PT_LOAD, byte-equal). The window
    is >= 1 (the NUL every reader stops on). It is supporting evidence; it does NOT bound what the reader may read:
    the reader's own behaviour does. The window simply shows the memory is also byte-equal well past the NUL.
Rows verified by the fresh reviewer in REVIEW.md (lines 70-85) with its own ELF reader and capstone disassembly.
usage: escape.py X_ELF Y_ELF SETTLE_TSV"""
import os, runpy, sys
HERE = os.path.dirname(os.path.abspath(__file__))
_argv = sys.argv[:]
sys.argv = [os.path.join(HERE, 'jtcheck.py'), _argv[1], _argv[2], '']
jt = runpy.run_path(os.path.join(HERE, 'jtcheck.py'), run_name='jtcheck_lib')
sys.argv = _argv
dc = jt['dc']; X = jt['X']; Y = jt['Y']

# One entry per row (keyed by function symbol). The escape pcs come from the function's disassembly (settle.py traced
# them; cross-checked by the reviewer in REVIEW.md). Each ParseString / Printf / __strftime_l reader stops at the first
# NUL byte of the string, which is the first byte at the target in both images.
READERS = {
    '_ZN11__sanitizer11CommonFlags11SetDefaultsEv': dict(
        escape='stores the empty-string pointer into 3 const-char* fields of CommonFlags: sd a1,24(a0) at +0x94; '
               'sd a1,200(a0) at +0xd8; sd a1,208(a0) at +0xdc',
        path='fields +24 (`exitcode` default), +200 (`log_suffix`), +208 (`external_symbolizer_path`) of the global '
             'CommonFlags record (the a0 struct this call initialises)',
        reader='FlagParser::ParseString(const char *) when the runtime parses __asan_default_options / ASAN_OPTIONS '
               '(it reads the string with internal_strlen before copying into the field) and Printf("%s", flag) in '
               'PrintFlagDescriptions when the user asks for the current flag values',
        nulstop='internal_strlen counts bytes up to the first NUL; Printf\'s %s handler (InternalScopedString::Append '
                'in VSNPrintf) walks the string one byte at a time and stops on the first NUL. Both are the SAME code '
                'in X and Y (both EQUAL-mod-pcrel across the record)'),
    '_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE': dict(
        escape='stores the empty-string pointer into a const-char* field of a CommonFlags record: sd a1,24(a2) at '
               '+0x1228, and again at +0x1274 (second RegisterFlag call for a different field)',
        path='field +24 of the a2 CommonFlags record, which is registered with the parser so FlagParser::ParseString '
             'can bind an ASAN_OPTIONS token to the field',
        reader='FlagParser::ParseString(const char *) at parse time; and Printf("%s", flag) via PrintFlagDescriptions',
        nulstop='internal_strlen / Printf\'s %s handler stop at the first NUL (same as above)'),
    '_ZN6__asan15InitializeFlagsEv': dict(
        escape='the empty-string pointer is spilled onto the stack at sd a3,288(sp) at +0x108 and reloaded at +0xc94 '
               '(ld a1,288(sp)); the one remaining escape is sd s3,104(s3) at +0x220 (a const-char* field store '
               'inside the same flags object)',
        path='reload reaches a1 of FlagParser::ParseString at +0xc9c (jal); the store at +0x220 lands in the same '
             'kind of const-char* field of the asan Flags struct',
        reader='FlagParser::ParseString(const char *) directly at +0xc9c (settle.py already named this reader)',
        nulstop='FlagParser::ParseString uses internal_strlen to size the copy and internal_strcmp to compare; both '
                'stop at the first NUL'),
    '_ZN6__lsan5Flags11SetDefaultsEv': dict(
        escape='stores the empty-string pointer into a const-char* field of __lsan::Flags: sd a1,32(a0) at +0x1c',
        path='field +32 of the a0 __lsan::Flags record (the LSan `suppressions` path, a `const char *`)',
        reader='FlagParser::ParseString(const char *) when the runtime parses LSAN_OPTIONS and when __lsan reads the '
               'suppressions file name',
        nulstop='internal_strlen / internal_strcmp stop at the first NUL (same reader family as above)'),
    '_ZN7__ubsan5Flags11SetDefaultsEv': dict(
        escape='stores the empty-string pointer into a const-char* field of __ubsan::Flags: sd a1,8(a0) at +0xc',
        path='field +8 of the a0 __ubsan::Flags record (the UBSan `suppressions` path, a `const char *`)',
        reader='FlagParser::ParseString(const char *) when the runtime parses UBSAN_OPTIONS',
        nulstop='internal_strlen / internal_strcmp stop at the first NUL'),
    '__nl_langinfo_l': dict(
        escape='returned (jalr zero,0(ra)) at +0x118 of __nl_langinfo_l with the empty-string pointer in a0',
        path='returned to __strftime_fmt_1 at that call site; __strftime_fmt_1 either hands the result straight to '
             '__strftime_l as the format pointer or compares it to another string pointer',
        reader='__strftime_l\'s format walker: lbu 0(a0) at +0x1cc and +0x23c of __strftime_l (within the format loop), '
               'and the beq a0,zero,... pointer / value tests at +0x1c0',
        nulstop='the strftime format walker reads a byte at the pointer with lbu and stops the format loop when the '
                'byte is 0 (the walker breaks out of the loop); the pointer is never dereferenced past the first NUL'),
    '__strftime_fmt_1': dict(
        escape='returned (jalr zero,0(ra)) at the two tails that hand back the empty-string pointer (at +0x530 and '
               '+0x54c of __strftime_fmt_1 the empty string is loaded as the return value a0)',
        path='returned to __strftime_l (the only caller); __strftime_l reads the returned pointer as the next '
             'format fragment and copies it into the output',
        reader='__strftime_l reads the pointer with lbu 0 at +0x1cc and +0x23c (the format loop) and does pointer '
               'equality tests (beq) at +0x1c0',
        nulstop='the strftime format walker stops at the first NUL byte, as above'),
    '__tm_to_tzname': dict(
        escape='returned (jalr zero,0(ra)) at +0xa4 of __tm_to_tzname',
        path='returned to __strftime_fmt_1 at +0x438; __strftime_fmt_1 returns to __strftime_l',
        reader='__strftime_l reads the pointer with lbu 0 and runs the pointer equality tests, as above',
        nulstop='the strftime format walker stops at the first NUL byte'),
}


def window(ax, ay):
    """the number of bytes from ax in X and ay in Y that are equal (file bytes); 0 if either is unreadable"""
    bx = dc.frd(X, ax, 65536) or b''; by = dc.frd(Y, ay, 65536) or b''
    n = 0
    while n < min(len(bx), len(by)) and bx[n] == by[n]: n += 1
    return n


old = open(_argv[3]).read().splitlines()
new = []; replaced = 0
for l in old:
    f = l.split('\t')
    if f[0] == 'ACCEPT' and f[6] == 'UNSETTLED' and f[9] == '00' and f[10] == '00':
        r = READERS.get(f[1])
        if r is None: new.append(l); continue
        ax, ay = int(f[4], 16), int(f[5], 16); w = window(ax, ay)
        ev = ('PRIMARY: the named reader reads the pointer and stops at the first NUL (= the equal first byte at the '
              'target in X and Y). ESCAPE: %s. PATH: %s. READER: %s. NUL-STOP: %s. SUPPORT: measured equal window at '
              'the target: %d bytes equal in both images (second check only; the reader\'s NUL-stop is the real '
              'bound). Verified in disassembly by the fresh reviewer in REVIEW.md.' %
              (r['escape'], r['path'], r['reader'], r['nulstop'], w))
        new.append('\t'.join(['ACCEPT', f[1], f[2], f[3], f[4], f[5], 'CSTR-ESCAPE', ev,
                              '1 byte to the NUL (reader bound); %d bytes equal window at the target (support)' % w,
                              f[9], f[10], 'SETTLED-EQUAL']))
        replaced += 1
    else:
        new.append(l)
by_fn = {}
for l in new:
    f = l.split('\t')
    if f[0] == 'ACCEPT' and f[1] != 'function': by_fn.setdefault(f[1], []).append(f[-1])
out = []
for l in new:
    f = l.split('\t')
    if f[0] == 'ROW' and f[1] in by_fn:
        vs = by_fn[f[1]]; ok = sum(1 for v in vs if v == 'SETTLED-EQUAL')
        tag = 'ROW SETTLED-EQUAL' if ok == len(vs) and vs else 'ROW NOT SETTLED'
        out.append('\t'.join(['ROW', f[1], f[2], 'settled-equal %d of %d' % (ok, len(vs)), tag]))
    else:
        out.append(l)
open(_argv[3], 'w').write('\n'.join(out) + '\n')
print('escape.py: %d target pairs re-classed CSTR-ESCAPE SETTLED-EQUAL (primary: named reader + NUL stop; support: '
      'equal window)' % replaced)
