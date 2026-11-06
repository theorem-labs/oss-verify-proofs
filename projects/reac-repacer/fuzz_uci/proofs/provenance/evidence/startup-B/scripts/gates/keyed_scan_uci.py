#!/usr/bin/env python3
"""keyed_scan_uci.py - the keyed-table (stack_malloc class) gate of decode B's gates_dec.py (G5) / keyed_scan2.py,
with fuzz_uci B's own numbers (the image-B start-up gate set). Reads only; writes nothing.

  1. fuzz_uci B's own __asan_stack_malloc_* symbols, from the unstripped twin's .symtab (pyelftools): T0.4 item 1 says
     exactly one class, __asan_stack_malloc_1 at 0x3c1b8.
  2. CONTROL FIRST: the same scan on cgif's released lib/A/AF0l.v (A classes 0x3c8a4 / 0x3ca34) and lib/YF0l.v
     (B classes 0x3c8d4 / 0x3ca64) must find cgif's rows (the scan does detect them).
  3. The files given: 0 literals equal to any cgif class address, in hex (0x.., 0X..) AND decimal; every line that
     names stack_malloc is listed (decode's gate demanded 0 of any kind).
  usage: keyed_scan_uci.py TWIN CGIF_LIB FILE.v ...      exit 0 = control detects and 0 forbidden literals, else 1
"""
import os
import re
import sys

from elftools.elf.elffile import ELFFile

BAD = {0x3c8a4: 'cgif A __asan_stack_malloc_1', 0x3ca34: 'cgif A __asan_stack_malloc_2',
       0x3c8d4: 'cgif B __asan_stack_malloc_1', 0x3ca64: 'cgif B __asan_stack_malloc_2'}


def scan(path):
    t = open(path).read()
    hits = []
    for v, lab in BAD.items():
        for pat in ('0x%x' % v, '0x%X' % v, '0X%x' % v, str(v)):
            for m in re.finditer(r'(?<![0-9A-Za-z_])' + re.escape(pat) + r'(?![0-9A-Za-z_])', t):
                hits.append((os.path.basename(path), t[:m.start()].count('\n') + 1, pat, lab))
    names = [(t[:m.start()].count('\n') + 1, m.group(0).strip()[:110]) for m in re.finditer(r'.*stack_malloc.*', t)]
    return hits, names


def main():
    twin, clib, files = sys.argv[1], sys.argv[2], sys.argv[3:]
    print('== fuzz_uci B own __asan_stack_malloc_* symbols (twin .symtab %s)' % twin)
    st = ELFFile(open(twin, 'rb')).get_section_by_name('.symtab')
    sm = sorted((s['st_value'], s.name, s['st_size'], s['st_info']['type']) for s in st.iter_symbols()
                if 'stack_malloc' in s.name)
    for a, n, z, ty in sm:
        print('   %#x %s size %d %s' % (a, n, z, ty))
    own = [(a, n) for a, n, z, ty in sm if ty == 'STT_FUNC']
    print('   classes defined (STT_FUNC): %d  -> T0.4 item 1 (one class, __asan_stack_malloc_1 @0x3c1b8): %s'
          % (len(own), own == [(0x3c1b8, '__asan_stack_malloc_1')]))
    print("== CONTROL FIRST: cgif's released lib/A/AF0l.v and lib/YF0l.v (the scan must find cgif's class rows)")
    det = True
    for c in ('A/AF0l.v', 'YF0l.v'):
        h, nm = scan(os.path.join(clib, c))
        print('   %-9s forbidden-literal hits %d: %s' % (c, len(h), h))
        print('   %-9s stack_malloc lines %d: %s' % (c, len(nm), nm[:4]))
        det = det and bool(h)
    print('   control detects (literal hits in both files): %s' % ('YES' if det else 'NO'))
    print('== the fuzz_uci B files')
    tot = 0
    for f in files:
        h, nm = scan(f)
        tot += len(h)
        print('   %-6s forbidden %d  stack_malloc lines %d  %s %s' % (os.path.basename(f)[:-2], len(h), len(nm),
                                                                   h if h else '', nm if nm else ''))
    print('   TOTAL forbidden literals in %d files: %d -> %s' % (len(files), tot, 'PASS' if tot == 0 else 'FAIL'))
    # the two page-floor literals recount.py counts in YB01 only: cgif's 1531 (0x5fb000/4096) and fuzz_uci B's 1524
    # (0x5f4000/4096), over every file (decimal, whole token)
    for lit, who in ((1531, "cgif's page floor 0x5fb000/4096"), (1524, "fuzz_uci B's page floor 0x5f4000/4096")):
        per = {os.path.basename(f)[:-2]: len(re.findall(r'(?<![0-9A-Za-z_.])%d(?![0-9A-Za-z_])' % lit, open(f).read()))
               for f in files}
        print('   literal %d (%s): total %d %s' % (lit, who, sum(per.values()), {k: v for k, v in per.items() if v}))
    return 0 if (tot == 0 and det) else 1


if __name__ == '__main__':
    raise SystemExit(main())
