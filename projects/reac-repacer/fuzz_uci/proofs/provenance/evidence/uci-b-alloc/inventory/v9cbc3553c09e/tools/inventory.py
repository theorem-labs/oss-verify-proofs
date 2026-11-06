#!/usr/bin/env python3
"""inventory.py -- interceptor inventory of one unstripped image (read-only).

Lists every defined STT_FUNC symbol whose name starts with `__interceptor_`, `___interceptor_` or `__asan_`, and marks
which ones the program code calls directly. Program code = the DWARF subprograms of every CU that is not under
/llvm-project and not musl (bsurvey.py's root rule, B-DONORS.md "Method"). A direct call = a jal (any rd, so tail calls
count) or an auipc+jalr whose target repin_check 9cbc3553c09e's targets() resolves (with the bytecmp that drvcmp.py
loads), a .got cell dereferenced, landing on the start of a FUNC symbol outside the calling function - the same rule as
bsurvey.py's callees(). A trampoline (`__interceptor_trampoline_X`, one `j`) that the program calls directly marks its
jump target as "via trampoline". Register-indirect call sites in the program code are counted, not followed.
usage: inventory.py UNIT_NAME ELF OUT_TSV     (prints a summary; OUT_TSV gets one row per symbol, then the direct
callees of the program code that are not in the inventory)"""
import sys, os, re, importlib.util
from elftools.elf.elffile import ELFFile
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('drvcmp', os.path.join(HERE, 'drvcmp.py'))
dc = importlib.util.module_from_spec(spec); spec.loader.exec_module(dc)
targets, bc_words = dc._g['targets'], dc.bc_words
unit, p, out = sys.argv[1:4]
X = dc.Img(p)
PFX = re.compile(r'^(___interceptor_|__interceptor_|__asan_)')
e = ELFFile(open(p, 'rb'))
funcs = []   # (name, addr, size, bind)
for s in e.get_section_by_name('.symtab').iter_symbols():
    if s['st_info']['type'] == 'STT_FUNC' and s['st_shndx'] != 'SHN_UNDEF' and s['st_value'] > 0:
        funcs.append((s.name, s['st_value'], s['st_size'], s['st_info']['bind']))
starts = {}
for n, a, z, b in funcs:
    if z > 0: starts.setdefault(a, []).append((n, z))
byaddr = {}
for n, a, z, b in funcs: byaddr.setdefault(a, set()).add(n)

# program code
roots, cus = {}, set()
for cu in e.get_dwarf_info().iter_CUs():
    top = cu.get_top_DIE(); name = top.attributes['DW_AT_name'].value.decode()
    if name.startswith('/llvm-project') or '/musl' in name or name.startswith('src/') and 'musl' in name:
        continue
    for die in top.iter_children():
        if die.tag == 'DW_TAG_subprogram' and 'DW_AT_low_pc' in die.attributes:
            lo = die.attributes['DW_AT_low_pc'].value
            if lo in starts:
                roots[lo] = starts[lo][0]; cus.add(name)
calls = {}; ind = 0
for a, (rn, z) in roots.items():
    b = X.rd(a, z); w = bc_words(b); t = targets(a, b)
    for i, (o, x, n) in enumerate(w):
        if n != 4: continue
        op = x & 0x7f; rd = (x >> 7) & 31
        if op in (0x6f, 0x67) and i in t:
            tg = t[i][1]
            if X.sec(tg) == '.got': tg = int.from_bytes(X.rd(tg, 8), 'little')
            if tg in starts and not (a <= tg < a + z):
                calls.setdefault(tg, []).append('%s+%#x' % (rn, o))
        elif op == 0x67 and rd != 0:
            ind += 1
via = {}
for a in calls:
    for n, z in starts[a]:
        if n.startswith('__interceptor_trampoline_') and z == 4:
            x = int.from_bytes(X.rd(a, 4), 'little')
            if x & 0x7f == 0x6f:
                tg = a + dc._g['sx'](((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11 | ((x >> 21) & 0x3ff) << 1, 21)
                via.setdefault(tg, set()).add(n)
inv = sorted((f for f in funcs if PFX.match(f[0])), key=lambda f: (f[1], f[0]))
ninv = {f[0] for f in inv}
with open(out, 'w') as f:
    f.write('# unit %s; image %s sha256 %s; program CUs %s; program functions %d; register-indirect call sites in them %d\n'
            % (unit, os.path.basename(p), dc.sha(p)[:12], sorted(cus), len(roots), ind))
    f.write('name\taddr\tsize\tbind\tother names at addr\tprogram calls directly (sites)\tvia directly called trampoline\n')
    for n, a, z, b in inv:
        oth = ','.join(sorted(byaddr[a] - {n}))
        cs = calls.get(a, [])
        f.write('%s\t%#x\t%d\t%s\t%s\t%s\t%s\n' % (n, a, z, b.replace('STB_', ''), oth or '-',
                ('%d: %s' % (len(cs), ' '.join(sorted(cs)))) if cs else 'no', ','.join(sorted(via.get(a, []))) or '-'))
    f.write('# direct callees of the program code outside the inventory\n')
    for a in sorted(calls):
        names = sorted(n for n, _ in starts[a])
        if not any(PFX.match(n) for n in names):
            f.write('%s\t%#x\t\t\t\t%d: %s\t-\n' % ('/'.join(names), a, len(calls[a]), ' '.join(sorted(calls[a]))))
direct = sorted({n for a in calls for n, _ in starts[a]})
print('# %s: inventory %d symbols (%d __asan_*, %d ___interceptor_*, %d __interceptor_* incl. %d trampolines); '
      'program functions %d; direct callees %d (%d in the inventory); register-indirect call sites %d'
      % (unit, len(inv), sum(1 for x in inv if x[0].startswith('__asan_')), sum(1 for x in inv if x[0].startswith('___interceptor_')),
         sum(1 for x in inv if x[0].startswith('__interceptor_')), sum(1 for x in inv if x[0].startswith('__interceptor_trampoline_')),
         len(roots), len(calls), sum(1 for a in calls if any(PFX.match(n) for n, _ in starts[a])), ind))
for k in ('__asan_memset', '__asan_memcpy', '__asan_memmove'):
    s = [x for x in funcs if x[0] == k]
    print('#   %s: %s' % (k, ('PRESENT %#x size %d' % (s[0][1], s[0][2])) if s else 'ABSENT'))
allnames = sorted({(s.name, s['st_value'], s['st_info']['type'].replace('STT_', '')) for s in e.get_section_by_name('.symtab').iter_symbols()
                   if ('memset' in s.name or 'memcpy' in s.name) and s['st_shndx'] != 'SHN_UNDEF'}, key=lambda x: (x[1], x[0]))
print('#   every defined symbol whose name contains memset or memcpy: %s' % ', '.join('%s %#x %s' % x for x in allnames))
