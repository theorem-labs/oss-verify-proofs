#!/usr/bin/env python3
"""dupnames.py KIT_DIR PAIRS.TSV -- read-only: for each of the 7 function pairs, every STT_FUNC symbol of that name in
the TARGET image (decode A unstripped twin) and in the DONOR image (cgif twin), from .symtab AND .dynsym separately,
with address and size. For a name that is NOT unique, every same-size candidate in the target is compared against the
donor function with strictcmp2 (the kit's one compare), so the copy funcpair.py used can be checked. funcpair.py
d37a0f9a14fb keeps only the FIRST symtab entry per name (funcpair.py:52), so a duplicated name can map to the wrong
same-size copy."""
import os, sys, importlib.util
from elftools.elf.elffile import ELFFile
KIT = os.path.abspath(sys.argv[1]); PAIRS = sys.argv[2]
sys.dont_write_bytecode = True
sp = importlib.util.spec_from_file_location('s2', os.path.join(KIT, 'strictcmp2.py'))
S = importlib.util.module_from_spec(sp); sp.loader.exec_module(S)
C = 'DONOR_TWIN'
A = 'DECODE_A_TWIN'
print('# kit', KIT, 'strictcmp2 sha256', S.sha(os.path.join(KIT, 'strictcmp2.py'))[:12])
print('# C (donor)', C, S.sha(C)[:12]); print('# A (target, decode A twin)', A, S.sha(A)[:12])


def table(path):
    """{section name: {symbol name: [(addr, size, type, bind)]}} for .symtab and .dynsym"""
    out = {}
    e = ELFFile(open(path, 'rb'))
    for sec in ('.symtab', '.dynsym'):
        s = e.get_section_by_name(sec)
        d = {}
        if s is not None:
            for sym in s.iter_symbols():
                d.setdefault(sym.name, []).append((sym['st_value'], sym['st_size'],
                                                   sym['st_info']['type'], sym['st_info']['bind']))
        out[sec] = d
    return out


TA, TC = table(A), table(C)
I = {'C': S.Img(C), 'A': S.Img(A)}
rows = [l.split('\t') for l in open(PAIRS).read().splitlines()[1:] if l.strip()]
uniq, dup = [], []
for r in rows:
    fn, daddr, aaddr, size = r[0], int(r[1], 16), int(r[2], 16), int(r[3])
    print()
    print('FUNCTION', fn)
    print('  record pair: donor %#x -> decode A %#x, size %d' % (daddr, aaddr, size))
    cands = {}
    for tag, T in (('C/donor', TC), ('A/target', TA)):
        for sec in ('.symtab', '.dynsym'):
            fun = [c for c in T[sec].get(fn, []) if c[2] == 'STT_FUNC']
            oth = [c for c in T[sec].get(fn, []) if c[2] != 'STT_FUNC']
            print('  %-9s %-8s STT_FUNC %d: %s%s' % (tag, sec, len(fun),
                  ' '.join('%#x/%d/%s' % (v, z, b) for v, z, _, b in fun) or '-',
                  ('   other types: ' + ' '.join('%#x/%d/%s' % (v, z, t) for v, z, t, _ in oth)) if oth else ''))
            if tag == 'A/target':
                for v, z, _, _ in fun:
                    cands[(v, z)] = True
    ucount = {k: len({c[0] for c in TA[k].get(fn, []) if c[2] == 'STT_FUNC'}) for k in ('.symtab', '.dynsym')}
    addrs = {c[0] for k in ('.symtab', '.dynsym') for c in TA[k].get(fn, []) if c[2] == 'STT_FUNC'}
    unique = len(addrs) == 1
    print('  TARGET: %d distinct STT_FUNC address(es) for the name (%s) -> %s' %
          (len(addrs), ' '.join(hex(a) for a in sorted(addrs)), 'UNIQUE' if unique else 'DUPLICATED'))
    same_size = sorted(a for (a, z) in cands if z == size)
    eq = []
    for a in same_size:
        v, c, t3, diff = S.tcmp(I, 'C', daddr, 'A', a, size, [])
        ok = v in ('EQUAL', 'EQUAL-mod-pcrel') and not diff
        print('    candidate %#x (size %d): strictcmp2 %s pcrel/real/unmeas %s, target differences %d -> %s'
              % (a, size, v, c, len(diff), 'EQUAL' if ok else 'not equal'))
        if ok: eq.append(a)
    print('    same-size candidates EQUAL under strictcmp2: %s (the pair of record uses %#x)' %
          ([hex(x) for x in eq], aaddr))
    if len(eq) > 1: print('    FINDING: more than one same-size candidate is EQUAL')
    (uniq if unique else dup).append(fn)
print()
print('SUMMARY: unique %d / duplicated %d %s' % (len(uniq), len(dup), [f[:40] for f in dup]))
