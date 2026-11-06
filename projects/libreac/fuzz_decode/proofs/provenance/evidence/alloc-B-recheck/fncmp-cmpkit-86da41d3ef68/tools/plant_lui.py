#!/usr/bin/env python3
"""plant_lui.py -- the two controls the lui classification must REFUSE, each a FILE copy of the cgif-B unstripped twin
with two or one instruction words changed (written to PLANTDIR, never into the record):
  (a) LUI-STORE-BASE: in __asan::InitializeAsanInterceptors, `lui a2, 0x38e` (+0x3c) feeds MmapOrDie's size through
      `addiw a0, a2, -0x4d8` (+0x44). The plant makes the lui value a STORE BASE through `add`:
        +0x44  addiw a0, a2, -0x4d8  ->  add a0, a2, zero      (0x00060533)
        +0x48  mv a2, zero           ->  sd zero, 0(a0)        (0x00053023)
  (b) LUI-ADDR-ARG: in __asan::SealedReserveShadow, `lui a0, 0x104 ; addiw a3, a0, 0x22` (+0x6c / +0x74) is
      internal_mmap's `int flags`. The plant also passes it as internal_mmap's `void *addr`:
        +0x7c  mv a0, s1             ->  mv a0, a3             (0x00068513)
Each original word is checked before it is changed. Writes planted-a.elf, planted-b.elf and plant-targets.tsv (the two
planted targets in luitrace's input format) to PLANTDIR, and prints their sha256. usage: PLANTDIR=... plant_lui.py"""
import hashlib, os, shutil, struct, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common
from elftools.elf.elffile import ELFFile

PLANTS = {
    'a': ('_ZN6__asan26InitializeAsanInterceptorsEv', [(0x44, None, 0x00060533),
                                                         (0x48, None, 0x00053023)], 0x3c, '0x38e000'),
    'b': ('_ZN6__asan19SealedReserveShadowEv', [(0x7c, None, 0x00068513)], 0x74, '0x104022'),
}
EXPECT = {('a', 0x44): 'addiw a0, a2, -0x4d8', ('a', 0x48): 'mv a2, zero', ('b', 0x7c): 'mv a0, s1'}


def main():
    out = os.environ.get('PLANTDIR')
    if not out:
        raise SystemExit('PLANTDIR is not set')
    os.makedirs(out, exist_ok=True)
    src = common.CGIF_B_TWIN
    e = ELFFile(open(src, 'rb'))
    sym = {}
    for s in e.get_section_by_name('.symtab').iter_symbols():
        if s['st_info']['type'] == 'STT_FUNC' and s['st_size'] > 0:
            sym.setdefault(s.name, (s['st_value'], s['st_size']))
    loads = [(s['p_vaddr'], s['p_offset'], s['p_filesz']) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
    foff = lambda va: [o + va - v for v, o, n in loads if v <= va < v + n][0]
    from capstone import Cs, CS_ARCH_RISCV, CS_MODE_RISCV64, CS_MODE_RISCVC
    md = Cs(CS_ARCH_RISCV, CS_MODE_RISCV64 | CS_MODE_RISCVC)
    rows = ['member\tX addr\tword\tvalues']
    for tag, (fn, edits, word, val) in PLANTS.items():
        a, z = sym[fn]
        data = bytearray(open(src, 'rb').read())
        for off, _unused, new in edits:
            fo = foff(a + off)
            old = bytes(data[fo:fo + 4])
            ins = next(md.disasm(old, a + off))
            have = '%s %s' % (ins.mnemonic, ins.op_str)
            if have != EXPECT[(tag, off)]:
                raise SystemExit('plant %s +%#x: found %r, expected %r' % (tag, off, have, EXPECT[(tag, off)]))
            data[fo:fo + 4] = struct.pack('<I', new)
            ins2 = next(md.disasm(bytes(data[fo:fo + 4]), a + off))
            print('plant %s: %s +%#x  %s  ->  %s %s' % (tag, fn, off, have, ins2.mnemonic, ins2.op_str))
        p = os.path.join(out, 'planted-%s.elf' % tag)
        open(p, 'wb').write(data)
        print('  %s sha256 %s' % (p, hashlib.sha256(data).hexdigest()[:16]))
        rows.append('%s\t%#x\t%#x\t%s in .bss | %s in .bss' % (fn, a, word, val, val))
    open(os.path.join(out, 'plant-targets.tsv'), 'w').write('\n'.join(rows) + '\n')
    print('original %s sha256 %s' % (src, hashlib.sha256(open(src, 'rb').read()).hexdigest()[:16]))


if __name__ == '__main__':
    main()
