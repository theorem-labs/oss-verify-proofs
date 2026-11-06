#!/usr/bin/env python3
"""refs.py KIT_DIR ELF ADDR[,ADDR...] -- which code of ELF forms each address, and how. Read-only.

For every sized STT_FUNC of ELF it runs the comparison kit's own pc-relative target pass (`targets` of
repin_check.py, loaded through strictcmp3.py / drvcmp.py of KIT_DIR, over bytecmp's words), which pairs each auipc with
the addi / load / store / jalr words its result reaches. It prints one row per word whose target is one of the given
addresses: the function, the word's offset in it, the kind, and capstone's text of the word and of the auipc that
built it. A row `(none)` means no code of the image forms that address this way.
usage: refs.py KIT_DIR ELF 0x1d038,0x10480,...   (addresses in hex)"""
import importlib.util, os, sys
import capstone

kit, elf, want = sys.argv[1:4]
sp = importlib.util.spec_from_file_location('strictcmp3_kit', os.path.join(kit, 'strictcmp3.py'))
S = importlib.util.module_from_spec(sp); sp.loader.exec_module(S)
md = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)
addrs = [int(x, 0) for x in want.split(',')]
I = S.Img(elf)
hits = {a: [] for a in addrs}
fns = sorted({(v, z, nm) for v, z, nm, t in I.syms if t == 'STT_FUNC' and z > 0})
for v, z, nm in fns:
    b = S.frd(I, v, z)
    if b is None:
        continue
    w = S.bc_words(b)
    try:
        tg = S._g['targets'](v, b)
    except Exception as e:                      # a function the pass cannot read is reported, never skipped silently
        print('# %s at %#x: targets failed: %s' % (nm, v, e))
        continue
    st = S.bc_states(w)
    for i, (kind, t) in tg.items():
        if t not in hits:
            continue
        off, word, n = w[i]
        txt = next(md.disasm(b[off:off + n], v + off), None)
        hi = ''
        if kind != 'jal' and st[i] is not None:
            j = st[i].get((word >> 15) & 31)
            if j is not None:
                ho, hw, hn = w[j]
                a2 = next(md.disasm(b[ho:ho + hn], v + ho), None)
                hi = '; built by +%#x %s %s' % (ho, a2.mnemonic, a2.op_str) if a2 else ''
        hits[t].append('%s+%#x (pc %#x) %s %s%s' % (nm, off, v + off, txt.mnemonic if txt else '?',
                                                    txt.op_str if txt else '', hi))
print('# %s sha256 %s' % (elf, S.sha(elf)[:12]))
for a in addrs:
    print('ADDR\t%#x\t%d reader(s)' % (a, len(hits[a])))
    for h in hits[a] or ['(none)']:
        print('    %s' % h)
