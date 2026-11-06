#!/usr/bin/env python3
"""window.py KIT_DIR FUNCTION ELF [ELF ...] -- every instruction word of FUNCTION in each image: offset, the word's file
bytes and capstone 5.0.7's disassembly. The function is found with the kit's Img.fsym (strictcmp3.py beside KIT_DIR's
drvcmp.py), its bytes read with strictcmp3's frd (file bytes only). Then one line per offset that compares the images'
words: `same`, or `differ` with both words. Read-only."""
import importlib.util, os, sys
import capstone

kit, fn, elfs = sys.argv[1], sys.argv[2], sys.argv[3:]
sp = importlib.util.spec_from_file_location('strictcmp3_kit', os.path.join(kit, 'strictcmp3.py'))
S = importlib.util.module_from_spec(sp); sp.loader.exec_module(S)
md = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)
words = []
for p in elfs:
    I = S.Img(p)
    a, n = I.fsym(fn)
    b = S.frd(I, a, n)
    print('### %s sha256 %s: %s at %#x, %d bytes' % (p, S.sha(p)[:12], fn, a, n))
    w = {}
    for i in md.disasm(b, 0):
        w[i.address] = i.bytes.hex()
        print('  +%#05x  %s  %s %s' % (i.address, i.bytes.hex(), i.mnemonic, i.op_str))
    words.append(w)
if len(words) > 1:
    offs = sorted(set().union(*words))
    diff = [o for o in offs if len({w.get(o) for w in words}) > 1]
    print('### word compare over %d offsets: %d same, %d differ' % (len(offs), len(offs) - len(diff), len(diff)))
    for o in diff:
        print('  +%#05x differ %s' % (o, ' / '.join(w.get(o, '-') for w in words)))
