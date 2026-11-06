#!/usr/bin/env python3
"""plantlui.py KIT_DIR ELF FUNCTION OUT -- the positive control of luicomb.py: a COPY of ELF whose FUNCTION begins with
a planted `lui a0,0x11 ; lui a1,0x2 ; add a0,a0,a1 ; ld a0,0(a0)`, the shape of the KNOWN FAIL-OPEN (two lui values
combined into one load base). The base is then 0x11000 + 0x2000 = 0x13000, a statically known address, so luicomb.py
must report the site with that value and the symbol it names. ELF is only read; OUT is written.
usage: plantlui.py KIT_DIR ELF FUNCTION OUT"""
import importlib.util, os, shutil, struct, sys

KIT, ELF, FN, OUT = sys.argv[1:5]
sp = importlib.util.spec_from_file_location('strictcmp3_kit', os.path.join(KIT, 'strictcmp3.py'))
S = importlib.util.module_from_spec(sp); sp.loader.exec_module(S)
WORDS = [0x00011537, 0x000025b7, 0x00b50533, 0x00053503]
TEXT = ['lui a0, 0x11', 'lui a1, 0x2', 'add a0, a0, a1', 'ld a0, 0(a0)']
I = S.Img(ELF)
s = I.fsym(FN)
if not s:
    raise SystemExit('plantlui: %s has no function %s' % (ELF, FN))
a, n = s
if n < 4 * len(WORDS):
    raise SystemExit('plantlui: %s is only %d bytes' % (FN, n))
off = next((g['p_offset'] + (a - g['p_vaddr']) for g in I.e.iter_segments()
            if g['p_type'] == 'PT_LOAD' and g['p_vaddr'] <= a < g['p_vaddr'] + g['p_filesz']), None)
if off is None:
    raise SystemExit('plantlui: %s at %#x is not file-backed' % (FN, a))
shutil.copyfile(ELF, OUT)
d = bytearray(open(OUT, 'rb').read())
for i, w in enumerate(WORDS):
    struct.pack_into('<I', d, off + 4 * i, w)
open(OUT, 'wb').write(d)
print('plantlui: %s (sha256 %s) -> %s (sha256 %s): the first %d words of %s at %#x are now %s; the load base is '
      '%#x + %#x = %#x' % (os.path.basename(ELF), S.sha(ELF)[:12], os.path.basename(OUT), S.sha(OUT)[:12],
                           len(WORDS), FN, a, ' ; '.join(TEXT), 0x11000, 0x2000, 0x13000))
