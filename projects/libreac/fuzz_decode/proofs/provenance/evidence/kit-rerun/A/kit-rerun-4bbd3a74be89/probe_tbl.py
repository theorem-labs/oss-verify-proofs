#!/usr/bin/env python3
"""probe_tbl.py KIT_DIR -- read-only probe of the one target strictcmp2 16982e3ef42b reports as data-differs in this
run: Allocator::Allocate +0xdc. It prints the target address in both images, the section, the region strictcmp2
compares (to the next FUNC / OBJECT symbol), the 64 bytes at the target in each image, and the words around +0xdc that
read it, so the bounded index can be read off the code (cmpkit README:153-160, KNOWN FALSE-DIFFERENCE class: an unnamed
.rodata target read through a bounded index is compared on its whole region, so equal tables can read data-differs)."""
import os, sys, importlib.util
KIT = os.path.abspath(sys.argv[1])
sys.dont_write_bytecode = True
sp = importlib.util.spec_from_file_location('s2', os.path.join(KIT, 'strictcmp2.py'))
S = importlib.util.module_from_spec(sp); sp.loader.exec_module(S)
C = 'DONOR_TWIN'
A = 'DECODE_A_TWIN'
FN, OFF = '_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb', 0xdc
I = {'C': S.Img(C), 'A': S.Img(A)}
print('# kit', KIT, 'strictcmp2 sha256', S.sha(os.path.join(KIT, 'strictcmp2.py'))[:12])
print('# C', C, S.sha(C)[:12]); print('# A', A, S.sha(A)[:12])
tgt = {}
for k in 'CA':
    a, n = I[k].fsym(FN); b = S.frd(I[k], a, n); t = S.targets(a, b); w = S.bc_words(b)
    idx = [i for i, (o, x, nb) in enumerate(w) if o == OFF][0]
    x = t[idx][1]; r = S.region(I[k], x)
    tgt[k] = x
    print('%s %s +%#x kind %s target %#x sec %s qres %s region %s bytes' %
          (k, FN[13:40], OFF, t[idx][0], x, I[k].sec(x), S.qres(I[k], x), len(r) if r else r))
    print('   64B at target:', S.frd(I[k], x, 64).hex())
    print('   words +%#x..+%#x:' % (w[max(idx - 4, 0)][0], w[min(idx + 6, len(w) - 1)][0]),
          ' '.join('%#x:%08x' % (w[j][0], w[j][1]) for j in range(max(idx - 4, 0), min(idx + 7, len(w)))))
print('C vs A, the 64 bytes at the target are equal:', S.frd(I['C'], tgt['C'], 64) == S.frd(I['A'], tgt['A'], 64))
print('C vs A, the 65th byte (outside the table):',
      S.frd(I['C'], tgt['C'] + 64, 1).hex(), S.frd(I['A'], tgt['A'] + 64, 1).hex())
