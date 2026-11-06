#!/usr/bin/env python3
"""BY-ADDRESS driver for cmpkit 86da41d3ef68's strictcmp3.py (sha256 65688e94214a): every row is one call of the
kit's own tcmp / verdict / fb_text / cstr_rows on (address in image 1, address in image 2, size), printed in
strictcmp3 cmp's columns. No compare rule lives here.
usage: byaddr3.py KITDIR TAG1=ELF1 TAG2=ELF2 ROWS...   ROW = label:0xADDR1:0xADDR2:SIZE (SIZE in bytes, decimal)
The kit's SHA256SUMS is checked and its id (first 12 hex of sha256(SHA256SUMS)) must be 86da41d3ef68."""
import sys, os, hashlib, subprocess, importlib.util

kit = os.path.abspath(sys.argv[1])
if subprocess.run(['sha256sum', '-c', '--quiet', 'SHA256SUMS'], cwd=kit).returncode:
    sys.exit('byaddr3: the kit copy does not match its SHA256SUMS')
kid = hashlib.sha256(open(os.path.join(kit, 'SHA256SUMS'), 'rb').read()).hexdigest()[:12]
if kid != '86da41d3ef68':
    sys.exit('byaddr3: kit id %s is not 86da41d3ef68' % kid)
spec = importlib.util.spec_from_file_location('strictcmp3', os.path.join(kit, 'strictcmp3.py'))
S = importlib.util.module_from_spec(spec)
spec.loader.exec_module(S)
(t1, p1), (t2, p2) = [x.split('=', 1) for x in sys.argv[2:4]]
I = {t1: S.Img(p1), t2: S.Img(p2)}
print('# kit cmpkit %s, strictcmp3.py sha256 %s' % (kid, S.sha(os.path.join(kit, 'strictcmp3.py'))[:12]))
for k, p in ((t1, p1), (t2, p2)):
    print('# %s = %s sha256 %s' % (k, p, S.sha(p)[:12]))
print('# C-string rule %s' % ('OFF (STRICT_LITERAL=1)' if S.LITERAL else 'ON (default)'))
print('fn\tpair\taddr1\taddr2\tsize1\tsize2\tverdict\tpcrel\treal\tunmeasured\ttargets(full-bytes-eq,got-value-or-tls-index-eq,'
      'cstr-eq)\ttarget-differ\tvalue/full-bytes/NAME-ONLY acceptances\tC-string acceptances\tdiffering targets printed\twords-only')
for row in sys.argv[4:]:
    lab, a1, a2, n = row.split(':')
    a1, a2, n = int(a1, 16), int(a2, 16), int(n)
    fb = []
    v, c, t3, diff = S.tcmp(I, t1, a1, t2, a2, n, fb)
    print('%s\t%s:%s\t%#x\t%#x\t%d\t%d\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\tprinted %d of %d targets\t%s'
          % (lab, t1, t2, a1, a2, n, n, S.verdict(v, diff), c[0] if c else '', c[1] if c else '', c[2] if c else '', t3,
             diff if diff else 0, S.fb_text(fb),
             ' '.join('%s@%#x|%#x=%r' % (o, x1, x2, s) for kk, o, x1, x2, s in fb if kk == 'cstr'), len(diff), len(diff), v))
    for r in S.cstr_rows(lab, '%s:%s' % (t1, t2), fb):
        print(r)
