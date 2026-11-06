#!/usr/bin/env python3
"""kitrange.py -- run cmpkit 86da41d3ef68's own compare (strictcmp3.tcmp + strictcmp3.verdict, the code behind
`strictcmp3.py cmp`) on code given BY ADDRESS: a whole function or a sub-range, in two images or in one. Use it where
`strictcmp3.py cmp` cannot pair the code: the two copies have different names, a range is only part of a function, or
one side has an inserted word (compare the parts before and after it). Read-only.

usage: kitrange.py KITDIR SPEC.tsv
  KITDIR: a directory holding exactly the files of cmpkit 86da41d3ef68 (checked: sha256(SHA256SUMS) starts 86da41d3ef68,
          and every file in SHA256SUMS has its sha256).
  SPEC.tsv rows (tab-separated, '#' lines skipped): label  TAG1=ELF1  ADDR1  TAG2=ELF2  ADDR2  LENGTH
          ADDR and LENGTH in hex (0x...); LENGTH bytes are compared from each address.
Output: one row per spec row, the columns of `strictcmp3.py cmp` (verdict = the combined verdict, words-only last),
then `realwords` = the word offsets bytecmp counts as REAL differences (each `+off:word1/word2`), so a claim of the form
"equal except at <named words>" can be checked word by word; then one CSTR row per C-string acceptance."""
import sys, os, hashlib, importlib.util

def main():
    kit, spec = sys.argv[1], sys.argv[2]
    sums = open(os.path.join(kit, 'SHA256SUMS'), 'rb').read()
    kid = hashlib.sha256(sums).hexdigest()[:12]
    if kid != '86da41d3ef68': raise SystemExit('kitrange.py: kit id %s, want 86da41d3ef68' % kid)
    for line in sums.decode().splitlines():
        h, f = line.split()
        if hashlib.sha256(open(os.path.join(kit, f), 'rb').read()).hexdigest() != h:
            raise SystemExit('kitrange.py: %s does not match SHA256SUMS' % f)
    sp = importlib.util.spec_from_file_location('strictcmp3', os.path.join(kit, 'strictcmp3.py'))
    s3 = importlib.util.module_from_spec(sp); sp.loader.exec_module(s3)
    bc = s3._bc
    I, rows = {}, []
    for line in open(spec):
        if not line.strip() or line.startswith('#'): continue
        lab, i1, a1, i2, a2, n = line.rstrip('\n').split('\t')
        t1, p1 = i1.split('=', 1); t2, p2 = i2.split('=', 1)
        for t, p in ((t1, p1), (t2, p2)):
            if t not in I: I[t] = (s3.Img(p), p)
            elif I[t][1] != p: raise SystemExit('kitrange.py: tag %s names two files' % t)
        rows.append((lab, t1, int(a1, 16), t2, int(a2, 16), int(n, 16)))
    print('# kit cmpkit %s (strictcmp3.tcmp / strictcmp3.verdict, called by address)' % kid)
    for t in sorted(I):
        print('# %s = %s sha256 %s' % (t, I[t][1], s3.sha(I[t][1])[:12]))
    print('# C-string rule %s' % ('OFF (STRICT_LITERAL=1)' if s3.LITERAL else 'ON (default)'))
    print('label\tpair\taddr1\taddr2\tlength\tverdict\tpcrel\treal\tunmeasured\ttargets(full-bytes-eq,got-value-or-tls-index-eq,'
          'cstr-eq)\ttarget-differ\tvalue/full-bytes/NAME-ONLY acceptances\tC-string acceptances\tdiffering targets printed'
          '\twords-only\trealwords')
    II = {t: v[0] for t, v in I.items()}
    for lab, t1, a1, t2, a2, n in rows:
        fb = []
        v, c, t3, diff = s3.tcmp(II, t1, a1, t2, a2, n, fb)
        realw = []
        b1, b2 = s3.frd(II[t1], a1, n), s3.frd(II[t2], a2, n)
        if c is not None and b1 is not None and b2 is not None:
            # the same word classification as bytecmp-1480ca2faea0.py cmp() (lines 157-177), listing the REAL words
            w1, w2 = bc['words'](b1), bc['words'](b2); st = bc['flow_states'](w1); UNK = bc['UNKNOWN']
            for i, ((o, x, nb), (_, y, _)) in enumerate(zip(w1, w2)):
                if x == y: continue
                if nb == 4 and (x & 0x7f) == (y & 0x7f):
                    op = x & 0x7f; rs1 = (x >> 15) & 31
                    mask = 0x01fff07f if op in (0x23, 0x27) else 0x000fffff
                    lo12 = op in (0x13, 0x03, 0x23, 0x67, 0x07, 0x27) and (x & mask) == (y & mask)
                    j = st[i].get(rs1)
                    if op in (0x17, 0x6f) and ((x >> 7) & 31) == ((y >> 7) & 31): continue
                    if lo12 and j is not None and j >= 0: continue
                    if lo12 and j == UNK: continue
                realw.append('+%#x:%08x/%08x' % (o, x, y))
        print('%s\t%s:%s\t%#x\t%#x\t%#x\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\tprinted %d of %d targets\t%s\t%s'
              % (lab, t1, t2, a1, a2, n, s3.verdict(v, diff), c[0] if c else '', c[1] if c else '', c[2] if c else '', t3,
                 diff if diff else 0, s3.fb_text(fb),
                 ' '.join('%s@%#x|%#x=%r' % (o, x1, x2, s) for k, o, x1, x2, s in fb if k == 'cstr'), len(diff), len(diff),
                 v, ' '.join(realw) if realw else '-'))
        for r in s3.cstr_rows(lab, '%s:%s' % (t1, t2), fb): print(r)

if __name__ == '__main__':
    main()
