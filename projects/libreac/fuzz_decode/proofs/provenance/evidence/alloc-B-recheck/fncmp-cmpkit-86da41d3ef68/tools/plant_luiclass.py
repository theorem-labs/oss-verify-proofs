#!/usr/bin/env python3
"""plant_luiclass.py -- runs the two controls of plant_lui.py through the lui settlement (luitrace.py, then luiclass.py):
  (a) LUI-STORE-BASE  (a lui value feeds a store base through `add`)
  (b) LUI-ADDR-ARG    (a lui value passed as a `void *addr` parameter)
Each planted cgif-B copy stands in for CGIF_B_TWIN (the real decode-B twin is the other image) in a scratch record (its own
scans/, the record's out/ read only). Both planted rows must come out NOT CERTIFIED. usage: PLANTDIR=... plant_luiclass.py"""
import os, shutil, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common

T = os.path.dirname(os.path.abspath(__file__))


def main():
    pd = os.environ.get('PLANTDIR')
    if not pd:
        raise SystemExit('PLANTDIR is not set')
    subprocess.run([sys.executable, os.path.join(T, 'plant_lui.py')], check=True)
    rows = [l.rstrip('\n').split('\t') for l in list(open(os.path.join(pd, 'plant-targets.tsv')))[1:]]
    res = {}
    for tag, row in zip(('a', 'b'), rows):
        rec = tempfile.mkdtemp(prefix='luiclass-plant-%s-' % tag, dir=pd)
        os.makedirs(os.path.join(rec, 'scans'))
        os.symlink(common.OUT, os.path.join(rec, 'out'))
        shutil.copy(os.path.join(common.SCANS, 'exposure.tsv'), os.path.join(rec, 'scans'))
        tgt = os.path.join(rec, 'scans', 'plant-%s-targets.tsv' % tag)
        open(tgt, 'w').write('member\tX addr\tword\tvalues\n' + '\t'.join(row) + '\n')
        env = dict(os.environ, CMPREC=rec, CGIF_B_TWIN=os.path.join(pd, 'planted-%s.elf' % tag))
        out = os.path.join(rec, 'scans', 'plant-%s-trace.tsv' % tag)
        subprocess.run([sys.executable, os.path.join(T, 'luitrace.py'), tgt, out], env=env, check=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        subprocess.run([sys.executable, os.path.join(T, 'luiclass.py'), out], env=env, check=True, stdout=subprocess.DEVNULL)
        c = list(open(os.path.join(rec, 'scans', 'luiclass.tsv')))[1].rstrip('\n').split('\t')
        res[tag] = c[6]
        print('plant %s: %s %s V=%s -> %s' % (tag, c[0][:50], c[2], c[3], c[6]))
        tr = list(open(out))[1].rstrip('\n').split('\t')
        print('   luitrace verdict %s; bases X: %s' % (tr[10], tr[7][:200]))
        for u in c[8].split(' ;; '):
            if 'verdict' in u or 'internal_mmap' in u or 'BASE' in u:
                print('   unsettled: %s' % u[:300])
    ok = all(v.startswith('NOT CERTIFIED') for v in res.values())
    print('plant_luiclass: %s' % ('both controls REFUSED (NOT CERTIFIED)' if ok else 'A CONTROL WAS NOT REFUSED: %s' % res))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
