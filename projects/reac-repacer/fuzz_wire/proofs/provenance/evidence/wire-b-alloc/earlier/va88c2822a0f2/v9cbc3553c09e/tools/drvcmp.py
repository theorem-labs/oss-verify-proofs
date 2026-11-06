#!/usr/bin/env python3
"""drvcmp.py -- per-function byte compare of named functions between ELF images. Read-only.

Reuses, without running their mains (these copies differ only in comments and in host paths read from the environment):
  - bytecmp.py 1480ca2faea0 (tool registry commit 797e8971d27d, tools/bytecmp/1480ca2faea0/bytecmp.py): load / words /
    auipc_states / cmp, everything above its `base = {` line;
  - repin_check.py 9cbc3553c09e (same commit, tools/repin_check/9cbc3553c09e/repin_check.py): class Img (lines 31-59)
    and sx / targets / tcmp / w_off (lines 188-237), its target pass: every pc-relative target (jal, auipc+lo12 bound
    by bytecmp's MUST dataflow) is resolved to symbol+offset on both images and compared; a target with no symbol is
    compared by its bytes.
usage: drvcmp.py twins STRIPPED UNSTRIPPED ...      (PT_LOAD byte equality of stripped vs unstripped twin)
       drvcmp.py cmp FNLIST TAG1=ELF1 TAG2=ELF2 ... PAIRS   (PAIRS: comma list T1:T2)"""
import sys, os, bisect, hashlib
from elftools.elf.elffile import ELFFile

HERE = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(HERE, 'bytecmp-1480ca2faea0.py')).read().split('\n')
_bc = {}
exec('\n'.join(_src[:[i for i, l in enumerate(_src) if l.startswith('base = {')][0]]), _bc)
bc_words, bc_cmp, bc_states = _bc['words'], _bc['cmp'], _bc['auipc_states']
_rc = open(os.path.join(HERE, 'repin_check-9cbc3553c09e.py')).read().split('\n')
_g = dict(ELFFile=ELFFile, bisect=bisect, bc_words=bc_words, bc_cmp=bc_cmp, bc_states=bc_states)
exec('\n'.join(_rc[30:59]), _g)      # lines 31-59: class Img
exec('\n'.join(_rc[187:237]), _g)    # lines 188-237: sx, targets, tcmp, w_off
Img, tcmp = _g['Img'], _g['tcmp']

def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()

def twins(a, b):
    la = [(g['p_vaddr'], g['p_memsz'], g.data()) for g in ELFFile(open(a, 'rb')).iter_segments() if g['p_type'] == 'PT_LOAD']
    lb = [(g['p_vaddr'], g['p_memsz'], g.data()) for g in ELFFile(open(b, 'rb')).iter_segments() if g['p_type'] == 'PT_LOAD']
    same_hdr = [(x[0], x[1], len(x[2])) for x in la] == [(x[0], x[1], len(x[2])) for x in lb]
    nd = [v1 + i for (v1, _, d1), (v2, _, d2) in zip(la, lb) for i in range(min(len(d1), len(d2))) if d1[i] != d2[i]]
    note = [(s['sh_addr'], s['sh_size']) for s in ELFFile(open(b, 'rb')).iter_sections() if s.name == '.note.gnu.build-id'][0]
    out = [hex(x) for x in nd if not (0x10000 <= x < 0x10040 or note[0] <= x < note[0] + note[1])]
    print('%s %s | %s %s | PT_LOAD layout equal: %s | differing loadable bytes: %d, outside ELF header [0x10000,0x10040) '
          'and .note.gnu.build-id [%#x,%#x): %s'
          % (os.path.basename(a), sha(a)[:12], os.path.basename(b), sha(b)[:12], same_hdr, len(nd), note[0],
             note[0] + note[1], out))

def cmp(fns, imgs, pairs):
    I = {k: Img(p) for k, p in imgs.items()}
    for k, p in imgs.items():
        print('# %s = %s sha256 %s' % (k, p, sha(p)[:12]))
    print('fn\tpair\taddr1\taddr2\tsize1\tsize2\tverdict\tpcrel\treal\tunmeasured\ttargets(rodata-str-eq,jumptab-eq,const-eq)\ttarget-differ')
    for f in fns:
        for k1, k2 in pairs:
            s1, s2 = I[k1].fsym(f), I[k2].fsym(f)
            if not s1 or not s2:
                print('%s\t%s:%s\t%s\t%s\t\t\tABSENT' % (f, k1, k2, s1 and hex(s1[0]), s2 and hex(s2[0])))
                continue
            if s1[1] != s2[1]:
                print('%s\t%s:%s\t%#x\t%#x\t%d\t%d\tSIZE' % (f, k1, k2, s1[0], s2[0], s1[1], s2[1]))
                continue
            v, c, t3, diff = tcmp(I, k1, s1[0], k2, s2[0], s1[1])
            print('%s\t%s:%s\t%#x\t%#x\t%d\t%d\t%s\t%s\t%s\t%s\t%s\t%s'
                  % (f, k1, k2, s1[0], s2[0], s1[1], s2[1], v, c[0] if c else '', c[1] if c else '',
                     c[2] if c else '', t3, diff if diff else 0))

if __name__ == '__main__':
    if sys.argv[1] == 'twins':
        a = sys.argv[2:]
        for i in range(0, len(a), 2):
            twins(a[i], a[i + 1])
    else:
        fns = sys.argv[2].split(',')
        imgs = dict(x.split('=', 1) for x in sys.argv[3:-1])
        pairs = [tuple(x.split(':')) for x in sys.argv[-1].split(',')]
        cmp(fns, imgs, pairs)
