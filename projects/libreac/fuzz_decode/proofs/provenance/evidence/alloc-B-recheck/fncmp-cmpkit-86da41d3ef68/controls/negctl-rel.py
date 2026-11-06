#!/usr/bin/env python3
"""negctl.py -- repin_check CONTROL (1)/(2) (<agent>'s negctl_frame controls (a) natural, BASELINE, (c) planted call) under
the old repin_check e5487165abb8 tcmp and the kit's (repin_check's tcmp = strictcmp2's). The (c) plant is an in-memory
Img.segs patch, as in negctl_frame.py / ctl.py. Read-only. usage: negctl.py KIT_DIR"""
import os, sys, re, bisect, importlib.util
sys.dont_write_bytecode = True
from elftools.elf.elffile import ELFFile
KIT = os.path.abspath(sys.argv[1])
S = 'driver'
E548 = 'e548/repin_check.py'
env = {}
for l in open(S + '/env.sh'):
    for part in l.strip().split('; '):
        m = re.match(r'([A-Z]+)=(.*)$', part)
        if m: env[m.group(1)] = re.sub(r'\$(\w+)', lambda k: env.get(k.group(1), ''), m.group(2))
FA, DA, DP = env['FA'], env['DA'], env['DP']
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
rc = load('kit_repin_check', os.path.join(KIT, [f for f in os.listdir(KIT) if f.startswith('repin_check') and f.endswith('.py')][0])); s2 = rc.S2
_e = open(E548).read().split('\n')
_g = dict(ELFFile=ELFFile, bisect=bisect, bc_words=s2.bc_words, bc_cmp=s2.bc_cmp, bc_states=s2.bc_states)
exec('\n'.join(_e[30:59]), _g); exec('\n'.join(_e[187:247]), _g)
PASSES = [('repin_check e5487165abb8 (old)', _g['Img'], _g['tcmp']),
          ('kit repin_check %s (tcmp = %s %s)' % (s2.sha(rc.__file__)[:12], os.path.basename(s2.__file__), s2.sha(s2.__file__)[:12]), s2.Img, rc.tcmp)]
for p in (FA, DA, DP): print('# image %s sha256 %s' % (p, s2.sha(p)[:12]))
def patch(I, a, data):
    for k, (v, fz, d) in enumerate(I.segs):
        if v <= a and a + len(data) <= v + fz:
            b = bytearray(d); b[a - v:a - v + len(data)] = data; I.segs[k] = (v, fz, bytes(b)); return
    raise SystemExit('not in a PT_LOAD')
def enc_jal(pc, tgt, rd):
    off = tgt - pc; o = off & 0x1fffff
    return (((o >> 20) & 1) << 31) | (((o >> 1) & 0x3ff) << 21) | (((o >> 11) & 1) << 20) | (((o >> 12) & 0xff) << 12) | (rd << 7) | 0x6f
def run(tag, xp, yp, plant=None):
    for pn, ImgC, tc in PASSES:
        X, Y = ImgC(xp), ImgC(yp); I = {'X': X, 'Y': Y}
        if plant: plant(Y)
        s1, s2_ = X.fsym('main'), Y.fsym('main')
        v, c, t3, diff = tc(I, 'X', s1[0], 'Y', s2_[0], s1[1])
        eq = v in ('EQUAL', 'EQUAL-mod-pcrel') and not diff
        print('%s [%s]: main %#x vs %#x size %d: %s %s fallbacks %s; target-differ %d -> %s\n    %s'
              % (tag, pn, s1[0], s2_[0], s1[1], v, c, t3, len(diff), 'EQUAL' if eq else 'not equal',
                 [tuple(d[:3]) for d in diff]))
run('CONTROL (a) natural FA:DP', FA, DP)
run('BASELINE FA:DA', FA, DA)
def plant_c(Y):
    a, z = Y.fsym('main'); b = Y.rd(a, z); t = s2.targets(a, b)
    mal, fre = Y.fsym('__wrap_malloc')[0], Y.fsym('__wrap_free')[0]
    for i, (o, x, n) in enumerate(s2.bc_words(b)):
        if n == 4 and x & 0x7f == 0x6f and i in t and t[i][1] == mal:
            patch(Y, a + o, enc_jal(a + o, fre, (x >> 7) & 31).to_bytes(4, 'little')); return
run('CONTROL (c) planted DA main+0x50 jal __wrap_malloc -> __wrap_free', FA, DA, plant_c)
