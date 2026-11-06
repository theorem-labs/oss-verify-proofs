#!/usr/bin/env python3
"""plant_uciB.py: the CONTROL copy for classify.py on fuzz_uci B (start-up gate set, after plant.py 9a1461e70b54).
fuzz_uci B .text = [0x2fbf0, 0x95b90) (classify.py's own first line), so .text end + 4 = 0x95b94 (decimal 613268).
CODE-role plants (each MUST be a FINDING):
  P1 YF0m.v  Tfib_const_abs `z8 (ANum 0x98f80) 0x90458` (real_memcpy, a jump-target cell) -> 0x95b94
  P2 YF0m.v  DRV_TRACES first pc 0x51a24 -> 0x95b94
  P3 YB12.v  x_memset 0x9085c -> 0x95b94                     (only when YB12.v is in the snapshot)
  P4 YB01.v  HS_tfib_0 register x1 (ra) ELit 550212 (0x86544) -> ELit 613268
DATA-role plant (MUST NOT be a finding, the same value):
  D1 YF0m.v  Tfib_const_abs `z8 (ANum 0x9c8f8) 0x100ffffffff` (asan_flags_dont_use_directly+0, a data cell) -> 0x95b94
  usage: plant_uciB.py SRC_DIR DST_DIR      (copies every file of SRC_DIR, then plants; SRC_DIR is never written)"""
import os
import shutil
import sys

SRC, DST = sys.argv[1], sys.argv[2]
os.makedirs(DST, exist_ok=True)
for fn in os.listdir(SRC):
    if os.path.isfile(os.path.join(SRC, fn)):
        shutil.copyfile(os.path.join(SRC, fn), os.path.join(DST, fn))


def plant(tag, fn, old, new, line_pred=lambda n, l: True, optional=False):
    p = os.path.join(DST, fn)
    if not os.path.exists(p):
        if optional:
            print('not planted %s: %s is not in the snapshot' % (tag, fn))
            return
        raise SystemExit('plant target file missing: %s' % fn)
    ls = open(p).read().split('\n')
    for i, l in enumerate(ls):
        if line_pred(i + 1, l) and old in l:
            ls[i] = l.replace(old, new, 1)
            open(p, 'w').write('\n'.join(ls))
            print('planted %s %s:%d  %s -> %s' % (tag, fn, i + 1, old, new))
            return
    raise SystemExit('plant target not found: %s %s' % (fn, old))


plant('P1-CODE', 'YF0m.v', 'z8 (ANum 0x98f80) 0x90458', 'z8 (ANum 0x98f80) 0x95b94')
plant('P2-CODE', 'YF0m.v', '[[0x51a24; 0x7ee9c]', '[[0x95b94; 0x7ee9c]')
plant('P3-CODE', 'YB12.v', 'x_memset := 0x9085c', 'x_memset := 0x95b94', optional=True)
plant('P4-CODE', 'YB01.v', 'SS 519752 [ELit 0; ELit 550212;', 'SS 519752 [ELit 0; ELit 613268;',
      lambda n, l: l.startswith('Definition HS_tfib_0 :'))
plant('D1-DATA', 'YF0m.v', 'z8 (ANum 0x9c8f8) 0x100ffffffff', 'z8 (ANum 0x9c8f8) 0x95b94')
