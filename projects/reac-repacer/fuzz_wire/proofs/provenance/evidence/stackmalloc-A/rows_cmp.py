#!/usr/bin/env python3
"""rows_cmp.py KIT DONOR_TWIN TARGET_TWIN [PLANT_OUT] -- the code-table rows of A/Rt/AF0r.v's fs_ranges, compared word
by word by cmpkit KIT's strictcmp3 tcmp (the one compare, 65688e94214a): each fuzz_wire row (address, word count) is
paired with fuzz_grant's row by the function that holds it and its offset in that function; the pair is compared over
exactly the row's bytes (count * 4), so every instruction the walks decode is compared and nothing else.

With PLANT_OUT: also the planted control. PLANT_OUT is written as a copy of TARGET_TWIN with the 4-byte word at
__asan_stack_malloc_1 + 0x40 XOR 0x00100000 (one register field bit); the stack_malloc_1 row must then come out
different, and every other row as before (exit 1 otherwise). Prints one line per row; exit 0 when every row of the
real compare is EQUAL or EQUAL-mod-pcrel."""
import importlib.util
import os
import shutil
import sys

KIT, DON, TGT = sys.argv[1:4]
PLANT = sys.argv[4] if len(sys.argv) > 4 else None
spec = importlib.util.spec_from_file_location('strictcmp3', os.path.join(KIT, 'strictcmp3.py'))
sc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sc)

ROWS = [  # (fuzz_grant row, fuzz_wire row, words): AF0r.v fs_ranges, donor and relocated
    (0x3cda4, 0x3c544, 93), (0x3cf18, 0x3c6b8, 100), (0x61ccc, 0x61474, 2), (0x46aac, 0x45ee4, 31),
    (0x96620, 0x92708, 9), (0x5c00c, 0x5b7b4, 8), (0x54b58, 0x54300, 6), (0x976d4, 0x937bc, 7),
    (0x69720, 0x68ec8, 140), (0x3d410, 0x3c848, 28)]


def holder(I, a):
    c = [(v, z, nm) for v, z, nm, t in I.syms if t == 'STT_FUNC' and z > 0 and v <= a < v + z]
    return min(c, key=lambda x: x[1]) if c else None

EQ = ('EQUAL', 'EQUAL-mod-pcrel')


def run(tgt, tag):
    I = {'G': sc.Img(DON), 'W': sc.Img(tgt)}
    out = []
    for ga, wa, n in ROWS:
        hg, hw = holder(I['G'], ga), holder(I['W'], wa)
        same = hg and hw and hg[2] == hw[2] and ga - hg[0] == wa - hw[0] and ga + 4 * n <= hg[0] + hg[1] \
            and wa + 4 * n <= hw[0] + hw[1]
        fb = []
        v, c, t3, diff = sc.tcmp(I, 'G', ga, 'W', wa, 4 * n, fb)
        verdict = sc.verdict(v, diff)
        how = 'row'
        if verdict not in EQ and same and hg[1] == hw[1]:
            # a row that is a part of its function can cut an auipc pair whose consumer lies past the row's end
            # (strictcmp3 rule 6: UNMEASURED): the whole function, compared, decides every word the row holds
            fw = []
            vw, _c, _t, dw = sc.tcmp(I, 'G', hg[0], 'W', hw[0], hg[1], fw)
            if sc.verdict(vw, dw) in EQ:
                verdict, how, fb, diff = sc.verdict(vw, dw), 'whole function (row: %s)' % verdict, fw, dw
        out.append((ga, wa, n, verdict, same))
        print('%s\t%#x\t%#x\t%d words\t%s+%#x\t%s\t%s\tby %s\tdiffer %d\t%s' % (
            tag, ga, wa, n, hw[2] if hw else '-', wa - hw[0] if hw else 0, 'same holder+offset' if same else 'HOLDER DIFFERS',
            verdict, how, len(diff) if diff else 0, sc.fb_text(fb)))
    return out


real = run(TGT, 'row')
ok = all(r[3] in EQ and r[4] for r in real)
print('rows_cmp: %d of %d rows equal, holder and offset the same in both images' % (
    sum(1 for r in real if r[3] in EQ and r[4]), len(real)))
if PLANT:
    shutil.copyfile(TGT, PLANT)
    I = sc.Img(TGT)
    a = [v for v, z, nm, t in I.syms if nm == '__asan_stack_malloc_1' and t == 'STT_FUNC'][0] + 0x40
    off = next(o + a - v for v, fz, o in ((s['p_vaddr'], s['p_filesz'], s['p_offset']) for s in I.e.iter_segments()
                                          if s['p_type'] == 'PT_LOAD') if v <= a < v + fz)
    with open(PLANT, 'r+b') as f:
        f.seek(off)
        w = int.from_bytes(f.read(4), 'little') ^ 0x00100000
        f.seek(off)
        f.write(w.to_bytes(4, 'little'))
    print('plant: word at %#x (file offset %#x) XOR 0x00100000' % (a, off))
    pl = run(PLANT, 'plant')
    caught = [r for r, q in zip(real, pl) if r[3] != q[3]]
    ctl = len(caught) == 1 and caught[0][1] == 0x3c6b8
    print('rows_cmp control: %s (rows that changed verdict: %s)' % (
        'CAUGHT' if ctl else 'MISSED', ', '.join('%#x' % r[1] for r in caught) or 'none'))
    ok = ok and ctl
sys.exit(0 if ok else 1)
