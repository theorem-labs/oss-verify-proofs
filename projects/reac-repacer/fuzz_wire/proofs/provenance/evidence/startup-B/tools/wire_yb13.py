#!/usr/bin/env python3
"""wire_yb13.py -- reac-repacer/fuzz_wire image-B YB13.v: cgif's released lib/YB13.v (commit 25e3d17bdb50,
blob 7bf6329799b9) with every image numeral recomputed from fuzz_wire.asan-ubsan by the rule the donor's own numeral
follows. The rules and the token-substitution engine are fuzz_decode's gen.py (gen_dec.py beside this file, sha256
6ccd419c977f, imported unchanged): slots_AB13 (TFIB_BSS = the start of the last PT_LOAD's zero suffix up to img_hi, the
four segments' bases / sizes / byte counts, the writable window) plus ONE slot this image needs and decode's did not:
segment 1's base in hex (cgif 0x30000 = seg 0's page-up end; it bounds tfib_rom0 / tfib_rom1 / tfib_rom_all; decode's
equals cgif's, fuzz_wire's is 0x2f000). CONTROL first: the same rules on cgif's asan-ubsan image (symbols: cgif's
released YB1w.v) must reproduce cgif's released YB13.v byte for byte. RESIDUE gate: no token of a cgif value the slots
move survives in the output.

  wire_yb13.py --out DIR [--table TSV]   writes DIR/YB13.v (donor module paths; tools/nsW.py rewrites them).
                                         Paths from env.sh: HUB, UB, UBs, CB.
"""
import argparse, hashlib, os, re, subprocess, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_dec import Img, slots_AB13, apply_slots, hexs  # noqa: E402

HUB = os.environ['HUB']
IMG, TWIN = os.environ['UB'], os.environ['UBs']
IMG_SHA = 'af4534831a4528320c7dc74ca3f64bb96e8232ed2e313f01126d10879f3417d6'
TWIN_SHA = '51eb4bef24252e4df6e11baa89f653d20d74e38ae684f61bc94f4fb339ac97c3'
CG = os.environ['CB']
CG_SHA = '1c29845fe6058de6e1dbf3f6ec6abd566ea612d76b65ea5435d7ff77c63e08ef'
fail = []


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def git(path):
    return subprocess.run(['git', '-C', HUB, 'show', '25e3d17bdb50:proofs/cgif/cgif_file_fuzzer/lib/' + path],
                          check=True, capture_output=True, text=True).stdout


def check(name, ok, detail=''):
    print(('  ok   ' if ok else '  FAIL ') + name + (' : ' + detail if detail else ''))
    if not ok:
        fail.append(name)


def slots_YB13(I):
    return slots_AB13(I) + [('0x%x' % I.segs[1][0], lambda J: hexs(J.segs[1][0]))]   # seg 1 base, hex


def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--out', required=True)
    ap.add_argument('--table', help='write the per-value slot table (TSV: cgif token, fuzz_wire token, occurrences)')
    a = ap.parse_args()
    assert sha(IMG) == IMG_SHA and sha(TWIN) == TWIN_SHA and sha(CG) == CG_SHA, 'image pin mismatch'
    cgsym = os.path.join(a.out, 'YB1w.cgif.v')
    open(cgsym, 'w').write(git('YB1w.v'))
    C, D = Img(CG, cgsym), Img(IMG, TWIN)
    donor = git('YB13.v')
    lines = donor.split('\n')
    k = 0
    while lines[k].startswith('(*'):
        k += 1
    head, body = lines[:k], '\n'.join(lines[k:])
    sl = slots_YB13(C)
    ctl, _ = apply_slots(body, sl, C, 'YB13')
    check('control: the rules on cgif\'s asan-ubsan image reproduce cgif YB13.v', ctl == body)
    out, seen = apply_slots(body, sl, D, 'YB13')
    print('   slots: ' + ', '.join('%s->%s x%d' % (t, f(D), seen[t]) for t, f in sl))
    if a.table:
        with open(a.table, 'w') as tf:
            tf.write('# YB13.v slots: cgif_file_fuzzer.asan-ubsan token -> fuzz_wire.asan-ubsan token (rules: decode gen.py '
                     'slots_AB13 + segment 1 base), occurrences in the donor text\ncgif\tfuzz_wire\toccurrences\n')
            for tk, f in sl:
                tf.write('%s\t%s\t%d\n' % (tk, f(D), seen[tk]))
    moved = {t for t, f in sl if f(D) != t}
    kept = {f(D) for t, f in sl}
    residue = [t for t in re.findall(r'0x[0-9a-fA-F]+|\b\d+\b', out) if t in moved and t not in kept]
    check('residue: no moved cgif token survives', not residue, str(sorted(set(residue))))
    m = re.search(r'Definition TFIB_BSS : Z \* Z := \((0x[0-9a-f]+), (0x[0-9a-f]+)\)', out)
    lo, hi = int(m.group(1), 16), int(m.group(2), 16)
    base, size, b = D.segs[-1]
    check('TFIB_BSS = (start of the image\'s zero suffix, img_hi)', (lo, hi) == (D.bss_zero_start(), D.img_hi()),
          '%#x %#x' % (lo, hi))
    check('every byte of [TFIB_BSS) is zero in the image and the byte below it is not',
          all(x == 0 for x in b[lo - base:]) and b[lo - base - 1] != 0)
    m = re.search(r'tfib_rw_rom : forall x, (0x[0-9a-f]+) <= x < (0x[0-9a-f]+)', out)
    check('tfib_rw_rom window == (first writable PT_LOAD page, img_hi)',
          (int(m.group(1), 16), int(m.group(2), 16)) == (D.segs[2][0], D.img_hi()), m.group(0))
    for i, (bse, sz, bb) in enumerate(D.segs):
        mm = re.search(r'tfib_hex%d : scanN AsanUbsan_seg_bytes_%03d 64 0 (\d+)' % (i, i), out)
        ml = re.search(r'tfib_len%d : .*AsanUbsan_seg_bytes_%03d\) / 2\) = (\d+)%%N' % (i, i), out)
        check('seg %d byte count == image segment size %#x' % (i, sz), int(mm.group(1)) == sz and int(ml.group(1)) == sz)
    for i in range(4):
        mr = re.search(r'tfib_rom%d : forall x, (0x[0-9a-f]+) <= x < (0x[0-9a-f]+) ->' % i, out)
        if mr:
            check('tfib_rom%d window == segment %d pages' % (i, i),
                  (int(mr.group(1), 16), int(mr.group(2), 16)) == (D.segs[i][0], D.segs[i][0] + D.segs[i][1]
                                                                   if i < 3 else D.img_hi()), mr.group(0))
    mz = re.search(r'tfib_zero3 : zscanN AsanUbsan_seg_bytes_003 64 (\d+) (\d+)', out)
    check('zero scan == [TFIB_BSS, img_hi) inside segment 3', (int(mz.group(1)), int(mz.group(2))) == (lo - base, hi - lo),
          mz.group(0))
    line = ('(* Modified by Theorem Labs: generated from proofs/cgif/cgif_file_fuzzer/lib/YB13.v (commit '
            '25e3d17bdb50) with its module paths changed and every image numeral recomputed from reac-repacer/fuzz_wire\'s '
            'asan-ubsan image by the rule the donor\'s own numeral follows (decode\'s gen.py slots_AB13 + segment 1\'s base): '
            'its four PT_LOAD pages (bases, sizes, byte counts), the writable window %#x..%#x and TFIB_BSS = (%#x, %#x), the '
            'start of the image\'s zero suffix up to img_hi; the rules reproduce cgif\'s released text on cgif\'s image. *)'
            % (D.segs[2][0], D.img_hi(), lo, hi))
    read = ('(* Read from: fuzz_wire.asan-ubsan (reac-repacer/fuzz_wire asan-ubsan) sha256 %s; '
            'unstripped twin sha256 %s *)' % (IMG_SHA, TWIN_SHA))
    txt = '\n'.join(head + [line, read]) + '\n' + out
    p = os.path.join(a.out, 'YB13.v')
    open(p, 'w').write(txt)
    print('  wrote %s sha256 %s' % (p, sha(p)))
    if fail:
        print('FAILED: ' + '; '.join(fail)); return 1
    print('all checks pass')
    return 0


sys.exit(main())
