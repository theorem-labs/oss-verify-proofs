#!/usr/bin/env python3
"""ownctl.py KIT_DIR -- planted controls on THIS run's own inputs (in-memory Img.segs patch of the decode image-A twin,
as cmpkit's controls/negctl.py does). Read-only; nothing is written to any image.
  BASELINE  cgif twin (C) vs decode A twin (A), Allocator::Allocate: the kit's verdict before any plant.
  PLANT 1   the first jal of Allocate in A re-pointed to the next FUNC symbol after its callee: strictcmp2 must report a
            target difference at that word.
  PLANT 2   the first compared ld target of Allocate in A moved 8 bytes: strictcmp2 must report a target difference there.
  PLANT 3   one body word of memset in A changed (addi -> andi, same registers): bytecmp 1480ca2faea0's own per-word rule
            must call it a REAL difference (verdict DIFFERENT), not pc-relative.
Expected: every plant adds a report the baseline lacks."""
import os, sys, importlib.util
KIT = os.path.abspath(sys.argv[1])
sys.dont_write_bytecode = True
sp = importlib.util.spec_from_file_location('s2', os.path.join(KIT, 'strictcmp2.py'))
S = importlib.util.module_from_spec(sp); sp.loader.exec_module(S)
C = 'DONOR_TWIN'
A = 'DECODE_A_TWIN'
FN = '_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb'
print('# kit', KIT, 'strictcmp2 sha256', S.sha(os.path.join(KIT, 'strictcmp2.py'))[:12])
print('# C', C, S.sha(C)[:12]); print('# A', A, S.sha(A)[:12])


def patch(I, a, data):
    for k, (v, fz, d) in enumerate(I.segs):
        if v <= a and a + len(data) <= v + fz:
            b = bytearray(d); b[a - v:a - v + len(data)] = data; I.segs[k] = (v, fz, bytes(b)); return
    raise SystemExit('not in a PT_LOAD')


def enc_jal(pc, tgt, rd):
    o = (tgt - pc) & 0x1fffff
    return (((o >> 20) & 1) << 31) | (((o >> 1) & 0x3ff) << 21) | (((o >> 11) & 1) << 20) | (((o >> 12) & 0xff) << 12) | (rd << 7) | 0x6f


def run(tag, fn=FN, plant=None):
    I = {'C': S.Img(C), 'A': S.Img(A)}
    note = plant(I['A']) if plant else ''
    s1, s2 = I['C'].fsym(fn), I['A'].fsym(fn)
    v, c, t3, diff = S.tcmp(I, 'C', s1[0], 'A', s2[0], s1[1], [])
    print('%s %s [%s]: %s pcrel/real/unmeas %s targets %s; differences %d: %s'
          % (tag, note, fn[:40], v, c, t3, len(diff), [tuple(map(str, d[:4])) for d in diff]))
    return v, {d[0] for d in diff}


base_v, base = run('BASELINE')
mem_v, mem_base = run('BASELINE memset', 'memset')


def plant1(Y):
    a, z = Y.fsym(FN); b = S.frd(Y, a, z); t = S.targets(a, b); W = S.bc_words(b)
    funcs = sorted(x[0] for x in Y.syms if x[3] == 'STT_FUNC' and x[1] > 0)
    for i, (o, x, n) in enumerate(W):
        if n == 4 and x & 0x7f == 0x6f and i in t:
            cal = t[i][1]; nxt = next(f for f in funcs if f > cal)
            patch(Y, a + o, enc_jal(a + o, nxt, (x >> 7) & 31).to_bytes(4, 'little'))
            return 'jal at +%#x: %#x -> %#x' % (o, cal, nxt)
    raise SystemExit('no jal target in ' + FN)


def plant2(Y):
    a, z = Y.fsym(FN); b = S.frd(Y, a, z); t = S.targets(a, b); W = S.bc_words(b)
    for i, (o, x, n) in enumerate(W):
        if n == 4 and x & 0x707f == 0x3003 and i in t:        # ld rd, imm(rs1), a compared target
            imm = (x >> 20) & 0xfff; new = (x & 0xfffff) | (((imm + 8) & 0xfff) << 20)
            patch(Y, a + o, new.to_bytes(4, 'little'))
            return 'ld at +%#x: target %#x -> %#x' % (o, t[i][1], t[i][1] + 8)
    raise SystemExit('no ld target in ' + FN)


def plant3(Y):
    a, z = Y.fsym('memset'); b = S.frd(Y, a, z); W = S.bc_words(b)
    for o, x, n in W:
        if n == 4 and x & 0x707f == 0x0013:                   # addi rd, rs1, imm -> andi, same registers
            patch(Y, a + o, ((x & ~0x7000) | 0x7000).to_bytes(4, 'little'))
            return 'memset word at +%#x: addi %08x -> andi %08x' % (o, x, (x & ~0x7000) | 0x7000)
    raise SystemExit('no addi in memset')


for tag, fn, p, base_set in (('PLANT 1', FN, plant1, base), ('PLANT 2', FN, plant2, base),
                             ('PLANT 3', 'memset', plant3, mem_base)):
    v, got = run(tag, fn, p)
    new = sorted(got - base_set)
    caught = bool(new) or (fn == 'memset' and v != mem_v)
    print('  %s: verdict %s (baseline %s), new difference words %s -> %s'
          % (tag, v, base_v if fn == FN else mem_v, new, 'CAUGHT' if caught else 'MISSED'))
