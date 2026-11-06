#!/usr/bin/env python3
"""luiuse_control.py X_ELF Y_ELF   (KIT=<cmpkit 86da41d3ef68 dir>): planted controls for luiuse.py's walk, on synthetic
functions (encoded words; the two images only satisfy luiuse.py's start-up). Each plant states the verdict it must get.
 P1 `lui a0, 0x100; ld a1, 0(a0); ret`                      the value is an absolute load address   -> ADDRESS
 P2 `lui a0, 0x100; add a0, a0, a1; ld a2, 0(a0); ret`      an offset added to an unknown register  -> NUMBER
 P3 `lui a0, 0x100; jal CALLEE; ret` / CALLEE `ld a1, 8(a0); ret`   absolute address inside a callee   -> ADDRESS
 P4 `lui a0, 0x100; addi a1, zero, 8; add a0, a0, a1; sd a2, 0(a0); ret`   value + a constant as a store base -> ADDRESS
 P5 `lui a0, 0x100; sd a0, 16(sp); ld a3, 16(sp); lw a4, 0(a3); ret`       spilled, reloaded, then a base     -> ADDRESS
 P6 `lui a0, 0x100; slli a0, a0, 2; ret`                     returned (a HAND row)                   -> NUMBER+HAND
Exit 0 only if every plant gets its verdict."""
import sys, os, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('luiuse', os.path.join(HERE, 'luiuse.py'))
sys_argv = sys.argv; sys.argv = [sys.argv[0], sys.argv[1], sys.argv[2], os.devnull]
L = importlib.util.module_from_spec(spec); spec.loader.exec_module(L)

def I(op, rd=0, f3=0, rs1=0, rs2=0, imm=0):
    if op in (0x13, 0x03, 0x67): return op | rd << 7 | f3 << 12 | rs1 << 15 | (imm & 0xfff) << 20
    if op == 0x33: return op | rd << 7 | f3 << 12 | rs1 << 15 | rs2 << 20
    if op == 0x23: return op | (imm & 31) << 7 | f3 << 12 | rs1 << 15 | rs2 << 20 | ((imm >> 5) & 0x7f) << 25
    if op == 0x37: return op | rd << 7 | (imm & 0xfffff) << 12
    raise ValueError(op)
def JAL(rd, off):
    o = off & 0x1fffff
    return 0x6f | rd << 7 | ((o >> 12) & 0xff) << 12 | ((o >> 11) & 1) << 20 | ((o >> 1) & 0x3ff) << 21 | ((o >> 20) & 1) << 31
RET = I(0x67, 0, 0, 1, imm=0)
LUI = I(0x37, 10, imm=0x100)
plants = {
    'P1': ([LUI, I(0x03, 11, 3, 10), RET], None, 'ADDRESS'),
    'P2': ([LUI, I(0x33, 10, 0, 10, 11), I(0x03, 12, 3, 10), RET], None, 'NUMBER'),
    'P3': ([LUI, JAL(1, 0xfc), RET], [I(0x03, 11, 3, 10, imm=8), RET], 'ADDRESS'),
    'P4': ([LUI, I(0x13, 11, 0, 0, imm=8), I(0x33, 10, 0, 10, 11), I(0x23, 0, 3, 10, 12), RET], None, 'ADDRESS'),
    'P5': ([LUI, I(0x23, 0, 3, 2, 10, imm=16), I(0x03, 13, 3, 2, imm=16), I(0x03, 14, 2, 13), RET], None, 'ADDRESS'),
    'P6': ([LUI, I(0x13, 10, 1, 10, imm=2), RET], None, 'NUMBER+HAND'),
}
class Fake:
    def __init__(self, main, callee):
        self.I = None; self.busy = set(); self.memo = {}
        self.funcs = {0x1000: (0x1000, 4 * len(main), 'plant')}
        self.ws = {0x1000: main}
        if callee: self.funcs[0x1100] = (0x1100, 4 * len(callee), 'callee'); self.ws[0x1100] = callee
    def words(self, v):
        w = [(4 * i, x, 4) for i, x in enumerate(self.ws[v])]
        return w, {o: j for j, (o, x, n) in enumerate(w)}
ok = True
for name, (main, callee, want) in plants.items():
    M = Fake(main, callee)
    uses, rets = L.walk(M, 0x1000, 1, {10: 'PURE'}, 0, True)
    us = sorted(uses)
    got = 'ADDRESS' if any(u[2] == 'base' and 'PURE' in u[3] for u in us) else \
          'NUMBER+HAND' if any(u[2] in ('data', 'ret', 'indirect', 'syscall', 'deep') for u in us) else 'NUMBER'
    print('%s\twant %s\tgot %s\t%s\t%s' % (name, want, got, 'OK' if got == want else 'FAIL', us))
    ok &= got == want
sys.exit(0 if ok else 1)
