#!/usr/bin/env python3
"""basecalc_control.py X_ELF Y_ELF   (KIT=<cmpkit 86da41d3ef68 dir>): planted controls for basecalc.py's walk on synthetic
functions (encoded words; X_ELF only names the addresses). Each plant states the class its base must get.
 B1 `lui a0, 0x100; auipc a1, 0; add a2, a1, a0; ld a3, 0(a2); ret`        image address + lui value   -> IMAGE
 B2 `lui a0, 0x100; add a2, a1, a0; ld a3, 0(a2); ret` (a1 = a parameter)   run-time pointer + lui value -> RUNTIME
 B3 `lui a0, 0x100; ld a3, 0(a0); ret`                                     the lui value alone          -> ABS
 B4 `lui a0, 0x100; auipc a1, 0; addi a1, a1, 16; sd a1, 8(sp); ld a5, 8(sp); add a2, a5, a0; sw a3, 4(a2); ret`
                                                                           spill / reload of the image address -> IMAGE
Exit 0 only if every plant gets its class (and B1 / B4 the expected full address)."""
import sys, os, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('basecalc', os.path.join(HERE, 'basecalc.py'))
B = importlib.util.module_from_spec(spec); spec.loader.exec_module(B)
L = B.L

def I(op, rd=0, f3=0, rs1=0, rs2=0, imm=0):
    if op in (0x13, 0x03, 0x67): return op | rd << 7 | f3 << 12 | rs1 << 15 | (imm & 0xfff) << 20
    if op == 0x33: return op | rd << 7 | f3 << 12 | rs1 << 15 | rs2 << 20
    if op == 0x23: return op | (imm & 31) << 7 | f3 << 12 | rs1 << 15 | rs2 << 20 | ((imm >> 5) & 0x7f) << 25
    if op in (0x37, 0x17): return op | rd << 7 | (imm & 0xfffff) << 12
RET = I(0x67, 0, 0, 1)
LUI = I(0x37, 10, imm=0x100)
FA = 0x10000
plants = {
    'B1': ([LUI, I(0x17, 11, imm=0), I(0x33, 12, 0, 11, 10), I(0x03, 13, 3, 12), RET], 'IMAGE', FA + 4 + 0x100000),
    'B2': ([LUI, I(0x33, 12, 0, 11, 10), I(0x03, 13, 3, 12), RET], 'RUNTIME', None),
    'B3': ([LUI, I(0x03, 13, 3, 10), RET], 'ABS', 0x100000),
    'B4': ([LUI, I(0x17, 11, imm=0), I(0x13, 11, 0, 11, imm=16), I(0x23, 0, 3, 2, 11, imm=8), I(0x03, 15, 3, 2, imm=8),
            I(0x33, 12, 0, 15, 10), I(0x23, 0, 2, 12, 13, imm=4), RET], 'IMAGE', FA + 4 + 16 + 0x100000 + 4),
}
class Fake:
    def __init__(self, ws):
        self.I = None; self.busy = set(); self.funcs = {FA: (FA, 4 * len(ws), 'plant')}; self.ws = ws
    def words(self, v):
        w = [(4 * i, x, 4) for i, x in enumerate(self.ws)]
        return w, {o: j for j, (o, x, n) in enumerate(w)}
ok = True
for nm, (ws, want, addr) in plants.items():
    M = Fake(ws); sites = []
    init = dict(B.pre_state(M, FA, 0)); init[10] = ('K', 0x100000, True, 0)
    B.walk(M, FA, 1, init, 0, sites, ())
    kinds = sorted({s[3] for s in sites}); got = kinds[0] if len(kinds) == 1 else str(kinds)
    a = sites[0][5] if sites else None
    a = a[0] if isinstance(a, tuple) else a
    good = got == want and (addr is None or a == addr)
    print('%s\twant %s %s\tgot %s %s\t%s' % (nm, want, hex(addr) if addr else '-', got, hex(a) if isinstance(a, int) else a, 'OK' if good else 'FAIL'))
    ok &= good
sys.exit(0 if ok else 1)
