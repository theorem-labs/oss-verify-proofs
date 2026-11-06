#!/usr/bin/env python3
"""plant.py -- the planted controls of failopen.py: for each KNOWN FAIL-OPEN shape (a)-(h) of cmpkit 86da41d3ef68, a
pair of image COPIES whose function FN begins with a synthetic instruction sequence of that shape.

Variant `diff`: the address reaches the load on side 1 at one symbol and on side 2 at ANOTHER symbol, so failopen.py
must report the planted site DIFFERENT, with the shape. Variant `same`: both sides reach the SAME symbol + offset (at
different absolute addresses), so the site must be SAME. The ELF inputs are only read; the copies are written to OUTDIR.
For each control it prints one PLANT line: the name, the variant, the planted offset of the load that the check reads,
the shape, both targets, and the planted words of both sides.
usage: plant.py ELF1 ELF2 FN OUTDIR       (side 1 and side 2; prints PLANT lines, writes OUTDIR/<ctl>_<variant>.{1,2})
       plant.py check PLANTS OUTDIR      (reads OUTDIR/<ctl>_<variant>.out, the failopen.py pair output of each copy,
                                          and prints one CHECK line per control: PASS when the planted site is
                                          DIFFERENT (diff) or SAME (same) and carries its shape)
"""
import importlib.util, os, shutil, struct, sys

H = os.path.dirname(os.path.abspath(__file__))
sp = importlib.util.spec_from_file_location('failopen', os.path.join(H, 'failopen.py'))
FO = importlib.util.module_from_spec(sp)
sp.loader.exec_module(FO)

R = {n: i for i, n in enumerate(FO.IREGS)}
F = {n: i for i, n in enumerate(['ft%d' % i for i in range(8)] + ['fs0', 'fs1'] + ['fa%d' % i for i in range(8)] +
                                ['fs%d' % i for i in range(2, 12)] + ['ft%d' % i for i in range(8, 12)])}
CSR = {'sscratch': 0x140}


def I(op, f3, rd, rs1, imm):
    assert -2048 <= imm < 2048, imm
    return ((imm & 0xfff) << 20) | (R[rs1] << 15) | (f3 << 12) | (R[rd] << 7) | op


def S(f3, rs2, rs1, imm):
    assert -2048 <= imm < 2048, imm
    return (((imm >> 5) & 0x7f) << 25) | (R[rs2] << 20) | (R[rs1] << 15) | (f3 << 12) | ((imm & 0x1f) << 7) | 0x23


def U(op, rd, imm20):
    return ((imm20 & 0xfffff) << 12) | (R[rd] << 7) | op


def J(rd, off):
    assert -(1 << 20) <= off < (1 << 20) and off % 2 == 0
    o = off & 0x1fffff
    return (((o >> 20) & 1) << 31) | (((o >> 1) & 0x3ff) << 21) | (((o >> 11) & 1) << 20) | \
        (((o >> 12) & 0xff) << 12) | (R[rd] << 7) | 0x6f


def lui(rd, v): return U(0x37, rd, v)
def auipc(rd, v): return U(0x17, rd, v)
def addi(rd, rs, imm): return I(0x13, 0, rd, rs, imm)
def addiw(rd, rs, imm): return I(0x1b, 0, rd, rs, imm)
def ori(rd, rs, imm): return I(0x13, 6, rd, rs, imm)
def xori(rd, rs, imm): return I(0x13, 4, rd, rs, imm)
def slli(rd, rs, sh): return I(0x13, 1, rd, rs, sh)
def ld(rd, rs, imm): return I(0x03, 3, rd, rs, imm)
def sd(rs2, rs1, imm): return S(3, rs2, rs1, imm)
def jalr(rd, rs, imm): return I(0x67, 0, rd, rs, imm)
def fmv_d_x(fd, rs): return 0xf2000053 | (R[rs] << 15) | (F[fd] << 7)
def fmv_x_d(rd, fs): return 0xe2000053 | (F[fs] << 15) | (R[rd] << 7)
def csrrw(rd, csr, rs): return (CSR[csr] << 20) | (R[rs] << 15) | (1 << 12) | (R[rd] << 7) | 0x73
def csrrs(rd, csr, rs): return (CSR[csr] << 20) | (R[rs] << 15) | (2 << 12) | (R[rd] << 7) | 0x73


def c_lui(rd, n):
    assert n and -32 <= n < 32
    return ('h', (0b011 << 13) | (((n >> 5) & 1) << 12) | (R[rd] << 7) | ((n & 0x1f) << 2) | 0b01)


C_NOP = ('h', 0x0001)


def hilo(v):
    hi = ((v + 0x800) >> 12) & 0xfffff
    lo = v - (FO.sx(hi << 12, 32))
    return hi, lo


def addr_of(e, name, off=0):
    c = [y for y in e.syms if y['name'] == name and y['size'] and y['type'] == 1]
    if len(c) != 1:
        raise SystemExit('plant: %s has %d objects named %s' % (e.path, len(c), name))
    return c[0]['value'] + off


def got_cell(e, target):
    s = [x for x in e.alloc if x['name'] == '.got'][0]
    for a in range(s['addr'], s['addr'] + s['size'], 8):
        if struct.unpack('<Q', e.read(a, 8))[0] == target:
            return a
    raise SystemExit('plant: %s has no .got cell holding %#x' % (e.path, target))


# --- the sequences: f(e, pc, T) -> (words, offset of the load the check reads). T is the side's target address.
def seq_a(e, pc, T):                    # V + imm: V = T - 8 built by lui / addi, the load immediate adds 8
    hi, lo = hilo(T - 8)
    return [lui('a0', hi), addi('a0', 'a0', lo), ld('a1', 'a0', 8)], 8


def seq_b(e, pc, T):                    # an addiw / addi chain
    hi, lo = hilo(T - 0x100)
    return [lui('a0', hi), addiw('a0', 'a0', lo), addi('a0', 'a0', 0x100), ld('a1', 'a0', 0)], 12


def seq_c_ori(e, pc, T):
    hi, lo = hilo(T & ~0x7f)
    return [lui('a0', hi), addi('a0', 'a0', lo), ori('a0', 'a0', T & 0x7f), ld('a1', 'a0', 0)], 12


def seq_c_xori(e, pc, T):
    hi, lo = hilo(T ^ 0x40)
    return [lui('a0', hi), addi('a0', 'a0', lo), xori('a0', 'a0', 0x40), ld('a1', 'a0', 0)], 12


def seq_c_slli(e, pc, T):
    assert T % 8 == 0
    hi, lo = hilo(T >> 3)
    return [lui('a0', hi), addi('a0', 'a0', lo), slli('a0', 'a0', 3), ld('a1', 'a0', 0)], 12


def seq_d_spill(e, pc, T):
    hi, lo = hilo(T)
    return [lui('a0', hi), addi('a0', 'a0', lo), addi('sp', 'sp', -16), sd('a0', 'sp', 8), addi('a0', 'zero', 0),
            ld('a1', 'sp', 8), ld('a2', 'a1', 0)], 24


def seq_d_fmv(e, pc, T):
    hi, lo = hilo(T)
    return [lui('a0', hi), addi('a0', 'a0', lo), fmv_d_x('ft0', 'a0'), addi('a0', 'zero', 0), fmv_x_d('a1', 'ft0'),
            ld('a2', 'a1', 0)], 20


def seq_d_csr(e, pc, T):
    hi, lo = hilo(T)
    return [lui('a0', hi), addi('a0', 'a0', lo), csrrw('zero', 'sscratch', 'a0'), addi('a0', 'zero', 0),
            csrrs('a1', 'sscratch', 'zero'), ld('a2', 'a1', 0)], 20


def seq_e(e, pc, T):                    # an indirect jump; arm 1 forms the address, arm 2 (fall-through) loads
    hi, lo = hilo(T)
    return [jalr('zero', 'a5', 0), lui('a0', hi), addi('a0', 'a0', lo), ld('a1', 'a0', 0)], 12


def seq_f(e, pc, T):                    # the address passed in a0 to a callee inside the function's region
    hi, lo = hilo(T)
    return [lui('a0', hi), addi('a0', 'a0', lo), J('ra', 8), J('zero', 12), ld('a1', 'a0', 0),
            jalr('zero', 'ra', 0)], 16


def seq_g(e, pc, T):                    # c.lui (+ slli, addi): T = (n << 13) + lo
    n = (T + (1 << 12)) >> 13
    lo = T - (n << 13)
    return [c_lui('a0', n), C_NOP, slli('a0', 'a0', 1), addi('a0', 'a0', lo), ld('a1', 'a0', 0)], 12


def seq_h_auipc(e, pc, T):
    hi, lo = hilo(T - pc)
    return [auipc('a0', hi), addi('a0', 'a0', lo), ld('a1', 'a0', 0)], 8


def seq_h_ldk(e, pc, T):                # the address is a loaded constant: a .got cell that holds T
    G = got_cell(e, T)
    hi, lo = hilo(G - pc)
    return [auipc('a0', hi), ld('a0', 'a0', lo), ld('a1', 'a0', 0)], 8


def seq_h_li(e, pc, T):                 # the address built from an addi-from-zero and a shift, no lui, no auipc
    K = T >> 11
    assert K < 2048
    return [addi('a0', 'zero', K), slli('a0', 'a0', 11), ld('a1', 'a0', T - (K << 11))], 8


FLAGS, COMMON = '_ZN6__asan28asan_flags_dont_use_directlyE', '_ZN11__sanitizer21common_flags_dont_useE'
P_A = 'oft_aligned_copy.empty'          # same name and size in both images, a different object right after it
# name, shape, sequence, diff targets (side 1, side 2), same target (both sides): (symbol, offset)
CONTROLS = [
    ('a', 'a', seq_a, ((P_A, 0x20), (P_A, 0x20)), (FLAGS, 0x10)),
    ('b', 'b', seq_b, ((FLAGS, 0x10), (COMMON, 0x10)), (FLAGS, 0x10)),
    ('c.ori', 'c', seq_c_ori, ((FLAGS, 0x10), (COMMON, 0x10)), (FLAGS, 0x10)),
    ('c.xori', 'c', seq_c_xori, ((FLAGS, 0x10), (COMMON, 0x10)), (FLAGS, 0x10)),
    ('c.slli', 'c', seq_c_slli, ((FLAGS, 0x10), (COMMON, 0x10)), (FLAGS, 0x10)),
    ('d.spill', 'd', seq_d_spill, ((FLAGS, 0x10), (COMMON, 0x10)), (FLAGS, 0x10)),
    ('d.fmv', 'd', seq_d_fmv, ((FLAGS, 0x10), (COMMON, 0x10)), (FLAGS, 0x10)),
    ('d.csr', 'd', seq_d_csr, ((FLAGS, 0x10), (COMMON, 0x10)), (FLAGS, 0x10)),
    ('e', 'e', seq_e, ((FLAGS, 0x10), (COMMON, 0x10)), (FLAGS, 0x10)),
    ('f', 'f', seq_f, ((FLAGS, 0x10), (COMMON, 0x10)), (FLAGS, 0x10)),
    ('g', 'g', seq_g, (('errmsgidx', 0), ('__c_locale', 0)), ('errmsgidx', 0)),
    ('h.auipc', 'h', seq_h_auipc, ((FLAGS, 0x10), (COMMON, 0x10)), (FLAGS, 0x10)),
    ('h.ldk', 'h', seq_h_ldk, ((FLAGS, 0), (COMMON, 0)), (FLAGS, 0)),
    ('h.li', 'h', seq_h_li, ((FLAGS, 0x10), (COMMON, 0x10)), (FLAGS, 0x10)),
]


def encode(words):
    b = b''
    for w in words:
        b += struct.pack('<H', w[1]) if isinstance(w, tuple) else struct.pack('<I', w)
    return b


def plant(e, fn, seq, target, out):
    a, n = e.fsym(fn)
    words, ld_off = seq(e, a, target)
    b = encode(words)
    assert len(b) % 4 == 0 and len(b) <= n
    off = next(p_off + (a - va) for (va, msz, fsz, p_off, pf) in e.loads if va <= a < va + fsz)
    shutil.copyfile(e.path, out)
    d = bytearray(open(out, 'rb').read())
    d[off:off + len(b)] = b
    open(out, 'wb').write(d)
    return ld_off, b.hex()


def main():
    e1, e2, fn, outdir = FO.Elf(sys.argv[1]), FO.Elf(sys.argv[2]), sys.argv[3], sys.argv[4]
    print('# side 1 %s sha256 %s; side 2 %s sha256 %s; function %s'
          % (os.path.basename(e1.path), e1.sha, os.path.basename(e2.path), e2.sha, fn))
    for name, shape, seq, (t1, t2), same in CONTROLS:
        for var, (s1, s2) in (('diff', (t1, t2)), ('same', (same, same))):
            T1, T2 = addr_of(e1, *s1), addr_of(e2, *s2)
            o1 = os.path.join(outdir, '%s_%s.1' % (name, var))
            o2 = os.path.join(outdir, '%s_%s.2' % (name, var))
            l1, w1 = plant(e1, fn, seq, T1, o1)
            l2, w2 = plant(e2, fn, seq, T2, o2)
            assert l1 == l2
            print('PLANT\t%s\t%s\t+%#x\tshape %s\tside 1 %s+%#x (%#x)\tside 2 %s+%#x (%#x)\twords 1 %s\twords 2 %s'
                  % (name, var, l1, shape, s1[0], s1[1], T1, s2[0], s2[1], T2, w1, w2))


def check(plants, outdir):
    n = ok = 0
    for ln in open(plants):
        f = ln.rstrip('\n').split('\t')
        if f[0] != 'PLANT':
            continue
        name, var, off, shape = f[1], f[2], f[3], f[4].split()[1]
        want = 'DIFFERENT' if var == 'diff' else 'SAME'
        rows = [r.rstrip('\n').split('\t') for r in open(os.path.join(outdir, '%s_%s.out' % (name, var)))
                if r.startswith('SITE\t') and r.split('\t')[2] == off]
        got, shapes = (rows[0][-1], rows[0][6].split()[1]) if len(rows) == 1 else ('no site', '-')
        good = got == want and shape in shapes
        n += 1
        ok += good
        print('CHECK\t%s\t%s\t%s\twant %s, shape %s\tgot %s, shapes %s\t%s'
              % (name, var, off, want, shape, got, shapes, 'PASS' if good else 'FAIL'))
    print('controls PASS %d of %d' % (ok, n))
    return ok == n


if __name__ == '__main__':
    if len(sys.argv) == 4 and sys.argv[1] == 'check':
        sys.exit(0 if check(sys.argv[2], sys.argv[3]) else 1)
    main()
