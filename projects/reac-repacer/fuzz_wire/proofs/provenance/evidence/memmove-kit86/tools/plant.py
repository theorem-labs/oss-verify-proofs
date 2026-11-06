#!/usr/bin/env python3
"""plant.py -- the two controls this record's settlement must refuse.

Both plants put the SAME three words into a copy of one X function and of its Y counterpart, so every word of the pair
stays equal (bytecmp: EQUAL / EQUAL-mod-pcrel) and only the two layouts make the address they build name two different
objects:
    plant ADD   lui a0, HI ; add a0, a0, zero ; ld a0, LO(a0)
    plant XOR   lui a0, HI ; xor a0, a0, zero ; ld a0, LO(a0)
HI / LO are chosen so that HI<<12 + LO is the address of a named object in X and of a DIFFERENT named object in Y.
The ADD plant is a lui value read by an R-type op, which strictcmp3 judges as a lui target (`lui-in-section`); the XOR
plant is the kit's fail-open: xor is a logical read, so with no memory pair the kit settles the value as
`lui-const (dataflow)` and never compares the address the load uses. This record's settlement traces the lui value
through BOTH ops into the load base and computes the full address on both images, so both plants must be refused.
usage: plant.py KITDIR X_ELF Y_TWIN Y_PIN OUTDIR FUNC"""
import sys, os, shutil
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import luitrace as LT

kit, xe, yte, ype, outdir, fn = sys.argv[1:7]
s3 = LT.load_kit(kit)
X, Y = s3.Img(xe), s3.Img(yte)
os.makedirs(outdir, exist_ok=True)


def fsym(I, f):
    c = s3.fcopies(I, f)
    if len({(v, z) for v, z, n in c}) != 1: raise SystemExit('plant: %s is not one function in %s' % (f, I))
    return c[0][0], c[0][1]


xa, xz = fsym(X, fn)
ya, yz = fsym(Y, fn)
if xz != yz: raise SystemExit('plant: sizes differ')

# an address that names a DIFFERENT object in X and in Y, reachable as HI<<12 + LO with LO in [-2048, 2047]
cand = None
for v, z, nm, t in sorted(X.syms):
    if t != 'STT_OBJECT' or z <= 0 or not X.sec(v) or X.sec(v) not in ('.bss', '.data', '.data.rel.ro'): continue
    nx, ny = LT.name(s3, X, v), LT.name(s3, Y, v)
    if nx == ny or nx.startswith('(') or ny.startswith('('): continue
    hi = (v + 0x800) >> 12; lo = v - (hi << 12)
    if not -2048 <= lo < 2048 or hi >= (1 << 20): continue
    cand = (v, hi, lo, nx, ny); break
if cand is None: raise SystemExit('plant: no address that names two different objects')
v, hi, lo, nx, ny = cand


def words(op):
    lui = (hi << 12) | (10 << 7) | 0x37
    alu = (0 << 25) | (0 << 20) | (10 << 15) | ((0 if op == 'add' else 4) << 12) | (10 << 7) | 0x33
    ld = ((lo & 0xfff) << 20) | (10 << 15) | (3 << 12) | (10 << 7) | 0x03
    return [lui, alu, ld]


def plant(path, base, off, ws, dst):
    shutil.copyfile(path, dst)
    # the file offset of base+off: the PT_LOAD that holds it
    import struct
    from elftools.elf.elffile import ELFFile
    fo = None
    with open(path, 'rb') as f:
        e = ELFFile(f)
        for g in e.iter_segments():
            if g['p_type'] == 'PT_LOAD' and g['p_vaddr'] <= base + off < g['p_vaddr'] + g['p_filesz']:
                fo = g['p_offset'] + (base + off - g['p_vaddr'])
    if fo is None: raise SystemExit('plant: no PT_LOAD for %#x' % (base + off))
    with open(dst, 'r+b') as f:
        f.seek(fo)
        f.write(b''.join(struct.pack('<I', w) for w in ws))
    return fo


OFF = 0x10          # the three words replace the ones at FUNC+0x10 in both images
for op in ('add', 'xor'):
    ws = words(op)
    px = os.path.join(outdir, 'plant-%s-X.elf' % op)
    pt = os.path.join(outdir, 'plant-%s-Ytwin.elf' % op)
    pp = os.path.join(outdir, 'plant-%s-Ypin.elf' % op)
    plant(xe, xa, OFF, ws, px); plant(yte, ya, OFF, ws, pt); plant(ype, ya, OFF, ws, pp)
    print('# plant %s in %s at +%#x of X %#x / Y %#x: %s' % (op.upper(), fn, OFF, xa, ya,
          ' ; '.join('%08x %s' % (w, LT.dis(w)) for w in ws)))
    print('#   the load base is %#x: %s in X, %s in Y (sha256 X %s, Y twin %s, Y pin %s)'
          % (v, nx, ny, s3.sha(px)[:12], s3.sha(pt)[:12], s3.sha(pp)[:12]))
