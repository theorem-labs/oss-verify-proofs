#!/usr/bin/env python3
"""dis.py -- the disassembly a hand reading cites: a function of X and its Y counterpart side by side, word by word,
with every pc-relative target the kit's targets() binds named by the kit's naming (strictcmp3.qres, else atname) and,
for a read-only unnamed target, its first bytes; words that differ between X and Y are marked `*`.
usage: dis.py KITDIR X_ELF Y_ELF FUNC[@0xX:0xY] [FROM_OFF TO_OFF]   (FUNC: a unique name or NAME{file}; @X:Y gives the
       two addresses explicitly)"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import luitrace as LT


def fsym(s3, I, f):
    c = s3.fcopies(I, f)
    if len({(v, z) for v, z, n in c}) != 1: raise SystemExit('dis: %s names %d functions' % (f, len(c)))
    return c[0][0], c[0][1]


def main(argv):
    kit, xe, ye, f = argv[:4]
    lo, hi = (int(argv[4], 16), int(argv[5], 16)) if len(argv) > 5 else (0, 1 << 30)
    s3 = LT.load_kit(kit)
    X, Y = s3.Img(xe), s3.Img(ye)
    if '@' in f:
        f, ad = f.split('@'); ax, ay = [int(v, 16) for v in ad.split(':')]
        z = fsym(s3, X, f)[1] if f else [zz for v, zz, n, t in X.syms if v == ax and zz > 0][0]
    else:
        ax, z = fsym(s3, X, f); ay, zy = fsym(s3, Y, f)
        if zy != z: raise SystemExit('dis: sizes differ')
    bx, by = s3.frd(X, ax, z), s3.frd(Y, ay, z)
    wx, wy = s3.bc_words(bx), s3.bc_words(by)
    tx, ty = s3.targets(ax, bx), s3.targets(ay, by)
    print('# %s X %#x Y %#x size %d (X sha256 %s, Y sha256 %s)' % (f, ax, ay, z, s3.sha(xe)[:12], s3.sha(ye)[:12]))
    for i, ((o, x, n), (oy, y, ny)) in enumerate(zip(wx, wy)):
        if not lo <= o <= hi: continue
        t = ''
        if i in tx and i in ty:
            a, b = tx[i][1], ty[i][1]
            nx, ny_ = LT.name(s3, X, a), LT.name(s3, Y, b)
            t = '  -> %#x %s | %#x %s' % (a, nx, b, ny_)
            if nx.startswith('('):
                dx, dy = s3.frd(X, a, 16), s3.frd(Y, b, 16)
                t += ' bytes %s | %s' % (dx and dx.hex(), dy and dy.hex())
        print('  +%-6s %08x %s %-30s%s' % (hex(o), x, '*' if x != y else ' ', LT.dis(x) if n == 4 else '(2-byte parcel)', t))


if __name__ == '__main__':
    main(sys.argv[1:])
