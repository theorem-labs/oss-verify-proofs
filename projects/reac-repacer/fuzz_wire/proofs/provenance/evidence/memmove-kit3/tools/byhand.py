#!/usr/bin/env python3
"""By-hand measurement of the targets a kit run leaves unsettled (cmpkit 4bbd3a74be89 README: 'a listed by-hand
acceptance with a separate measurement, never a kit EQUAL').
usage: byhand.py KITDIR X_ELF Y_ELF FUNC+OFF ...   (X, Y unstripped; OFF = the word offset the kit reports)
Per target: X / Y addresses (the kit's targets()), the consumer words, and two readings:
  CSTR-ANY  the bytes up to the first NUL, any byte values, compared WITH the NUL;
  JT32      the region read as a table of 32-bit entries, each taken as absolute (entry) and as relative
            (table + signed entry); for the reading under which entry 0 lands inside the function on both sides,
            the entries are compared by their offset from the function start, until an entry leaves the
            function on either side (reported: n equal, where and why it stops, the consumer's bound if found)."""
import sys, os, struct, importlib.util

kit, xe, ye = sys.argv[1:4]
args = sys.argv[4:]
spec = importlib.util.spec_from_file_location('rc', os.path.join(kit, 'repin_check-4c05cadaeba3.py'))
rc = importlib.util.module_from_spec(spec); sys.argv = [sys.argv[0]]; spec.loader.exec_module(rc)
X, Y = rc.Img(xe), rc.Img(ye)


def fb(img, a, n):
    for (v, fz, d) in img.segs:
        if v <= a < v + fz:
            return d[a - v:min(a - v + n, fz)]
    return b''


def fsym(img, name):
    for v, z, nm, t in img.syms:
        if nm == name and t == 'STT_FUNC' and z > 0:
            return v, z


def tgt(img, fv, fz, off):
    b = fb(img, fv, fz); t = rc.targets(fv, b); w = rc.bc_words(b)
    for i, (o, x, n) in enumerate(w):
        if o == off and i in t:
            return t[i][1], w, i
    return None, w, None


def bound(w, i):
    # sltiu / bltu / bgeu against a small constant loaded by addi rX, x0, K in the 12 words before the lo12
    ks = []
    for (o, x, n) in w[max(0, i - 12):i]:
        if n == 4 and (x & 0x7f) == 0x13 and ((x >> 12) & 7) == 0 and ((x >> 15) & 31) == 0:
            ks.append(rc.sx(x >> 20, 12))
        if n == 4 and (x & 0x7f) == 0x13 and ((x >> 12) & 7) == 3:
            ks.append(rc.sx(x >> 20, 12))
    return ks


for a in args:
    fn, off = a.rsplit('+', 1); off = int(off, 16)
    xs, ys = fsym(X, fn), fsym(Y, fn)
    xa, xw, xi = tgt(X, xs[0], xs[1], off); ya, yw, yi = tgt(Y, ys[0], ys[1], off)
    print('== %s+%#x  X %#x  Y %#x  consumer X: %s' % (fn, off, xa, ya, ' '.join('%08x' % x for (o, x, n) in xw[xi:xi + 5])))
    bx, by = fb(X, xa, 4096), fb(Y, ya, 4096)
    nx, ny = bx.find(b'\0'), by.find(b'\0')
    if nx >= 0 and ny >= 0:
        print('   CSTR-ANY %s  X %d bytes %r | Y %d bytes %r' % ('EQUAL' if bx[:nx + 1] == by[:ny + 1] else 'DIFFER', nx, bx[:nx][:60], ny, by[:ny][:60]))
    for mode in ('abs', 'rel'):
        def ent(img, base, k, b):
            e = struct.unpack_from('<I', b, 4 * k)[0]
            return e if mode == 'abs' else (base + (e - (1 << 32) if e & 0x80000000 else e)) & 0xffffffffffffffff
        n = 0; why = 'region end'
        while 4 * (n + 1) <= min(len(bx), len(by)) and n < 4096:
            ex, ey = ent(X, xa, n, bx), ent(Y, ya, n, by)
            inx = xs[0] <= ex < xs[0] + xs[1]; iny = ys[0] <= ey < ys[0] + ys[1]
            if not inx or not iny:
                why = 'entry %d leaves the function: X %s Y %s' % (n, 'in' if inx else 'out', 'in' if iny else 'out'); break
            if ex - xs[0] != ey - ys[0]:
                why = 'entry %d differs: X +%#x Y +%#x' % (n, ex - xs[0], ey - ys[0]); break
            n += 1
        if n:
            print('   JT32-%s  %d entries equal by function offset; stop: %s; consumer bound constants %s' % (mode, n, why, bound(xw, xi)))
    # STRTAB32-rel: entries relative to the table that point to C strings (a switch returning a name)
    n = 0; why = 'region end'; names = []
    while 4 * (n + 1) <= min(len(bx), len(by)) and n < 4096:
        ex = (xa + struct.unpack_from('<i', bx, 4 * n)[0]); ey = (ya + struct.unpack_from('<i', by, 4 * n)[0])
        sx_, sy_ = fb(X, ex, 256), fb(Y, ey, 256)
        kx, ky = sx_.find(b'\0'), sy_.find(b'\0')
        if kx <= 0 or ky <= 0 or not all(32 <= c < 127 for c in sx_[:kx]) or not all(32 <= c < 127 for c in sy_[:ky]):
            why = 'entry %d is not a printable C string on %s' % (n, 'X' if kx <= 0 or not all(32 <= c < 127 for c in sx_[:kx]) else 'Y'); break
        if sx_[:kx + 1] != sy_[:ky + 1]:
            why = 'entry %d differs: %r | %r' % (n, sx_[:kx], sy_[:ky]); break
        names.append(sx_[:kx].decode()); n += 1
    if n:
        print('   STRTAB32-rel  %d entries are equal C strings (NUL included): %s; stop: %s; consumer bound constants %s'
              % (n, ', '.join(names), why, bound(xw, xi)))
