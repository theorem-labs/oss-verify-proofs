#!/usr/bin/env python3
"""gen_globals_cells.py -- emit the program-global part of a target's at-main snapshot from the target's own ELF.

    gen_globals_cells.py ELF [--sec asan_globals]

Prints three blocks, in the form the core's Tfib_const / <Target>_const files use:

  DESC   one `z8 (ANum <cell>) <value>` per 8-byte word of every __asan_global descriptor of the section
         asan_globals, read from the ELF (8 words per descriptor: beg, size, size_with_redzone, name,
         module_name, has_dynamic_init, location, odr_indicator).
  SHADOW one `z1 (ANum <shadow addr>) <byte>` per shadow byte that __asan_register_globals poisons for a
         descriptor whose size is not a multiple of 8 (the partial granule, value size mod 8) or that covers the
         right redzone (0xf9), for every descriptor. shadow(a) = (a >> 3) + 0x7fff8000.
  ZERO   the maximal ranges of the image whose shadow is zero, i.e. the complement of the poisoned granules in
         [IMG_LO, asan_globals_end) and, with --img-top T, the tail [asan_globals_end, T) as well, as
         `(lo, hi - lo)` pairs. With --img-top-name N the tail's upper end is printed as the name N, so that no
         image-top literal appears in the generated text.

Every value comes from the ELF: no address of another target appears. Run it per image; the two images of one
target give two different blocks.
"""
import struct, sys


class Elf:
    def __init__(self, path):
        d = open(path, 'rb').read()
        self.d = d
        shoff = struct.unpack_from('<Q', d, 0x28)[0]
        shentsz, shnum, shstrndx = struct.unpack_from('<HHH', d, 0x3a)
        sh = [struct.unpack_from('<IIQQQQIIQQ', d, shoff + i * shentsz) for i in range(shnum)]
        stro = sh[shstrndx][4]

        def nm(o):
            e = d.index(b'\0', stro + o)
            return d[stro + o:e].decode()
        self.secs = [(nm(x[0]), x[3], x[3] + x[5], x[1]) for x in sh if x[3]]
        self.ph = []
        phoff = struct.unpack_from('<Q', d, 0x20)[0]
        phentsz, phnum = struct.unpack_from('<HH', d, 0x36)
        for i in range(phnum):
            t, fl, off, va, pa, fsz, msz, al = struct.unpack_from('<IIQQQQQQ', d, phoff + i * phentsz)
            if t == 1:
                self.ph.append((va, msz, off, fsz))

    def section(self, name):
        for n, lo, hi, t in self.secs:
            if n == name:
                return lo, hi
        raise SystemExit('gen_globals_cells: no section ' + name)

    def read(self, a, n):
        for va, msz, off, fsz in self.ph:
            if va <= a < va + fsz:
                return self.d[off + a - va:off + a - va + n]
            if va <= a < va + msz:
                return b'\0' * n
        raise SystemExit('gen_globals_cells: address %s is in no LOAD segment' % hex(a))

    def word(self, a):
        return struct.unpack('<Q', self.read(a, 8))[0]


SHADOW_BASE = 0x7FFF8000
IMG_LO = 0x10000


def shadow(a):
    return (a >> 3) + SHADOW_BASE


def main():
    args = sys.argv[1:]
    sec = 'asan_globals'
    img_top = None
    img_top_name = None
    if '--img-top-name' in args:
        i = args.index('--img-top-name')
        img_top_name = args[i + 1]
        del args[i:i + 2]
    if '--img-top' in args:
        i = args.index('--img-top')
        img_top = int(args[i + 1], 0)
        del args[i:i + 2]
    if '--sec' in args:
        i = args.index('--sec')
        sec = args[i + 1]
        del args[i:i + 2]
    if len(args) != 1:
        raise SystemExit(__doc__)
    e = Elf(args[0])
    lo, hi = e.section(sec)
    if (hi - lo) % 64:
        raise SystemExit('gen_globals_cells: %s size %d is not a multiple of 64' % (sec, hi - lo))
    descs = [(a, [e.word(a + 8 * i) for i in range(8)]) for a in range(lo, hi, 64)]
    print('(* %d descriptors, %s [%s, %s) *)' % (len(descs), sec, hex(lo), hex(hi)))
    print('DESC')
    for a, f in descs:
        for i, v in enumerate(f):
            print('z8 (ANum %s) %s  ;' % (hex(a + 8 * i), hex(v)))
    print('SHADOW')
    poisoned = []
    for a, f in descs:
        beg, size, swr = f[0], f[1], f[2]
        gran_end = beg + (size & ~7)
        if size % 8:
            print('z1 (ANum %s) %s  ;' % (hex(shadow(gran_end)), hex(size % 8)))
            poisoned.append((gran_end, gran_end + 8))
        rz_lo = gran_end + (8 if size % 8 else 0)
        for x in range(rz_lo, beg + swr, 8):
            print('z1 (ANum %s) 0xf9  ;' % hex(shadow(x)))
        poisoned.append((rz_lo, beg + swr))
    for x in range(lo, hi, 8):
        print('z1 (ANum %s) 0xf9  ;' % hex(shadow(x)))
    poisoned.append((lo, hi))
    print('ZERO')
    poisoned.sort()
    cur = IMG_LO
    out = []
    for plo, phi in poisoned:
        if plo > cur:
            out.append((cur, plo))
        cur = max(cur, phi)
    if cur < hi:
        out.append((cur, hi))
    if img_top is not None and hi < img_top:
        out.append((hi, img_top))
    for a, b in out:
        hi_txt = img_top_name if (img_top_name and img_top is not None and b == img_top) else hex(b)
        print('(%s, %s - %s);' % (hex(a), hi_txt, hex(a)))


if __name__ == '__main__':
    main()
