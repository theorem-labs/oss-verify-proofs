#!/usr/bin/env python3
"""plant_controls.py -- the two planted controls luitrace.py must refuse (AGENT TIME and TIME).

Each plant goes into a COPY of the image; no pinned file is written.

  static-base  a lui-built MASK applied to a STATIC base made by auipc + addi with no load between them, then used
               as a load base (AGENT TIME):
                   lui t1, 0xfff80 ; srli t1, t1, 0x10 ; auipc t2, 0x0 ; addi t2, t2, 0x10 ;
                   and t3, t2, t1 ; ld t4, 0(t3)
  x5-logical   WORKER's plant X5 shape (AGENT TIME): the lui value goes through LOGICAL ops only and then
               IS the load base. cmpkit 86da41d3ef68 calls such a row `lui-const (dataflow)` and prints EQUAL:
                   lui t1, 0x40 ; ori t1, t1, 0x100 ; xor t2, t1, zero ; andi t3, t2, -8 ; ld t4, 0(t3)

PASS for both = luitrace.py reports the load base with a statically known address (a `val=`/`ea=`/`sym=` that is not
`?`), i.e. it does NOT clear the site as a runtime base.

usage: plant_controls.py PLANT ELF FUNCTION +OFFSET OUT_ELF        (PLANT: static-base | x5-logical)
"""
import sys, shutil
from elftools.elf.elffile import ELFFile

PLANTS = {
    'static-base': [(0xfff80337, 'lui t1, 0xfff80'), (0x01035313, 'srli t1, t1, 0x10'),
                    (0x00000397, 'auipc t2, 0x0'), (0x01038393, 'addi t2, t2, 0x10'),
                    (0x0063fe33, 'and t3, t2, t1'), (0x000e3e83, 'ld t4, 0(t3)')],
    'x5-logical': [(0x00040337, 'lui t1, 0x40'), (0x10036313, 'ori t1, t1, 0x100'),
                   (0x000343b3, 'xor t2, t1, zero'), (0xff83fe13, 'andi t3, t2, -8'),
                   (0x000e3e83, 'ld t4, 0(t3)')],
    # the fresh reviewer's plants (AGENT TIME, REVIEW_DIR/myplants.py)
    'srai': [(0xfff80337, 'lui t1, 0xfff80'), (0x41035313, 'srai t1, t1, 0x10'),
             (0x00000397, 'auipc t2, 0x0'), (0x01038393, 'addi t2, t2, 0x10'),
             (0x0063fe33, 'and t3, t2, t1'), (0x000e3e83, 'ld t4, 0(t3)')],
    # plant at +0x6d8 (the `jalr a3` of Allocator::Allocate): the load is reached only by the jalr fall-through
    'jalr': [(0x00040db7, 'lui s11, 0x40'), (0x000680e7, 'jalr a3'), (0x000dbe83, 'ld t4, 0(s11)')],
    # the value leaves the integer file through an FP register and comes back
    'fp': [(0x00040337, 'lui t1, 0x40'), (0xf2030053, 'fmv.d.x ft0, t1'), (0xe20003d3, 'fmv.x.d t2, ft0'),
           (0x0003be83, 'ld t4, 0(t2)')],
    # the second-round reviewer plants (AGENT TIME, REVIEW_DIR/myplants2.py)
    'spill': [(0x00040337, 'lui t1, 0x40'), (0x00613023, 'sd t1, 0(sp)'), (0x00013383, 'ld t2, 0(sp)'),
              (0x0003be83, 'ld t4, 0(t2)')],
    'fpjoin': [(0x00040337, 'lui t1, 0x40'), (0xf2030053, 'fmv.d.x ft0, t1'), (0x00051263, 'bnez a0, 4'),
               (0xe20003d3, 'fmv.x.d t2, ft0'), (0x0003be83, 'ld t4, 0(t2)')],
}


def main(plant, src, fn, off, dst):
    words = PLANTS[plant]
    off = int(off, 0)
    with open(src, 'rb') as f:
        e = ELFFile(f)
        sym = None
        for sec in e.iter_sections():
            if sec.header['sh_type'] in ('SHT_SYMTAB', 'SHT_DYNSYM'):
                for s in sec.iter_symbols():
                    if s.name == fn and s['st_info']['type'] == 'STT_FUNC' and s['st_size']:
                        sym = (s['st_value'], s['st_size'])
        if sym is None:
            raise SystemExit('no sized FUNC symbol %s in %s' % (fn, src))
        segs = [(g['p_vaddr'], g['p_filesz'], g['p_offset']) for g in e.iter_segments() if g['p_type'] == 'PT_LOAD']
    a, z = sym
    if off + 4 * len(words) > z:
        raise SystemExit('plant does not fit in %s (size 0x%x)' % (fn, z))
    va = a + off
    fo = None
    for v, fsz, o in segs:
        if v <= va and va + 4 * len(words) <= v + fsz:
            fo = o + (va - v)
    if fo is None:
        raise SystemExit('0x%x is not in a PT_LOAD file range' % va)
    shutil.copyfile(src, dst)
    with open(dst, 'r+b') as g:
        g.seek(fo)
        old = g.read(4 * len(words))
        g.seek(fo)
        g.write(b''.join(w.to_bytes(4, 'little') for w, _ in words))
    print('# plant %s into a COPY: %s -> %s' % (plant, src, dst))
    print('# %s @0x%x size 0x%x, planted at +0x%x (vaddr 0x%x, file offset 0x%x)' % (fn, a, z, off, va, fo))
    for k, (w, t) in enumerate(words):
        print('#   +0x%03x  %08x  %-20s  (was %08x)' % (off + 4 * k, w, t,
                                                        int.from_bytes(old[4 * k:4 * k + 4], 'little')))


if __name__ == '__main__':
    main(*sys.argv[1:6])
