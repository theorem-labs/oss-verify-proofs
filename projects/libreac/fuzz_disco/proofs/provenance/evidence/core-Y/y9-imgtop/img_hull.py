#!/usr/bin/env python3
"""img_hull.py --pin PIN

Prints the PT_LOAD hull of the image PIN, one value per line, in the names of lib/Reusable/YImgTop.v:
    IMG_LO <lowest p_vaddr of a PT_LOAD>
    IMG_TOP <highest p_vaddr + p_memsz of a PT_LOAD, rounded up to the page size>
The page size is the largest p_align of the PT_LOAD segments (the alignment the linker gave the loadable segments).
Values are printed as lower-case hex with a 0x prefix. Needs pyelftools.
"""
import argparse
from elftools.elf.elffile import ELFFile


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pin', required=True, help='the pinned image')
    a = ap.parse_args()
    with open(a.pin, 'rb') as f:
        loads = [(s['p_vaddr'], s['p_memsz'], s['p_align']) for s in ELFFile(f).iter_segments() if s['p_type'] == 'PT_LOAD']
    page = max(al for _, _, al in loads)
    lo = min(va for va, _, _ in loads)
    end = max(va + sz for va, sz, _ in loads)
    top = -(-end // page) * page
    print('IMG_LO %#x' % lo)
    print('IMG_TOP %#x' % top)


if __name__ == '__main__':
    main()
