#!/usr/bin/env python3
"""measure-sm1.py: the image-B record's one override value, measured by its ROLE on the image-A images, with the donor
image as the control.

  AF0s.v donor line 253 `assert (HSHe : 2148213760 <= SH ...)`: a lower bound of the shadow of a fake frame in the low
  zone. The image-B record's donor (grant B's YF0s.v:255) states it exactly, kLowShadowBeg + TFIB_IMG_END / 8
  (YF0r.shLO false; kLowShadowBeg = 0x7fff7000, lib/Reusable/YG0f.v; TFIB_IMG_END = IMG_TOP = the page-rounded end of the
  image's last PT_LOAD, lib/Reusable/YImgTop.v), and needed an override. Grant A's released AF0s.v states a smaller
  constant, 2148213760 = 0x800b2400, which port_core leaves unchanged. The assertion is proved by lia from
  SH >= kLowShadowBeg + IMG_TOP / 8 + ...: it holds on an image exactly when the donor constant is at most that image's
  kLowShadowBeg + IMG_TOP / 8. This script prints that value for both images and checks the donor constant against
  each (exit 1 if it exceeds either).

  env: P (libreac's pinned image tree), R (reac-repacer's)."""
import os, sys
from elftools.elf.elffile import ELFFile

K_LOW_SHADOW_BEG = 0x7fff7000
DONOR_BOUND = 2148213760


def img_top(path):
    e = ELFFile(open(path, 'rb'))
    end = max(p['p_vaddr'] + p['p_memsz'] for p in e.iter_segments() if p['p_type'] == 'PT_LOAD')
    return end, (end + 0xfff) & ~0xfff


bad = 0
for who, path in (('donor fuzz_grant.asan', os.environ['P'] + '/bin/fuzz_grant/fuzz_grant.asan'),
                  ('target fuzz_uci.asan', os.environ['R'] + '/result/bin/fuzz_uci/fuzz_uci.asan')):
    end, top = img_top(path)
    v = K_LOW_SHADOW_BEG + top // 8
    ok = DONOR_BOUND <= v
    bad += not ok
    print(f'{who}: last PT_LOAD end {end:#x}, IMG_TOP {top:#x} = {top}, IMG_TOP / 8 = {top // 8}, '
          f'kLowShadowBeg + IMG_TOP / 8 = {v} ({v:#x}); the donor bound {DONOR_BOUND} ({DONOR_BOUND:#x}) '
          f'{"<=" if ok else ">"} it: {"holds" if ok else "FAILS"}')
sys.exit(1 if bad else 0)
