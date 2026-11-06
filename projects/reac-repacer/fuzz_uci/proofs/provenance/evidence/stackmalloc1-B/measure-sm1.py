#!/usr/bin/env python3
"""measure-sm1.py: the one value of the run no port_core rule decides, measured by its ROLE on the pinned image, with the
same rule on the donor's image as the control (it must print the donor's own value).

  YF0s.v donor line 255  `assert (HSHe : 2148230656 <= SH ...)`: the low-shadow bound of a fake frame in the low zone,
  kLowShadowBeg + TFIB_IMG_END / 8 (YF0r.shLO false; kLowShadowBeg = 0x7fff7000, lib/Reusable/YG0f.v), TFIB_IMG_END =
  IMG_TOP = the page-rounded end of the image's last PT_LOAD (lib/B/YImgTop.v). port_core read the donor value as the
  shadow of a .bss address (0x5f3000 -> 0x5ec780) and wrote 2148227312: the wrong role.

  env: P (libreac's pinned image tree), R (reac-repacer's)."""
import os
from elftools.elf.elffile import ELFFile

K_LOW_SHADOW_BEG = 0x7fff7000


def img_top(path):
    e = ELFFile(open(path, 'rb'))
    end = max(p['p_vaddr'] + p['p_memsz'] for p in e.iter_segments() if p['p_type'] == 'PT_LOAD')
    return end, (end + 0xfff) & ~0xfff


for who, path in (('donor fuzz_grant.asan-ubsan', os.environ['P'] + '/bin/fuzz_grant/fuzz_grant.asan-ubsan'),
                  ('target fuzz_uci.asan-ubsan', os.environ['R'] + '/result/bin/fuzz_uci/fuzz_uci.asan-ubsan')):
    end, top = img_top(path)
    v = K_LOW_SHADOW_BEG + top // 8
    print(f'{who}: last PT_LOAD end {end:#x}, IMG_TOP {top:#x} = {top}, IMG_TOP / 8 = {top // 8}, '
          f'kLowShadowBeg + IMG_TOP / 8 = {v} ({v:#x})')
