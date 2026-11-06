#!/usr/bin/env python3
"""The image facts the start-up rules lean on, printed for the four images (ours and the donor, A and B):
the toolchain strings (.comment), the strings __asan/__ubsan/__lsan_default_options return (decoded auipc+addi),
the PT_TLS header, and the sizes of the run-time objects whose start-up words the files keep from the donor.

  premises.py IMG_DIR      (cmd.A.pin/.twin, cmd.B.*, cgif.A.*, cgif.B.*)"""
import os
import sys

from elftools.elf.elffile import ELFFile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import imgmeas  # noqa: E402

OBJS = ['_ZN6__asanL8instanceE', 'builtin_tls', '__pthread_tsd_main', '__libc', '_ZN11__sanitizer21common_flags_dont_useE',
        '_ZN6__asan28asan_flags_dont_use_directlyE', '_ZN11__sanitizerL10stackStoreE', '_ZN11__sanitizerL8theDepotE',
        'read_stage', '_ZN11__sanitizerL26internal_alloc_placeholderE']
OPTS = ['__asan_default_options', '__ubsan_default_options', '__lsan_default_options', '__asan_default_suppressions']


def ret_str(im, pc):
    """the string a 12-byte `auipc a0; addi a0, a0, lo; ret` function returns."""
    w0, w1 = im.word(pc, 4), im.word(pc + 4, 4)
    if w0 & 0x7F != 0x17 or w1 & 0x7F != 0x13:
        return None
    t = pc + imgmeas._sx(w0 & 0xFFFFF000, 32) + imgmeas._sx(w1 >> 20, 12)
    return im.cstr(t)


def main():
    d = sys.argv[1]
    for role in ('cmd.A', 'cgif.A', 'cmd.B', 'cgif.B'):
        im = imgmeas.Img(os.path.join(d, role + '.pin'), os.path.join(d, role + '.twin'), role)
        with open(os.path.join(d, role + '.twin'), 'rb') as f:
            c = ELFFile(f).get_section_by_name('.comment').data()
        comment = sorted(set(x.decode() for x in c.split(b'\0') if x))
        print(f'{role} pin {im.sha_pin} twin {im.sha_twin}')
        print(f'  .comment {comment}')
        for n in OPTS:
            print(f'  {n} returns {ret_str(im, im.by_name[n][0][0])!r}')
        print(f'  PT_TLS (filesz, memsz, align) {im.tls_hdr}')
        print(f'  asan_globals descriptors {len(im.descriptors())}')
        print('  sizes ' + ', '.join(f'{n}={im.by_name[n][0][1]:#x}' for n in OBJS if n in im.by_name))


if __name__ == '__main__':
    main()
