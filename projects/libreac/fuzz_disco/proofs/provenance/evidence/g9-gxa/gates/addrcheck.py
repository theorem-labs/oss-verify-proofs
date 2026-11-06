#!/usr/bin/env python3
"""The address checker runs of the GXA / Bz memory layers, re-made by the checker itself.

  addrcheck.py KIT_DIR HUB OUT_DIR R=PIN:TWIN A=PIN:TWIN B=PIN:TWIN

KIT_DIR: the address checker kit 16f8a030c869 (port_addr_check.py, scan_literals.py, insn-targets/insn_targets.py; a
check tool, cited and not copied); each file's sha256 is checked. HUB: a git repository that holds the commits named
below (the checker reads the source and the ported file from it). R: the fuzz_reply asan image, the donor image of
the image-A memset walk and of the A table; A and B: the two fuzz_disco images (asan, asan-ubsan). PIN is the
stripped image of record, TWIN its unstripped twin (the checker reads its .symtab); PT_LOAD 2..4 of each twin must be
byte-equal to its pin's, and each pair's sha256 is written to standard error.

Each run checks one ported file against its source file, as the record ran it: same files (by commit), same images,
same renames. The outputs go to OUT_DIR under the file names of the record (gates.py addrcheck-A / addrcheck-B read
them); the runs that the record superseded by a renamed run are not repeated.
"""
import hashlib
import os
import subprocess
import sys

from elftools.elf.elffile import ELFFile

KIT = {'port_addr_check.py': '16f8a030c869fb97eff621fc97728d6c446c4d5ee1b005a8fedc9fc5768dfcbf',
       'scan_literals.py': 'ae01d69b2ee4af269258982bef0de35a38a44d2b8832b62ef217e58439cd5804',
       'insn-targets/insn_targets.py': '2a46b7498ec8746c998476f2146b7cb059903a98c9f5036eed1290a7064b4e73'}
REPLY = 'proofs/plugin-hostd/fuzz_reply/lib/'
DISCO = 'proofs/libreac/fuzz_disco/lib/'
DONOR = '86b50358d34d6323ebebcb6c366bb44937af56a1'     # the fuzz_reply files the image-A walk and table copy
MEMSET_A = '3e25af8fd6216efb52d758b0e00db699e6a00ff7'  # lib/A memset walk relocated to image A
TABLE_A = 'd44a6f47bca754d0883affc1bd99fdb26699d45b'   # lib/A RT_gxa_mem_Tbl.v and its call contracts
SOURCE_B = '8816cefba36f84c0ad04f0bbe790808a6a480d24'  # lib/A, the source of the image-B twins
TWINS_B = '406eaba3f51eee9ee9f6ee67d2397d2be3ba8a2a'   # lib/B twins
CALLS_B = '79bf1bd8f6dc5c5839241c2f148e53eb33220033'   # lib/B table, call contracts and image record
TWIN_FILES = ['Bz/A/F_memset', 'Bz/A/I_amemcpy', 'Bz/A/I_amemcpyw', 'Bz/A/I_amemcpyw2', 'Bz/A/I_consts',
              'Bz/A/I_imemset', 'Bz/A/I_memcpy', 'Bz/A/I_memcpyw', 'Bz/A/I_memcpyw2', 'Bz/A/I_memsetw',
              'Bz/A/R_isPoisoned', 'Bz/A/R_m2s', 'Bz/A/R_memiszero', 'Bz/A/R_small', 'Bz/Lib/ImageA', 'Prog/memcpy',
              'Prog/memcpy_c', 'Prog/memcpy_same', 'Prog/memcpy_same_c', 'Prog/memset_c', 'RT_mem_bz', 'R_memset']
# (output name, source commit, source path, ported commit, ported path, source image, ported image, extra arguments)
RUNS = ([('pac-%s.tsv' % f, DONOR, REPLY + 'A/Bz/A/%s.v' % f, MEMSET_A, DISCO + 'A/Bz/A/%s.v' % f, 'R', 'A', [])
         for f in ('I_memsetw', 'I_imemset')]
        + [('pac-%s.tsv' % f, DONOR, REPLY + 'A/%s.v' % f, TABLE_A, DISCO + 'A/%s.v' % f, 'R', 'A', [])
           for f in ('RT_gxa_calls_mem', 'RT_gxa_mem_Tbl')]
        + [('lib_B_%s.v.tsv' % p.replace('/', '_'), SOURCE_B, DISCO + 'A/%s.v' % p, TWINS_B, DISCO + 'B/%s.v' % p,
            'A', 'B', []) for p in TWIN_FILES]
        + [('lib_B_%s.v.tsv' % p, SOURCE_B, DISCO + 'A/%s.v' % p, CALLS_B, DISCO + 'B/%s.v' % p, 'A', 'B', [])
           for p in ('RT_gxa_bridge', 'RT_gxa_mem_Tbl')]
        + [('lib_B_RT_gxa_calls_mem.v.ren.tsv', SOURCE_B, DISCO + 'A/RT_gxa_calls_mem.v', CALLS_B,
            DISCO + 'B/RT_gxa_calls_mem.v', 'A', 'B',
            ['--rename', 'stack_contract_A=stack_contract_B', '--rename', 'A_sym_=B_sym_']),
           ('lib_CJ_RL_I_RecAsanB.v.ren.tsv', SOURCE_B, DISCO + 'CJ/RL/I/RecAsanA.v', CALLS_B,
            DISCO + 'CJ/RL/I/RecAsanB.v', 'A', 'B', ['--rename', 'RecAsanA=RecAsanB', '--rename', '_asan=_asan_ubsan'])])


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def loads(path):
    return [(g['p_vaddr'], g['p_memsz'], g.data()) for g in ELFFile(open(path, 'rb')).iter_segments()
            if g['p_type'] == 'PT_LOAD']


def main(a):
    if len(a) != 6:
        sys.exit(__doc__)
    kit, hub, out = a[:3]
    img = dict(x.split('=', 1) for x in a[3:])
    if sorted(img) != ['A', 'B', 'R']:
        sys.exit(__doc__)
    for n, h in KIT.items():
        if sha(os.path.join(kit, n)) != h:
            sys.exit('addrcheck.py: %s is not the kit file %s' % (n, h[:12]))
    for k in 'RAB':
        pin, twin = img[k].split(':', 1)
        lp, lt = loads(pin), loads(twin)
        same = len(lp) >= 4 and len(lt) >= 4 and lp[1:4] == lt[1:4]
        sys.stderr.write('image %s: pin %s sha256 %s; twin %s sha256 %s; PT_LOAD 2..4 byte-equal: %s\n'
                         % (k, os.path.basename(pin), sha(pin), os.path.basename(twin), sha(twin), 'yes' if same else 'NO'))
        if not same:
            sys.exit('addrcheck.py: the twin of image %s is not its pin in PT_LOAD 2..4' % k)
    os.makedirs(out, exist_ok=True)
    for name, sc, sp, dc, dp, si, di, extra in RUNS:
        r = subprocess.run([sys.executable, os.path.join(kit, 'port_addr_check.py'), '--git', hub,
                            '--src', '%s:%s' % (sc, sp), '--dst', '%s:%s' % (dc, dp), '--src-image', 'A=' + img[si],
                            '--dst-image', 'A=' + img[di], '--cache', os.path.join(out, 'cache'),
                            '--out', os.path.join(out, name)] + extra, capture_output=True, text=True)
        if r.returncode:
            sys.exit('addrcheck.py: the checker failed on %s (rc %d): %s' % (name, r.returncode, r.stderr[-400:]))


if __name__ == '__main__':
    main(sys.argv[1:])
