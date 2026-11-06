#!/usr/bin/env python3
"""run_binmatch_plan.py DONOR_AB05.v OUT.v --binmatch BINMATCH.json --cgif CGIF_IMAGE --disco DISCO_IMAGE --funcs FUNCS.tsv
--names TWIN_LISTING -- run binmatch_plan.py and the imgref.py it imports (copy as found, not of record: the tools that
produced the AB05 plan body, tools/startup-cited/binmatch_plan/7f058fcb8e4a/ at registry commit 5fd6732f0003, sha256
7f058fcb8e4a, 064874159929), both unchanged, from TOOLS/plan/ on these inputs.

binmatch_plan names its function pairing as a host-path constant (BM) and takes DONOR_AB05.v OUT.v from sys.argv; imgref
names the donor image, the unit's image, its unstripped twin and the function table as host-path constants (CGIF, DISCO,
DISCO_DEBUG, FUNCS). This driver sets those five constants to the arguments before either tool reads them.

imgref reads the twin for the unit's symbols (value, size, name; value nonzero) and section table, which it uses only to
name addresses in printed evidence (stdout), never for a value binmatch_plan writes. For a listing this driver gives imgref
the listing's symbols with a nonzero address (sorted, as imgref sorts them) and the image's own section table (the twin's
is not in the listing), after checking that the listing's header names the image's sha256 as its pinned image. An ELF
goes to imgref's own reader.
"""
import argparse
import hashlib
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import twinlist  # noqa: E402

ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
ap.add_argument('src')
ap.add_argument('out')
ap.add_argument('--binmatch', required=True, help='the function pairing (binmatch.cgif.asan.json)')
ap.add_argument('--cgif', required=True, help="the donor's pinned image (cgif_file_fuzzer.asan)")
ap.add_argument('--disco', required=True, help="the unit's pinned image (fuzz_disco.asan)")
ap.add_argument('--funcs', required=True, help="the unit's function table with its cgif pairing (funcs.asan.tsv)")
ap.add_argument('--names', required=True, help="the twin symbol listing of the unit's image")
a = ap.parse_args()

imgref = twinlist.load('plan', 'imgref')
_Elf = imgref.Elf


class Elf(_Elf):
    def __init__(self, path):
        if not twinlist.is_listing(path):
            return super().__init__(path)
        image = _Elf(imgref.DISCO)
        if twinlist.header(path)[1] != hashlib.sha256(image.b).hexdigest():
            sys.exit('run_binmatch_plan: twin listing %s: its header does not name %s as its pinned image' % (path, imgref.DISCO))
        self.b, self.loads, self.sections = image.b, image.loads, image.sections
        self.syms = sorted((value, size, name, None) for value, size, letter, name in twinlist.rows(path) if value)


imgref.Elf = Elf
imgref.CGIF, imgref.DISCO, imgref.DISCO_DEBUG, imgref.FUNCS = a.cgif, a.disco, a.names, a.funcs
binmatch_plan = twinlist.load('plan', 'binmatch_plan')
if binmatch_plan.imgref is not imgref:
    sys.exit('run_binmatch_plan: binmatch_plan imported another imgref (%s)' % binmatch_plan.imgref.__file__)
binmatch_plan.BM = a.binmatch
twinlist.run_main(binmatch_plan, [a.src, a.out])
