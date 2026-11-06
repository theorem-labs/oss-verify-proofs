#!/usr/bin/env python3
"""run_atable.py IMAGE TWIN_LISTING [ARGS...] -- run atable.py (startup-set 2026-10-30d, sha256 e88affcf0526; internal record),
unchanged, from TOOLS/startup-set/ with the twin symbol listing as its twin.

atable's SymSource takes from the twin ELF its STT_FUNC symbols with a nonzero value (the first one of each name, in .symtab
order), after checking that the twin's PT_LOAD bytes are the image's. For a listing this driver gives SymSource the same
symbols: the t/T/w/W rows with a nonzero address, the first one of each name, in the listing's (.symtab) order. In place of
the PT_LOAD check it requires the listing's header to name the image's sha256 as its pinned image (twin_symbols.py made
the PT_LOAD check when it wrote the listing). A twin ELF or an AB1w.v goes to atable's own SymSource. Every argument goes
to atable as given.
"""
import hashlib
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import twinlist  # noqa: E402

atable = twinlist.load('startup-set', 'atable')
_symsource_init = atable.SymSource.__init__


def symsource_init(self, symsrc, image):
    if symsrc.endswith('.v') or not twinlist.is_listing(symsrc):
        return _symsource_init(self, symsrc, image)
    pin = twinlist.header(symsrc)[1]
    if pin != hashlib.sha256(image.b).hexdigest():
        raise ValueError(f'twin listing {symsrc}: its header does not name the image {image.path} as its pinned image')
    self.kind = 'elf'
    self.table = {}
    for value, size, letter, name in twinlist.rows(symsrc):
        if letter in 'tTwW' and value:
            self.table.setdefault(name, (value, size))
    self.desc = symsrc


atable.SymSource.__init__ = symsource_init
twinlist.run_main(atable, sys.argv[1:])
