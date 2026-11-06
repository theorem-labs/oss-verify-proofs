#!/usr/bin/env python3
"""run_gen_ad1k.py [ARGS...] -- run gen_ad1k.py (startup-set 2026-10-30d, sha256 2a6885e5c27f; internal record), unchanged,
from TOOLS/startup-set/ with the twin symbol listing as its --twin.

gen_ad1k's all_symbols reads the twin ELF's .symtab: (value, size, name) of every named symbol that is not a mapping symbol
(`$...`), in .symtab order; gen_ad1k takes __stdout_FILE / __stderr_FILE from it and the symbol that holds FILE.buf. For a
listing this driver gives the same rows from it, in its (.symtab) order. The listing leaves out the source-file and
undefined symbols (value 0, size 0), so no name gen_ad1k looks up and no address it looks for changes. A twin ELF goes to
gen_ad1k's own all_symbols. Every argument goes to gen_ad1k as given.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import twinlist  # noqa: E402

gen_ad1k = twinlist.load('startup-set', 'gen_ad1k')
_all_symbols = gen_ad1k.all_symbols


def all_symbols(path):
    if not twinlist.is_listing(path):
        return _all_symbols(path)
    return [(value, size, name) for value, size, letter, name in twinlist.rows(path) if not name.startswith('$')]


gen_ad1k.all_symbols = all_symbols
twinlist.run_main(gen_ad1k, sys.argv[1:])
