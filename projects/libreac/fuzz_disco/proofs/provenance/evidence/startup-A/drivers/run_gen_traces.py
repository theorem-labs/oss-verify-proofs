#!/usr/bin/env python3
"""run_gen_traces.py IMAGE TWIN_LISTING [ARGS...] -- run gen_traces.py (indexed as found, not of record:
tools/startup-cited/gen_traces/59966c883510/ at registry commit 5fd6732f0003, sha256 59966c883510), unchanged, from
TOOLS/traces/ on the modules beside it and the twin symbol listing.

gen_traces puts a host directory of the ELF kit (its KIT constant) first on sys.path and imports rvelf from it, and
resolve_code (sym_ranges, text_code) from its own directory. This driver imports TOOLS/traces/rvelf.py (pg-reloc-portcore
e0e94a04094b, sha256 23152d9ca11c; internal record) and TOOLS/traces/resolve_code.py (indexed as found, not of record:
tools/startup-cited/resolve_code/81803218fe79/ at registry commit 5fd6732f0003, sha256 81803218fe79) before gen_traces
is imported, so its imports take those and nothing from the host directory; it checks that before it runs gen_traces.

resolve_code's sym_ranges takes from the twin ELF its STT_FUNC symbols with a nonzero size, as (lo, hi, name), sorted
and without duplicates. For a listing this driver gives the same symbols: its t/T/w/W rows with a nonzero size. A twin
ELF goes to resolve_code's own sym_ranges. Every argument goes to gen_traces as given.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import twinlist  # noqa: E402

rvelf = twinlist.load('traces', 'rvelf')
resolve_code = twinlist.load('traces', 'resolve_code')
_sym_ranges = resolve_code.sym_ranges


def sym_ranges(path):
    if not twinlist.is_listing(path):
        return _sym_ranges(path)
    return sorted({(value, value + size, name) for value, size, letter, name in twinlist.rows(path)
                   if letter in 'tTwW' and size > 0})


resolve_code.sym_ranges = sym_ranges
gen_traces = twinlist.load('traces', 'gen_traces')
traces = os.path.join(twinlist.tools_dir(), 'traces')
for m in (rvelf, resolve_code, gen_traces):
    if sys.modules[m.__name__] is not m or os.path.dirname(os.path.abspath(m.__file__)) != traces:
        sys.exit('run_gen_traces: module %s is not the copy in %s' % (m.__name__, traces))
twinlist.run_main(gen_traces, sys.argv[1:])
