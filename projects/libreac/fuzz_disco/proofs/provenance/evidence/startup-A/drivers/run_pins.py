#!/usr/bin/env python3
"""run_pins.py [ARGS...] -- run pins.py (startup-set 2026-10-30d, sha256 4778073f01be; internal record), unchanged, from
TOOLS/startup-set/ with the twin symbol listing as its --twin.

pins' provenance line ends `; unstripped twin sha256 <sha256 of the --twin file> *)`. For a listing this driver writes the
sha256 of the twin the listing was made from (its header names it), so the line names the same twin as a run on the twin
itself. The pin gate is pins' own. pins reads its pin table from OSSV_BINARIES_TSV (run.sh sets it to the repository's
index/binaries.tsv); without it pins would fall back on a host checkout, so this driver refuses to run when it is unset.
Every argument goes to pins as given.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import twinlist  # noqa: E402

if not os.environ.get('OSSV_BINARIES_TSV'):
    sys.exit('run_pins: OSSV_BINARIES_TSV is not set: name the pin table (the repository\'s index/binaries.tsv)')
pins = twinlist.load('startup-set', 'pins')
_provenance = pins.provenance


def provenance(image, twin=None, index=None):
    if not twin or not twinlist.is_listing(twin):
        return _provenance(image, twin, index)
    line = _provenance(image, None, index)
    assert line.endswith(' *)'), line
    return line[:-len(' *)')] + '; unstripped twin sha256 %s *)' % twinlist.header(twin)[0]


pins.provenance = provenance
twinlist.run_main(pins, sys.argv[1:])
