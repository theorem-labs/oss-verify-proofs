#!/usr/bin/env python3
"""otherrows.py -- the function names the comparison kit reports as `other` for one root: the by-name closure rows of
closure_strict2's output (as printed, name{file} when qualified), then the rows of paircl's output whose X function is
not among them (paircl prints a name cut to 80 characters and the X address: the row is resolved by that address to the
sized FUNC symbol(s) of X starting there). Read-only. Prints one comma-separated list.
usage: otherrows.py X_ELF CLOSURE_OUT PAIRCL_OUT ROOT"""
import re, sys
from elftools.elf.elffile import ELFFile
xp, co, po, root = sys.argv[1:5]
names = []; addrs = set(); cur = None
for l in open(co):
    if not l.startswith('   '): cur = l.split('\t')[0]; continue
    m = re.match(r'   (\S+) @(0x[0-9a-f]+): ', l)
    if cur == root and m and m.group(1) not in names: names.append(m.group(1)); addrs.add(int(m.group(2), 16))
at = {}
for s in ELFFile(open(xp, 'rb')).get_section_by_name('.symtab').iter_symbols():
    if s['st_info']['type'] == 'STT_FUNC' and s['st_size'] > 0: at.setdefault(s['st_value'], []).append(s.name)
for l in open(po):
    if not l.startswith('   ') or l.startswith('   CONFLICT') or l.startswith('   ACCEPT'): continue
    p = l.split(); xa = int(p[1], 16)
    if xa in addrs: continue
    c = sorted(set(at.get(xa, [])))
    if len(c) != 1: sys.exit('otherrows: paircl row at %#x has %d names: %s' % (xa, len(c), c))
    if c[0] not in names: names.append(c[0]); addrs.add(xa)
print(','.join(names))
