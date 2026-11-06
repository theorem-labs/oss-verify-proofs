#!/usr/bin/env python3
"""luiconst_rows.py CLOSURE_OUT > luiconst-rows.txt
Every `lui-const+0xOFF[...]=dataflow` acceptance closure_strict3 printed (cmpkit 86da41d3ef68 settles these as constants
by its own dataflow, which does not follow every operation: registered kit limit) as a row in the form luiuse.py /
basecalc.py read: a function line `NAME<TAB>X 0x...` then `   DIFF +0xOFF strictcmp3 lui-in-section: (kit lui-const)`."""
import sys, re, collections
rows = collections.OrderedDict()
for l in open(sys.argv[1]):
    m = re.match(r'^   ACCEPT (\S+) @(0x[0-9a-f]+)/(0x[0-9a-f]+): (.*)$', l)
    if not m: continue
    for k in re.finditer(r'lui-const\+(0x[0-9a-f]+)\[([^\]]*)\]', m.group(4)):
        rows.setdefault((m.group(1), m.group(2)), []).append((int(k.group(1), 16), k.group(2)))
n = 0
for (fn, xa), offs in rows.items():
    print('%s\tX %s (closure_strict3 lui-const acceptances)' % (fn, xa))
    for off, vals in sorted(set(offs)):
        print('   DIFF +%#x strictcmp3 lui-in-section: (kit lui-const, values %s)' % (off, vals)); n += 1
print('# %d lui-const targets in %d functions' % (n, len(rows)), file=sys.stderr)
