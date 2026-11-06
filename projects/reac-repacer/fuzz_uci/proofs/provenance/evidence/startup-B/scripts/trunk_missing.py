#!/usr/bin/env python3
"""trunk_missing.py LIBDIR FILE... -- for each generated lib/B file, the unit-lib modules it Requires (From
OssFuzzTheorems.Proofs.reac_repacer.fuzz_uci.lib.<DIR> Require [Import|Export] M ...) that LIBDIR (the trunk clone's
proofs/reac-repacer/fuzz_uci/lib, with this lane's lib/B files in place) does not hold as <DIR>/<M>.v. The images module
OssFuzzTheorems.reac_repacer.fuzz_uci.images.* is the unit's statements (projects/reac-repacer/fuzz_uci/images), present.
Prints one line per file and the union; exit 0."""
import os, re, sys

lib, files = sys.argv[1], sys.argv[2:]
rx = re.compile(r'From\s+OssFuzzTheorems\.Proofs\.reac_repacer\.fuzz_uci\.lib\.(\w+)\s+Require(?:\s+Import|\s+Export)?\s+'
                r'([\w.\'\s]+?)\.(?=\s|$)')
union = {}
for f in files:
    t = open(f).read()
    mods = [(d, m) for mm in rx.finditer(t) for d, m in [(mm.group(1), x) for x in mm.group(2).split()]]
    miss = sorted({'%s.%s' % (d, m) for d, m in mods if not os.path.exists(os.path.join(lib, d, m.replace('.', '/') + '.v'))})
    for x in miss:
        union.setdefault(x, []).append(os.path.basename(f)[:-2])
    print('%s: %d unit modules Required, %d missing in the trunk: %s' % (os.path.basename(f), len(set(mods)), len(miss),
                                                                        ' '.join(miss) or '-'))
print('UNION %d missing modules: %s' % (len(union), ' '.join(sorted(union))))
