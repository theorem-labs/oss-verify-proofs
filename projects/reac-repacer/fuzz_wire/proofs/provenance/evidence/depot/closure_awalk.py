#!/usr/bin/env python3
"""closure_awalk.py FILE... -- second closure rule (pending ruling): in the Require-closure files (knock-only lib/A files),
the module AWalkFw0 in a `Require` line is written as AB1v, the same rename as the consumer merges (--merge
F:2:AWalkFw0=AB1v). In libreac/fuzz_knock, AB1v takes its tfibsegs from AWalkFw0 (one constant); in this unit (grant
lineage) AB1v defines tfibsegs itself, so a closure file must name AB1v's to meet the consumers' (measured: A/AD3g.v:244
`Found no subterm matching "AB1v.tfibsegs"`). Only `Require` lines change; AWalkFw0 then leaves the closure. Each site
is printed (FILE:LINE: before -> after) with the total; a qualified use AWalkFw0.x in code refuses (exit)."""
import re, sys

total = 0
for f in sys.argv[1:]:
    lines = open(f).read().split('\n')
    n = 0
    for i, ln in enumerate(lines):
        if re.search(r'\bAWalkFw0\.[A-Za-z_]', ln):
            sys.exit('closure_awalk: %s:%d uses AWalkFw0 qualified: %s' % (f, i + 1, ln.strip()))
        if re.search(r'\bRequire\b', ln) and re.search(r'\bAWalkFw0\b', ln):
            new = re.sub(r'\s*\bAWalkFw0\b', '', ln) if re.search(r'\bAB1v\b', ln) else re.sub(r'\bAWalkFw0\b', 'AB1v', ln)
            print('%s:%d: %s  ->  %s' % (f.split('/lib/')[-1], i + 1, ln.strip(), new.strip()))
            lines[i] = new
            n += 1
    if n:
        open(f, 'w').write('\n'.join(lines))
    total += n
print('closure_awalk: %d Require line(s) changed' % total)
