"""zify_flag_sets.py BEFORE BASELINE -- the files of glue rules E6 and E7, read from the image-A core's two flag tables (flag_probe.py read):
BEFORE = the flag each lib/A file starts with in the unit's Require closure before the rules, BASELINE = the same in
fuzz_grant's released lib (655d9c3e47c). E6: the closure sets true where the release sets false; E7: the closure sets
false where the release sets true; a file with no value in either table (rc != 0) is in neither. Prints two lines,
`E6 F...` and `E7 F...` (lib/A file names)."""
import sys


def table(p):
    t = {}
    for line in open(p).read().splitlines()[1:]:
        q = line.split('\t')
        if len(q) >= 3 and q[1] in ('true', 'false'):
            t[q[0].split('/')[-1]] = q[1]
    return t


before, base = table(sys.argv[1]), table(sys.argv[2])
e6 = sorted(f for f in before if before[f] == 'true' and base.get(f) == 'false')
e7 = sorted(f for f in before if before[f] == 'false' and base.get(f) == 'true')
print('E6 ' + ' '.join(e6))
print('E7 ' + ' '.join(e7))
