#!/usr/bin/env python3
"""flag_probe.py make LIB OUTDIR  |  flag_probe.py after LIB OUTDIR FILE...  |  flag_probe.py read OUTDIR > TSV

The measurement behind glue rules E6 / E7: the value of Zify.zify_convert_to_euclidean_division_equations_flag that a
lib/A file sees, read by Rocq itself (`Print Ltac`).

make: the value a file's body STARTS with. For every LIB/A/<F>.v, writes OUTDIR/P<F>.v = <F>'s leading Require block
(through the end of its last Require sentence, without an E6 / E7 line), then `Print Ltac Zify...flag.`. Run on
fuzz_grant's released lib (the baseline of record) it gives the release value; run on the unit's lib it gives the value
the unit's Require closure sets ("before").
after: the value at the END of each named laid file. Writes OUTDIR/P<F>.v = the whole file LIB/A/<F>.v as laid (its
E6 / E7 line included), then `Print Ltac Zify...flag.`: the compile proves the whole file and prints the value after
its last sentence, so it also shows that nothing in the body overrides the line. Nothing is added but the Print.
The probes are compiled by `rocq compile` against the built lib of the tree under test (run-flag-probe.sh: the unit's
-Q mappings, -R OUTDIR Fx), one compile per probe; each output goes to OUTDIR/P<F>.out with a last line `rc=N`.
read: one row per probe: file, flag (the last value printed; - when the compile failed), rc."""
import os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zify_flag import LINE, LINE_E7  # noqa: E402

PRINT = 'Print Ltac Zify.zify_convert_to_euclidean_division_equations_flag.'


def make(src, out):
    os.makedirs(out, exist_ok=True)
    n = 0
    for f in sorted(os.listdir(os.path.join(src, 'A'))):
        if not f.endswith('.v'):
            continue
        t = open(os.path.join(src, 'A', f), encoding='utf-8').read().split('\n')
        req = [k for k, l in enumerate(t[:120]) if re.search(r'\bRequire\b', l)]
        if not req:
            continue
        e = req[-1]
        while e < len(t) and not t[e].rstrip().endswith('.'):
            e += 1
        body = [l for l in t[:e + 1] if l not in (LINE, LINE_E7)] + [PRINT, '']
        open(os.path.join(out, 'P' + f), 'w', encoding='utf-8').write('\n'.join(body))
        n += 1
    print('flag_probe make: %d probe(s) in %s' % (n, out))


def after(src, out, files):
    os.makedirs(out, exist_ok=True)
    for f in files:
        t = open(os.path.join(src, 'A', f), encoding='utf-8').read()
        open(os.path.join(out, 'P' + f), 'w', encoding='utf-8').write(t.rstrip('\n') + '\n' + PRINT + '\n')
    print('flag_probe after: %d probe(s) in %s' % (len(files), out))


def read(out):
    print('file\tflag\trc')
    for f in sorted(os.listdir(out)):
        if f.startswith('P') and f.endswith('.out'):
            t = open(os.path.join(out, f), errors='replace').read()
            m = re.findall(r'zify_convert_to_euclidean_division_equations_flag :=\s*constr:\((true|false)\)', t)
            rc = (re.findall(r'rc=(\d+)', t) or ['?'])[-1]
            print('A/%s.v\t%s\t%s' % (f[1:-4], m[-1] if m else '-', rc))


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[:1] == ['make'] and len(a) == 3:
        make(a[1], a[2])
    elif a[:1] == ['after'] and len(a) >= 4:
        after(a[1], a[2], a[3:])
    elif a[:1] == ['read'] and len(a) == 2:
        read(a[1])
    else:
        sys.exit(__doc__)
