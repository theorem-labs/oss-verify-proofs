#!/usr/bin/env python3
"""How many .symtab FUNC entries carry each function name of the code-identity list, in each twin.

  symcount.py PAIRS FM_TWIN TAG=TWIN ...  > symcount.tsv

PAIRS: codeid/pairs.tsv. One row per function name (and alias) of the list: the number of STT_FUNC .symtab entries of
that name in the fm twin and in each image twin, and their addresses when there is more than one. A count above 1
means a lookup by name is ambiguous (a lookup that takes the lowest address may pick another copy); codeid_kit.py
compares every pair by the addresses in PAIRS and, for such names, also records the lowest-address compare.
"""
import collections
import csv
import hashlib
import os
import sys

from elftools.elf.elffile import ELFFile


def funcs(path):
    out = collections.defaultdict(list)
    for y in ELFFile(open(path, 'rb')).get_section_by_name('.symtab').iter_symbols():
        if y.name and y['st_info']['type'] == 'STT_FUNC' and y['st_shndx'] != 'SHN_UNDEF':
            out[y.name].append(y['st_value'])
    return out


def main():
    if len(sys.argv) < 4:
        sys.exit(__doc__)
    pairs, fm = sys.argv[1:3]
    imgs = [a.split('=', 1) for a in sys.argv[3:]]
    tw = [('fm', fm)] + imgs
    F = {t: funcs(p) for t, p in tw}
    names = []
    for r in csv.DictReader(open(pairs), delimiter='\t'):
        for n in (r['fm function'], r['aliases']):
            if n not in ('', '-') and n not in names:
                names.append(n)
    out = ['# STT_FUNC .symtab entries per name; twins: %s' % ', '.join(
        '%s %s sha256 %s' % (t, os.path.basename(p), hashlib.sha256(open(p, 'rb').read()).hexdigest()) for t, p in tw)]
    out.append('\t'.join(['name'] + ['count %s' % t for t, _ in tw] + ['addresses where a count is above 1']))
    for n in names:
        c = [len(F[t].get(n, ())) for t, _ in tw]
        more = '; '.join('%s %s' % (t, ' '.join(hex(a) for a in sorted(F[t][n]))) for t, _ in tw
                         if len(F[t].get(n, ())) > 1)
        out.append('\t'.join([n] + [str(x) for x in c] + [more]))
    many = sum(1 for l in out[2:] if any(int(x) > 1 for x in l.split('\t')[1:1 + len(tw)]))
    out.insert(1, '# %d names; %d with more than one entry in some twin' % (len(names), many))
    sys.stdout.write('\n'.join(out) + '\n')


if __name__ == '__main__':
    main()
