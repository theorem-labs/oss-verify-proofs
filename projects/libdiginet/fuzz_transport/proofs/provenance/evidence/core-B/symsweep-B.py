#!/usr/bin/env python3
"""symsweep-B.py WORK DONOR_PIN DONOR_TWIN TARGET_PIN TARGET_TWIN: the donor-paired symbol + offset sweep of a port_core
run (the libreac owner 19:51Z, tools registry KNOWN LIMIT: a by-address move onto an unrelated cell reads SAME).

For every relocated numeral of the run (check.tsv rows old -> new, with fixed.tsv's later value where it wrote one)
whose DONOR value lies in a data section of the donor image (anything but .text / .plt and the ELF header), resolve
donor symbol + offset on the donor twin and target symbol + offset on the target twin (the covering sized OBJECT /
FUNC / NOTYPE symbol, else the section + offset). A row is a HIT when the target value lies in .got / .got.plt while
the donor value does not, or when the two symbol names differ (STT_FILE-local names compared bare). Expected 0 hits.
Rows whose new value equals the old one are listed apart (kept numerals: SAME image quantity, no move).
Output: one line per hit, then counts. Control: plant a row moved onto a .got cell (the registry's example class)."""
import bisect, csv, sys
from elftools.elf.elffile import ELFFile

work, dpin, dtwin, tpin, ttwin = sys.argv[1:6]


class Img:
    def __init__(self, pin, twin):
        self.secs = sorted((s['sh_addr'], s['sh_addr'] + s['sh_size'], s.name) for s in ELFFile(open(pin, 'rb')).iter_sections()
                           if s['sh_addr'] and s['sh_flags'] & 2)
        syms = [(y['st_value'], y['st_size'], y.name) for y in ELFFile(open(twin, 'rb')).get_section_by_name('.symtab').iter_symbols()
                if y.name and y['st_value'] and y['st_info']['type'] in ('STT_OBJECT', 'STT_FUNC', 'STT_NOTYPE', 'STT_COMMON')]
        self.syms = sorted(syms)
        self.starts = [s[0] for s in self.syms]

    def sec(self, a):
        for lo, hi, n in self.secs:
            if lo <= a < hi:
                return n
        return None

    def name(self, a):
        i = bisect.bisect_right(self.starts, a) - 1
        while i >= 0 and self.syms[i][0] <= a:
            v, z, n = self.syms[i]
            if a < v + max(z, 1):
                return f'{n}+{a - v:#x}'
            if z == 0 and v == a:
                return f'{n}+0x0'
            i -= 1
        s = self.sec(a)
        if s:
            lo = next(l for l, h, nn in self.secs if nn == s)
            return f'[{s}]+{a - lo:#x}'
        return None


D, T = Img(dpin, dtwin), Img(tpin, ttwin)
fixed = {}
for r in csv.DictReader(open(f'{work}/fixed.tsv'), delimiter='\t'):
    fixed[(r['file'], r['line'], r['old'])] = r['new']
CODE = {'.text', '.plt', '.init', '.fini'}
hits, kept, n = [], 0, 0
for r in csv.DictReader(open(f'{work}/check.tsv'), delimiter='\t'):
    try:
        old = int(r['old'], 0)
        new = int(fixed.get((r['file'], r['line'], r['old']), r['new']), 0)
    except (ValueError, TypeError):
        continue
    ds = D.sec(old)
    if ds is None or ds in CODE:
        continue
    n += 1
    if new == old:
        kept += 1
    ts = T.sec(new)
    dn, tn = D.name(old), T.name(new)
    bare = lambda s: s.split('+')[0] if s else s
    got = ts in ('.got', '.got.plt') and ds not in ('.got', '.got.plt')
    if got or bare(dn) != bare(tn):
        hits.append((r['file'], r['line'], hex(old), dn, ds, hex(new), tn, ts, 'GOT' if got else 'OTHER-SYMBOL'))
for h in hits:
    print('HIT\t' + '\t'.join(map(str, h)))
print(f'rows naming a donor data object: {n} (kept unmoved {kept}); hits {len(hits)}')
