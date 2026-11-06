#!/usr/bin/env python3
"""Symbol facts of the unstripped twins behind every numeral the G9 tool moved, as text (no binary is shipped).

  twin_facts.py TABLE FM_TWIN FM_PIN TWIN PIN > facts.tsv

TABLE: a combined per-numeral table of one target (g9tool/g9-table-disco-<A|Y>.tsv). FM_TWIN / FM_PIN and TWIN / PIN:
the unstripped and the stripped fm image and target image. The header names each twin's and pin's sha256 and checks
that PT_LOAD 2..4 of twin and pin are byte-equal (so the twin's symbols describe the pin's code and data). One row per
distinct (fm value, target value) pair the tool moved (how: applied, propagated, hand): each value resolved in its own
twin the way the same-name rule of numerals.py reads it: the smallest FUNC / OBJECT symbol that contains it (all names
at that address, + offset), else the end of a symbol, else in .got the symbol the 8-byte slot holds, else in read-only
data the C string there, else a named bound (a PT_LOAD or section start or end, also rounded up to a page), else its
section + offset; `same name + offset` says whether the two resolutions agree (same name and offset, same held symbol,
same string bytes, same bound name).
"""
import bisect
import collections
import csv
import hashlib
import os
import sys

from elftools.elf.elffile import ELFFile

MOVED = ('applied', 'propagated', 'hand')


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


class Twin:
    def __init__(self, path):
        e = ELFFile(open(path, 'rb'))
        self.loads = [(g['p_vaddr'], g['p_memsz'], g.data()) for g in e.iter_segments() if g['p_type'] == 'PT_LOAD']
        self.secs = [(s.name, s['sh_addr'], s['sh_size'], s['sh_flags']) for s in e.iter_sections() if s['sh_addr']]
        at = collections.defaultdict(set)
        for y in e.get_section_by_name('.symtab').iter_symbols():
            t = y['st_info']['type']
            if y.name and t in ('STT_FUNC', 'STT_OBJECT') and y['st_value'] and y['st_shndx'] != 'SHN_UNDEF':
                at[(y['st_value'], y['st_size'])].add(y.name)
        self.syms = sorted((v, z, sorted(ns)) for (v, z), ns in at.items())
        self.starts = [s[0] for s in self.syms]

    def read(self, a, n):
        return next((d[a - v:a - v + n] for v, z, d in self.loads if v <= a and a + n <= v + len(d)), None)

    def symbol(self, a):
        i = bisect.bisect_right(self.starts, a)
        inside = [(z, v, ns) for v, z, ns in self.syms[max(0, i - 400):i] if v <= a < v + z]
        if inside:
            z, v, ns = min(inside)
            return '%s+%#x' % ('/'.join(ns), a - v), [(n, a - v) for n in ns]
        ends = [(v, z, ns) for v, z, ns in self.syms[max(0, i - 400):i] if z and v + z == a]
        if ends:
            v, z, ns = ends[-1]
            return 'end of %s' % '/'.join(ns), [('end:' + n, 0) for n in ns]
        return None, []

    def bounds(self, a):
        out = []
        for k, (v, z, d) in enumerate(self.loads, 1):
            for what, b in (('start', v), ('end', v + z), ('end rounded to a page', -(-(v + z) // 0x1000) * 0x1000)):
                if a == b:
                    out.append('PT_LOAD %d %s' % (k, what))
        for n, v, z, f in self.secs:
            if a == v:
                out.append('start of %s' % n)
            if a == v + z:
                out.append('end of %s' % n)
        return out

    def resolve(self, a):
        r, k = self.symbol(a)
        if r:
            return r, k
        sec = next(((n, v, z, f) for n, v, z, f in self.secs if v <= a < v + z), None)
        if sec and sec[0] == '.got':
            slot = a - (a - sec[1]) % 8
            cell = self.read(slot, 8)
            held = int.from_bytes(cell, 'little') if cell else None
            hr, hk = self.symbol(held) if held else (None, [])
            return ('.got slot %#x + %d holds %s (%s)' % (slot, a - slot, hex(held) if held is not None else '?', hr),
                    [('got', n, o, a - slot) for n, o in hk])
        if sec and not sec[3] & 1:
            d = self.read(a, 256) or b''
            s = d[:d.find(b'\0') + 1] if b'\0' in d else b''
            if len(s) > 1 and all(32 <= ch < 127 or ch in (9, 10, 13) for ch in s[:-1]):
                return '(%s) C string %r' % (sec[0], s), [('str', s)]
        b = self.bounds(a)
        if b:
            return 'bound: %s' % ', '.join(b), [('bound', x) for x in b]
        if sec:
            return '(%s+%#x)' % (sec[0], a - sec[1]), [('sec', sec[0], a - sec[1])]
        return '(no section)', []


def num(x):
    return int(x, 16) if x.lower().startswith('0x') else int(x)


def main():
    if len(sys.argv) != 6:
        sys.exit(__doc__)
    table, fmt, fmp, tw, tp = sys.argv[1:]
    out = []
    for tag, twin, pin in (('fm', fmt, fmp), ('target', tw, tp)):
        lt = [(v, z, d) for v, z, d in Twin(twin).loads]
        lp = [(g['p_vaddr'], g['p_memsz'], g.data()) for g in ELFFile(open(pin, 'rb')).iter_segments()
              if g['p_type'] == 'PT_LOAD']
        same = len(lt) >= 4 and lt[1:4] == lp[1:4]
        if not same:
            sys.exit('twin_facts.py: %s twin and pin differ in PT_LOAD 2..4' % tag)
        out.append('# %s image: twin %s sha256 %s; pin %s sha256 %s; PT_LOAD 2..4 of twin and pin byte-equal: yes'
                   % (tag, os.path.basename(twin), sha(twin), os.path.basename(pin), sha(pin)))
    F, T = Twin(fmt), Twin(tw)
    pairs = collections.OrderedDict()
    for r in csv.DictReader(open(table), delimiter='\t'):
        if r['how'] in MOVED:
            k = (r['fm value'], r['disco value'])
            pairs.setdefault(k, [set(), set()])
            pairs[k][0].add(r['shipped file'])
            pairs[k][1].add(r['how'])
    out.append('fm value\tfm twin: symbol + offset\ttarget value\ttarget twin: symbol + offset\tsame name + offset\t'
               'shipped files\thow')
    for (fv, tv), (files, hows) in sorted(pairs.items(), key=lambda kv: (num(kv[0][0]), num(kv[0][1]))):
        fr, fk = F.resolve(num(fv))
        tr, tk = T.resolve(num(tv))
        out.append('\t'.join([fv, fr, tv, tr, 'yes' if set(fk) & set(tk) else 'no', str(len(files)),
                              ','.join(sorted(hows))]))
    sys.stdout.write('\n'.join(out) + '\n')


if __name__ == '__main__':
    main()
