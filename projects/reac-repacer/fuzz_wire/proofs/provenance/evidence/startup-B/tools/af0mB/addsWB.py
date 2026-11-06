#!/usr/bin/env python3
"""addsWB.py -- fuzz_wire image B's af0m --add cells, mapped BY NAME from fuzz_decode B's list of record
(adds.AtoB.tsv, sha256 2d6852fa7e15, not in the published tree, read from $LT/decB-ref/: image A's 34 --add cells keyed and moved to decode B;
the 6 shadow rows and the 2 musl __atexit rows are not passed). decode's base and this base are
both cgif-derived (port_core cgif -> unit + relocownB), so decode's list is the twin list. Keys are resolved on fuzz_wire
B's own twin .symtab / image, never by address: SYMBOL -> the same symbol + offset; POINTER -> the unique .got slot whose
image word is fuzz_uci's &target. Rows with no fuzz_wire counterpart are dropped, each with its reason (the fuzz_uci lanes'
reasons): the REAC_MODE_* .got slots (decode's own program globals; fuzz_wire defines no REAC_MODE_* symbol, checked
below), the SECTION .rodata+0x58 constant (read only by decode's program code; its bytes' occurrences in fuzz_wire's
.rodata are counted below). A mapped cell whose exact (address, width)
row the base already carries is reported, not passed (only the cells the base lacks are passed).

  addsB.py BASE.v            prints the table and, last line, the --add arguments
"""
import re, struct, sys
from elftools.elf.elffile import ELFFile

import os
TWIN = os.environ['UBs']
PIN = os.environ['UB']
TSV = os.environ['LT'] + '/decB-ref/adds.AtoB.tsv'
DEC = os.environ['LR'] + '/bin/fuzz_decode/fuzz_decode.asan-ubsan'

e = ELFFile(open(TWIN, 'rb'))
sym = {}
for s in e.get_section_by_name('.symtab').iter_symbols():
    if s.name and s['st_value']:
        sym.setdefault(s.name, s['st_value'])
secs = {s.name: (s['sh_addr'], s['sh_size']) for s in e.iter_sections() if s['sh_addr']}
pe = ELFFile(open(PIN, 'rb'))
loads = [(g['p_vaddr'], g.data(), g['p_memsz']) for g in pe.iter_segments() if g['p_type'] == 'PT_LOAD']


def word(a):
    for va, d, ms in loads:
        if va <= a and a + 8 <= va + len(d):
            return struct.unpack_from('<Q', d, a - va)[0]
    return None


def base_rows(path):
    t = open(path).read()
    i = t.index('Definition Tfib_const_abs'); j = t.index('].', i)
    return {(int(m.group(2), 16), int(m.group(1))) for m in re.finditer(r'z(\d) \(ANum (0x[0-9a-f]+)\)', t[i:j])}


def main():
    rows = base_rows(sys.argv[1])
    out, adds = [], []
    gl, gs = secs['.got']
    for l in open(TSV):
        if l.startswith('#') or l.startswith('A cell'):
            continue
        acell, w, kind, key, bcell, passed = l.rstrip('\n').split('\t')
        w = int(w)
        if not passed.startswith('yes'):
            out.append((key, 'not passed by decode B (%s)' % passed[:40], None)); continue
        if key.startswith('slot+') or key.startswith('head+'):
            out.append((key, 'DROP: musl __atexit cell, withdrawn (GATES-decB Part 5)', None)); continue
        if 'REAC_MODE' in key:
            out.append((key, 'DROP: decode program global; fuzz_wire has no REAC_MODE_* symbol: %s' %
                        [n for n in sym if 'REAC_MODE' in n], None)); continue
        if kind == 'SECTION':
            ro = secs['.rodata']
            de = ELFFile(open(DEC, 'rb')); dl = [(g['p_vaddr'], g.data()) for g in de.iter_segments() if g['p_type'] == 'PT_LOAD']
            a0 = int(bcell.split('/')[0], 16)
            db = next(d[a0 - va:a0 - va + 8] for va, d in dl if va <= a0 < va + len(d))
            ub = b''.join(next(d[ro[0] - va:ro[0] + ro[1] - va] for va, d, _ in loads if va <= ro[0] < va + len(d)) for _ in [0])
            off = int(re.match(r'\.rodata\+(0x[0-9a-f]+)$', key).group(1), 16)
            here = next(d[ro[0] + off - va:ro[0] + off - va + 8] for va, d, _ in loads if va <= ro[0] + off < va + len(d))
            if here == db and ub.count(db) == 1:
                # fuzz_wire: the same 8 bytes sit at the same .rodata offset, once (its own program code reads them:
                # rp_frame_channels' divide-by-36 constant), so the twin of decode's SECTION row is this cell
                a = ro[0] + off
            else:
                out.append((key, 'DROP: decode .rodata constant %s (read only by decode program code); occurrences in '
                            'fuzz_wire .rodata: %d' % (db.hex(), ub.count(db)), None)); continue
        elif kind == 'SYMBOL':
            n, off = re.match(r'(.+)\+(0x[0-9a-f]+)$', key).groups()
            if n not in sym:
                out.append((key, 'NO such symbol in fuzz_wire B', None)); continue
            a = sym[n] + int(off, 16)
        elif kind == 'POINTER':
            n, off = re.match(r'\.got slot holding &(.+)\+(0x[0-9a-f]+)$', key).groups()
            tgt = sym[n] + int(off, 16)
            hits = [q for q in range(gl, gl + gs, 8) if word(q) == tgt]
            if len(hits) != 1:
                out.append((key, 'POINTER: %d .got slots hold %#x' % (len(hits), tgt), None)); continue
            a = hits[0]
        else:
            out.append((key, 'unknown kind %s' % kind, None)); continue
        have = (a, w) in rows
        out.append((key, 'base row already' if have else 'ADD', '%#x/%d' % (a, w)))
        if not have:
            adds.append('%#x/%d' % (a, w))
    for k, why, c in out:
        print('%-70s %-12s %s' % (k[:70], c or '-', why))
    print('ADD ' + ' '.join('--add ' + x for x in adds))


main()
