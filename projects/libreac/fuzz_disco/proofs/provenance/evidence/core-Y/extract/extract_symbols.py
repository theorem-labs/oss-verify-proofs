#!/usr/bin/env python3
"""Text extract of the symbol facts of an unstripped twin, for scripts that must not read a binary.

Usage: extract_symbols.py --twin TWIN --pin PIN --out SYMBOLS.tsv

Writes SYMBOLS.tsv: a header of '#' lines, then one row per .symtab entry:
    name <TAB> value(hex) <TAB> size <TAB> type <TAB> bind <TAB> section_name
in .symtab order (index order), so a reader that took "the first symbol of this name" from the ELF takes the same row.
The header names the sha256 of TWIN and of PIN, and states, for each PT_LOAD of PIN (counted from 1), whether its
file bytes equal the twin's PT_LOAD at the same index (PIN is the pinned image; TWIN is the same build with its symbol
table). The script exits 1 unless PT_LOAD 2..4 are equal, so an extract can only be written for a matching twin.
Needs pyelftools.
"""
import argparse, hashlib, sys
from elftools.elf.elffile import ELFFile

def sha256(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()

def loads(elf, raw):
    out = []
    for seg in elf.iter_segments():
        if seg['p_type'] == 'PT_LOAD':
            out.append((seg['p_vaddr'], seg['p_filesz'], raw[seg['p_offset']:seg['p_offset'] + seg['p_filesz']]))
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--twin', required=True); ap.add_argument('--pin', required=True); ap.add_argument('--out', required=True)
    a = ap.parse_args()
    tw_raw = open(a.twin, 'rb').read(); pn_raw = open(a.pin, 'rb').read()
    tw = ELFFile(open(a.twin, 'rb')); pn = ELFFile(open(a.pin, 'rb'))
    lt, lp = loads(tw, tw_raw), loads(pn, pn_raw)
    eq = []
    for i, (va, sz, b) in enumerate(lp, 1):
        same = i <= len(lt) and lt[i - 1][0] == va and lt[i - 1][2] == b
        eq.append((i, va, sz, same))
    if not all(s for i, _, _, s in eq if 2 <= i <= 4):
        sys.exit('PT_LOAD 2..4 of twin and pin differ: not the same build')
    st = tw.get_section_by_name('.symtab')
    if st is None:
        sys.exit('twin has no .symtab')
    rows = []
    for s in st.iter_symbols():
        shndx = s['st_shndx']
        sec = tw.get_section(shndx).name if isinstance(shndx, int) and 0 < shndx < tw.num_sections() else str(shndx)
        rows.append((s.name, '0x%x' % s['st_value'], str(s['st_size']), s['st_info']['type'], s['st_info']['bind'], sec))
    with open(a.out, 'w') as f:
        f.write('# symbol facts of an unstripped twin (text extract; the binaries are not shipped)\n')
        f.write('# twin sha256 %s\n' % sha256(a.twin))
        f.write('# pin  sha256 %s\n' % sha256(a.pin))
        for i, va, sz, same in eq:
            f.write('# PT_LOAD %d vaddr 0x%x filesz %d: %s\n' % (i, va, sz, 'equal' if same else 'differs'))
        f.write('# columns: name, value, size, type, bind, section\n')
        for r in rows:
            f.write('\t'.join(r) + '\n')
    print('%d symbols' % len(rows))

if __name__ == '__main__':
    main()
