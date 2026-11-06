#!/usr/bin/env python3
"""pac_namediff.py OLD_TSV NEW_TSV OUT_TSV -- the named-symbol rows of two port_addr_check runs on the same run directory
(the raw --out TSVs of gates/pac-A.sh), for the fail-open that the checker's owner reported for 205a90fd19b8 (08:31Z): a
cell whose NAME contains the symbol name at its value passes as SAME-SYMBOL. Kind: measurement; it proves no function.

Rows are joined on (src_file, src_line, dst_file, dst_line, sentence, idx, src_value, dst_value). Selected: rows OLD
calls DIFFERENT-SYMBOL or UNMEASURED-NAME and NEW calls SAME-SYMBOL. Each is read against the twins (env DST_TWIN,
SRC_TWIN: unstripped fuzz_transport.asan 86efc3a80314, fuzz_grant.asan 57c26f993615). The cell's stated name is
`<prefix>_(A|D|E)_<name>` (the Definition the row's sentence names). The symbols at the value: for A and D the symbols
that start at the value, else the sized function / object that holds it; for E the sized function / object that ends at
the value (start + size), the end of the walked region. The stated function is <name> itself, read literally: a symbol
named <name> up to leading underscores. It is the SAME function when such a symbol is at the value (starts there, or for
E ends there), else DIFFERENT; the column `stated function in the twin` gives where the twin has it (start..end), or
`none`. The donor side is read the same way at src_value in fuzz_grant's twin, and the last column says whether the
donor's value and the port's value carry the same symbol names (the relocation kept the object). OUT_TSV gets every
selected row; stdout the counts."""
import hashlib
import os
import re
import sys

from elftools.elf.elffile import ELFFile

KEY = ('src_file', 'src_line', 'dst_file', 'dst_line', 'sentence', 'idx', 'src_value', 'dst_value')


def load(path):
    rows, hdr = {}, None
    for ln in open(path, errors='replace'):
        if ln.startswith('#') or not ln.strip():
            continue
        f = ln.rstrip('\n').split('\t')
        if hdr is None:
            hdr = f
            continue
        r = dict(zip(hdr, f))
        rows.setdefault(tuple(r.get(k, '') for k in KEY), []).append(r)
    return rows


class Syms:
    def __init__(self, path, want):
        h = hashlib.sha256(open(path, 'rb').read()).hexdigest()[:12]
        if h != want:
            sys.exit(f'pac_namediff: {path} is {h}, not {want}')
        e = ELFFile(open(path, 'rb'))
        self.s = [(x.name, x['st_value'], x['st_size'], x['st_info']['type'])
                  for x in e.get_section_by_name('.symtab').iter_symbols()
                  if x.name and not x.name.startswith('$') and x['st_shndx'] != 'SHN_UNDEF'
                  and x['st_info']['type'] not in ('STT_FILE', 'STT_SECTION')]

    def at(self, v, kind):
        if kind == 'E':
            return sorted({n for n, a, sz, t in self.s if sz and a + sz == v and t in ('STT_FUNC', 'STT_OBJECT')})
        start = sorted({n for n, a, sz, t in self.s if a == v})
        if start:
            return start
        return sorted({f'{n}+{v - a:#x}' for n, a, sz, t in self.s if sz and a <= v < a + sz and t in ('STT_FUNC', 'STT_OBJECT')})

    def named(self, stated):
        return sorted({(n, a, a + sz) for n, a, sz, t in self.s if n.lstrip('_') == stated.lstrip('_') and t in ('STT_FUNC', 'STT_OBJECT')})


def main():
    old, new, out = sys.argv[1:4]
    a, b = load(old), load(new)
    D = Syms(os.environ['DST_TWIN'], '86efc3a80314')
    G = Syms(os.environ['SRC_TWIN'], '57c26f993615')
    sel = []
    for k, rs in b.items():
        if not any(r['verdict'] == 'SAME-SYMBOL' for r in rs):
            continue
        olds = {r['verdict'] for r in a.get(k, [])}
        if olds & {'DIFFERENT-SYMBOL', 'UNMEASURED-NAME'}:
            sel.append((k, sorted(olds & {'DIFFERENT-SYMBOL', 'UNMEASURED-NAME'})[0]))
    lines = ['file:line (src -> dst)\tcell\tkind\tvalue (dst)\told verdict (0d24592683b6)\tsymbols at the dst value\t'
             'stated function in the twin\tstated function at the value\tdonor value\tsymbols at the donor value\t'
             'donor and port values carry the same symbols']
    diff = 0
    for k, ov in sorted(sel, key=lambda x: (x[0][2], int(x[0][3] or 0), x[0][4])):
        m = re.search(r'\b(\w+?)_(A|D|E)_(\w+)', k[4])
        cell, kind, stated = (m.group(0), m.group(2), m.group(3)) if m else (k[4], '?', '?')
        dv, sv = int(k[7], 0), int(k[6], 0) if k[6] else None
        ds, gs = D.at(dv, kind), (G.at(sv, kind) if sv is not None else [])
        nm = D.named(stated)
        here = any((e if kind == 'E' else s) == dv for _, s, e in nm)
        st = 'SAME' if here else 'DIFFERENT'
        diff += not here
        where = ' '.join(f'{n} [{s:#x}, {e:#x})' for n, s, e in nm) or 'none'
        keep = 'yes' if ds and ds == gs else 'no'
        lines.append('\t'.join((f'{k[0]}:{k[1]} -> {k[3]}', cell, kind, k[7], ov, ' '.join(ds) or '-', where, st,
                                k[6] or '-', ' '.join(gs) or '-', keep)))
    open(out, 'w').write('\n'.join(lines) + '\n')
    print(f'rows 0d24592683b6 calls DIFFERENT-SYMBOL or UNMEASURED-NAME and 205a90fd19b8 calls SAME-SYMBOL: {len(sel)}; '
          f'stated function DIFFERENT from the one at the value: {diff}; SAME: {len(sel) - diff}; donor and port values '
          f'carry the same symbols: {sum(l.endswith(chr(9) + "yes") for l in lines[1:])} of {len(sel)}')


main()
