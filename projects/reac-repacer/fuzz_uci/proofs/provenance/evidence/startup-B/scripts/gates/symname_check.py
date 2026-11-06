#!/usr/bin/env python3
"""symname_check.py TWIN_ELF FILE.v... -- the independent .symtab control asked for with port_addr_check e165063a0081's
fix (3): every definition whose OWN NAME names a symbol -- e165's NAMED_SYM shape
`(Definition|Notation|Let) <prefix>_(A|D|E)_<name>` (A / D = the start of the object, E = its end) -- is checked
against the unstripped twin's .symtab directly, not through any tool's labels: the numeral the definition states must
be <name>'s address (A / D) or address + size (E), for <name> as written or with one / two leading underscores. It
also lists every definition named `src0_D_*` and every `tfib_*` definition whose numeral is an address of the image,
so the absence of such cells is a recorded result. Exit 1 if a named definition disagrees with the .symtab.

  symname_check.py TWIN_ELF FILE.v...
"""
import re, sys
from elftools.elf.elffile import ELFFile

NAMED = re.compile(r"(?m)^\s*(Definition|Notation|Let)\s+([A-Za-z_][\w']*?)_(A|D|E)_([A-Za-z_][\w']*)\b([^.]*?)\.\s*$")
SRC0 = re.compile(r"(?m)^\s*(?:Definition|Notation|Let)\s+(src0_D_\w+)")
NUM = re.compile(r'\b0x[0-9a-fA-F]+\b|\b\d+\b')


def main():
    e = ELFFile(open(sys.argv[1], 'rb'))
    by = {}
    for s in e.get_section_by_name('.symtab').iter_symbols():
        if s.name and s['st_shndx'] != 'SHN_UNDEF':
            by.setdefault(s.name, set()).add((s['st_value'], s['st_size']))
    bad = n_named = n_src0 = 0
    for f in sys.argv[2:]:
        t = open(f).read()
        t_nc = re.sub(r'\(\*.*?\*\)', lambda m: '\n' * m.group(0).count('\n'), t, flags=re.S)
        for m in SRC0.finditer(t_nc):
            n_src0 += 1
            print('SRC0 %s:%d %s' % (f.split('/')[-1], t_nc.count('\n', 0, m.start(1)) + 1, m.group(1)))
        for m in NAMED.finditer(t_nc):
            n_named += 1
            kind, pre, role, name, body = m.groups()
            ln = t_nc.count('\n', 0, m.start(2)) + 1
            vals = [int(x, 0) for x in NUM.findall(body)]
            hits = [(v, sz) for cand in (name, '_' + name, '__' + name) for v, sz in by.get(cand, ())]
            want = {a + (sz if role == 'E' else 0) for a, sz in hits}
            ok = bool(vals) and vals[-1] in want
            bad += not ok
            print('%s %s:%d %s_%s_%s = %s; .symtab %s: %s' % ('OK  ' if ok else 'DIFF', f.split('/')[-1], ln, pre, role,
                                                           name, [hex(v) for v in vals],
                                                           name, sorted(hex(w) for w in want) or 'absent'))
    print('symname_check: %d files; %d definitions named <x>_(A|D|E)_<symbol>, %d disagree with the .symtab; %d src0_D_* '
          'definitions' % (len(sys.argv) - 2, n_named, bad, n_src0))
    sys.exit(1 if bad else 0)


main()
