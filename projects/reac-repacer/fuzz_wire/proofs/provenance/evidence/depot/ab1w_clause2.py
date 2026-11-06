#!/usr/bin/env python3
"""ab1w_clause2.py AB1w.v TWIN [LIB_ROOT] -- clause 2 of the AB1w DIFFERENT-SYMBOL rule (the publication owner's ruling, 20:58Z): a named cell
`tfib_A_<X>` / `tfib_E_<X>` is TRUE by name iff its value is the START (A) / END = start + size (E) of the symbol <X>
names, in the twin's OWN symtab. The name <X> is matched to twin symbols by a key: the demangled name with a leading
`__asan::` / `__sanitizer::` / `__lsan::` / `__ubsan::` namespace dropped, `::` -> `_`, argument list dropped, and a
plain C symbol's leading underscores dropped; a trailing `_<digits>` disambiguator in the cell name is tried both kept
and dropped. For each cell prints: name, value, the named symbol(s) and their start / end, verdict TRUE / FALSE-BY-NAME /
NO-SYMBOL, and (FALSE / NO-SYMBOL) the symbol that actually starts / ends at the value and the reader count (word grep
of the cell name over LIB_ROOT, its own definition excluded)."""
import bisect, os, re, subprocess, sys
from elftools.elf.elffile import ELFFile

ab1w, twin = sys.argv[1:3]
root = sys.argv[3] if len(sys.argv) > 3 else None
NS = re.compile(r'^(?:__asan|__sanitizer|__lsan|__ubsan|__interception)::')


NSN = ('__asan', '__sanitizer', '__lsan', '__ubsan', '__interception')


def comps(m):
    """the name components of an Itanium mangled symbol (_ZN<len>id...E or _Z<len>id); None if not mangled"""
    if not m.startswith('_Z'):
        return None
    i = 2
    nested = m[i:i + 1] == 'N'
    if nested:
        i += 1
        while i < len(m) and m[i] in 'rVKRO':
            i += 1
    out = []
    while i < len(m) and m[i].isdigit():
        j = i
        while j < len(m) and m[j].isdigit():
            j += 1
        n = int(m[i:j])
        out.append(m[j:j + n])
        i = j + n
        if not nested or (i < len(m) and m[i] == 'I'):
            break
    return out or None


def key(mangled):
    c = comps(mangled)
    if c is None:
        return mangled.lstrip('_')
    while c and c[0] in NSN:
        c = c[1:]
    return '_'.join(c)


e = ELFFile(open(twin, 'rb'))
syms = [(s.name, s['st_value'], s['st_size']) for s in e.get_section_by_name('.symtab').iter_symbols()
        if s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT') and s['st_value'] and s.name]
bykey = {}
for n, v, sz in syms:
    bykey.setdefault(key(n), []).append((n, n, v, sz))
starts = {}
ends = {}
for n, v, sz in syms:
    starts.setdefault(v, []).append(n)
    ends.setdefault(v + sz, []).append(n)

text = open(ab1w).read()
cells = re.findall(r'Definition (tfib_([AE])_(\w+?))\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+|\d+)\s*\.', text)


def readers(name):
    if not root:
        return '-'
    p = subprocess.run(['git', 'grep', '-n', '-w', name, '--', '.'], cwd=root, capture_output=True, text=True)
    lines = [l for l in p.stdout.splitlines() if not re.search(r'Definition %s\b' % re.escape(name), l)]
    return len(lines)


print('cell\tvalue\tside\tnamed symbol(s) [start,end)\tverdict\tactual symbol at value\treaders')
for full, side, x, val in cells:
    v = int(val, 0)
    cands = bykey.get(x) or bykey.get(re.sub(r'_\d+$', '', x)) or []
    named = ' '.join('%s[%#x,%#x)' % (d.split('(')[0], s, s + sz) for _, d, s, sz in cands) or '-'
    if not cands:
        verdict = 'NO-SYMBOL'
    elif any((s == v) if side == 'A' else (s + sz == v) for _, _, s, sz in cands):
        verdict = 'TRUE'
    else:
        verdict = 'FALSE-BY-NAME'
    actual = '-'
    if verdict != 'TRUE':
        hit = (starts if side == 'A' else ends).get(v, [])
        actual = ' '.join(hit[:3]) or 'none'
    rd = readers(full) if verdict != 'TRUE' else '-'
    print('%s\t%#x\t%s\t%s\t%s\t%s\t%s' % (full, v, side, named, verdict, actual, rd))
