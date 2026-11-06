#!/usr/bin/env python3
"""Measure every row whose verdict changed between port_addr_check 0d24592683b6 and 205a90fd19b8 on one gate.

Usage: triage_205a.py GATE CHANGED.tsv FULL_205A.tsv OURS_LIB DONOR_LIB IMGDIR OUT.tsv SDCP_OUT.tsv FLAG_CLASSES.txt
  GATE       RA (image A core, lib/A) or RB (image B core, lib/B)
  CHANGED    rerun-0d24's diff_rows.py changed.tsv for that gate (old = 0d24, new = 205a)
  FULL_205A  the 205a run's full.tsv (its STALE-DONOR-CODE-POINTER rows are read too, changed or not)
  OURS_LIB   extract of our lib/ (A/, B/, ...); DONOR_LIB the donor's lib/ extract
  IMGDIR     the image copies (cmd.K.pin / .twin, cgif.K.pin / .twin)

Each row is measured by its group; the group is read from the row (old and new verdict, file, sentence), never
assumed. A row of no group is written with triage OPEN and makes the exit status 1.
  geom      SAME-GEOMETRY -> NON-ADDRESS-CHANGED: the quantity the tool names (dst_res `hq:<q>`) computed from
            the PT_LOAD table of our pin (segN.size = page-rounded extent of the N-th PT_LOAD; image.span = top of
            the last page-rounded PT_LOAD minus the first one's base), and the donor's value from the donor pin.
  table     a cell of the generated function table (AB1w.v / YB1w.v) whose verdict became SAME-SYMBOL: the sized FUNC
            symbols of our twin that start (tfib_A_*) or end (tfib_E_*) at our value, those of the donor twin at
            the donor's value, how the label relates to that symbol name, which FUNC of our twin carries the
            label's own name, and the files of lib/ outside the two table files that name the cell.
  bound     a numeral inside `assert (Hrange ... <= N)` over the entries of icpt_rodata: the largest start + length
            of icpt_rodata in our AE2y.v / YE2y.v against N, the A twin's / donor's N, and the proof's end.
  maplen    the literal 262144 as a register value of a symbolic state: the containing function of each pin pc in
            our image and the rounding constants it loads (lui 0x40 = 0x40000, lui 0xfffc0 = its mask), and the
            register equation x11 = 262144 with x12 = PROT, as rerun-0d24's triage_changed.py measures it.
  no flag   the new verdict is not a finding class and the value is unchanged (src = dst): listed, value checked.
The SDCP_OUT file holds every STALE-DONOR-CODE-POINTER row of the 205a run (changed or not), read the same way:
pin rows by maplen, table rows by the twin FUNC at the value against the label, REAL-slot rows by the 8 pin bytes
at the cell address.
"""
import collections
import os
import re
import sys
from elftools.elf.elffile import ELFFile

gate, changed_p, full_p, lib, dlib, imgdir, out_p, sdcp_p, fc_p = sys.argv[1:10]
side = {'RA': 'A', 'RB': 'B'}[gate]
TABLES = ('AB1w.v', 'YB1w.v')
FLAGS = {l.strip() for l in open(fc_p) if l.strip()}
PAGE = 0x1000


def pdown(v):
    return v & ~(PAGE - 1)


def pup(v):
    return (v + PAGE - 1) & ~(PAGE - 1)


def sx(v, b):
    return v - (1 << b) if v & (1 << (b - 1)) else v


class Img:
    def __init__(self, pin, twin):
        with open(pin, 'rb') as f:
            e = ELFFile(f)
            self.loads = [(s['p_vaddr'], s['p_memsz'], s.data() + b'\0' * (s['p_memsz'] - s['p_filesz']))
                          for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
            self.relro = [s['p_vaddr'] for s in e.iter_segments() if s['p_type'] == 'PT_GNU_RELRO']
        with open(twin, 'rb') as f:
            self.funcs = [(s['st_value'], s['st_size'], s.name)
                          for s in ELFFile(f).get_section_by_name('.symtab').iter_symbols()
                          if s['st_info']['type'] == 'STT_FUNC' and s['st_size'] > 0]
        self.by_start = collections.defaultdict(set)
        self.by_end = collections.defaultdict(set)
        self.by_name = collections.defaultdict(list)
        for a, n, name in self.funcs:
            self.by_start[a].add(name)
            self.by_end[a + n].add(name)
            self.by_name[name].append(a)

    def geom(self):
        g = {}
        for i, (a, n, _) in enumerate(self.loads):
            g[f'seg{i}.lo'], g[f'seg{i}.hi'] = pdown(a), pup(a + n)
            g[f'seg{i}.size'] = g[f'seg{i}.hi'] - g[f'seg{i}.lo']
        g['image.lo'] = min(pdown(a) for a, _, _ in self.loads)
        g['image.top'] = max(pup(a + n) for a, n, _ in self.loads)
        g['image.span'] = g['image.top'] - g['image.lo']
        if self.relro:
            g['relro.lo.page'] = pdown(self.relro[0])
        return g

    def read(self, a, n):
        for b, m, d in self.loads:
            if b <= a and a + n <= b + m:
                return d[a - b:a - b + n]
        return None

    def luis(self, pc):
        s, n, name = min([t for t in self.funcs if t[0] <= pc < t[0] + t[1]], key=lambda t: t[1])
        out, a = [], s
        while a < s + n:
            h = int.from_bytes(self.read(a, 2), 'little')
            if h & 3 != 3:
                if h & 3 == 1 and h >> 13 == 3 and ((h >> 7) & 31) not in (0, 2):
                    v = sx(((h >> 12) & 1) << 5 | ((h >> 2) & 31), 6)
                    out.append((a, (h >> 7) & 31, sx((v << 12) & 0xffffffff, 32) & (2 ** 64 - 1)))
                a += 2
                continue
            w = int.from_bytes(self.read(a, 4), 'little')
            if w & 0x7f == 0x37:
                out.append((a, (w >> 7) & 31, sx(w & 0xfffff000, 32) & (2 ** 64 - 1)))
            a += 4
        return name, s, out


ours = Img(os.path.join(imgdir, f'cmd.{side}.pin'), os.path.join(imgdir, f'cmd.{side}.twin'))
donor = Img(os.path.join(imgdir, f'cgif.{side}.pin'), os.path.join(imgdir, f'cgif.{side}.twin'))
G_OURS, G_DONOR = ours.geom(), donor.geom()


def dem(names):
    """The symbol names as the twin's .symtab spells them (mangled where C++; no demangler is used). A label
    is matched against the mangled name, which carries each identifier's text unchanged."""
    return list(names)


def lines_of(path):
    return open(path, encoding='utf-8', errors='replace').read().split('\n')


# readers: identifier -> files outside the two table files that name it
readers = collections.defaultdict(set)
for dp, _, fs in os.walk(lib):
    for f in fs:
        if f.endswith('.v') and f not in TABLES:
            p = os.path.join(dp, f)
            for m in set(re.findall(r'\btfib_[A-Za-z0-9_]+\b', open(p, encoding='utf-8', errors='replace').read())):
                readers[m].add(os.path.relpath(p, lib))

# icpt_rodata: largest start + length in our file of this image
y2 = open(os.path.join(lib, side, 'AE2y.v' if side == 'A' else 'YE2y.v'), encoding='utf-8').read()
i = y2.index('Definition icpt_rodata ')
body = y2[y2.index(':=', i) + 2:y2.index('].', i)]
ents = re.findall(r'^\s*\[?\s*\(\s*(0x[0-9a-fA-F]+|\d+)\s*,\s*(\d+)\s*,\s*\[', body, re.M)
icpt_max = max(int(a, 0) + int(b) for a, b in ents)


def label_relation(label, names):
    """How a table label relates to the symbol names its value starts / ends."""
    rel = []
    for n, d in zip(names, dem(names)):
        if n == '__interceptor_trampoline_' + label:
            rel.append(f'{n} is the interceptor trampoline of libc `{label}` (the table\'s tfib_A_<f> / tfib_E_<f> '
                       f'convention: the 4-byte trampoline the program calls; musl\'s body is a separate tfib_*_musl_<f> '
                       f'row)')
        elif label.endswith('_globals') and n.replace('_elf_globals', '_globals').lstrip('_') == label:
            rel.append(f'{n} is `{label}` with the `_elf_` infix: the label names the ELF-globals entry point, as the '
                       f'donor\'s row of the same name does')
        elif label in d or label in n:
            rel.append(f'{d} contains the label')
        else:
            rel.append(f'{d} does not contain the label')
    return '; '.join(rel) or 'no FUNC symbol'


def own_name_funcs(label):
    """FUNCs of our twin whose name IS the label's own spelling (label, _label, __label, __asan_label), with their
    start: the 'other function' a reader could take the label to mean."""
    out = []
    for n in (label, '_' + label, '__' + label):
        for a in ours.by_name.get(n, []):
            out.append(f'{n}@{a:#x}')
    return out


def maplen(text):
    pins = re.findall(r'pin \(runto (0x[0-9a-fA-F]+) [A-Za-z0-9_]+\) (\d+)%bv \(SLit 262144\)', text)
    regeq = re.search(r'11%bv = SLit 262144', text) and re.search(r'12%bv = SLit (\d+)\b', text)
    meas = []
    for pc_s, reg in pins:
        name, s, ls = ours.luis(int(pc_s, 16))
        g = [f'lui x{rd} {v:#x} at {a:#x}' for a, rd, v in ls if v in (0x40000, 0xfffffffffffc0000)]
        meas.append(f'x{reg} pinned at pc {pc_s} in {dem([name])[0]} (at {s:#x}), which loads '
                    f'{", ".join(g) or "no 0x40000 rounding constant"}')
    if regeq:
        prot = int(regeq.group(1))
        pn = {0: 'PROT_NONE', 3: 'PROT_READ | PROT_WRITE'}.get(prot, 'prot ?')
        meas.append(f'register equation: x11 = 262144 with x12 = {prot} ({pn}): the length argument of the map call')
    ok = bool(meas) and all('no 0x40000' not in m for m in meas)
    return ok, ('a map length, not a code pointer: ' + '; '.join(meas)) if meas else 'role not read from the line'


def table_cell(r, ix, val):
    sent = r[ix['sentence']]
    name = sent.split()[1]
    kind = 'A' if name.startswith('tfib_A_') else 'E'
    label = name[len('tfib_A_'):]
    sv = int(r[ix['src_value']], 0)
    if kind == 'A':
        o, d = sorted(ours.by_start.get(val, ())), sorted(donor.by_start.get(sv, ()))
    else:
        o, d = sorted(ours.by_end.get(val, ())), sorted(donor.by_end.get(sv, ()))
    same = bool(set(o) & set(d))
    nread = len(readers.get(name, ()))
    what = 'starts' if kind == 'A' else 'ends'
    other = own_name_funcs(label)
    ok = same and nread == 0
    why = (f'{name}: our value {val:#x} {what} FUNC {", ".join(dem(o)) or "(none)"} in our twin; the donor value {sv:#x} '
           f'{what} FUNC {", ".join(dem(d)) or "(none)"} in the donor twin ({"the same function" if same else "NOT the same function"}); '
           f'label relation: {label_relation(label, o)}; FUNCs of our twin spelled as the label itself: '
           f'{", ".join(other) or "none"}; named by {nread} files of lib/ outside the two table files')
    return ok, why


def bound(f, ln, val):
    L = lines_of(os.path.join(lib, side, f))
    text = L[ln - 1]
    b = int(re.search(r'<=\s*(0x[0-9a-fA-F]+|\d+)\s*\)', text).group(1), 0)
    end = next(k for k in range(ln, len(L)) if re.search(r'\b(Qed|Admitted|Abort|Defined)\.', L[k]))
    endw = re.search(r'\b(Qed|Admitted|Abort|Defined)\.', L[end]).group(1)
    return b, icpt_max, endw, end + 1


def twin_bound(f, ln):
    """The bound the A twin states at the same assert (file name A<->Y, line - 1)."""
    tf = ('A' + f[1:]) if side == 'B' else None
    if not tf:
        return None
    L = lines_of(os.path.join(lib, 'A', tf))
    for k in (ln - 2, ln - 1, ln):
        if 0 <= k < len(L) and 'Hrange' in L[k]:
            return tf, k + 1, int(re.search(r'<=\s*(0x[0-9a-fA-F]+|\d+)\s*\)', L[k]).group(1), 0)
    return None


rows = [l.rstrip('\n').split('\t') for l in open(changed_p, encoding='utf-8')]
hdr, rows = rows[0], rows[1:]
ix = {c: k for k, c in enumerate(hdr)}
out = []
opened = 0
for r in rows:
    ov, nv, f, ln = r[ix['old_verdict']], r[ix['new_verdict']], r[ix['dst_file']], int(r[ix['dst_line']])
    sent, val, sv = r[ix['sentence']], int(r[ix['dst_value']], 0), int(r[ix['src_value']], 0)
    note = r[ix['note']]
    exp = re.search(r'expected (0x[0-9a-f]+)', note)
    exp = exp.group(1) if exp else '-'
    where = f'lib/{side}/{f}:{ln}'
    text = lines_of(os.path.join(lib, side, f))[ln - 1]
    if ov == 'SAME-GEOMETRY' and nv == 'NON-ADDRESS-CHANGED':
        qs = re.findall(r'hq:([\w.]+)', r[ix['dst_res']])
        qd = re.findall(r'hq:([\w.]+)', r[ix['src_res']])
        mo = [(q, G_OURS.get(q)) for q in qs]
        md = [(q, G_DONOR.get(q)) for q in qd]
        ok = any(v == val for _, v in mo) and any(v == sv for _, v in md)
        tri = 'OK' if ok else 'OPEN'
        why = (f'an image quantity of our own pin, not a moved size: our value {val:#x} = '
               + ', '.join(f'{q} {v:#x}' for q, v in mo if v is not None)
               + f' of cmd.{side}.pin (PT_LOAD page-rounded); the donor value {sv:#x} = '
               + ', '.join(f'{q} {v:#x}' for q, v in md if v is not None) + f' of cgif.{side}.pin')
        lm = re.search(r'rewrite (tfib_len\d)', lines_of(os.path.join(lib, side, f))[ln - 2])
        if lm:
            lt = next((l for l in lines_of(os.path.join(lib, side, f)) if l.startswith(f'Lemma {lm.group(1)} ')), '')
            m = re.search(r'= (\d+)%N', lt)
            if m:
                why += (f'; the line bounds the byte list whose length {lm.group(1)} states as {m.group(1)} '
                        f'({int(m.group(1)):#x}) by vm_compute')
                ok = ok and int(m.group(1)) == val
                tri = 'OK' if ok else 'OPEN'
    elif f in TABLES and sent.startswith('Definition tfib_') and nv == 'SAME-SYMBOL':
        ok, why = table_cell(r, ix, val)
        tri = 'OK' if ok else 'OPEN'
    elif 'Hrange' in text and nv in ('NON-ADDRESS-SAME', 'NON-ADDRESS-CHANGED'):
        b, imax, endw, endl = bound(f, ln, val)
        tb = twin_bound(f, ln)
        why = (f'the bound of `assert (Hrange : 0 <= start /\\ start + length <= {b:#x})` over every entry of '
               f'icpt_rodata; the largest start + length in our {"AE2y.v" if side == "A" else "YE2y.v"} is {imax:#x}; '
               f'the proof ends {endw} at line {endl}; the donor states {sv:#x}'
               + (f'; the A twin lib/A/{tb[0]}:{tb[1]} states {tb[2]:#x}' if tb else ''))
        if val == sv and imax <= b and endw == 'Qed':
            tri = 'OK'
        elif val != sv and tb and tb[2] == sv:
            tri = 'FINDING (recorded)'
            why += (f'. A WRONG VALUE IN OUR TREE: {val:#x} is the 2 MiB bound {sv:#x} moved by the image-B relay '
                    f'as an address (delta {val - sv:#x}); the right value is {sv:#x}. Recorded before this run: '
                    f'core-recheck/code-values.tsv row lib/B/YE6k.v 1388 0x1ffb80 -> 0x200000 (fixed on the series '
                    f'head). Both bounds hold the icpt_rodata entries, so the proof closes either way')
        else:
            tri = 'OPEN'
    elif val == 262144 and ov == 'STALE-DONOR-CODE-POINTER':
        ok, why = maplen(text)
        ok = ok and val == sv
        tri = 'OK' if ok else 'OPEN'
    elif nv not in FLAGS and val == sv:
        tri, why = 'no flag', f'the new verdict {nv} is not a finding class; the value is unchanged ({val:#x} on both sides)'
    else:
        tri, why = 'OPEN', 'no group'
    opened += tri == 'OPEN'
    out.append([gate, where, sent, ov, nv, r[ix['dst_value']], exp, tri, why, note])

with open(out_p, 'w') as fh:
    fh.write('\t'.join(['gate', 'file:line', 'sentence', 'verdict_0d24', 'verdict_205a', 'our_value',
                        'tool_expected', 'triage', 'measured', 'tool_note_205a']) + '\n')
    for o in out:
        fh.write('\t'.join(o) + '\n')

# every STALE-DONOR-CODE-POINTER row of the 205a run
frows = [l.rstrip('\n').split('\t') for l in open(full_p, encoding='utf-8', errors='replace') if not l.startswith('#')]
fh_, frows = frows[0], frows[1:]
fx = {c: k for k, c in enumerate(fh_)}
sd = []
for r in frows:
    if r[fx['verdict']] != 'STALE-DONOR-CODE-POINTER':
        continue
    f, ln = r[fx['dst_file']], int(r[fx['dst_line']])
    val, sv = int(r[fx['dst_value']], 0), int(r[fx['src_value']], 0)
    sent, note = r[fx['sentence']], r[fx['note']]
    text = lines_of(os.path.join(lib, side, f))[ln - 1]
    where = f'lib/{side}/{f}:{ln}'
    if val == 262144:
        ok, why = maplen(text)
    elif f in TABLES and sent.startswith('Definition tfib_A_'):
        label = sent.split()[1][len('tfib_A_'):]
        o = sorted(ours.by_start.get(val, ()))
        d = sorted(donor.by_start.get(sv, ()))
        od = dem(o)
        # the label is the function's own identifier: the whole name, or a mangled <length><identifier> component
        # (the length prefix makes the component exactly the label)
        ok = any(x == label or re.search(r'(?<!\d)' + str(len(label)) + re.escape(label), x) for x in od)
        why = (f'our value {val:#x} starts FUNC {", ".join(od)} in our twin, which IS the label `{label}`'
               if ok else f'our value {val:#x} starts FUNC {", ".join(od) or "(none)"}: not the label `{label}`')
        why += (f'; the donor value {sv:#x} starts {", ".join(dem(d)) or "(none)"} in the donor twin: the donor\'s '
                f'label names another function, our row names its own')
    else:
        m = re.search(r'\(ANum (0x[0-9a-fA-F]+)\)\s+' + re.escape(r[fx['dst_value']]) + r'\b', text)
        if m:
            cell = int(m.group(1), 16)
            word = ours.read(cell, 8)
            w = int.from_bytes(word, 'little') if word else None
            o = sorted(ours.by_start.get(val, ()))
            ok = w == val
            why = (f'the 8 pin bytes at the cell {cell:#x} (little endian) are {w:#x}' if w is not None else
                   f'cell {cell:#x} not in a PT_LOAD') + \
                  f' {"=" if ok else "!="} our value {val:#x} ({", ".join(dem(o)) or "no FUNC start"}): the slot the ' \
                  f'image holds; the donor value {sv:#x} is the donor\'s own slot contents ({note.split(";")[0]})'
        else:
            ok, why = False, 'no group'
    sd.append([gate, where, sent, r[fx['src_value']], r[fx['dst_value']], 'OK' if ok else 'OPEN', why, note])
    opened += not ok
with open(sdcp_p, 'w') as fh:
    fh.write('\t'.join(['gate', 'file:line', 'sentence', 'donor_value', 'our_value', 'triage', 'measured',
                        'tool_note_205a']) + '\n')
    for o in sd:
        fh.write('\t'.join(o) + '\n')

c = collections.Counter((o[3], o[4], o[7]) for o in out)
for (a, b, t), n in sorted(c.items()):
    print(f'{gate}\t{a} -> {b}\t{t}\t{n}')
c = collections.Counter(o[5] for o in sd)
print(f'{gate}\tSTALE-DONOR-CODE-POINTER rows of 205a: {len(sd)} ({dict(c)})')
sys.exit(1 if opened else 0)
