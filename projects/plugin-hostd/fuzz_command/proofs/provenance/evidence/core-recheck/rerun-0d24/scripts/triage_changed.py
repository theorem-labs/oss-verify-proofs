#!/usr/bin/env python3
"""Triage every row whose verdict changed between port_addr_check 3d2eee813cce and 0d24592683b6 on one gate.

Usage: triage_changed.py GATE CHANGED.tsv OURS_LIB IMGDIR OUT.tsv
  GATE      RA (image A core, lib/A) or RB (image B core, lib/B)
  CHANGED   diff_rows.py's changed.tsv for that gate
  OURS_LIB  extract of the checked commit's lib/ (A/, B/, ...)
  IMGDIR    the image copies (cmd.A.pin / cmd.A.twin, cmd.B.pin / cmd.B.twin)

Each changed row is measured by its group; the group is read from the row, never assumed:
  table     a cell of the generated function table (AB1w.v / YB1w.v): its readers outside the two table files in the
            whole lib/ tree, the object our value names against the donor's (the row's dst_res / src_res: the symbol +
            offset for a start cell tfib_A_*, the object it ends for an end cell tfib_E_*), and which definitions of the
            same table hold the value the tool expects.
  bound     a numeral inside an `assert (Hrange ... <= N)` over the entries of icpt_rodata: the largest
            start + length of icpt_rodata in our file of that image (AE2y.v / YE2y.v) against N, and the proof's end.
  maplen    the literal 262144 as a register value of a symbolic state (a `pin (runto PC ..) R (SLit 262144)` or a
            register equation `sr_get .. 11%bv = SLit 262144 .. 12%bv = SLit PROT`): the containing function of each pin
            PC in our image and the rounding constants that function loads (lui 0x40 = 0x40000, lui 0xfffc0 = its mask).
  no flag   the new verdict is not a finding class: listed, not triaged.
A row of no group is written with triage OPEN and makes the exit status 1.
"""
import collections
import os
import re
import sys
from elftools.elf.elffile import ELFFile

gate, changed_p, lib, imgdir, out_p = sys.argv[1:6]
side = {'RA': 'A', 'RB': 'B'}[gate]
TABLES = ('AB1w.v', 'YB1w.v')
NOFLAG = {'UNMEASURED-NAME', 'SAME-SYMBOL'}


def sx(v, b):
    return v - (1 << b) if v & (1 << (b - 1)) else v


# readers: identifier -> files outside the two table files that name it
readers = collections.defaultdict(set)
for dp, _, fs in os.walk(lib):
    for f in fs:
        if f.endswith('.v') and f not in TABLES:
            p = os.path.join(dp, f)
            for m in set(re.findall(r'\btfib_[A-Za-z0-9_]+\b', open(p, encoding='utf-8', errors='replace').read())):
                readers[m].add(os.path.relpath(p, lib))

table_txt = open(os.path.join(lib, side, TABLES[0] if side == 'A' else TABLES[1]), encoding='utf-8').read()
table_defs = collections.defaultdict(list)
for name, val in re.findall(r'Definition (tfib_[A-Za-z0-9_]+) : Z := (0x[0-9a-fA-F]+|\d+)\.', table_txt):
    table_defs[int(val, 0)].append(name)

# icpt_rodata: largest start + length
y2 = open(os.path.join(lib, side, 'AE2y.v' if side == 'A' else 'YE2y.v'), encoding='utf-8').read()
i = y2.index('Definition icpt_rodata ')
body = y2[y2.index(':=', i) + 2:y2.index('].', i)]
ents = re.findall(r'^\s*\[?\s*\(\s*(0x[0-9a-fA-F]+|\d+)\s*,\s*(\d+)\s*,\s*\[', body, re.M)
icpt_max = max(int(a, 0) + int(b) for a, b in ents)

# image: functions and loaded bytes
img = os.path.join(imgdir, f'cmd.{side}.pin')
twin = os.path.join(imgdir, f'cmd.{side}.twin')
with open(twin, 'rb') as f:
    funcs = [(s['st_value'], s['st_size'], s.name) for s in ELFFile(f).get_section_by_name('.symtab').iter_symbols()
             if s['st_info']['type'] == 'STT_FUNC' and s['st_size'] > 0]
with open(img, 'rb') as f:
    segs = [(s['p_vaddr'], s.data()) for s in ELFFile(f).iter_segments() if s['p_type'] == 'PT_LOAD']


def luis(pc):
    """containing FUNC symbol of pc and every lui / c.lui it holds, as (pc, rd, value)."""
    s, n, name = min([t for t in funcs if t[0] <= pc < t[0] + t[1]], key=lambda t: t[1])
    base, d = next((b, d) for b, d in segs if b <= s < b + len(d))
    out, a = [], s
    while a < s + n:
        h = int.from_bytes(d[a - base:a - base + 2], 'little')
        if h & 3 != 3:
            if h & 3 == 1 and h >> 13 == 3 and ((h >> 7) & 31) not in (0, 2):
                v = sx(((h >> 12) & 1) << 5 | ((h >> 2) & 31), 6)
                out.append((a, (h >> 7) & 31, sx((v << 12) & 0xffffffff, 32) & (2 ** 64 - 1)))
            a += 2
            continue
        w = int.from_bytes(d[a - base:a - base + 4], 'little')
        if w & 0x7f == 0x37:
            out.append((a, (w >> 7) & 31, sx(w & 0xfffff000, 32) & (2 ** 64 - 1)))
        a += 4
    return name, s, out


def lines_of(path):
    return open(path, encoding='utf-8', errors='replace').read().split('\n')


rows = [l.rstrip('\n').split('\t') for l in open(changed_p, encoding='utf-8')]
hdr, rows = rows[0], rows[1:]
ix = {c: k for k, c in enumerate(hdr)}
out = []
opened = 0
for r in rows:
    ov, nv, f, ln = r[ix['old_verdict']], r[ix['new_verdict']], r[ix['dst_file']], int(r[ix['dst_line']])
    sent, val = r[ix['sentence']], int(r[ix['dst_value']], 0)
    note = r[ix['note']]
    exp = re.search(r'expected (0x[0-9a-f]+)', note)
    exp = exp.group(1) if exp else '-'
    where = f'lib/{side}/{f}:{ln}'
    text = lines_of(os.path.join(lib, side, f))[ln - 1]
    if nv in NOFLAG:
        tri, why = 'no flag', f'the new verdict {nv} is not a finding class'
    elif f in TABLES and sent.startswith('Definition tfib_'):
        name = sent.split()[1]
        nread = len(readers.get(name, ()))
        # an A cell is the start of an object: compare the symbol + offset the value resolves to; an E cell is the end
        # of an object: compare the object it ends ("end of X"), since the object after it may differ by build
        res_o, res_d = r[ix['dst_res']], r[ix['src_res']]
        eo, ed = re.search(r'end of (\S+)', res_o), re.search(r'end of (\S+)', res_d)
        if name.startswith('tfib_E_') and eo and ed:
            ours, donor = f'the end of {eo.group(1)}', f'the end of {ed.group(1)}'
        else:
            ours = res_o.replace('END by name: ', '').split(';')[0].strip()
            donor = res_d.replace('END by name: ', '').split(';')[0].strip()
        holders = [n for n in table_defs.get(int(exp, 16), []) if n != name] if exp != '-' else []
        ok = nread == 0 and ours == donor
        tri = 'OK' if ok else 'OPEN'
        why = (f'{name} is named by {nread} files of lib/ outside the two table files; our value is {ours}, the '
               f'donor\'s cell is {donor} ({"the same object" if ours == donor else "NOT the same object"}); the '
               f'tool\'s expected {exp} is '
               + (f'the value of {", ".join(holders)} in the same table' if holders else 'held by no other row of the table'))
    elif 'Hrange' in text and nv == 'SAME-VALUE-DIFFERENT-OBJECT':
        bound = int(re.search(r'<=\s*(0x[0-9a-fA-F]+|\d+)\s*\)', text).group(1), 0)
        L = lines_of(os.path.join(lib, side, f))
        end = next(k for k in range(ln, len(L)) if re.search(r'\b(Qed|Admitted|Abort|Defined)\.', L[k]))
        endw = re.search(r'\b(Qed|Admitted|Abort|Defined)\.', L[end]).group(1)
        ok = val == bound and icpt_max <= bound and endw == 'Qed'
        tri = 'OK' if ok else 'OPEN'
        why = (f'a bound, not an address: the assert states start + length <= {bound:#x} for every entry of '
               f'icpt_rodata; the largest start + length in our {"AE2y.v" if side == "A" else "YE2y.v"} is {icpt_max:#x}; '
               f'each entry is closed by lia and the proof ends {endw} at line {end + 1}')
    elif val == 262144 and nv == 'STALE-DONOR-CODE-POINTER':
        pins = re.findall(r'pin \(runto (0x[0-9a-fA-F]+) [A-Za-z0-9_]+\) (\d+)%bv \(SLit 262144\)', text)
        regeq = re.search(r'11%bv = SLit 262144', text) and re.search(r'12%bv = SLit (\d+)\b', text)
        meas = []
        for pc_s, reg in pins:
            name, s, ls = luis(int(pc_s, 16))
            g = [f'lui x{rd} {v:#x} at {a:#x}' for a, rd, v in ls if v in (0x40000, 0xfffffffffffc0000)]
            meas.append(f'x{reg} pinned at pc {pc_s} in {name} (at {s:#x}), which loads {", ".join(g) or "no 0x40000 rounding constant"}')
        if regeq:
            prot = int(regeq.group(1))
            pn = {0: 'PROT_NONE', 3: 'PROT_READ | PROT_WRITE'}.get(prot, 'prot ?')
            meas.append(f'register equation: x11 = 262144 with x12 = {prot} ({pn}): the length argument of the map call')
        ok = bool(meas) and all('no 0x40000' not in m for m in meas)
        tri = 'OK' if ok else 'OPEN'
        why = 'a map length, not a code pointer: ' + '; '.join(meas) if meas else 'role not read from the line'
    else:
        tri, why = 'OPEN', 'no group'
    opened += tri == 'OPEN'
    out.append([gate, where, sent, ov, nv, r[ix['dst_value']], exp, tri, why, note])

with open(out_p, 'w') as f:
    f.write('\t'.join(['gate', 'file:line', 'sentence', 'verdict_3d2e', 'verdict_0d24', 'our_value',
                       'tool_expected', 'triage', 'measured', 'tool_note_0d24']) + '\n')
    for o in out:
        f.write('\t'.join(o) + '\n')
c = collections.Counter((o[4], o[7]) for o in out)
for (v, t), n in sorted(c.items()):
    print(f'{gate}\t{v}\t{t}\t{n}')
sys.exit(1 if opened else 0)
