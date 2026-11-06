#!/usr/bin/env python3
"""__strftime_fmt_1 +0x60: where does a1 = 0x20028 (set just before the `jr t2` dispatch) go?
Reads the neutral excerpt of __strftime_fmt_1 (neutral_dis.py, old-pin listing; same address 0xa1be4 and the same
instruction words as e89be137db17's twin except 7 pc-relative words) and the 86-entry rel4 jump table from the image;
for every case target it follows straight-line code (both arms of branches, `j` targets) until a1 is written,
read, passed to a call, or the function returns, and prints each distinct outcome with its count.
usage: strftime_a1_trace.py LISTING.s IMAGE"""
import re, sys
from elftools.elf.elffile import ELFFile
LST, IMG = sys.argv[1], sys.argv[2]
BASE, SIZE = 0xa1be4, 1572
def sext(v, b): return v - (1 << b) if v & (1 << (b - 1)) else v
def rd(a, n):
    e = ELFFile(open(IMG, 'rb'))
    for s in e.iter_segments():
        if s['p_type'] == 'PT_LOAD' and s['p_vaddr'] <= a < s['p_vaddr'] + s['p_filesz']:
            f = open(IMG, 'rb'); f.seek(s['p_offset'] + a - s['p_vaddr']); return f.read(n)
ins = {}
for l in open(LST):
    m = re.match(r'\s+([0-9a-f]+):\s+[0-9a-f]+\s+(\S+)\s*(.*)', l)
    if m: ins[int(m.group(1), 16)] = (m.group(2), m.group(3).split('#')[0].strip())
m, o = ins[BASE + 0x40]; assert m == 'auipc' and o.startswith('a7,')
m2, o2 = ins[BASE + 0x44]; assert m2 == 'addi' and o2.startswith('t0,a7,')
t0 = BASE + 0x40 + (sext(int(o.split(',')[1], 16), 20) << 12) + int(o2.split(',')[2])
tab = rd(t0, 86 * 4)
targets = [t0 + sext(int.from_bytes(tab[i*4:i*4+4], 'little'), 32) for i in range(86)]
addrs = sorted(ins); nxt = {a: addrs[i + 1] for i, a in enumerate(addrs[:-1])}
REG = re.compile(r'\b(zero|ra|sp|gp|tp|t[0-6]|s[0-9]|s1[01]|a[0-7]|fp)\b')
BR = {'beq','bne','blt','bge','bltu','bgeu','beqz','bnez','blez','bgez','bltz','bgtz','bgt','ble','bgtu','bleu'}
ST = {'sd','sw','sh','sb','fsd','fsw'}
out = {}
for t in targets:
    ev = set(); seen = set(); st = [t]
    while st:
        a = st.pop()
        while a in ins and a not in seen and BASE <= a < BASE + SIZE:
            seen.add(a); m, o = ins[a]; r = REG.findall(o)
            mt = re.search(r'([0-9a-f]+) <', o); tg = int(mt.group(1), 16) if mt else None
            if m in BR:
                if 'a1' in r: ev.add('read %#x %s %s' % (a - BASE, m, o))
                st.append(tg)
            elif m == 'j': a = tg; continue
            elif m in ('jal', 'call'): ev.add('call with a1 live %#x %s' % (a - BASE, o)); break
            elif m in ('jr', 'ret', 'jalr'): ev.add('leaves %#x %s %s' % (a - BASE, m, o)); break
            elif m in ST:
                if 'a1' in r: ev.add('read %#x %s %s' % (a - BASE, m, o))
            elif o:
                p = [x.strip() for x in o.split(',')]
                if 'a1' in REG.findall(','.join(p[1:])): ev.add('read %#x %s %s' % (a - BASE, m, o))
                if p[0] == 'a1': break
            a = nxt.get(a)
    k = tuple(sorted(ev)) or ('a1 written before any read',)
    out[k] = out.get(k, 0) + 1
print('table %#x, 86 entries, %d distinct targets' % (t0, len(set(targets))))
for k, n in sorted(out.items(), key=lambda x: -x[1]): print(n, '; '.join(k))
