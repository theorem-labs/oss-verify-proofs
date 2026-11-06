#!/usr/bin/env python3
"""flagreads.py IMAGE NM AF0M [--entry HEX ...] [--depth N] [--reads OUT] -- the flag bytes and REAL(f) cells the
interceptors reac-pw/fuzz_link's program reaches read, checked against AF0m's Tfib_const_abs.

Reach: from main, over direct jal / j edges (pautrlen/base.Image's call graph; plus the jump-table targets and tail
entries given with --entry), not descending into the runtime (names starting _ZN11__sanitizer, _ZN6__asan,
_ZN14__interception, __asan_, __sanitizer, __lsan, __ubsan) and stopping AT every ___interceptor_* body (recorded).
Reads: in each reached ___interceptor_* body (and, with --depth 1, the runtime functions it calls directly), a linear
scan tracks registers that hold a known address (auipc + addi, auipc + load of a GOT slot whose word points into a flag
struct, mv) and records every load whose address falls in _ZN11__sanitizer21common_flags_dont_useE or
_ZN6__asan28asan_flags_dont_use_directlyE, or is the start of an __interception::real_<f> cell (the 8-byte load an
interceptor makes before its indirect call): (cell, offset, width, reader pc, function).
Output: one row per distinct (address, width): covered when Tfib_const_abs of AF0M has a cell AT that address OF that
width (consumers look a cell up by address and width, e.g. icells_sc_of_ARm; a wider word over the byte does not serve
them), else MISSING (the row says when a wider cell holds the bytes); --reads OUT writes the MISSING ones as af0m
`--reads` lines (ADDR/W). Controls: ___interceptor_strncmp must show common_flags+0xf5 (strict_string_checks), and
___interceptor_strlen REAL(strlen) at 0xa36d0 (its load at 0x43120).
"""
import argparse, re, struct, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'set/tools/startup-set/2026-10-30b/pautrlen'))
from base import Image, tgt, hi20   # noqa: E402

RUNTIME = ('_ZN11__sanitizer', '_ZN6__asan', '_ZN14__interception', '__asan_', '__sanitizer', '__lsan', '__ubsan', '_ZN7__lsan', '_ZN7__ubsan')
LOADS = {'lb': 1, 'lbu': 1, 'lh': 2, 'lhu': 2, 'lw': 4, 'lwu': 4, 'ld': 8, 'c.lw': 4, 'c.ld': 8, 'c.lwsp': 4, 'c.ldsp': 8}


def nm_table(path):
    by_addr, by_name = {}, {}
    for l in open(path):
        p = l.split()
        if len(p) == 4:
            a, s, n = int(p[0], 16), int(p[1], 16), p[3]
        elif len(p) == 3:
            a, s, n = int(p[0], 16), 0, p[2]
        else:
            continue
        by_addr.setdefault(a, []).append((n, s))
        by_name.setdefault(n, []).append((a, s))
    return by_addr, by_name


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('image'); ap.add_argument('nm'); ap.add_argument('af0m')
    ap.add_argument('--entry', action='append', default=[], help='extra reached function starts (hex)')
    ap.add_argument('--depth', type=int, default=1)
    ap.add_argument('--reads', default=None)
    ap.add_argument('--all-real', action='store_true',
                    help='also scan EVERY ___interceptor_* body of the image for REAL(f) loads (reached or not)')
    a = ap.parse_args()
    I = Image(a.image)
    by_addr, by_name = nm_table(a.nm)
    structs = {}
    for n, label in (('_ZN11__sanitizer21common_flags_dont_useE', 'common_flags'), ('_ZN6__asan28asan_flags_dont_use_directlyE', 'asan_flags')):
        (addr, size), = by_name[n]
        structs[label] = (addr, size)

    def name(f):
        return by_addr.get(f, [('fn_%x' % f, 0)])[0][0]

    real = {a_: n for n, lst in by_name.items() if n.startswith('_ZN14__interception') and 'real_' in n
            for a_, _s in lst}

    def in_struct(x):
        for lab, (lo, sz) in structs.items():
            if lo <= x < lo + sz:
                return lab, x - lo
        if x in real:
            return 'REAL(%s)' % re.sub(r'^_ZN14__interception\d+real_(\w+)E$', r'\1', real[x]), 0
        return None
    # reach
    starts = [I.main] + [int(x, 16) for x in a.entry]
    seen, todo, icpt = set(), list(starts), set()
    while todo:
        f = todo.pop()
        if f in seen:
            continue
        seen.add(f)
        n = name(f)
        if n.startswith('___interceptor_'):
            icpt.add(f)
            continue
        if n.startswith('__interceptor_trampoline_'):
            for x in I.first(f, 1):
                t = tgt(x)
                if t is not None:
                    todo.append(t)
            continue
        if n.startswith(RUNTIME):
            continue
        for t in I.callees.get(f, ()):
            todo.append(t)
    # reads
    rows = {}

    def scan(f, who, real_only=False):
        regs = {}
        for x in I.body(f):
            m, ops = x.mnemonic, [o.strip() for o in x.op_str.split(',')]
            if m == 'auipc':
                regs[ops[0]] = x.address + hi20(ops[1])
                continue
            if m in ('addi', 'c.addi') and len(ops) == 3 and ops[1] in regs:
                regs[ops[0]] = regs[ops[1]] + int(ops[2], 0)
                continue
            if m in ('mv', 'c.mv') and ops[1] in regs:
                regs[ops[0]] = regs[ops[1]]
                continue
            mm = re.match(r'(-?0x[0-9a-f]+|-?\d+)\((\w+)\)', ops[-1]) if len(ops) >= 2 else None
            if m in LOADS and mm and mm.group(2) in regs:
                addr = regs[mm.group(2)] + int(mm.group(1), 0)
                hit = in_struct(addr)
                if hit and not (real_only and not hit[0].startswith('REAL(')):
                    rows.setdefault((addr, LOADS[m]), []).append((hit, x.address, who))
                if m in ('ld', 'c.ld'):
                    w = I.read64(addr)
                    if w is not None and in_struct(w):
                        regs[ops[0]] = w          # a GOT slot holding a flag struct's address
                        continue
                regs.pop(ops[0], None)
                continue
            if ops and re.match(r'^[a-z]\w*$', ops[0]) and m not in ('sd', 'sw', 'sh', 'sb', 'c.sd', 'c.sw', 'beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu', 'j', 'c.j', 'jr', 'c.jr', 'ret'):
                regs.pop(ops[0], None)
            if m in ('jal', 'c.jal', 'jalr', 'c.jalr'):
                for r in ('ra', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7', 't0', 't1', 't2', 't3', 't4', 't5', 't6'):
                    regs.pop(r, None)
    for f in sorted(icpt):
        scan(f, name(f))
        if a.depth >= 1:
            for t in sorted(I.callees.get(f, ())):
                if name(t).startswith(RUNTIME):
                    scan(t, '%s <- %s' % (name(t), name(f)))
    unreached = sorted(x for x, lst in by_addr.items() if x not in icpt and any(n.startswith('___interceptor_') for n, _ in lst)) \
        if a.all_real else []
    for f in unreached:
        scan(f, '%s (not reached)' % name(f), real_only=True)
    if a.all_real:
        print('--all-real: %d further ___interceptor_* bodies scanned for REAL(f) loads only' % len(unreached))
    # AF0m coverage
    txt = open(a.af0m).read()
    m = re.search(r'Definition Tfib_const_abs : list acell :=\n\[(.*?)\]\.', txt, re.S)
    body = re.sub(r'\(\*.*?\*\)', ' ', m.group(1), flags=re.S)
    cov, exact = set(), set()
    for w, ad in re.findall(r'\b[zc](\d)\s*\(ANum\s+(0x[0-9a-fA-F]+)\)', body):
        exact.add((int(ad, 16), int(w)))
        for k in range(int(w)):
            cov.add(int(ad, 16) + k)
    print('reached interceptors (%d): %s' % (len(icpt), ', '.join(sorted(name(f) for f in icpt))))
    missing = []
    for (addr, w), uses in sorted(rows.items()):
        ok = (addr, w) in exact
        (lab, off), _, _ = uses[0]
        print('%s %s+%#x (%#x) w%d%s readers: %s' % (
            'covered' if ok else 'MISSING', lab, off, addr, w,
            '' if ok else (' (bytes held by a wider cell)' if all(addr + k in cov for k in range(w)) else ' (no cell holds it)'),
            '; '.join('%#x %s' % (pc, who) for _, pc, who in uses)))
        if not ok:
            missing.append((addr, w))
    print('flag reads: %d distinct (address, width); %d covered by Tfib_const_abs; %d MISSING' % (len(rows), len(rows) - len(missing), len(missing)))
    if a.reads:
        with open(a.reads, 'w') as o:
            o.write('# flag bytes read by the interceptors link reaches, missing from Tfib_const_abs (flagreads.py)\n')
            for addr, w in missing:
                o.write('%#x/%d\n' % (addr, w))


if __name__ == '__main__':
    main()
