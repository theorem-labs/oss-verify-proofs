#!/usr/bin/env python3
"""ptrfollow.py -- follows every field POINTER that objscan.py saw stored into memory (PTRSTORE) to the code that later
reads the field through it. The pattern in these images is the flag handler: Register*Flags allocates an object, writes
its vtable to word 0 and the field's address to word h (`sd vt, 0(obj) ; sd &field, h(obj)`), and hands the object to the
parser. For each PTRSTORE line of out/objscan.out whose pointer is EXACTLY a watched field:
  1. in the storing function, the store of word 0 on the same base register within 24 instructions; its value
     (escape.reg_value: auipc pair / .got cell) is the vtable address point, inside a _ZTV symbol;
  2. each vtable slot function: a load `ld p, h(a0)` (a0 = this, before a0 is overwritten), then every load THROUGH p
     (`l* x, k(p)`: a read of the field) and every store through p (a write of the field);
  3. each read value is followed with escape.track() to its reader.
usage: ptrfollow.py   (reads out/objscan.out, writes out/ptrfollow.out)"""
import collections, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common, escape

LD = {'lb', 'lbu', 'lh', 'lhu', 'lw', 'lwu', 'ld'}
SD = {'sb', 'sh', 'sw', 'sd'}
LINE = re.compile(r'^    PTRSTORE (.+)\+(0x[0-9a-f]+) stored at unknown (\w+)\+(0x[0-9a-f]+)  at (.+) \+(0x[0-9a-f]+)$')


def fields_of(text):
    """watched fields per object, from the summary lines '<tag>: <object> field +0x..: ...'"""
    f = collections.defaultdict(set)
    for l in text.split('\n'):
        m = re.match(r'^(cgif B|decode B): (.+) field \+(0x[0-9a-f]+): ', l)
        if m:
            f[(m.group(1), m.group(2))].add(int(m.group(3), 16))
    return f


def main():
    text = open(os.path.join(common.OUT, 'objscan.out')).read()
    fl = fields_of(text)
    out, tsv = [], []
    for tag, path in (('cgif B', common.CGIF_B_TWIN), ('decode B', common.DECODE_B_TWIN)):
        img = escape.Image(path); img._index()
        part = text.split('#### %s' % tag)[1].split('####')[0]
        done = set()
        for l in part.split('\n'):
            m = LINE.match(l)
            if not m:
                continue
            obj, off, base, h, label, o = m.group(1), int(m.group(2), 16), m.group(3), int(m.group(4), 16), m.group(5), int(m.group(6), 16)
            if off not in fl.get((tag, obj), ()):
                continue
            fn = label.split(' > ')[-1]
            key = (obj, off, fn, o)
            if key in done:
                continue
            done.add(key)
            a, z = img.I.fsym(fn)
            ins = img.dis(a, z)
            k = [i for i, x in enumerate(ins) if x[0] == o][0]
            # the object is the one allocated by the last call before the site; its word-0 store lies between that call
            # and the next call after the site, on the same base register
            iscall = lambda x: x[1] in ('jal', 'jalr') and not x[2].startswith('zero')
            lo = max([j for j in range(k) if iscall(ins[j])] or [0])
            hi = min([j for j in range(k + 1, len(ins)) if iscall(ins[j])] or [len(ins)])
            vt = None
            for j in range(lo + 1, hi):
                oj, mj, pj, nj = ins[j]
                mm = re.match(r'(\w+), (-?(?:0x[0-9a-f]+|\d+))?\(%s\)$' % base, pj)
                if mj == 'sd' and mm and int(mm.group(2) or '0', 0) == 0:
                    vt = img.reg_value(a, z, j, mm.group(1))
                    if vt is not None:
                        break
            home = img.home(vt) if vt else None
            out.append('%s: %s+%#x stored at %s+%#x of a heap object in %s +%#x; word 0 := %s (%s)' % (
                tag, obj, off, base, h, fn[:90], o, hex(vt) if vt else '?', home))
            if not vt or not home or not home.startswith('_ZTV'):
                out.append('    no vtable found at the site: FOLLOW BY HAND')
                continue
            sym = [(v, zz, n) for v, zz, n, t in img.I.syms if t == 'STT_OBJECT' and v <= vt < v + zz][0]
            for slot in range(vt, sym[0] + sym[1], 8):
                f = int.from_bytes(escape.sc.frd(img.I, slot, 8), 'little')
                fz = [x for x in img.funcs if x[0] == f]
                if not fz:
                    continue
                fins = img.dis(f, fz[0][1])
                reads, writes = [], []
                for j, (oj, mj, pj, nj) in enumerate(fins):
                    mh = re.match(r'(\w+), (-?(?:0x[0-9a-f]+|\d+))?\(a0\)$', pj)
                    if mj == 'ld' and mh and int(mh.group(2) or '0', 0) == h:
                        p = pj.split(',')[0].strip()
                        for j2 in range(j + 1, min(len(fins), j + 48)):
                            o2, m2, p2, n2 = fins[j2]
                            mm = re.match(r'(\w+), (-?(?:0x[0-9a-f]+|\d+))?\(%s\)$' % p, p2)
                            if mm and m2 in LD:
                                us = escape.track(img, f, fz[0][1], j2 + 1, {mm.group(1)})
                                reads.append('+%#x %s: %s' % (o2, m2, ' ; '.join(sorted(' '.join(u) for u in us)) or 'no use found'))
                            if mm and m2 in SD:
                                writes.append('+%#x %s' % (o2, m2))
                            if p2.split(',')[0].strip() == p and m2 not in SD and not m2.startswith('b'):
                                break
                    if pj and pj.split(',')[0].strip() == 'a0' and mj not in SD and not mj.startswith('b'):
                        break
                out.append('    slot +%#x %s: reads of the field %s; writes %s' % (
                    slot - vt, img.name_at(f)[:90], ' | '.join(reads) or 'none', ' '.join(writes) or 'none'))
                tsv.append((tag, obj, '%#x' % off, '%s +%#x' % (fn, o), '%s' % home, '+%#x' % (slot - vt), img.name_at(f),
                            ' | '.join(reads) or 'none', ' '.join(writes) or 'none'))
        out.extend(reuse(img, tag))
    open(os.path.join(common.OUT, 'ptrfollow.out'), 'w').write('\n'.join(out) + '\n')
    with open(os.path.join(common.OUT, 'ptrfollow.tsv'), 'w') as f:
        f.write('image\tobject\tfield\tsite storing the field pointer\tvtable\tslot\tmethod\treads of the field (and their uses)\twrites\n')
        for r in tsv:
            f.write('\t'.join(r) + '\n')
    print('\n'.join(out))


def reuse(img, tag, fn='_ZN6__asan15InitializeFlagsEv', d0=0x168, size=0x120):
    """the stack slot [sp+d0, sp+d0+size) of InitializeFlags, in program order: every instruction that addresses it and every
    call, with the slot address in a0 / a1 marked -- the evidence that the CommonFlags copy there is copied back to the
    global and the slot then rewritten as a FlagParser before the FlagParser calls whose loads objscan attributes to it"""
    a, z = img.I.fsym(fn)
    ins = img.dis(a, z)
    out = ['%s: stack reuse in %s, slot sp+%#x..+%#x (program order):' % (tag, fn, d0, d0 + size)]
    hold, seq = {}, []
    WID = {'sb': 1, 'sh': 2, 'sw': 4, 'sd': 8}
    for k, (o, mn, op, n) in enumerate(ins):
        ops = [x.strip() for x in op.split(',')] if op else []
        mm = re.search(r'(-?(?:0x[0-9a-f]+|\d+))\(sp\)$', op)
        if mn == 'addi' and len(ops) == 3 and ops[1] == 'sp' and d0 <= int(ops[2], 0) < d0 + size:
            hold[ops[0]] = int(ops[2], 0)
            out.append('  +%#x %s %s' % (o, mn, op))
            continue
        if mm and d0 <= int(mm.group(1), 0) < d0 + size and mn in LD | SD:
            out.append('  +%#x %s %s   (slot +%#x)' % (o, mn, op, int(mm.group(1), 0) - d0))
            if mn in SD:
                seq.append((o, 'STORE', int(mm.group(1), 0) - d0, WID[mn]))
            else:
                seq.append((o, 'LOAD', int(mm.group(1), 0) - d0, 8))
            continue
        if mn in ('jal', 'jalr'):
            tg = img.wtarget.get(a + o)
            if tg is None and mn == 'jal':
                tg = a + o + int(ops[-1], 0)
            args = {r: v for r, v in hold.items() if r in ('a0', 'a1', 'a2') and v == d0}
            if args:
                nm = img.name_at(tg) if tg else '?'
                out.append('  +%#x %s -> %s   (%s)' % (o, mn, nm[:70], ', '.join('%s=sp+%#x' % kv for kv in sorted(args.items()))))
                if 'CopyFrom' in nm and 'a0' in args:
                    seq.append((o, 'COPYIN', nm, None))
                elif 'CopyFrom' in nm and 'a1' in args:
                    seq.append((o, 'COPYOUT', nm, None))
                elif 'memset' in nm and 'a0' in args:
                    seq.append((o, 'FILL', nm, None))
                else:
                    seq.append((o, 'CALL', nm, sorted(args)))
            for r in [r for r in hold if r.startswith(('a', 't')) or r == 'ra']:
                del hold[r]
            continue
        if ops and ops[0] in hold and mn not in SD and not mn.startswith('b'):
            del hold[ops[0]]
    # the verdict, in program order, per field of the CommonFlags copy: what each call receiving the slot sees in that word
    for F in (0x18, 0xc8, 0xd0):
        state, src = None, None
        for o, kind, x, y in seq:
            if kind == 'COPYIN':
                state, src = 'the copy', '+%#x' % o
            elif kind == 'FILL':
                state, src = 'memset fill', '+%#x' % o
            elif kind == 'STORE' and x <= F < x + y:
                state, src = 'rewritten', '+%#x' % o
            elif kind == 'LOAD' and x <= F < x + 8:
                out.append('REUSE-VERDICT %s field +%#x: load at +%#x in %s sees %s (%s)' % (tag, F, o, fn, state, src))
            elif kind == 'CALL':
                out.append('REUSE-VERDICT %s field +%#x: call +%#x %s (%s) sees %s (%s)' % (tag, F, o, x, ','.join(y), state, src))
    return out


if __name__ == '__main__':
    main()
