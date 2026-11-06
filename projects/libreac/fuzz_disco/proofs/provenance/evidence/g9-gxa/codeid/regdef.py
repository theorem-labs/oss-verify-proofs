#!/usr/bin/env python3
"""Which instruction defines a register on every control-flow path that reaches one instruction of a function, in the
fm twin and in each fuzz_disco twin; and, when that definition is the low half of an auipc pair, the pair's target and
the comparison kit's judgement of that pair against the fm side.

  regdef.py KIT_DIR FUNC OFFSET REG [--table OFF:N ...] TAG=TWIN ...     (the first TAG is the reference, the fm twin)

KIT_DIR: the comparison kit (strictcmp2's Img, targets and tsame are used; nothing is copied from it). FUNC: a function
name that one FUNC symbol of each twin carries; OFFSET: the instruction's offset in it; REG: xN. --table OFF:N: a jump
table whose address the auipc pair ending at function offset OFF computes and which has N 4-byte entries, each
relative to the table's address (the jump tables the kit's jtcheck accepted); its dispatch is the first `jalr x0` at
or after OFF. Control flow: a branch goes to its target and to the next instruction; `jal x0` / `jalr x0` only to
their targets (a table's entries, or none for a return); a call (`jal` / `jalr` with rd != x0) to the next
instruction and it DEFINES every caller-saved register. The search walks back from the instruction over its
predecessors and stops on each path at the first instruction that writes REG. The function must have no 2-byte
parcel (the decoder reads 4-byte words only; a 2-byte parcel stops the run).
"""
import argparse
import hashlib
import importlib.util
import os
import struct
import sys

import capstone

CALLER_SAVED = {1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31}
WRITES_RD = {0x37, 0x17, 0x6f, 0x67, 0x03, 0x13, 0x1b, 0x33, 0x3b, 0x2f}
MD = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def sx(v, bits):
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def writes(w):
    """the integer register a 4-byte word writes (None: none); calls return 'call'"""
    op, rd = w & 0x7f, (w >> 7) & 31
    if op in (0x6f, 0x67) and rd != 0:
        return 'call'
    if op == 0x73 and (w >> 12) & 7:
        return rd or None
    if op == 0x53 and (w >> 27) & 31 in (0x14, 0x18, 0x1c):
        return rd or None
    return rd if op in WRITES_RD and rd else None


def btarget(a, w):
    op = w & 0x7f
    if op == 0x63:
        imm = ((w >> 31) << 12) | (((w >> 7) & 1) << 11) | (((w >> 25) & 0x3f) << 5) | (((w >> 8) & 0xf) << 1)
        return a + sx(imm, 13)
    if op == 0x6f:
        imm = ((w >> 31) << 20) | (((w >> 12) & 0xff) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3ff) << 1)
        return a + sx(imm, 21)
    return None


def text(a, w):
    i = next(MD.disasm(struct.pack('<I', w), a), None)
    return '%08x %s' % (w, '%s %s' % (i.mnemonic, i.op_str) if i else '?')


def cfg(s2, img, v, z, func, tables, who='regdef.py'):
    """(words {offset: word}, succ, pred) of the function at v (size z): 4-byte words only; branches go to their target
    and the next word, `jal x0` / `jalr x0` to their targets only (a table's entries, none for a return or an unknown
    jump), a call to the next word; tables: (offset of the auipc pair's lo12 word, entry count) of rel4 jump tables"""
    data = next(d[v - pv:v - pv + z] for pv, fz, d in img.segs if pv <= v and v + z <= pv + fz)
    words = {}
    k = 0
    while k < z:
        h = struct.unpack_from('<H', data, k)[0]
        if h & 3 != 3:
            sys.exit('%s: 2-byte parcel at %s+%#x: not measured' % (who, func, k))
        words[k] = struct.unpack_from('<I', data, k)[0]
        k += 4
    succ = {o: [] for o in words}
    tab_of = {}
    for toff, n in tables:
        aw, lw = words[toff - 4], words[toff]           # auipc, then its lo12 partner
        if aw & 0x7f != 0x17 or (lw >> 15) & 31 != (aw >> 7) & 31:
            sys.exit('%s: no auipc pair ends at %s+%#x' % (who, func, toff))
        taddr = v + toff - 4 + sx(aw & 0xfffff000, 32) + sx(lw >> 20, 12)
        disp = next(o for o in sorted(words) if o >= toff and words[o] & 0x7f == 0x67 and (words[o] >> 7) & 31 == 0)
        ents = []
        for e in range(n):
            t = taddr + struct.unpack('<i', s2.frd(img, taddr + 4 * e, 4))[0] - v
            if t not in words:
                sys.exit('%s: table %#x entry %d is not an instruction of %s' % (who, taddr, e, func))
            ents.append(t)
        tab_of[disp] = (taddr, ents)
    for o, w in words.items():
        op, rd = w & 0x7f, (w >> 7) & 31
        nxt = [o + 4] if o + 4 in words else []
        if op == 0x63:
            succ[o] = nxt + [btarget(v + o, w) - v]
        elif op == 0x6f:
            succ[o] = [btarget(v + o, w) - v] if rd == 0 else nxt
        elif op == 0x67:
            succ[o] = tab_of[o][1] if rd == 0 and o in tab_of else ([] if rd == 0 else nxt)
        else:
            succ[o] = nxt
    pred = {o: set() for o in words}
    for o, ss in succ.items():
        for t in ss:
            if t in pred:
                pred[t].add(o)
    return words, succ, pred, tab_of


def measure(s2, img, func, off, reg, tables):
    v, z = img.fsym(func)
    words, succ, pred, tab_of = cfg(s2, img, v, z, func, tables)
    return v, words, pred, sorted(pred[off]), reaching(words, pred, off, reg)


def reaching(words, pred, at, reg):
    """the instructions that define reg on the control-flow paths reaching `at` (a call defines every caller-saved
    register)"""
    defs, seen, work = set(), set(), list(pred[at])
    while work:
        p = work.pop()
        if p in seen:
            continue
        seen.add(p)
        wr = writes(words[p])
        if wr == reg or (wr == 'call' and reg in CALLER_SAVED):
            defs.add(p)
        else:
            work.extend(pred[p])
    return sorted(defs)


def pair_of(words, pred, d, reg):
    """(auipc offset, lo12 offset) when the definition at d is `addi/ld reg, lo(reg)` and, on every path reaching d,
    reg is defined by one and the same `auipc reg`"""
    w = words[d]
    if w & 0x7f in (0x13, 0x03) and (w >> 15) & 31 == reg:
        up = reaching(words, pred, d, reg)
        if len(up) == 1 and words[up[0]] & 0x7f == 0x17 and (words[up[0]] >> 7) & 31 == reg:
            return up[0], d
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('kit')
    ap.add_argument('func')
    ap.add_argument('offset')
    ap.add_argument('reg')
    ap.add_argument('images', nargs='+')
    ap.add_argument('--table', action='append', default=[])
    a = ap.parse_args()
    spec = importlib.util.spec_from_file_location('strictcmp2', os.path.join(a.kit, 'strictcmp2.py'))
    s2 = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(s2)
    off, reg = int(a.offset, 16), int(a.reg.lstrip('x'))
    tables = [(int(t.split(':')[0], 16), int(t.split(':')[1])) for t in a.table]
    imgs = [(t, p) for t, p in (x.split('=', 1) for x in a.images)]
    print('# %s+%#x, register x%d; kit %s; tables %s' % (a.func, off, reg, hashlib.sha256(
        open(os.path.join(a.kit, 'SHA256SUMS'), 'rb').read()).hexdigest()[:12], ', '.join(a.table) or 'none'))
    print('image\ttwin sha256\tinstruction\tcontrol-flow predecessors\tdefinitions of x%d on the paths reaching it\t'
          'definition pair (auipc, lo12) and its target\tkit tsame of that pair against %s\twhat the instruction does'
          % (reg, imgs[0][0]))
    ref = None
    for tag, path in imgs:
        img = s2.Img(path)
        v, words, pred, preds, defs = measure(s2, img, a.func, off, reg, tables)
        cells, judged, kinds, lands = [], [], set(), []
        for d in defs:
            pr = pair_of(words, pred, d, reg)
            if not pr:
                cells.append('+%#x %s (not an auipc pair)' % (d, text(v + d, words[d])))
                kinds.add('other')
                continue
            ao, lo = pr
            tgt = v + ao + sx(words[ao] & 0xfffff000, 32) + sx(words[lo] >> 20, 12)
            cells.append('+%#x %s; +%#x %s -> %#x %s' % (ao, text(v + ao, words[ao]), lo, text(v + lo, words[lo]), tgt,
                                                         s2.qres(img, tgt)))
            cs = s2.cstring(img, tgt)
            lands.append((tgt, cs, ao, lo))
            if ref is None:
                judged.append('reference')
            else:
                rimg, rv, rwords = ref
                rt = s2.targets(rv, s2.frd(rimg, rv, max(rwords) + 4))
                mt = s2.targets(v, s2.frd(img, v, max(words) + 4))
                wi = sorted(rwords).index(lo)
                if wi in rt and wi in mt:
                    ok, kind, ra, rb, info = s2.tsame(rimg, rt[wi][1], img, mt[wi][1], words[lo])
                    judged.append('+%#x %s %s (%s | %s%s)' % (lo, 'accepted' if ok else 'NOT accepted', kind, ra, rb,
                                                             ', %r' % info if kind == 'cstr' else ''))
                else:
                    judged.append('+%#x not a compared target' % lo)
            kinds.add('pair')
        w = words[off]
        rs1, imm = (w >> 15) & 31, sx(w >> 20, 12)
        if kinds == {'pair'} and w & 0x707f == 0x13 and rs1 == reg:
            inside = ['%#x = byte %d of the %d-byte C string %r at %#x' % (t + imm, imm, len(c), c, t) if c and
                      0 <= imm < len(c) else '%#x (outside a C string at %#x)' % (t + imm, t) for t, c, _, _ in lands]
            what = ('x%d = x%d %+d; control-flow predecessors: %s; x%d is, on every path, the completed '
                    'address of the auipc pair %s; the word adds %d to that address (a pointer increment, %s), it is '
                    'not the lo12 half of an auipc'
                    % ((w >> 7) & 31, rs1, imm, ', '.join('+%#x' % p for p in preds), rs1,
                       ', '.join('+%#x / +%#x' % (x, y) for _, _, x, y in lands), imm, '; '.join(inside)))
        else:
            what = 'not settled by this measurement'
        print('\t'.join([tag, sha(path), '+%#x %s' % (off, text(v + off, w)), ', '.join('+%#x' % p for p in preds),
                         ', '.join('+%#x' % d for d in defs), ' | '.join(cells), ' | '.join(judged), what]))
        if ref is None:
            ref = (img, v, words)


if __name__ == '__main__':
    main()
