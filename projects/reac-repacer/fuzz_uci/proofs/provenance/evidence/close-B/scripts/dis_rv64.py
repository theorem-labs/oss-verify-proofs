#!/usr/bin/env python3
"""dis_rv64.py IMAGE TWIN OUTDIR TAG -- the measurements of image TAG (A or B) that lib/B/Prog's statement texts and
lib/B/UciBClose.v cite: an RV64IM listing of the six program functions (LLVMFuzzerTestOneInput, check_no_overread,
check_value, check_clamp, rp_hot_clamp, rp_uci_int), every branch or jump to an `unimp` word (0xc0001073, UBSan's trap)
in them, and every instruction that writes s0 in the three functions whose call contexts the statements fix.
Words are read from IMAGE (the pin), symbol names from TWIN (its unstripped twin; its words must equal the pin's in
the listed functions, checked). Needs pyelftools. Writes OUTDIR/dis-TAG.txt, OUTDIR/ubsan-traps-TAG.txt,
OUTDIR/s0-writes-TAG.txt.
"""
import struct
import sys

from elftools.elf.elffile import ELFFile

ABI = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
       's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
FUNCS = ['LLVMFuzzerTestOneInput', 'check_no_overread', 'check_value', 'check_clamp', 'rp_hot_clamp', 'rp_uci_int']
CTX_FUNCS = ['LLVMFuzzerTestOneInput', 'check_no_overread', 'check_value']
UNIMP = 0xc0001073


def sx(v, b):
    v &= (1 << b) - 1
    return v - (1 << b) if v >> (b - 1) else v


def segs_of(path):
    f = ELFFile(open(path, 'rb'))
    return [(s['p_vaddr'], s['p_filesz'], s.data()) for s in f.iter_segments() if s['p_type'] == 'PT_LOAD']


def word(segs, a):
    for va, fs, d in segs:
        if va <= a and a + 4 <= va + fs:
            return struct.unpack('<I', d[a - va:a - va + 4])[0]
    raise KeyError(hex(a))


def target(w, pc):
    op = w & 0x7f
    if op == 0x6f:
        return pc + sx((((w >> 31) & 1) << 20) | (((w >> 12) & 0xff) << 12) | (((w >> 20) & 1) << 11)
                       | (((w >> 21) & 0x3ff) << 1), 21)
    if op == 0x63:
        return pc + sx((((w >> 31) & 1) << 12) | (((w >> 7) & 1) << 11) | (((w >> 25) & 0x3f) << 5)
                       | (((w >> 8) & 0xf) << 1), 13)
    return None


def dis(w, pc, name):
    op = w & 0x7f; rd = (w >> 7) & 31; f3 = (w >> 12) & 7; rs1 = (w >> 15) & 31; rs2 = (w >> 20) & 31; f7 = w >> 25
    R = ABI
    if w == UNIMP:
        return 'unimp'
    if op == 0x37:
        return 'lui %s, %#x' % (R[rd], (w >> 12) & 0xfffff)
    if op == 0x17:
        return 'auipc %s, %#x  # %#x' % (R[rd], (w >> 12) & 0xfffff, (pc + sx(w & 0xfffff000, 32)) % 2 ** 64)
    if op == 0x6f:
        t = target(w, pc)
        return 'jal %s, %#x <%s>' % (R[rd], t, name.get(t, '?'))
    if op == 0x67:
        return 'jalr %s, %d(%s)' % (R[rd], sx(w >> 20, 12), R[rs1])
    if op == 0x63:
        n = {0: 'beq', 1: 'bne', 4: 'blt', 5: 'bge', 6: 'bltu', 7: 'bgeu'}.get(f3, 'b?')
        return '%s %s, %s, %#x' % (n, R[rs1], R[rs2], target(w, pc))
    if op == 0x03:
        n = {0: 'lb', 1: 'lh', 2: 'lw', 3: 'ld', 4: 'lbu', 5: 'lhu', 6: 'lwu'}[f3]
        return '%s %s, %d(%s)' % (n, R[rd], sx(w >> 20, 12), R[rs1])
    if op == 0x23:
        n = {0: 'sb', 1: 'sh', 2: 'sw', 3: 'sd'}[f3]
        return '%s %s, %d(%s)' % (n, R[rs2], sx(((w >> 25) << 5) | ((w >> 7) & 31), 12), R[rs1])
    if op == 0x13:
        imm = sx(w >> 20, 12)
        if f3 == 0:
            return 'addi %s, %s, %d' % (R[rd], R[rs1], imm)
        if f3 == 1:
            return 'slli %s, %s, %d' % (R[rd], R[rs1], (w >> 20) & 63)
        if f3 == 5:
            return '%s %s, %s, %d' % ('srai' if (w >> 30) & 1 else 'srli', R[rd], R[rs1], (w >> 20) & 63)
        return '%s %s, %s, %d' % ({2: 'slti', 3: 'sltiu', 4: 'xori', 6: 'ori', 7: 'andi'}[f3], R[rd], R[rs1], imm)
    if op == 0x1b:
        imm = sx(w >> 20, 12)
        if f3 == 0:
            return 'addiw %s, %s, %d' % (R[rd], R[rs1], imm)
        if f3 == 1:
            return 'slliw %s, %s, %d' % (R[rd], R[rs1], (w >> 20) & 31)
        return '%s %s, %s, %d' % ('sraiw' if (w >> 30) & 1 else 'srliw', R[rd], R[rs1], (w >> 20) & 31)
    if op in (0x33, 0x3b):
        sfx = 'w' if op == 0x3b else ''
        if f7 == 1:
            n = {0: 'mul', 1: 'mulh', 2: 'mulhsu', 3: 'mulhu', 4: 'div', 5: 'divu', 6: 'rem', 7: 'remu'}[f3]
        else:
            n = {0: 'sub' if f7 == 0x20 else 'add', 1: 'sll', 2: 'slt', 3: 'sltu', 4: 'xor',
                 5: 'sra' if f7 == 0x20 else 'srl', 6: 'or', 7: 'and'}[f3]
        return '%s%s %s, %s, %s' % (n, sfx, R[rd], R[rs1], R[rs2])
    return '.word %#x' % w


def writes(w):
    op = w & 0x7f
    return None if op in (0x23, 0x63, 0x0f, 0x73) else (w >> 7) & 31


def main():
    img, twin, out, tag = sys.argv[1:5]
    segs, tsegs = segs_of(img), segs_of(twin)
    syms, name = {}, {}
    for s in ELFFile(open(twin, 'rb')).get_section_by_name('.symtab').iter_symbols():
        if s['st_info']['type'] == 'STT_FUNC' and s.name:
            syms.setdefault(s.name, (s['st_value'], s['st_size']))
            name.setdefault(s['st_value'], s.name)
    lst, traps, s0w = [], [], []
    for f in FUNCS:
        base, size = syms[f]
        lst.append('== %s %#x size %#x' % (f, base, size))
        unimps = [a for a in range(base, base + size, 4) if word(segs, a) == UNIMP]
        for a in range(base, base + size, 4):
            w = word(segs, a)
            if w != word(tsegs, a):
                raise SystemExit('pin and twin differ at %#x' % a)
            t = dis(w, a, name)
            lst.append('  +%#05x %#x %08x %s' % (a - base, a, w, t))
            if target(w, a) in unimps:
                traps.append('%s +%#x %#x %s' % (f, a - base, a, t))
            if f in CTX_FUNCS and writes(w) == 8:
                s0w.append('%s +%#x %#x %s' % (f, a - base, a, t))
        traps.append('%s: unimp at %s' % (f, ', '.join('+%#x %#x' % (u - base, u) for u in unimps) or 'none'))
    open('%s/dis-%s.txt' % (out, tag), 'w').write('\n'.join(lst) + '\n')
    open('%s/ubsan-traps-%s.txt' % (out, tag), 'w').write('\n'.join(traps) + '\n')
    open('%s/s0-writes-%s.txt' % (out, tag), 'w').write('\n'.join(s0w) + '\n')


if __name__ == '__main__':
    main()
