#!/usr/bin/env python3
"""settle.py -- a named measurement for each target difference of a strictcmp2.py cmp output, beside the kit verdict.

The kit fails closed; a row it reports is settled here only by one of two measurements, each checked on BOTH images,
and is otherwise UNSETTLED:
  bounded-byte-table  a data-differs at an `addi` that forms the address of an unnamed read-only table, where the code
                      reads the table only as `srli rI, rX, S` (index < 2^(64-S)), `add rK, rT, rI`, `lbu rM, 0(rK)`
                      in the next words, and rT and rK are dead after that use (dead_walk): the extent the code reads
                      is 2^(64-S) bytes, compared as file bytes. One-byte entries cannot hold image addresses.
  got-value-zero-test a got-tls / got-value at an 8-byte `ld rd` of a .got cell, where the next word is `beqz rd` /
                      `bnez rd` and rd is dead after it on both successors (dead_walk): the only consumer of the value
                      is the zero test, so equal raw cell values are the same datum. Prints the PT_TLS headers.
dead_walk follows every path over the function's words: a write of the register ends a path; a read, an RVC control
transfer, a target outside the function or falling off its end fails; a call / return ends a path only for t0-t6.
Words come from the kit's bytecmp (bc_words), targets from the kit's `targets`, bytes from strictcmp2's frd (file bytes
only); disassembly text from capstone. Output: one TSV row per difference.
Usage: settle.py KIT_DIR OUT.tsv"""
import ast, importlib.util, os, sys
import capstone

KIT, OUT = sys.argv[1:3]
sp = importlib.util.spec_from_file_location('strictcmp2_kit', os.path.join(KIT, 'strictcmp2.py'))
S = importlib.util.module_from_spec(sp); sp.loader.exec_module(S)
MD = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)
REGS = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
        's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
STORE = ('sb', 'sh', 'sw', 'sd', 'fsw', 'fsd', 'c.sw', 'c.sd', 'c.swsp', 'c.sdsp', 'c.fsd', 'c.fsdsp')
TWO_ADDR = ('c.addi', 'c.addiw', 'c.slli', 'c.srli', 'c.srai', 'c.andi', 'c.add', 'c.sub', 'c.xor', 'c.or', 'c.and',
            'c.subw', 'c.addw', 'c.addi16sp')
JUMP = ('j', 'jal', 'jr', 'jalr', 'ret', 'c.j', 'c.jal', 'c.jr', 'c.jalr', 'tail', 'call')


def dis(b, a):
    i = next(MD.disasm(b, a), None)
    return (i.mnemonic, i.op_str) if i else ('?', b.hex())


def regs_of(op):
    return [t.strip().split('(')[-1].rstrip(')') for t in op.split(',')]


def reads_writes(mn, op):
    """(registers read, registers written, is control transfer) of one instruction, from its assembly text"""
    r = [x for x in regs_of(op) if x in REGS]
    if mn in STORE: return set(r), set(), False
    if mn.startswith('b') or mn in ('c.beqz', 'c.bnez'): return set(r), set(), True
    if mn in JUMP: return set(r), set(), True
    if not r: return set(), set(), False
    if mn in TWO_ADDR: return set(r), {r[0]}, False
    return set(r[1:]), {r[0]}, False


def fields(x):
    return x & 0x7f, (x >> 7) & 31, (x >> 12) & 7, (x >> 15) & 31, (x >> 20) & 31


def bimm(x):
    return S._g['sx'](((x >> 31) & 1) << 12 | ((x >> 7) & 1) << 11 | ((x >> 25) & 0x3f) << 5 | ((x >> 8) & 0xf) << 1, 13)


def jimm(x):
    return S._g['sx'](((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11 | ((x >> 21) & 0x3ff) << 1, 21)


def wtext(a, b, o, nb, x):
    mn, opnd = dis(b[o:o + nb], a + o)
    t = 'pc %#x (+%#x) %s %s' % (a + o, o, mn, opnd)
    if nb == 4 and x & 0x7f == 0x63: t += ' -> pc %#x (+%#x)' % (a + o + bimm(x), o + bimm(x))
    if nb == 4 and x & 0x7f == 0x6f: t += ' -> pc %#x (+%#x)' % (a + o + jimm(x), o + jimm(x))
    return t


BUILTIN = 'bcahstijlmxy'    # Itanium builtin integer / bool / char parameter codes: one integer argument register each


def int_args(name):
    """the number of integer argument registers of a callee from its mangled name, or None when the name does not fix
    it: only `_Z[L]<len><id><params>` (a global function) and `_ZN<len><id>...L<len><id>E<params>` whose LAST component
    has internal linkage `L` (a namespace-scope function, so no implicit `this`), with parameters all builtin integer
    codes, or `v`"""
    def comp(s, i):
        j = i
        while j < len(s) and s[j].isdigit(): j += 1
        if j == i: return None, i
        n = int(s[i:j])
        return (s[j:j + n], j + n) if j + n <= len(s) else (None, i)
    if not name.startswith('_Z'): return None
    i = 2
    if name[i:i + 1] == 'N':
        i += 1; last_l = False
        while i < len(name) and name[i] != 'E':
            last_l = name[i] == 'L'
            if last_l: i += 1
            c, i2 = comp(name, i)
            if c is None: return None
            i = i2
        if i >= len(name) or not last_l: return None
        i += 1
    else:
        if name[i:i + 1] == 'L': i += 1
        c, i = comp(name, i)
        if c is None: return None
    rest = name[i:]
    if rest == 'v': return 0
    return len(rest) if rest and all(ch in BUILTIN for ch in rest) else None


def dead_walk(I, a, b, w, starts, rname):
    """-> (ok, text): every path from the word offsets `starts` is walked over the function's words. A read of rname is
    a failure; a write of rname ends the path; a 32-bit branch forks, a 32-bit `j` follows its target, a word seen before
    ends the path. RISC-V psABI: t0-t6 and a0-a7 are caller-saved, a0-a7 carry the integer arguments and a0 / a1 the
    return value. So a call (jal / jalr with rd = ra) ends the path when rname is one of t0-t6, or is a_i and the callee
    is named (the kit's qres, offset 0) by a mangled non-member name whose builtin parameters fill fewer than i + 1
    argument registers (int_args); a `ret` ends it when rname is t0-t6 or a2-a7; another jalr with rd = zero only for
    t0-t6. An RVC control transfer, a target outside the function or falling off its end is a failure."""
    temp = rname in ('t0', 't1', 't2', 't3', 't4', 't5', 't6')
    argi = int(rname[1:]) if rname in ('a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7') else None
    offs = {o2: i for i, (o2, _, _) in enumerate(w)}
    todo, seen, ends, path = list(reversed(starts)), set(), [], []
    while todo:
        o2 = todo.pop()
        if o2 in seen: continue
        if o2 not in offs: return False, '+%#x: not a word start of the function' % o2
        seen.add(o2)
        _, x2, nb = w[offs[o2]]
        mn, opnd = dis(b[o2:o2 + nb], a + o2)
        rr, ww, ct = reads_writes(mn, opnd)
        here = wtext(a, b, o2, nb, x2)
        path.append(here)
        if rname in rr: return False, '%s reads %s' % (here, rname)
        if rname in ww: ends.append('%s writes %s' % (here, rname)); continue
        if nb != 4:
            if ct: return False, '%s: RVC control transfer' % here
            todo.append(o2 + nb); continue
        op2, rd2, _, rs1, _ = fields(x2)
        if op2 == 0x63:
            todo += [o2 + bimm(x2), o2 + 4]
        elif op2 == 0x6f and rd2 == 0:
            todo.append(o2 + jimm(x2))
        elif op2 in (0x6f, 0x67) and rd2 == 1:
            if temp:
                ends.append('%s call (%s caller-saved, never an argument)' % (here, rname)); continue
            callee = S.qres(I, a + o2 + jimm(x2)) if op2 == 0x6f else None
            k = int_args(callee[:-4]) if argi is not None and callee and callee.endswith('+0x0') else None
            if k is None or argi < k: return False, '%s: call with %s live (callee %s)' % (here, rname, callee)
            ends.append('%s call to %s: %d integer argument register(s), so %s is no argument and is caller-saved'
                        % (here, callee, k, rname))
        elif op2 == 0x67 and rd2 == 0:
            if temp or (argi is not None and argi >= 2 and rs1 == 1 and (x2 >> 20) == 0):
                ends.append('%s return / indirect jump (%s caller-saved, not a return register)' % (here, rname)); continue
            return False, '%s: return / indirect jump with %s live' % (here, rname)
        elif op2 in (0x6f, 0x67):
            return False, '%s: jump with link register %s' % (here, REGS[rd2])
        else:
            todo.append(o2 + 4)
    return True, '%s dead: walk of %d words in walk order [%s]; every path ends: %s' % (
        rname, len(seen), ' | '.join(path), '; '.join(ends))


def bounded_byte_table(I, a, b, w, k):
    """-> (ok, extent, text). The address register of the addi and the sum register must be dead after their one use
    (dead_walk), so the lbu is the only read of the table through this target word."""
    op, rd, f3, rs1, _ = fields(w[k][1])
    if w[k][2] != 4 or op != 0x13 or f3 != 0: return False, None, 'target word is not addi'
    sh = [j for j in range(max(0, k - 6), k) if w[j][2] == 4 and fields(w[j][1])[0] == 0x13 and fields(w[j][1])[2] == 5
          and (w[j][1] >> 26) == 0]
    if not sh: return False, None, 'no srli in the 6 words before'
    j = sh[-1]; ri = fields(w[j][1])[1]; s = (w[j][1] >> 20) & 63
    if k + 3 >= len(w) or w[k + 1][2] != 4 or w[k + 2][2] != 4: return False, None, 'next words are not 32-bit'
    o1, r1, f31, a1, a2 = fields(w[k + 1][1])
    o2, r2, f32, b1, _ = fields(w[k + 2][1])
    if not (o1 == 0x33 and f31 == 0 and (w[k + 1][1] >> 25) == 0 and {a1, a2} == {rd, ri}):
        return False, None, 'word +1 is not add of the table address and the index'
    if not (o2 == 0x03 and f32 == 4 and b1 == r1 and (w[k + 2][1] >> 20) == 0):
        return False, None, 'word +2 is not lbu 0 from the sum'
    for j2 in range(j + 1, k):
        if w[j2][2] != 4 or (fields(w[j2][1])[1] == ri and fields(w[j2][1])[0] not in (0x23, 0x63)):
            return False, None, 'index register rewritten between srli and add'
    txt = ['; '.join(wtext(a, b, w[x][0], w[x][2], w[x][1]) for x in (j, k, k + 1, k + 2))]
    if r1 != rd:
        ok, t = dead_walk(I, a, b, w, [w[k + 2][0]], REGS[rd])
        if not ok: return False, None, 'table address register: ' + t
        txt.append('table address register ' + t)
    if r2 != r1:
        ok, t = dead_walk(I, a, b, w, [w[k + 3][0]], REGS[r1])
        if not ok: return False, None, 'sum register: ' + t
        txt.append('sum register ' + t)
    else:
        txt.append('sum register %s is overwritten by the lbu itself' % REGS[r1])
    return True, 1 << (64 - s), '; '.join(txt)


def got_zero_test(I, a, b, w, k):
    """-> (ok, text): the ld's register is consumed by the zero test, then dead on every path (dead_walk)."""
    op, rd, f3, _, _ = fields(w[k][1])
    if w[k][2] != 4 or op != 0x03 or f3 != 3: return False, 'target word is not ld'
    if k + 1 >= len(w) or w[k + 1][2] != 4: return False, 'next word is not 32-bit'
    x = w[k + 1][1]; o, _, f, r1, r2 = fields(x)
    if not (o == 0x63 and f in (0, 1) and r1 == rd and r2 == 0): return False, 'next word is not beqz / bnez of rd'
    ok, t = dead_walk(I, a, b, w, [w[k + 1][0] + 4, w[k + 1][0] + bimm(x)], REGS[rd])
    if not ok: return False, t
    return True, '%s; zero test %s; after it, from both successors: %s' % (
        wtext(a, b, w[k][0], 4, w[k][1]), wtext(a, b, w[k + 1][0], 4, x), t)


def tls_hdr(I):
    return ', '.join('PT_TLS p_offset %#x p_vaddr %#x p_filesz %d p_memsz %d p_align %d p_flags %d'
                     % (g['p_offset'], g['p_vaddr'], g['p_filesz'], g['p_memsz'], g['p_align'], g['p_flags'])
                     for g in I.e.iter_segments() if g['p_type'] == 'PT_TLS') or 'no PT_TLS'

RULE = {
    'bounded-byte-table': 'extent the code reads: the table is read only by lbu (1 byte) at table + (x >> S), so the '
                          'index is below 2^(64-S) and the extent is 2^(64-S) bytes; the table address and the sum '
                          'registers are dead after that one use on every path (walks below; a call ends a path only '
                          'when the callee\'s mangled name shows the register is no argument); those file bytes are '
                          'compared on both sides (1-byte entries hold no image address); no FUNC / OBJECT symbol '
                          'starts inside',
    'got-value-zero-test': 'extent the code reads: the 8-byte .got cell the ld reads, compared as a raw value; its only '
                           'consumer is the zero test: on every path after it the register is written before any read, '
                           'or the path ends at a call (psABI: t0-t6 are caller-saved, no argument or return '
                           'register); the kit differs only in naming a value inside PT_TLS (the cgif twin holds no '
                           'STT_TLS symbol)',
    'none': 'no measurement applies; not settled'}

def main():
    imgs = {}
    for line in open(OUT):
        if line.startswith('# ') and ' = ' in line and ' sha256 ' in line:
            k, rest = line[2:].split(' = ', 1)
            imgs[k] = rest.rsplit(' sha256 ', 1)[0]
    I = {k: S.Img(p) for k, p in imgs.items()}
    ids = {k: '%s sha256 %s' % (os.path.basename(p), S.sha(p)) for k, p in imgs.items()}
    print('pair\timage 1\timage 2\tfn\taddr1\taddr2\tword\tkit verdict\tkit kind\tkit detail\tmeasurement\trule\tside 1\t'
          'side 2\tsettled')
    for line in open(OUT):
        c = line.rstrip('\n').split('\t')
        if line.startswith(('#', 'fn\t', 'CSTR\t')) or len(c) < 12 or c[11] == '0':
            continue
        fn, pair = c[0], c[1]; k1, k2 = pair.split(':'); a1, a2, n = int(c[2], 16), int(c[3], 16), int(c[4])
        nd = len(ast.literal_eval(c[11]))
        head = [pair, ids[k1], ids[k2], fn, hex(a1), hex(a2)]
        sides = []
        for kk, aa in ((k1, a1), (k2, a2)):
            b = S.frd(I[kk], aa, n); w = S.bc_words(b); t = S.targets(aa, b)
            sides.append((I[kk], aa, b, w, t))
        for off, r1, r2, kind, info in ast.literal_eval(c[11]):
            o = int(off, 16)
            ks = [next((i for i, (oo, _, _) in enumerate(sd[3]) if oo == o), None) for sd in sides]
            res = []
            if kind == 'data-differs' and None not in ks:
                ms = [bounded_byte_table(sd[0], sd[1], sd[2], sd[3], kx) for sd, kx in zip(sides, ks)]
                xs = [sd[4][kx][1] for sd, kx in zip(sides, ks)]
                if all(m[0] for m in ms) and ms[0][1] == ms[1][1]:
                    n2 = ms[0][1]
                    d = [S.frd(sd[0], x, n2) for sd, x in zip(sides, xs)]
                    secs = [sd[0].sec(x) for sd, x in zip(sides, xs)]
                    inner = [[nm for v, z, nm, ty in sd[0].syms if x < v < x + n2 and ty in ('STT_FUNC', 'STT_OBJECT')]
                             for sd, x in zip(sides, xs)]
                    ok = None not in d and d[0] == d[1] and secs[0] == secs[1] and not inner[0] and not inner[1]
                    for sd, x, m, dd, sc, inn in zip(sides, xs, ms, d, secs, inner):
                        res.append('%s; table %#x in %s, %d entries x 1 byte, no FUNC/OBJECT symbol inside: %s; bytes %s'
                                   % (m[2], x, sc, n2, not inn, dd.hex() if dd else 'not file bytes'))
                    print('\t'.join(head + [off, 'NOT-SAME (%s, target-differ %d)' % (c[6], nd), kind, '%s | %s' % (r1, r2), 'bounded-byte-table', RULE['bounded-byte-table'],
                                     res[0], res[1], 'SAME (%d bytes equal)' % n2 if ok else 'DIFFERENT (bytes differ)']))
                    continue
                res = [m[2] for m in ms]
            elif kind in ('got-tls', 'got-value') and None not in ks:
                ms = [got_zero_test(sd[0], sd[1], sd[2], sd[3], kx) for sd, kx in zip(sides, ks)]
                cells = [sd[4][kx][1] for sd, kx in zip(sides, ks)]
                vals = [S.frd(sd[0], cl, 8) for sd, cl in zip(sides, cells)]
                if all(m[0] for m in ms) and None not in vals:
                    ok = vals[0] == vals[1]
                    for sd, cl, v, m in zip(sides, cells, vals, ms):
                        res.append('%s; ld reads cell %#x (%s), 8 file bytes %s = value %#x; %s'
                                   % (m[1], cl, sd[0].sec(cl), v.hex(), int.from_bytes(v, 'little'), tls_hdr(sd[0])))
                    print('\t'.join(head + [off, 'NOT-SAME (%s, target-differ %d)' % (c[6], nd), kind, '%s | %s' % (r1, r2), 'got-value-zero-test', RULE['got-value-zero-test'],
                                     res[0], res[1], 'SAME (equal raw value, zero test only)' if ok else 'DIFFERENT (values differ)']))
                    continue
                res = [m[1] for m in ms]
            print('\t'.join(head + [off, 'NOT-SAME (%s, target-differ %d)' % (c[6], nd), kind, '%s | %s | %r' % (r1, r2, info), 'none', RULE['none'],
                             res[0] if res else '-', res[1] if len(res) > 1 else '-', 'UNSETTLED']))


if __name__ == '__main__':
    main()
