#!/usr/bin/env python3
"""bytecmp.py -- is each function of preset's snprintf chain byte-equal (up to pc-relative fields) to the same-named
function in another image? Words are compared as 32-bit RISC-V instructions (2-byte RVC parcels too if present).
A differing word counts as PC-RELATIVE only when it is auipc (0x17) or jal (0x6f) with the same rd, or an I/S-type word
(addi/ld/sd/jalr/fld/...) that differs ONLY in its immediate (I-type: x & 0x000fffff equal; store: x & 0x01fff07f equal)
whose rs1 is bound to an auipc on EVERY path reaching it (`auipc_states`, a forward MUST analysis over the function's
control-flow graph: no distance window; a run ends at j / jr / ret and at a branch; a binding reaches a branch target
only when every predecessor carries it; a call clobbers the caller-saved registers; a 2-byte parcel clears the state).
A differing I/S-type word that only an INDIRECT jump reaches is UNMEASURED (the verdict then is UNMEASURED, and the
counts are (pcrel, real, unmeasured)). Anything else is a REAL difference. This does NOT resolve targets, so a changed
immediate that keeps its pairing (another offset inside the same symbol) reads as pc-relative: pair it with
repin_check.py's target pass. Prints one row per (image pair, function)."""
import sys, hashlib, os
from elftools.elf.elffile import ELFFile
FNS = ['___interceptor_snprintf', '___interceptor_vsnprintf', 'vsnprintf', 'sn_write', 'vfprintf', 'printf_core',
       'pop_arg', 'pad', 'fmt_fp', 'fmt_x', 'fmt_o', 'fmt_u', 'out', 'getint', 'pad.isra.0']

def load(p):
    e = ELFFile(open(p, 'rb'))
    syms = {}
    for s in e.get_section_by_name('.symtab').iter_symbols():
        if s['st_info']['type'] == 'STT_FUNC' and s['st_size'] > 0 and s.name not in syms:
            syms[s.name] = (s['st_value'], s['st_size'])
    segs = [(g['p_vaddr'], g['p_filesz'], g.data()) for g in e.iter_segments() if g['p_type'] == 'PT_LOAD']
    def rd(a, n):
        for v, fz, d in segs:
            if v <= a and a + n <= v + fz: return d[a - v:a - v + n]
        return None
    return syms, rd

def words(b):
    out, i = [], 0
    while i < len(b):
        lo = b[i] | (b[i + 1] << 8)
        if lo & 3 == 3: out.append((i, int.from_bytes(b[i:i + 4], 'little'), 4)); i += 4
        else: out.append((i, lo, 2)); i += 2
    return out

# Which ops write an integer rd (an FP load/store/op and a store/branch/fence do not), and the caller-saved set a call clobbers.
WRITES_RD = (0x33, 0x3b, 0x13, 0x1b, 0x03, 0x67, 0x6f, 0x37, 0x17, 0x73)
CALLER_SAVED = (1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31)

def auipc_states(ws):
    """For each word index, the auipc bindings (register -> index of the auipc) that hold on EVERY path reaching it.

    A linear scan is wrong in both directions, as two measurements on 2026-10-29 showed: it pairs an auipc with a word that is a
    jump-table case entered from elsewhere (printf_core+0x890: a false differing reference), and it drops a
    binding that a branch target does have, because the FALL-THROUGH path overwrote the register
    (HaveStackTraceBasedSuppressions+0x3c: a false DIFFERENT). So this is a forward MUST analysis over the
    function's own control-flow graph: a word takes the intersection of its predecessors' states, an unreachable word
    (a jump-table case reached only through jalr) gets nothing, and a 2-byte parcel - which this comparer does not
    decode - clears the state.
    """
    n = len(ws)
    succ = [[] for _ in range(n)]
    off = {o: i for i, (o, _, _) in enumerate(ws)}
    for i, (o, x, sz) in enumerate(ws):
        op = x & 0x7f; rd = (x >> 7) & 31
        if sz == 2:
            if i + 1 < n: succ[i].append(i + 1)                      # an RVC jump's state is empty anyway
            continue
        if op == 0x6f:                                                # jal: target, and fall-through only for a call
            t = o + (((x >> 31) << 20) | (((x >> 12) & 0xff) << 12) | (((x >> 20) & 1) << 11) | (((x >> 21) & 0x3ff) << 1))
            t -= (1 << 21) if t - o >= (1 << 20) else 0
            if t in off: succ[i].append(off[t])
            if rd != 0 and i + 1 < n: succ[i].append(i + 1)
        elif op == 0x67:                                              # jalr: a call returns; jr / ret leaves the function
            if rd != 0 and i + 1 < n: succ[i].append(i + 1)
            # An indirect jump's targets are not decoded here. Making every word its successor is sound for a MUST analysis
            # but useless (measured 15:5xZ: 52 of 148 functions then lose every binding). Instead a word that only an
            # indirect jump reaches (a jump-table case) is given the state at the indirect jumps themselves, below.
        elif op == 0x63:                                              # branch: target and fall-through
            t = o + (((x >> 31) << 12) | (((x >> 7) & 1) << 11) | (((x >> 25) & 0x3f) << 5) | (((x >> 8) & 0xf) << 1))
            t -= (1 << 13) if t - o >= (1 << 12) else 0
            if t in off: succ[i].append(off[t])
            if i + 1 < n: succ[i].append(i + 1)
        elif i + 1 < n:
            succ[i].append(i + 1)
    ins = [None] * n; ins[0] = {}
    work = [0]
    while work:
        i = work.pop()
        st = ins[i]
        if st is None: continue
        o, x, sz = ws[i]; op = x & 0x7f; rd = (x >> 7) & 31
        out = {} if sz == 2 else dict(st)
        if sz == 4:
            if op in WRITES_RD: out.pop(rd, None)
            # AMO / LR / SC (0x2f) and the OP-FP words that write an INTEGER rd (funct5 0x14 feq/flt/fle, 0x18 fcvt.w/l,
            # 0x1c fmv.x/fclass) also kill the register, and WRITES_RD missed them (FlowAdopt, 16:3xZ: grant A
            # ScopedErrorReportLock::Lock 0x79120 `lr.d.aqrl a0,(s2)` kept a0 bound to the auipc at 0x79114).
            if op == 0x2f or (op == 0x53 and ((x >> 27) & 31) in (0x14, 0x18, 0x1c)): out.pop(rd, None)
            if op in (0x6f, 0x67) and rd != 0:
                for r in CALLER_SAVED: out.pop(r, None)
            # ecall / ebreak (SYSTEM, funct3 = 0) return a value in a0 (and the kernel may write a1), and rd = 0 there,
            # so the WRITES_RD pop above kills nothing: a binding kept across an ecall was accepted (16:35Z).
            if op == 0x73 and ((x >> 12) & 7) == 0:
                out.pop(10, None); out.pop(11, None)
            if op == 0x17: out[rd] = i
        for s in succ[i]:
            new = out if ins[s] is None else {r: v for r, v in ins[s].items() if out.get(r) == v}
            if ins[s] is None or new != ins[s]:
                ins[s] = new; work.append(s)
    # A word only an indirect jump reaches (a jump-table case) keeps None, and a DIFFERING word there is reported
    # UNMEASURED, to be settled by resolving both targets. The two alternatives were measured (15:5xZ) and rejected:
    # giving the indirect jump every word as a successor loses every binding in 52 of 148 functions, and giving such a
    # word the state at the function's indirect jumps turns printf_core's 11 cases into 'real' differences - a claim this
    # method cannot support (the register may be set inside the case, or the word may not be an address computation).
    return ins

def cmp(b1, b2):
    if len(b1) != len(b2): return 'SIZE %d vs %d' % (len(b1), len(b2)), None
    w1, w2 = words(b1), words(b2)
    if len(w1) != len(w2) or any(a[2] != b[2] for a, b in zip(w1, w2)): return 'SHAPE', None
    pcrel = real = unk = 0; st = auipc_states(w1)
    for i, ((o, x, n), (_, y, _)) in enumerate(zip(w1, w2)):
        if x != y:
            if n == 4 and (x & 0x7f) == (y & 0x7f):
                op = x & 0x7f; rs1 = (x >> 15) & 31
                # Only the IMMEDIATE may differ: everything else (opcode, funct3, rd / rs2, rs1) must be equal, so a changed
                # width or operation is a real difference (16:15Z: `ld a2,0x18c(a2)` -> `lw a2,...`, lbu -> lb,
                # sd -> sw, addi -> andi all passed when only opcode and the registers were compared). I-type: bits 0..19
                # are opcode, rd, funct3, rs1; S-type: bits 0..6 and 12..24 are opcode, funct3, rs1, rs2 (bits 7..11 are
                # imm[4:0], not rd).
                mask = 0x01fff07f if op in (0x23, 0x27) else 0x000fffff
                lo12_shape = op in (0x13, 0x03, 0x23, 0x67, 0x07, 0x27) and (x & mask) == (y & mask)
                if op in (0x17, 0x6f) and ((x >> 7) & 31) == ((y >> 7) & 31): pcrel += 1
                elif lo12_shape and st[i] is not None and rs1 in st[i]: pcrel += 1
                # a word only an indirect jump reaches (a jump-table case): its register's auipc cannot be found here, so
                # the difference is neither proved pc-relative nor proved real - it is UNMEASURED and must be checked by
                # resolving both targets (repin_check.py's target compare does that)
                elif lo12_shape and st[i] is None: unk += 1
                else: real += 1
            else: real += 1
    v = ('EQUAL' if real == 0 and pcrel == 0 and unk == 0 else 'DIFFERENT' if real else
         'UNMEASURED' if unk else 'EQUAL-mod-pcrel')
    return v, (pcrel, real, unk)

base = {'A': os.environ.get('BYTECMP_BASE_A', ''),  # unstripped fuzz_preset.asan of omx-clap-core
        'B': os.environ.get('BYTECMP_BASE_B', '')}  # unstripped fuzz_preset.asan-ubsan of omx-clap-core
others = sys.argv[1:]
print('preset_img\tother\tfn\tpreset_addr\tother_addr\tsize\tverdict\tpcrel\treal')
for img, bp in base.items():
    s1, r1 = load(bp)
    for op in others:
        s2, r2 = load(op)
        tag = op.split('/')[-1] + ':' + hashlib.sha256(open(op, 'rb').read()).hexdigest()[:12]
        for f in FNS:
            if f not in s1: continue
            if f not in s2: print('%s\t%s\t%s\t%#x\t-\t%d\tABSENT\t\t' % (img, tag, f, s1[f][0], s1[f][1])); continue
            v, c = cmp(r1(*s1[f]), r2(*s2[f]))
            print('%s\t%s\t%s\t%#x\t%#x\t%d\t%s\t%s\t%s' % (img, tag, f, s1[f][0], s2[f][0], s1[f][1], v, c[0] if c else '', c[1] if c else ''))
