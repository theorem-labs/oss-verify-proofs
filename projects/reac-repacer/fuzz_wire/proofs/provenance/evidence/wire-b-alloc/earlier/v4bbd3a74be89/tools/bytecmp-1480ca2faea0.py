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

# ---- insnflow block begin. The same bytes as insnflow a36c2b82eb44 (tools/insnflow/a36c2b82eb44/insnflow.py, tool
# registry commit 797e8971d27d) apart from comments. symreloc.py and elfdis.py CARRY this block instead of importing it, so that a tool's sha fixes its
# behaviour and a tool copied alone still runs. From bytecmp 475ff6314d3c (`words`, `auipc_states`) so the comparers
# agree; changed: WRITES_RD (AMO, OP-FP to an integer rd), an auipc to x0 binds nothing, and a word that only an indirect
# jump reaches is a block entry with every register UNKNOWN (flow_states) instead of a word with no state.
def words(b):
    out, i = [], 0
    while i < len(b):
        lo = b[i] | (b[i + 1] << 8)
        if lo & 3 == 3: out.append((i, int.from_bytes(b[i:i + 4], 'little'), 4)); i += 4
        else: out.append((i, lo, 2)); i += 2
    return out

# Which ops write an integer rd (an FP load/store and a store/branch/fence do not), and the caller-saved set a call clobbers.
# 0x2f (AMO / LR / SC) writes rd. OP-FP (0x53) writes an INTEGER rd only for feq / flt / fle (funct5 0x14), fcvt to an
# integer (0x18) and fmv.x / fclass (0x1c); any other OP-FP word writes an FP register (bytecmp 475ff6314d3c lacked both:
# it kept a0 bound across `lr.d.aqrl a0,(s2)` in fuzz_grant's ScopedErrorReportLock::Lock and `flt.d a0,fa0,fa5` in
# fuzz_disco's reac_rate_snap).
WRITES_RD = (0x33, 0x3b, 0x13, 0x1b, 0x03, 0x67, 0x6f, 0x37, 0x17, 0x73, 0x2f)
FP_WRITES_XRD = (0x14, 0x18, 0x1c)
CALLER_SAVED = (1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31)
UNKNOWN = -1   # a register whose value is unknown: some path into the word enters through an indirect jump

def _meet(a, b):
    """Meet of two states: a binding both sides agree on stays; UNKNOWN on either side gives UNKNOWN; anything else (two
    different auipcs, or bound on one side and unbound on the other) is unbound, i.e. left out."""
    out = {}
    for r in a.keys() | b.keys():
        x, y = a.get(r), b.get(r)
        if x == y: out[r] = x
        elif x == UNKNOWN or y == UNKNOWN: out[r] = UNKNOWN
    return out

def flow_states(ws):
    """For each word index, a dict: register -> index of the auipc whose result it holds on EVERY path reaching the word,
    or register -> UNKNOWN; a register that is left out holds no auipc result on some path (unbound). Never None.

    A linear scan is wrong in both directions, as two measurements on 2026-10-29 showed: it pairs an auipc with a word that is a
    jump-table case entered from elsewhere (printf_core+0x890: a false differing reference), and it drops a
    binding that a branch target does have, because the FALL-THROUGH path overwrote the register
    (HaveStackTraceBasedSuppressions+0x3c: a false DIFFERENT). So this is a forward MUST analysis over the
    function's own control-flow graph: a word takes the meet of its predecessors' states (_meet), and a 2-byte parcel -
    which this comparer does not decode - clears the state. Successors: the next word; a jal's in-function target (plus
    the next word only for a call); a branch's target and the next word; none for jr / ret. A call clobbers the
    caller-saved registers; an ecall / ebreak drops a0 and a1. The entry word starts with every register unbound. A word
    that no decoded edge reaches (a jump-table case, entered through jalr) is a block entry with every register but x0
    UNKNOWN, so an auipc inside the case still pairs with its consumer (fuzz_grant ErrorGeneric `+0x238 auipc a1;
    +0x23c addi s2,a1,-0x458`), while a consumer whose base was set before the indirect jump reads UNKNOWN: a differing
    one is UNMEASURED, never pc-relative and never real. Words with no predecessor at all are seeded first, then any
    word still unreached (a cycle of such words), lowest index first. KNOWN LIMIT: a case word that ALSO has a decoded
    predecessor takes its state from the decoded edges only, as in bytecmp. ws must not be empty.
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
            # but useless (measured: 52 of 148 functions then lose every binding). A word that only an indirect
            # jump reaches (a jump-table case) is instead a block entry where every register is UNKNOWN, below.
        elif op == 0x63:                                              # branch: target and fall-through
            t = o + (((x >> 31) << 12) | (((x >> 7) & 1) << 11) | (((x >> 25) & 0x3f) << 5) | (((x >> 8) & 0xf) << 1))
            t -= (1 << 13) if t - o >= (1 << 12) else 0
            if t in off: succ[i].append(off[t])
            if i + 1 < n: succ[i].append(i + 1)
        elif i + 1 < n:
            succ[i].append(i + 1)
    ins = [None] * n; ins[0] = {}
    work = [0]
    has_pred = [False] * n
    for s in succ:
        for t in s: has_pred[t] = True
    roots = [k for k in range(1, n) if not has_pred[k]]
    while True:
        while work:
            i = work.pop()
            o, x, sz = ws[i]; op = x & 0x7f; rd = (x >> 7) & 31
            out = {} if sz == 2 else dict(ins[i])
            if sz == 4:
                if op in WRITES_RD or (op == 0x53 and (x >> 27) in FP_WRITES_XRD): out.pop(rd, None)
                if op in (0x6f, 0x67) and rd != 0:
                    for r in CALLER_SAVED: out.pop(r, None)
                # ecall / ebreak (SYSTEM, funct3 = 0) return a value in a0 (and the kernel may write a1), and rd = 0 there,
                # so the WRITES_RD pop above kills nothing: a binding kept across an ecall was accepted.
                if op == 0x73 and ((x >> 12) & 7) == 0:
                    out.pop(10, None); out.pop(11, None)
                if op == 0x17 and rd != 0: out[rd] = i
            for s in succ[i]:
                new = out if ins[s] is None else _meet(ins[s], out)
                if ins[s] is None or new != ins[s]:
                    ins[s] = new; work.append(s)
        seed = [k for k in roots if ins[k] is None] or [k for k in range(n) if ins[k] is None][:1]
        if not seed:
            return ins
        for k in seed:
            ins[k] = dict.fromkeys(range(1, 32), UNKNOWN); work.append(k)

def auipc_states(ws):
    """flow_states with the UNKNOWN registers left out: per word, register -> auipc index of the BOUND registers only, the
    shape bytecmp's cmp() was written for (but never None now). A consumer that tests `rs1 in st[i]` on it reads an
    unknown base as unbound - a difference, never a pairing; use flow_states to tell UNKNOWN apart (UNMEASURED)."""
    return [{r: j for r, j in s.items() if j != UNKNOWN} for s in flow_states(ws)]
# ---- insnflow block end

def cmp(b1, b2):
    if len(b1) != len(b2): return 'SIZE %d vs %d' % (len(b1), len(b2)), None
    w1, w2 = words(b1), words(b2)
    if len(w1) != len(w2) or any(a[2] != b[2] for a, b in zip(w1, w2)): return 'SHAPE', None
    pcrel = real = unk = 0; st = flow_states(w1)
    for i, ((o, x, n), (_, y, _)) in enumerate(zip(w1, w2)):
        if x != y:
            if n == 4 and (x & 0x7f) == (y & 0x7f):
                op = x & 0x7f; rs1 = (x >> 15) & 31
                # Only the IMMEDIATE may differ: everything else (opcode, funct3, rd / rs2, rs1) must be equal, so a changed
                # width or operation is a real difference (`ld a2,0x18c(a2)` -> `lw a2,...`, lbu -> lb,
                # sd -> sw, addi -> andi all passed when only opcode and the registers were compared). I-type: bits 0..19
                # are opcode, rd, funct3, rs1; S-type: bits 0..6 and 12..24 are opcode, funct3, rs1, rs2 (bits 7..11 are
                # imm[4:0], not rd).
                mask = 0x01fff07f if op in (0x23, 0x27) else 0x000fffff
                lo12_shape = op in (0x13, 0x03, 0x23, 0x67, 0x07, 0x27) and (x & mask) == (y & mask)
                j = st[i].get(rs1)
                if op in (0x17, 0x6f) and ((x >> 7) & 31) == ((y >> 7) & 31): pcrel += 1
                elif lo12_shape and j is not None and j >= 0: pcrel += 1
                # a word only an indirect jump reaches (a jump-table case): its register's auipc cannot be found here, so
                # the difference is neither proved pc-relative nor proved real - it is UNMEASURED and must be checked by
                # resolving both targets (repin_check.py's target compare does that)
                elif lo12_shape and j == UNKNOWN: unk += 1
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
