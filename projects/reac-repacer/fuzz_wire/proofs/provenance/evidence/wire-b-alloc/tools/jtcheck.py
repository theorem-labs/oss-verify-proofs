#!/usr/bin/env python3
"""jtcheck.py -- settle the functions a byte compare leaves UNMEASURED or 'target-differ' (jump tables). Read-only.

Loads the comparison kit beside it; named here are the kit originals, the pins below are set to this record's copies:
  strictcmp3.py 65688e94214a  -> `tsame`, the target rule of record (and qres / region / frd / cstr_rows), which loads
  drvcmp.py     4d70e90bc1fa  -> class Img = repin_check 4c05cadaeba3 lines 31-80, targets / sx / w_off lines 209-231,
                                 bytecmp 1480ca2faea0 (drvcmp checks those two itself).

For a same-named, same-size function in images X and Y whose words differ only in immediates:
 1. PAIRS: every lo12 word (addi / loads / stores / jalr) is paired with the auipc that wrote its base, by bytecmp's MUST
    dataflow, else - only in a function with no 2-byte parcel - with the nearest earlier auipc in the same basic block.
    UNPAIRED (settles nothing): a differing word that cannot be paired; a word that cannot be paired whose base register
    was last written, in address order, by an auipc, equal or not; an auipc that no pair consumes. A differing word of
    any other shape (a branch, another opcode, a 2-byte parcel) is a REAL difference and stops the function.
 2. EVERY TARGET PAIR - each lo12 pair and each jal - is judged first by strictcmp3's `tsame`, the rule of record:
    qualified names (a duplicated name by its STT_FILE; exact-address names for size-0 / NOTYPE symbols such as
    `dlsym`), a name on one side only or two different names = a difference with no content compare; .got cells by
    what they hold (a pointer by name; a value raw, inside PT_TLS also by its STT_TLS symbol; an address-taken cell as a
    general-dynamic tls_index); unnamed code = a difference; unnamed writable data outside PT_GNU_RELRO = a difference;
    unnamed read-only data by the bytes a load reads, else the C-STRING RULE (the pool owner's option B: bytes before
    the first NUL all printable and that NUL inside the region -> the C string INCLUDING its NUL), else the full region
    to the next FUNC / OBJECT start; every content read on FILE bytes only (never the loader's zero-fill).
 3. ON TOP of tsame, only where it refuses an unnamed .rodata / .data.rel.ro target:
    a. a TABLE, and only when the function REALLY DISPATCHES THROUGH ONE and the entry count is PROVEN ON EVERY PATH
       (`Flow.prove`, the CFG reaching-definitions rule below): the base the lo12 word forms reaches an `add` /
       `sh{1,2,3}add` with an index scaled by the entry size, a load of that size reads the entry at offset 0 from it,
       and a compare on that index bounds it on EVERY path into the load. The base must be aligned to the entry size,
       the entry size 4 or 8, the count >= 2, and X and Y must prove the SAME count. Exactly that many entries are then
       read: a jump table (the X entry points into the X function, absolute or relative to the base) is compared as
       function-relative offsets; else 8-byte entries as pointers (the same qualified symbol+offset, or equal bytes)
       and 4-byte entries as values (equal bytes). A bound check ALONE is not a table: a verbosity test
       `addi a1,zero,2; bgeu` beside a string used to be read as a 2-entry table, and a jump table's own bound used to
       be reused for a nearby string (83 / 129 / 5 entries).
    b. an INITIALIZER, and only when a MEMCPY-FAMILY call reads the whole object: `addi a2,zero,L` then a `jal ra`
       whose callee resolves to memcpy / memmove / mempcpy (so it reads exactly L bytes), AND the unnamed region is
       exactly L bytes on both sides. `internal_strncpy(dst, "", 16)` stops at the source's NUL, so its 16 is a bound,
       not an extent; such a copy length is refused.
    c. UNMEASURED in place of tsame's 'data-differs' for an address-taken target whose two regions (to the next FUNC /
       OBJECT start) are not equally long: the object's extent is not in the symbol table, so jtcheck cannot say.
    Anything that fails these tests is left to tsame, which fails closed (the C-string rule, else the whole region).
 4. A function name that several sized FUNC symbols carry in either image is SKIPped unless given as name{file}.
 OUTPUT: one line per function (lo12 pairs, jal, target differs, target unmeasured, unpaired, C-string acceptances,
 tables), then DIFF / UNMEASURED / UNPAIRED lines, ACCEPT lines for every acceptance that is not a name, and one CSTR
 row per C-string acceptance in strictcmp3's format (function, pair, word offset, addr1, addr2, length, hex, repr).
 Settled = target differs, target unmeasured, unpaired and REAL all 0.
usage: [STRICT_LITERAL=1] jtcheck.py X_ELF Y_ELF fn1,fn2{file},...   (strictcmp3.py, drvcmp.py,
       repin_check-4c05cadaeba3.py, bytecmp-1480ca2faea0.py beside it; X_ELF and Y_ELF carry .symtab)"""
import sys, os, re, hashlib
import importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
for _f, _want in (('strictcmp3.py', 'b553126fa2247d965b16c4f3f6008319d6355b49146b666e36fe51c3dda3cd55'),
                  ('drvcmp.py', '2fffab5c772f21d1c84a0fc3b70283afa415f657e401d9cb1b92c38b0fcf9a5d')):
    _got = hashlib.sha256(open(os.path.join(HERE, _f), 'rb').read()).hexdigest()
    if _got != _want: raise SystemExit('jtcheck.py: %s has sha256 %s, want %s' % (_f, _got, _want))
spec = importlib.util.spec_from_file_location('strictcmp3', os.path.join(HERE, 'strictcmp3.py'))
dc = importlib.util.module_from_spec(spec); spec.loader.exec_module(dc)
Img, bc_words, sx = dc.Img, dc.bc_words, dc._g['sx']
WRITES_RD = dc._bc['WRITES_RD']
X, Y = Img(sys.argv[1]), Img(sys.argv[2])
# CONTROL SCAFFOLDING IS NEVER A VERDICT OF RECORD. The controls run on copies of their two images in which the
# loop recurrences of three unplanted functions are `nop` (controls/host.py, the README's "host patch"): those
# recurrences hold value sets no cap enumerates, so this version seeds them and refuses the functions, and
# without the patch every control planted there would be refused for the host's reason. An input that carries
# the patch IN ANY NO-OP ENCODING - every listed word of one of those functions an instruction whose only effect
# is a write to x0 (the canonical nop, any base HINT, or two compressed no-op / HINT parcels), which no compiled
# function has - is refused, unless JTCHECK_SCAFFOLD=1. Then a banner line says so AND every function row
# carries the marker first in its table list, the one field every harness of the controls keeps.
SCAFFOLD = {
    '_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE20parseFDEInstructionsERS1_RKNS2_8FDE_InfoERKNS2_8CIE_InfoEmi'
    'PNS2_10PrologInfoE': (0xd8, 0x198, 0x1a8, 0x258, 0x268, 0x53c, 0x54c, 0x9c4, 0x9d4),
    '_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE8parseCIEERS1_mPNS2_8CIE_InfoE': (0x188, 0x198, 0x19c),
    '_ZN9libunwind17DwarfInstructionsINS_17LocalAddressSpaceENS_15Registers_riscvEE18evaluateExpressionEmRS1_RKS2_m':
        (0xcc, 0xdc, 0x210, 0x220, 0x2f0, 0x300)}
SCAFFOLD_MARK = 'SCAFFOLD INPUT - NOT a verdict of record'
def _noop32(x):
    """a 32-bit word whose only effect is a write to x0: the canonical nop and every base HINT - an integer ALU
    instruction (OP-IMM, OP, OP-IMM-32, OP-32), LUI or AUIPC with rd = x0 - or a FENCE with no predecessor or
    no successor set"""
    op = x & 0x7f
    if op in (0x13, 0x1b, 0x33, 0x3b, 0x37, 0x17): return ((x >> 7) & 31) == 0
    return op == 0x0f and ((x >> 12) & 7) == 0 and (((x >> 20) & 15) == 0 or ((x >> 24) & 15) == 0)
def _noop16(h):
    """a compressed parcel that only writes x0 or writes a register with its own value: C.NOP and the RVC HINTs -
    C.ADDI with rd x0 or imm 0, C.LI / C.LUI with rd x0, C.SLLI with rd x0 or shift 0, C.SRLI / C.SRAI with
    shift 0, C.MV / C.ADD with rd x0"""
    q, f3, rd = h & 3, h >> 13, (h >> 7) & 31
    imm = ((h >> 12) & 1) << 5 | ((h >> 2) & 31)
    if q == 1:
        if f3 == 0: return rd == 0 or imm == 0
        if f3 in (2, 3): return rd == 0
        if f3 == 4: return ((h >> 10) & 3) in (0, 1) and imm == 0
    if q == 2:
        if f3 == 0: return rd == 0 or imm == 0
        if f3 == 4 and (h >> 2) & 31: return rd == 0
    return False
def _noop(b):
    """4 bytes that do nothing: one 32-bit no-op, or two compressed ones"""
    x = int.from_bytes(b, 'little')
    if x & 3 == 3: return _noop32(x)
    return (x >> 16) & 3 != 3 and _noop16(x & 0xffff) and _noop16(x >> 16)
def scaffold(I):
    """the control function whose host-patch words are ALL no-ops in image I, else None"""
    for fn, offs in SCAFFOLD.items():
        s = I.fsym(fn)
        if not s or isinstance(s, str): continue
        b = dc.frd(I, s[0], s[1])
        if b and all(len(b) >= o + 4 and _noop(b[o:o + 4]) for o in offs): return fn
    return None
_sc = []
if X is not None:
    _sc = [os.path.basename(p) for p, I in ((sys.argv[1], X), (sys.argv[2], Y)) if scaffold(I)]
    if _sc and os.environ.get('JTCHECK_SCAFFOLD') != '1':
        raise SystemExit('jtcheck.py: the controls\' host patch is in %s; no verdict is given on a scaffold image'
                         % ', '.join(_sc))
    if _sc: print('# %s: %s (control use only)' % (SCAFFOLD_MARK, ', '.join(_sc)))
LO12 = (0x13, 0x03, 0x23, 0x67, 0x07, 0x27)

def qname_ok(vx, vy, ex, ey):
    """an 8-byte table entry / initializer word: equal file bytes, or both addresses (inside a section) of the same
    qualified symbol+offset (never an unnamed one)"""
    if ex == ey: return True
    if len(ex) < 8 or X.sec(vx) is None or Y.sec(vy) is None: return False
    rx, ry = dc.qres(X, vx), dc.qres(Y, vy)
    return rx is not None and rx == ry and not rx.startswith('(')

LOADW = {0: 1, 1: 2, 2: 4, 3: 8, 4: 1, 5: 2, 6: 4}      # funct3 of an integer load -> width
MEMCPY = ('memcpy', 'memmove', 'mempcpy')               # an exact-length copy; str* copies stop at a NUL

# ---------------------------------------------------------------------------------------------------------------
# THE BOUND RULE: a CFG with reaching definitions over the whole function.
#
# A table's entry count is the constant c such that EVERY definition of the bound register that REACHES the guard
# compare is the same `addi rK, zero, c` - over the real control-flow graph, with the value followed through
# register copies and through 8-byte stack slots (a spill and its reload). A definition on a path that never
# reaches the guard (a stack restore on an exit path, a reload under an abort) does not count, and a loop head
# between the constant and the guard does not matter: both defeated the address-order rule this version replaces.
# THE GRAPH holds every control transfer the BYTES fix: both edges of every branch, every in-function jump, every
# arm of every jump table, and a call to a word of this function - direct (`jal rd`), or through a register when
# an auipc fixed its target (`jalr rd`) - as an edge as well as a fall-through. Loops run to a fixed point, and
# the arms and the call targets are resolved in the same fixed point, since each is known only once the dataflow
# reaches it.
# The index must be bounded ON EVERY PATH into the entry load: each register carries, besides the set of
# definitions that reach it, the set of guards whose IN-RANGE edge every path to that point has taken since the
# register was last written (a must-set: intersection at a join, cleared by any write, carried by copies and
# spills). The load's address register must have ONE reaching definition, the `add` / `sh{1,2,3}add` that forms
# base + index*size (the shift an `slli`: funct3 1 AND funct6 0, so the Zbs / Zbb ops that share funct3 1 are not
# read as shifts), whose base operand has ONE reaching definition, the lo12 word that forms the table base, and
# whose index operand passed such a guard. Then address in [base, base + size*(n-1)] on every path.
#
# Fail-closed everywhere: anything the analysis cannot follow refuses the table (and the whole function):
#   - a 2-byte parcel, an opcode outside the integer / FP / system set, a branch out of the function or into the
#     middle of a word, an indirect jump that is not a resolvable jump table / a `ret` / an auipc-formed tail call;
#   - a register call whose target no auipc fixes: it could enter this function anywhere;
#   - a `ret` whose ra MAY hold an address inside this function - any value the write test below would refuse
#     (an auipc / lui / addi pair, a call's link, a value the fold could not enumerate or evaluate): the bytes
#     then contradict the psABI reading of that word, so it is not an exit;
#   - ANY WRITE that puts a value that MAY BE an address inside this function, at any offset, where this
#     analysis stops following it: a STORE (0x23), an ATOMIC (0x2f) - the value is rs2 in both - or ANY
#     INTEGER -> FP instruction (0x53, funct7 0x68 fcvt.s.<int>, 0x69 fcvt.d.<int>, 0x78 fmv.w.x, 0x79 fmv.d.x),
#     which puts it in an FP register this analysis does not model - and the way back (fcvt.l.d, fmv.x.d)
#     would return it with a fresh, untainted definition. The `ret` test reads only the definitions that reach
#     the `ret`, and a return address re-pointed through the frame reaches it as a LOAD, which proves no
#     address - so the write is what refuses, and every opcode that writes has to be named. The value is
#     followed, not pattern-matched: the four shapes the bytes name (an auipc, a `lui`, an `addi` off either, a
#     call's link) and everything address arithmetic or a tracked reload builds from them - through a MERGE
#     (the value at a point is the union over the reaching definitions that are fixed, to a fixed point over
#     the graph, so a chain laid out against address order still settles), and with RV64I's own arithmetic: a
#     *W instruction reads the LOW 32 BITS and sign-extends its 32-bit result, and a shift immediate is a shift
#     only for its own funct6 (funct7 for the *W forms), so a Zbs op is never evaluated as a shift. A value
#     the fold did NOT ENUMERATE or COULD NOT EVALUATE is OVER, and is seeded: a set past VCAP (4096) values,
#     past VPAIRS operand pairs, still changing after FWIDEN passes (where a loop recurrence ends), or an ALU
#     word whose operands are enumerated - one definition or a merge of several - but whose opcode `_alu`
#     does not evaluate (RV64M and every other one: the class, not a list). The fold's limits fail CLOSED;
#     what that costs on real code is the README's stated cost.
#     Refusing every integer -> FP instruction is what lets an FP store (0x27) go unchecked: no FP register
#     can then hold such a value;
#   - a definition of the bound register that is not that one constant: an entry value, a call clobber, a load
#     that is not a tracked reload, a second constant, an `addiw`;
#   - an indexed load off the same table base that is not proven, a store or an ATOMIC through it, any write OF
#     it out of reach, a constant-offset read past the proven entries.
# A word that no modelled edge reaches is NOT a refusal: it is entered with EVERY value unknown, the state weaker
# than any real one, so a path through it proves nothing while the rest of the function still can.
# ASSUMED, not proved (stated in the README): the psABI's callee-saved registers (s0-s11, sp, gp, tp) survive a
# call; a caller-saved register is clobbered. Signal, longjmp and C++ exception edges are not modelled; the
# unknown-state entry above is what covers a landing pad no modelled edge reaches.
# ---------------------------------------------------------------------------------------------------------------
OPS = frozenset((0x37, 0x17, 0x6f, 0x67, 0x63, 0x03, 0x23, 0x13, 0x1b, 0x33, 0x3b, 0x0f, 0x73, 0x2f,
                 0x07, 0x27, 0x43, 0x47, 0x4b, 0x4f, 0x53))       # every opcode the transfer function models
FP_XRD = (0x14, 0x18, 0x1c)                 # OP-FP funct7 >> 2 that writes an INTEGER rd (fcmp / fcvt.x / fmv.x)
# OP-FP funct7 >> 2 of every instruction that reads an INTEGER rs1 into an FP rd, as a CLASS, the way FP_XRD
# above already tests its own: 0x1a is fcvt.{s,d,h,q}.{w,wu,l,lu} (funct7 0x68-0x6b) and 0x1e is
# fmv.{w,d,h,q}.x (0x78-0x7b). A list of exact funct7 values would miss a width - the half and quad forms reach
# an FP register exactly as the single and double ones do, and `fsh` / `fsq` write it.
INT2FP = {0x1a: 'fcvt.<fp>.<int>', 0x1e: 'fmv.<fp>.x'}
SHW = {2: 1, 4: 2, 6: 3}                    # sh1add / sh2add / sh3add funct3 -> shift
CALLER_SAVED = tuple(dc._bc['CALLER_SAVED'])
EMPTY = frozenset()
OVER = type('OVER', (), {'__repr__': lambda s: 'OVER'})()   # the may fold's top: a value set not enumerated
_M = 0xffffffffffffffff
def _s64(v):
    v &= _M
    return v - (1 << 64) if v >> 63 else v
def _s32(v): return sx(v & 0xffffffff, 32)
# A table whose base LEAVES the function may be read past the compared entries by whoever receives it.
# STORED TO MEMORY: the bytes settle it, the refusal is ON and it costs nothing - of the 48 tables the
# control-set functions accept across the three measured images, 0 store the base. IN AN ARGUMENT / RETURN
# REGISTER at a call or a return: the bytes do NOT settle it, because the register may simply be dead there,
# and the refusal is OFF by default - it flags 18 of those 48, and turning it on costs 48 -> 30 acceptances on the
# record pairs (README A5, controls/escmeas.out and esccost.out).
# JTCHECK_REFUSE_ESCAPING_BASE=1 turns that half on; the verdicts of record are made with it off.
ARG_ESCAPE_REFUSES = os.environ.get('JTCHECK_REFUSE_ESCAPING_BASE') == '1'

class St:
    """per register: the set of definitions that reach it, and the must-set of guards its value passed; per 8-byte
    stack slot (offset from the entry sp) the same pair; the sp delta from entry sp (None = unknown)"""
    __slots__ = ('r', 'g', 's', 'd')
    def __init__(self, r, g, s, d): self.r, self.g, self.s, self.d = r, g, s, d
    def key(self): return (self.r, self.g, tuple(sorted(self.s.items())), self.d)

def _join(a, b):
    s = {k: (a.s[k][0] | b.s[k][0], a.s[k][1] & b.s[k][1]) for k in a.s.keys() & b.s.keys()}
    return St(tuple(p | q for p, q in zip(a.r, b.r)), tuple(p & q for p, q in zip(a.g, b.g)), s,
              a.d if a.d == b.d else None)

class Flow:
    """the CFG and its reaching definitions for ONE function of ONE image. `bases` maps the index of a lo12 addi to
    the address it forms (from bytecmp's MUST auipc dataflow); `rd(addr, n)` reads n FILE bytes."""
    STEPS = 600000
    # The may fold's limits. Each of them FAILS CLOSED: a value set that passes one is OVER - a value the bytes
    # fix that this did not enumerate, so it is not ruled out, and it is SEEDED (never "unknown").
    VCAP = 4096               # values per definition; past it, OVER
    VPAIRS = 65536            # operand pairs one ALU word may enumerate; past it, OVER
    FWIDEN = 24               # passes; a definition that still changes after this many is widened to OVER

    def __init__(self, wx, size, fbase, bases, rd):
        self.wx, self.size, self.fbase, self.bases, self.rd = wx, size, fbase, bases, rd
        self.at = {o: k for k, (o, x, n) in enumerate(wx)}
        self.ijmp = []; self.IN = {}; self.ok = False; self.why = None; self._cache = {}
        self.jt = {}; self.ce = {}; self.seed = ()
        self._fv = self._fvin = None; self._tok = self._tokin = None
        for k, (o, x, n) in enumerate(wx):
            if n != 4: self.why = '2-byte parcel at +%#x' % o; return
            op = x & 0x7f
            if op not in OPS: self.why = 'opcode %#x at +%#x not modelled' % (op, o); return
            if op == 0x67 and ((x >> 7) & 31) == 0 and not (((x >> 15) & 31) == 1 and (x >> 20) == 0):
                self.ijmp.append(k)
        self._settle()

    # ---- the transfer function
    def _xfer(self, k, st):
        o, x, _ = self.wx[k]
        op = x & 0x7f; rd = (x >> 7) & 31; rs1 = (x >> 15) & 31; rs2 = (x >> 20) & 31
        f3 = (x >> 12) & 7; f7 = x >> 25
        r = list(st.r); g = list(st.g); s = dict(st.s); d = st.d
        me = frozenset(((('d', k),)))
        def put(reg, orig=me, gu=EMPTY):
            if reg: r[reg] = orig; g[reg] = gu
        spadj = op == 0x13 and f3 == 0 and rd == 2 and rs1 == 2
        if op in (0x13, 0x1b, 0x33, 0x3b):
            cp = 0
            if op == 0x13 and f3 == 0 and rs1 and (x >> 20) == 0: cp = rs1            # mv rd, rs1
            elif op == 0x33 and f7 == 0 and f3 in (0, 4, 6):                          # add / xor / or with x0
                cp = rs1 if (rs2 == 0 and rs1) else rs2 if (rs1 == 0 and rs2) else 0
            put(rd, r[cp], g[cp]) if cp else put(rd)
            if spadj: d = None if d is None else d + sx(x >> 20, 12)
        elif op == 0x03:
            a = sx(x >> 20, 12) + d if (rs1 == 2 and d is not None) else None
            if f3 == 3 and a is not None and a in s: put(rd, s[a][0], s[a][1])
            else: put(rd)
        elif op in (0x23, 0x27):
            imm = sx(((x >> 25) << 5) | ((x >> 7) & 31), 12)
            w = (1 << f3) if op == 0x23 else (4 if f3 == 2 else 8)
            if rs1 == 2 and d is not None:
                a = d + imm
                for q in [q for q in s if q < a + w and a < q + 8]: del s[q]
                if op == 0x23 and f3 == 3: s[a] = (r[rs2], g[rs2])
            else: s.clear()
        elif (op in (0x6f, 0x67) and rd != 0) or (op == 0x73 and f3 == 0):
            # a call (and ecall / ebreak): the psABI's caller-saved registers are clobbered, a callee may write the
            # frame through a pointer it was given, so every tracked slot is forgotten
            for q in CALLER_SAVED: r[q] = frozenset(((('c', k, q),))); g[q] = EMPTY
            s.clear()
            if op in (0x6f, 0x67): put(rd)
        elif op == 0x73: put(rd)                                   # a CSR read / write
        elif op == 0x2f: put(rd); s.clear()                        # an atomic: it writes memory
        elif op == 0x53:
            if (x >> 27) in FP_XRD: put(rd)
        elif op in (0x37, 0x17): put(rd)
        # 0x63 branch, 0x0f fence, 0x07 FP load, 0x43 / 0x47 / 0x4b / 0x4f FMA: no integer rd
        if rd == 2 and not spadj and (op in WRITES_RD or (op == 0x53 and (x >> 27) in FP_XRD)): d = None
        return St(tuple(r), tuple(g), s, d)

    def _guard(self, k):
        """(bound register, index register, n - c) when word k is `bltu rK,rI` (n = c+1) or `bgeu rI,rK` (n = c),
        whose FALL-THROUGH edge is the in-range one"""
        x = self.wx[k][1]
        if x & 0x7f != 0x63: return None
        f3 = (x >> 12) & 7
        if f3 not in (6, 7): return None
        r1, r2 = (x >> 15) & 31, (x >> 20) & 31
        rk, ri = (r1, r2) if f3 == 6 else (r2, r1)
        return None if (not rk or not ri or rk == ri) else (rk, ri, 1 if f3 == 6 else 0)

    def _succ(self, k, jt, ce):
        """[(word index, fall-through?)] - None for 'an edge this analysis cannot follow'. `jt` holds the arms of
        each resolved jump table, `ce` the in-function target of each resolved register call."""
        o, x, _ = self.wx[k]
        op = x & 0x7f; rd = (x >> 7) & 31; rs1 = (x >> 15) & 31
        nxt = self.at.get(o + 4, -1 if o + 4 >= self.size else None)
        if nxt is None: return None
        fall = [] if nxt == -1 else [(nxt, True)]
        if op == 0x63:
            t = self.at.get(o + sx(((x >> 31) & 1) << 12 | ((x >> 7) & 1) << 11 | ((x >> 25) & 0x3f) << 5 |
                                   ((x >> 8) & 0xf) << 1, 13))
            return None if t is None else [(t, False)] + fall
        if op == 0x6f:
            t = jal_target(0, o, x)
            if rd:
                # a DIRECT CALL. Its target is in the bytes: when it lies in this function the call is an edge of
                # this function's graph (and the call may also return, so the fall-through stays).
                if not (0 <= t < self.size): return fall
                return None if t not in self.at else [(self.at[t], False)] + fall
            if not (0 <= t < self.size): return []                 # a tail call leaves the function
            return None if t not in self.at else [(self.at[t], False)]
        if op == 0x67:
            if rd:
                # a REGISTER CALL: `ce` has its in-function target when an auipc fixed one, else it leaves (one
                # that cannot be resolved at all refuses the function in _settle)
                return [(self.at[t], False) for t in sorted(ce.get(k, ()))] + fall
            if rs1 == 1 and (x >> 20) == 0: return []              # ret (_settle checks ra was not re-pointed)
            return [(self.at[t], False) for t in sorted(jt.get(k, ()))]
        return fall

    def _dataflow(self, jt, ce, seed=()):
        r = tuple(frozenset(((('z',),))) if q == 0 else frozenset(((('e', q),))) for q in range(32))
        TOP = St(tuple(frozenset(((('u', q),))) for q in range(32)), tuple(EMPTY for _ in range(32)), {}, None)
        IN = {0: St(r, tuple(EMPTY for _ in range(32)), {}, 0)}
        for q in seed: IN[q] = TOP                 # a word no modelled edge reaches: entered with EVERY value unknown
        work = [0] + list(seed); steps = 0
        while work:
            steps += 1
            if steps > self.STEPS: self.why = 'the dataflow did not settle'; return
            k = work.pop()
            out = self._xfer(k, IN[k])
            sc = self._succ(k, jt, ce)
            if sc is None: self.why = 'an edge at +%#x this analysis cannot follow' % self.wx[k][0]; return
            gd = self._guard(k)
            for t, fallthrough in sc:
                ns = out
                if gd and fallthrough:                             # the in-range edge of a guard
                    ns = St(out.r, tuple(q | {k} if i == gd[1] else q for i, q in enumerate(out.g)), out.s, out.d)
                if t not in IN: IN[t] = ns; work.append(t)
                else:
                    j = _join(IN[t], ns)
                    if j.key() != IN[t].key(): IN[t] = j; work.append(t)
        self.IN = IN

    def _fold(self):
        """{word index: frozenset of the values its result MAY hold, or OVER; absent = nothing fixed reaches it}.
        Every definition the BYTES fix is evaluated: an `auipc`, a `lui`, a call's link, and anything the
        integer ALU computes from them and from immediates off x0, to a fixed point.
        A MERGE DOES NOT STOP IT. A register's value at a word is the UNION over the reaching definitions
        that are fixed; a definition with no value contributes nothing, so nothing is ever seeded merely
        because it is unknown (a load, an entry value), but the members that ARE fixed survive a join.
        Without that, three plain instructions laid out against address order - the last step at the lowest
        address, reached by a backward branch - build a code address the seed never sees.
        THE LATTICE, per definition: nothing yet < a set of at most VCAP values < OVER. Nothing-yet is NOT
        final: a word computed before its operands is computed again, so the order of the words cannot hide
        a value. OVER is final and FAILS CLOSED - `_infunc_values` seeds it, because a value the bytes fix
        that this did not enumerate is not ruled out. A definition becomes OVER when its set passes VCAP, when
        one ALU word would enumerate more than VPAIRS operand pairs, when an operand is OVER, when it is STILL
        CHANGING after FWIDEN passes (a loop counter gains one value per pass and never settles, so a fixed
        pass limit with no widening would stop on a partial set), and - THE CLASS RULE - when its operands
        are enumerated but `_alu` does not evaluate its opcode (RV64M, Zb*, any other): such a word has a
        value the bytes fix and this does not know, so it is not ruled out. No ALU word with enumerated
        operands can be left "unknown". After FWIDEN every change is to OVER, which is final, so the
        iteration ends. The class rule replaces the strict one-definition fold earlier versions kept for
        the same purpose: every word that fold marked is OVER here, and a word whose operands MERGE fixed
        values - which it missed (`mulw` over `t1 in {0x2093f, 1}`) - is OVER too.
        The result is cached against the reaching-definition map it was computed from: it is returned only
        when `self._fvin is self.IN`, and `_dataflow` assigns a NEW dict to `self.IN` on every call and
        nothing updates that dict in place, so a fold cannot outlive the edge set it read, whatever the
        input. That is why no control can kill mutant M31 (the key removed) - it survives by design; the
        measurement (645 fold computations over 747 analyses, none while the edge fixed point runs) is a
        consequence of it, not the argument."""
        if self._fv is not None and self._fvin is self.IN: return self._fv
        val = {}

        def vset(st, reg):
            """the values `reg` may hold here, over the reaching definitions that are fixed: a set (empty when
            nothing fixed reaches it yet) or OVER"""
            if reg == 0: return frozenset((0,))
            out = set()
            for org in st.r[reg]:
                if org[0] == 'z': out.add(0); continue
                if org[0] != 'd': continue
                v = val.get(org[1])
                if v is None: continue
                if v is OVER: return OVER
                out |= v
                if len(out) > self.VCAP: return OVER
            return frozenset(out)

        p = 0
        grew = True
        while grew:
            grew = False
            for k, (o, x, n) in enumerate(self.wx):
                op = x & 0x7f; rd = (x >> 7) & 31
                if not rd or val.get(k) is OVER: continue
                nv = self._imm(o, x, op)
                if nv is not None: nv = frozenset((nv,))
                elif self._alu_word(x, op):
                    st = self.IN.get(k)
                    if st is None: continue
                    s1 = vset(st, (x >> 15) & 31)
                    s2 = vset(st, (x >> 20) & 31) if op in (0x33, 0x3b) else frozenset((0,))
                    if s1 is OVER or s2 is OVER: nv = OVER
                    elif not s1 or not s2: nv = None                      # nothing fixed reaches an operand yet
                    elif self._alu(x, op, [0, 0]) is None: nv = OVER      # THE CLASS RULE: not evaluable
                    elif len(s1) * len(s2) > self.VPAIRS: nv = OVER
                    else:
                        out = {self._alu(x, op, [a, b]) for a in sorted(s1) for b in sorted(s2)}
                        nv = OVER if None in out or len(out) > self.VCAP else frozenset(out)
                else: continue
                if nv != val.get(k):
                    val[k] = OVER if p >= self.FWIDEN else nv         # still changing after FWIDEN: widen
                    grew = True
            p += 1
        self._fv, self._fvin = val, self.IN
        return val

    def _imm(self, o, x, op):
        """the value a word fixes with no register operand: an `auipc`, a `lui`, or the link a call writes"""
        if op == 0x17: return _s64(self.fbase + o + sx(x >> 12, 20) * 4096)
        if op == 0x37: return _s64(sx(x >> 12, 20) * 4096)
        if op in (0x6f, 0x67): return _s64(self.fbase + o + 4)
        return None

    def _alu_word(self, x, op):
        """True when the fold evaluates this word from the values of its register operands"""
        return op in (0x13, 0x1b, 0x33, 0x3b)

    def _alu(self, x, op, a):
        """the value an integer ALU word computes from fixed operands, or None when this does not evaluate
        it. RV64I 3.1.2: a *W instruction IGNORES the upper 32 bits of its inputs and always produces a
        32-bit signed value, sign-extended to 64 - so the shift is on 32 bits, not on 64 then truncated.
        A shift immediate is a shift only for its own funct6 (funct7 for the *W forms): the Zbs / Zbb
        immediate ops share funct3 1 and 5, which is why `_indexed` checks funct6 for the dispatch shift."""
        f3 = (x >> 12) & 7; f7 = x >> 25
        w = op in (0x1b, 0x3b)
        p = [v & 0xffffffff for v in a] if w else [v & _M for v in a]
        out = lambda r: _s32(r) if w else _s64(r)
        if op in (0x13, 0x1b):
            imm = sx(x >> 20, 12)
            if w and f3 not in (0, 1, 5): return None            # only addiw / slliw / srliw / sraiw exist
            if f3 in (1, 5):
                top = f7 if w else (x >> 26)
                if top not in (0, 0x20 if w else 0x10) or (top and f3 != 5): return None  # bclri / rori / ...
                sh = (x >> 20) & (31 if w else 63)
                if f3 == 1: return out(p[0] << sh)
                if top: return out((_s32(p[0]) if w else _s64(p[0])) >> sh)   # arithmetic, on the width
                return out(p[0] >> sh)                                        # logical, on the width's bits
            if f3 == 2: return int(_s64(a[0]) < imm)
            if f3 == 3: return int((a[0] & _M) < (imm & _M))
            q = imm & 0xffffffff if w else imm & _M
            r = {0: p[0] + q, 4: p[0] ^ q, 6: p[0] | q, 7: p[0] & q}.get(f3)
            return None if r is None else out(r)
        if op in (0x33, 0x3b):
            if f7 not in (0, 0x20): return None                  # the M extension and Zb* are not evaluated
            sub = f7 == 0x20
            if w and f3 not in (0, 1, 5): return None            # only addw / subw / sllw / srlw / sraw
            sh = p[1] & (31 if w else 63)
            if f3 == 0: return out(p[0] - p[1] if sub else p[0] + p[1])
            if sub and f3 != 5: return None                      # sub and sra are the only funct7 0x20 forms
            if f3 == 1: return out(p[0] << sh)
            if f3 == 5: return out((_s32(p[0]) if w else _s64(p[0])) >> sh) if sub else out(p[0] >> sh)
            if f3 == 2: return int(_s64(a[0]) < _s64(a[1]))
            if f3 == 3: return int((a[0] & _M) < (a[1] & _M))
            r = {4: p[0] ^ p[1], 6: p[0] | p[1], 7: p[0] & p[1]}.get(f3)
            return None if r is None else out(r)
        return None

    def _infunc(self, o):
        """an in-function address this origin MAY hold, OVER when its value set was not enumerated or could not
        be evaluated (so one is not ruled out), else None. The fold gives each definition the set of values the
        bytes fix for it, so this is a value test over that set, not a list of shapes."""
        if o[0] != 'd': return None
        v = self._fold().get(o[1])
        if v is OVER: return OVER
        return next((q for q in sorted(v) if self.fbase <= q < self.fbase + self.size), None) if v else None

    def _calls(self):
        """the in-function target of every register call; None when one of them cannot be resolved at all"""
        ce = {}
        for k, (o, x, n) in enumerate(self.wx):
            if x & 0x7f != 0x67 or not ((x >> 7) & 31): continue
            st = self.IN.get(k)
            if st is None: continue                                # not reached: it contributes no edge
            m = self._one(st.r[(x >> 15) & 31])
            xm = self.wx[m][1] if m is not None else 0
            if m is None or xm & 0x7f != 0x17:
                self.why = 'the register call at +%#x has no target the bytes fix' % o; return None
            v = self.fbase + self.wx[m][0] + sx(xm >> 12, 20) * 4096 + sx(x >> 20, 12)
            if not (self.fbase <= v < self.fbase + self.size): continue      # it calls out of the function
            t = self.at.get(v - self.fbase)
            if t is None:
                self.why = 'the register call at +%#x enters the middle of a word' % o; return None
            ce[k] = {self.wx[t][0]}
        return ce

    def _rets(self):
        """False when a `ret` can jump back INTO this function: ra at the `ret` may hold an in-function address -
        any origin `_infunc_values` names, so a value the fold could not enumerate (OVER) or could not evaluate
        refuses here as it does at a write. The psABI assumption A1 does not cover a return address the bytes
        themselves re-point."""
        tok = self._infunc_values()
        for k, (o, x, n) in enumerate(self.wx):
            if x & 0x7f != 0x67 or ((x >> 7) & 31) or ((x >> 15) & 31) != 1 or (x >> 20) != 0: continue
            st = self.IN.get(k)
            if st is None: continue
            bad = [q for q in sorted(st.r[1]) if q in tok]
            if bad:
                a = self._infunc(bad[0])
                where = ('an address inside this function (+%#x)' % (a - self.fbase) if isinstance(a, int)
                         else 'a value that may be an address inside this function')
                self.why = 'the `ret` at +%#x returns to %s' % (o, where)
                return False
        return self._stores()

    def _infunc_values(self):
        """every ORIGIN whose value MAY be an address inside this function, by value flow.
        SEEDED with every definition `_infunc` names: one the bytes fix to an in-function address (over the
        folded value, not over a list of shapes), and one whose value set the fold did not enumerate or could
        not evaluate (OVER) - its value is not ruled out, so it is not ruled in either.
        PROPAGATED through: the integer ALU ops `_derived` follows, a tracked reload (which carries the
        definitions that were stored), and A CALL - `_xfer` gives every caller-saved register a fresh
        definition there, which is right about WHICH registers a callee writes and wrong about WHAT it writes,
        since a callee may return an argument (`memcpy` returns its first). A call holding a tainted value in
        an argument register therefore taints A0, the register a returned argument comes back in. a1 carries
        only the second half of a two-register return, which is an argument of the callee's only if it returns
        a pair whose second field is that pointer - not something the bytes show (A1), and tainting it refuses
        a real control with no finding behind it (B59, where the function's own later store of a1 would then
        refuse). Tainting the return rather than refusing the call is what keeps a call that merely passes such
        a value and ignores the result proving its table (B59).
        The propagation runs to its exact fixed point - every round adds an origin or stops."""
        if self._tokin is self.IN: return self._tok
        D = {('d', k) for k in range(len(self.wx)) if self._infunc(('d', k)) is not None}
        while True:
            add = set()
            for k, (o, x, n) in enumerate(self.wx):
                op = x & 0x7f; rd = (x >> 7) & 31
                st = self.IN.get(k)
                if st is None: continue
                if op in (0x13, 0x1b, 0x33, 0x3b) and rd and ('d', k) not in D:
                    if st.r[(x >> 15) & 31] & D or (op in (0x33, 0x3b) and st.r[(x >> 20) & 31] & D):
                        add.add(('d', k))
                elif ((op in (0x6f, 0x67) and rd) or (op == 0x73 and ((x >> 12) & 7) == 0)) \
                        and any(st.r[q] & D for q in self.ARGS):
                    add |= {('c', k, 10)} - D          # a0: where a callee returns an argument it gives back
            if not add: break
            D |= add
        self._tok, self._tokin = frozenset(D), self.IN
        return self._tok

    def _writes(self, k, x, st, tok):
        """why word k puts a value of `tok` somewhere this analysis stops following it, else None. EVERY way a
        register leaves for memory counts, not the plain store alone: `_rets` reads only the definitions that
        reach the `ret`, and a value written to the frame comes back as the epilogue's load, which proves no
        address - so the WRITE is the test, and it has to name every opcode that writes.
          STORE (0x23) and ATOMIC (0x2f): the value is rs2 in both.
          INTEGER -> FP (0x53, funct7 >> 2 in INT2FP: 0x1a every width of fcvt.<fp>.<int>, 0x1e every width
          of fmv.<fp>.x - every instruction that reads an integer register into an FP one, as a class):
          refused AT THE INSTRUCTION, because after it the value sits in an FP register this analysis does not
          model; an FP store (0x27) would put it in memory unseen, and the way back (fcvt.l.d / fmv.x.d) gives
          an integer rd a FRESH definition, so the value would return with no taint on it. Refusing all four is
          what lets the FP stores themselves go unchecked: no FP register can hold such a value, so none can
          write one. The integer source is rs1 in all four.
        A 2-byte parcel refuses the function and opcode 0x57 is not modelled, so a compressed or vector store
        cannot reach here."""
        op = x & 0x7f
        if op in (0x23, 0x2f) and st.r[(x >> 20) & 31] & tok:
            return 'the %s at +%#x writes it to memory' % ('store' if op == 0x23 else 'atomic', self.wx[k][0])
        if op == 0x53 and (x >> 27) in INT2FP and st.r[(x >> 15) & 31] & tok:
            return 'the `%s` at +%#x puts it in an FP register, which this analysis does not model' % (
                INT2FP[x >> 27], self.wx[k][0])
        return None

    def _stores(self):
        """False when any write puts a value that may be an address inside this function beyond reach. No offset
        is exempt: storing the function's own entry is harmless in itself, but it is a value an untracked reload
        and one `addi` turn into any offset, and a function of record never writes an address of itself at all
        (0 such writes in the control sets)."""
        tok = self._infunc_values()
        for k, (o, x, n) in enumerate(self.wx):
            st = self.IN.get(k)
            if st is None: continue
            why = self._writes(k, x, st, tok)
            if why: self.why = why; return False
        return True

    def _edges(self, seed):
        """the (jump-table arm, register-call) edge sets to a fixed point for a given seed; False on a refusal"""
        jt, ce = dict(self.jt), dict(self.ce)
        for _ in range(24):
            self.IN = {}; self._cache = {}          # a NEW dict: what the fold and taint caches are keyed on
            self._dataflow(jt, ce, seed)
            if self.why: return False
            nce = self._calls()
            if nce is None: return False
            new = {}
            for k in self.ijmp:
                t = self._resolve(k)
                if t is None:
                    self.why = 'the indirect jump at +%#x is not a resolvable dispatch' % self.wx[k][0]; return False
                new[k] = set(jt.get(k, ())) | t
            if new == jt and nce == ce:
                self.jt, self.ce, self.seed = jt, ce, seed; return True
            jt, ce = new, nce
        self.why = 'the control-flow edges did not settle'; return False

    def _settle(self):
        """the CFG and its reaching definitions to a joint fixed point: a jump table's arms and a register call's
        target are edges, and both are known only once the dataflow has a state there, so the edge set grows until
        it stops changing. ONLY THEN is a word that no modelled edge reaches entered with EVERY value unknown (a
        state weaker than any real one), so a path through it proves nothing instead of being overlooked - the
        seed comes last because an arm is unreached until its own table is resolved."""
        self.jt, self.ce, self.seed = {}, {}, ()
        if not self._edges(()): return
        for _ in range(8):
            un = tuple(sorted(set(self.seed) | {k for k in range(len(self.wx)) if k not in self.IN}))
            if un == self.seed: self.ok = self._rets(); return
            if not self._edges(un): return
        self.why = 'the words no path reaches did not settle'

    # ---- reading the reaching definitions
    def _one(self, orgs):
        """the single in-function definition that reaches, else None"""
        if len(orgs) != 1: return None
        o = next(iter(orgs))
        return o[1] if o[0] == 'd' else None

    def _const(self, o):
        """the constant an origin holds, if it is an `addi rd, zero, c` (or x0)"""
        if o[0] == 'z': return 0
        if o[0] != 'd': return None
        x = self.wx[o[1]][1]
        if x & 0x7f == 0x13 and ((x >> 12) & 7) == 0 and ((x >> 15) & 31) == 0: return sx(x >> 20, 12)
        return None

    def _bound(self, st, reg):
        """(n, guard word index, bound register, c, n - c): the tightest count proven for `reg` at a point whose
        state is st - over the guards every path took, each one's bound register having ONE constant reaching it"""
        best = None
        for b in sorted(st.g[reg]):
            gd = self._guard(b)
            if not gd or gd[1] != reg: continue
            sb = self.IN.get(b)
            if sb is None: continue
            cs = {self._const(o) for o in sb.r[gd[0]]}
            if len(cs) != 1 or None in cs: continue
            c = cs.pop()
            if c < 0: continue
            n = c + gd[2]
            if n >= 2 and (best is None or n < best[0]): best = (n, b, gd[0], c, gd[2])
        return best

    def _indexed(self, L):
        """(base word index, entry size, n, guard text) when the load at word L reads base + index * size with the
        index bounded on every path, else None"""
        if L in self._cache: return self._cache[L]
        self._cache[L] = None
        o, x, _ = self.wx[L]
        if x & 0x7f != 0x03 or (x >> 20) != 0: return None
        w = LOADW.get((x >> 12) & 7)
        st = self.IN.get(L)
        if w not in (4, 8) or st is None: return None
        j = self._one(st.r[(x >> 15) & 31])
        sj = self.IN.get(j) if j is not None else None
        if sj is None: return None
        xj = self.wx[j][1]
        if xj & 0x7f != 0x33: return None
        f3, f7 = (xj >> 12) & 7, xj >> 25
        ra, rb = (xj >> 15) & 31, (xj >> 20) & 31
        got = None
        if f7 == 0 and f3 == 0:                                    # add rd, ra, rb
            for ib, ii in ((ra, rb), (rb, ra)):
                i = self._one(sj.r[ib])
                if i is None or i not in self.bases: continue
                k = self._one(sj.r[ii])
                if k is None: continue
                xk = self.wx[k][1]
                # `slli rd, rs1, sh` and nothing else: funct6 0 as well as funct3 1, so that bclri / bseti /
                # binvi (Zbs) and the Zbb unary ops, which share funct3 1 with a non-zero funct6, are not shifts
                if xk & 0x7f != 0x13 or (xk >> 26) != 0 or ((xk >> 12) & 7) != 1 or (1 << ((xk >> 20) & 63)) != w:
                    continue
                sk = self.IN.get(k)
                bd = self._bound(sk, (xk >> 15) & 31) if sk is not None else None
                if bd: got = (i, w, bd, (xk >> 15) & 31); break
        elif f7 == 0x10 and f3 in SHW and (1 << SHW[f3]) == w:     # sh{1,2,3}add rd, index, base
            i = self._one(sj.r[rb])
            bd = self._bound(sj, ra) if i is not None and i in self.bases else None
            if bd: got = (i, w, bd, ra)
        if got is None: return None
        i, w, bd, ridx = got
        n, b, rk, c, plus = bd
        self._cache[L] = (i, w, n, '%s x%d, %d' % ('bltu' if plus else 'bgeu', ridx, c))
        return self._cache[L]

    def _entryadd(self, k, i):
        """True when word k is the `add` that turns a PROVEN entry of table i into the target it names (a case
        address, a string address). Its result addresses the entry's TARGET, which the table comparison judges on
        its own terms, not a word of the table, so it is not an address derived from the base."""
        x = self.wx[k][1]
        if x & 0x7f != 0x33 or (x >> 25) != 0 or ((x >> 12) & 7) != 0: return False
        st = self.IN.get(k)
        if st is None: return False
        for ra, rb in (((x >> 15) & 31, (x >> 20) & 31), ((x >> 20) & 31, (x >> 15) & 31)):
            L = self._one(st.r[ra]); b = self._one(st.r[rb])
            p = self._indexed(L) if L is not None else None
            if p and p[0] == i and b == i: return True
        return False

    def _derived(self, i):
        """the words whose value is the table base plus something: address arithmetic from the base word i, to its
        exact fixed point - every round adds a word or stops, so no chain is cut off by a pass limit"""
        D = {i}
        while True:
            tok = frozenset(('d', m) for m in D); add = set()
            for k, (o, x, n) in enumerate(self.wx):
                op = x & 0x7f
                if k in D or op not in (0x13, 0x1b, 0x33, 0x3b) or not ((x >> 7) & 31): continue
                st = self.IN.get(k)
                if st is None: continue
                if st.r[(x >> 15) & 31] & tok or (op in (0x33, 0x3b) and st.r[(x >> 20) & 31] & tok):
                    if not self._entryadd(k, i): add.add(k)
            if not add: return D
            D |= add

    def _target(self, v):
        """the word index a resolved jump target names: -1 when it leaves the function, None when it is not a word"""
        if not (self.fbase <= v < self.fbase + self.size): return -1
        return self.at.get(v - self.fbase)

    def _resolve(self, k):
        """the in-function offsets an indirect jump can reach: a jump table's arms, or an auipc-formed tail call"""
        x = self.wx[k][1]
        st = self.IN.get(k)
        if st is None: return set()                                # not reached yet: it contributes no edge
        if (x >> 20) != 0 and not self._one(st.r[(x >> 15) & 31]): return None
        m = self._one(st.r[(x >> 15) & 31])
        if m is None: return None
        xm = self.wx[m][1]
        if xm & 0x7f == 0x17:                                      # auipc + jalr: a far call / tail call
            v = self.fbase + self.wx[m][0] + sx(xm >> 12, 20) * 4096 + sx(x >> 20, 12)
            t = self._target(v)
            return None if t is None else set() if t == -1 else {self.wx[t][0]}
        if (x >> 20) != 0: return None
        ent = None
        if xm & 0x7f == 0x33 and (xm >> 25) == 0 and ((xm >> 12) & 7) == 0:       # add entry, base -> rel4 / rel8
            sm = self.IN.get(m)
            ra, rb = (xm >> 15) & 31, (xm >> 20) & 31
            for rl, rba in ((ra, rb), (rb, ra)):
                L = self._one(sm.r[rl]); i = self._one(sm.r[rba])
                p = self._indexed(L) if L is not None else None
                if p and i is not None and p[0] == i: ent = (p, self.bases[i], True); break
        else:
            p = self._indexed(m)
            if p: ent = (p, self.bases[p[0]], False)
        if ent is None: return None
        (i, w, n, _), ax, rel = ent
        out = set()
        for e in range(n):
            b = self.rd(ax + w * e, w)
            if b is None: return None
            v = int.from_bytes(b, 'little', signed=rel)
            t = self._target(ax + v if rel else v)
            if t is None: return None
            if t != -1: out.add(self.wx[t][0])
        return out

    # the registers a value leaves the function in: the psABI's argument / return registers a0-a7
    ARGS = tuple(range(10, 18))

    def _escapes(self, tok, args):
        """the first word at which the table base (or an address derived from it) leaves this function, where a
        callee may read the object past the entries jtcheck compares. Two shapes:
          WRITTEN OUT OF REACH - to memory by a store or an atomic, or into an FP register by `fmv.{d,w}.x`:
          the bytes settle it, and it always refuses (the same `_writes` the return-address rule uses);
          IN AN ARGUMENT / RETURN REGISTER at a call, a tail call or a return - the bytes do NOT settle it (the
          register may be dead), so it refuses only when `args` is set (README A5). None when it never leaves."""
        for k, (o, x, n) in enumerate(self.wx):
            op = x & 0x7f; rd = (x >> 7) & 31; rs1 = (x >> 15) & 31
            st = self.IN.get(k)
            if st is None: continue
            w = self._writes(k, x, st, tok)
            if w: return o, w
            if not args: continue
            leaves = ((op in (0x6f, 0x67) and rd) or (op == 0x73 and ((x >> 12) & 7) == 0)
                      or (op == 0x6f and not rd and not (0 <= jal_target(0, o, x) < self.size))
                      or (op == 0x67 and not rd and not self.jt.get(k)))   # a resolved dispatch stays inside
            if not leaves: continue
            a = [q for q in self.ARGS if st.r[q] & tok]
            if a: return o, 'in x%d at a call or a return out of the function' % a[0]
        return None

    def prove(self, i, ax):
        """(entry size, count, evidence) for the table the lo12 word i addresses: every indexed load off that base
        is bounded on every path, nothing writes through it, no constant-offset read goes past the entries, and
        the base never leaves the function"""
        if not self.ok or i not in self.bases or self.bases[i] != ax: return None
        D = self._derived(i)
        tok = frozenset(('d', m) for m in D)
        best = None; plain = []
        for k, (o, x, n) in enumerate(self.wx):
            op = x & 0x7f
            if op not in (0x03, 0x23, 0x07, 0x27, 0x2f): continue      # every opcode that ADDRESSES memory by rs1
            st = self.IN.get(k)
            if st is None or not (st.r[(x >> 15) & 31] & tok): continue
            if op != 0x03: return None          # a store or an atomic through the table base, or an FP access
            if st.r[(x >> 15) & 31] == frozenset((('d', i),)):     # a read at a constant offset from the base
                plain.append((k, sx(x >> 20, 12), LOADW.get((x >> 12) & 7, 8))); continue
            p = self._indexed(k)
            if p is None or p[0] != i: return None
            if best is None or (p[2], -o) > (best[0][2], -self.wx[best[1]][0]): best = (p, k)
        if best is None: return None
        (i2, w, n, why), k = best
        if ax % w: return None
        for _, imm, lw in plain:
            if imm < 0 or imm + lw > w * n: return None            # it reads past the entries jtcheck compares
        if self._escapes(tok, ARG_ESCAPE_REFUSES) is not None: return None
        return w, n, '%d-byte entries, %s, l%s at +%#x from the base' % (w, why, 'd' if w == 8 else 'w', self.wx[k][0])

def _labels(wx):
    """the offsets every in-function branch and jal can enter at"""
    out = set()
    for o, x, n in wx:
        if n != 4: continue
        if x & 0x7f == 0x63:
            out.add(o + sx(((x >> 31) & 1) << 12 | ((x >> 7) & 1) << 11 | ((x >> 25) & 0x3f) << 5 | ((x >> 8) & 0xf) << 1, 13))
        elif x & 0x7f == 0x6f:
            out.add(jal_target(0, o, x))
    return out

TSTR = []     # C strings accepted for the entries of a string table; run() lists them as CSTR rows

def table(fx, fy, ax, ay, size, nmax):
    """(kind, n, ok, cases) or None, over exactly the nmax entries the dispatch can index. A `size`-byte entry is a
    jump-table case when the X entry points into the X function (absolute, or relative to the table base): compared as
    a function-relative offset. A 4-byte entry that points at an unnamed .rodata address on both sides is a string
    table: each entry by the C-string rule. Otherwise 8-byte entries are pointers (qname_ok) and 4-byte entries are
    values (raw). File bytes only."""
    out = []
    for rel in ((False, True) if size == 4 else (False,)):
        n = 0; ok = True; cases = set(); kind = None; strs = []
        while n < nmax:
            ex = dc.frd(X, ax + size * n, size); ey = dc.frd(Y, ay + size * n, size)
            if ex is None or ey is None: break
            if rel:
                vx = ax + int.from_bytes(ex, 'little', signed=True); vy = ay + int.from_bytes(ey, 'little', signed=True)
            else:
                vx = int.from_bytes(ex, 'little'); vy = int.from_bytes(ey, 'little')
            if fx[0] <= vx < fx[0] + fx[1] and kind in (None, 'jump'):
                kind = 'jump'; cases.add(vx - fx[0])
                if vy - fy[0] != vx - fx[0]: ok = False
            elif rel and kind in (None, 'str') and X.sec(vx) == Y.sec(vy) == '.rodata' \
                    and dc.qres(X, vx) == '(.rodata)' and dc.qres(Y, vy) == '(.rodata)':
                kind = 'str'
                sa, sb = dc.cstring(X, vx), dc.cstring(Y, vy)
                if sa is not None and sa == sb: strs.append((vx, vy, sa))
                elif ex != ey or sa != sb: ok = False
            elif not rel and kind in (None, 'ptr' if size == 8 else 'value'):
                kind = 'ptr' if size == 8 else 'value'
                if not (qname_ok(vx, vy, ex, ey) if size == 8 else ex == ey): ok = False
            else:
                break
            n += 1
        if n == nmax:
            out.append(('%s%d-%s' % ('rel' if rel else 'abs', size, kind), n, ok, cases, strs))
    # a 4-byte entry can be read as a value, as an offset to a case or as an offset to a string; the reading that says
    # what the dispatch does wins, and a reading that settles the target wins over one that does not
    out.sort(key=lambda t: (t[0].endswith('value'), not t[2]))
    if not out: return None
    TSTR.extend(out[0][4])
    return out[0][:4]

def blob(ax, ay, L):
    """L bytes as 8-byte words, each by qname_ok; a read past the file bytes is a difference"""
    ok = True
    for k in range(0, L, 8):
        ex = dc.frd(X, ax + k, min(8, L - k)); ey = dc.frd(Y, ay + k, min(8, L - k))
        if ex is None or ey is None or not qname_ok(int.from_bytes(ex, 'little'), int.from_bytes(ey, 'little'), ex, ey):
            ok = False
    return ok

def same_target(fx, fy, tx, ty, word, shape=None, copy=None):
    """-> (verdict, what, table, acceptance): verdict True / False / None (UNMEASURED). tsame decides first; on top of
    it, for an unnamed .rodata / .data.rel.ro target it refuses: a table the function really dispatches through
    (`shape`), an initializer an exact-length copy reads whole (`copy` = (length, callee)), or UNMEASURED when the two
    regions are not equally long. acceptance = (kind, x, y, info) for anything but a name."""
    ok, kind, rx, ry, info = dc.tsame(X, tx, Y, ty, word)
    # the kinds tsame gives an unnamed data target; the table / initializer rule may still settle one of these
    unnamed_data = kind in ('full', 'cstr', 'data-differs', 'cstr-differs', 'strlabel-differs')
    ro = X.sec(tx) in ('.rodata', '.data.rel.ro')
    shape = shape() if (unnamed_data and ro and shape) else None
    t = table(fx, fy, tx, ty, shape[0], shape[1]) if shape else None
    if ok:
        info = (rx if kind in ('gotval', 'tlsindex') else
                '%s|%s %r' % (rx, ry, info) if kind == 'NAME-ONLY' else info)
        return True, '%s %s' % (kind, rx), t, (None if kind == 'name' else (kind, tx, ty, info))
    if t and t[1] >= 2 and (t[0].endswith('jump') or t[2]):
        what = 'table %s %d entries (%s)' % (t[0], t[1], shape[2])
        return t[2], what, t, (('table', tx, ty, '%s %d entries' % (t[0], t[1])) if t[2] else None)
    if unnamed_data and ro and copy:
        # the length is the whole object only when the call reads exactly that many bytes (a memcpy-family callee) AND
        # the unnamed region is exactly that long on both sides. `internal_strncpy(dst, "", 16)` reads to the NUL, so
        # its 16 is a bound, not an extent, and it used to make 16 bytes of an empty string an 'initializer'.
        L, callee = copy
        ra, rb = dc.region(X, tx), dc.region(Y, ty)
        if ra is not None and rb is not None and len(ra) == L and len(rb) == L and blob(tx, ty, L):
            return True, 'initializer %d bytes (%s reads the whole region)' % (L, callee), t, ('initializer', tx, ty, L)
    if kind == 'data-differs' and dc.loadwidth(word) is None:
        ra, rb = dc.region(X, tx), dc.region(Y, ty)
        if ra is not None and rb is not None and len(ra) != len(rb):
            return None, 'unnamed %s: region %d | %d bytes to the next FUNC / OBJECT start (extent unknown)' % (
                rx, len(ra), len(rb)), t, None
        if open_string(X, tx) or open_string(Y, ty):
            return None, 'unnamed %s: printable bytes with no NUL before the region or the file bytes end (C-string ' \
                'rule cannot bound it)' % rx, t, None
    return False, '%s: %s | %s' % (kind, rx, ry), t, None

def open_string(I, a):
    """the region at a (to the next FUNC / OBJECT start or the end of a's section) runs past its PT_LOAD's file bytes,
    and the file bytes from a to their end are non-empty, all printable and hold no NUL: a C string whose NUL no file
    holds, so the C-string rule cannot bound it (the kit Img.rd's zero-fill would supply a NUL; jtcheck does not use it)"""
    s = next(((v, z) for nm, v, z in I.secs if v <= a < v + z), None)
    g = next(((v, fz, d) for v, fz, d in I.segs if v <= a < v + fz), None)
    if s is None or g is None: return False
    st = dc._meta(I)['starts']; k = dc.bisect.bisect_right(st, a)
    rend = min(s[0] + s[1], st[k] if k < len(st) else s[0] + s[1])
    if rend <= g[0] + g[1]: return False
    b = g[2][a - g[0]:]
    return bool(b) and b'\0' not in b and all(ch in dc.PRINTABLE for ch in b)

def copy_len(wx, i, base):
    """(length, callee name) when `addi a2, zero, L` and then a `jal ra` within the 3 words after word i call a
    memcpy-family function, which reads exactly L bytes of the source. None for any other callee: `internal_strncpy`
    and the other str* copies stop at the source's NUL, so their L is a bound, not the object's extent."""
    L = None
    for j in range(i + 1, min(len(wx), i + 4)):
        o, x, n = wx[j]
        if n != 4: break
        if x & 0x7f == 0x13 and ((x >> 12) & 7) == 0 and ((x >> 15) & 31) == 0 and ((x >> 7) & 31) == 12:
            L = sx(x >> 20, 12)
        if x & 0x7f == 0x6f and ((x >> 7) & 31) == 1:
            if L is None or L <= 0: return None
            nm = (dc.qres(X, jal_target(base, o, x)) or '').split('+')[0]
            # the name may be mangled (`_ZN11__sanitizerL15internal_memcpyEPvPKvm`), so match inside it, and refuse
            # every str* copy by name: those stop at the source's NUL
            if any(s in nm for s in ('strncpy', 'strcpy', 'strlcpy', 'strcat', 'strncat')): return None
            return (L, nm) if any(m in nm for m in MEMCPY) else None
    return None

def jal_target(base, o, x):
    return base + o + sx(((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11 | ((x >> 21) & 0x3ff) << 1, 21)

def hi_lo(base, ws, k, w, op):
    ho, hx, _ = ws[k]
    hi = base + ho + sx(hx >> 12, 20) * 4096
    return hi + (sx(((w >> 25) << 5) | ((w >> 7) & 31), 12) if op in (0x23, 0x27) else sx(w >> 20, 12))

def bb_auipc(wx, i, rs1, labels):
    j = i - 1
    while j >= 0:
        if wx[j + 1][0] in labels: return None
        oj, xj, _ = wx[j]; opj = xj & 0x7f; rdj = (xj >> 7) & 31
        if opj in (0x63, 0x6f, 0x67): return None
        if opj == 0x73 and ((xj >> 12) & 7) == 0 and rs1 in (10, 11): return None
        if rdj == rs1 and opj == 0x17: return j
        if rdj == rs1 and (opj in WRITES_RD or opj == 0x2f or (opj == 0x53 and ((xj >> 27) & 31) in (0x14, 0x18, 0x1c))):
            return None
        j -= 1
    return None

def fsymq(I, spec):
    """(addr, size) of the sized FUNC named spec (or name{file}); None if absent; 'ambiguous' if several, unqualified.
    An unqualified unique name goes through I.fsym (the same answer: the one sized FUNC of that name)."""
    nm = spec.split('{')[0]
    c = sorted({(v, z) for v, z, t in I.byname.get(nm, []) if t == 'STT_FUNC' and z > 0})
    if '{' in spec: c = [(v, z) for v, z in c if dc.qname(I, nm, v) == spec]
    elif len(c) <= 1: return I.fsym(nm)
    return None if not c else c[0] if len(c) == 1 else 'ambiguous'

def run(fn):
    fx, fy = fsymq(X, fn), fsymq(Y, fn)
    if 'ambiguous' in (fx, fy):
        print('%s\tSKIP AMBIGUOUS: several sized FUNC symbols carry this name (give it as name{file})' % fn); return
    if not fx or not fy or fx[1] != fy[1]:
        print('%s\tSKIP %s %s' % (fn, fx, fy)); return
    bx, by = dc.frd(X, *fx), dc.frd(Y, *fy)
    if bx is None or by is None:
        print('%s\tUNREADABLE (function bytes not all file bytes)' % fn); return
    wx, wy = bc_words(bx), bc_words(by)
    def mask(op): return 0xfff if op in (0x17, 0x6f) else 0x01fff07f if op in (0x23, 0x27) else 0x000fffff
    shape = [i for i, ((o, x, n), (_, y, _)) in enumerate(zip(wx, wy)) if x != y and (
        (x & 0x7f) != (y & 0x7f) or (x & 0x7f) not in LO12 + (0x17, 0x6f) or (x & mask(x & 0x7f)) != (y & mask(x & 0x7f)))]
    if shape:
        print('%s\tREAL difference (not immediate-only) at %s' % (fn, [hex(wx[i][0]) for i in shape[:6]])); return
    st_all = dc._g['bc_states'](wx)
    onreg = dc.auipc_reg_words(wx); flabels = _labels(wx)
    rvc = any(n == 2 for o, x, n in wx)   # 2-byte parcels are not decoded here: no basic-block pairing then
    # the table bases the CFG analysis may use: a lo12 addi whose auipc bytecmp's MUST dataflow binds
    bsx, bsy = {}, {}
    for i, (o, x, n) in enumerate(wx):
        st = st_all[i]; rs1 = (x >> 15) & 31
        if n != 4 or x & 0x7f != 0x13 or ((x >> 12) & 7) != 0 or not st or rs1 not in st: continue
        k = st[rs1]
        if k is None or k < 0 or wx[k][1] & 0x7f != 0x17: continue
        bsx[i] = hi_lo(fx[0], wx, k, x, 0x13); bsy[i] = hi_lo(fy[0], wy, k, wy[i][1], 0x13)
    FLOW = {}
    def flow(I, ws, fs, bs):
        if id(ws) not in FLOW:
            FLOW[id(ws)] = Flow(ws, fs[1], fs[0], bs, lambda a, n, I=I: dc.frd(I, a, n))
        return FLOW[id(ws)]
    def prove(i, tx, ty):
        """the shape X and Y BOTH prove for the table at word i, else None (they must agree on size and count)"""
        a = flow(X, wx, fx, bsx).prove(i, tx)
        if a is None: return None
        b = flow(Y, wy, fy, bsy).prove(i, ty)
        return a if (b is not None and a[:2] == b[:2]) else None
    base_labels = set()
    for o, x, n in wx:
        op = x & 0x7f
        if op == 0x63:
            base_labels.add(o + sx(((x >> 31) & 1) << 12 | ((x >> 7) & 1) << 11 | ((x >> 25) & 0x3f) << 5 | ((x >> 8) & 0xf) << 1, 13))
        elif op == 0x6f:
            t = jal_target(0, o, x)
            if 0 <= t < fx[1]: base_labels.add(t)
    cases = set()
    while True:
        labels = base_labels | cases
        pairs = {}; unpaired = []
        for i, ((o, x, n), (_, y, _)) in enumerate(zip(wx, wy)):
            op = x & 0x7f; rs1 = (x >> 15) & 31
            if op not in LO12: continue
            st = st_all[i]
            k = st[rs1] if st and rs1 in st else None
            if k is None and not rvc: k = bb_auipc(wx, i, rs1, labels)
            if k is None:
                if x != y: unpaired.append('+%#x %08x vs %08x op %#x rs1 x%d' % (o, x, y, op, rs1))
                elif i in onreg: unpaired.append('+%#x %08x (equal) op %#x rs1 x%d: base register last written by an auipc' % (o, x, op, rs1))
                continue
            pairs[i] = (hi_lo(fx[0], wx, k, x, op), hi_lo(fy[0], wy, k, y, op), k)
        newcases = set(cases); res = []; acc = []
        for i, (tx, ty, k) in sorted(pairs.items()):
            del TSTR[:]
            ok, what, t, a = same_target(fx, fy, tx, ty, wx[i][1], (lambda i=i, tx=tx, ty=ty: prove(i, tx, ty)),
                                         copy_len(wx, i, fx[0]))
            if t and t[0].endswith('jump'): newcases |= t[3]
            res.append((wx[i][0], ok, what, wx[i][1] != wy[i][1]))
            if ok and a: acc.append((a[0], hex(wx[i][0]), a[1], a[2], a[3]))
            # the C strings a string table's entries point at, listed under the word that addresses the table
            if ok: acc += [('cstr', hex(wx[i][0]), vx, vy, s) for vx, vy, s in sorted(set(TSTR))]
        if newcases == cases: break
        cases = newcases
    used = {k for (tx, ty, k) in pairs.values()}
    for k, (o, x, n) in enumerate(wx):
        if n == 4 and x & 0x7f == 0x17 and (x >> 7) & 31 and k not in used:
            unpaired.append('+%#x %08x vs %08x auipc consumed by no pair' % (o, x, wy[k][1]))
    jres = []
    for i, ((o, x, n), (_, y, _)) in enumerate(zip(wx, wy)):
        if n == 4 and x & 0x7f == 0x6f:
            tx, ty = jal_target(fx[0], o, x), jal_target(fy[0], o, y)
            if fx[0] <= tx < fx[0] + fx[1] or fy[0] <= ty < fy[0] + fy[1]:
                jres.append((o, tx - fx[0] == ty - fy[0], 'jal +%#x | +%#x (in-function)' % (tx - fx[0], ty - fy[0]), x != y))
            else:
                ok, kind, rx, ry, info = dc.tsame(X, tx, Y, ty, x)
                jres.append((o, ok, 'jal %s: %s | %s' % (kind, rx, ry), x != y))
    bad = [r for r in res + jres if r[1] is False]
    unm = [r for r in res if r[1] is None]
    # THE KIT'S OWN VERDICT. strictcmp3's tcmp runs over the same function - its pc-relative and jal targets, its
    # unbound auipc / auipc-register words, and its rule 8 lui pass (lui+addi / lui+load / lui+store / lui+jalr, a lui
    # value used as a call argument, a return value or a raw operand). Every row it reports stays a difference (or
    # UNMEASURED, for its `unmeasured` kind) UNLESS jtcheck settled that same word offset by a table or an initializer
    # (the only settlements jtcheck adds), or jtcheck already reports that offset itself.
    fbk = []
    _v, _c, _cnt, sdiff = dc.tcmp({'X': X, 'Y': Y}, 'X', fx[0], 'Y', fy[0], fx[1], fbk)
    settled = {int(a[1], 16) for a in acc if a[0] in ('table', 'initializer')}
    have = {r[0] for r in bad} | {r[0] for r in unm}
    have |= {int(re.match(r'\+(0x[0-9a-f]+)', u).group(1), 16) for u in unpaired if re.match(r'\+0x', u)}
    for oh, r1, r2, kind, info in sdiff:
        o = int(oh, 16)
        if o in settled and kind in ('data-differs', 'cstr-differs', 'strlabel-differs'): continue
        if o in have: continue
        have.add(o)
        what = 'strictcmp3 %s: %s | %s%s' % (kind, r1, r2, (' (%s)' % (info,)) if info else '')
        (unm if kind == 'unmeasured' else bad).append((o, None if kind == 'unmeasured' else False, what, True))
    # list every acceptance strictcmp3 made at a word jtcheck does not judge itself (the lui pass, lui-const)
    mine = {r[0] for r in res + jres}
    acc += [f for f in fbk if int(f[1], 16) not in mine]
    bad.sort(); unm.sort()
    ncs = sum(1 for a in acc if a[0] == 'cstr')
    tabs = sorted({r[2] for r in res if r[2].startswith('table')})
    if _sc: tabs = [SCAFFOLD_MARK] + tabs          # kept by every harness: a scaffold row says so itself
    print('%s\tX %#x Y %#x size %d\tlo12 pairs %d (in differing words %d)\tjal %d (differing %d)\ttarget differs %d\t'
          'target unmeasured %d\tunpaired %d\tC-string acceptances %d\t%s'
          % (fn, fx[0], fy[0], fx[1], len(res), sum(1 for r in res if r[3]), len(jres), sum(1 for r in jres if r[3]),
             len(bad), len(unm), len(unpaired), ncs, tabs))
    for o, ok, what, d in bad: print('   DIFF +%#x %s' % (o, what))
    for o, ok, what, d in unm: print('   UNMEASURED +%#x %s' % (o, what))
    for u in unpaired: print('   UNPAIRED ' + u)
    for k, o, x, y, info in acc:
        if k != 'cstr': print('   ACCEPT %s %s +%s [%#x|%#x] %s' % (fn, k, o, x, y, info))
    for r in dc.cstr_rows(fn, 'X:Y', acc): print(r)

if __name__ == '__main__':
    for f in sys.argv[3].split(','):
        run(f)
