#!/usr/bin/env python3
"""luitrace.py -- every lui of a record's compared functions, traced by hand rules in both images. Read-only. Loads
strictcmp3.py (cmpkit 86da41d3ef68) from its own directory for the ELF reader, the decoder helpers and qres.

COMPARED SET: the functions reached in X from the roots through any pc-relative target or .got cell that starts a sized
FUNC symbol (calls and address-taking, transitively); each one's Y copy is the function at the same word of Y's
counterpart of an X function that reaches it (the roots by name). This is a superset of the by-name closure and of
paircl's target-paired closure.

TRACE: for every lui word of a member, a forward MAY dataflow over the function's control-flow graph follows the lui's
value and EVERY value computed from it until each register holding it is written. The CFG is bytecmp's successors plus
an edge from every indirect jump to every jump-table arm (arms_of: shape e) and, for an in-function call, an edge that
carries the caller's registers into the callee (shape f). Each value carries a symbolic form (anchor, constant): anchor
None (a pure number), ('sym', address) for an operand formed by auipc or the .got, or ('ptr', origin) for an object
pointer (a value loaded from memory, a parameter of the function, or the return of a call); constant is the summed lui
/ immediate part when it is known. Per shape of the unit owner's ruling:
  (a) a load / store / AMO base is the value + the instruction's immediate (V+imm);
  (b) addi / addiw / mv sum their immediates (addiw sign-extends from 32 bits);
  (c) slli / srli / srai / andi / ori / xori / slti / sltiu and every R-type op are computed exactly on known numbers
      (imm_op, alu); on an anchored or unknown value they give an unknown number, so a base built from it is NOT
      CERTIFIED, never EQUAL;
  (d) a store into a stack slot (sp, or a register built from sp: anchor()) is a SPILL, followed into every reload of
      that slot, only when the slot is PRIVATE: no pointer into the frame object that may cover it leaves the function
      (stack_escapes / slot_escape: passed to a call, tail jump or ecall, stored, returned). A store into a slot whose
      frame object escapes is a STORE row (its reader, a callee or the kernel, is not traced), and its reloads are
      followed too. A move into an FP register or a CSR is a NOT CERTIFIED row;
  (e) a jump-table arm also reached by fall-through gets the values live at the dispatch (the arm edges);
  (f) an in-function callee: the values in a0-a7 are arg ROWs at the call AND are followed into the callee;
  (g) a function with a 2-byte parcel (a possible c.lui) is refused whole: UNMEASURED;
  (h) addresses built without a lui are basescan.py's.
A call ends a caller-saved register only when that is measured (live_after / clobbers). A call to a function that never
returns (noreturn(): no return and no tail jump anywhere in it, its last word a jump, a trap or a call to such a
function; Die, CheckFailed, internal__exit, Abort, abort, ...) has no edge to its next word, so nothing after it is
reached from it and a0 there is never "the return of" it (the uci review, D1). A value live in an argument register at
any later call is a use there (an arg ROW or a measured NOTARG), so a trace does not stop early on an abort path (D2).
The trace stops at these EVENTS, each a ROW unless noted:
  arg     a register holding the value is live at a call or a tail jump (jal / jalr ra / jalr zero that is not a
          jump-table dispatch): a ROW unless the register is past the callee's parameters and the callee (followed
          into what it calls first) never reads it (NOTARG)
  ret     a0 / a1 holding the value at a return: a ROW unless measured otherwise (NOTRET)
  store   the value is stored as data (not into a private stack slot)
  base    the value is a load / store / jump base (or an AMO address)
  amo     an AMO data operand
  ecall   the value is live in a0-a5 at an ecall
  fpmove, csr   the value leaves the integer registers
  cmp, arith, spill, reload: trace only
A lui word with no ROW and no measured non-row on any feasible path is COMPARE-ONLY when its trace holds a branch /
compare (CMPONLY line), else NO USE (NOUSE line: the value is not read, or only by arithmetic or private spills that are
not read). Every ALU op keeps its result traced. A use the trace reaches only when the fall-through edges of noreturn
calls are put back is on no feasible path: an UNREACH line (the use, and the noreturn calls between), never a row.
CLASSES (ruling of the unit owner; one class per row, with its citation). The evidence for a type or a name is the PINNED
SOURCE (llvm-project llvmorg-20.1.8 compiler-rt and musl 1.2.5, the `Alpine clang version 20.1.8` of both images'
.comment), read by cite_gen.py into a CITE table and cross-checked against the type the MANGLED NAME itself carries;
these images are built without DWARF parameters (134 DW_TAG_formal_parameter in the whole image), so DWARF cannot cite.
  (i) CALL ARGUMENT: the callee's parameter at that register is an integer type that is not address-sized (never uptr /
      a pointer) AND the pinned source names it a size / len / count / flags / mode / prot / align.
  (ii) RETURN: the pinned source's return type is an integer that is not address-sized.
  (iii) DISPLACEMENT: a base whose anchor is an object pointer (a load, an argument, an allocator return) settles; a base
      anchored at an auipc / lui address settles only when the FULL address (anchor + constant + immediate), in X and in
      Y, is the same symbol + offset (qres); a different one is DIFFERS.
  (iv) STORE: a store into a stack slot of a frame object whose address leaves the function, where at least one reader
      receives the object as a cited struct and the stored bytes are cited integer, non-address members or padding
      (cite-extra.tsv `param` / `size` / `field` rows; iv_settle); every other escape cannot read memory or ends below.
  STORE-UNREAD: the same store, where every callee the object is passed to has no load, AMO, ecall or call
      (writer_only, measured in both images; the row gives each callee's instruction count). A measured class, not (iv).
  anything else: NOT CERTIFIED (real 0).
MEASURED NON-ROWS: NOTARG (the register is past the callee's parameters, which the mangled name counts), NOTECALL (past
  the syscall's argument registers), NOTRET (a void return, or a1 where the return takes one register, or a1 read by no
  direct caller), UNMEASURED (a function with a 2-byte parcel), NOY (no Y copy of the same size), UNREACH (above).
usage: luitrace.py X_ELF Y_ELF ROOT1,ROOT2,... [CITE_TSV] [--only FN,FN]
  X_ELF, Y_ELF are the two UNSTRIPPED twins. CITE_TSV rows: `arg<TAB>callee<TAB>aK<TAB>type<TAB>name<TAB>citation` and
  `ret<TAB>function<TAB>-<TAB>type<TAB>meaning<TAB>citation` (cite_gen.py writes them; it defaults to cite.tsv here)."""
import collections, importlib.util, os, re, runpy, sys
HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('strictcmp3', os.path.join(HERE, 'strictcmp3.py'))
s3 = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(s3)
RN = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
      's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
M64 = (1 << 64) - 1
# the MEANINGS that settle a call argument (the unit owner's ruling (a)): the pinned source's name must say the parameter is a
# byte count, a length, a count, a size, flags, a mode, a protection or an alignment. Matched as whole words of the
# parameter name (`max_len`, `buf_len`, `n`, `nmemb`, `size`, `alignment`, `flags`, `mode`, `prot`), never as a
# substring of an address name (`addr`, `beg`, `ptr`, `p`, `base`, `shadow`).
SETTLE_WORDS = ('size', 'len', 'length', 'count', 'cnt', 'n', 'num', 'nmemb', 'bytes', 'flag', 'flags', 'mode',
                'prot', 'align', 'alignment', 'width')
NEVER_SETTLE_WORDS = ('addr', 'address', 'ptr', 'p', 'beg', 'begin', 'end', 'base', 'shadow', 'mem', 'buf', 'buff',
                      'buffer', 'dst', 'src', 'data', 'this', 'name', 'filename', 'cond', 'file')
CS = s3._bc['CALLER_SAVED']
# the anchor texts origin() gives an OBJECT POINTER: a parameter, a stack address, the return of a call, a value the
# function loaded, or a .got cell. Everything else a form can carry ("two anchors or a scaled anchor", "many forms")
# is not one pointer and never settles a base.
OBJPTR = ('parameter ', 'a stack address', 'the return of ', 'a value loaded by ', 'loaded from the .got')

def sxv(v, b): return v - (1 << b) if v & (1 << (b - 1)) else v
def dec(x):
    op = x & 0x7f; return op, (x >> 7) & 31, (x >> 12) & 7, (x >> 15) & 31, (x >> 20) & 31, x >> 25
def text(x, o):
    op, rd, f3, r1, r2, f7 = dec(x)
    if op == 0x37: return 'lui %s,%#x' % (RN[rd], (x >> 12) & 0xfffff)
    if op == 0x17: return 'auipc %s,%#x' % (RN[rd], (x >> 12) & 0xfffff)
    if op in (0x13, 0x1b):
        m = (['addi', 'slli', 'slti', 'sltiu', 'xori', 'srli', 'ori', 'andi'] if op == 0x13 else
             ['addiw', 'slliw', '?', '?', '?', 'srliw', '?', '?'])[f3]
        if f3 == 5 and (x >> 30) & 1: m = 'srai' if op == 0x13 else 'sraiw'
        return '%s %s,%s,%d' % (m, RN[rd], RN[r1], sxv(x >> 20, 12) if f3 not in (1, 5) else (x >> 20) & 63)
    if op in (0x33, 0x3b):
        if f7 == 1: m = ['mul', 'mulh', 'mulhsu', 'mulhu', 'div', 'divu', 'rem', 'remu'][f3]
        elif f7 == 0x10 and f3 in (2, 4, 6): m = {2: 'sh1add', 4: 'sh2add', 6: 'sh3add'}[f3]
        elif f7 == 0x04 and op == 0x3b: m = 'add.uw' if f3 == 0 else 'zba?'
        else: m = {0: 'sub' if f7 == 0x20 else 'add', 1: 'sll', 2: 'slt', 3: 'sltu', 4: 'xor',
                   5: 'sra' if f7 == 0x20 else 'srl', 6: 'or', 7: 'and'}[f3]
        return '%s%s %s,%s,%s' % (m, 'w' if op == 0x3b and m not in ('add.uw', 'zba?') else '', RN[rd], RN[r1], RN[r2])
    if op == 0x03: return '%s %s,%d(%s)' % (['lb', 'lh', 'lw', 'ld', 'lbu', 'lhu', 'lwu', '?'][f3], RN[rd], sxv(x >> 20, 12), RN[r1])
    if op == 0x23:
        return '%s %s,%d(%s)' % (['sb', 'sh', 'sw', 'sd', '?', '?', '?', '?'][f3], RN[r2],
                                 sxv(((x >> 25) << 5) | ((x >> 7) & 31), 12), RN[r1])
    if op == 0x63:
        t = sxv(((x >> 31) & 1) << 12 | ((x >> 7) & 1) << 11 | ((x >> 25) & 0x3f) << 5 | ((x >> 8) & 0xf) << 1, 13)
        return '%s %s,%s -> +%#x' % (['beq', 'bne', '?', '?', 'blt', 'bge', 'bltu', 'bgeu'][f3], RN[r1], RN[r2], o + t)
    if op == 0x67: return 'jalr %s,%d(%s)' % (RN[rd], sxv(x >> 20, 12), RN[r1])
    if op == 0x6f: return 'jal %s' % RN[rd]
    if op == 0x2f: return 'amo%d %s,%s,(%s)' % (x >> 27, RN[rd], RN[r2], RN[r1])
    if op == 0x73: return 'ecall' if x == 0x73 else 'system'
    return 'op%#x' % op

_NORET = {}
def noreturn(I, a):
    """does the function at a never return? Only when it is certain: a sized FUNC symbol of the image (STARTS) with no
    2-byte parcel, no return, no tail jump (no jal zero out of it, no jalr zero at all); its calls may be anything (a call
    that returns falls through to the next word, and the function still has no way out)"""
    st = STARTS.get(id(I), {})
    if a not in st: return False
    key = (id(I), a)
    if key not in _NORET:
        # a cycle of last-word calls (Die -> internal__exit -> Die) is assumed noreturn while it is evaluated (the greatest
        # fixpoint): every function in it has passed the scan below, so it has no return and no tail jump, and its only
        # way out would be a call in the cycle returning, which needs a return somewhere in the cycle
        _NORET[key] = True
        z = st[a][0][1]; b = s3.frd(I, a, z); r = b is not None
        if r:
            for o, x, n in s3.bc_words(b):
                op, rd = x & 0x7f, (x >> 7) & 31
                if n == 2 or (op == 0x67 and rd == 0) or (op == 0x6f and rd == 0 and not 0 <= o + s3._jal_off(x) < len(b)):
                    r = False; break
            if r and len(b) >= 4:
                o, x, n = s3.bc_words(b)[-1]
                op, rd = x & 0x7f, (x >> 7) & 31
                # the last word must not fall off the end into the next function: an unconditional jump, or a call
                # (whose fall-through leaves the function only if the callee returns: a noreturn callee then)
                if not ((op == 0x6f and rd == 0) or (op == 0x6f and rd and noreturn_last(I, a, o, x)) or
                        x in (0xc0001073, 0x00100073)): r = False      # or unimp / ebreak: a trap
        _NORET[key] = r
    return _NORET[key]

def noreturn_last(I, a, o, x):
    t = a + o + s3._jal_off(x)
    return t != a and noreturn(I, t)

_JT = []
JTARGS = []                                            # [X_ELF, Y_ELF]: set by the main() of every tool that builds Fn
def _jtcheck():
    """the namespace of this record's jtcheck.py (tools/jtcheck.py, from the original sha256 226254f48c97; tools/DIFFS.md: the jtcheck of
    record for table verdicts: Flow, table, same_target, ...), loaded from this directory once (jtcheck reads the two images named on its
    command line when it loads); None when no image paths were given"""
    if not _JT:
        if not JTARGS: return None
        argv = sys.argv[:]
        sys.argv = [os.path.join(HERE, 'jtcheck.py'), JTARGS[0], JTARGS[1], '']
        try: _JT.append(runpy.run_path(os.path.join(HERE, 'jtcheck.py'), run_name='jtcheck_lib'))
        finally: sys.argv = argv
    return _JT[0]

_FLOW = {}
def table_proof(jt, I, w, a, z, i, t, rd):
    """(entry size, count, evidence) that jtcheck 226254f48c97's own proof (Flow.prove: every indexed load off the base
    bounded on every path of its CFG, nothing written through the base, no read past the entries, the base never leaving
    the function) gives for the table at t that the lo12 word i of the function (a, z) of image I addresses, in that
    image alone; None when it refuses. The table bases are those jtcheck's run() gives Flow: a lo12 `addi` whose auipc
    bytecmp's MUST dataflow binds. rd(address, n) reads n file bytes of I. The one table rule of every tool here."""
    key = (id(I), a)
    if key not in _FLOW:
        st_all = jt['dc']._g['bc_states'](w); bs = {}
        for k, (o, x, n) in enumerate(w):
            st = st_all[k]; r1 = (x >> 15) & 31
            if n != 4 or x & 0x7f != 0x13 or (x >> 12) & 7 or not st or r1 not in st: continue
            h = st[r1]
            if h is None or h < 0 or w[h][1] & 0x7f != 0x17: continue
            bs[k] = jt['hi_lo'](a, w, h, x, 0x13)
        _FLOW[key] = jt['Flow'](w, z, a, bs, rd)
    return _FLOW[key].prove(i, t)

def table_proof2(jt, IX, wx, fx, IY, wy, fy, i, tx, ty, rdx, rdy):
    """the shape X and Y BOTH prove for the table at word i (as jtcheck's run() takes it: the two must agree on entry
    size and count), else None"""
    p = table_proof(jt, IX, wx, fx[0], fx[1], i, tx, rdx)
    if p is None: return None
    q = table_proof(jt, IY, wy, fy[0], fy[1], i, ty, rdy)
    return p if q is not None and p[:2] == q[:2] else None

def arms_of(F):
    """(shape e) the jump-table arms of F: every word of F that an entry of a table F addresses lands on. A table is a
    pc-relative target of F outside F and outside .text. Where jtcheck 226254f48c97 proves the table (table_proof), its
    entry size and count are read exactly; otherwise the table is read as 4-byte entries relative to the table start
    (the LLVM RISC-V form, `.word .LBB - .LJTI`) and as 8-byte absolute entries, each up to its first entry that does
    not land on a word of F. An over-approximation (data that happens to land on a word adds an arm): every extra arm
    only adds values, never removes one."""
    out = set()
    for i, t in F.tpc.items():
        if F.a <= t < F.a + F.z: continue
        sec = F.I.sec(t)
        if not sec or sec.startswith('.text'): continue
        jt = _jtcheck()
        shape = table_proof(jt, F.I, F.w, F.a, F.z, i, t, lambda q, n, I=F.I: s3.frd(I, q, n)) if jt else None
        if shape:
            size, cnt, why = shape
            for k in range(cnt):
                e = s3.frd(F.I, t + size * k, size)
                if e is None: break
                v = t + int.from_bytes(e, 'little', signed=True) if size == 4 else int.from_bytes(e, 'little')
                if F.a <= v < F.a + F.z and (v - F.a) in F.idx: out.add(F.idx[v - F.a])
            continue
        for size in (4, 8):
            for k in range(4096):
                e = s3.frd(F.I, t + size * k, size)
                if e is None: break
                v = t + int.from_bytes(e, 'little', signed=True) if size == 4 else int.from_bytes(e, 'little')
                if not (F.a <= v < F.a + F.z) or (v - F.a) not in F.idx: break
                out.add(F.idx[v - F.a])
    return sorted(out)

class Fn:
    """one function's words and CFG: bytecmp's successors (strictcmp3._succ), plus (shape e) an edge from every indirect
    jump to every jump-table arm (arms_of), so an arm that is also reached by fall-through still receives the values
    live at the dispatch; and (shape f) `icall`, each in-function call's target word, whose edge carries the caller's
    registers into the callee (trace(), anchor(), origin())."""
    def __init__(self, I, a, z):
        self.I, self.a, self.z = I, a, z
        self.b = s3.frd(I, a, z); self.w = s3.bc_words(self.b)
        self.idx = {o: i for i, (o, x, n) in enumerate(self.w)}
        self.tpc = {i: t for i, (kd, t) in s3.targets(a, self.b).items()}
        self.jr = [i for i, (o, x, n) in enumerate(self.w) if x & 0x7f == 0x67 and (x >> 7) & 31 == 0 and not s3._isret(x)]
        self.succ = [list(s) for s in s3._succ(self.w)]
        # a direct call to a function that never returns (noreturn(): no return and no tail jump of any kind) has no
        # edge to its next word: nothing after it is reached from it, and a0 there is not "the return of" the callee
        self.noret = set()
        for i, (o, x, n) in enumerate(self.w):
            if n == 4 and x & 0x7f == 0x6f and (x >> 7) & 31 and not 0 <= o + s3._jal_off(x) < len(self.b):
                if noreturn(I, a + o + s3._jal_off(x)):
                    self.noret.add(i); self.succ[i] = [t for t in self.succ[i] if t != i + 1]
        self.arms = arms_of(self) if self.jr else []
        for i in self.jr: self.succ[i] = sorted(set(self.succ[i]) | set(self.arms))
        self.pr = collections.defaultdict(list)
        for i, ss in enumerate(self.succ):
            for t in ss: self.pr[t].append(i)
        self.roots = sorted(set(range(1, len(self.w))) - {t for ss in self.succ for t in ss})
        self.icall = {}
        for i, (o, x, n) in enumerate(self.w):
            if n == 4 and x & 0x7f == 0x6f and (x >> 7) & 31 and o + s3._jal_off(x) in self.idx:
                self.icall[i] = self.idx[o + s3._jal_off(x)]
        self.sk = {}                                   # (word, base register, imm) -> stack slot, filled by trace()
        self.esc = None                                # stack_escapes(), computed once
    def pc(self, i): return '+%#x' % self.w[i][0]
    def callee(self, i):
        t = self.tgt(i)
        return s3.qres(self.I, t) if t is not None else None
    def tgt(self, i):
        """the absolute address a direct jal at word i calls, or an auipc + jalr pair (the kit's targets) jumps to;
        else None"""
        o, x, n = self.w[i]
        if x & 0x7f == 0x6f: return self.a + o + s3._jal_off(x)
        if x & 0x7f == 0x67 and i in self.tpc: return self.tpc[i]
        return None

def stack_escapes(F):
    """(shape d; the egress review's R1) where the ADDRESS of a stack object leaves F: {entry-relative offset of the
    escaping pointer, or None (unknown offset): the first evidence}. A forward MAY analysis over F's CFG (jump-table and
    in-function call edges included) of the registers that hold a pointer into F's frame: sp at entry is offset 0; addi
    keeps the offset; add / sub / sh*add / any other ALU op on such a pointer gives an unknown offset; a pointer stored
    into a stack slot is followed into that slot's reloads (the slots: flow-insensitive). The pointer ESCAPES when it is
    live in a0-a7 at a call or a tail jump (or a0-a5 at an ecall), stored anywhere but a known stack slot, written by an
    AMO, moved into an FP register or a CSR, or returned in a0 / a1. After a call, a0 / a1 may be any pointer the call
    was given. A store of a traced value into slot S is a SPILL only when no escaping pointer has an offset E <= S (the
    object it points to may extend up over S) and none has an unknown offset (slot_escape)."""
    if F.esc is not None: return F.esc
    ins = {0: {2: frozenset({0})}}; slots = {}; esc = {}
    def note(offs, i, why, kind='other', reg=None):
        ev = {'i': i, 'kind': kind, 'reg': reg, 'tgt': F.tgt(i) if kind == 'call' else None,
              'text': '%s `%s` (%s)' % (F.pc(i), text(F.w[i][1], F.w[i][0]), why)}
        for e in offs:
            l = esc.setdefault(e, [])
            if not any(x['i'] == i and x['reg'] == reg for x in l): l.append(ev)
    def cap(v): return v if len(v) <= 16 else frozenset({None})
    while True:
        work = sorted(ins, reverse=True); seen_slots = dict(slots)     # every reached word again when the slots grew
        while work:
            i = work.pop(); S = ins[i]; o, x, n = F.w[i]; op, rd, f3, r1, r2, f7 = dec(x)
            out = dict(S); imm = s3._lo12(x); pre = None
            if op == 0x13 and f3 == 0:
                if r1 in S: out[rd] = cap(frozenset(None if e is None else e + imm for e in S[r1]))
                else: out.pop(rd, None)
            elif op in (0x13, 0x1b):
                if r1 in S: out[rd] = frozenset({None})
                else: out.pop(rd, None)
            elif op in (0x33, 0x3b):
                if r1 in S or r2 in S: out[rd] = frozenset({None})
                else: out.pop(rd, None)
            elif op == 0x03:
                v = frozenset()
                if r1 in S:
                    for e in S[r1]:
                        if e is None: v = v.union(*slots.values()) if slots else v
                        elif e + imm in slots: v = v | slots[e + imm]
                if v: out[rd] = cap(v)
                else: out.pop(rd, None)
            elif op == 0x23:
                if r2 in S:
                    if r1 in S and None not in S[r1]:
                        for e in S[r1]: slots[e + imm] = cap(slots.get(e + imm, frozenset()) | S[r2])
                    else: note(S[r2], i, 'stored to memory', 'store')
            elif op == 0x2f:
                if r2 in S: note(S[r2], i, 'an AMO data operand')
                out.pop(rd, None)
            elif op == 0x53:
                if (x >> 27) in (0x1a, 0x1e) and r1 in S: note(S[r1], i, 'moved into an FP register')
                wr = s3._writes(x)
                if wr: out.pop(wr, None)
            elif op == 0x73:
                if f3 == 0:
                    for r in range(10, 16):
                        if r in S: note(S[r], i, '%s at an ecall' % RN[r], 'ecall', r)
                    out.pop(10, None)
                elif f3 in (1, 2, 3) and r1 in S: note(S[r1], i, 'written into a CSR')
                wr = s3._writes(x)
                if wr: out.pop(wr, None)
            elif op == 0x67 and s3._isret(x):
                fnm = s3.qres(F.I, F.a); fnm = fnm[:-4] if fnm and fnm.endswith('+0x0') else fnm
                rt = CITE_REF[0].get('ret', fnm, '-') if CITE_REF else None
                if not (rt is not None and rt[0].strip() == 'void'):     # a void return hands the caller no value
                    for r in (10, 11):
                        if r in S: note(S[r], i, 'returned in %s' % RN[r], 'ret', r)
            elif op in (0x6f, 0x67) and (rd or (op == 0x6f and not 0 <= o + s3._jal_off(x) < len(F.b)) or
                                          (op == 0x67 and not F.arms)):
                passed = frozenset()
                cpt = prototype((F.callee(i) or '')[:-4] if (F.callee(i) or '').endswith('+0x0') else (F.callee(i) or ''))
                for r in s3.ARGS:
                    if r in S:
                        # a register past the callee's parameters that the callee (and what it calls first) never reads
                        # does not hand it the pointer (the NOTARG measurement)
                        if (cpt is not None and not cpt[1] and r - 10 >= len(cpt[0]) and F.tgt(i) is not None and
                                i not in F.icall and reads_deep(F.I, F.tgt(i), r) is False): continue
                        passed |= S[r]; note(S[r], i, '%s passed to %s' % (RN[r], F.callee(i) or 'a register-indirect call'), 'call', r)
                if i in F.icall: pre = dict(S); pre.pop(rd, None)
                rf = ret_forms(F.I, F.tgt(i)) if (passed and rd and i not in F.icall) else None
                ccn = (F.callee(i) or '')[:-4] if (F.callee(i) or '').endswith('+0x0') else (F.callee(i) or '')
                crt = CITE_REF[0].get('ret', ccn, '-') if CITE_REF and ccn else None
                if crt is not None and crt[0].strip() == 'void': rf = {10: (), 11: ()}    # a void callee returns no value
                for r in CS: out.pop(r, None)
                if passed:
                    # a0 / a1 after the call: what the callee's returns measure (ret_forms), mapped back through the
                    # registers it was given; any unknown return form keeps every pointer the call was given
                    for r in (10, 11):
                        v = frozenset()
                        for fm in (rf[r] if rf is not None else ('unknown',)):
                            if fm == 'unknown': v |= passed
                            elif fm[0] == 'param' and fm[1] in S: v |= frozenset(None if e is None else e + fm[2] for e in S[fm[1]])
                        if v: out[r] = cap(v)
            else:
                wr = s3._writes(x)
                if wr: out.pop(wr, None)
            if 2 not in out: out[2] = frozenset({None})
            out.pop(0, None)
            for t in F.succ[i]:
                src = pre if pre is not None and t == F.icall.get(i) and t != i + 1 else out
                old = ins.get(t)
                new = dict(old) if old else {}
                for r, v in src.items(): new[r] = cap(new.get(r, frozenset()) | v)
                if new != old: ins[t] = new; work.append(t)
        if slots == seen_slots: break
    F.esc = esc
    return esc

CITE_REF = []                                          # [Cite] set by main(): the cited return types (void returns)
_RETF = {}
def ret_forms(I, a, depth=0):
    """{10: forms, 11: forms} of what the function at a leaves in a0 / a1 at its returns: ('param', register, offset)
    for a value it received unwritten (plus an offset), or 'unknown'; a form that cannot be a frame pointer (a number,
    a symbol, the stack of the callee, a load narrower than 8 bytes) is left out. A tail jump to a function returns that
    function's forms, mapped back through the registers at the jump (3 jumps deep). None when a cannot be read."""
    st = STARTS.get(id(I), {})
    if a is None or a not in st: return None
    key = (id(I), a)
    if key in _RETF: return _RETF[key]
    _RETF[key] = {10: ('unknown',), 11: ('unknown',)}  # recursion: unknown
    b = s3.frd(I, a, st[a][0][1])
    if b is None or any(n == 2 for o, x, n in s3.bc_words(b)): return _RETF[key]
    F = Fn(I, a, st[a][0][1]); out = {10: set(), 11: set()}
    def add(r, fs):
        for fm in fs:
            if fm[0] == 'param': out[r].add(('param', fm[1], fm[2]))
            elif fm[0] in ('num', 'sym', 'stack', 'gp', 'tls'): pass
            elif fm[0] == 'load' and re.search(r'`(lb|lbu|lh|lhu|lw|lwu) ', fm[1]): pass
            else: out[r].add('unknown')
    for i, (o, x, n) in enumerate(F.w):
        op, rd = x & 0x7f, (x >> 7) & 31
        if s3._isret(x):
            for r in (10, 11): add(r, anchor(F, i, r))
        elif op == 0x6f and rd == 0 and not 0 <= o + s3._jal_off(x) < len(F.b):
            sub = ret_forms(I, F.tgt(i), depth + 1) if depth < 3 else None
            for r in (10, 11):
                if sub is None: out[r].add('unknown'); continue
                for fm in sub[r]:
                    if fm == 'unknown': out[r].add('unknown')
                    else: add(r, {(f2[0], f2[1], f2[2] + fm[2]) if f2[0] == 'param' else f2 for f2 in anchor(F, i, fm[1])})
        elif op == 0x67 and rd == 0 and not s3._isret(x) and not F.arms:
            out[10].add('unknown'); out[11].add('unknown')
    _RETF[key] = {r: tuple(sorted(v, key=repr)) for r, v in out.items()}
    return _RETF[key]

def slot_escape(F, sk):
    """the evidence that the stack slot at entry-relative offset sk lies in a frame object whose address leaves F
    (stack_escapes), or None when the slot is private to F"""
    esc = stack_escapes(F)
    if None in esc: return 'a pointer into the frame with an unknown offset leaves at %s' % esc[None][0]['text']
    cov = [e for e in esc if e is not None and e <= sk]
    if not cov: return None
    e = max(cov)
    return 'the frame object at sp%+d (at entry) leaves at %s' % (e, esc[e][0]['text'])

def covering_escapes(F, sk):
    """every escape event whose pointer may cover the stack slot sk: [(entry-relative offset or None, event)]"""
    esc = stack_escapes(F)
    return [(e, ev) for e, evs in sorted(esc.items(), key=lambda kv: (kv[0] is not None, kv[0] or 0))
            if e is None or e <= sk for ev in evs]

_WRONLY = {}
def writer_only(I, a):
    """the number of instructions of the function at a when it cannot read memory (no load, AMO, ecall / CSR or call
    of any kind in it, no 2-byte parcel: measured on its words); 0 otherwise"""
    st = STARTS.get(id(I), {})
    if a not in st: return 0
    key = (id(I), a)
    if key not in _WRONLY:
        b = s3.frd(I, a, st[a][0][1])
        ws = s3.bc_words(b) if b is not None else []
        _WRONLY[key] = 0 if b is None or any(
            n == 2 or x & 0x7f in (0x03, 0x07, 0x2f, 0x73) or (x & 0x7f == 0x6f and (x >> 7) & 31) or
            (x & 0x7f == 0x67 and not s3._isret(x)) or (x & 0x7f == 0x6f and not 0 <= o + s3._jal_off(x) < len(b))
            for o, x, n in ws) else len(ws)
    return _WRONLY[key]
INT_FIELD = {'u8': 1, 's8': 1, 'u16': 2, 's16': 2, 'u32': 4, 's32': 4, 'u64': 8, 's64': 8, 'int': 4, 'bool': 1,
             'unsigned': 4, 'char': 1, 'short': 2, 'long': 8}

def callee_reads(I, a, reg, lo, hi, depth=0, seen=()):
    """the loads in the function at a (and, to 3 calls deep, in the callees it passes the same pointer to) whose address
    is the pointer it received in reg plus an offset in [lo, hi): ['name+pc `insn`']"""
    st = STARTS.get(id(I), {})
    if a not in st or depth > 3 or a in seen: return []
    F = Fn(I, a, st[a][0][1]); nm = s3.qres(I, a); nm = nm[:-4] if nm.endswith('+0x0') else nm
    out = []
    for k, (o, x, n) in enumerate(F.w):
        op = x & 0x7f
        if op in (0x03, 0x07):
            fs = anchor(F, k, (x >> 15) & 31, s3._lo12(x))
            wd = 1 << ((x >> 12) & 3)
            for fm in fs:
                if fm[0] == 'param' and fm[1] == reg and fm[2] < hi and fm[2] + wd > lo:
                    out.append('%s%s `%s`' % (nm, F.pc(k), text(x, o))); break
        elif op == 0x6f and ((x >> 7) & 31 or not 0 <= o + s3._jal_off(x) < len(F.b)) and F.tgt(k) is not None and k not in F.icall:
            for r in s3.ARGS:
                for fm in anchor(F, k, r, 0):
                    if fm[0] == 'param' and fm[1] == reg:
                        out += callee_reads(I, F.tgt(k), r, lo - fm[2], hi - fm[2], depth + 1, seen + (a,))
    return out

def iv_settle(C, F, sk, w):
    """a store of a traced value into the stack slot sk, w bytes, of a frame object whose address leaves F. Every
    escape that may cover the slot must be a direct call; for each one the record measures either
      'unread': the callee cannot read memory at all (writer_only: no load, AMO, ecall or call in it), or
      'below': the callee receives a cited struct that ends below the slot, or
      'struct': the callee receives the pointer as a parameter the pinned source types as a cited struct, inside which the
                stored bytes are integer, non-address members or padding (cite-extra.tsv `param` / `field` / `size`
                rows); the evidence lists the members, their citations and the callee's loads of them.
    -> (kinds, evidence) with kinds the set of those words, or (None, why) when an escape is none of them."""
    evs = covering_escapes(F, sk); parts = []; kinds = set()
    if not evs: return None, 'no escape covers the slot'
    for E, ev in evs:
        if E is None: return None, 'a frame pointer with an unknown offset leaves at %s' % ev['text']
        if ev['kind'] != 'call' or ev['tgt'] is None:
            return None, 'the frame object at sp%+d leaves at %s: no typed reader to cite' % (E, ev['text'])
        cn = s3.qres(F.I, ev['tgt']); cn = cn[:-4] if cn and cn.endswith('+0x0') else cn
        nw = writer_only(F.I, ev['tgt'])
        if nw:
            kinds.add('unread')
            parts.append('%s: %s has %d instructions in this image, none a load, AMO, ecall or call' % (F.pc(ev['i']), cn, nw))
            continue
        p = C.get('param', cn, RN[ev['reg']])
        if p is None: return None, 'the frame object at sp%+d is passed in %s to %s, which has no cited struct parameter there' % (E, RN[ev['reg']], cn)
        struct = p[0]; sz = C.get('size', struct, '-'); f = sk - E
        if sz is None: return None, 'no cited size for %s' % struct
        if f >= int(sz[0]):
            kinds.add('below'); parts.append('%s: %s (%s, %s bytes) ends below the slot' % (F.pc(ev['i']), struct, p[1], sz[0])); continue
        cover = []
        for b in range(f, f + w):
            fl = None
            for off in range(b, -1, -1):
                r = C.get('field', struct, str(off))
                if r is not None:
                    if off + INT_FIELD.get(r[0], 0) > b: fl = (off, r)
                    break
            if fl is None:
                if b >= int(sz[0]): return None, 'the store runs past the end of %s' % struct
                cover.append(None); continue                      # padding
            if r[0] not in INT_FIELD: return None, '%s+%d is `%s %s`, not an integer field' % (struct, fl[0], r[0], r[1])
            if fl not in cover: cover.append(fl)
        named = [c for c in cover if c is not None]
        rd = callee_reads(F.I, ev['tgt'], ev['reg'], f, f + w)
        kinds.add('struct')
        parts.append('%s: %s receives it as `%s %s` [%s]; bytes %d..%d are %s%s; its reads of them: %s' % (
            F.pc(ev['i']), cn, struct, p[1], p[2], f, f + w - 1,
            ', '.join('`%s %s` [%s]' % (c[1][0], c[1][1], c[1][2]) for c in named),
            ' and padding' if None in cover else '', '; '.join(rd[:6]) or 'none (it does not read them)'))
    return kinds, ' | '.join(parts)

def origin(F, k, reg, depth=0):
    """the anchors reg may hold at word k: ('sym', address) / ('ptr', why) / ('lui', value) / ('num', why); by reaching
    definitions over the CFG with its jump-table and in-function call edges (the same edge rules as anchor())"""
    def entry(r):
        return (('ptr', 'parameter %s' % RN[r]) if 10 <= r <= 17 else ('ptr', 'a stack address') if r == 2
                else ('num', 'entry %s' % RN[r]))
    out = set()
    if k == 0: out.add(entry(reg))
    elif not F.pr[k]: return {('num', 'a word no decoded edge reaches')}
    work = [(j, k) for j in F.pr[k]]; vis = set()
    while work:
        j, kk = work.pop()
        if (j, kk) in vis: continue
        vis.add((j, kk))
        o, x, n = F.w[j]; op, rd, f3, r1, r2, f7 = dec(x)
        if op in (0x6f, 0x67) and rd:
            if F.icall.get(j) == kk and kk != j + 1:
                if reg == rd: out.add(('num', 'the return address of the in-function call at %s' % F.pc(j))); continue
                if j == 0: out.add(entry(reg))
                work += [(p, j) for p in F.pr[j]]; continue
            if reg in CS:
                out.add(('ptr', 'the return of %s' % ((F.callee(j) or '?')[:-4] if op == 0x6f else 'a register-indirect call'))
                        if reg == 10 else ('num', 'clobbered by the call at %s' % F.pc(j))); continue
        if s3._writes(x) == reg and reg:
            if j in F.tpc:
                t = F.tpc[j]
                if F.I.sec(t) == '.got':
                    c = s3.frd(F.I, t, 8); t = int.from_bytes(c, 'little') if c else 0
                    out.add(('ptr', 'loaded from the .got: the address of %s' % s3.qres(F.I, t)) if op == 0x03 else ('sym', t))
                else: out.add(('sym', t) if op != 0x03 else ('ptr', 'a value loaded by `%s` at %s' % (text(x, o), F.pc(j))))
            elif op == 0x13 and f3 == 0 and r1 == 2: out.add(('ptr', 'a stack address'))
            elif op in (0x13, 0x1b) and f3 == 0 and r1 == 0: out.add(('lui', sxv(x >> 20, 12) & M64))   # li: a number
            elif op in (0x13, 0x1b) and f3 == 0 and r1 and depth < 6: out |= origin(F, j, r1, depth + 1)
            elif op == 0x03: out.add(('ptr' if f3 == 3 else 'num', 'a value loaded by `%s` at %s' % (text(x, o), F.pc(j))))
            elif op == 0x37: out.add(('lui', (sxv(x >> 12, 20) << 12) & M64))
            else: out.add(('num', 'computed by `%s` at %s' % (text(x, o), F.pc(j))))
            continue
        if j == 0: out.add(entry(reg))
        elif not F.pr[j]: out.add(('num', 'a word no decoded edge reaches'))
        work += [(p, j) for p in F.pr[j]]
    return out

def reach_from(F, src, dst):
    """is word dst reachable from word src over F's successors (src itself counts)?"""
    seen = set(); work = [src]
    while work:
        i = work.pop()
        if i == dst: return True
        if i in seen: continue
        seen.add(i); work += F.succ[i]
    return False

def live_after(F, k, reg):
    """is reg read after word k (a call) before it is written, on some path in F?"""
    seen = set(); work = list(F.succ[k])
    while work:
        i = work.pop()
        if i in seen: continue
        seen.add(i)
        o, x, n = F.w[i]; op, rd, f3, r1, r2, f7 = dec(x)
        rr = set(s3._raw_reads(x))
        if s3._lo12(x) is not None and r1: rr.add(r1)
        if s3._isret(x): rr |= {10, 11}
        elif op == 0x67 or (op == 0x6f and (rd or not 0 <= o + s3._jal_off(x) < len(F.b))): rr |= set(s3.ARGS)
        if reg in rr: return True
        if s3._writes(x) == reg or (op in (0x6f, 0x67) and rd and reg in CS): continue
        work += F.succ[i]
    return False

STARTS = {}          # id(image) -> {address: [(name, size)]}: set by main(), read by the call rule of trace()
_CLOB = {}
def clobbers(Im, a, reg):
    """does the function at address a WRITE reg on every path from its entry to every return (a must-analysis over its
    CFG; a call inside it counts as a write of a0 / a1 only)? True / False; None when the function cannot be read"""
    st = STARTS.get(id(Im), {})
    if a is None or a not in st: return None
    key = (id(Im), a, reg)
    if key in _CLOB: return _CLOB[key]
    z = st[a][0][1]; b = s3.frd(Im, a, z)
    if b is None or any(n == 2 for o, x, n in s3.bc_words(b)):
        _CLOB[key] = None; return None
    F = Fn(Im, a, z)
    N = len(F.w)
    def wr(i, t=None):
        """does word i write reg on its edge to word t? (an in-function call writes only ra on the edge to its target)"""
        o, x, n = F.w[i]; op, rd, f3, r1, r2, f7 = dec(x)
        if s3._writes(x) == reg and reg: return True
        if t is not None and F.icall.get(i) == t and t != i + 1: return False
        return op in (0x6f, 0x67) and rd and reg in (10, 11)
    # written_in[i]: reg was written on EVERY path from the entry to word i (exclusive); entry: False
    win = [True] * N; win[0] = False
    changed = True
    while changed:
        changed = False
        for i in range(N):
            if i == 0: continue
            ps = F.pr.get(i, [])
            # a word with no predecessor may be reached without the write: conservatively not written
            v = all(win[p] or wr(p, i) for p in ps) if ps else False
            if v != win[i]: win[i] = v; changed = True
    ok = True
    for i, (o, x, n) in enumerate(F.w):
        op, rd = x & 0x7f, (x >> 7) & 31
        # the function's exits: a return, a tail jump out of it, or any indirect jump (a tail call through a register;
        # a jump-table dispatch is counted too, which can only make the answer False)
        tail = (op == 0x6f and rd == 0 and not 0 <= o + s3._jal_off(x) < len(F.b)) or (op == 0x67 and rd == 0)
        if (s3._isret(x) or tail) and not (win[i] or (wr(i) and not tail)): ok = False; break
    _CLOB[key] = ok
    return ok

SHAPE = collections.Counter()     # per shape (a)-(h): how often the trace used the rule for it (printed as `# SHAPES`)
_DEEP = {}
UNKNOWN_PROTO = collections.Counter()      # nested callees reads_deep met with no prototype (each a read)
def reads_deep(Im, a, reg, depth=0, stack=()):
    """does the function at a read reg (as received) on some path before writing it? Like reads_in, but a direct call
    inside it is followed: it reads reg only if reg is one of the nested callee's parameters (its mangled name), the
    nested callee is variadic or unknown, or the nested callee itself reads it (recursively, to depth 4); after the call
    the path goes on only if the nested callee does not write reg on every path (clobbers()). A register-indirect call,
    a function that cannot be read, recursion or depth 5 count as a read (fail-closed). At a return, a0 / a1 count as
    read (the value goes back to the caller); any other register leaves the callee unread."""
    st = STARTS.get(id(Im), {})
    if a is None or a not in st or depth > 4 or a in stack: return True
    key = (id(Im), a, reg)
    if key in _DEEP: return _DEEP[key]
    z = st[a][0][1]; b = s3.frd(Im, a, z)
    if b is None or any(n == 2 for o, x, n in s3.bc_words(b)):
        _DEEP[key] = True; return True
    F = Fn(Im, a, z)
    seen = set(); work = [0]; res = False
    while work:
        i = work.pop()
        if i in seen: continue
        seen.add(i)
        o, x, n = F.w[i]; op, rd, f3, r1, r2, f7 = dec(x)
        rr = set(s3._raw_reads(x))
        if s3._lo12(x) is not None and r1: rr.add(r1)
        if s3._isret(x):
            if reg in (10, 11): res = True; break
            continue
        if op == 0x73 and f3 == 0:
            # an ecall reads a7 and the syscall's own argument registers (SYSCALL, by the a7 constant); an unknown
            # syscall number reads every argument register. It writes a0.
            nr = const_of(F, i, 17); sc = SYSCALL.get(nr)
            if reg == 17 or sc is None or reg - 10 < sc[1]: res = True; break
            if reg == 10: continue
            work += F.succ[i]; continue
        if op == 0x67:
            if reg in rr: res = True; break
            if rd == 0 and (F.arms or F.roots): work += F.succ[i] + F.roots; continue   # a jump-table dispatch
            res = True; break                                           # a register-indirect call or tail jump
        if op == 0x6f and (rd or not 0 <= o + s3._jal_off(x) < len(F.b)):
            ta = a + o + s3._jal_off(x)
            nm = s3.qres(Im, ta); nm = nm[:-4] if nm.endswith('+0x0') else nm
            pt = prototype(nm)
            if pt is None: UNKNOWN_PROTO[nm] += 1
            if pt is None or pt[1] or reg - 10 < len(pt[0]): res = True; break
            if reads_deep(Im, ta, reg, depth + 1, stack + (a,)): res = True; break
            if not rd: continue                                         # a tail call: the path ends there
            if clobbers(Im, ta, reg) is True: continue
            work += F.succ[i]; continue
        if reg in rr: res = True; break
        if s3._writes(x) == reg: continue
        work += F.succ[i]
    _DEEP[key] = res
    return res

def alu(m, a, b):
    """(shape c) the value of R-type op m on two known numbers (64-bit; a `w` op on the low 32 bits, sign-extended);
    None for an op this table does not compute"""
    if m == 'add.uw': return ((a & 0xffffffff) + b) & M64
    w = m.endswith('w')
    base = m[:-1] if w else m
    if base in ('sh1add', 'sh2add', 'sh3add'): v = ((a << int(base[2])) + b)
    elif base == 'add': v = a + b
    elif base == 'sub': v = a - b
    elif base == 'and': v = a & b
    elif base == 'or': v = a | b
    elif base == 'xor': v = a ^ b
    elif base == 'sll': v = a << (b & (31 if w else 63))
    elif base == 'srl': v = ((a & 0xffffffff) if w else a) >> (b & (31 if w else 63))
    elif base == 'sra': v = sxv((a & 0xffffffff) if w else a, 32 if w else 64) >> (b & (31 if w else 63))
    elif base == 'slt': v = int(sxv(a, 64) < sxv(b, 64))
    elif base == 'sltu': v = int(a < b)
    elif base == 'mul': v = a * b
    elif base in ('div', 'divu', 'rem', 'remu'):
        # RISC-V M: the w forms work on the low 32 bits; division by zero gives all ones (div / divu) or the dividend
        # (rem / remu); signed overflow gives the dividend (div) or 0 (rem)
        bits = 32 if w else 64; msk = (1 << bits) - 1
        ua, ub = a & msk, b & msk
        sa, sb = sxv(ua, bits), sxv(ub, bits)
        if base == 'divu': v = msk if ub == 0 else ua // ub
        elif base == 'remu': v = ua if ub == 0 else ua % ub
        elif ub == 0: v = msk if base == 'div' else ua
        elif sa == -(1 << (bits - 1)) and sb == -1: v = ua if base == 'div' else 0
        else:
            q = abs(sa) // abs(sb) * (1 if (sa < 0) == (sb < 0) else -1)
            v = q if base == 'div' else sa - q * sb
    else: return None
    return (sxv(v & 0xffffffff, 32) & M64) if w else v & M64

def imm_op(x, an, c):
    """(shape c) the form of an OP-IMM other than addi / addiw (slli, slti, sltiu, xori, srli, srai, ori, andi and the
    -w shifts) on a value of form (an, c): exact when the value is a known number; any anchored or unknown value gives an
    unknown number, so a base built from it is NOT CERTIFIED, never EQUAL"""
    if an is not None or c is None: return (None, None)
    op, f3 = x & 0x7f, (x >> 12) & 7
    imm = sxv(x >> 20, 12) & M64; sh = (x >> 20) & 63
    if op == 0x13:
        v = {1: c << sh, 2: int(sxv(c, 64) < sxv(imm, 64)), 3: int(c < imm), 4: c ^ imm,
             5: (sxv(c, 64) >> sh) if (x >> 30) & 1 else (c >> sh), 6: c | imm, 7: c & imm}[f3]
        return (None, v & M64)
    sh &= 31
    lo = c & 0xffffffff
    v = {1: lo << sh, 5: (sxv(lo, 32) >> sh) if (x >> 30) & 1 else (lo >> sh)}.get(f3)
    return (None, sxv(v & 0xffffffff, 32) & M64) if v is not None else (None, None)

def combine(A, B, m):
    """the symbolic forms of `m rd, A, B` -> set of (anchor, constant)"""
    out = set()
    for (an1, c1) in A:
        for (an2, c2) in B:
            if m in ('add', 'addw', 'sh1add', 'sh2add', 'sh3add', 'add.uw') and (an1 is not None or an2 is not None):
                sh = {'sh1add': 1, 'sh2add': 2, 'sh3add': 3}.get(m, 0)
                an = [z for z in (an1, an2) if z is not None]
                if len(an) > 1 or (sh and an1 is not None): out.add((('ptr', 'two anchors or a scaled anchor'), None)); continue
                c = None if c1 is None or c2 is None else ((c1 << sh) + c2) & M64
                out.add((an[0], c))
            elif m in ('sub', 'subw') and an1 is not None and an2 is None:
                out.add((an1, None if c1 is None or c2 is None else (c1 - c2) & M64))
            elif an1 is None and an2 is None and c1 is not None and c2 is not None:
                out.add((None, alu(m, c1, c2)))                     # (shape c) two known numbers: exact
            else: out.add((None, None))
    return frozenset(out)

def trace(F, j, plant_note=''):
    """events for the lui at word j: [(word, kind, detail, forms)]"""
    o0, x0, n0 = F.w[j]; rd0 = dec(x0)[1]; v0 = (sxv(x0 >> 12, 20) << 12) & M64
    ins = collections.defaultdict(dict); ev = []; evk = set(); slots = {}
    for t in F.succ[j]: ins[t] = {rd0: frozenset({(None, v0)})}
    work = list(F.succ[j]); reseeded = set()
    shapes_seen = set()
    def seen_shape(k, where):
        if (k, where) not in shapes_seen: shapes_seen.add((k, where)); SHAPE[k] += 1
    def add_ev(i, kind, det, forms):
        key = (i, kind, det)
        if key not in evk: evk.add(key); ev.append((i, kind, det, forms))
    def anchors_of(i, r):
        out = set()
        for an in origin(F, i, r):
            if an[0] == 'sym': out.add((('sym', an[1]), 0))
            elif an[0] == 'lui': out.add((None, an[1]))
            elif an[0] == 'ptr': out.add((('ptr', an[1]), None))
            else: out.add((None, None))
        return frozenset(out)
    def slot(i, r, imm):
        """(shape d) the stack slot a load / store at word i addresses through base register r + imm: its offset from sp
        at the function's entry, when anchor() gives exactly one stack form (sp, or s0 / any register built from sp by
        addi chains); else None"""
        key = (i, r, imm)
        if key not in F.sk:
            fs = anchor(F, i, r, imm)
            F.sk[key] = next(iter(fs))[2] if len(fs) == 1 and next(iter(fs))[0] == 'stack' else None
        return F.sk[key]
    while True:
        while work:
            i = work.pop(); S = ins[i]; o, x, n = F.w[i]; op, rd, f3, r1, r2, f7 = dec(x)
            out = dict(S); T = lambda r: S.get(r)
            imm = s3._lo12(x)
            reloaded = False
            if op in (0x03, 0x07) and r1 in S:
                add_ev(i, 'base', text(x, o), frozenset((a, None if c is None else (c + imm) & M64) for a, c in S[r1]))
                seen_shape('a: load base, the immediate added (V+imm)', i)
            if op in (0x23, 0x27):
                if r1 in S:
                    add_ev(i, 'base', text(x, o), frozenset((a, None if c is None else (c + imm) & M64) for a, c in S[r1]))
                    seen_shape('a: store base, the immediate added (V+imm)', i)
                if op == 0x23 and r2 in S:                          # an FP store's data is an FP register: never a traced value
                    sk = slot(i, r1, imm)
                    if sk is not None:
                        slots[sk] = slots.get(sk, frozenset()) | S[r2]          # its reloads are followed either way
                        esc = slot_escape(F, sk)
                        if esc is None:
                            seen_shape('d: spill to a private stack slot through %s' % ('sp' if r1 == 2 else 'a register built from sp (%s)' % RN[r1]), i)
                            add_ev(i, 'spill', '%s (private stack slot sp%+d at entry; followed into its reloads)' % (text(x, o), sk), S[r2])
                        else:
                            # (the unit owner's ruling, review R1) the slot lies in a frame object whose address leaves the
                            # function: its reader (a callee or the kernel) is not traced, so this is a STORE row
                            seen_shape('d: store into a stack slot whose frame object escapes (a STORE row)', i)
                            add_ev(i, 'store', '%s (%d-byte store into the stack slot sp%+d at entry; %s)'
                                   % (text(x, o), 1 << (f3 & 3), sk, esc), S[r2])
                    else: add_ev(i, 'store', '%s (%d-byte store)' % (text(x, o), 1 << (f3 & 3)), S[r2])
            if op == 0x2f:
                if r1 in S: add_ev(i, 'base', 'AMO address: ' + text(x, o), S[r1])
                if r2 in S: add_ev(i, 'amo', 'AMO data operand: ' + text(x, o), S[r2])
            if op == 0x53 and (x >> 27) in (0x1a, 0x1e) and r1 in S:
                add_ev(i, 'fpmove', 'moved into an FP register: op%#x funct5 %#x' % (op, x >> 27), S[r1]); seen_shape('d: FP move (a NOT CERTIFIED row)', i)
            if op == 0x73 and f3 in (1, 2, 3) and r1 in S:
                add_ev(i, 'csr', 'written into CSR %#x' % (x >> 20), S[r1]); seen_shape('d: CSR write (a NOT CERTIFIED row)', i)
            if op == 0x63 and (r1 in S or r2 in S): add_ev(i, 'cmp', text(x, o), None)
            if op in (0x33, 0x3b) and (r1 in S or r2 in S):
                m = text(x, o).split(' ')[0]
                A = S.get(r1) or anchors_of(i, r1); B = S.get(r2) or anchors_of(i, r2)
                f = combine(A, B, m); add_ev(i, 'arith', text(x, o), f)
                if m not in ('add', 'addw', 'sh1add', 'sh2add', 'sh3add', 'add.uw', 'sub', 'subw'):
                    seen_shape('c: R-type %s' % ('computed exactly on known numbers' if any(c is not None for a, c in f)
                                                 else 'on an anchored or unknown value -> unknown number'), i)
                if rd: out[rd] = f
            elif op in (0x13, 0x1b) and r1 in S and rd:
                if f3 == 0:
                    seen_shape('b: %s followed, the immediate summed' % ('addi' if op == 0x13 else 'addiw (sign-extended from 32 bits)'), i)
                    out[rd] = frozenset((a, None if c is None else (c + imm) & M64 if op == 0x13 else
                                                  sxv((c + imm) & 0xffffffff, 32) & M64) for a, c in S[r1])
                else:
                    out[rd] = frozenset(imm_op(x, a, c) for a, c in S[r1]); add_ev(i, 'arith', text(x, o), out[rd])
                    if any(c is not None for a, c in out[rd]): seen_shape('c: OP-IMM other than addi computed exactly on a known number', i)
                    else: seen_shape('c: OP-IMM other than addi on an anchored or unknown value -> unknown number', i)
            elif op == 0x73 and f3 == 0:
                for r in range(10, 16):
                    if r in S: add_ev(i, 'ecall', 'a%d live at an ecall' % (r - 10), S[r])
            elif op == 0x67 and s3._isret(x):
                for r in (10, 11):
                    if r in S: add_ev(i, 'ret', 'a%d at a return' % (r - 10), S[r])
            elif (op == 0x6f and (rd or not 0 <= o + s3._jal_off(x) < len(F.b))) or (op == 0x67 and rd) or \
                    (op == 0x67 and not F.arms):
                # a call (an in-function callee too: its arguments are rows here AND followed into it on the call
                # edge below), or a tail jump out of the function (jal zero to another function, or jalr zero that is
                # not a jump-table dispatch: e.g. auipc t1 + jalr zero,lo(t1)): the values in a0-a7 are its arguments
                if op == 0x67 and r1 in S: add_ev(i, 'base', 'jump base: ' + text(x, o), S[r1])
                for r in s3.ARGS:
                    if r in S: add_ev(i, 'arg', 'a%d' % (r - 10), S[r])
            elif op == 0x67 and r1 in S: add_ev(i, 'base', 'jump base: ' + text(x, o), S[r1])
            if op == 0x03 and rd and slots:
                sk = slot(i, r1, imm)
                if sk is not None and sk in slots:
                    reseeded.add((i, sk)); out[rd] = slots[sk]; reloaded = True; seen_shape('d: reload of a spilled value followed', i)
                    add_ev(i, 'reload', '%s (stack slot sp%+d at entry)' % (text(x, o), sk), slots[sk])
            if not reloaded and not (op in (0x33, 0x3b) and (r1 in S or r2 in S)) and not (op in (0x13, 0x1b) and r1 in S):
                wr = s3._writes(x)
                if wr: out.pop(wr, None)
            pre = None
            if i in F.icall:
                pre = dict(S); pre.pop(rd, None); pre.pop(0, None)     # the callee entry: the caller's registers, ra written
            if op in (0x6f, 0x67) and rd:
                # the unit owner's ruling (e): a caller-saved register still holding the value at a call is dead after it only
                # when that is MEASURED: the caller does not read it again before writing it, or the (direct) callee
                # writes it on every path to its return (clobbers(), a must-analysis over the callee's CFG). Otherwise
                # the value is kept and the trace continues in the caller (fail-closed: every row it adds is a row).
                ta = F.tgt(i)
                for r in CS:
                    if r in out and (not live_after(F, i, r) or (ta is not None and clobbers(F.I, ta, r) is True)):
                        out.pop(r, None)
            if op == 0x73 and f3 == 0: out.pop(10, None); out.pop(11, None)
            out.pop(0, None)
            for t in F.succ[i]:
                src = pre if pre is not None and t == F.icall[i] and t != i + 1 else out
                if src and src is pre: seen_shape('f: values carried into an in-function callee', i)
                if src and i in F.jr and t in F.arms and any(p not in F.jr for p in F.pr[t]):
                    seen_shape('e: values carried from a dispatch into an arm that is also reached by fall-through', (i, t))
                new = {r: ins[t].get(r, frozenset()) | src.get(r, frozenset()) for r in ins[t].keys() | src.keys()}
                new = {r: (v if len(v) <= 8 else frozenset({(('ptr', 'many forms'), None)})) for r, v in new.items()}
                if new != ins[t] or t not in ins: ins[t] = new; work.append(t)
        u = {}
        for i in F.jr:
            if i in ins:
                for r, v in ins[i].items(): u[r] = u.get(r, frozenset()) | v
        changed = False
        for t in F.roots:
            new = {r: ins[t].get(r, frozenset()) | u.get(r, frozenset()) for r in ins[t].keys() | u.keys()}
            if u and new != ins.get(t): ins[t] = new; work.append(t); changed = True
        # reloads of a stack slot anywhere in the function (a slot reloaded on a path the flow did not reach, or a slot
        # that gained values after its reload was processed)
        for i, (o, x, n) in enumerate(F.w):
            op, rd, f3, r1, r2, f7 = dec(x)
            if op != 0x03 or not rd or not slots: continue
            sk = slot(i, r1, s3._lo12(x))
            if sk is None or sk not in slots: continue
            if (i, sk) not in reseeded:
                reseeded.add((i, sk)); add_ev(i, 'reload', '%s (stack slot sp%+d at entry)' % (text(x, o), sk), slots[sk])
            for t in F.succ[i]:
                cur = ins[t].get(rd, frozenset()) if t in ins else frozenset()
                new = cur | slots[sk]
                if len(new) > 8: new = frozenset({(('ptr', 'many forms'), None)})
                if new != cur:
                    ins[t] = dict(ins.get(t, {})); ins[t][rd] = new; work.append(t); changed = True
        if not changed: break
    return v0, sorted(ev)

def fmt_forms(F, forms):
    if not forms: return '-'
    out = []
    for an, c in sorted(forms, key=repr):
        if an is None: out.append('number %s' % ('%#x' % c if c is not None else '?'))
        elif an[0] == 'sym': out.append('%s + %s' % (s3.qres(F.I, an[1]), '%#x' % c if c is not None else '?'))
        else: out.append('object pointer (%s) + %s' % (an[1], '%#x' % c if c is not None else '?'))
    return ' | '.join(out)

import ctypes
_lib = ctypes.CDLL('libstdc++.so.6'); _dm = _lib.__cxa_demangle; _dm.restype = ctypes.c_void_p
_dm.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.POINTER(ctypes.c_size_t), ctypes.POINTER(ctypes.c_int)]
NAMESPACES = ('__sanitizer', '__asan', '__lsan', '__ubsan', '__interception', '(anonymous namespace)', 'detail')
# C functions (musl / libc / sanitizer C entry points): parameter types (musl 1.2.5 headers; sanitizer interface)
C_PROTO = {
    'memset': ['void *', 'int', 'size_t'], '__sanitizer_internal_memset': ['void *', 'int', 'uptr'],
    '__sanitizer_internal_memcpy': ['void *', 'const void *', 'uptr'], 'memcpy': ['void *', 'const void *', 'size_t'],
    'snprintf': ['char *', 'size_t', 'const char *', '...'], 'strcmp': ['const char *', 'const char *'],
    'nl_langinfo_l': ['nl_item', 'locale_t'], '__nl_langinfo_l': ['nl_item', 'locale_t'],
    'mmap': ['void *', 'size_t', 'int', 'int', 'int', 'off_t'], '__mmap': ['void *', 'size_t', 'int', 'int', 'int', 'off_t'],
    'mprotect': ['void *', 'size_t', 'int'], '__mprotect': ['void *', 'size_t', 'int'],
    'socket': ['int', 'int', 'int'], 'open': ['const char *', 'int', '...'], 'sched_yield': [],
    '__syscall_ret': ['unsigned long'], '__stack_chk_fail': [], '__stack_chk_fail_local': [],
    '__assert_fail': ['const char *', 'const char *', 'int', 'const char *'], '__errno_location': [], '___errno_location': [],
    '__libc_malloc': ['size_t'], 'sysinfo': ['struct sysinfo *'], '__lsysinfo': ['struct sysinfo *'],
    '__syscall_cp': ['long', 'long', 'long', 'long', 'long', 'long', 'long'], '__malloc_alloc_meta': [],
    'fstatat': ['int', 'const char *', 'struct stat *', 'int'], '__fstatat': ['int', 'const char *', 'struct stat *', 'int'],
    'clock_gettime': ['clockid_t', 'struct timespec *'], '__clock_gettime': ['clockid_t', 'struct timespec *'],
    '__timedwait': ['volatile int *', 'int', 'clockid_t', 'const struct timespec *', 'int'],
    '__year_to_secs': ['long long', 'int *'], '__month_to_secs': ['int', 'int'], '__tm_to_tzname': ['const struct tm *'],
    'getauxval': ['unsigned long'], '__getauxval': ['unsigned long'],
    # POSIX / musl / sanitizer-interface prototypes of callees the call rule meets (parameter counts only)
    'sysconf': ['int'], 'abort': [], 'fcntl': ['int', 'int', '...'], '__vm_wait': [], '__lock': ['volatile int *'],
    'pthread_self': [], '__pthread_self_internal': [], 'thrd_current': [],
    'pthread_getspecific': ['pthread_key_t'], '__pthread_getspecific': ['pthread_key_t'], 'tss_get': ['tss_t'],
    '__libc_malloc_impl': ['size_t'], '__sanitizer_malloc_hook': ['const volatile void *', 'size_t'],
    '__sanitizer_internal_memmove': ['void *', 'const void *', 'uptr'],
    'dl_iterate_phdr': ['int (*)(struct dl_phdr_info *, size_t, void *)', 'void *'],
    'static_dl_iterate_phdr': ['int (*)(struct dl_phdr_info *, size_t, void *)', 'void *'],
    '__wrap___tls_get_addr': ['void *'], '__interceptor_trampoline___tls_get_addr': ['void *'],
    '__wrap_clock_gettime': ['clockid_t', 'struct timespec *'],
    '__interceptor_trampoline_clock_gettime': ['clockid_t', 'struct timespec *'],
    '___interceptor_clock_gettime': ['clockid_t', 'struct timespec *'], '__interceptor_clock_gettime': ['clockid_t', 'struct timespec *'],
    '___interceptor___tls_get_addr': ['void *'], '__interceptor___tls_get_addr': ['void *'],
    '__interceptor_trampoline_memset': ['void *', 'int', 'size_t'], '__wrap_memset': ['void *', 'int', 'size_t'],
    'getrlimit': ['int', 'struct rlimit *'], 'raise': ['int'],
    '__wait': ['volatile int *', 'volatile int *', 'int', 'int'],
}
def demangle(nm):
    st = ctypes.c_int(); p = _dm(nm.encode(), None, None, ctypes.byref(st))
    return ctypes.string_at(p).decode() if st.value == 0 and p else None
def split_params(s):
    out = []; d = 0; cur = ''
    for ch in s:
        if ch in '<(': d += 1
        elif ch in '>)': d -= 1
        if ch == ',' and d == 0: out.append(cur.strip()); cur = ''
        else: cur += ch
    if cur.strip(): out.append(cur.strip())
    return out
def prototype(callee):
    """(argument register types [a0, a1, ...], variadic, evidence) for a callee name, or None"""
    for nm in callee.split('/'):
        nm = nm.split('{')[0]
        if nm in C_PROTO:
            ps = C_PROTO[nm]
            return [p for p in ps if p != '...'], '...' in ps, 'C prototype %s(%s)' % (nm, ', '.join(ps))
        if nm.startswith('_Z'):
            d = demangle(nm)
            if not d: continue
            # the parameter list: the last top-level (...) of the demangled name
            depth = 0; end = len(d) - 1
            while end >= 0 and d[end] != ')': end -= 1
            k = end; depth = 0
            while k >= 0:
                if d[k] == ')': depth += 1
                elif d[k] == '(':
                    depth -= 1
                    if depth == 0: break
                k -= 1
            head, params = d[:k], d[k + 1:end]
            ps = [] if params.strip() in ('', 'void') else split_params(params)
            var = '...' in ps; ps = [p for p in ps if p != '...']
            qual = head.split('<')[0].split('::')
            member = len(qual) >= 2 and qual[-2] not in NAMESPACES and not qual[-2].startswith('(')
            if member: ps = ['this'] + ps
            return ps, var, 'demangled %s%s' % (d, ' (a member: a0 = this)' if member else '')
    return None

SYSCALL = {   # RISC-V 64 (Linux asm-generic/unistd.h): number -> (name, how many argument registers the kernel reads)
    17: ('getcwd', 2), 25: ('fcntl', 3), 29: ('ioctl', 3), 34: ('mkdirat', 3), 35: ('unlinkat', 3),
    46: ('ftruncate', 2), 48: ('faccessat', 4), 56: ('openat', 4), 57: ('close', 1), 61: ('getdents64', 3),
    62: ('lseek', 3), 63: ('read', 3), 64: ('write', 3), 65: ('readv', 3), 66: ('writev', 3), 72: ('pselect6', 6),
    78: ('readlinkat', 4), 79: ('newfstatat', 4), 80: ('fstat', 2), 93: ('exit', 1), 94: ('exit_group', 1),
    96: ('set_tid_address', 1), 98: ('futex', 6), 99: ('set_robust_list', 2), 101: ('nanosleep', 2),
    113: ('clock_gettime', 2), 115: ('clock_nanosleep', 4), 117: ('ptrace', 4), 124: ('sched_yield', 0),
    129: ('kill', 2), 130: ('tkill', 2), 131: ('tgkill', 3), 134: ('rt_sigaction', 4), 135: ('rt_sigprocmask', 4),
    160: ('uname', 1), 167: ('prctl', 5), 169: ('gettimeofday', 2), 172: ('getpid', 0), 173: ('getppid', 0),
    174: ('getuid', 0), 175: ('geteuid', 0), 178: ('gettid', 0), 179: ('sysinfo', 1), 198: ('socket', 3),
    206: ('sendto', 6), 214: ('brk', 1), 215: ('munmap', 2), 220: ('clone', 5), 222: ('mmap', 6),
    226: ('mprotect', 3), 233: ('madvise', 3), 260: ('wait4', 4), 261: ('prlimit64', 4), 278: ('getrandom', 3),
    283: ('membarrier', 3),
}

def entry_value(reg, off):
    """what reg holds at the function's entry: a parameter (a0-a7), the stack pointer, gp / tp, else unknown"""
    if 10 <= reg <= 17: return ('param', reg, off)
    if reg == 2: return ('stack', 'sp at entry', off)
    if reg == 3: return ('gp', '__global_pointer$', off)
    if reg == 4: return ('tls', 'tp', off)
    return ('other', 'entry value of %s' % RN[reg])

def anchor(F, k, reg, off=0, depth=0):
    """what reg may hold at word k, with the constant added to it: a set of ('param', register, offset) a value the
    function received unwritten | ('stack', 'sp at entry', offset) | ('gp', ..., offset) | ('tls', 'tp', offset) |
    ('ret', callee, offset) | ('load', where, offset) | ('sym', address, offset) a pc-relative or .got target |
    ('num', value, offset) | ('other', why). Reaching definitions backwards over the CFG with its jump-table and
    in-function call edges, following addi / addiw / mv and summing the immediates. Word 0 is the function's entry (its
    entry values join whatever reaches it by an edge); another word no edge reaches is unknown. On the edge from an
    in-function call to its target the caller's registers pass unchanged (only ra is written); on the edge from a call
    to the next word, a caller-saved register is the callee's (a0: its return; any other: clobbered)."""
    out = set()
    if depth > 8: return {('other', 'followed through more than 8 addi')}
    if k == 0: out.add(entry_value(reg, off))
    elif not F.pr[k]: return {('other', 'a word no decoded edge reaches (+%#x)' % F.w[k][0])}
    work = [(j, k) for j in F.pr[k]]; vis = set()
    while work:
        j, kk = work.pop()
        if (j, kk) in vis: continue
        vis.add((j, kk))
        o, x, n = F.w[j]; op, rd, f3, r1, r2, f7 = dec(x)
        if op in (0x6f, 0x67) and rd:
            if F.icall.get(j) == kk and kk != j + 1:                  # the edge into an in-function callee
                if reg == rd: out.add(('other', 'the return address of the in-function call at %s' % F.pc(j))); continue
                if j == 0: out.add(entry_value(reg, off))
                work += [(p, j) for p in F.pr[j]]; continue
            if reg in CS:
                out.add(('ret', (F.callee(j) or 'a register-indirect call'), off) if reg == 10
                        else ('other', 'clobbered by the call at %s' % F.pc(j)))
                continue
        if s3._writes(x) == reg and reg:
            if j in F.tpc:
                t = F.tpc[j]
                if F.I.sec(t) == '.got' and op == 0x03: out.add(('load', 'the .got cell %#x' % t, off))
                elif op == 0x03: out.add(('load', 'a load of %s at %s' % (s3.qres(F.I, t), F.pc(j)), off))
                else: out.add(('sym', t, off))
            elif op in (0x13, 0x1b) and f3 == 0 and r1:
                out |= anchor(F, j, r1, off + (s3._lo12(x) or 0), depth + 1)
            elif op == 0x03: out.add(('load', 'a load by `%s` at %s' % (text(x, o), F.pc(j)), off))
            elif op == 0x37: out.add(('num', (sxv(x >> 12, 20) << 12) & M64, off))
            elif op in (0x13, 0x1b) and f3 == 0 and r1 == 0: out.add(('num', (s3._lo12(x) or 0) & M64, off))
            else: out.add(('other', 'computed by `%s` at %s' % (text(x, o), F.pc(j))))
            continue
        if j == 0: out.add(entry_value(reg, off))
        elif not F.pr[j]: out.add(('other', 'a word no decoded edge reaches (+%#x)' % o))
        work += [(p, j) for p in F.pr[j]]
    return out

def const_of(F, k, reg):
    """the one constant reg holds at word k, or None"""
    vs = set()
    for a in anchor(F, k, reg):
        if a[0] != 'num': return None
        vs.add((a[1] + a[2]) & M64)
    return vs.pop() if len(vs) == 1 else None

def struct_of(t):
    """the struct name of a pointer-to-struct type, else None"""
    return t[7:-2] if t.startswith('struct ') and t.endswith(' *') else None

def srcof(fl): return ('%s:%d' % fl) if fl else 'no decl line'

INT_SRC = ('int', 'unsigned', 'long', 'short', 'char', 'bool', 'u8', 'u16', 'u32', 'u64', 's8', 's16', 's32', 's64',
           'size_t', 'ssize_t', 'off_t', 'mode_t', 'error_t', 'fd_t', 'tid_t', 'pid_t', 'nl_item', 'socklen_t',
           'clockid_t', 'uptr', 'sptr', 'uhwptr')
ADDRESS_SRC = ('uptr', 'sptr', 'uhwptr', 'uintptr_t', 'intptr_t')

def src_kind(t):
    """how the pinned source's type reads: 'ptr' a pointer / reference / array, 'uptr' a pointer-SIZED integer typedef
    (uptr, sptr, uhwptr, uintptr_t), 'int' any other integer, None anything else (a struct, a float, an unknown name).
    A `uptr` is an integer, so it settles when the source's name gives it the meaning of a count or a length
    (the unit owner's ruling (a)); as an ADDRESS parameter it never settles."""
    t = t.replace('const', ' ').replace('volatile', ' ').strip()
    if '*' in t or '&' in t or '[' in t: return 'ptr'
    toks = [w for w in re.split(r'[\s]+', t) if w]
    if not toks: return None
    if any(w in ADDRESS_SRC for w in toks): return 'uptr'
    if all(w in INT_SRC or w in ('signed', 'unsigned', 'enum') for w in toks): return 'int'
    return None

def dm_kind(t):
    """the same for a type the DEMANGLER printed (the mangled name's own type, so it carries no typedef: a uptr reads
    as `unsigned long`, i.e. 'int' here)"""
    t = t.replace('const', ' ').strip()
    if '*' in t or '&' in t or '[' in t or t == 'this': return 'ptr'
    toks = [w for w in re.split(r'[\s]+', t) if w]
    base = ('int', 'unsigned', 'long', 'short', 'char', 'bool', 'signed')
    if toks and all(w in base for w in toks): return 'int'
    return None

def means_count(pnm):
    """does the pinned source's parameter name say the parameter is a byte count / length / count / size / flags /
    mode / prot / alignment? (whole words of the name, and no address word in it)"""
    ws = [w for w in re.split(r'[^a-z0-9]+', (pnm or '').lower()) if w]
    if not ws or any(w in NEVER_SETTLE_WORDS for w in ws): return False
    return any(w in SETTLE_WORDS for w in ws)

class Cite:
    """the CITE table: cite_gen.py's rows read from the pinned source, then the hand-written rows of cite-extra.tsv
    (which override them, and which may carry the kind `arg!` / `ret!`: a row whose citation states the contract that
    settles it, for a parameter whose NAME alone does not say what it means). Plus the X -> Y map of the compared set."""
    def __init__(self, cp, yof):
        self.yof = yof; self.t = {}; self.forced = set()
        for p in ([cp] if cp else []) + ([os.path.join(os.path.dirname(cp), 'cite-extra.tsv')] if cp else []):
            if not p or not os.path.exists(p): continue
            for l in open(p):
                f = l.rstrip('\n').split('\t')
                if len(f) < 6 or l.startswith('#'): continue
                k = f[0].rstrip('!')
                self.t[(k, f[1], f[2])] = (f[3], f[4], f[5])
                if f[0].endswith('!'): self.forced.add((k, f[1], f[2]))
    def get(self, kind, name, key): return self.t.get((kind, name, key))
    def is_forced(self, kind, name, key): return (kind, name, key) in self.forced

def classify(C, FX, FY, i, kind, det, fx, fy):
    """(class, citation) for one ROW"""
    if kind == 'arg':
        r = 10 + int(det[1:])
        callee = FX.callee(i)
        if callee is None: return 'NOT CERTIFIED', 'a register-indirect call: no callee to cite'
        cn = callee[:-4] if callee.endswith('+0x0') else callee
        pt = prototype(cn)
        dmt = pt[0][r - 10] if pt and r - 10 < len(pt[0]) else ('a variadic argument' if pt and pt[1] else 'unknown')
        c = C.get('arg', cn, det)
        if c is None and pt and r - 10 >= len(pt[0]):
            if pt[1]:
                return 'NOT CERTIFIED', '%s %s: a VARIADIC argument (past the %d named parameter(s)) [%s]' % (
                    cn, det, len(pt[0]), pt[2])
            return 'NOT CERTIFIED', '%s %s: past the callee\'s %d parameter(s), but the callee, or a callee it calls first, ' \
                'may read the register (reads_deep: a register-indirect call, a variadic or unknown callee, or a read on ' \
                'some path) [%s]' % (cn, det, len(pt[0]), pt[2])
        if c is None:
            return 'NOT CERTIFIED', '%s %s (the mangled name gives `%s`): no parameter cited in the pinned source [%s]' \
                % (cn, det, dmt, pt[2] if pt else 'no prototype')
        typ, pnm, src = c
        kd = src_kind(typ)
        if C.is_forced('arg', cn, det):
            return '(i) CALL ARGUMENT', '%s parameter %s `%s %s` [%s]' % (cn, det, typ, pnm, src)
        if dm_kind(dmt) != kd and not (dm_kind(dmt) == 'int' and kd == 'uptr'):
            return 'NOT CERTIFIED', '%s %s: the mangled name says `%s`, the source says `%s %s`: they do not agree [%s]' \
                % (cn, det, dmt, typ, pnm, src)
        if kd in ('int', 'uptr') and means_count(pnm):
            return '(i) CALL ARGUMENT', '%s parameter %s `%s %s`: the source names a count / length / size / flags / ' \
                'mode / prot / alignment, and the mangled name gives the integer `%s` [%s]' % (cn, det, typ, pnm, dmt, src)
        why = ('a pointer' if kd == 'ptr' else 'not an integer type' if kd is None else
               'an address-sized integer whose name does not say it is a count or a length' if kd == 'uptr' else
               'an integer whose name does not say it is a count or a length')
        return 'NOT CERTIFIED', '%s parameter %s `%s %s`: %s [%s]' % (cn, det, typ, pnm, why, src)
    if kind == 'ret':
        fn = s3.qres(FX.I, FX.a); fn = fn[:-4] if fn.endswith('+0x0') else fn
        c = C.get('ret', fn, '-')
        if c is None: return 'NOT CERTIFIED', '%s: no return type cited in the pinned source' % fn
        typ, meaning, src = c
        kd = src_kind(typ)
        if C.is_forced('ret', fn, '-') or kd == 'int':
            return '(ii) RETURN', '%s returns `%s`%s [%s]' % (fn, typ, ' (%s)' % meaning if meaning else '', src)
        return 'NOT CERTIFIED', '%s returns `%s`: %s [%s]' % (
            fn, typ, 'a pointer' if kd == 'ptr' else 'address-sized' if kd == 'uptr' else 'not an integer type', src)
    if kind in ('store', 'amo'):
        o, x, n = FX.w[i]; op, rd, f3, r1, r2, f7 = dec(x)
        width = (1 << (f3 & 3)) if op in (0x23, 0x27) else (4 if f3 == 2 else 8)
        if 'leaves at' in det:
            sk = int(re.search(r'stack slot sp([+-]\d+) at entry', det).group(1))
            kx, whyx = iv_settle(C, FX, sk, width); ky, why_y = iv_settle(C, FY, sk, width)
            if kx is not None and ky is not None and kx == ky and ('struct' in kx or kx == {'unread'}):
                if 'struct' in kx:
                    # class (iv): every callee that can read the bytes receives them as cited integer struct members
                    # (any other escape is a callee that cannot read memory, or a cited struct that ends below the slot)
                    return '(iv) STORE', 'a %d-byte store into the stack slot sp%+d (at entry); every reader of the frame ' \
                        'object receives these bytes as cited integer struct members. X: %s || Y: %s' % (width, sk, whyx, why_y)
                # STORE-UNREAD (a class added on 2026-10-31, after the re-reviews): no escape can read the bytes at all; measured,
                # not cited, so it is its own class and not (iv)
                return 'STORE-UNREAD', 'a %d-byte store into the stack slot sp%+d (at entry); every callee the frame ' \
                    'object is passed to has no load / AMO / ecall / call, disassembled in both images. X: %s || Y: %s' % (
                        width, sk, whyx, why_y)
            return 'NOT CERTIFIED', 'a %d-byte store into a stack slot of a frame object whose address leaves the ' \
                'function (%s): its reader is not traced, and neither class (iv) nor STORE-UNREAD applies: %s' % (
                    width, det.split('; ', 1)[1].rstrip(')'),
                    whyx if kx is None else why_y if ky is None else 'the escapes differ between X and Y')
        base = anchor(FX, i, r1, s3._lo12(x) if op in (0x23, 0x27) else 0)
        bt = [(('%s %s +%#x' % (a[0], RN[a[1]] if a[0] == 'param' else a[1], a[2])) if a[0] != 'other' else a[1])
              for a in sorted(base, key=repr)]
        return 'NOT CERTIFIED', 'a %d-byte store; its base is %s; no struct field is cited (these images carry no ' \
            'DWARF member layout)' % (width, ' | '.join(bt))
    if kind == 'ecall':
        nr = const_of(FX, i, 17); s = SYSCALL.get(nr)
        return 'NOT CERTIFIED', ('an argument register of the %s syscall (a7 = %d)' % (s[0], nr) if s else
                                 'live at an ecall whose number is %s' %
                                 ('%d, not in the table' % nr if nr is not None else 'not one constant'))
    if kind == 'base':
        if not fx or not fy: return 'NOT CERTIFIED', 'no form'
        # (iii) settles onto an OBJECT POINTER: a parameter the function received, a stack (sp-derived) address, the
        # return of a call, or a value loaded from memory. A sum of two anchors, a scaled anchor and a widened
        # ("many forms") value are NOT object pointers and never settle (the unit owner's ruling (d), and the one on
        # FAIL-OPEN #3).
        def objptr(an): return an is not None and an[0] == 'ptr' and an[1].startswith(OBJPTR)
        if all(objptr(an) for an, c in fx) and all(objptr(an) for an, c in fy):
            return '(iii) DISPLACEMENT', 'onto an object pointer: %s' % fmt_forms(FX, fx)
        if any(an is not None and an[0] == 'ptr' for an, c in fx) or any(an is not None and an[0] == 'ptr' for an, c in fy):
            return 'NOT CERTIFIED', 'a base whose anchor is not one object pointer: %s | %s' % (fmt_forms(FX, fx), fmt_forms(FY, fy))
        full = []
        for F, fs in ((FX, fx), (FY, fy)):
            names = set()
            for an, c in fs:
                if c is None: return 'NOT CERTIFIED', 'a base of unknown form: %s' % fmt_forms(F, fs)
                addr = (c + (an[1] if an else 0)) & M64
                names.add(s3.qres(F.I, addr) if F.I.sec(addr) else 'outside every section %#x' % addr)
            full.append(names)
        if full[0] == full[1]:
            return '(iii) DISPLACEMENT', 'full address the same symbol + offset in X and Y: %s' % ', '.join(sorted(full[0]))
        return 'DIFFERS', 'full address X %s | Y %s' % (sorted(full[0]), sorted(full[1]))
    if kind in ('fpmove', 'csr'):
        return 'NOT CERTIFIED', 'the value leaves the integer registers (%s): not followed further' % det
    return 'NOT CERTIFIED', kind

def compared_set(X, Y, roots):
    """the COMPARED SET of the docstring: (SX, SY, seen, yof). SX / SY: {address: [(name, size)]} of every sized FUNC
    symbol (also registered in STARTS for clobbers / reads_deep); seen: the X addresses reached from the roots through any
    pc-relative target or .got cell that starts a sized FUNC symbol; yof: X address -> its Y counterpart"""
    def starts(Im):
        st = {}
        for v, z, n, t in Im.syms:
            if t == 'STT_FUNC' and z > 0: st.setdefault(v, []).append((n, z))
        return st
    SX, SY = starts(X), starts(Y)
    STARTS[id(X)] = SX; STARTS[id(Y)] = SY
    def refs(Im, st, a, z):
        b = s3.frd(Im, a, z); out = {}
        if b is None: return out
        for i, (kind, ta) in s3.targets(a, b).items():
            if Im.sec(ta) == '.got':
                c = s3.frd(Im, ta, 8); ta = int.from_bytes(c, 'little') if c else -1
            if ta in st and not (a <= ta < a + z): out[i] = ta
        return out
    yof = {}; seen = set(); work = []
    for r in roots:
        cx, cy = s3.fcopies(X, r), s3.fcopies(Y, r)
        yof[cx[0][0]] = cy[0][0]; seen.add(cx[0][0]); work.append(cx[0][0])
    while work:
        a = work.pop(); z = SX[a][0][1]; ya = yof.get(a)
        ry = refs(Y, SY, ya, z) if ya is not None and SY.get(ya, [(None, -1)])[0][1] == z else {}
        for i, t in refs(X, SX, a, z).items():
            if t not in yof and i in ry: yof[t] = ry[i]
            if t not in seen: seen.add(t); work.append(t)
    return SX, SY, seen, yof

def main():
    a_ = sys.argv[1:]
    only = None
    if '--only' in a_:
        k = a_.index('--only'); only = set(a_[k + 1].split(',')); a_ = a_[:k] + a_[k + 2:]
    xp, yp, roots = a_[0], a_[1], a_[2].split(',')
    cp = a_[3] if len(a_) > 3 else os.path.join(HERE, 'cite.tsv')
    X, Y = s3.Img(xp), s3.Img(yp); JTARGS[:] = [xp, yp]
    SX, SY, seen, yof = compared_set(X, Y, roots)
    C = Cite(cp, yof); CITE_REF[:] = [C]
    print('#\tX %s sha256 %s\tY %s sha256 %s\troots %s' % (os.path.basename(xp), s3.sha(xp)[:12], os.path.basename(yp),
                                                           s3.sha(yp)[:12], ','.join(roots)))
    print('#\tCITE %s sha256 %s\t%d cited parameters / return types' % (os.path.basename(cp), s3.sha(cp)[:12], len(C.t)))
    tot = collections.Counter(); classes = collections.Counter()
    nfun = 0
    for a in sorted(seen):
        nx, zx = sorted(SX[a])[0]; qx = s3.qname(X, nx, a) or nx; ya = yof.get(a)
        if only and qx not in only: continue
        b = s3.frd(X, a, zx)
        if b is None: continue
        ws = s3.bc_words(b)
        luis = [i for i, (o, x, n) in enumerate(ws) if n == 4 and x & 0x7f == 0x37 and (x >> 7) & 31]
        if any(n == 2 for o, x, n in ws):
            # (shape g) a 2-byte parcel may be a c.lui (or c.addi / c.mv carrying a lui value): the whole function is
            # refused, whether or not it holds a 4-byte lui
            print('UNMEASURED\t%s\t2-byte parcels (%d): c.lui and the compressed ops are not decoded; %d 4-byte lui words '
                  'not followed' % (qx, sum(1 for o, x, n in ws if n == 2), len(luis)))
            tot['unmeasured functions'] += 1; continue
        if not luis: continue
        nfun += 1
        if ya is None:
            c = s3.fcopies(Y, qx)
            ya = c[0][0] if len(c) == 1 else None
        if ya is None or SY.get(ya, [(None, -1)])[0][1] != zx:
            print('NOY\t%s\tno Y copy of the same size' % qx); tot['no-y'] += 1; continue
        FX, FY = Fn(X, a, zx), Fn(Y, ya, zx)
        GX = None
        if FX.noret:
            # the same CFG with every noreturn call's fall-through edge put back: the uses the trace finds only there are
            # on no feasible path (the callee never returns); they are listed as UNREACH lines, never dropped silently
            GX = Fn(X, a, zx)
            for q in GX.noret:
                if q + 1 < len(GX.w) and q + 1 not in GX.succ[q]: GX.succ[q].append(q + 1); GX.pr[q + 1].append(q)
            GX.roots = sorted(set(range(1, len(GX.w))) - {t for ss in GX.succ for t in ss})
        meet = collections.defaultdict(dict)        # base word -> {lui word: its form} (the lui+lui -> base check)
        meetcls = collections.defaultdict(collections.Counter)
        for j in luis:
            tot['lui'] += 1
            vx, evx = trace(FX, j); vy, evy = trace(FY, j)
            print('LUI\t%s\t%s\t`%s`\tvalue X %#x Y %#x' % (qx, FX.pc(j), text(FX.w[j][1], FX.w[j][0]), vx, vy))
            if vx != vy: print('ROW\t%s\t%s\tlui\t-\tDIFFERS\tthe lui value differs' % (qx, FX.pc(j))); classes['DIFFERS'] += 1; continue
            sx_ = [(e[0], e[1], e[2]) for e in evx]; sy_ = [(e[0], e[1], e[2]) for e in evy]
            if sx_ != sy_: print('ROW\t%s\t%s\ttrace\t-\tDIFFERS\tthe traces differ between X and Y' % (qx, FX.pc(j))); classes['DIFFERS'] += 1
            print('TRACE\t%s\t%s\t%s' % (qx, FX.pc(j), ' ; '.join('%s %s %s' % (FX.pc(i), k, d) for i, k, d, f in evx) or 'no use'))
            nunr = 0
            if GX is not None:
                def ukey(i, k, d): return (i, 'st', '') if k in ('store', 'spill') else (i, k, d)
                seen_ev = {ukey(i, k, d) for i, k, d, f in evx}
                vg, evg = trace(GX, j)
                for i, k, d, f in evg:
                    if k in ('arith', 'cmp', 'spill', 'reload') or ukey(i, k, d) in seen_ev: continue
                    # the noreturn calls the use lies beyond: reachable from the lui, and the use reachable from their
                    # restored fall-through
                    via = []
                    for q in sorted(FX.noret):
                        if q + 1 < len(GX.w) and reach_from(GX, j, q) and reach_from(GX, q + 1, i):
                            via.append('%s %s' % (FX.pc(q), (FX.callee(q) or '?')[:-4]))
                    print('UNREACH\t%s\t%s\t%s %s\t%s\ton no feasible path: the trace reaches this use only when the '
                          'fall-through edges of the noreturn calls are put back (each callee is measured noreturn: no return '
                          'and no tail jump in it); the noreturn calls between the lui and the use: %s' % (
                          qx, FX.pc(j), FX.pc(i), k, d, '; '.join(via) or '?'))
                    nunr += 1; tot['unreachable uses (beyond a noreturn call)'] += 1
            fy_of = {(i, k, d): f for i, k, d, f in evy}
            nrow = 0; nuse = 0
            for i, kind, det, fx in evx:
                if kind == 'base': meet[i][j] = fx
                if kind in ('arith', 'cmp', 'spill', 'reload'): continue
                nuse += 1
                fy = fy_of.get((i, kind, det))
                if kind == 'arg':
                    r = 10 + int(det[1:])
                    callee = FX.callee(i)
                    pt = prototype(callee[:-4] if callee and callee.endswith('+0x0') else (callee or ''))
                    if pt is not None and not pt[1] and r - 10 >= len(pt[0]):
                        # the ABI says the register is past the callee's parameters; the unit owner's ruling (e) also wants the
                        # callee's own code: it must not read that register before writing it, on any path to a return.
                        ta = FX.tgt(i); rd_ = reads_deep(X, ta, r)
                        if rd_ is False:
                            print('NOTARG\t%s\t%s\t%s\t%s\t%s is not a parameter: %d argument register(s) [%s]; and the '
                                  'callee at %#x never reads %s before writing it, on any path, nor does any callee it '
                                  'calls first (reads_deep: measured on their CFGs, to depth 4)'
                                  % (qx, FX.pc(j), FX.pc(i), callee[:-4], RN[r], len(pt[0]), pt[2], ta, RN[r]))
                            tot['not-arg'] += 1; continue
                if kind == 'ecall':
                    r = 10 + int(det[1]); nr = const_of(FX, i, 17); sc = SYSCALL.get(nr)
                    if sc is not None and r - 10 >= sc[1]:
                        print('NOTECALL\t%s\t%s\t%s\t%s is not an argument of the %s syscall (a7 = %d, %d arguments)'
                              % (qx, FX.pc(j), FX.pc(i), RN[r], sc[0], nr, sc[1])); tot['not-ecall'] += 1; continue
                if kind == 'ret':
                    r = 10 + int(det[1])
                    fn = s3.qres(X, FX.a); fn = fn[:-4] if fn.endswith('+0x0') else fn
                    cr = C.get('ret', fn, '-')
                    if cr is not None and cr[0].strip() == 'void':
                        print('NOTRET\t%s\t%s\t%s\t%s: the pinned source returns void [%s]'
                              % (qx, FX.pc(j), FX.pc(i), RN[r], cr[2])); tot['not-ret'] += 1; continue
                    if r == 11 and cr is not None and src_kind(cr[0]) is not None:
                        print('NOTRET\t%s\t%s\t%s\ta1 is not part of the return value: `%s` takes one register [%s]'
                              % (qx, FX.pc(j), FX.pc(i), cr[0], cr[2])); tot['not-ret'] += 1; continue
                    live = None
                    if r == 11:
                        live = False
                        for v in SX:
                            bb = s3.frd(X, v, SX[v][0][1])
                            if bb is None: continue
                            for q, (oo, xx, nn) in enumerate(s3.bc_words(bb)):
                                if nn == 4 and xx & 0x7f == 0x6f and (xx >> 7) & 31 == 1 and v + oo + s3._jal_off(xx) == FX.a:
                                    if live_after(Fn(X, v, SX[v][0][1]), q, 11): live = True
                    if live is False:
                        print('NOTRET\t%s\t%s\t%s\ta1 at the return is read by no direct caller (measured)' % (qx, FX.pc(j), FX.pc(i)))
                        tot['not-ret'] += 1; continue
                cl, why = classify(C, FX, FY, i, kind, det, fx, fy)
                classes[cl] += 1; nrow += 1
                if kind == 'base': meetcls[i][cl] += 1
                print('ROW\t%s\t%s\t%s %s\t%s\t%s\t%s\tforms X: %s | Y: %s' % (qx, FX.pc(j), FX.pc(i), kind, det, cl, why,
                                                                             fmt_forms(FX, fx), fmt_forms(FY, fy)))
            if nrow == 0 and nuse == 0:
                kinds = {k for i, k, d, f in evx}
                if 'cmp' in kinds:
                    # (c) COMPARE-ONLY (the unit owner's ruling; labelling fixed after the egress review): no ROW and no measured
                    # non-row, and the trace holds at least one branch / compare of the value or of a value computed from
                    # it; every other event is arithmetic or a spill into a PRIVATE slot (no escaping frame object)
                    print('CMPONLY\t%s\t%s\tno row on any feasible path: the events are %s, and at least one is a branch / '
                          'compare (the TRACE line above lists them)%s' % (qx, FX.pc(j), ', '.join(sorted(kinds)),
                          '; %d use(s) lie only beyond a noreturn call (the UNREACH lines above)' % nunr if nunr else ''))
                    tot['compare-only'] += 1
                else:
                    print('NOUSE\t%s\t%s\tno row and no compare on any feasible path: the events are %s (the value is not '
                          'read, or only by arithmetic or private spills whose results are not read)%s' % (
                          qx, FX.pc(j), ', '.join(sorted(kinds)) or 'none',
                          '; %d use(s) lie only beyond a noreturn call (the UNREACH lines above)' % nunr if nunr else ''))
                    tot['no use'] += 1
        for i, byj in sorted(meet.items()):
            if len(byj) < 2: continue
            # FAIL-OPEN #3 (the unit owner's ruling): two or more lui values reach ONE load / store / jalr / AMO base. The
            # verdict is the class of the base ROWS at that word: every one is the X-vs-Y comparison of that base.
            o, x, n = FX.w[i]
            cls_ = meetcls.get(i, collections.Counter())
            v = ('DIFFERS' if cls_.get('DIFFERS') else
                 'settled: every base row there is (iii), an object-pointer displacement or the same symbol + offset in '
                 'X and Y' if cls_ and not cls_.get('NOT CERTIFIED') else
                 'NOT CERTIFIED: %d of %d base rows' % (cls_.get('NOT CERTIFIED', 0), sum(cls_.values())) if cls_ else
                 'no base row')
            print('LUIMEET\t%s\t%s\t%s\t%s\t%s\tX: %s | Y: %s' % (
                qx, FX.pc(i), text(x, o), ','.join(FX.pc(j) for j in sorted(byj)), v,
                ' / '.join(fmt_forms(FX, byj[j]) for j in sorted(byj)),
                ' / '.join(fmt_forms(FY, byj[j]) for j in sorted(byj))))
            tot['lui-meet sites'] += 1
            tot['lui-meet ' + v.split(':')[0]] += 1
    print('#\tSHAPES\t%s' % '\t'.join('%s: %d' % (k, v) for k, v in sorted(SHAPE.items())))
    nr = sorted(qn for qn in (s3.qname(X, sorted(SX[a])[0][0], a) or sorted(SX[a])[0][0] for a in seen if noreturn(X, a)))
    print('#\tNORETURN %d\t%s' % (len(nr), ','.join(nr)))
    if UNKNOWN_PROTO:
        print('#\tcallees with no prototype, each counted as reading the register (fail-closed): %s' % ', '.join(
            '%s %d' % kv for kv in UNKNOWN_PROTO.most_common()))
    print('TOTAL\tfunctions with a lui %d\t%s\t%s' % (nfun, '\t'.join('%s %d' % kv for kv in sorted(tot.items())),
                                                      '\t'.join('%s %d' % kv for kv in sorted(classes.items()))))

if __name__ == '__main__':
    main()
