#!/usr/bin/env python3
"""settle3.py -- settle every target cmpkit 86da41d3ef68 leaves unsettled in the __asan_memmove donor comparison, from the
kit's FULL target list, by the named measurements of the record's README only; trace every lui row.

Inputs (one image): the kit directory (strictcmp3.py is loaded from it and its sha256 checked), X (unit, unstripped),
Y's stripped pin and unstripped twin, closure_strict3's output, paircl's output and its targets TSV (--full
--targets-out), jtcheck's output over the non-certified functions, and the hand classes file (luiclass.tsv).

1. Function pairs. Closure: every member row closure_strict3 prints as not EQUAL / EQUAL-mod-pcrel-with-all-targets-equal
   (X address; Y = the FUNC of the same qualified name in the twin, closure_strict3's ycounterpart), compared X twin vs Y
   twin. Paircl: every row of the targets TSV (X address, Y address), compared against Y's PIN bytes with the twin's
   names (paircl's own construction). Plus, for the lui trace, every member / pair whose ACCEPT line lists a
   `lui-const` acceptance.
2. strictcmp3.tcmp is run again on each pair; its full differing-target list must equal the kit's printed list
   (closure) / TSV rows (paircl), offset and kind for offset and kind (MATCH, else the tool stops).
3. Per differing target:
   data-differs / cstr-differs on an unnamed read-only target (no lui):
     TABLE      the target register reaches an add / sh{1,2,3}add with an index register, a load of width w reads the
                sum at offset 0, and the index is bounded in the code: `srli r, s` (64-bit: 2^(64-s) entries), `andi r,
                m` (m+1), or `addi rK, zero, K` with a `bltu rK, rI` / `bgeu rK, rI` guarding the load (K+1). The first
                k*w bytes are compared on both sides; the consumer words are printed
     JTCHECK    jtcheck 8b0ea3862423 (kit member) ACCEPTs a table / initializer at this offset (its table rule)
     BYHAND-TABLE  a table read entry by entry as the hand classes file says (JT32-rel: relative 32-bit jump table,
                entry by entry as function offset; STRTAB32-rel: relative 32-bit entries to C strings, each compared
                with its NUL); the bound constant is read from the code and cited
     CSTR       none of these: the bytes up to and including the first NUL are equal on both sides, AND the hand
                classes file cites the consumer that uses the target as a C string (else NOT CERTIFIED)
   lui-in-section: the lui trace (luitrace.py); SETTLED only when every use is settled: a BASE use by
                FULL-ADDRESS-EQUAL, every other use by a class with its citation in the hand classes file
   unmeasured:  no named measurement: NOT CERTIFIED: REAL 0
   any other kind: REAL (a difference: stop and report)
   And every lui-const acceptance row: the same lui trace and the same rule.
Output: OUT-targets.tsv (one row per target and per lui-const row), OUT-luitrace.txt (every lui row's trace with its
uses and their classes), OUT-members.tsv (per member / pair: KIT-CERTIFIED / SETTLED / NOT CERTIFIED), and a summary.
usage: settle3.py KITDIR X_ELF Y_PIN Y_TWIN CLOSURE_OUT PAIRCL_OUT PAIRCL_TSV JTCHECK_OUT CLASSES OUT"""
import sys, os, re, ast, hashlib, importlib.util, collections, struct
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import luitrace as LT

kit, xe, ype, yte, clf, pcf, pct, jtf, clsf, out = sys.argv[1:11]
if hashlib.sha256(open(os.path.join(kit, 'strictcmp3.py'), 'rb').read()).hexdigest()[:12] != '65688e94214a':
    raise SystemExit('settle3: strictcmp3.py is not 65688e94214a')
s3 = LT.load_kit(kit)
from elftools.elf.elffile import ELFFile
X, YT, YP = s3.Img(xe), s3.Img(yte), s3.Img(yte)
segs = [(g['p_vaddr'], g['p_filesz'], g['p_memsz'], g.data()) for g in ELFFile(open(ype, 'rb')).iter_segments()
        if g['p_type'] == 'PT_LOAD']
if [x[:3] for x in segs] != [(v, fz, mz) for (v, fz, d), mz in zip(YP.segs, YP.mzs)]:
    raise SystemExit('settle3: Y pin and twin have different PT_LOAD layouts')
YP.segs = [(v, fz, d) for v, fz, mz, d in segs]
IMG = {'closure': {'X': X, 'Y': YT}, 'paircl': {'X': X, 'Y': YP}}

# ---- the hand classes file ------------------------------------------------------------------------------------------
CL = {'CSTR': {}, 'LUI': {}, 'BYHAND': {}}
SIG = {}          # function -> (return kind:type, source citation, [(type, name, kind)] per integer-argument register)
CONSUMER = {}     # a C-string consumer -> (argument index or 'ret', source citation that it reads to the NUL)
for ln in open(clsf):
    if not ln.strip() or ln.startswith('#'): continue
    f = ln.rstrip('\n').split('\t')
    if f[0] == 'CSTR': CL['CSTR'][(f[1], f[2])] = f[3]                         # CSTR fn off citation
    elif f[0] == 'LUI': CL['LUI'][(f[1], f[2], f[3], f[4])] = (f[5], f[6])     # LUI fn lui-off use-off role class citation
    elif f[0] == 'BYHAND': CL['BYHAND'][(f[1], f[2])] = (f[3], f[4], f[5])     # BYHAND fn off reading:N cmp-off citation
    elif f[0] == 'SIG':                                                        # SIG fn ret-kind:type cite params
        SIG[f[1]] = (f[2], f[3], [tuple(x.split(':')) for x in f[4].split(',') if x])
    elif f[0] == 'CONSUMER': CONSUMER[f[1]] = (f[2], f[3])                     # CONSUMER callee arg-index|ret citation
    else: raise SystemExit('settle3: bad classes line %r' % ln)

# ---- 1. function pairs ------------------------------------------------------------------------------------------------
starts = {}
for v, z, n, t in X.syms:
    if t == 'STT_FUNC' and z > 0: starts.setdefault(v, []).append((n, z))
dupx = {n for n, l in X.byname.items() if len([e for e in l if e[2] == 'STT_FUNC' and e[1] > 0]) > 1}


def member(a):
    l = sorted(starts[a]); n, z = next(((n, z) for n, z in l if n not in dupx), l[0])
    return n, z, s3.qname(X, n, a)


def ycounterpart(n, q):
    c = sorted({(v, z) for v, z, t in YT.byname.get(n, []) if t == 'STT_FUNC' and z > 0 and s3.qname(YT, n, v) == q})
    return c[0] if len(c) == 1 else None


pairs = collections.OrderedDict()      # (run, xa) -> dict
kitlist = {}
first = open(clf).readline().split('\t')
for ln in open(clf).read().splitlines()[1:]:
    m = re.match(r'^   (\S+) @(0x[0-9a-f]+): (\S+) \(words-only (\S+)\) (.*) (\S*) \(printed (\d+) of (\d+) targets\)$', ln)
    if not m: continue
    nm, xa, v, words, diffs, dup, pm, pn = m.groups(); xa = int(xa, 16)
    d = ast.literal_eval(diffs)
    n, z, q = member(xa); ys = ycounterpart(n, q)
    if ys is None or ys[1] != z: raise SystemExit('settle3: no Y counterpart for %s' % nm)
    pairs[('closure', xa)] = dict(name=q or n, xa=xa, ya=ys[0], z=z, kit=v, words=words)
    kitlist[('closure', xa)] = sorted((e[0], e[3]) for e in d)
    if int(pm) != int(pn) or int(pn) != len(d): raise SystemExit('settle3: closure row not fully printed: %s' % nm)
tsv = collections.OrderedDict()
for ln in open(pct).read().splitlines()[1:]:
    fn, xa, ya, off, xt, yt, kind, info = ln.split('\t')
    tsv.setdefault((int(xa, 16), int(ya, 16), fn), []).append((off, kind))
for (xa, ya, fn), l in tsv.items():
    n, z, q = member(xa)
    pairs[('paircl', xa)] = dict(name=q or n, xa=xa, ya=ya, z=z, kit=None, words=None)
    kitlist[('paircl', xa)] = sorted(l)
nbad = {}
for ln in open(pcf):
    m = re.match(r'^closure (\d+) functions paired; EQUAL (\d+); EQUAL-mod-pcrel \(targets paired\) (\d+); other (\d+)', ln)
    if m: nbad['paircl'] = int(m.group(4))
if nbad['paircl'] != len(tsv): raise SystemExit('settle3: paircl other %d != TSV functions %d' % (nbad['paircl'], len(tsv)))
nclosure_other = int(re.search(r'other (\d+)', open(clf).readline()).group(1))
if nclosure_other != sum(1 for k in pairs if k[0] == 'closure'): raise SystemExit('settle3: closure other count mismatch')

# lui-const acceptance rows (any member / pair, certified or not)
luiconst = collections.OrderedDict()
for run, path in (('closure', clf), ('paircl', pcf)):
    for ln in open(path):
        m = re.match(r'   ACCEPT (\S+) @(0x[0-9a-f]+)/(0x[0-9a-f]+): (.*)', ln)
        if not m: continue
        nm, xa, ya, rest = m.groups(); xa, ya = int(xa, 16), int(ya, 16)
        for mm in re.finditer(r'lui-const\+(0x[0-9a-f]+)\[(0x[0-9a-f]+)\|(0x[0-9a-f]+)\]', rest):
            n, z, q = member(xa)
            luiconst[(run, xa, mm.group(1))] = dict(name=q or n, xa=xa, ya=ya, z=z, vx=int(mm.group(2), 16), vy=int(mm.group(3), 16))

# ---- jtcheck acceptances ----------------------------------------------------------------------------------------------
JT = {}
for ln in open(jtf):
    m = re.match(r'   ACCEPT (\S+) (table|initializer) \+(0x[0-9a-f]+) \[(0x[0-9a-f]+)\|(0x[0-9a-f]+)\] (.*)', ln)
    if m: JT[(m.group(1), m.group(3))] = '%s [%s|%s] %s' % (m.group(2), m.group(4), m.group(5), m.group(6))

# ---- helpers ---------------------------------------------------------------------------------------------------------
W = {0: 1, 1: 2, 2: 4, 3: 8, 4: 1, 5: 2, 6: 4}


def table_reading(w, i):
    """(entries, width, words) when the register word i writes reaches add / sh*add with an index, a load of the sum at
    offset 0, and the index is bounded in the code (srli / andi / a constant compare guarding the load)"""
    o, x, n = w[i]; rt = (x >> 7) & 31; regs = {rt}
    for k in range(i + 1, min(len(w), i + 12)):
        ok, xk, nk = w[k]; op = xk & 0x7f; rd = (xk >> 7) & 31; r1 = (xk >> 15) & 31; r2 = (xk >> 20) & 31
        f3, f7 = (xk >> 12) & 7, xk >> 25
        if op == 0x13 and f3 == 0 and (xk >> 20) == 0 and r1 in regs: regs.add(rd); continue          # mv
        if op == 0x33 and ((f3 == 0 and f7 == 0) or (f7 == 0x10 and f3 in (2, 4, 6))) and (r1 in regs or r2 in regs):
            idx = r1 if r2 in regs else r2; s = rd
            for j in range(k + 1, min(len(w), k + 4)):
                oj, xj, nj = w[j]
                if xj & 0x7f == 0x03 and (xj >> 15) & 31 == s and (xj >> 20) == 0:
                    width = W[(xj >> 12) & 7]; ld = (xj >> 7) & 31
                    if width == 8: return None                    # 8-byte entries may be pointers: jtcheck / by hand
                    sums = set()                                   # entry + a base, then jr / ret: a relative table
                    for u in range(j + 1, min(len(w), j + 9)):
                        xu = w[u][1]; opu = xu & 0x7f; a_, b_ = (xu >> 15) & 31, (xu >> 20) & 31
                        if opu == 0x33 and ((xu >> 12) & 7) == 0 and (xu >> 25) == 0 and ld in (a_, b_): sums.add((xu >> 7) & 31)
                        if opu == 0x67 and (xu >> 7) & 31 == 0 and (a_ in sums or (a_ == 1 and 10 in sums)): return None
                    bnd = index_bound(w, k, idx, width, j)
                    if bnd: return bnd, width, w[max(0, i - 8):j + 1]
                    return None
            return None
        if rd in regs and op in (0x13, 0x33, 0x03, 0x37, 0x17, 0x6f, 0x67): regs.discard(rd)
    return None


def index_bound(w, k, idx, width, j):
    """entries the index register idx can select: from the words before the add at k (the index definition: srli s ->
    2^(64-s) ... scaled by the add's shift; andi m -> m+1; or `addi rK, zero, K` + `bltu rK, rI` / `bgeu` with rI the
    unscaled index -> K+1)"""
    scale = 1; r = idx
    for t in range(k - 1, max(-1, k - 14), -1):
        ot, xt, nt = w[t]; op = xt & 0x7f; rd = (xt >> 7) & 31; r1 = (xt >> 15) & 31; f3 = (xt >> 12) & 7
        if rd != r: continue
        if op == 0x13 and f3 == 1:
            sh = (xt >> 20) & 63
            if (1 << sh) != width: return None
            r = r1; continue
        if op == 0x13 and f3 == 5 and (xt >> 26) == 0:
            return 1 << (64 - ((xt >> 20) & 63))
        if op == 0x13 and f3 == 7:
            return LT.sx(xt >> 20, 12) + 1
        break
    for t in range(k - 1, max(-1, k - 14), -1):     # a constant compare on the unscaled index
        ot, xt, nt = w[t]
        if xt & 0x7f == 0x63 and ((xt >> 12) & 7) in (6, 7):
            a, b = (xt >> 15) & 31, (xt >> 20) & 31
            if ((xt >> 12) & 7) == 6 and b == r: kreg = a                 # bltu rK, rI: taken when K < I
            elif ((xt >> 12) & 7) == 7 and b == r: kreg = a                # bgeu rK, rI: falls through when K < I
            else: continue
            for u in range(t - 1, max(-1, t - 6), -1):
                ou, xu, nu = w[u]
                if xu & 0x7f == 0x13 and ((xu >> 12) & 7) == 0 and ((xu >> 15) & 31) == 0 and ((xu >> 7) & 31) == kreg:
                    return LT.sx(xu >> 20, 12) + 1
    return None


def cstr_any(I, a):
    for v, fz, d in I.segs:
        if v <= a < v + fz:
            b = d[a - v:a - v + 4096]; k = b.find(b'\0')
            return b[:k + 1] if k >= 0 else None
    return None


def fb(I, a, n):
    return s3.frd(I, a, n)


def bound_ok(I, a, z, cmp_off, k):
    """the word at cmp_off is bltu rK, rI / bgeu rK, rI and the ONLY definition of rK reaching it (MAY reaching
    definitions over the function's CFG) is `addi rK, zero, K` with K + 1 == k"""
    b = s3.frd(I, a, z)
    w = s3.bc_words(b); x = next((x for o, x, n in w if o == cmp_off), None)
    if x is None or x & 0x7f != 0x63 or (x >> 12) & 7 not in (6, 7): return False, 'no bltu / bgeu at +%#x' % cmp_off
    rk = (x >> 15) & 31
    d, _ = LT.reaching_defs(s3, b, rk, cmp_off)
    if len(d) != 1 or d[0] == 'entry': return False, 'definitions of %s reaching +%#x: %s' % (LT.RN[rk], cmp_off, d)
    xd = next(x for o, x, n in w if o == d[0])
    if not (xd & 0x7f == 0x13 and (xd >> 12) & 7 == 0 and (xd >> 15) & 31 == 0) or LT.sx(xd >> 20, 12) + 1 != k:
        return False, 'reaching definition +%#x %s does not give %d entries' % (d[0], LT.dis(xd), k)
    return True, '+%#x %s; the only definition of %s reaching it: +%#x %s' % (cmp_off, LT.dis(x), LT.RN[rk], d[0], LT.dis(xd))


def byhand(run, p, off, reading, cmp_off, xt, yt):
    I = IMG[run]; xa, ya, z = p['xa'], p['ya'], p['z']
    kind, k = reading.split(':'); k = int(k)
    okx, bdx = bound_ok(I['X'], xa, z, int(cmp_off, 16), k)
    oky, bdy = bound_ok(I['Y'], ya, z, int(cmp_off, 16), k)
    if not (okx and oky): return False, 'bound not verified: X %s | Y %s' % (bdx, bdy)
    bx, by = fb(I['X'], xt, 4 * k), fb(I['Y'], yt, 4 * k)
    if bx is None or by is None: return False, 'unreadable'
    ents = []
    for e in range(k):
        ex = xt + struct.unpack_from('<i', bx, 4 * e)[0]; ey = yt + struct.unpack_from('<i', by, 4 * e)[0]
        if kind == 'JT32-rel':
            if not (xa <= ex < xa + z and ya <= ey < ya + z) or ex - xa != ey - ya:
                return False, 'entry %d: X %#x Y %#x' % (e, ex, ey)
            ents.append('+%#x' % (ex - xa))
        elif kind == 'STRTAB32-rel':
            sx_, sy_ = cstr_any(I['X'], ex), cstr_any(I['Y'], ey)
            if sx_ is None or sx_ != sy_: return False, 'entry %d: %r | %r' % (e, sx_, sy_)
            ents.append(repr(sx_))
        else: return False, 'unknown reading'
    return True, '%s %d entries equal (%s); bound (X and Y): %s' % (kind, k, ' '.join(ents), bdx)

# ---- 2/3. replay and settle -----------------------------------------------------------------------------------------
rows = []; members = collections.OrderedDict(); trace_out = []; real = []; cstr_out = []; cstr_seen = set()
_killcache = {}


def noret_for(run, xa, ya, z):
    """the `noret` callback luitrace takes: True when the call at that word goes to a function that never returns
    (Die, CheckFailed and the like), in BOTH images, so the word after the call is on no path (R1)."""
    def nr(off):
        key = (run, xa, off, 'noret')
        if key in _killcache: return _killcache[key]
        v = True
        for side, a in (('X', xa), ('Y', ya)):
            ce = LT.callee_of(s3, IMG[run][side], a, s3.frd(IMG[run][side], a, z), off)
            if ce is None or LT.callee_returns(s3, IMG[run][side], ce[0], ce[1]): v = False; break
        _killcache[key] = v
        return v
    return nr


def kills_for(run, xa, ya, z):
    """the `kills` callback luitrace takes: a call clobbers a caller-saved register only when the callee WRITES it on
    every path to its return, in BOTH images. Without that the register stays live and the trace goes on in the caller
    past the call (rule (e)); the psABI caller-saved convention is never relied on."""
    def k(off, reg):
        key = (run, xa, off, reg)
        if key in _killcache: return _killcache[key]
        v = True
        for side, a in (('X', xa), ('Y', ya)):
            ce = LT.callee_of(s3, IMG[run][side], a, s3.frd(IMG[run][side], a, z), off)
            if ce is None or not LT.callee_kills(s3, IMG[run][side], ce[0], ce[1], reg): v = False; break
        _killcache[key] = v
        return v
    return k
traced = {}


# class (i): an INTEGER-typed parameter named size / len / count / flags / mode / prot / align. uptr and sptr are the
# kit's address types and NEVER settle by type (the record's rule), nor does any pointer type.
INT_TYPES = {'u8', 'u16', 'u32', 'u64', 's32', 's64', 'int', 'unsigned', 'unsigned_int', 'long', 'unsigned_long',
             'size_t', 'off_t', 'int32_t', 'uint32_t', 'int64_t', 'uint64_t', 'socklen_t', 'mode_t'}
PARAM_NAME = re.compile(r'^(?:[a-z0-9]+_)*(size|len|length|count|flags|mode|prot|align|alignment)(?:_[a-z0-9]+)*$')


def call_continues(run, p, uo, reg, ce):
    """None when the value a callee may leave intact in `reg` comes back to THIS function at a word the trace covers;
    else the refusal. Two cases leave the trace with nowhere to go on: a TAIL call (the callee returns in this
    function's place, so the value leaves this function), and a call that is the function's LAST word (a return would
    fall past the end of the function). Both are refused unless the callee writes `reg` on every path back, in X and Y
    (sysconf +0x224 -> __stack_chk_fail is the second case: the tool has no model of a callee that never returns
    other than a function without a `ret`)."""
    wx = s3.bc_words(s3.frd(IMG[run]['X'], p['xa'], p['z']))
    k = next(i for i, (o, xx, n) in enumerate(wx) if o == uo)
    xw = wx[k][1]
    tail = not ((xw >> 7) & 31)
    last = k == len(wx) - 1
    if not (tail or last): return None
    kills = all(LT.callee_kills(s3, IMG[run][side], ce[side][0], ce[side][1], LT.RN.index(reg)) for side in ('X', 'Y'))
    if kills: return None
    if tail:
        return ('%s is a TAIL call that does not write %s on every path, so the value leaves this function and the trace '
                'cannot be continued' % (ce['X'][2], reg))
    return ('the call to %s is the last word of this function and %s may return without writing %s, so control would '
            'fall past the end of the function: the trace cannot be continued' % (ce['X'][2], ce['X'][2], reg))


def classify_use(run, p, role, reg, uo, sett, detail, c):
    """-> (class, citation) for one use of a lui value; 'NONE' when no named measurement or class settles it.
    Classes: FULL-ADDRESS-EQUAL (a base or value whose full address is the same symbol + offset on both images),
    i (a call argument whose parameter the pinned source's contract makes a byte count / length / count / size /
    flags / mode / prot / alignment: the SIG line's `len` kind), ii (an integer return), iii-disp (a displacement on an
    object-pointer base), iii-store (a store into an integer, non-address field), dead-at-call / dead-at-ret (not a
    use: beyond the callee's arguments / the function's return value, with the callee analysed to its return on every
    path), frame (an sp-derived base with no auipc / lui / section value on any path)"""
    if sett in ('FULL-ADDRESS-DIFFERS', 'FULL-ADDRESS-TERM-DIFFERS'): return 'REAL', detail
    if sett == 'FULL-ADDRESS-EQUAL':
        return 'FULL-ADDRESS-EQUAL', ('the full address, same symbol + offset on both images: ' + detail)
    if sett == 'FULL-ADDRESS-TERM-EQUAL':
        return 'FULL-ADDRESS-TERM-EQUAL', ('the value is an object address plus a runtime term; its constant part is '
                                           'the same symbol + offset on both images: ' + detail)
    if sett == 'FULL-ADDRESS-TERM-EQUAL+POINTER':
        # the dataflow's MAY set holds both the static object (named, equal on both images) and the same offset on a
        # pointer a call returned or a load gave: the first settles by full address, the second needs class (iii)
        if not (c and c[0] == 'iii-disp'):
            return 'NONE', 'the value is the named object OR a runtime pointer with the same offset, and no class (iii) line covers the pointer: ' + detail
        return 'iii-disp+full-address', c[1] + ' [' + detail + ']'
    if role == 'BASE' and sett in ('FULL-ADDRESS-UNNAMED', 'FULL-ADDRESS-TERM-UNNAMED'):
        return 'NONE', 'the address names no symbol on either side: ' + detail
    if c and c[0] == 'frame' and role == 'BASE':
        return ('frame', c[1] + ' [' + detail + ']') if 'arg:sp' in detail and 'A@' not in detail else \
               ('NONE', 'frame refused: the base is not sp-only [%s]' % detail)
    if c and c[0] == 'iii-disp':
        # class (iii) holds only when the value really is a displacement on an OBJECT POINTER: the expression must
        # hold a runtime pointer leaf (an argument, a load, a call result, an AMO result) and NO auipc / lui-built
        # address of its own (such a value is settled by its full address, not by a hand citation)
        if 'A@' in detail or 'FULL-ADDRESS' in (sett or ''):
            return 'NONE', 'iii-disp refused: the value is built on an auipc, so it settles only by full address [%s]' % detail
        ok, why_ = object_pointer(run, p, detail)
        if not ok:
            return 'NONE', 'iii-disp refused: %s [%s]' % (why_, detail)
        unk = detail.split('unknown leaves: ')[-1] if 'unknown leaves' in detail else detail
        return 'iii-disp', '%s [base: %s, %s]' % (c[1], unk, why_)
    if role == 'BASE': return 'NONE', 'no class (%s)' % sett
    if role == 'STORE-DATA':
        if c and c[0] == 'iii-store': return 'iii-store', c[1]
        return 'NONE', 'no class for this store'
    if role == 'CALLEE':
        # a register that is not an argument register, holding the value at a call: no ABI convention says the callee
        # leaves it alone, so the value goes into the callee and is settled only if the callee reads it on no path
        ce = {}
        for side, a in (('X', p['xa']), ('Y', p['ya'])):
            ce[side] = LT.callee_of(s3, IMG[run][side], a, s3.frd(IMG[run][side], a, p['z']), uo)
        if ce['X'] is None or ce['Y'] is None:
            return 'NONE', 'the value is in %s at a call this tool cannot resolve (register-indirect): it may reach the callee' % reg
        for side in ('X', 'Y'):
            rd_ = LT.callee_reads(s3, IMG[run][side], ce[side][0], ce[side][1], LT.RN.index(reg))
            if rd_: return 'NONE', 'the value is in %s at the call to %s, which may read it: %s' % (reg, ce['X'][2], rd_)
        cc = call_continues(run, p, uo, reg, ce)
        if cc: return 'NONE', cc
        return 'not-read-by-callee', ('the value is in %s, not an argument register, at the call to %s, which reads it '
                                      'on no path to its return, in X and Y (no ABI convention assumed)'
                                      % (reg, ce['X'][2]))
    if role == 'RET':
        # no ABI convention: EVERY register that still holds the value when the function returns goes to its callers.
        # The return type only decides whether a0 / a1 CARRY the return value (class ii); every other register, and
        # a0 / a1 of a function that returns something else, take the complete-caller test, which needs no signature.
        sg = SIG.get(p['name'])
        ret, cite = (sg[0], sg[1]) if sg else ('?:(the return type is not in the signature table)', 'no SIG line')
        if sg and reg == 'a0' and ret.startswith('int:'):
            return 'ii', 'the function returns %s (%s)' % (ret.split(':')[1], cite)
        if sg and reg in ('a0', 'a1') and ret.startswith('pair:int:'):
            return 'ii', 'the function returns %s, two integer words in a0 and a1 (%s)' % (ret.split(':')[-1], cite)
        return dead_at_ret(run, p, reg, ret, cite)
    if role != 'ARG': return 'NONE', 'no class for a %s use' % role
    if c and c[0].startswith('i:'):           # a hand class (i) line: a vararg, whose conversion the format decides
        return 'i', c[1]
    # ARG: the callee's signature decides. Beyond its arguments the register is not a use (dead-at-call, checked).
    ce = {}
    for side, a in (('X', p['xa']), ('Y', p['ya'])):
        b_ = s3.frd(IMG[run][side], a, p['z'])
        ce[side] = LT.callee_of(s3, IMG[run][side], a, b_, uo)
    if ce['X'] is None or ce['Y'] is None: return 'NONE', 'the callee is not resolved (register-indirect or ecall)'
    sg = SIG.get(ce['X'][2])
    if not sg: return 'NONE', 'no SIG line for callee %s' % ce['X'][2]
    ret, cite, params = sg
    k = LT.RN.index(reg) - 10
    if k < len(params):
        ty, pn, kind = params[k]
        if kind == 'len':
            return 'i', 'argument %d of %s is `%s %s` (%s)' % (k, ce['X'][2], ty, pn, cite)
        if kind == 'checkval':
            return 'b', ('argument %d of %s is `%s %s`, a CHECK value (%s); CheckFailed only formats v1 and v2, with '
                         '`Printf("%%s: CHECK failed: %%s:%%d \\"%%s\\" (0x%%zx, 0x%%zx) (tid=%%u)\\n", ..., (uptr)v1, '
                         '(uptr)v2, tid)` (compiler-rt/lib/sanitizer_common/sanitizer_termination.cpp:74-76, the `0x%%zx` conversions), and the '
                         'CHECK that passes it is the one the file / line / cond arguments of this call name'
                         % (k, ce['X'][2], ty, pn, cite))
        return 'NONE', 'argument %d of %s is `%s %s` (%s), not a count / length / size / flags / mode / prot / alignment' \
            % (k, ce['X'][2], ty, pn, cite)
    # rule (e): the callee is analysed to its return on EVERY path. Not reading the register is not enough: unless the
    # callee WRITES it on every path, the value survives the call, and the trace (which does not rely on the psABI)
    # goes on in the caller past the call, where its further uses are classified like any other.
    for side in ('X', 'Y'):
        rd_ = LT.callee_reads(s3, IMG[run][side], ce[side][0], ce[side][1], LT.RN.index(reg))
        if rd_: return 'NONE', 'dead-at-call refused on %s: %s' % (side, rd_)
    cc = call_continues(run, p, uo, reg, ce)
    if cc: return 'NONE', 'dead-at-call refused: ' + cc
    kills = all(LT.callee_kills(s3, IMG[run][side], ce[side][0], ce[side][1], LT.RN.index(reg)) for side in ('X', 'Y'))
    if kills:
        return 'dead-at-call', ('%s takes %d integer-register argument(s) (%s), so a%d is not one; it reads %s on no '
                                'path to its return and writes it on every path to its return, in X and Y'
                                % (ce['X'][2], len(params), cite, k, reg))
    return 'dead-at-call', ('%s takes %d integer-register argument(s) (%s), so a%d is not one, and it reads %s on no '
                            'path to its return (checked in X and Y); it may leave the register intact, so the trace '
                            'above does NOT end at the call: it goes on in the caller to the register\'s next write '
                            '(rule (e); the psABI caller-saved convention is not relied on)'
                            % (ce['X'][2], len(params), cite, k, reg))


def object_pointer(run, p, detail):
    """(True, what it is) when EVERY runtime leaf of the value is a real object pointer: an argument register the
    pinned signature of THIS function gives a pointer type, a loaded value, or the a0 a call returns whose callee's
    signature returns a pointer. An integer argument, a value a call left in a2-a7, an AMO result, an FP or CSR
    value and a widened value are NOT object pointers (the pool owner's R2)."""
    leaves = sorted(set(re.findall(r'(?:arg:\w+|ld@0x[0-9a-f]+|ret@0x[0-9a-f]+:\w+|amo@0x[0-9a-f]+|fp@0x[0-9a-f]+|'
                                   r'csr@0x[0-9a-f]+|\?@0x[0-9a-f]+|WIDENED@0x[0-9a-f]+)', detail)))
    if not leaves: return False, 'the value holds no runtime leaf at all'
    sg = SIG.get(p['name']); ok = []; ptr = False
    for lf in leaves:
        if lf.startswith('ld@'):
            ok.append('%s is a loaded value' % lf); ptr = True; continue
        if lf.startswith('arg:'):
            r = lf[4:]
            if r == 'sp': return False, '%s is the frame pointer, not an object pointer' % lf
            if not sg: return False, 'no SIG line for this function, so %s cannot be shown to be a pointer' % lf
            k = LT.RN.index(r) - 10
            if not 0 <= k < len(sg[2]): return False, '%s is not a parameter of this function (%s)' % (lf, sg[1])
            ty, pn, kind = sg[2][k]
            if kind == 'addr':
                ok.append('%s is `%s %s` (%s)' % (lf, ty, pn, sg[1])); ptr = True; continue
            # an integer parameter is no object pointer, but it may be the INDEX added to one: it is allowed only
            # beside a real pointer leaf, never on its own (the pool owner's R2)
            ok.append('%s is `%s %s`, the index (%s)' % (lf, ty, pn, sg[1])); continue
        if lf.startswith(('amo@',)):
            ok.append('%s is an atomic result, allowed only as an index term' % lf); continue
        if lf.startswith('ret@'):
            off, rr = lf[4:].split(':')
            if rr != 'a0':
                # the pool owner's R2: a value a call left in a2-a7 is no object pointer; it may be an index term
                ok.append('%s is no object pointer (a register no callee returns a value in): index term only' % lf)
                continue
            ce = LT.callee_of(s3, IMG[run]['X'], p['xa'], s3.frd(IMG[run]['X'], p['xa'], p['z']), int(off, 16))
            if ce is None: return False, '%s: the callee is not resolved' % lf
            cs = SIG.get(ce[2])
            if not cs: return False, 'no SIG line for %s, so %s cannot be shown to be a pointer' % (ce[2], lf)
            if not cs[0].startswith('ptr:'):
                ok.append('%s is the %s %s returns: index term only' % (lf, cs[0].split(':', 1)[-1], ce[2])); continue
            ok.append('%s is the %s %s returns (%s)' % (lf, cs[0].split(':', 1)[-1], ce[2], cs[1])); ptr = True; continue
        return False, '%s is not an object pointer' % lf
    if not ptr: return False, 'no leaf of the value is an object pointer (%s)' % '; '.join(ok)
    return True, 'object pointer: ' + '; '.join(ok)


def _dar_side(run, side, a, reg, depth, seen):
    """None when the value a function leaves in `reg` at its return dies in every caller on this image; else the
    refusal. A tail caller returns in this function's place, so the test runs on it too."""
    I = IMG[run][side]
    if (side, a, reg) in seen: return None
    seen.add((side, a, reg))
    if depth > 4: return 'the chain of tail callers is deeper than 4'
    at = LT.addr_taken(s3, I, a)
    if at:
        return ('on %s the address of %s is in loadable data (%s), so its caller list cannot be shown complete'
                % (side, LT.name(s3, I, a), ', '.join(at[:4])))
    cr = LT.code_refs(s3, I, a)
    if cr:
        return ('on %s code forms the address of %s without calling it (%s), so its caller list cannot be shown '
                'complete' % (side, LT.name(s3, I, a), ', '.join(cr[:3])))
    cl = LT.all_callers(s3, I).get(a, [])
    if not cl and depth == 0:
        return 'on %s no caller of %s was found, so no caller could be traced' % (side, LT.name(s3, I, a))
    for (ca, cz, co, kind) in cl:
        xw = next((xx for o, xx, n in s3.bc_words(s3.frd(I, ca, cz)) if o == co), 0)
        if not ((xw >> 7) & 31):                 # a TAIL call: this caller returns in the function's place
            r = _dar_side(run, side, ca, reg, depth + 1, seen)
            if r: return '%s reaches %s by a tail call at +%#x, and %s' % (LT.name(s3, I, ca), LT.name(s3, I, a), co, r)
            continue
        r = LT.reads_after_call(s3, I, ca, cz, co, LT.RN.index(reg))
        if r and r.startswith('RET-LIVE'):
            # the caller reads the register nowhere but still holds the value when IT returns: the same test, one
            # level up, so the chain of callers is followed to the frame where the value dies
            r2 = _dar_side(run, side, ca, reg, depth + 1, seen)
            if r2: return '%s keeps %s to its own `ret` (%s), and %s' % (LT.name(s3, I, ca), reg, r.split()[-1], r2)
            continue
        if r: return 'on %s the caller %s reads %s after the call at +%#x (%s)' % (side, LT.name(s3, I, ca), reg, co, r)
    return None


def dead_at_ret(run, p, reg, ret, cite):
    """class dead-at-ret under the pool owner's ruling O3, applied to EVERY register that still holds the value when
    the function returns (no ABI convention): the caller list must be shown COMPLETE -- every direct call site found,
    and the function's address formed nowhere else, in data (`addr_taken`) or in code (`code_refs`) -- and EVERY
    caller traced to the register's next write."""
    seen = set(); n = {}
    for side, a in (('X', p['xa']), ('Y', p['ya'])):
        r = _dar_side(run, side, a, reg, 0, seen)
        if r: return 'NONE', 'dead-at-ret refused: ' + r
        n[side] = len(LT.all_callers(s3, IMG[run][side]).get(a, []))
    return 'dead-at-ret', ('the function returns %s (%s), so %s does not carry the return value; its caller list is '
                           'complete (no loadable data word and no code sequence forms its address) and every caller '
                           '(X %d, Y %d, tail callers followed) writes %s before any read after the call'
                           % (ret.split(':', 1)[-1], cite, reg, n['X'], n['Y'], reg))


def cstr_use(run, p, role, reg, uo, uinfo, hand=None):
    """-> (settled, citation) for one use of a C-string target: a consumer the CONSUMER table names as reading it only
    up to its NUL, a register the callee does not read (dead-at-call, machine-checked), or the function's own return
    with a CONSUMER `ret` line"""
    if role == 'ARG':
        ce = {}
        for side, a in (('X', p['xa']), ('Y', p['ya'])):
            ce[side] = LT.callee_of(s3, IMG[run][side], a, s3.frd(IMG[run][side], a, p['z']), uo)
        if ce['X'] is None or ce['Y'] is None: return False, 'NOT SETTLED: the callee is not resolved'
        k = LT.RN.index(reg) - 10
        co = CONSUMER.get('%s:%d' % (ce['X'][2], k))
        if co: return True, 'argument %d of %s: %s (%s)' % (k, ce['X'][2], co[0], co[1])
        sg = SIG.get(ce['X'][2])
        if sg and k >= len(sg[2]):
            for side in ('X', 'Y'):
                rd_ = LT.callee_reads(s3, IMG[run][side], ce[side][0], ce[side][1], LT.RN.index(reg))
                if rd_: return False, 'NOT SETTLED: dead-at-call refused on %s: %s' % (side, rd_)
            cc = call_continues(run, p, uo, reg, ce)
            if cc: return False, 'NOT SETTLED: ' + cc
            return True, ('not a use: %s takes %d integer-register argument(s) (%s), so %s is not one, and it reads '
                          '%s on no path to its return, in X and Y (what is checked is the READ; the callee may leave '
                          'the register intact, and the trace goes on in the caller past the call)'
                          % (ce['X'][2], len(sg[2]), sg[1], reg, reg))
        return False, 'NOT SETTLED: no CONSUMER line for argument %d of %s' % (k, ce['X'][2])
    if role == 'CALLEE':
        ce = {}
        for side, a in (('X', p['xa']), ('Y', p['ya'])):
            ce[side] = LT.callee_of(s3, IMG[run][side], a, s3.frd(IMG[run][side], a, p['z']), uo)
        if ce['X'] is None or ce['Y'] is None:
            return False, 'NOT SETTLED: the value is in %s at a call this tool cannot resolve' % reg
        for side in ('X', 'Y'):
            rd_ = LT.callee_reads(s3, IMG[run][side], ce[side][0], ce[side][1], LT.RN.index(reg))
            if rd_: return False, 'NOT SETTLED: %s may read %s: %s' % (ce['X'][2], reg, rd_)
        cc = call_continues(run, p, uo, reg, ce)
        if cc: return False, 'NOT SETTLED: ' + cc
        return True, ('not a use: the value is in %s, not an argument register, at the call to %s, which reads it on '
                      'no path to its return, in X and Y' % (reg, ce['X'][2]))
    if role == 'RET':
        co = CONSUMER.get('%s:ret' % p['name'])
        if co and reg == 'a0': return True, 'the return value: %s (%s)' % (co[0], co[1])
        sg = SIG.get(p['name'])
        if reg == 'a0' and not co and sg and not sg[0].startswith('void:'):
            return False, 'NOT SETTLED: a0 carries the return value of %s and no CONSUMER ret line covers it' % p['name']
        ret, cite = (sg[0], sg[1]) if sg else ('?:(the return type is not in the signature table)', 'no SIG line')
        k, cit = dead_at_ret(run, p, reg, ret, cite)
        return (k != 'NONE'), ('not a use: ' + cit if k != 'NONE' else 'NOT SETTLED: ' + cit)
    co = CONSUMER.get('%s:%s@%s' % (p['name'], role, hex(uo)))
    if co: return True, '%s (%s)' % (co[0], co[1])
    if role == 'STORE-DATA' and hand:
        # the row's CSTR hand line names the `const char *` field this store writes: it settles THIS use only
        return True, 'a store into a `const char *` field: %s' % hand
    return False, 'NOT SETTLED: no CONSUMER line for this %s use' % role


def lui_rows_settle(run, p, k_off, value_x, value_y, rowkind):
    """trace the lui behind a lui row (consumer offset k_off) and settle it; -> (verdict, measurement, detail)"""
    I = IMG[run]
    bx, by = s3.frd(I['X'], p['xa'], p['z']), s3.frd(I['Y'], p['ya'], p['z'])
    tg, unm = s3.lui_scan(bx)
    w = s3.bc_words(bx)
    js = sorted({j for (k, j), e in tg.items() if hex(w[k][0]) == k_off and e[1] == value_x})
    if len(js) != 1:
        return 'NOT CERTIFIED', 'LUI', 'lui behind the row not unique: %s' % js
    j = js[0]; lui_off = w[j][0]
    key = (run, p['xa'], lui_off)
    if key not in traced:
        traced[key] = LT.trace(s3, I['X'], I['Y'], p['xa'], p['ya'], p['z'], lui_off, ybytes=by,
                               kills=kills_for(run, p['xa'], p['ya'], p['z']),
                               noret=noret_for(run, p['xa'], p['ya'], p['z']))
    r = traced[key]
    head = '== %s %s X %#x Y %#x row +%s (%s %#x|%#x) lui +%#x' % (run, p['name'], p['xa'], p['ya'], k_off[2:], rowkind,
                                                                 value_x, value_y, lui_off)
    lines = [head] + r['lines']
    if r['parcels']:
        trace_out.append('\n'.join(lines + ['  2-byte parcels: NOT CERTIFIED']))
        return 'NOT CERTIFIED', 'LUI', 'function holds 2-byte parcels'
    ok = True; why = []; classes = []
    # COMPARE-ONLY: when EVERY use of the value on every path up to its next write is a branch / compare operand, the
    # value is never an address, never passed and never stored (the trace above shows every path)
    cmponly = bool(r['uses']) and all(u[1] == 'CMP' for u in r['uses'])
    # a compare in a row whose OTHER uses are all settled: those classes fix the value's meaning, and a branch /
    # compare operand reads no memory and builds no address
    others = [u for u in r['uses'] if u[1] != 'CMP']
    othersok = bool(others) and all(classify_use(run, p, u[1], u[2], u[0], u[4], u[5],
                                                 CL['LUI'].get((p['name'], hex(lui_off), '%s@%s' % (hex(u[0]), u[2]), u[1]))
                                                 or CL['LUI'].get((p['name'], hex(lui_off), hex(u[0]), u[1]))
                                                 or CL['LUI'].get((p['name'], hex(lui_off), '*', u[1])))[0]
                                    not in ('NONE', 'REAL') for u in others)
    for (uo, role, reg, info, sett, detail) in r['uses']:
        c = (CL['LUI'].get((p['name'], hex(lui_off), '%s@%s' % (hex(uo), reg), role))
             or CL['LUI'].get((p['name'], hex(lui_off), hex(uo), role))
             or CL['LUI'].get((p['name'], hex(lui_off), '*', role)))
        if cmponly:
            cls, cit = 'compare-only', 'every use of this value is a branch / compare operand (%d of %d; the trace ' \
                                       'above is every path up to the next write of each register that holds it)' \
                                       % (len(r['uses']), len(r['uses']))
        elif role == 'CMP' and othersok:
            cls, cit = 'compare', 'a branch / compare operand: it reads no memory and builds no address, and every ' \
                                  'other use of this value in the trace above is settled by its own class'
        else:
            cls, cit = classify_use(run, p, role, reg, uo, sett, detail, c)
        if cls == 'REAL': real.append((p['name'], hex(uo), detail))
        if cls in ('NONE', 'REAL'): ok = False
        classes.append(cls)
        lines.append('  USE +%#x %-10s %-4s %s => %s: %s' % (uo, role, reg, info, cls, cit))
        why.append('+%#x %s %s' % (uo, role, cls))
    if not r['uses']:
        ok = False; why.append('no use found'); lines.append('  NO USE FOUND: NOT CERTIFIED')
    v = 'SETTLED' if ok else ('REAL' if 'REAL' in classes else 'NOT CERTIFIED')
    # pool owner's O3 ruling (21:56Z): `compare`, dead-at-call, callee-analysed `compare-only`, (i) / (ii) / (iii),
    # store and `dead-at-ret` (with a complete caller list) are all SETTLED classes; a mixed row settles iff EVERY use
    # is in one of them (named per use above). No class is pending.
    lines.append('  ROW %s (%d uses: %s)' % (v, len(r['uses']), ', '.join('%s %d' % kv for kv in sorted(collections.Counter(classes).items()))))
    trace_out.append('\n'.join(lines))
    return v, 'LUI', '; '.join(why)


for key, p in pairs.items():
    run = key[0]; I = IMG[run]
    v, c, t3, diff = s3.tcmp(I, 'X', p['xa'], 'Y', p['ya'], p['z'])
    mine = sorted((d[0], d[3]) for d in diff)
    if mine != kitlist[key]:
        raise SystemExit('settle3: MISMATCH %s %s: %s vs kit %s' % (run, p['name'], mine, kitlist[key]))
    bx = s3.frd(I['X'], p['xa'], p['z']); by = s3.frd(I['Y'], p['ya'], p['z'])
    tx, ty = s3.targets(p['xa'], bx), s3.targets(p['ya'], by); w = s3.bc_words(bx)
    oi = {hex(o): i for i, (o, x, n) in enumerate(w)}
    st = []
    tgx, _ = s3.lui_scan(bx); tgy, _ = s3.lui_scan(by)
    for (off, r1, r2, kind, info) in diff:
        i = oi[off]
        if kind == 'lui-in-section':
            vals = info[0]
            mm = re.match(r'(0x[0-9a-f]+) in \S+ \| (0x[0-9a-f]+) in', vals)
            vx, vy = int(mm.group(1), 16), int(mm.group(2), 16)
            verdict, meas, det = lui_rows_settle(run, p, off, vx, vy, 'lui-in-section')
            rows.append((run, p['name'], hex(p['xa']), hex(p['ya']), off, kind, hex(vx), hex(vy), meas, verdict, det))
            st.append(verdict); continue
        if kind == 'unmeasured':
            rows.append((run, p['name'], hex(p['xa']), hex(p['ya']), off, kind, '', '', 'NONE', 'NOT CERTIFIED',
                         'REAL 0: %s; word X %08x Y %08x %s; no named measurement' % (r1, w[i][1], s3.bc_words(by)[i][1],
                                                                                    'equal' if w[i][1] == s3.bc_words(by)[i][1] else 'DIFFERENT')))
            st.append('NOT CERTIFIED'); continue
        if kind not in ('data-differs', 'cstr-differs') or i not in tx or i not in ty:
            rows.append((run, p['name'], hex(p['xa']), hex(p['ya']), off, kind, r1, r2, 'NONE', 'REAL', repr(info)))
            real.append((p['name'], off, kind)); st.append('REAL'); continue
        xt, yt = tx[i][1], ty[i][1]
        tr = table_reading(w, i)
        jk = JT.get((p['name'], off))
        bh = CL['BYHAND'].get((p['name'], off))
        if tr:
            k, width, cw = tr
            bxx, byy = fb(I['X'], xt, k * width), fb(I['Y'], yt, k * width)
            okk = bxx is not None and bxx == byy
            rows.append((run, p['name'], hex(p['xa']), hex(p['ya']), off, kind, hex(xt), hex(yt), 'TABLE-%dx%d' % (k, width),
                         'SETTLED' if okk else 'REAL', '%d bytes %s; consumer: %s' % (k * width, 'equal' if okk else 'DIFFER',
                                                                             '; '.join('+%#x %s' % (o, LT.dis(x)) for o, x, n in cw))))
            st.append('SETTLED' if okk else 'REAL')
            if not okk: real.append((p['name'], off, 'table'))
        elif jk:
            rows.append((run, p['name'], hex(p['xa']), hex(p['ya']), off, kind, hex(xt), hex(yt), 'JTCHECK', 'SETTLED', jk))
            st.append('SETTLED')
        elif bh:
            okk, det = byhand(run, p, off, bh[0], bh[1], xt, yt)
            vv = 'SETTLED' if okk else ('NOT CERTIFIED' if det.startswith(('bound', 'unreadable', 'unknown')) else 'REAL')
            rows.append((run, p['name'], hex(p['xa']), hex(p['ya']), off, kind, hex(xt), hex(yt), 'BYHAND-' + bh[0].split(':')[0],
                         vv, det + '; ' + bh[2]))
            st.append(vv)
            if vv == 'REAL': real.append((p['name'], off, 'byhand'))
        else:
            sxx, syy = cstr_any(I['X'], xt), cstr_any(I['Y'], yt)
            r = LT.trace(s3, I['X'], I['Y'], p['xa'], p['ya'], p['z'], int(off, 16), ybytes=by, src='ADDR',
                         kills=kills_for(run, p['xa'], p['ya'], p['z']),
                         noret=noret_for(run, p['xa'], p['ya'], p['z']))
            uses = []; allok = True
            hand = CL['CSTR'].get((p['name'], off))
            for (uo, role, reg, uinfo, usett, udetail) in r['uses']:
                okc, cc = cstr_use(run, p, role, reg, uo, uinfo, hand)
                allok = allok and okc
                uses.append('  USE +%#x %-10s %-4s %s => %s' % (uo, role, reg, uinfo, cc))
            if not r['uses']: allok = False; uses.append('  NO USE FOUND')
            if (p['name'], off) not in cstr_seen:
                cstr_seen.add((p['name'], off))
                cstr_out.append('\n'.join(['== %s %s X %#x Y %#x +%s -> X %#x Y %#x %r (%d bytes to the NUL)'
                                           % (run, p['name'], p['xa'], p['ya'], off[2:], xt, yt, sxx, len(sxx or b''))]
                                          + r['lines'] + uses + ['  ROW %s' % ('SETTLED' if allok else 'NOT CERTIFIED')]))
            det = 'equal %d byte(s) to the NUL %r; consumers: %s' % (len(sxx or b''), sxx,
                                                                     '; '.join(u.split('=> ', 1)[-1] for u in uses))
            if sxx is None or sxx != syy:
                rows.append((run, p['name'], hex(p['xa']), hex(p['ya']), off, kind, hex(xt), hex(yt), 'CSTR', 'REAL',
                             'the bytes to the NUL differ: %r | %r' % (sxx, syy)))
                real.append((p['name'], off, 'cstr')); st.append('REAL')
            elif allok:
                rows.append((run, p['name'], hex(p['xa']), hex(p['ya']), off, kind, hex(xt), hex(yt), 'CSTR', 'SETTLED', det))
                st.append('SETTLED')
            else:
                rows.append((run, p['name'], hex(p['xa']), hex(p['ya']), off, kind, hex(xt), hex(yt), 'CSTR',
                             'NOT CERTIFIED', det))
                st.append('NOT CERTIFIED')
    members[key] = (p, st)

# lui-const rows
lc_status = collections.defaultdict(list)
for (run, xa, off), p in luiconst.items():
    verdict, meas, det = lui_rows_settle(run, p, off, p['vx'], p['vy'], 'lui-const')
    rows.append((run, p['name'], hex(p['xa']), hex(p['ya']), off, 'lui-const', hex(p['vx']), hex(p['vy']), meas, verdict, det))
    lc_status[(run, xa)].append(verdict)

with open(out + '-targets.tsv', 'w') as f:
    f.write('run\tfunction\tX fn\tY fn\tword offset\tkit kind\tX target/value\tY target/value\tmeasurement\tverdict\tdetail\n')
    for r in rows: f.write('\t'.join(map(str, r)) + '\n')
with open(out + '-luitrace.txt', 'w') as f:
    f.write('# every lui row (lui-in-section targets and lui-const acceptances), traced; X sha256 %s, Y twin %s, Y pin %s\n'
            % (s3.sha(xe)[:12], s3.sha(yte)[:12], s3.sha(ype)[:12]))
    f.write('\n'.join(trace_out) + '\n')
with open(out + '-cstr-consumers.txt', 'w') as f:
    f.write('# every CSTR target: the string address traced from its addi to every use (luitrace, src ADDR), and the\n'
            '# hand reading of the consumer (luiclass.tsv CSTR line); X sha256 %s, Y twin %s, Y pin %s\n'
            % (s3.sha(xe)[:12], s3.sha(yte)[:12], s3.sha(ype)[:12]))
    f.write('\n'.join(cstr_out) + '\n')

# member status: kit-certified / settled / not certified (a kit-certified member with a lui-const row is re-judged)
summ = {}
with open(out + '-members.tsv', 'w') as f:
    f.write('run\tfunction\tX fn\tstatus\ttargets\tlui-const rows\n')
    for run in ('closure', 'paircl'):
        allx = set()
        if run == 'closure':
            tot = int(re.search(r'closure (\d+) functions', open(clf).readline()).group(1))
        else:
            tot = int(re.search(r'closure (\d+) functions paired', open(pcf).read()).group(1))
        cnt = collections.Counter()
        keys = [k for k in members if k[0] == run]
        lcx = {xa for (r, xa) in lc_status if r == run}
        for k in keys:
            p, st = members[k]; lst = lc_status.get(k, [])
            sts = st + lst
            s = 'NOT CERTIFIED' if any(x in ('NOT CERTIFIED', 'REAL') for x in sts) else 'SETTLED'
            if 'REAL' in sts: s = 'REAL'
            cnt[s] += 1
            f.write('%s\t%s\t%#x\t%s\t%s\t%s\n' % (run, p['name'], p['xa'], s, dict(collections.Counter(st)), dict(collections.Counter(lst))))
        for (r, xa), lst in lc_status.items():
            if r != run or (run, xa) in members: continue
            p = luiconst[next(kk for kk in luiconst if kk[0] == run and kk[1] == xa)]
            s = 'SETTLED' if all(x == 'SETTLED' for x in lst) else ('REAL' if 'REAL' in lst else 'NOT CERTIFIED')
            cnt[s + ' (kit EQUAL with lui-const)'] += 1
            f.write('%s\t%s\t%#x\t%s\t{}\t%s\n' % (run, p['name'], xa, s + ' (kit EQUAL with lui-const)', dict(collections.Counter(lst))))
        nonkit = len(keys) + sum(1 for (r, xa) in lc_status if r == run and (run, xa) not in members)
        cnt['KIT-CERTIFIED'] = tot - nonkit
        summ[run] = (tot, cnt)
tc = collections.Counter((r[0], r[8].split('-')[0] if r[8].startswith(('TABLE', 'BYHAND')) else r[8], r[9]) for r in rows)
print('# settle3: X %s Y pin %s Y twin %s; strictcmp3 65688e94214a; replay of every non-certified row MATCHES the kit list'
      % (s3.sha(xe)[:12], s3.sha(ype)[:12], s3.sha(yte)[:12]))
for run in ('closure', 'paircl'):
    tot, cnt = summ[run]
    print('%s: %d functions; %s' % (run, tot, '; '.join('%s %d' % kv for kv in sorted(cnt.items()))))
    print('  targets: %s' % '; '.join('%s/%s %d' % (k[1], k[2], n) for k, n in sorted(tc.items()) if k[0] == run))
print('REAL: %d %s' % (len(real), real))
