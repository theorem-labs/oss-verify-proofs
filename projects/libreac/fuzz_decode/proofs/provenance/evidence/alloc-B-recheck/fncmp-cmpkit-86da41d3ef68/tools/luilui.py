#!/usr/bin/env python3
"""luilui.py -- FAIL-OPEN #3 of cmpkit 86da41d3ef68: two lui values combined by add / sub / sh*add into ONE load / store /
AMO / jalr base are not compared as an address by the kit. For EVERY compared function (the 8 roots and every closure
member, scans/exposure.tsv) whose luiscan row counts 2 or more lui instructions in either image (`luis` >= 2, whatever
its exposure), in BOTH images, by this record's own decoder (capstone; the control-flow graph of objscan.Fn: blocks split
at every branch / jump target, `jr` dispatches into the measured jump-table cases, else every block; a `jr` in a
function with no measured switch (an auipc pair or a function pointer) is a tail call with no successor; a call to a
no-return function (luitrace.NORETURN: CheckFailed, Die, __stack_chk_fail, ..) ends the path):
  a forward data-flow over registers. A lui-derived value is ('c', n, O) -- a constant n built from the lui words O (a
  set of word offsets) -- or ('e', O, T) -- a value derived from the lui words O with its whole EXPRESSION TREE T. The
  leaves of T are lui-built constants (L), other constants (I), image addresses (A: an auipc pair or .got cell the
  flow-sensitive data-flow of luihand.Ctx.fstate knows) and non-lui registers named by their provenance before the
  instruction that reads them (R: luihand.Ctx.prov, e.g. `ENTRY a0`, `LOAD s0+0x30 [..]`, `CALL f`). lui starts
  ('c', imm << 12, {o}); every ALU op (add / sub / sh*add / and / or / xor / shifts / mul / not / neg / mv / sext, with
  register or immediate operands) on constants computes the constant; any other mix builds the tree. A load or any other
  write ends a value; a call clobbers a0-a7 / t0-t6 / ra. Join at block entries: set union; more than 64 values, or a
  tree deeper than 300 (a loop that keeps growing it), -> ('u', O): no expression.
At every load / store / AMO / jalr, a base register value whose origins hold 2 or more lui words is a SITE. Its full
address is split into additive summands (add / addi / sh*add / sub of a constant):
  CONST   no non-constant summand: the full address n + the immediate, named symbol + offset;
  OBJECT  the non-lui summands are runtime registers (the object the base points to, by provenance) and the lui words
          sit in a displacement constant and / or an INDEX summand (a non-additive expression over runtime data and the
          lui constants: and / mul / shifts, e.g. a SWAR popcount or a hash mask). Compared: the same base provenance,
          the same constant displacement and the same index expression in both images;
  TABLE   a non-lui summand is an image address (A): the table at A + displacement read through the index. Compared:
          the same index expression, and the table bytes over the index's bound (from the expression: srli / and /
          slli) plus the access width, equal in both images;
  REVIEW  a ('u', O) base, an unnamed base summand (provenance unknown or CLOBBERED), or a table whose bound the
          expression does not give.
The two images' sites must be the same words, the same instruction and the same comparison: else DIFFERS.
Writes scans/luilui.tsv (one row per examined function: luis X / Y, sites X / Y, verdict) and prints the record line
`lui+lui->base: none` or `N sites, targets equal ...` (or the DIFFERS / REVIEW rows). usage: luilui.py"""
import collections, functools, hashlib, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common, escape, objscan

CAP = 64
NODE_MAX = 300                                    # the deepest expression tree kept
M64 = 2**64 - 1
MEMOP = re.compile(r'(-?(?:0x[0-9a-f]+|\d+))?\((\w+)\)\s*$')
CALLER_SAVED = {'a%d' % i for i in range(8)} | {'t%d' % i for i in range(7)} | {'ra'}
COMB = {'add': 0, 'addw': 0, 'sh1add': 1, 'sh2add': 2, 'sh3add': 3, 'sh1add.uw': 1, 'sh2add.uw': 2, 'sh3add.uw': 3,
        'add.uw': 0, 'sub': -1, 'subw': -1}
IMMOP = {'slli': lambda a, b: a << b, 'srli': lambda a, b: (a & M64) >> b, 'srai': lambda a, b: a >> b,
         'andi': lambda a, b: a & b, 'ori': lambda a, b: a | b, 'xori': lambda a, b: a ^ b,
         'slliw': lambda a, b: sx(a << b, 32), 'srliw': lambda a, b: sx((a & 0xffffffff) >> b, 32),
         'sraiw': lambda a, b: sx(a, 32) >> b, 'addi': lambda a, b: a + b, 'addiw': lambda a, b: sx(a + b, 32)}
REGOP = {'and': lambda a, b: a & b, 'or': lambda a, b: a | b, 'xor': lambda a, b: a ^ b,
         'sll': lambda a, b: a << (b & 63), 'srl': lambda a, b: (a & M64) >> (b & 63), 'sra': lambda a, b: a >> (b & 63),
         'mul': lambda a, b: a * b}
UNOP = {'not': lambda a: ~a, 'neg': lambda a: -a, 'negw': lambda a: sx(-a, 32), 'sext.w': lambda a: sx(a, 32),
        'seqz': lambda a: int(a == 0), 'snez': lambda a: int(a != 0), 'sltz': lambda a: int(a < 0),
        'sgtz': lambda a: int(a > 0), 'zext.b': lambda a: a & 0xff, 'zext.h': lambda a: a & 0xffff,
        'zext.w': lambda a: a & 0xffffffff, 'sext.b': lambda a: sx(a, 8), 'sext.h': lambda a: sx(a, 16)}
WIDTH = {'lb': 1, 'lbu': 1, 'sb': 1, 'lh': 2, 'lhu': 2, 'sh': 2, 'lw': 4, 'lwu': 4, 'sw': 4, 'flw': 4, 'fsw': 4,
         'ld': 8, 'sd': 8, 'fld': 8, 'fsd': 8}


def sx(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


@functools.lru_cache(maxsize=None)
def size(t):
    """the DEPTH of a tree (shared subexpressions are shared objects: the depth bounds a loop that keeps growing a value,
    without counting a shared subexpression once per use); memoised per node"""
    if t[0] != 'op':
        return 1
    return 1 + max(size(c) for c in t[2])


@functools.lru_cache(maxsize=None)
def origins(t):
    if t[0] == 'L':
        return t[2]
    if t[0] == 'op':
        return frozenset().union(*(origins(c) for c in t[2]))
    return frozenset()


def orig(v):
    return v[2] if v[0] == 'c' else v[1]


_RENDER = {}


def render(t, img):
    """the text of a tree; a subexpression whose text passes 20000 characters is named by the sha256 of its text"""
    key = (id(img), t)
    s = _RENDER.get(key)
    if s is None:
        if t[0] in ('L', 'I'):
            s = '%#x' % (t[1] & M64)
        elif t[0] == 'A':
            s = 'ABS %s' % img.home(t[1])
        elif t[0] == 'R':
            s = '(%s)' % t[1]
        else:
            s = '%s(%s)' % (t[1], ', '.join(render(c, img) for c in t[2]))
        if len(s) > 20000:
            s = 'E#%s' % hashlib.sha256(s.encode()).hexdigest()[:16]
        _RENDER[key] = s
    return s


def show(s, n=700):
    return s if len(s) <= n else '%s.. [%d chars, sha256 %s]' % (s[:n], len(s), hashlib.sha256(s.encode()).hexdigest()[:16])


def cap(vals):
    if len(vals) <= CAP:
        return frozenset(vals)
    return frozenset({('u', frozenset().union(*(orig(v) for v in vals)))})


def mk(o_, t):
    return ('e', o_, t) if size(t) <= NODE_MAX else ('u', o_)


def summands(t):
    """the additive summands of a tree (add / addi / sh*add / sub of a constant)"""
    if t[0] == 'op':
        mn, ch = t[1], t[2]
        if mn in ('add', 'addi'):
            return summands(ch[0]) + summands(ch[1])
        if mn in ('sh1add', 'sh2add', 'sh3add'):
            return [('op', 'slli', (ch[0], ('I', int(mn[2])))) ] + summands(ch[1])
        if mn == 'sub' and ch[1][0] in ('I', 'L'):
            return summands(ch[0]) + [(ch[1][0], -ch[1][1]) + ch[1][2:]]
    return [t]


def bound(t):
    """the largest value of a non-negative index tree, or None when the expression does not give one"""
    if t[0] in ('I', 'L'):
        return t[1] & M64
    if t[0] != 'op':
        return None
    mn, ch = t[1], t[2]
    if mn == 'srli' and ch[1][0] == 'I':
        return M64 >> ch[1][1]
    if mn == 'srliw' and ch[1][0] == 'I':
        return 0xffffffff >> ch[1][1]
    if mn in ('and', 'andi'):
        bs = [b for b in (bound(c) for c in ch) if b is not None]
        return min(bs) if bs else None
    if mn == 'slli' and ch[1][0] == 'I':
        b = bound(ch[0])
        return b << ch[1][1] if b is not None else None
    if mn in ('add', 'addi', 'mul'):
        b1, b2 = bound(ch[0]), bound(ch[1])
        return None if b1 is None or b2 is None else (b1 + b2 if mn != 'mul' else b1 * b2)
    if mn in ('zext.b', 'zext.h', 'zext.w'):
        return {'zext.b': 0xff, 'zext.h': 0xffff, 'zext.w': 0xffffffff}[mn]
    return None


def classify(v, imm, img):
    """one site's comparison: (kind, text, key, table) -- table = (address, extent) to compare by bytes, or None"""
    if v[0] == 'u':
        fo = lambda x: '+%#x' % x if isinstance(x, int) else '%s+%#x' % (x[0][:40], x[1])
        return 'REVIEW', 'REVIEW: constants %s: the expression was dropped (too large / too many values)' % \
            ','.join(fo(x) for x in sorted(v[1])), None, None
    if v[0] == 'c':
        addr = v[1] + imm
        return 'CONST', '%#x = %s' % (addr & M64, img.home(addr)), img.home(addr), None
    sm = summands(v[2])
    const = imm + sum(s[1] for s in sm if s[0] in ('I', 'L'))
    base = [s for s in sm if s[0] in ('R', 'A')]
    idx = [s for s in sm if s[0] == 'op']
    itxt = ' + '.join(sorted(render(s, img) for s in idx)) or '-'
    ishow = show(itxt)
    if any(s[0] == 'R' and ('?' in s[1] or 'CLOBBERED' in s[1]) for s in base):
        return 'REVIEW', 'REVIEW: an unnamed base summand: %s' % show(render(v[2], img)), None, None
    tabs = [s for s in base if s[0] == 'A']
    if tabs:
        if len(tabs) > 1 or len(idx) != 1:
            return 'REVIEW', 'REVIEW: table base with %d image addresses and %d index summands: %s' % (
                len(tabs), len(idx), show(render(v[2], img))), None, None
        b = bound(idx[0])
        if b is None or b > 0x10000:
            return 'REVIEW', 'REVIEW: table %s + %#x, index bound unknown / too large: %s' % (
                img.home(tabs[0][1]), const, ishow), None, None
        names = ' + '.join(sorted(render(s, img) for s in base if s[0] == 'R'))
        return 'TABLE', 'TABLE %s%s + %#x indexed by %s (index <= %#x)' % (
            img.home(tabs[0][1]), (' + ' + names) if names else '', const, ishow, b), \
            ('TABLE', names, itxt, b), (tabs[0][1] + const, b)
    if not base:
        return 'LUIADDR', 'LUI-BUILT %#x = %s + index %s' % (const & M64, img.home(const), ishow), \
            ('LUIADDR', img.home(const), itxt), None
    names = ' + '.join(sorted(render(s, img) for s in base))
    return 'OBJECT', 'OBJECT base %s + %#x%s' % (names, const, (' + index ' + ishow) if idx else ''), \
        ('OBJECT', names, const, itxt), None


def step(regs, o, mn, op, a, z, img, ctx, sites, k):
    ops = [x.strip() for x in op.split(',')] if op else []
    get = lambda r: regs.get(r, frozenset())
    rd = ops[0] if ops else None
    base_m = mn.split('.')[0]
    is_mem = base_m in ('lb', 'lbu', 'lh', 'lhu', 'lw', 'lwu', 'ld', 'lr', 'flw', 'fld', 'sb', 'sh', 'sw', 'sd', 'sc',
                        'fsw', 'fsd') or base_m.startswith('amo')

    def leaf(r):
        """a non-lui register before instruction k: an image address when the flow-sensitive data-flow knows one; a
        value LOADED from a fixed image address, named by the 8 bytes there (the same name in both images only when the
        bytes are equal); else its provenance"""
        fv = ctx.fstate(a, z).get(k, {}).get(r, set())
        if len(fv) == 1 and list(fv)[0][0] == 'abs' and isinstance(list(fv)[0][1], int) and list(fv)[0][1] >= 0x10000:
            return ('A', list(fv)[0][1])
        pv = ctx.prov(a, z, k, r) or '?'
        lm = re.match(r'^(?:linear: )*LOAD (0x[0-9a-f]+)$', pv)
        if lm:
            b8 = escape.sc.frd(img.I, int(lm.group(1), 16), 8)
            if b8:
                return ('R', 'a load of the image constant %s' % b8.hex())
        return ('R', pv)

    def tree(v, r):
        if v is None:
            return leaf(r)
        if v[0] == 'c':
            return ('L', v[1], v[2]) if v[2] else ('I', v[1])
        return v[2]

    if is_mem or mn in ('jalr', 'jr'):
        m = MEMOP.search(op) if op else None
        base, imm = (m.group(2), int(m.group(1) or '0', 0)) if m else ((ops[-1] if ops else None), 0)
        for v in get(base):
            if len(orig(v)) >= 2:
                kind, text, key, table = classify(v, imm, img)
                w = WIDTH.get(base_m, 8 if mn.endswith('.d') else 4)
                sites.append((o, '%s %s' % (mn, op), tuple(sorted(orig(v))), kind, text, key,
                              (table[0], table[1] + w) if table else None))
        is_load = base_m in ('lb', 'lbu', 'lh', 'lhu', 'lw', 'lwu', 'ld', 'lr', 'flw', 'fld') or \
            (base_m in ('sc',) or base_m.startswith('amo'))
        if is_load and rd and rd not in ('zero',):
            regs.pop(rd, None)
        if mn in ('jalr',) and (len(ops) == 1 or ops[0] == 'ra' or '(' in op):
            for r in CALLER_SAVED:
                regs.pop(r, None)
        return
    if mn in ('jal', 'call') and (len(ops) <= 1 or ops[0] == 'ra'):
        for r in CALLER_SAVED:
            regs.pop(r, None)
        return
    if not ops or rd in ('zero', 'sp') or mn in escape.BR or mn in ('j', 'ret', 'ecall', 'ebreak') or mn.startswith('fence'):
        return
    if mn == 'lui':
        regs[rd] = frozenset({('c', sx(int(ops[1], 0) << 12, 32), frozenset({o}))}); return
    if mn == 'mv' and len(ops) == 2:
        s = get(ops[1])
        if s:
            regs[rd] = s
        else:
            regs.pop(rd, None)
        return
    if mn in UNOP and len(ops) == 2:
        s = get(ops[1])
        if not s:
            regs.pop(rd, None); return
        regs[rd] = cap({('c', UNOP[mn](v[1]), v[2]) if v[0] == 'c' else
                        mk(orig(v), ('op', mn, (tree(v, ops[1]),))) if v[0] == 'e' else v for v in s})
        return
    if mn in IMMOP and len(ops) == 3:
        s = get(ops[1])
        if not s:
            regs.pop(rd, None); return
        c = int(ops[2], 0)
        regs[rd] = cap({('c', IMMOP[mn](v[1], c), v[2]) if v[0] == 'c' else
                        mk(orig(v), ('op', mn, (tree(v, ops[1]), ('I', c)))) if v[0] == 'e' else v for v in s})
        return
    if (mn in COMB or mn in REGOP) and len(ops) == 3:
        s1, s2 = get(ops[1]), get(ops[2])
        if ops[1] == 'zero':
            s1 = frozenset({('c', 0, frozenset())})
        if ops[2] == 'zero':
            s2 = frozenset({('c', 0, frozenset())})
        if not any(orig(v) for v in s1) and not any(orig(v) for v in s2):
            regs.pop(rd, None); return
        out = set()
        for v1 in (s1 or {None}):
            for v2 in (s2 or {None}):
                o1 = orig(v1) if v1 else frozenset(); o2 = orig(v2) if v2 else frozenset()
                if v1 and v2 and v1[0] == 'c' and v2[0] == 'c':
                    if mn in COMB:
                        n = COMB[mn]
                        val = v1[1] - v2[1] if n < 0 else (v1[1] << n) + v2[1]
                        if mn in ('addw', 'subw'):
                            val = sx(val, 32)
                    else:
                        val = REGOP[mn](v1[1], v2[1])
                    out.add(('c', val, o1 | o2))
                elif (v1 and v1[0] == 'u') or (v2 and v2[0] == 'u'):
                    out.add(('u', o1 | o2))
                else:
                    out.add(mk(o1 | o2, ('op', mn, (tree(v1, ops[1]), tree(v2, ops[2])))))
        regs[rd] = cap(out); return
    regs.pop(rd, None)


def analyse(ctx, a, z):
    import luitrace
    img = ctx.img
    f = objscan.Fn(img, a, z)
    ins = f.ins
    for s in f.lead:                                  # a call to a no-return function (luitrace.NORETURN) ends the path
        kd, tg, _ = f.kind[f.end[s]]
        if kd == 'call' and tg is not None and tg in img.starts and img.name_at(tg) in luitrace.NORETURN:
            f.succ[s] = []
        if kd == 'ijmp' and (img.wtarget.get(a + ins[f.end[s]][0]) in img.starts or not img.cases.get(a)):
            f.succ[s] = []                            # a `jr` tail call (auipc pair or function pointer), no switch
    IN = {f.lead[0]: {}}
    work = [f.lead[0]]
    sites, iters = {}, 0
    while work and iters < 20000:
        iters += 1
        s = work.pop()
        regs = dict(IN[s])
        local = []
        for k in range(s, f.end[s] + 1):
            o, mn, op, n = ins[k]
            step(regs, o, mn, op, a, z, img, ctx, local, k)
        for x in local:
            sites.setdefault(x[:3], set()).add(x[3:])
        for t in f.succ[s]:
            if t not in IN:
                IN[t] = dict(regs); work.append(t); continue
            nr, ch = dict(IN[t]), False
            for r, v in regs.items():
                u = cap(nr.get(r, frozenset()) | v)
                if u != nr.get(r, frozenset()):
                    nr[r] = u; ch = True
            if ch:
                IN[t] = nr
                if t not in work:
                    work.append(t)
    return {k_: sorted(v, key=str) for k_, v in sites.items()}


def compare(X, Y, sx_, sy_):
    """per site: 'EQUAL <kind>' / 'DIFFERS ..' / 'REVIEW ..'; tables compared by their bytes in both images"""
    out = {}
    for key in sorted(set(sx_) | set(sy_)):
        a, b = sx_.get(key), sy_.get(key)
        if a is None or b is None:
            out[key] = 'DIFFERS: site in one image only'; continue
        if any(x[0] == 'REVIEW' for x in a + b):
            out[key] = 'REVIEW'; continue
        if [x[2] for x in a] != [x[2] for x in b]:
            out[key] = 'DIFFERS: %s | %s' % ([x[1] for x in a], [x[1] for x in b]); continue
        bad = []
        for x, y in zip(a, b):
            if x[3]:
                bx, by = escape.sc.frd(X.I, x[3][0], x[3][1]), escape.sc.frd(Y.I, y[3][0], y[3][1])
                if bx is None or bx != by:
                    bad.append('table bytes differ at %#x / %#x (%d bytes)' % (x[3][0], y[3][0], x[3][1]))
        out[key] = ('DIFFERS: ' + '; '.join(bad)) if bad else 'EQUAL ' + '/'.join(sorted({x[0] for x in a}))
    return out


def main():
    import luihand
    CX, CY = luihand.Ctx(common.CGIF_B_TWIN), luihand.Ctx(common.DECODE_B_TWIN)
    X, Y = CX.img, CY.img
    common.jump_cases(X, Y)                         # every measured rel4 jump table: a `jr` goes to its cases
    rows, cnt, kinds, nsites = [], collections.Counter(), collections.Counter(), 0
    luis = lambda s: int(re.search(r'luis=(\d+)', s).group(1)) if 'luis=' in s else 0
    fmt = lambda ss, vd: ' ;; '.join('+%#x %s [lui %s] %s => %s' % (k_[0], k_[1], ','.join('+%#x' % x for x in k_[2]),
                                                                   ' | '.join(x[1] for x in v), vd.get(k_, '-'))
                                     for k_, v in sorted(ss.items())) or '-'
    for l in list(open(os.path.join(common.SCANS, 'exposure.tsv')))[1:]:
        c = l.rstrip('\n').split('\t')
        q, ax, ay, z = c[0], int(c[1], 16), (int(c[2], 16) if c[2].startswith('0x') else None), int(c[3])
        lx, ly = luis(c[4]), luis(c[5])
        if max(lx, ly) < 2:
            continue
        sx_ = analyse(CX, ax, z)
        sy_ = analyse(CY, ay, z) if ay is not None else {}
        vd = compare(X, Y, sx_, sy_)
        if not vd:
            v = 'none'
        elif any(x.startswith('DIFFERS') for x in vd.values()):
            v = 'DIFFERS'
        elif any(x.startswith('REVIEW') for x in vd.values()):
            v = 'REVIEW'
        else:
            v = 'EQUAL'
        cnt[v] += 1
        kinds.update(vd.values())
        nsites += len(vd)
        rows.append((q, '%#x' % ax, '%#x' % ay if ay else '-', str(lx), str(ly), fmt(sx_, vd), fmt(sy_, vd), v))
    with open(os.path.join(common.SCANS, 'luilui.tsv'), 'w') as f:
        f.write('function (qualified)\tX addr\tY addr\tluis X\tluis Y\tsites X (lui+lui -> base: word, instruction, lui words, '
                'comparison => site verdict)\tsites Y\tverdict\n')
        for r in rows:
            f.write('\t'.join(r) + '\n')
    print('functions with luis >= 2 in either image: %d; verdicts %s' % (len(rows), dict(sorted(cnt.items()))))
    print('sites: %d; %s' % (nsites, dict(sorted(kinds.items()))))
    if nsites == 0:
        print('lui+lui->base: none')
    else:
        print('lui+lui->base: %d sites, %s' % (nsites, 'targets equal (by symbol + offset, base + index, or table bytes)'
                                                if not cnt['DIFFERS'] and not cnt['REVIEW'] else 'SEE THE DIFFERS / REVIEW ROWS'))
    for r in rows:
        if r[7] != 'none':
            print('  %s %s' % (r[7], r[0][:90]))
            for s in r[5].split(' ;; '):
                print('    X %s' % s[:400])


if __name__ == '__main__':
    main()
