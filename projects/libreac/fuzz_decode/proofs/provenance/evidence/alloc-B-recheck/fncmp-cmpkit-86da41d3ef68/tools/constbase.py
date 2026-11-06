#!/usr/bin/env python3
"""constbase.py -- the cmpkit 86da fail-opens (a)-(h) (<agent> 21:53Z): an EQUAL* verdict is no evidence where an address
value reaches a load / store / jalr / AMO base. For EVERY compared function (the 8 roots and every closure member,
scans/exposure.tsv), in BOTH images, by this record's own decoder (capstone; objscan.Fn's control-flow graph: blocks split
at every branch / jump target and after every branch / jump / call / return, fall-through edges kept, `jr` dispatches
into the measured jump-table cases (every switch `jr` of the closure has them); a `jr` in a function with no measured
switch (an auipc pair or a function pointer) is a tail call, its a0-a7 passed; a call to a no-return function ends the
path), a forward
data-flow tracks EVERY CONSTANT the code builds without auipc, and every value computed from one:
  sources   lui (c.lui decodes as lui; no compressed instruction is in these images), addi / addiw rd, zero, imm (li);
  steps     every ALU op on them (add / sub / sh*add / and / or / xor / addi / addiw / ori / xori / andi / slli / srli /
            srai / shifts / mul / not / neg / mv / sext / zext): constants fold, any other mix builds the expression tree
            (luilui.py's trees: lui / li constants, image addresses, non-constant registers by provenance);
  memory    a store of a tracked value to a PRIVATE stack slot (spslot.py: no pointer to the slot is passed to a call or
            ecall, stored or returned, and no sp-derived pointer reads or writes it) and its reload keep it (the slot by
            its offset from sp at entry); FP moves (fmv.*) and CSR round trips (csrrw / csrr) keep it; any other load
            ends a value. A tracked value stored ANYWHERE ELSE (a non-private slot, any object) is a STORED site: the
            value itself is classed and compared the way a base is (a number outside both images is no site);
  calls     a tracked value in a0-a7 at a call or tail call that may form an address (an expression, or a constant
            >= 0x10000: the images start at 0x10000, so a smaller number names no image object and is the same number
            in both images) is a PASSED site, and such a value in a0 / a1 at a return a RETURNED site: the value itself
            is classed and compared the way a base is. The callee (or caller), whose code the kit compares, then gets
            the same value in both images; every compared function is analysed on its own, so its own bases are sites
            too. A call clobbers the caller-saved registers.
At every load / store / AMO / jalr whose base register holds a tracked value, a SITE; its full address (with the
instruction's IMMEDIATE) is split into summands and classed as luilui.py does: CONST (no non-constant summand: the full
address; inside an image it must name the same symbol + offset in both images, outside both images the same number),
OBJECT (a runtime base + constant displacement + index expression, compared whole), TABLE (an image address + index:
the bytes over the index bound compared), REVIEW (no expression / unnamed base / no bound); STORED- / PASSED- /
RETURNED-<kind> for a value stored, passed or returned.
The site key is (function, offset, instruction, the origins of its constants); the two images' sites must have the same
keys and the same comparison: else DIFFERS.
(CONSTBASE_ONLY=addr,addr.. limits the run to those cgif-B members, for the controls.)
Writes scans/constbase.tsv (one row per function with a site: sites X / Y, verdict) and prints the counts per kind and
the sites per shape. usage: constbase.py"""
import collections, functools, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common, escape, objscan, spslot
import luilui as LL
LL.CAP = 256                                      # more li constants than luilui tracks: up to 256 values per register

ARGS = ['a%d' % i for i in range(8)]
WIDEN = 4                                         # a block entry that changed this often: its changing values widen


class Analyser:
    def __init__(self, ctx):
        import luitrace
        self.ctx, self.img = ctx, ctx.img
        self.noreturn = luitrace.NORETURN
        self.memo = {}
        self.sizes = {f[0]: f[1] for f in self.img.funcs}
        self.reloads = 0
        self.img.home = functools.lru_cache(maxsize=None)(self.img.home)     # symbol + offset lookups, memoised

    def judge(self, raw):
        """a site's comparison, once per distinct (value, immediate): (kind, text, key, table to compare by bytes)"""
        what, v, imm, w = raw
        img = self.img
        kind, text, key, table = LL.classify(v, imm, img)
        if kind == 'CONST':
            ad = (v[1] + imm) & LL.M64
            inimg = img.I.sec(ad) is not None
            key = ('CONST', img.home(ad), ad) if inimg else ('CONST-OUTSIDE', ad)
            text += '' if inimg else ' (outside both images: compared as the number)'
        elif kind == 'LUIADDR':
            key = key + (int(text.split(' ')[1], 16),)    # (LUIADDR, symbol + offset, index text, the number)
        if what in ('STORED', 'PASSED', 'RETURNED'):
            return what + '-' + kind, 'the value %s: %s' % (what.lower(), text), key, table
        return kind, text, key, (table[0], table[1] + w) if table else None

    def step(self, regs, o, mn, op, a, z, fname, sites, k, path):
        img, ctx = self.img, self.ctx
        ops = [x.strip() for x in op.split(',')] if op else []
        get = lambda r: regs.get(r, frozenset())
        rd = ops[0] if ops else None
        base_m = mn.split('.')[0]
        is_ld = base_m in ('lb', 'lbu', 'lh', 'lhu', 'lw', 'lwu', 'ld', 'lr', 'flw', 'fld')
        is_st = base_m in ('sb', 'sh', 'sw', 'sd', 'sc', 'fsw', 'fsd') or base_m.startswith('amo')

        def leaf(r):
            fv = ctx.fstate(a, z).get(k, {}).get(r, set())
            if len(fv) == 1 and list(fv)[0][0] == 'abs' and isinstance(list(fv)[0][1], int) and list(fv)[0][1] >= 0x10000:
                return ('A', list(fv)[0][1])
            pv = ctx.prov(a, z, k, r) or '?'
            lm = re.match(r'^(?:linear: )*LOAD (0x[0-9a-f]+)$', pv)
            if lm:
                b8 = escape.sc.frd(img.I, int(lm.group(1), 16), 8)
                if b8:
                    return ('R', 'a load of the image constant %s' % b8.hex())
            am = re.match(r'^((?:linear: )*)ABS (0x[0-9a-f]+)$', pv)
            if am:
                # an unnamed image address: named by the 16 bytes there (the same name in both images only when equal)
                b16 = escape.sc.frd(img.I, int(am.group(2), 16), 16)
                if b16:
                    return ('R', '%sABS (an unnamed image address holding %s)' % (am.group(1), b16.hex()))
            return ('R', pv)

        def tree(v, r):
            if v is None:
                return leaf(r)
            if v[0] == 'c':
                return ('L', v[1], v[2]) if v[2] else ('I', v[1])
            return v[2]

        if is_ld or is_st or mn in ('jalr', 'jr'):
            m = LL.MEMOP.search(op) if op else None
            base, imm = (m.group(2), int(m.group(1) or '0', 0)) if m else ((ops[-1] if ops else None), 0)
            w = LL.WIDTH.get(base_m, 8 if mn.endswith('.d') else 4)
            for v in get(base):
                if LL.orig(v):
                    sites.append((path, fname, o, '%s %s' % (mn, op), tuple(sorted(LL.orig(v))), ('BASE', v, imm, w)))
            slot = None
            if m and m.group(2) == 'sp':
                fr = spslot.frame(img, a, z)
                ok, why = fr.private(k, imm, w)
                if ok:
                    slot = '[sp@%+d]' % (fr.sp_at[k] + imm)       # a private slot, by its offset from sp at entry
            if is_st and ops and slot is not None:
                if ops[0] in regs:
                    regs[slot] = regs[ops[0]]                 # a spill of a tracked value to a private slot
                else:
                    regs.pop(slot, None)
            data = (ops[1] if len(ops) > 1 else None) if (base_m == 'sc' or base_m.startswith('amo')) else (ops[0] if ops else None)
            if is_st and data in regs and slot is None:
                # a tracked value stored to memory a reader outside this trace may load (any non-private slot, any
                # other object): the stored value is compared as a full address, the way a base is
                for v in regs[data]:
                    if v[0] == 'c' and img.I.sec(v[1] & LL.M64) is None:
                        continue                              # a number outside both images names no image object
                    sites.append((path, fname, o, '%s %s' % (mn, op), tuple(sorted(LL.orig(v))), ('STORED', v, 0, w)))
            if is_ld and rd and rd != 'zero':
                if slot is not None and slot in regs:
                    regs[rd] = regs[slot]                     # its reload
                    self.reloads += 1
                else:
                    regs.pop(rd, None)
            if base_m in ('sc',) or base_m.startswith('amo'):
                if rd and rd != 'zero':
                    regs.pop(rd, None)
            return
        if mn.startswith('fmv') and len(ops) == 2 or mn in ('fmv.d', 'fmv.s'):
            if ops[1] in regs:
                regs[rd] = regs[ops[1]]
            else:
                regs.pop(rd, None)
            return
        if mn in ('csrrw', 'csrw', 'csrr', 'csrrs', 'csrrc'):
            if mn == 'csrw' and len(ops) == 2:
                if ops[1] in regs:
                    regs['csr:' + ops[0]] = regs[ops[1]]
                return
            if mn == 'csrr' and len(ops) == 2:
                if ('csr:' + ops[1]) in regs:
                    regs[rd] = regs['csr:' + ops[1]]
                else:
                    regs.pop(rd, None)
                return
            if mn == 'csrrw' and len(ops) == 3:
                old = regs.get('csr:' + ops[1])
                if ops[2] in regs:
                    regs['csr:' + ops[1]] = regs[ops[2]]
                else:
                    regs.pop('csr:' + ops[1], None)
                if old is not None and rd != 'zero':
                    regs[rd] = old
                elif rd != 'zero':
                    regs.pop(rd, None)
                return
            regs.pop(rd, None)
            return
        if not ops or rd in ('zero', 'sp') or mn in escape.BR or mn in ('j', 'ret', 'ecall', 'ebreak') or mn.startswith('fence'):
            return
        if mn == 'lui':
            regs[rd] = frozenset({('c', LL.sx(int(ops[1], 0) << 12, 32), frozenset({(fname, o)}))}); return
        if mn in ('addi', 'addiw') and len(ops) == 3 and ops[1] == 'zero':
            c = int(ops[2], 0)
            regs[rd] = frozenset({('c', c, frozenset({(fname, o)}))}); return
        if mn == 'mv' and len(ops) == 2:
            s = get(ops[1])
            if s:
                regs[rd] = s
            else:
                regs.pop(rd, None)
            return
        if mn in LL.UNOP and len(ops) == 2:
            s = get(ops[1])
            if not s:
                regs.pop(rd, None); return
            regs[rd] = LL.cap({('c', LL.UNOP[mn](v[1]), v[2]) if v[0] == 'c' else
                               LL.mk(LL.orig(v), ('op', mn, (tree(v, ops[1]),))) if v[0] == 'e' else v for v in s})
            return
        if mn in LL.IMMOP and len(ops) == 3:
            s = get(ops[1])
            if not s:
                regs.pop(rd, None); return
            c = int(ops[2], 0)
            regs[rd] = LL.cap({('c', LL.IMMOP[mn](v[1], c), v[2]) if v[0] == 'c' else
                               LL.mk(LL.orig(v), ('op', mn, (tree(v, ops[1]), ('I', c)))) if v[0] == 'e' else v for v in s})
            return
        if (mn in LL.COMB or mn in LL.REGOP) and len(ops) == 3:
            s1, s2 = get(ops[1]), get(ops[2])
            if ops[1] == 'zero':
                s1 = frozenset({('c', 0, frozenset())})
            if ops[2] == 'zero':
                s2 = frozenset({('c', 0, frozenset())})
            if not any(LL.orig(v) for v in s1) and not any(LL.orig(v) for v in s2):
                regs.pop(rd, None); return
            out = set()
            for v1 in (s1 or {None}):
                for v2 in (s2 or {None}):
                    o1 = LL.orig(v1) if v1 else frozenset(); o2 = LL.orig(v2) if v2 else frozenset()
                    if v1 and v2 and v1[0] == 'c' and v2[0] == 'c':
                        if mn in LL.COMB:
                            n = LL.COMB[mn]
                            val = v1[1] - v2[1] if n < 0 else (v1[1] << n) + v2[1]
                            if mn in ('addw', 'subw'):
                                val = LL.sx(val, 32)
                        else:
                            val = LL.REGOP[mn](v1[1], v2[1])
                        out.add(('c', val, o1 | o2))
                    elif (v1 and v1[0] == 'u') or (v2 and v2[0] == 'u'):
                        out.add(('u', o1 | o2))
                    else:
                        out.add(LL.mk(o1 | o2, ('op', mn, (tree(v1, ops[1]), tree(v2, ops[2])))))
            regs[rd] = LL.cap(out); return
        regs.pop(rd, None)

    def analyse(self, a):
        """the raw sites of the function at a, analysed on its own (memoised): every base, stored value, passed value and
        returned value that carries a tracked constant"""
        if a in self.memo:
            return self.memo[a]
        if a not in self.sizes:
            return []
        img = self.img
        z = self.sizes[a]
        fname = img.name_at(a)
        f = objscan.Fn(img, a, z)
        ins = f.ins
        for s in f.lead:
            kd, tg, _ = f.kind[f.end[s]]
            if kd == 'call' and tg is not None and tg in img.starts and img.name_at(tg) in self.noreturn:
                f.succ[s] = []
            if kd == 'ijmp' and (img.wtarget.get(a + ins[f.end[s]][0]) in self.sizes or not img.cases.get(a)):
                f.succ[s] = []                            # a `jr` tail call (auipc pair or function pointer), no switch
        IN = {f.lead[0]: {}}
        work = [f.lead[0]]
        sites, iters, grow = {}, 0, collections.Counter()
        while work and iters < 20000:
            iters += 1
            s = work.pop()
            regs = dict(IN[s])
            for k in range(s, f.end[s] + 1):
                o, mn, op, n = ins[k]
                kd, tg, inside = f.kind[k]
                if kd == 'ijmp' and (img.wtarget.get(a + o) in self.sizes or not img.cases.get(a)):
                    kd = 'tail'
                local = []
                if kd in ('call', 'tail'):
                    if mn in ('jalr', 'jr'):
                        self.step(dict(regs), o, mn, op, a, z, fname, local, k, ())   # a jalr base check only
                    callee = tg if tg is not None else img.wtarget.get(a + o)
                    cname = img.name_at(callee) if callee is not None and callee in img.starts else 'an indirect callee'
                    # a value passed to a callee that may form an address (an expression, or a constant >= 0x10000:
                    # the images start at 0x10000, so a smaller number names no image object and is the same number in
                    # both images) is a PASSED site, compared as a full address the way a base is: the callee, whose
                    # code the kit compares, receives the same value in both images
                    for r in ARGS:
                        for v in regs.get(r, ()):
                            if v[0] != 'c' or (v[1] & LL.M64) >= 0x10000:
                                local.append(((), fname, o, '%s -> %s %s' % (mn, cname[:60], r),
                                              tuple(sorted(LL.orig(v))), ('PASSED', v, 0, 8)))
                    for r in LL.CALLER_SAVED:
                        regs.pop(r, None)
                elif kd == 'ret':
                    for r in ('a0', 'a1'):
                        for v in regs.get(r, ()):
                            if v[0] != 'c' or (v[1] & LL.M64) >= 0x10000:
                                local.append(((), fname, o, 'return %s' % r, tuple(sorted(LL.orig(v))),
                                              ('RETURNED', v, 0, 8)))
                else:
                    self.step(regs, o, mn, op, a, z, fname, local, k, ())
                for x in local:
                    sites.setdefault(x[:5], set()).add(x[5:])
            for t in f.succ[s]:
                if t not in IN:
                    IN[t] = dict(regs); work.append(t); continue
                nr, ch = dict(IN[t]), False
                grow[t] += 1
                for r, v in regs.items():
                    old = nr.get(r, frozenset())
                    u = LL.cap(old | v)
                    if u != old:
                        if grow[t] > WIDEN and old and not any(x[0] == 'e' and x[2][0] == 'R' and
                                                               x[2][1].startswith('loop-varying') for x in old):
                            # a loop keeps changing this register: one value, varying, named by its values at the loop
                            # entry (so the comparison still sees where it starts in each image)
                            # ordered canonically: never by str() of a frozenset, whose order changes with the hash seed
                            first = sorted(old | v, key=lambda x: (LL.size(x[2]) if x[0] == 'e' else 0,
                                                                   x[1] if x[0] == 'c' else 0,
                                                                   LL.render(x[2], img) if x[0] == 'e' else '',
                                                                   sorted(LL.orig(x))))[:6]
                            u = frozenset({('e', frozenset().union(*(LL.orig(x) for x in u)),
                                            ('R', 'loop-varying value; at the loop entry: %s' % ' | '.join(
                                                LL.render(x[2], img) if x[0] == 'e' else '%#x' % (x[1] & LL.M64)
                                                if x[0] == 'c' else 'unknown' for x in first)))})
                        elif any(x[0] == 'e' and x[2][0] == 'R' and x[2][1].startswith('loop-varying') for x in old):
                            continue                      # already widened: the loop adds nothing
                        nr[r] = u; ch = True
                if ch:
                    IN[t] = nr
                    if t not in work:
                        work.append(t)
        out = [k_ + v_ for k_, vs in sites.items() for v_ in vs]
        self.memo[a] = out
        return out


def lui_rows():
    """(member, lui word offset) -> the settlement class of that lui row (scans/luiclass.tsv)"""
    out = {}
    p = os.path.join(common.SCANS, 'luiclass.tsv')
    for l in (list(open(p))[1:] if os.path.exists(p) else []):
        c = l.rstrip('\n').split('\t')
        out[(c[0], int(c[2], 16))] = c[6]
    return out

START = {}                                        # cgif-B function name -> start address (main fills it)

def compare(X, Y, sx_, sy_, lui=None):
    """per site key: 'EQUAL <kind>' / 'DIFFERS ..' / 'REVIEW' / 'NUMBER-IN-IMAGE ..'. The same NUMBER in both images that
    falls inside an image section, naming different symbols (a size or a mask, or an address: the number alone cannot
    say), is settled by the lui settlement of its lui words (luiclass.py: the row's class) or stays NOT CERTIFIED"""
    lui = lui_rows() if lui is None else lui
    out = {}
    for key in sorted(set(sx_) | set(sy_), key=str):
        a, b = sx_.get(key), sy_.get(key)
        if a is None or b is None:
            out[key] = 'DIFFERS: site in one image only'; continue
        if any(x[0].endswith('REVIEW') for x in a + b):
            out[key] = 'REVIEW ' + '/'.join(sorted({x[0] for x in a + b if x[0].endswith('REVIEW')})); continue
        if [x[2] for x in a] != [x[2] for x in b]:
            num = lambda k: (k[0], k[-1], k[2] if k[0] == 'LUIADDR' else None) if k and k[0] in ('CONST', 'LUIADDR') else k
            if [num(x[2]) for x in a] == [num(y[2]) for y in b]:
                # the kit's lui row is keyed by the word that completes the value (the addi / addiw after the lui):
                # each lui origin matches the nearest row word at or after it, within 8 instructions
                st = START.get(key[1])
                words = [o for f_, o in key[4] if f_ == key[1] and st is not None and X.dis(st + o, 4)[0][1] == 'lui']
                near = [min((w for (f2, w) in lui if f2 == key[1] and o <= w <= o + 0x20), default=None) for o in words]
                li = [o for f_, o in key[4] if f_ == key[1] and o not in words]
                cls = sorted({lui[(key[1], w)] if w is not None else 'no lui row' for w in near} |
                             ({'a li constant (no lui row)'} if li else set())) or ['no lui row']
                ok = all(not c.startswith(('NOT', 'no lui', 'a li')) for c in cls)
                out[key] = ('NUMBER-IN-IMAGE, settled by the lui row: %s' % '/'.join(cls)) if ok else \
                    'NOT CERTIFIED: REAL 0 (the same number in an image section; lui row: %s)' % '/'.join(cls)
                continue
            out[key] = 'DIFFERS: %s | %s' % ([x[1][:300] for x in a], [x[1][:300] for x in b]); continue
        bad = []
        for x, y in zip(a, b):
            if x[3]:
                bx, by = escape.sc.frd(X.I, x[3][0], x[3][1]), escape.sc.frd(Y.I, y[3][0], y[3][1])
                if bx is None or bx != by:
                    bad.append('table bytes differ at %#x / %#x (%d bytes)' % (x[3][0], y[3][0], x[3][1]))
        out[key] = ('DIFFERS: ' + '; '.join(bad)) if bad else 'EQUAL ' + '/'.join(sorted({x[0] for x in a}))
    return out


def shape_counts(img, keys, by_name):
    """per fail-open shape, how many sites show it: (a) a non-zero load / store immediate; (f) a value passed to a callee
    or returned to a caller; (h) no lui among the site's constants (li / addi-from-zero only)"""
    cnt = collections.Counter()
    for path, fn, o, insn, orig in keys:
        m = LL.MEMOP.search(insn.split(' ', 1)[1]) if ' ' in insn and ' -> ' not in insn else None
        if m and int(m.group(1) or '0', 0):
            cnt['(a) immediate'] += 1
        if ' -> ' in insn or insn.startswith('return'):
            cnt['(f) passed / returned'] += 1
        mns = set()
        for f_, off in orig:
            st = by_name.get(f_)
            if st is not None:
                mns.add(img.dis(st + off, 4)[0][1])
        if mns and 'lui' not in mns:
            cnt['(h) without lui'] += 1
    return dict(sorted(cnt.items()))


def main():
    import luihand
    CX, CY = luihand.Ctx(common.CGIF_B_TWIN), luihand.Ctx(common.DECODE_B_TWIN)
    X, Y = CX.img, CY.img
    common.jump_cases(X, Y)
    AX, AY = Analyser(CX), Analyser(CY)
    LUI = lui_rows()
    for a_ in sorted(X.starts):
        START.setdefault(X.name_at(a_), a_)
    rows, cnt, kinds, nsites, allkeys = [], collections.Counter(), collections.Counter(), 0, []
    fmt = lambda ss, vd: ' ;; '.join('%s%s +%#x %s [const %s] %s => %s' % (
        ''.join('%s+%#x > ' % (p[0][:40], p[1]) for p in k_[0] if len(p) == 2), k_[1][:60], k_[2], k_[3],
        ','.join('%s+%#x' % (q[0][:30], q[1]) if q[0] != k_[1] else '+%#x' % q[1] for q in sorted(k_[4])),
        ' | '.join(x[1][:400] for x in v), vd.get(k_, '-')) for k_, v in sorted(ss.items(), key=lambda kv: str(kv[0]))) or '-'
    only = {int(x, 16) for x in os.environ.get('CONSTBASE_ONLY', '').split(',') if x}
    import time
    t0 = time.time()
    for i, l in enumerate(list(open(os.path.join(common.SCANS, 'exposure.tsv')))[1:]):
        c = l.rstrip('\n').split('\t')
        q, ax, ay = c[0], int(c[1], 16), (int(c[2], 16) if c[2].startswith('0x') else None)
        if only and ax not in only:
            continue
        if i % 50 == 0:
            print('  member %d, %.0fs, memo %d / %d' % (i, time.time() - t0, len(AX.memo), len(AY.memo)), file=sys.stderr)
        sx_ = {}
        for x in set(AX.analyse(ax)):
            sx_.setdefault(x[:5], []).append(AX.judge(x[5]))
        sy_ = {}
        if ay is not None:
            for x in set(AY.analyse(ay)):
                sy_.setdefault(x[:5], []).append(AY.judge(x[5]))
        for d in (sx_, sy_):
            for k_ in d:
                d[k_] = sorted(set(d[k_]), key=lambda x: (str(x[2]), x[0], x[1], str(x[3])))   # a total order: no set order
        vd = compare(X, Y, sx_, sy_, LUI)
        if not vd:
            continue
        v = 'DIFFERS' if any(x.startswith('DIFFERS') for x in vd.values()) else \
            'REVIEW' if any(x.startswith('REVIEW') for x in vd.values()) else \
            'NOT CERTIFIED' if any(x.startswith('NOT CERTIFIED') for x in vd.values()) else 'EQUAL'
        cnt[v] += 1
        kinds.update(vd.values())
        nsites += len(vd)
        allkeys.extend(vd)
        rows.append((q, '%#x' % ax, '%#x' % ay if ay else '-', str(len(sx_)), str(len(sy_)), fmt(sx_, vd), fmt(sy_, vd), v))
    with open(os.path.join(common.SCANS, 'constbase.tsv'), 'w') as f:
        f.write('function (qualified)\tX addr\tY addr\tsites X\tsites Y\tsites X (call path > function +offset instruction '
                '[constants: function+offset] comparison => site verdict)\tsites Y\tverdict\n')
        for r in rows:
            f.write('\t'.join(r) + '\n')
    print('functions with a constant-derived base: %d; verdicts %s' % (len(rows), dict(sorted(cnt.items()))))
    print('sites: %d; %s' % (nsites, dict(sorted(kinds.items()))))
    by_name = {}
    for a_ in sorted(X.starts):
        by_name.setdefault(X.name_at(a_), a_)
    print('sites per shape: %s; tracked values spilled and reloaded: X %d / Y %d' % (
        shape_counts(X, allkeys, by_name), AX.reloads, AY.reloads))
    short = lambda n: re.sub(r'^_ZN?K?\d+__(sanitizer|asan|lsan)', '', n)[:60]
    simple = collections.Counter('EQUAL' if v.startswith('EQUAL') else v.split(':')[0].split(',')[0].split(' (')[0]
                                 .replace('REVIEW ', 'REVIEW-').split('-')[0] for v in kinds.elements())
    summ = ['sites: %d; %s' % (nsites, dict(simple.most_common())), '',
            '| function | REVIEW sites | NOT CERTIFIED sites |', '|---|---|---|']
    for r in rows:
        if r[7] != 'EQUAL':
            print('  %s %s' % (r[7], r[0][:90]))
            nrv = sum('=> REVIEW' in s for s in r[5].split(' ;; '))
            nnc = sum('=> NOT CERTIFIED' in s for s in r[5].split(' ;; '))
            if nrv or nnc:
                summ.append('| %s | %d | %d |' % (short(r[0]), nrv, nnc))
            for s in r[5].split(' ;; '):
                if '=> EQUAL' not in s:
                    print('    X %s' % s[-500:])
    open(os.path.join(common.SCANS, 'constbase-summary.md'), 'w').write('\n'.join(summ) + '\n')


if __name__ == '__main__':
    main()
