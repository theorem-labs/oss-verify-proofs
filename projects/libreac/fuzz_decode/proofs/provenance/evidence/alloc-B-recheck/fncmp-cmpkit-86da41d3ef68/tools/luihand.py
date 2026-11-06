#!/usr/bin/env python3
"""luihand.py -- the evidence for the hand argument on every `lui-in-section` row of strictcmp3 (cmpkit 86da41d3ef68) in
this record's closure (scans/lui-targets.tsv), in BOTH images. For each target (member, word, value V):
  - the forward dataflow of V inside the member (luiflow.flow's walk: copies and ALU results carry it, both arms of every
    branch, measured jump-table cases), each instruction it reaches;
  - for every `add` / `addw` / `sub` that combines V with another register, that register's PROVENANCE at that point
    (backward reaching definition, followed through mv / loads / addi): ABS <symbol+off> (an auipc pair or a .got cell:
    an image address), ENTRY <reg> (a parameter of the member), LOAD <base>+<off>, SP+<d>, CALL <callee> (a return value),
    CONST <n>, or OP <mnemonic> (other arithmetic);
  - for every memory access whose base carries V: the base's composition, and when the other part is an image address,
    the address actually accessed (other + V + constant) named in each image (it must be the same symbol + offset);
  - for every call argument that carries V: the callee's parameter at that register (Itanium mangling: `this` first for a
    member; types m / j / i / y ... are integers) and, followed INTO the callee (2 levels), what the callee does with it;
  - for a value stored to memory, the store's destination; for a returned value, nothing more (the record lists the callers).
Writes scans/luihand.tsv (one row per target: the evidence for X, and whether Y gives the same after addresses are masked)
and prints a summary. The ARGUMENT column of RECORD.md section 4g is written by hand from this evidence. usage: luihand.py"""
import collections, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common, escape, luiflow

MEMOP = re.compile(r'(-?(?:0x[0-9a-f]+|\d+))?\((\w+)\)\s*$')


# C callees reached in these images (musl / the sanitizer's C entry points): their parameter types, from their prototypes
CSIG = {'open': ['const char *path', 'int flags', 'mode_t mode (variadic)'],
        'socket': ['int domain', 'int type', 'int protocol'],
        '__nl_langinfo_l': ['nl_item item (int)', 'locale_t loc'],
        '__syscall_ret': ['unsigned long r'],
        '__stack_chk_fail': [],
        '__sanitizer_internal_memset': ['void *s', 'int c', 'uptr n (unsigned long)'],
        'memset': ['void *s', 'int c', 'size_t n'],
        '__tm_to_secs': ['const struct tm *tm'],
        '__tm_to_tzname': ['const struct tm *tm'],
        'week_num': ['const struct tm *tm'],
        '__getauxval': ['unsigned long item'],
        '__lsysinfo': ['struct sysinfo *info']}


def param(name, reg):
    """what the callee `name` takes in argument register `reg`: 'this' for a member's a0, else the declared type"""
    k = int(reg[1:])
    if not name.startswith('_Z'):
        sig = CSIG.get(name)
        if sig is None:
            return '? (unmangled, no prototype listed)'
        return sig[k] if k < len(sig) else '(beyond the signature)'
    if luiflow.itanium_params(name) is None:
        return '? (name not parsed)'
    t = luiflow.is_member(name)
    if t and k == 0:
        return 'this'
    return luiflow.ptype(name, 'a%d' % (k - (1 if t else 0)), False)


class Ctx:
    def __init__(self, path):
        self.img = escape.Image(path)
        self.img._index()
        self._fs = {}

    def fstate(self, a, z):
        """FLOW-SENSITIVE register values at each instruction of the function at a: objscan.Fn's data-flow over the
        control-flow graph (auipc pairs, .got cells, mv / addi, stack slots; a call clobbers the caller-saved registers),
        seeded with ('arg', r) for every argument and callee-saved register at entry. {instruction index: {reg: values}}"""
        if (a, z) in self._fs:
            return self._fs[(a, z)]
        import objscan
        rec = collections.defaultdict(lambda: collections.defaultdict(set))

        class Obs(objscan.Fn):
            def step(s, k, regs, slots, W, summaries, events, seen_ev, label):
                for r, v in regs.items():
                    rec[k][r] |= set(v)
                o, mn, op, n = s.ins[k]
                ops = [x.strip() for x in op.split(',')] if op else []
                if mn in ('li', 'lui') and ops and ops[0] not in ('zero', 'sp'):
                    # a constant, not an image address: objscan's model calls every value 'abs'; here only an auipc pair
                    # (or a .got cell) is an address
                    regs[ops[0]] = frozenset({('const', ops[-1])})
                    return
                if mn in ('addi', 'addiw') and len(ops) == 3 and ops[1] in regs and \
                        all(x[0] == 'const' for x in regs[ops[1]]) and regs[ops[1]]:
                    regs[ops[0]] = frozenset({('const', '%s%+d' % (min(x[1] for x in regs[ops[1]]), int(ops[2], 0)))})
                    return
                return objscan.Fn.step(s, k, regs, slots, W, summaries, events, seen_ev, label)
        f = Obs(self.img, a, z)
        seed = {r: frozenset({('arg', r)}) for r in luiflow.ARGS + ['s%d' % i for i in range(12)]}
        f.run(objscan.Watch(), seed, {}, [], '')
        self._fs[(a, z)] = rec
        return rec

    def fprov(self, a, z, k, reg):
        """the flow-sensitive provenance of `reg` before instruction index k, or None when the data-flow does not know it"""
        if reg == 'sp':
            return 'SP'
        v = self.fstate(a, z).get(k, {}).get(reg, set())
        if not v:
            return None
        v = {('const', '%#x' % x[1]) if x[0] == 'abs' and x[1] < 0x10000 else x for x in v}   # 0 / small: not an address
        kinds = {x[0] for x in v}
        if kinds == {'abs'}:
            return 'ABS ' + ' | '.join(sorted('%s' % self.img.home(x[1]) for x in v))
        if kinds == {'const'}:
            return 'CONST ' + ' | '.join(sorted(('%#x' % x[1]) if isinstance(x[1], int) else str(x[1]) for x in v))
        if kinds == {'arg'}:
            return 'ENTRY ' + ' | '.join(sorted(x[1] for x in v))
        if kinds <= {'sp'}:
            return 'SP'
        return None

    def prov(self, a, z, k, reg, depth=4):
        """the provenance of `reg` just before instruction index k: the flow-sensitive one when the data-flow knows it,
        else a backward linear scan (marked `linear:`), which a hand reading must confirm"""
        fp = self.fprov(a, z, k, reg)
        if fp is not None:
            return fp
        return 'linear: ' + self.lprov(a, z, k, reg, depth)

    def lprov(self, a, z, k, reg, depth=4):
        """the backward linear provenance of `reg` just before instruction index k of the function at a"""
        img = self.img
        ins = img.dis(a, z)
        if reg == 'sp':
            return 'SP'
        if reg == 'zero':
            return 'CONST 0'
        for j in range(k - 1, -1, -1):
            o, m, p, n = ins[j]
            ops = [x.strip() for x in p.split(',')] if p else []
            if m in ('jal', 'jalr') and (len(ops) <= 1 or ops[0] == 'ra' or '(' in p) and reg in luiflow.CLOB:
                if reg == 'a0':
                    tg = img.wtarget.get(a + o)
                    if tg is None and m == 'jal':
                        tg = a + o + int(ops[-1], 0)
                    return 'CALL %s' % (img.name_at(tg) if tg else 'indirect')
                return 'CLOBBERED by a call'
            if not ops or ops[0] != reg or m in escape.ST or m in escape.BR:
                continue
            if a + o in img.wtarget and m in ('addi', 'ld'):
                tg = img.wtarget[a + o]
                if m == 'addi':
                    return 'ABS %s' % img.home(tg)
                if img.I.sec(tg) == '.got':
                    c8 = escape.sc.frd(img.I, tg, 8)
                    return 'ABS %s (via .got)' % img.home(int.from_bytes(c8, 'little')) if c8 else 'LOAD .got'
                return 'LOAD %s' % img.home(tg)
            if m == 'mv' and depth:
                return self.prov(a, z, j, ops[1], depth - 1)
            if m in ('li', 'lui'):
                return 'CONST %s' % ops[-1]
            if m in escape.LD or m in luiflow.LD:
                mm = MEMOP.search(p)
                b = self.prov(a, z, j, mm.group(2), depth - 1) if depth and mm else '?'
                return 'LOAD %s+%s [%s]' % (mm.group(2), mm.group(1) or '0', b) if mm else 'LOAD'
            if m in ('addi', 'addiw') and depth:
                b = self.prov(a, z, j, ops[1], depth - 1)
                return '%s + %s' % (b, ops[2])
            return 'OP %s %s' % (m, p)
        return 'ENTRY %s' % reg if reg in luiflow.ARGS or reg.startswith('s') else 'ENTRY %s (callee-saved / unset)' % reg

    def walk(self, a, z, k0, regs, depth, label, out, seen_calls):
        """luiflow's walk from instruction index k0 with `regs` carrying V; appends evidence lines to out"""
        img = self.img
        ins = img.dis(a, z)
        at = {o: k for k, (o, m, p, n) in enumerate(ins)}
        seen, work, steps = set(), [(k0, frozenset(regs))], 0
        while work:
            k, T = work.pop()
            while 0 <= k < len(ins) and T:
                if (k, T) in seen:
                    break
                seen.add((k, T)); steps += 1
                if steps > luiflow.BUDGET:
                    out.add('%sLIMIT' % label); return
                o, m, p, nb = ins[k]
                ops = [x.strip() for x in p.split(',')] if p else []
                pc = a + o
                mm = MEMOP.search(p) if p else None
                tag = '%s+%#x %s %s' % (label, o, m, p)
                if m in ('mv', 'sext.w') and len(ops) == 2:
                    T = (T | {ops[0]}) if ops[1] in T else (T - {ops[0]})
                    k += 1; continue
                if m in luiflow.ALU and ops:
                    srcs = [x for x in ops[1:] if x in T]
                    if srcs:
                        if m in ('add', 'addw', 'sub', 'subw') and len(ops) == 3:
                            other = [x for x in ops[1:] if x not in T]
                            pv = '; '.join('%s = %s' % (x, self.prov(a, z, k, x)) for x in other) or 'both sides carry V'
                            kind = None
                            if m == 'add' and len(other) == 1:
                                x = other[0]
                                pr = self.prov(a, z, k, x)
                                fv = self.fstate(a, z).get(k, {}).get(x, set())
                                av = list(fv)[0][1] if len(fv) == 1 and list(fv)[0][0] == 'abs' and list(fv)[0][1] >= 0x10000 else None
                                ent = re.match(r'ENTRY (a\d)$', pr)
                                pt = param(self.member, ent.group(1)) if ent and self.member else ''
                                if av is not None:
                                    tot = av + self.vval
                                    kind = 'OFFSET into the image object at %#x (%s): the address formed is %#x = %s' % (
                                        av, img.home(av), tot, img.home(tot))
                                elif pr == 'SP':
                                    kind = 'OFFSET into the stack frame'
                                elif pt == 'this' or pt.startswith('pointer'):
                                    kind = 'OFFSET into the object the parameter %s (%s) points to' % (ent.group(1), pt)
                            if kind:
                                out.add('%sOFFSET %s [%s] -> %s; the sum is a pointer into that object, not followed' % (
                                    label, tag, pv, kind))
                                T = T - {ops[0]}
                                k += 1; continue
                            out.add('%sCOMBINE %s [%s]' % (label, tag, pv))
                        T = T | {ops[0]}
                    else:
                        T = T - {ops[0]}
                    k += 1; continue
                base_m = m.split('.')[0]
                is_ld = m in luiflow.LD or base_m == 'lr'
                is_st = base_m in escape.ST or base_m == 'sc' or base_m.startswith('amo')
                if is_ld or is_st:
                    if mm and mm.group(2) in T:
                        out.add('%sMEM-BASE %s' % (label, tag))
                    # the data register: `s* data, off(base)`; atomics `sc/amo rd, data, (base)` (capstone prints sc.d as sd.rl)
                    data = ops[1] if len(ops) == 3 else (ops[0] if ops else None)
                    if is_st and data in T:
                        out.add('%sSTORE-DATA %s [dest %s = %s]' % (label, tag, mm.group(2) if mm else '?',
                                                                 self.prov(a, z, k, mm.group(2)) if mm else '?'))
                    if (is_ld or len(ops) == 3) and ops:
                        T = T - {ops[0]}
                    k += 1; continue
                if m in luiflow.CMP:
                    if any(x in T for x in ops):
                        out.add('%sCMP %s' % (label, tag))
                    if m in escape.BR:
                        try:
                            t2 = o + int(ops[-1], 0)
                            if t2 in at:
                                work.append((at[t2], T))
                        except ValueError:
                            pass
                    elif ops:
                        T = T - {ops[0]}
                    k += 1; continue
                if m == 'ecall':
                    out.add('%sSYSCALL %s [a7 = %s]' % (label, ' '.join(sorted(T & set(luiflow.ARGS))) or 'none',
                                                     self.prov(a, z, k, 'a7')))
                    k += 1; continue
                if m == 'ret':
                    if 'a0' in T:
                        out.add('%sRET' % label)
                    break
                if m in ('j', 'jal', 'jr', 'jalr'):
                    tgt = img.wtarget.get(pc)
                    if tgt is None and m in ('j', 'jal'):
                        tgt = pc + int(ops[-1], 0)
                    is_call = (m == 'jal' and (len(ops) == 1 or ops[0] == 'ra')) or \
                              (m == 'jalr' and (len(ops) == 1 or ops[0] == 'ra' or '(' in p))
                    if m in ('jr', 'jalr'):
                        b = (re.findall(r'\((\w+)\)', p) or [ops[-1] if ops else ''])[0]
                        if b in T:
                            out.add('%sJUMP %s' % (label, tag))
                        if tgt is None:
                            v = self.prov(a, z, k, b)
                            mm2 = re.match(r'ABS (.+)\+(0x[0-9a-f]+)', v)
                            tgt = None
                            if v.startswith('ABS') and ' + ' not in v:
                                hit = [s for s in img.starts if img.name_at(s) == v[4:].split('+')[0]]
                                tgt = hit[0] if hit else None
                    if not is_call and m == 'j' and tgt is not None and a <= tgt < a + z and (tgt - a) in at:
                        k = at[tgt - a]; continue
                    if not is_call and m == 'jr' and img.cases.get(a):
                        for c in img.cases[a]:
                            if c in at:
                                work.append((at[c], T))
                        break
                    name = img.name_at(tgt) if tgt is not None else None
                    for r in sorted(T & set(luiflow.ARGS)):
                        if name and tgt in img.starts:
                            pt = param(name, r)
                            out.add('%s%s %s %s [param: %s]' % (label, 'ARG' if is_call else 'TAILARG', name, r, pt))
                            if depth > 0 and pt not in ('(beyond the signature)',) and (name, r) not in seen_calls:
                                seen_calls.add((name, r))
                                cz = [x for x in img.funcs if x[0] == tgt]
                                if cz:
                                    self.walk(tgt, cz[0][1], 0, {r}, depth - 1, '%s  in %s: ' % (label, name[:80]), out, seen_calls)
                        else:
                            out.add('%sINDIRECT-ARG %s [call target %s]' % (label, r, self.prov(a, z, k, (re.findall(r'\((\w+)\)', p) or [ops[-1] if ops else '?'])[0])))
                    if not is_call:
                        break
                    T = T - luiflow.CLOB
                    k += 1; continue
                if ops and ops[0] in T and m not in escape.ST:
                    T = T - {ops[0]}
                k += 1


def evidence(ctx, a, z, word, member, vval):
    """the evidence for one target; callees are not entered (each call argument is typed from the callee's signature)"""
    ins = ctx.img.dis(a, z)
    k0 = [k for k, x in enumerate(ins) if x[0] == word][0]
    rd = ins[k0][2].split(',')[0].strip()
    out = set()
    ctx.member, ctx.vval = member, vval
    ctx.walk(a, z, k0 + 1, {rd}, 0, '', out, set())
    return ins[k0][1] + ' ' + ins[k0][2], sorted(out)


def main():
    X, Y = Ctx(common.CGIF_B_TWIN), Ctx(common.DECODE_B_TWIN)
    common.jump_cases(X.img, Y.img)                 # every measured rel4 jump table: a `jr` goes to its cases
    fd = {}
    for l in list(open(os.path.join(common.HERE, 'scans', 'exposure.tsv')))[1:]:
        c = l.rstrip('\n').split('\t')
        fd[int(c[1], 16)] = (int(c[2], 16), int(c[3]))
    rows, nsame = [], 0
    for l in list(open(os.path.join(common.HERE, 'scans', 'lui-targets.tsv')))[1:]:
        member, ax, word, vals = l.rstrip('\n').split('\t')
        ax, w = int(ax, 16), int(word, 16)
        ay, z = fd[ax]
        vv = int(vals.split(' ')[0], 16)
        lx, ex = evidence(X, ax, z, w, X.img.name_at(ax), vv)
        ly, ey = evidence(Y, ay, z, w, Y.img.name_at(ay), vv)
        mask = lambda es: sorted(re.sub(r'0x[0-9a-f]{4,}', '#', e) for e in es)
        same = mask(ex) == mask(ey)
        nsame += same
        rows.append((member, '%#x' % ax, '%#x' % ay, word, vals, lx, ' ;; '.join(ex) or 'none',
                     'same' if same else 'DIFFER: ' + ' ;; '.join(ey)))
    with open(os.path.join(common.HERE, 'scans', 'luihand.tsv'), 'w') as f:
        f.write('member\tX addr\tY addr\tword\tvalues (X | Y)\tlui word\tevidence in X (uses, combines with provenance, callee uses)\t'
                'evidence in Y (masked compare)\n')
        for r in rows:
            f.write('\t'.join(r) + '\n')
    print('targets %d; evidence identical in both images (addresses masked): %d' % (len(rows), nsame))


if __name__ == '__main__':
    main()
