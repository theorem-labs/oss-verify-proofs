#!/usr/bin/env python3
"""objscan.py -- whole-image search for every access to a FIELD of an object, whatever the base, and every way a pointer
into the object leaves the code that forms it. The primary settlement of an escaping string stored into a field: when no
code in the image reads the field (directly, through any pointer into the object, or through a copy of the object), the code
cannot observe the string; when a copy carries it, the copy is followed to its reader.

Analysis (per function, every sized FUNC of the image; capstone decode): a FLOW-SENSITIVE forward data-flow over the
function's control-flow graph (blocks split at every branch / jump target and after every branch, jump, call and return;
`jr` switch dispatches go to the cases of the function's measured jump tables, else to every block). The state maps each
register, and each 8-byte stack slot of the function, to a set of values:
  ('abs', A)       an absolute address        (auipc: pc + imm<<12; lui: imm<<12; li; addi / addiw; ld of a .got cell
                                                -> the address the cell holds; ld of a stack slot -> what was stored)
  ('sp', F, d)     function F's stack pointer + d (sp itself never changes in the model: locals are addressed off it)
  ('anyabs', A) / ('anysp', F)   a pointer plus an unknown offset (add of a pointer and a non-constant)
A call clobbers a0..a7, t0..t6, ra; a0 then holds the callee's return summary (pass 1 records every function that returns a
pointer into a watched object). A set larger than 16 values is cut to 'any offset'.
Events (only those whose operand points into a watched object):
  LOAD / STORE   <object>+<offset> <width>       (offset 'any' when unknown)
  PASS           <callee> <reg>                  (a direct call or tail call: the callee is analysed with the caller's
                                                  argument values at the call, 4 levels deep; INDIRECT when the target is not
                                                  known)
  COPY           <callee> dst=<values> src=<object>+<off> size=<n>   (memcpy / memmove / internal_memcpy / internal_memmove /
                                                  CopyFrom): the copied field's new location is watched in its turn
  PTRSTORE       a pointer into the object stored to memory other than a PRIVATE slot of the function's own stack
                                                 (spslot.py: a slot is private when no pointer to it is passed to a call or
                                                  ecall, stored or returned, and no sp-derived pointer reads or writes it)
  RETPTR         a pointer into the object returned
usage: objscan.py   (the watched objects are in main(); output: out/objscan.out)"""
import collections, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common, escape

LD = {'lb': 1, 'lbu': 1, 'lh': 2, 'lhu': 2, 'lw': 4, 'lwu': 4, 'ld': 8, 'flw': 4, 'fld': 8}
ST = {'sb': 1, 'sh': 2, 'sw': 4, 'sd': 8, 'fsw': 4, 'fsd': 8}
BR = {'beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu', 'beqz', 'bnez', 'blez', 'bgez', 'bltz', 'bgtz', 'bgt', 'ble', 'bgtu', 'bleu'}
ARGS = ['a%d' % i for i in range(8)]
CLOB = set(ARGS) | {'ra'} | {'t%d' % i for i in range(7)}
COPYRE = re.compile(r'memcpy|memmove|CopyFrom')
MEMOP = re.compile(r'(-?(?:0x[0-9a-f]+|\d+))?\((\w+)\)\s*$')
CAP = 16
EMPTY = frozenset()


def sx(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def imm(s):
    return int(s, 0)


class Watch:
    """the watched objects: name -> (kind, base, size, fields); kind 'abs' (base = address) or 'sp' (base = (F, d))"""
    def __init__(self):
        self.objs = collections.OrderedDict()

    def add(self, name, kind, base, size, fields):
        self.objs[name] = (kind, base, size, tuple(fields))

    def where(self, v, k=0):
        for nm, (kind, base, size, fl) in self.objs.items():
            if kind == 'abs':
                if v[0] == 'abs' and base <= v[1] + k < base + size:
                    return nm, v[1] + k - base
                if v[0] == 'anyabs' and base <= v[1] < base + size:
                    return nm, 'any'
            else:
                F, d0 = base
                if v[0] == 'sp' and v[1] == F and d0 <= v[2] + k < d0 + size:
                    return nm, v[2] + k - d0
                if v[0] == 'anysp' and v[1] == F:
                    return nm, 'any'
        return None

    def ptr(self, vals):
        return any(self.where(v) for v in vals)


class Fn:
    def __init__(self, img, a, z):
        self.img, self.a, self.z = img, a, z
        self.ins = img.dis(a, z)
        self.at = {o: k for k, (o, m, p, n) in enumerate(self.ins)}
        self.blocks()

    def target(self, k):
        o, mn, op, n = self.ins[k]
        ops = [x.strip() for x in op.split(',')] if op else []
        pc = self.a + o
        tgt = self.img.wtarget.get(pc)
        if tgt is None and (mn in BR or mn in ('j', 'jal')) and ops:
            try:
                tgt = pc + imm(ops[-1])
            except ValueError:
                tgt = None
        return tgt

    def blocks(self):
        ins, lead = self.ins, {0}
        self.kind = []
        for k, (o, mn, op, n) in enumerate(ins):
            ops = [x.strip() for x in op.split(',')] if op else []
            tg = self.target(k)
            inside = tg is not None and self.a <= tg < self.a + self.z and (tg - self.a) in self.at
            if mn in BR:
                kd = 'br'
            elif mn == 'j' or (mn == 'jal' and ops and ops[0] == 'zero'):
                kd = 'jmp' if inside else 'tail'
            elif mn == 'jal' or (mn == 'jalr' and (len(ops) == 1 or (ops and ops[0] == 'ra'))):
                kd = 'call'
            elif mn == 'ret' or (mn in ('jr', 'jalr') and op in ('ra', 'zero, 0(ra)')):
                kd = 'ret'
            elif mn in ('jr',) or (mn == 'jalr' and ops and ops[0] == 'zero'):
                kd = 'ijmp'
            else:
                kd = None
            self.kind.append((kd, tg if tg is not None else None, inside))
            if kd in ('br', 'jmp') and inside:
                lead.add(self.at[tg - self.a])
            if kd is not None and k + 1 < len(ins):
                lead.add(k + 1)
        for c in self.img.cases.get(self.a, ()):          # the cases of a measured jump table start blocks too
            if c in self.at:
                lead.add(self.at[c])
        self.lead = sorted(lead)
        self.bid = {}
        for i, s in enumerate(self.lead):
            e = self.lead[i + 1] if i + 1 < len(self.lead) else len(ins)
            for k in range(s, e):
                self.bid[k] = s
        self.succ, self.end = {}, {}
        cases = self.img.cases.get(self.a)
        for i, s in enumerate(self.lead):
            e = (self.lead[i + 1] if i + 1 < len(self.lead) else len(ins)) - 1
            kd, tg, inside = self.kind[e]
            nxt = [e + 1] if e + 1 < len(ins) else []
            if kd == 'br':
                sc = nxt + ([self.at[tg - self.a]] if inside else [])
            elif kd == 'jmp':
                sc = [self.at[tg - self.a]]
            elif kd in ('tail', 'ret'):
                sc = []
            elif kd == 'ijmp':
                sc = [self.at[c] for c in cases if c in self.at] if cases else list(self.lead)
            else:
                sc = nxt
            self.succ[s] = sorted(set(sc))
            self.end[s] = e

    def run(self, W, entry, summaries, events, label):
        """forward data-flow; entry: {reg: frozenset(values)}; appends events (kind, object, offset, extra, ins offset)"""
        F = self.a
        start = {r: frozenset(v) for r, v in entry.items()}
        IN = {self.lead[0]: (start, {})}
        work = [self.lead[0]]
        seen_ev = set()
        iters = 0
        while work and iters < 20000:
            iters += 1
            s = work.pop()
            regs, slots = IN[s]
            regs, slots = dict(regs), dict(slots)
            for k in range(s, self.end[s] + 1):
                self.step(k, regs, slots, W, summaries, events, seen_ev, label)
            for t in self.succ[s]:
                if t not in IN:
                    IN[t] = (dict(regs), dict(slots)); work.append(t); continue
                r0, s0 = IN[t]
                ch = False
                nr = dict(r0)
                for r, v in regs.items():
                    u = nr.get(r, EMPTY) | v
                    if len(u) > CAP:
                        u = frozenset(('anyabs', x[1]) if x[0] == 'abs' else (('anysp', x[1]) if x[0] == 'sp' else x) for x in u)
                    if u != nr.get(r, EMPTY):
                        nr[r] = u; ch = True
                ns = dict(s0)
                for d, v in slots.items():
                    u = ns.get(d, EMPTY) | v
                    if u != ns.get(d, EMPTY):
                        ns[d] = u; ch = True
                if ch:
                    IN[t] = (nr, ns)
                    if t not in work:
                        work.append(t)

    def val(self, regs, r):
        if r == 'sp':
            return frozenset({('sp', self.a, 0)})
        if r == 'zero':
            return frozenset({('abs', 0)})
        return regs.get(r, EMPTY)

    def step(self, k, regs, slots, W, summaries, events, seen_ev, label):
        o, mn, op, n = self.ins[k]
        ops = [x.strip() for x in op.split(',')] if op else []
        pc = self.a + o
        kd, tg, inside = self.kind[k]

        def ev(*e):
            key = (o,) + e[:3]
            if key not in seen_ev:
                seen_ev.add(key)
                events.append(e + (o, label))
        if not ops and mn != 'ret':
            return
        rd = ops[0] if ops else None
        if mn == 'auipc':
            regs[rd] = frozenset({('abs', pc + (sx(imm(ops[1]), 20) << 12))}); return
        if mn == 'lui':
            regs[rd] = frozenset({('abs', sx(imm(ops[1]) << 12, 32))}); return
        if mn == 'li':
            regs[rd] = frozenset({('abs', imm(ops[1]))}); return
        if mn in ('addi', 'addiw') and len(ops) == 3:
            if rd == 'sp':
                return
            c = imm(ops[2])
            out = set()
            for x in self.val(regs, ops[1]):
                if x[0] == 'abs':
                    out.add(('abs', (sx(x[1] + c, 32) if mn == 'addiw' else x[1] + c)))
                elif x[0] == 'sp':
                    out.add(('sp', x[1], x[2] + c))
                else:
                    out.add(x)
            regs[rd] = frozenset(out); return
        if mn == 'mv':
            regs[rd] = self.val(regs, ops[1]); return
        if mn == 'add' and len(ops) == 3:
            a, b = self.val(regs, ops[1]), self.val(regs, ops[2])
            out = set()
            for x in a | b:
                if x[0] in ('abs', 'anyabs') and W.where(x):
                    out.add(('anyabs', x[1]))
                elif x[0] in ('sp', 'anysp'):
                    out.add(('anysp', x[1]))
            regs[rd] = frozenset(out); return
        if mn in LD or mn in ST:
            m = MEMOP.search(op)
            if not m:
                regs.pop(rd, None); return
            c, base = imm(m.group(1) or '0'), m.group(2)
            bv = self.val(regs, base)
            for x in bv:
                w = W.where(x, c)
                if w:
                    ev('LOAD' if mn in LD else 'STORE', w[0], w[1], LD.get(mn) or ST.get(mn))
            if mn in ST:
                if mn == 'sd':
                    own = [x for x in bv if x[0] == 'sp' and x[1] == self.a]
                    for x in own:
                        d = x[2] + c
                        slots[d] = (slots.get(d, EMPTY) | self.val(regs, rd)) if len(bv) > 1 else self.val(regs, rd)
                vals = self.val(regs, rd)
                own_all = bool(bv) and all(x[0] == 'sp' and x[1] == self.a for x in bv)
                private, why = False, ''
                if own_all and base == 'sp':
                    import spslot                     # (spslot imports this module)
                    private, why = spslot.frame(self.img, self.a, self.z).private(k, c, ST[mn])
                elif own_all:
                    why = 'stored through an sp-derived pointer'
                if W.ptr(vals) and not private:   # an unknown base, or a stack slot that is not private: escapes
                    for x in vals:
                        w = W.where(x)
                        if w:
                            ev('PTRSTORE', w[0], w[1], 'stored at %s' % ((','.join(self.desc(y, c) for y in sorted(bv)) or
                                                                          'unknown %s+%#x' % (base, c)) +
                                                                         (' (a stack slot that is not private: %s)' % why
                                                                          if own_all else '')))
                return
            out = set()
            for x in bv:
                if x[0] == 'abs' and mn == 'ld' and self.img.gotrange() and \
                        self.img.gotrange()[0] <= x[1] + c < self.img.gotrange()[1]:
                    c8 = escape.sc.frd(self.img.I, x[1] + c, 8)
                    if c8:
                        out.add(('abs', int.from_bytes(c8, 'little')))
                elif x[0] == 'sp' and x[1] == self.a and mn == 'ld':
                    out |= slots.get(x[2] + c, EMPTY)
            if rd in ('zero', 'sp'):
                return
            regs[rd] = frozenset(out); return
        if kd in ('call', 'tail') or (kd == 'ijmp'):
            argv = {r: self.val(regs, r) for r in ARGS}
            if any(W.ptr(v) for v in argv.values()):
                cname = self.img.name_at(tg) if tg is not None else None
                if tg is None or tg not in self.img.starts:
                    if kd != 'ijmp' or W.ptr(argv['a0']):
                        for r, v in argv.items():
                            for x in v:
                                w = W.where(x)
                                if w:
                                    ev('PASS', w[0], w[1], ('INDIRECT', r))
                elif COPYRE.search(cname):
                    ev('COPY', None, None, (cname, argv))
                else:
                    for r, v in argv.items():
                        for x in v:
                            w = W.where(x)
                            if w:
                                ev('PASS', w[0], w[1], (cname, r, tg, argv))
            if kd in ('call',):
                for r in CLOB:
                    regs.pop(r, None)
                if tg is not None and tg in summaries:
                    regs['a0'] = summaries[tg]
            return
        if kd == 'ret':
            v = self.val(regs, 'a0')
            for x in v:
                w = W.where(x)
                if w:
                    ev('RETPTR', w[0], w[1], frozenset(v))
            return
        if kd in ('br', 'jmp'):
            return
        if rd and re.match(r'^[a-z][a-z0-9]*$', rd) and rd not in ('zero', 'sp') and mn not in ST and mn not in BR:
            regs.pop(rd, None)

    def desc(self, x, c=0):
        if x[0] == 'abs':
            return self.img.home(x[1] + c)
        if x[0] == 'sp':
            return 'stack of %s +%#x' % (self.img.name_at(x[1])[:60], x[2] + c)
        return str(x)


def analyse(img, W, fns, summaries, depth=4, label=None, memo=None, out=None):
    """fns: [(addr, size, entry)]; returns events (kind, object, offset, extra, ins offset, label)"""
    memo = set() if memo is None else memo
    out = [] if out is None else out
    for a, z, entry in fns:
        key = (a, tuple(sorted((r, v) for r, v in entry.items() if W.ptr(v))))
        if key in memo:
            continue
        memo.add(key)
        f = Fn(img, a, z)
        ev = []
        lab = (label + ' > ' if label else '') + img.name_at(a)
        f.run(W, entry, summaries, ev, lab)
        for e in ev:
            out.append(e)
            if e[0] == 'PASS' and isinstance(e[3], tuple) and e[3][0] != 'INDIRECT' and depth > 0:
                cname, r, tg, argv = e[3]
                cz = [x for x in img.funcs if x[0] == tg]
                if cz:
                    ent = {rr: frozenset(v) for rr, v in argv.items()}
                    analyse(img, W, [(tg, cz[0][1], ent)], summaries, depth - 1, lab, memo, out)
    return out


def scan_image(img, W, extra_fns=()):
    """pass 1 (repeated to a fixpoint): return summaries -- every function that returns a pointer into a watched object;
    pass 2: every function (plus extra_fns) with those summaries"""
    img._index()
    allf = [(v, z, {}) for v, z, n in img.funcs]
    summ = {}
    for _ in range(3):
        ev = analyse(img, W, allf, summ, depth=0)
        rp = collections.defaultdict(set)
        for e in ev:
            if e[0] == 'RETPTR' and ' > ' not in e[5]:
                for v in [v for v in img.starts if img.name_at(v) == e[5]]:
                    rp[v] |= set(e[3])
        new = {v: frozenset(s) for v, s in rp.items()}
        if new == summ:
            break
        summ = new
    return analyse(img, W, allf + list(extra_fns), summ), summ


def fmt(img, e):
    kind, obj, off, extra, o, label = e
    offs = off if off == 'any' or off is None else '%#x' % off
    if kind in ('LOAD', 'STORE'):
        return '%s %s+%s w%s  at %s +%#x' % (kind, obj, offs, extra, label, o)
    if kind == 'PASS':
        return 'PASS %s+%s in %s to %s  at %s +%#x' % (obj, offs, extra[1] if extra[0] == 'INDIRECT' else extra[1],
                                                       extra[0], label, o)
    if kind == 'COPY':
        cname, argv = extra
        return 'COPY %s  a0(dst)=%s a1(src)=%s a2=%s  at %s +%#x' % (cname, sorted(argv['a0'])[:4], sorted(argv['a1'])[:4],
                                                                    sorted(argv['a2'])[:4], label, o)
    if kind == 'PTRSTORE':
        return 'PTRSTORE %s+%s %s  at %s +%#x' % (obj, offs, extra, label, o)
    return '%s %s+%s  at %s +%#x' % (kind, obj, offs, label, o)


def main():
    out, tsv = [], []
    for tag, path in (('cgif B', common.CGIF_B_TWIN), ('decode B', common.DECODE_B_TWIN)):
        img = escape.Image(path)
        sym = {n: (v, z) for v, z, n, t in img.I.syms if t == 'STT_OBJECT'}
        cf, lf = sym['_ZN11__sanitizer21common_flags_dont_useE'], sym['_ZN6__lsan10lsan_flagsE']
        af, uf = sym['_ZN6__asan28asan_flags_dont_use_directlyE'], sym['_ZN7__ubsan11ubsan_flagsE']
        ofn = img.I.fsym('_ZN6__asan20AsanDeactivatedFlags27OverrideFromActivationFlagsEv')
        W = Watch()
        # every object field into which an escaping C-string row of RECORD.md 4e stores its pointer
        W.add('common_flags_dont_use', 'abs', cf[0], cf[1], [0x18, 0xc8, 0xd0])
        W.add('lsan_flags', 'abs', lf[0], lf[1], [0x20])
        W.add('asan_flags_dont_use_directly', 'abs', af[0], af[1], [0x68])
        W.add('ubsan_flags', 'abs', uf[0], uf[1], [0x8])
        W.add('local CommonFlags (OverrideFromActivationFlags sp+0x20)', 'sp', (ofn[0], 0x20), cf[1], [0x18, 0xc8, 0xd0])
        out.append('#### %s: common_flags_dont_use %#x (%d B), lsan_flags %#x (%d B), asan_flags_dont_use_directly %#x (%d B), '
                   'ubsan_flags %#x (%d B), OverrideFromActivationFlags %#x' % (tag, cf[0], cf[1], lf[0], lf[1], af[0], af[1],
                                                                                uf[0], uf[1], ofn[0]))
        done, rounds = set(), 0
        while True:
            rounds += 1
            ev, summ = scan_image(img, W)
            out.append('## round %d: watched %s; return summaries (functions returning a pointer into a watched object): %s' % (
                rounds, list(W.objs), sorted(img.name_at(v) for v in summ) or 'none'))
            new = 0
            for e in ev:
                if e[0] != 'COPY':
                    continue
                cname, argv = e[3]
                for s in [W.where(x) for x in argv['a1']]:
                    if not s or s[1] == 'any':
                        continue
                    kind, base, size, fl = W.objs[s[0]]
                    n = [x[1] for x in argv['a2'] if x[0] == 'abs']
                    n = n[0] if len(n) == 1 and 'CopyFrom' not in cname else (size if 'CopyFrom' in cname else None)
                    moved = [F - s[1] for F in fl if F >= s[1] and (n is None or F - s[1] < n)]
                    for d in argv['a0']:
                        if not moved or d[0] not in ('abs', 'sp'):
                            continue
                        nm = 'copy of %s+%#x at %s' % (s[0], s[1], img.home(d[1]) if d[0] == 'abs' else
                                                       'stack of %s +%#x' % (img.name_at(d[1]), d[2]))
                        if nm in W.objs or nm in done:
                            continue
                        done.add(nm)
                        if d[0] == 'abs':
                            W.add(nm, 'abs', d[1], n or size, moved)
                        else:
                            W.add(nm, 'sp', (d[1], d[2]), n or size, moved)
                        new += 1
            if not new or rounds >= 4:
                break
        for nm, (kind, base, size, fl) in W.objs.items():
            for F in fl:
                hits = [e for e in ev if e[1] == nm and e[0] in ('LOAD', 'STORE') and
                        (e[2] == 'any' or (isinstance(e[2], int) and e[2] <= F < e[2] + e[3]))]
                ptrs = [e for e in ev if e[1] == nm and e[0] == 'PTRSTORE' and e[2] == F]
                copies = [o for o in W.objs if o.startswith('copy of %s+' % nm)]
                loads = sorted({'%s +%#x' % (e[5], e[4]) for e in hits if e[0] == 'LOAD'})
                out.append('%s: %s field +%#x: %d LOAD, %d STORE' % (tag, nm, F, sum(e[0] == 'LOAD' for e in hits),
                                                                   sum(e[0] == 'STORE' for e in hits)))
                out.extend('    ' + fmt(img, e) for e in sorted(hits, key=lambda e: (e[0], e[5], e[4])))
                tsv.append((tag, nm, '%#x' % base if kind == 'abs' else 'stack:%s+%#x' % (img.name_at(base[0]), base[1]),
                            '%#x' % F, str(len(loads)), str(sum(e[0] == 'STORE' for e in hits)), str(len(ptrs)),
                            ' | '.join(copies) or '-', ' ; '.join(loads) or '-'))
        esc = [e for e in ev if e[0] in ('PASS', 'COPY', 'PTRSTORE', 'RETPTR')]
        out.append('%s: pointers into the watched objects leaving the code that forms them: %d' % (tag, len(esc)))
        out.extend('    ' + fmt(img, e) for e in sorted(esc, key=lambda e: (e[0], str(e[1]), str(e[2]), e[5], e[4])))
    open(os.path.join(common.OUT, 'objscan.out'), 'w').write('\n'.join(out) + '\n')
    with open(os.path.join(common.OUT, 'objscan.tsv'), 'w') as f:
        f.write('image\tobject\tbase\tfield\tdistinct loads\tstores\tfield pointers stored\tcopies carrying the field\tload sites\n')
        for r in tsv:
            f.write('\t'.join(r) + '\n')
    print('\n'.join(l for l in out if not l.startswith('    ')))


if __name__ == '__main__':
    main()
