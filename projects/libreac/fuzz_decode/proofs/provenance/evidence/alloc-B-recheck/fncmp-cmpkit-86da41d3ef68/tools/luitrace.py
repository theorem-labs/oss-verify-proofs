#!/usr/bin/env python3
"""luitrace.py -- the hand-argument TRACE of every `lui-in-section` target of strictcmp3 (cmpkit 86da41d3ef68) in this
record's closure (scans/lui-targets.tsv), in BOTH images, by this record's own decoder (capstone, the kit's `targets` for
pc-relative values). It does not rely on luiscan's or strictcmp3's lui dataflow (which follows addi / ld / sd / jalr only).

From the target word, the register that holds V (the lui value, with its paired addi) is followed over the member's
control-flow graph (both arms of every branch; a `jr` dispatch into the cases of the measured jump tables) up to every
write that ends it. EVERY instruction that reads a followed register is recorded with the role of what it reads:
  V        the value itself (plus constants: V+c)
  D        an integer computed from V (add / sub / sh*add / and / or / xor / shifts / mul / div / rem with another integer)
  P        a pointer: V (or D) added to a register that holds an image object address (auipc pair / .got cell), the member's
           `this` or a pointer parameter, or the stack pointer; P carries the object, the constant part (V + c) and whether
           a variable index was added
Uses: CMP (branch / slt operand), ARG (call argument: the callee's parameter type from its mangled name, `this` for a
member), STORE-DATA (stored value; destination), BASE (load / store / AMO / jump base), RET, SYSCALL (ecall argument).
A store to a stack slot is a SPILL (not a use, followed to its reloads) only when spslot.py finds the slot PRIVATE: no
pointer to it is passed to a call or ecall, stored or returned, and no sp-derived pointer reads or writes it; any other
stack store is a STORE-DATA use. A call argument is followed INTO its callee and a value handed back INTO the callers
(`followups`, 4 levels), and a register left live at a call is checked dead in the callee (deadreg.py).
For every BASE the FULL address is computed in each image: P on an image object -> object + constant part (+ the
variable index, shown as `+ index`), named as symbol + offset; P on `this` / a pointer parameter -> the objects the
member's callers pass (each caller's argument value: an image object, or that caller's own parameter followed up 3 levels,
or `runtime` when it is computed from memory), each + constant part, named; a base that is V or D itself -> V + c named
directly (an absolute address use of V). The two images' names must be the same symbol + offset.
Writes scans/luitrace.tsv (one row per target: the trace in X, the trace in Y, the BASE full addresses in both, and the
verdict NOT-AN-ADDRESS / OFFSET-SAME-SYMBOL / DIFFERS / REVIEW) and prints the counts. usage: luitrace.py"""
import collections, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common, escape, luiflow, luihand, spslot

ALU = luiflow.ALU | {'sh1add', 'sh2add', 'sh3add', 'sh1add.uw', 'sh2add.uw', 'sh3add.uw', 'add.uw'}
MEMOP = luihand.MEMOP
IMG_LO = 0x10000
# calls that do not return (compiler-rt: NORETURN in sanitizer_common.h / sanitizer_internal_defs.h; musl: _Noreturn)
NORETURN = {'_ZN11__sanitizer11CheckFailedEPKciS1_yy', '_ZN11__sanitizer3DieEv', '__stack_chk_fail', 'abort', '_Exit',
            '_exit', '_ZN11__sanitizer14internal__exitEi', '_ZN11__sanitizer23ReportMmapFailureAndDieEmPKcS1_ib'}
# C typedefs of pointer types among the parameters of these images (musl include/alltypes.h.in at f21a96538f78:
# line 74 `TYPEDEF struct __locale_struct * locale_t;`, line 56 `TYPEDEF struct __pthread * pthread_t;` (C))
PTR_TYPEDEFS = {'locale_t', 'pthread_t'}


def sx(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


class Ctx(luihand.Ctx):
    def __init__(self, path):
        luihand.Ctx.__init__(self, path)
        import deadreg
        self.dead = deadreg.Dead(self.img)

    def fstate(self, a, z):
        """objscan.Fn's flow-sensitive values with numeric constants: ('abs', A) only from auipc pairs / .got cells,
        ('const', n) from li / lui / addi on constants, ('arg', r, off) from a parameter (or callee-saved) register plus a
        constant, ('sp', ...) stack; `add` of an address / parameter and a constant keeps the address + constant"""
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
                if mn == 'jal' and (len(ops) == 1 or ops[0] == 'ra'):
                    tg = s.img.wtarget.get(s.a + o)
                    if tg is None:
                        tg = s.a + o + int(ops[-1], 0)
                    if s.img.name_at(tg) in NORETURN:
                        regs.clear(); slots.clear()          # a call that does not return: nothing flows past it
                        return
                if not ops or ops[0] in ('zero', 'sp'):
                    return objscan.Fn.step(s, k, regs, slots, W, summaries, events, seen_ev, label)
                rd = ops[0]
                get = lambda r: (frozenset({('const', 0)}) if r == 'zero' else regs.get(r, frozenset()))
                if mn == 'li':
                    regs[rd] = frozenset({('const', int(ops[1], 0))}); return
                if mn == 'lui':
                    regs[rd] = frozenset({('const', sx(int(ops[1], 0) << 12, 32))}); return
                if mn in ('addi', 'addiw') and len(ops) == 3:
                    c = int(ops[2], 0)
                    src = get(ops[1])
                    if src and all(x[0] == 'const' for x in src):
                        regs[rd] = frozenset({('const', (sx(x[1] + c, 32) if mn == 'addiw' else x[1] + c)) for x in src}); return
                    if src and all(x[0] == 'arg' for x in src):
                        regs[rd] = frozenset({('arg', x[1], None if x[2] is None else x[2] + c) for x in src}); return
                if mn == 'add' and len(ops) == 3:
                    x, y = get(ops[1]), get(ops[2])
                    for p, q in ((x, y), (y, x)):
                        if p and q and len(q) == 1 and list(q)[0][0] == 'const':
                            c = list(q)[0][1]
                            if all(v[0] == 'abs' for v in p):
                                regs[rd] = frozenset({('abs', v[1] + c) for v in p}); return
                            if all(v[0] == 'arg' for v in p):
                                regs[rd] = frozenset({('arg', v[1], None if v[2] is None else v[2] + c) for v in p}); return
                    if x and y and all(v[0] == 'const' for v in x | y) and len(x) == 1 and len(y) == 1:
                        regs[rd] = frozenset({('const', list(x)[0][1] + list(y)[0][1])}); return
                    for p, q in ((x, y), (y, x)):
                        # a parameter pointer plus a non-constant (an index): a pointer into the same object, offset
                        # variable (None)
                        if p and all(v[0] == 'arg' for v in p) and not (q and all(v[0] == 'arg' for v in q)):
                            regs[rd] = frozenset({('arg', v[1], None) for v in p}); return
                if mn == 'mv' and len(ops) == 2:
                    regs[rd] = get(ops[1]); return
                r = objscan.Fn.step(s, k, regs, slots, W, summaries, events, seen_ev, label)
                # objscan keeps ('arg', r) through addi as is; normalise any 2-tuple arg to an offset 0
                if rd in regs:
                    regs[rd] = frozenset(('arg', v[1], 0) if v[0] == 'arg' and len(v) == 2 else v for v in regs[rd])
                return r
        f = Obs(self.img, a, z)
        seed = {r: frozenset({('arg', r, 0)}) for r in luiflow.ARGS + ['s%d' % i for i in range(12)]}
        f.run(objscan.Watch(), seed, {}, [], '')
        self._fs[(a, z)] = rec
        return rec

    def vals(self, a, z, k, reg):
        if reg == 'zero':
            return {('const', 0)}
        if reg == 'sp':
            return {('sp',)}
        v = self.fstate(a, z).get(k, {}).get(reg, set())
        return {('const', x[1]) if x[0] == 'abs' and x[1] < IMG_LO else x for x in v}

    def objs_of_param(self, fa, reg, off, depth=3, seen=None):
        """the objects a member's parameter `reg` points to: each direct caller's value of `reg` at the call"""
        seen = set() if seen is None else seen
        if (fa, reg) in seen or depth < 0:
            return {('runtime', 'recursion')}
        seen.add((fa, reg))
        out = set()
        callers = self.img.callers(fa)
        if not callers:
            return {('runtime', 'no direct caller (indirect or virtual calls only)')}
        for cv, cz, co in callers:
            ins = self.img.dis(cv, cz)
            ks = [i for i, x in enumerate(ins) if x[0] == co]
            if not ks:
                out.add(('runtime', 'call site not decoded')); continue
            v = self.vals(cv, cz, ks[0], reg)
            if not v:
                out.add(('runtime', '%s +%#x: computed / loaded' % (self.img.name_at(cv)[:60], co))); continue
            for x in v:
                if x[0] == 'abs':
                    out.add(('abs', x[1] + off, self.img.name_at(cv)[:60]))
                elif x[0] == 'arg':
                    for y in self.objs_of_param(cv, x[1], (x[2] or 0) + off, depth - 1, seen):
                        out.add(y)
                elif x[0] == 'sp':
                    out.add(('stack', self.img.name_at(cv)[:60]))
                else:
                    out.add(('runtime', '%s +%#x: %s' % (self.img.name_at(cv)[:60], co, x[0])))
        return out

    def classify_other(self, a, z, k, reg):
        """the role of the register an add combines V with: ('obj', ...) an image address, ('param', r, off) a pointer
        parameter / this, ('sp',), ('int', why) an integer, ('unknown', provenance)"""
        v = self.vals(a, z, k, reg)
        if v and all(x[0] == 'abs' for x in v):
            return ('obj', frozenset(x[1] for x in v))
        if v and all(x[0] == 'sp' for x in v):
            return ('sp',)
        if v and all(x[0] == 'const' for x in v):
            return ('int', 'constant')
        if v and all(x[0] == 'arg' for x in v) and len(v) == 1:
            r, off = list(v)[0][1], list(v)[0][2]
            if r.startswith('a'):
                pt = luihand.param(self.member, r)
                if pt == 'this' or pt.startswith('pointer') or '*' in pt or pt.split(' ')[0] in PTR_TYPEDEFS:
                    return ('param', r, off, pt)
                return ('int', 'parameter %s (%s)' % (r, pt))
            return ('unknown', 'callee-saved %s at entry' % r)
        return ('unknown', self.prov(a, z, k, reg))

    def trace(self, a, z, word, vval, start=None):
        """start=None: from the lui word (its rd holds V); start=(k_start, {reg: role}): from instruction index k_start
        with those registers holding the given roles (a callee's parameters, a caller's continuation after a call)"""
        img = self.img
        ins = img.dis(a, z)
        at = {o: k for k, (o, m, p, n) in enumerate(ins)}
        if start is None:
            k0 = at[word]
            rd = ins[k0][2].split(',')[0].strip()
            init = [(k0 + 1, frozenset({(rd, ('V', 0))}))]
        else:
            k0 = start[0] - 1 if start[0] > 0 else 0
            init = [(start[0], frozenset(start[1].items()))]
        rows, bases, follow = {}, set(), set()
        self.last_follow = follow

        def rec(k, text):
            rows[ins[k][0]] = (ins[k][0], '%s %s' % (ins[k][1], ins[k][2]), text) if ins[k][0] not in rows else \
                (ins[k][0], rows[ins[k][0]][1], rows[ins[k][0]][2] if text in rows[ins[k][0]][2] else rows[ins[k][0]][2] + ' | ' + text)

        def fmtrole(r):
            if r[0] == 'V':
                return 'V%+#x' % r[1] if r[1] else 'V'
            if r[0] == 'D':
                return 'D(%s)' % r[1]
            ob = r[1]
            if ob[0] == 'obj':
                od = 'object ' + ' | '.join(img.home(A) for A in sorted(ob[1]))
            elif ob[0] == 'param':
                od = '%s %s%s' % (ob[3], ob[1], ('%+#x' % ob[2] if ob[2] else '') if ob[2] is not None else ' + variable')
            else:
                od = 'stack'
            return 'P(%s, const %#x%s)' % (od, r[2], ', + index' if r[3] else '')

        def full(role, imm):
            """the full address(es) of a base with role `role` and immediate imm, in this image"""
            if role[0] in ('V', 'D'):
                if role[0] == 'V':
                    v = vval + role[1] + imm
                    return ['ABSOLUTE %#x = %s (V itself is the base)' % (v, img.home(v))]
                return ['ABSOLUTE V-derived %s + %#x: REVIEW' % (role[1], imm)]
            obj, cst, var = role[1], role[2] + imm, role[3]
            out = []
            if obj[0] == 'obj':
                for A in sorted(obj[1]):
                    out.append('%s + %#x%s = %s' % (img.home(A), cst, ' + index' if var else '', img.home(A + cst)))
            elif obj[0] == 'param':
                for o in sorted(self.objs_of_param(a, obj[1], obj[2] or 0), key=str):
                    if o[0] == 'abs':
                        out.append('%s (%s passed by %s) + %#x%s = %s' % (img.home(o[1]), obj[3], o[2], cst,
                                                                         ' + index' if var else '', img.home(o[1] + cst)))
                    else:
                        out.append('runtime object (%s) + %#x%s, no image address' % (
                            re.sub(r' \+0x[0-9a-f]+:.*$', '', o[1]), cst, ' + index' if var else ''))
            elif obj[0] == 'sp':
                out.append('stack frame + %#x' % cst)
            else:
                out.append('object %s + %#x: REVIEW' % (obj[1:], cst))
            return out

        seen, work, steps = set(), list(init), 0
        visits, first = collections.Counter(), {}
        while work:
            k, T = work.pop()
            T = dict(T)
            while 0 <= k < len(ins) and T:
                visits[k] += 1
                if visits[k] > 6:
                    # a loop that steps a pointer: widen every P to its first constant here plus a variable index
                    for r, rl in list(T.items()):
                        if rl[0] == 'P':
                            T[r] = ('P', rl[1], first.get((k, r), rl[2]), True)
                        elif rl[0] == 'D':
                            T[r] = ('D', 'loop-varying value from V')
                else:
                    for r, rl in T.items():
                        if rl[0] == 'P':
                            first.setdefault((k, r), rl[2])
                key = (k, frozenset(T.items()))
                if key in seen:
                    break
                seen.add(key); steps += 1
                if steps > 20000:
                    rows[-1] = (-1, '-', 'LIMIT'); break
                o, m, p, nb = ins[k]
                ops = [x.strip() for x in p.split(',')] if p else []
                mm = MEMOP.search(p) if p else None
                rd_ = ops[0] if ops else None
                srcs = [x for x in ops[1:] if x in T] if ops else []
                bm = m.split('.')[0]
                is_ld = bm in ('lb', 'lbu', 'lh', 'lhu', 'lw', 'lwu', 'ld', 'lr', 'flw', 'fld')
                is_st = bm in ('sb', 'sh', 'sw', 'sd', 'sc', 'fsw', 'fsd') or bm.startswith('amo')
                if is_ld or is_st:
                    if mm and mm.group(2) in T:
                        imm = int(mm.group(1) or '0', 0)
                        fa = full(T[mm.group(2)], imm)
                        rec(k, 'BASE %s (full address: BASE columns)' % fmtrole(T[mm.group(2)]))
                        bases.update(fa)
                    data = ops[1] if len(ops) == 3 else (ops[0] if ops else None)
                    slot, why = None, ''
                    if mm and mm.group(2) == 'sp' and bm in ('sd', 'ld'):
                        # the slot by its offset from the stack pointer at entry (spslot.py); a store is a SPILL only
                        # when no pointer to the slot leaves the function (passed / stored / returned) or reaches it
                        fr = spslot.frame(img, a, z)
                        imm = int(mm.group(1) or '0', 0)
                        spo = fr.sp_at.get(k)
                        ok, why = fr.private(k, imm)
                        slot = ('sp@%+d' % (spo + imm)) if ok and spo is not None else None
                    if is_st and data in T and slot is not None:
                        # a SPILL to a private slot of the function's own frame: not a use; followed to its reloads
                        T[slot] = T[data]
                        rec(k, 'SPILL %s to %s (a private slot; not a use; followed to its reloads)' % (fmtrole(T[data]), slot))
                    elif is_st and data in T:
                        rec(k, 'STORE-DATA %s into %s' % (fmtrole(T[data]), '%s+%s (%s)' % (
                            mm.group(2), mm.group(1) or '0', self.prov(a, z, k, mm.group(2)) + (
                                '; not a private slot: %s' % why if why else '')) if mm else '?'))
                        if T[data][0] == 'P':
                            bases.update('stored: ' + x for x in full(T[data], 0))
                    elif is_st and slot is not None and slot in T:
                        del T[slot]                    # the slot is overwritten by another value
                    if is_ld and slot is not None and slot in T:
                        T[rd_] = T[slot]
                        rec(k, 'RELOAD %s from %s into %s' % (fmtrole(T[slot]), slot, rd_))
                    elif (is_ld or len(ops) == 3) and rd_ in T:
                        rec(k, 'ends %s (overwritten by the load)' % rd_)
                        del T[rd_]
                    k += 1; continue
                if m in ('mv', 'sext.w') and len(ops) == 2:
                    if ops[1] in T:
                        T[rd_] = T[ops[1]]; rec(k, 'copy %s -> %s' % (fmtrole(T[ops[1]]), rd_))
                    elif rd_ in T:
                        rec(k, 'ends %s' % rd_); del T[rd_]
                    k += 1; continue
                if m in ALU and ops:
                    if srcs:
                        rs = [T[x] for x in srcs]
                        if m in ('addi', 'addiw') and len(ops) == 3:
                            r0, c = rs[0], int(ops[2], 0)
                            nr = ('V', r0[1] + c) if r0[0] == 'V' else (('P', r0[1], r0[2] + c, r0[3]) if r0[0] == 'P'
                                                                        else ('D', '%s%+#x' % (r0[1], c)))
                        elif m in ('add', 'addw', 'sh1add', 'sh2add', 'sh3add', 'add.uw') and len(ops) == 3:
                            other = [x for x in ops[1:] if x not in T]
                            if len(srcs) == 2:
                                pr = [r for r in rs if r[0] == 'P']
                                nr = (('P', pr[0][1], pr[0][2], True) if pr else ('D', 'sum of two values from V'))
                            else:
                                r0 = rs[0]
                                cls = self.classify_other(a, z, k, other[0])
                                if r0[0] == 'P':
                                    nr = ('P', r0[1], r0[2], r0[3] or cls[0] != 'int' or cls[1] != 'constant')
                                elif cls[0] in ('obj', 'param', 'sp'):
                                    nr = ('P', cls, (vval + r0[1]) if r0[0] == 'V' else 0,
                                          r0[0] == 'D' or (cls[0] == 'param' and cls[2] is None))
                                else:
                                    nr = ('D', '%s %s %s [%s]' % (fmtrole(r0), m, other[0], cls[1] if len(cls) > 1 else cls[0]))
                        else:
                            if m == 'andi' and len(ops) == 3 and int(ops[2], 0) < 0 and rs[0][0] == 'P':
                                # aligning a pointer down (andi p, -2^k): still a pointer into the same object
                                nr = ('P', rs[0][1], rs[0][2], True)
                            elif any(r[0] == 'P' for r in rs) and m in ('sub', 'subw'):
                                nr = ('D', 'difference of pointers / offsets')
                            else:
                                nr = ('D', '%s of %s' % (m, ', '.join(fmtrole(r) for r in rs)))
                        T[rd_] = nr
                        rec(k, '%s -> %s := %s' % (', '.join(fmtrole(r) for r in rs), rd_, fmtrole(nr)))
                    elif rd_ in T:
                        rec(k, 'ends %s' % rd_); del T[rd_]
                    k += 1; continue
                if m in luiflow.CMP:
                    if any(x in T for x in ops):
                        rec(k, 'CMP %s' % ', '.join(fmtrole(T[x]) for x in ops if x in T))
                    if m in escape.BR:
                        try:
                            t2 = o + int(ops[-1], 0)
                            if t2 in at:
                                work.append((at[t2], frozenset(T.items())))
                        except ValueError:
                            pass
                    elif rd_ in T:
                        del T[rd_]
                    k += 1; continue
                if m == 'ecall':
                    import deadreg
                    num = deadreg.syscall_number(ins, k)
                    sreads = deadreg.syscall_reads(ins, k)
                    regs = sorted(x for x in T if x in sreads)
                    nm_ = deadreg.SYSCALL_ARGS.get(num, ('?', 8))[0] if num is not None else 'unknown syscall'
                    if regs:
                        rec(k, 'SYSCALL %s %s (a7 = %s)' % (nm_, ', '.join('%s=%s' % (x, fmtrole(T[x])) for x in regs), num))
                    idle = sorted(x for x in T if x in luiflow.ARGS and x not in sreads)
                    if idle:
                        rec(k, 'SYSCALL-IGNORES %s (%s takes %s argument(s); the kernel preserves them)' % (
                            ','.join(idle), nm_, deadreg.SYSCALL_ARGS.get(num, ('?', '?'))[1]))
                    T.pop('a0', None)                    # the kernel writes the result to a0
                    k += 1; continue
                if m == 'ret':
                    if 'a0' in T:
                        rec(k, 'RET %s' % fmtrole(T['a0']))
                        follow.add(('return', 'a0', T['a0']))
                    for r in sorted(x for x in T if x in luiflow.CLOB and x != 'a0'):
                        rec(k, 'LIVE-AT-RETURN %s %s (a caller-saved register the function hands back unchanged)' % (r, fmtrole(T[r])))
                        follow.add(('return', r, T[r]))
                    break
                if m in ('j', 'jal', 'jr', 'jalr'):
                    pc = a + o
                    tgt = img.wtarget.get(pc)
                    if tgt is None and m in ('j', 'jal'):
                        tgt = pc + int(ops[-1], 0)
                    is_call = (m == 'jal' and (len(ops) == 1 or ops[0] == 'ra')) or \
                              (m == 'jalr' and (len(ops) == 1 or ops[0] == 'ra' or '(' in p))
                    if m in ('jr', 'jalr'):
                        b = (re.findall(r'\((\w+)\)', p) or [ops[-1] if ops else ''])[0]
                        if b in T:
                            rec(k, 'JUMP base %s' % fmtrole(T[b]))
                    if not is_call and m == 'j' and tgt is not None and a <= tgt < a + z and (tgt - a) in at:
                        k = at[tgt - a]; continue
                    if not is_call and m == 'jr' and img.cases.get(a):
                        for c in img.cases[a]:
                            if c in at:
                                work.append((at[c], frozenset(T.items())))
                        break
                    name = img.name_at(tgt) if tgt is not None and tgt in img.starts else None
                    keep = set()
                    for r in sorted(x for x in T if x in luiflow.CLOB):
                        pt = luihand.param(name, r) if name and r in luiflow.ARGS else ('indirect call' if not name else '(not an argument register)')
                        in_sig = pt not in ('(beyond the signature)', '(not an argument register)', 'indirect call') \
                            and not pt.startswith('? (')
                        if r in luiflow.ARGS and in_sig:
                            txt = 'ARG %s %s %s [param: %s]' % ('call' if is_call else 'tail call', name or '?', r, pt)
                            if T[r][0] == 'P':
                                fa = full(T[r], 0)
                                txt += ' -> passes a pointer (full address: BASE columns, `passed:`)'
                                bases.update('passed: ' + x for x in fa)
                            rec(k, '%s %s' % (txt, fmtrole(T[r])))
                            if T[r][0] in ('V', 'D') and tgt is not None and tgt in img.starts:
                                follow.add(('callee', tgt, r, T[r]))
                            if name and tgt is not None:
                                back = self.dead.analyse(tgt, r, ignore_reads=True)
                                if back[0] != 'DEAD' or back[1]:
                                    keep.add(r)          # the callee may hand the parameter back unchanged
                            continue
                        if not name or tgt is None:
                            import deadreg
                            ok, why = deadreg.indirect_unread(img, a, ins, k, r)
                            if ok:
                                rec(k, 'DEAD-AT-CALL %s %s: the indirect callee cannot read it (%s)' % (r, fmtrole(T[r]), why))
                            else:
                                rec(k, 'DEAD-AT-CALL %s %s: UNKNOWN (indirect call)' % (r, fmtrole(T[r])))
                            continue
                        d = self.dead.analyse(tgt, r)
                        if d[0] == 'READ':
                            rec(k, 'ARG-BEYOND-READ %s %s: %s reads it: %s' % (r, fmtrole(T[r]), name, d[1]))
                        elif d[0] == 'UNKNOWN':
                            rec(k, 'DEAD-AT-CALL %s %s: UNKNOWN (%s)' % (r, fmtrole(T[r]), d[1]))
                        elif d[1]:
                            keep.add(r)
                            rec(k, 'DEAD-AT-CALL %s %s: %s never reads it (every path to its return; %s %s) and may hand '
                                   'it back: traced on in the caller' % (r, fmtrole(T[r]), name, 'tail callee:' if not is_call else '', ''))
                        else:
                            rec(k, 'DEAD-AT-CALL %s %s: %s never reads it and writes it on every path to its return' % (
                                r, fmtrole(T[r]), name))
                    if not is_call or (name in NORETURN):
                        if name in NORETURN:
                            rec(k, 'path ends: %s does not return' % name)
                        elif keep:
                            rec(k, 'LIVE-AT-RETURN %s (tail call hands it back to the caller)' % ','.join(sorted(keep)))
                        break
                    for r in list(T):
                        if r in luiflow.CLOB and r not in keep:
                            del T[r]
                    k += 1; continue
                if rd_ in T and m not in ('sb', 'sh', 'sw', 'sd'):
                    rec(k, 'ends %s (%s)' % (rd_, m)); del T[rd_]
                k += 1
        return ins[k0][1] + ' ' + ins[k0][2], [rows[x] for x in sorted(rows)], sorted(bases)


def verdict(tx, ty, bx, by):
    text = ' '.join(r[2] for r in tx)
    if any('REVIEW' in b for b in bx + by) or 'LIMIT' in text:
        return 'REVIEW'
    if any('ABSOLUTE' in b for b in bx + by):
        return 'ABSOLUTE-USE'
    if bx or by:
        # every base / passed / stored pointer must name the same symbol + offset in both images; a runtime object is
        # compared by its constant offset (which caller passes it is attribution, not the address)
        key = lambda b: (b.split(':')[0] if b.startswith(('passed', 'stored')) else 'base',
                         b.split(' = ')[-1] if ' = ' in b else re.sub(r'runtime object \([^)]*\)', 'runtime object',
                                                                        b.split(': ', 1)[-1]))
        kx, ky = {key(b) for b in bx}, {key(b) for b in by}
        if kx != ky:
            return 'DIFFERS'
        return 'OFFSET-SAME-SYMBOL' if any(' = ' in b for b in bx) else 'OFFSET-RUNTIME-OBJECT'
    return 'NOT-AN-ADDRESS'


USEK = ('ARG', 'CMP', 'STORE-DATA', 'RET', 'BASE', 'JUMP', 'SYSCALL', 'DEAD-AT-CALL', 'ARG-BEYOND-READ', 'LIVE-AT-RETURN',
        'SPILL', 'RELOAD', 'path ends')


def followups(ctx, member_addr, vval, depth=4, seen=None, path=()):
    """up to `depth` levels beyond the member: (1) every in-signature argument that carries V / D and that no parameter
    contract settles (contracts.py) is traced in the CALLEE from its entry with that register holding it; (2) every value
    the member hands back (a0 returned, or a caller-saved register left live at a return) is traced in each direct CALLER
    of the member in this image from the instruction after its call. Each follow-up's own follow-ups are followed the
    same way. Returns the entries (path of headers, header, uses text, bases) and whether something was left to follow
    at the depth limit."""
    import contracts
    seen = set() if seen is None else seen
    img, out, more, saved = ctx.img, [], False, ctx.member
    pend = sorted(ctx.last_follow, key=str)
    usetext = lambda rows: [('+%#x %s' % (o, t)) for o, ins_, t in rows if t.split(' ')[0] in USEK or 'BASE' in t]
    for f in pend:
        if f[0] == 'callee':
            tgt, r, role = f[1], f[2], f[3]
            if contracts.lookup(img.name_at(tgt), r):
                continue                                   # settled by its parameter contract (class i)
            key = ('callee', tgt, r, role)
            if key in seen:
                continue
            seen.add(key)
            if depth <= 0:
                more = True; continue
            zc = [x for x in img.funcs if x[0] == tgt][0][1]
            ctx.member = img.name_at(tgt)
            _, rows, bases = ctx.trace(tgt, zc, None, vval, start=(0, {r: role}))
            hdr = 'IN-CALLEE %s %s (%s)' % (img.name_at(tgt), r, role[0])
            out.append((path + (hdr,), hdr, ' ; '.join(usetext(rows)) or 'no use', bases))
            sub, m2 = followups(ctx, tgt, vval, depth - 1, seen, path + (hdr,))
            out.extend(sub)
            more = more or m2
        else:
            r, role = f[1], f[2]
            if r == 'a0' and contracts.RETURNS.get(img.name_at(member_addr)):
                continue                                   # an integer return, not an address by its cited meaning (ii)
            for cv, cz, co in img.callers(member_addr):
                key = ('caller', cv, co, r, role)
                if key in seen:
                    continue
                seen.add(key)
                if depth <= 0:
                    more = True; continue
                cins = img.dis(cv, cz)
                ks = [i for i, x in enumerate(cins) if x[0] == co]
                if not ks:
                    continue
                ins0 = cins[ks[0]]
                ctx.member = img.name_at(cv)
                hdr = 'IN-CALLER %s +%#x %s' % (img.name_at(cv), co, r)
                if ins0[1] in ('j', 'jr') or (ins0[1] == 'jalr' and ins0[2].startswith('zero')):
                    # a tail call: the value goes back to the caller's own callers
                    out.append((path + (hdr,), hdr, 'a tail call there: followed into its callers', []))
                    ctx.last_follow = {('return', r, role)}
                    sub, m2 = followups(ctx, cv, vval, depth - 1, seen, path + (hdr,))
                    out.extend(sub)
                    more = more or m2
                    continue
                _, rows, bases = ctx.trace(cv, cz, None, vval, start=(ks[0] + 1, {r: role}))
                out.append((path + (hdr,), hdr, ' ; '.join(usetext(rows)) or 'no use (overwritten before any read)', bases))
                sub, m2 = followups(ctx, cv, vval, depth - 1, seen, path + (hdr,))
                out.extend(sub)
                more = more or m2
    ctx.member = saved
    return out, more


def ftext(e):
    return '%s%s: %s%s' % ('  ' * (len(e[0]) - 1), e[1], e[2], ' ; BASES ' + ' / '.join(e[3]) if e[3] else '')


def fcompare(fx, fy):
    """the follow-ups of the two images by their header path: the paths in both must give the same uses (hex of 4+ digits
    masked); a path in one image only (a caller the other program does not have) is listed, its uses settled on their
    own. Returns (equal, common paths, X-only paths, Y-only paths, the bases of the common paths X / Y)"""
    mask = lambda s: re.sub(r'0x[0-9a-f]{4,}', '#', s)
    kx = {tuple(mask(h) for h in e[0]): e for e in fx}
    ky = {tuple(mask(h) for h in e[0]): e for e in fy}
    common_ = sorted(set(kx) & set(ky))
    eq = all(mask(kx[k][2]) == mask(ky[k][2]) for k in common_)
    bx = [b for k in common_ for b in kx[k][3]]
    by = [b for k in common_ for b in ky[k][3]]
    return eq, common_, sorted(set(kx) - set(ky)), sorted(set(ky) - set(kx)), bx, by


def main():
    X, Y = Ctx(common.CGIF_B_TWIN), Ctx(common.DECODE_B_TWIN)
    common.jump_cases(X.img, Y.img)                 # every measured rel4 jump table: a `jr` goes to its cases
    fd = {}
    for l in list(open(os.path.join(common.HERE, 'scans', 'exposure.tsv')))[1:]:
        c = l.rstrip('\n').split('\t')
        fd[int(c[1], 16)] = (int(c[2], 16), int(c[3]))
    out, cnt = [], collections.Counter()
    targets = sys.argv[1] if len(sys.argv) > 1 else os.path.join(common.HERE, 'scans', 'lui-targets.tsv')
    outfile = sys.argv[2] if len(sys.argv) > 2 else os.path.join(common.HERE, 'scans', 'luitrace.tsv')
    only = set(filter(None, os.environ.get('LUI_ONLY', '').split(',')))      # member-address@word items, for the plants
    import time
    for l in list(open(targets))[1:]:
        member, ax, word, vals = l.rstrip('\n').split('\t')
        ax, w = int(ax, 16), int(word, 16)
        if only and '%#x@%#x' % (ax, w) not in only:
            continue
        t0 = time.time()
        ay, z = fd[ax]
        vv = int(vals.split(' ')[0], 16)
        X.member, Y.member = X.img.name_at(ax), Y.img.name_at(ay)
        lx, tx, bx = X.trace(ax, z, w, vv)
        fx, mx = followups(X, ax, vv)
        ly, ty, by = Y.trace(ay, z, w, vv)
        fy, my = followups(Y, ay, vv)
        feq, fcom, xonly, yonly, fbx, fby = fcompare(fx, fy)
        bx, by = bx + sorted(set(fbx)), by + sorted(set(fby))
        same = [re.sub(r'0x[0-9a-f]{5,}', '#', r[2]) for r in tx] == [re.sub(r'0x[0-9a-f]{5,}', '#', r[2]) for r in ty] \
            and feq
        v = verdict(tx, ty, bx, by)
        if not same and v not in ('DIFFERS', 'REVIEW'):
            v = 'REVIEW'
        cnt[v] += 1
        own = lambda fs, keys: ' ;; '.join(b for e in fs if tuple(re.sub(r'0x[0-9a-f]{4,}', '#', h) for h in e[0]) in keys
                                          for b in e[3]) or '-'
        out.append((member, '%#x' % ax, '%#x' % ay, word, '%#x' % vv, lx,
                    ' ;; '.join('+%#x %s :: %s' % r for r in tx), ' ;; '.join(bx) or '-', ' ;; '.join(by) or '-',
                    'same' if same else 'DIFFER: ' + ' ;; '.join('+%#x %s :: %s' % r for r in ty), v,
                    ' ;; '.join(ftext(e) for e in fx) or '-', 'MORE' if (mx or my) else '-',
                    ' ;; '.join(ftext(e) for e in fy) or '-',
                    'common %d (%s), X only %d, Y only %d' % (len(fcom), 'equal' if feq else 'NOT EQUAL', len(xonly),
                                                              len(yonly)),
                    own(fx, set(xonly)), own(fy, set(yonly))))
        print('  row %s %#x: %.1fs' % (member[:50], w, time.time() - t0), file=sys.stderr)
    with open(outfile, 'w') as f:
        f.write('member\tX addr\tY addr\tword\tV\tlui word\tTRACE in X (pc, instruction :: role / use)\tBASE full addresses X '
                '(main trace and the follow-ups both images have)\tBASE full addresses Y (the same)\ttrace in Y (masked '
                'compare)\tverdict\tfollow-ups in X (callees given V as a parameter; callers given V back; 4 levels)\ta '
                'further level left\tfollow-ups in Y\tfollow-up compare (by header path)\tBASES of the follow-ups only X '
                'has\tBASES of the follow-ups only Y has\n')
        for r in out:
            f.write('\t'.join(r) + '\n')
    print('targets %d (%s): %s' % (len(out), os.path.basename(targets), dict(sorted(cnt.items()))))
    for r in out:
        if r[10] not in ('NOT-AN-ADDRESS', 'OFFSET-SAME-SYMBOL', 'OFFSET-RUNTIME-OBJECT'):
            print('  %s %s %s %s' % (r[10], r[0][:70], r[3], r[4]))


if __name__ == '__main__':
    main()
