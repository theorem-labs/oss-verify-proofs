#!/usr/bin/env python3
"""objscan.py -- whole-image scan of every access to the object fields that an escaping empty-string pointer is stored
into. Read-only. Writes one TSV (OUT) and prints a summary.

For each ACCEPT row of SETTLE_TSV that settle.py left UNSETTLED on a 1-byte target (`00` in both images), in each image:
  1. ESCAPE: the stores of the pointer (`settle.uses` from the row's word), each with its decoded instruction.
  2. OBJECT: what the store's base register points to, by reaching definitions: the function's `this` (then the value
     of a0 at every direct call site in the image: a global symbol or a stack slot of the caller), a global symbol, or
     a heap object from `LowLevelAllocator::Allocate` whose word 0 is set to a vtable (`_ZTV...+0x10`) in that block.
  3. SCAN: every place in the image where that object's field is reached, as a pointer fact (function, word, register,
     offset from the object base) followed forward with `addi` offsets, stack spills / reloads and:
       - a direct call that uses the argument register: into the callee (with the call site kept as context);
       - a pointer return (a0 at `ret`): to the caller in context, else to every direct caller;
       - `internal_memcpy` with the object as source (a1): the destination (a0) becomes a copy of the object, scanned
         the same way (a stack slot, a global, or a parameter resolved through the context);
       - the field's address stored into a heap object with a vtable (a flag handler's `t_`): that class's vtable
         methods are scanned for loads of that slot, and the loaded address is followed;
       - a global object's address taken anywhere: every function that materialises it (auipc+addi or a .got cell).
     A register that is only live at a call whose callee never reads it is not an argument (recorded as such).
  4. READ SITES: every 8-byte load of the field. The loaded pointer's readers come from `settle.string_readers`
     (named `const char *` parameters, printf-like `%s` varargs with the format checked, lb/lbu, pointer compares,
     returns), with PARAMS entries added below for the callees this scan reaches, each from its mangled name; a
     register-indirect call is resolved through the vtables stored into the object it is made on.
  5. Anything the scan cannot follow is a row with kind UNRESOLVED (none is hidden).
Writes (`sd`/`sb`... into the field) are listed as WRITE rows: they replace the value and read nothing.
usage: objscan.py X_ELF Y_ELF SETTLE_TSV OUT_TSV"""
import os, runpy, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
_argv = sys.argv[:]
sys.argv = [os.path.join(HERE, 'settle.py'), _argv[1], _argv[2], '']
S = runpy.run_path(os.path.join(HERE, 'settle.py'), run_name='settle_lib')
sys.argv = _argv
dc, Fn, dec, RN = S['dc'], S['Fn'], S['dec'], S['RN']
LOADW, STORE, BRANCH, CALLER_SAVED, writes = S['LOADW'], S['STORE'], S['BRANCH'], S['CALLER_SAVED'], S['writes']
fsymq = S['jt']['fsymq']

# prototypes of the callees this scan reaches (added to settle's table; each from its mangled name)
S['PARAMS'].update({
    '_ZN11__sanitizer18SuppressionContext13ParseFromFileEPKc': (2, {1}, None,
        'SuppressionContext::ParseFromFile(this, const char *): member, PKc'),
    '_ZN11__sanitizer15StripPathPrefixEPKcS1_': (2, {0, 1}, None, 'StripPathPrefix(const char *, const char *): PKc S1_=PKc'),
    '_ZN11__sanitizer17StackTracePrinter20RenderSourceLocationEPNS_20InternalScopedStringEPKciibS4_': (7, {2, 6}, None,
        'StackTracePrinter::RenderSourceLocation(this, InternalScopedString *, const char *, int, int, bool, const char *): '
        'member, PKc ... S4_=PKc'),
    '_ZN11__sanitizer17StackTracePrinter20RenderModuleLocationEPNS_20InternalScopedStringEPKcmNS_10ModuleArchES4_': (6, {2, 5}, None,
        'StackTracePrinter::RenderModuleLocation(this, InternalScopedString *, const char *, uptr, ModuleArch, const char *): '
        'member, PKc ... S4_=PKc'),
    '_ZN11__sanitizer26FormattedStackTracePrinter11RenderFrameEPNS_20InternalScopedStringEPKcimPKNS_11AddressInfoEbS4_': (8, {2, 7}, None,
        'FormattedStackTracePrinter::RenderFrame(this, InternalScopedString *, const char *, int, uptr, const AddressInfo *, '
        'bool, const char *): member, PKc ... S4_=PKc'),
    '_ZN11__sanitizer23MarkupStackTracePrinter11RenderFrameEPNS_20InternalScopedStringEPKcimPKNS_11AddressInfoEbS4_': (8, {2, 7}, None,
        'MarkupStackTracePrinter::RenderFrame(this, InternalScopedString *, const char *, int, uptr, const AddressInfo *, '
        'bool, const char *): member, PKc ... S4_=PKc'),
    '_ZN11__sanitizer17internal_snprintfEPcmPKcz': (3, set(), (2, 3),
        'internal_snprintf(char *, uptr, const char *format, ...): Pc m PKcz'),
})
MEMCPY = {'__sanitizer_internal_memcpy', '_ZN11__sanitizer15internal_memcpyEPvPKvm'}
ALLOC = '_ZN11__sanitizer17LowLevelAllocator8AllocateEm'

_fn = {}
def fn_at(Im, a):
    k = (id(Im), a)
    if k not in _fn:
        z = next((z for v, z, n, t in Im.syms if v == a and t == 'STT_FUNC' and z > 0), None)
        _fn[k] = Fn(Im, a, z) if z else None
    return _fn[k]
def name(Im, a):
    q = dc.qres(Im, a); return q[:-4] if q and q.endswith('+0x0') else q

def ins(F, j):
    o, x, n = F.w[j]; m, rd, r1, r2, im = dec(x)
    if m in STORE: return '%s %s,%d(%s)' % (m, RN[r2], im, RN[r1])
    if m in LOADW: return '%s %s,%d(%s)' % (m, RN[rd], im, RN[r1])
    if m == 'jalr': return 'jalr %s,%d(%s)' % (RN[rd], im, RN[r1])
    if m == 'jal': return 'jal %s,%s' % (RN[rd], name(F.I, F.a + o + im))
    if m in ('addi', 'andi', 'ori', 'xori', 'slli', 'srli', 'srai'): return '%s %s,%s,%d' % (m, RN[rd], RN[r1], im)
    if m == 'auipc': return 'auipc %s,%#x' % (RN[rd], im & 0xfffff)
    return m + ' ' + ','.join(RN[r] for r in (rd, r1, r2) if r is not None)

def rdefs(F, i, reg):
    """reaching definitions of reg at word i: ('def', j), ('call', j) for a0/a1 after a call, ('entry',), ('clobber', j)"""
    out = set(); seen = set(); work = list(F.preds(i))
    if i == 0: out.add(('entry',))
    while work:
        j = work.pop()
        if j in seen: continue
        seen.add(j)
        m, rd, r1, r2, im = F.d[j]
        if m in ('jal', 'jalr') and rd == 1:
            if reg in (10, 11): out.add(('call', j)); continue
            if reg in CALLER_SAVED: out.add(('clobber', j)); continue
        if writes(m, rd) and rd == reg: out.add(('def', j)); continue
        if j == 0: out.add(('entry',))
        work += F.preds(j)
    return out

def value(F, i, reg, depth=0):
    """abstract values reg may hold at word i: ('sym', addr) ('stack', off) ('ret', callee, j) ('param', k) ('unknown', why)"""
    if depth > 10: return {('unknown', 'depth')}
    out = set()
    for d in rdefs(F, i, reg):
        if d[0] == 'entry': out.add(('param', reg - 10) if 10 <= reg <= 17 else ('unknown', 'entry %s' % RN[reg]))
        elif d[0] == 'clobber': out.add(('unknown', 'clobbered by the call at %s' % F.pc(d[1])))
        elif d[0] == 'call':
            o = F.w[d[1]][0]; m, rd, r1, r2, im = F.d[d[1]]
            out.add(('ret', name(F.I, F.a + o + im) if m == 'jal' else '(register-indirect)', d[1]))
        else:
            j = d[1]; m, rd, r1, r2, im = F.d[j]
            if m == 'addi' and j in F.t: out.add(('sym', F.t[j][1]))
            elif m == 'ld' and j in F.t and F.I.sec(F.t[j][1]) == '.got':
                out.add(('sym', int.from_bytes(dc.frd(F.I, F.t[j][1], 8), 'little')))
            elif m == 'addi' and r1 == 2: out.add(('stack', im))
            elif m == 'addi' and r1 == 0: out.add(('const', im))
            elif m == 'addi' and r1:
                for v in value(F, j, r1, depth + 1):
                    out.add((v[0], v[1] + im) + v[2:] if v[0] in ('sym', 'stack') else v)
            elif m == 'ld' and r1 == 2:
                for k in range(len(F.w)):
                    mk, rdk, r1k, r2k, imk = F.d[k]
                    if mk == 'sd' and r1k == 2 and imk == im: out |= value(F, k, r2k, depth + 1)
            else: out.add(('unknown', '%s %s' % (F.pc(j), ins(F, j))))
    return out

def track(F, start, reg, delta, entry=False):
    """forward uses of reg = base + delta: ('load', j, off, rd, m) ('write', j, off) ('addr-stored', j, base_reg, imm)
    ('call', j, callee_addr_or_None, argno, delta) ('ret', j, delta) ('other', j)"""
    out = []; seen = set(); slots = {}
    work = [(start, reg, delta)] if entry else [(j, reg, delta) for j in F.succ(start)]
    while work:
        i, r, dl = work.pop()
        if (i, r, dl) in seen or len(seen) > 200000: continue
        seen.add((i, r, dl))
        o = F.w[i][0]; m, rd, r1, r2, im = F.d[i]; stop = False
        if m == 'addi' and r1 == r and rd:
            for j in F.succ(i): work.append((j, rd, dl + im))
        elif m in LOADW and r1 == r: out.append(('load', i, dl + im, rd, m))
        elif m in STORE and r1 == r and r2 != r: out.append(('write', i, dl + im))
        elif m in STORE and r2 == r:
            if r1 == 2 and m == 'sd': slots[im] = dl
            else: out.append(('addr-stored', i, r1, im, dl))
        elif m == 'jal' and not (0 <= o + im < F.z):
            if 10 <= r <= 17: out.append(('call', i, F.a + o + im, r - 10, dl))
            stop = rd == 0 or r in CALLER_SAVED
        elif m == 'jalr':
            if rd == 0 and r1 == 1:
                if r == 10: out.append(('ret', i, dl))
                stop = True
            elif rd == 0 and F.cases: pass
            else:
                if 10 <= r <= 17: out.append(('call', i, None, r - 10, dl))
                stop = rd == 0 or r in CALLER_SAVED
        elif m in BRANCH and r in (r1, r2): pass
        elif r in (r1, r2): out.append(('other', i))
        if stop or (writes(m, rd) and rd == r): continue
        for j in F.succ(i): work.append((j, r, dl))
    for i in range(len(F.w)):
        m, rd, r1, r2, im = F.d[i]
        if m == 'ld' and r1 == 2 and im in slots and rd: out += track(F, i, rd, slots[im])
    return out

def reads_param(Im, a, k):
    """does the function at a read argument register a_k (any use before it is written)?"""
    C = fn_at(Im, a)
    return C is not None and bool(track(C, 0, 10 + k, 0, entry=True))

def heap_class(F, j, rb):
    """the vtable class of the heap object rb points to at word j (word 0 set to a _ZTV symbol in the block), or None"""
    for v in value(F, j, rb):
        if v[0] == 'ret' and v[1] == ALLOC:
            for k in range(v[2] + 1, min(len(F.w), v[2] + 24)):
                m, rd, r1, r2, im = F.d[k]
                if m == 'sd' and im == 0:
                    for vv in value(F, k, r2):
                        q = dc.qres(F.I, vv[1]) if vv[0] == 'sym' else ''
                        if q and q.startswith('_ZTV'):
                            if r1 == rb or any(x[0] == 'ret' and x[2] == v[2] for x in value(F, k, r1)): return q.split('+')[0]
    return None

def vt_methods(Im, vt):
    a, z = next((a, z) for a, z, t in Im.byname[vt] if t == 'STT_OBJECT')
    out = []
    for s in range(2, z // 8):
        p = int.from_bytes(dc.frd(Im, a + 8 * s, 8) or b'\0' * 8, 'little')
        if p and fn_at(Im, p): out.append((s - 2, p))
    return out

def virtual_callees(F, i):
    """callees of the register-indirect call at word i: jalr ra,0(t); t = ld s(v); v = ld 0(o); o = the return of R;
    R stores _ZTV...+0x10 at offset 0 of the object it returns -> slot s of each such vtable"""
    m, rd, r1, r2, im = F.d[i]; out = set()
    for d in rdefs(F, i, r1):
        if d[0] != 'def': return None
        ms, rds, r1s, _, ims = F.d[d[1]]
        if ms != 'ld': return None
        for d2 in rdefs(F, d[1], r1s):
            if d2[0] != 'def': return None
            mv, rdv, r1v, _, imv = F.d[d2[1]]
            if mv != 'ld' or imv != 0: return None
            for o in value(F, d2[1], r1v):
                if o[0] != 'ret' or not o[1] or o[1].startswith('('): return None
                R = fn_at(F.I, fsymq(F.I, o[1])[0])
                vts = set()
                for k in range(len(R.w)):
                    mk, rdk, r1k, r2k, imk = R.d[k]
                    if mk == 'sd' and imk == 0:
                        for vv in value(R, k, r2k):
                            q = dc.qres(R.I, vv[1]) if vv[0] == 'sym' else ''
                            if q and q.startswith('_ZTV') and q.endswith('+0x10'): vts.add(q[:-5])
                if not vts: return None
                for vt in vts:
                    a = next(a for a, z, t in F.I.byname[vt] if t == 'STT_OBJECT')
                    p = int.from_bytes(dc.frd(F.I, a + 16 + ims, 8), 'little')
                    out.add((vt, name(F.I, p), p))
    return out or None

def readers(F, j, rd):
    """C-string readers of the pointer loaded into rd at word j -> (ok, evidence list, unresolved list)"""
    ok, ev, unk = S['string_readers'](F, None, j, rd, 1)
    left = []
    for u in unk:
        if 'register-indirect' not in u: left.append(u); continue
        # resolve each register-indirect call that takes the pointer
        done = False
        for kind, i, d in S['uses'](F, j, rd):
            if kind == 'arg' and d[0] == '(register-indirect)' and F.pc(i) in u:
                cs = virtual_callees(F, i)
                if not cs: break
                k = d[1]; good = []
                for vt, nm, p in sorted(cs):
                    pr = S['PARAMS'].get(nm)
                    if pr and k in pr[1]: good.append('%s (slot of %s) [%s]' % (nm, vt, pr[3]))
                    else: good = None; break
                if good:
                    ev.append('%s a%d -> virtual call %s, resolved: %s' % (F.pc(i), k, ins(F, i), ' / '.join(good))); done = True
                break
        if not done: left.append(u)
    return not left and bool(ev), ev, left

def scan(Im, label, fld, objs, rowtag, out, osize):
    """follow every pointer fact for the object(s); emit READ / WRITE / UNRESOLVED / FOLLOW rows"""
    facts = []; seenf = set(); scanned_g = set(); nread = 0
    def emit(kind, F, j, detail):
        out.append('\t'.join([label, rowtag, kind, name(Im, F.a) if F else '-', F.pc(j) if F else '-',
                              ins(F, j) if F else '-', detail]))
    def is_kill(C, k, sp0):
        """a call that (re)initialises the stack region at sp+sp0: a constructor (C1/C2) or a memset with a0 in it"""
        m, rd, r1, r2, im = C.d[k]
        if m != 'jal' or rd != 1: return False
        cn = name(Im, C.a + C.w[k][0] + im) or ''
        return ('C1E' in cn or 'C2E' in cn or 'memset' in cn) and any(
            v[0] == 'stack' and sp0 <= v[1] < sp0 + osize for v in value(C, k, 10))
    def reach(C, starts, kills):
        seen = set(); work = []
        for k in starts: work += list(C.succ(k)) if k is not None else [0]
        while work:
            k = work.pop()
            if k in seen: continue
            seen.add(k)
            if k in kills: continue                          # another object starts here
            work += C.succ(k)
        return seen - kills
    def live_from(C, c, sp0):
        """the words that see the object at sp+sp0 of C that word c writes: the stack slot is shared by objects of
        disjoint scopes, so the object's lifetime is measured: from its birth (the constructor / memset of that region
        from which c is reachable without passing another one; the function entry if there is none) to the next one"""
        kills = {k for k in range(len(C.w)) if is_kill(C, k, sp0)}
        births = [k for k in kills if c in reach(C, [k], kills)] or [None]
        return reach(C, births, kills)
    def add_stack(C, sp0, base, ctx, why, c):
        """the object (base offset `base` of it) lives at sp+sp0 of C from word c on: follow every address of it
        computed while it is live, and read its field"""
        live = live_from(C, c, sp0)
        for w in sorted(live):
            mw, rdw, r1w, r2w, imw = C.d[w]
            if mw == 'addi' and r1w == 2 and rdw and sp0 <= imw < sp0 + osize:     # an address inside the object
                facts.append((C, w, rdw, base + imw - sp0, False, ctx, why))
            elif mw == 'ld' and r1w == 2 and imw == sp0 + fld - base: facts.append(('direct-load', C, w))
            elif mw in STORE and r1w == 2 and imw == sp0 + fld - base: emit('WRITE', C, w, '[%s] store into the field' % why)
    def add_global(ga, gn):
        if ga in scanned_g: return
        scanned_g.add(ga)
        gz = next(z for a, z, t in Im.byname[gn] if t == 'STT_OBJECT')
        for v, z, n, t in Im.syms:
            if t != 'STT_FUNC' or z <= 0: continue
            b = dc.frd(Im, v, z)
            if b is None: continue
            tt = dc.targets(v, b); F = None
            for k, (kind, ta) in tt.items():
                tv = ta
                if Im.sec(ta) == '.got': tv = int.from_bytes(dc.frd(Im, ta, 8) or b'\0' * 8, 'little')
                if not (ga <= tv < ga + gz): continue
                F = F or fn_at(Im, v)
                m, rd, r1, r2, im = F.d[k]
                if m == 'addi' or (m == 'ld' and Im.sec(ta) == '.got'): facts.append((F, k, rd, tv - ga, False, (), 'global %s' % gn))
                elif m in LOADW and tv - ga == fld: facts.append(('direct-load', F, k))
                elif m in STORE and tv - ga == fld: emit('WRITE', F, k, 'direct store to %s+%d' % (gn, fld))
    for o in objs:
        if o[0] == 'global': add_global(o[1], o[2])
        elif o[0] == 'stackobj': add_stack(o[1], o[2], 0, (), 'stack object at sp+%d of %s' % (o[2], name(Im, o[1].a)), o[3])
        elif o[0] == 'heap':
            for s, p in vt_methods(Im, o[1]):
                facts.append((fn_at(Im, p), 0, 10, 0, True, (), 'this of %s slot %d' % (o[1], s)))
    while facts:
        f = facts.pop()
        if f[0] == 'direct-load':
            F, k = f[1], f[2]; rd = F.d[k][1]
            ok, ev, un = readers(F, k, rd); nread += 1
            emit('READ' if ok else 'UNRESOLVED', F, k, '; '.join(ev) + (' | NOT SHOWN: ' + '; '.join(un) if un else '')); continue
        F, st0, reg, dl, ent, ctx, why = f
        key = (F.a, st0, reg, dl, ent, tuple((c[0].a, c[1]) for c in ctx))
        if key in seenf or len(ctx) > 6: continue
        seenf.add(key)
        for u in track(F, st0, reg, dl, ent):
            kind, i = u[0], u[1]
            if kind == 'load':
                if u[2] == fld and u[4] == 'ld':
                    ok, ev, un = readers(F, i, u[3]); nread += 1
                    emit('READ' if ok else 'UNRESOLVED', F, i, '[%s] ' % why + '; '.join(ev) + (' | NOT SHOWN: ' + '; '.join(un) if un else ''))
                elif u[2] == fld: emit('UNRESOLVED', F, i, 'a %s of the field (not an 8-byte pointer load)' % u[4])
            elif kind == 'write':
                if u[2] == fld: emit('WRITE', F, i, '[%s] store into the field' % why)
            elif kind == 'addr-stored':
                rb, imm, d0 = u[2], u[3], u[4]
                if d0 > fld or (d0 != fld and d0 != 0): continue      # the address of another field
                cls = heap_class(F, i, rb)
                if cls:
                    emit('FOLLOW', F, i, '[%s] address (+%d) stored at %d(%s), a %s object: its vtable methods\' loads of that slot are followed' % (why, d0, imm, RN[rb], cls))
                    for s, p in vt_methods(Im, cls):
                        M = fn_at(Im, p)
                        for v in track(M, 0, 10, 0, entry=True):
                            if v[0] == 'load' and v[2] == imm and v[4] == 'ld':
                                facts.append((M, v[1], v[3], d0, False, (), '%s slot %d via %s' % (cls, s, why)))
                else: emit('UNRESOLVED', F, i, '[%s] address (+%d) stored at %d(%s): not a heap object with a vtable' % (why, d0, imm, RN[rb]))
            elif kind == 'call':
                ca, k, d0 = u[2], u[3], u[4]
                if ca is None:
                    cs = virtual_callees(F, i)
                    if cs:
                        for vt, nm, p in cs:
                            if reads_param(Im, p, k): facts.append((fn_at(Im, p), 0, 10 + k, d0, True, ctx + ((F, i),), why))
                    else: emit('UNRESOLVED', F, i, '[%s] a%d (+%d) to an unresolved register-indirect call' % (why, k, d0))
                    continue
                cn = name(Im, ca)
                if k == 0 and ('C1E' in cn or 'C2E' in cn or 'memset' in cn):
                    emit('WRITE', F, i, '[%s] the address (+%d) is initialised by %s (another object starts here)' % (why, d0, cn)); continue
                if cn in MEMCPY or any(c in MEMCPY for c in cn.split('/')):
                    ln = sorted(v[1] for v in value(F, i, 12) if v[0] == 'const')
                    if k == 1 and ln != [osize]:
                        emit('UNRESOLVED', F, i, '[%s] the object is the memcpy source, length %s, not the object size %d' % (why, ln or 'unknown', osize)); continue
                    if k == 1:
                        for dv in value(F, i, 10):
                            if dv[0] == 'stack':
                                emit('FOLLOW', F, i, '[%s] the object (+%d) is copied by %s into sp+%d of %s' % (why, d0, cn, dv[1], name(Im, F.a)))
                                add_stack(F, dv[1], d0, ctx, 'copy at sp+%d of %s' % (dv[1], name(Im, F.a)), i)
                            elif dv[0] == 'sym':
                                gq = dc.qres(Im, dv[1]); gn = gq.split('+')[0] if gq else None
                                emit('FOLLOW', F, i, '[%s] the object (+%d) is copied by %s into %s' % (why, d0, cn, gq))
                                if gn: add_global(dv[1] - int(gq.split('+')[1], 16) if '+' in gq else dv[1], gn)
                            elif dv[0] == 'param' and ctx:
                                C, ci = ctx[-1]
                                for cv in value(C, ci, 10 + dv[1]):
                                    if cv[0] == 'stack':
                                        emit('FOLLOW', C, ci, '[%s] the object is copied (via %s) into sp+%d of %s' % (why, name(Im, F.a), cv[1], name(Im, C.a)))
                                        add_stack(C, cv[1], d0, ctx[:-1], 'copy at sp+%d of %s' % (cv[1], name(Im, C.a)), ci)
                                    elif cv[0] == 'sym':
                                        gq = dc.qres(Im, cv[1]); gn = gq.split('+')[0]
                                        emit('FOLLOW', C, ci, '[%s] the object is copied (via %s) into %s' % (why, name(Im, F.a), gq))
                                        add_global(cv[1], gn)
                                    else: emit('UNRESOLVED', C, ci, '[%s] copy destination %s' % (why, cv))
                            else: emit('UNRESOLVED', F, i, '[%s] copy destination %s' % (why, dv))
                    continue                                          # k == 0 / 2: the object is written or a length
                if reads_param(Im, ca, k): facts.append((fn_at(Im, ca), 0, 10 + k, d0, True, ctx + ((F, i),), why))
            elif kind == 'ret':
                if ctx:
                    C, ci = ctx[-1]; facts.append((C, ci, 10, u[2], False, ctx[:-1], why))
                else:
                    for C, ci in S['callers'](Im, F.a): facts.append((C, ci, 10, u[2], False, (), why))
            elif kind == 'other':
                m = F.d[i][0]
                if m in ('add', 'sub', 'and', 'or', 'xor', 'sltu', 'slt'): continue   # pointer compares / arithmetic: no read
                emit('UNRESOLVED', F, i, '[%s] %s on the object pointer' % (why, m))
    return nread

def main():
    lines = open(_argv[3]).read().splitlines(); out = []
    rows = [l.split('\t') for l in lines if l.startswith('ACCEPT\t') and not l.startswith('ACCEPT\tfunction')]
    rows = [r for r in rows if r[6] in ('UNSETTLED', 'CSTR-ESCAPE') and r[9] == '00' and r[10] == '00']
    summary = []
    for label, Im, path in (('X', S['X'], _argv[1]), ('Y', S['Y'], _argv[2])):
        gseen = {}
        for r in rows:
            fn, off = r[1], int(r[2], 16)
            F = fn_at(Im, fsymq(Im, fn)[0]); i = F.idx[off]; rd = F.d[i][1]
            stores = [u for u in S['uses'](F, i, rd) if u[0] == 'store']
            for kind, j, d in stores:
                m, _, rb, rv, fld = F.d[j]
                rowtag = '%s+%s %s' % (fn, r[2], F.pc(j))
                objs = []; desc = []
                for v in value(F, j, rb):
                    if v[0] == 'param' and v[1] == 0:
                        for C, ci in S['callers'](Im, F.a):
                            for cv in value(C, ci, 10):
                                if cv[0] == 'sym':
                                    gq = dc.qres(Im, cv[1]); gn = gq.split('+')[0]
                                    objs.append(('global', cv[1], gn)); desc.append('%s (this at %s %s)' % (gq, name(Im, C.a), C.pc(ci)))
                                elif cv[0] == 'stack':
                                    objs.append(('stackobj', C, cv[1], ci))
                                    desc.append('a stack object at sp+%d of %s (this at %s)' % (cv[1], name(Im, C.a), C.pc(ci)))
                                else: desc.append('UNRESOLVED this %s at %s %s' % (cv, name(Im, C.a), C.pc(ci)))
                    elif v[0] == 'sym':
                        gq = dc.qres(Im, v[1]); gn = gq.split('+')[0]
                        objs.append(('global', v[1] - (int(gq.split('+')[1], 16) if '+' in gq else 0), gn)); desc.append(gq)
                        fld = fld + (int(gq.split('+')[1], 16) if '+' in gq else 0)
                    else:
                        cls = heap_class(F, j, rb)
                        if cls: objs.append(('heap', cls)); desc.append('a heap %s object (LowLevelAllocator::Allocate, vtable at +0)' % cls)
                        else: desc.append('UNRESOLVED base %s' % (v,))
                out.append('\t'.join([label, rowtag, 'ESCAPE', fn, F.pc(j), '%s %s,%d(%s)' % (m, RN[rv], fld, RN[rb]),
                                      'field +%d of %s' % (fld, '; '.join(sorted(set(desc))))]))
                gs = sorted({next(z for a, z, t in Im.byname[o[2]] if t == 'STT_OBJECT') for o in objs if o[0] == 'global'})
                osize = gs[0] if len(gs) == 1 else 0
                if any(o[0] == 'stackobj' for o in objs) and not osize:
                    out.append('\t'.join([label, rowtag, 'UNRESOLVED', fn, F.pc(j), '-', 'stack object size unknown']))
                n = scan(Im, label, fld, objs, rowtag, out, osize)
                summary.append((label, rowtag, n))
                for o in objs:
                    if o[0] == 'global': gseen.setdefault((o[1], o[2]), set()).add(fld)
        # data words that point into a scanned global object (the code scan above follows pc-relative and .got
        # references; a pointer kept in other data is listed here, and one that points at a scanned field is UNRESOLVED)
        from elftools.elf.elffile import ELFFile
        e = ELFFile(open(path, 'rb'))
        for sec in e.iter_sections():
            if sec['sh_type'] != 'SHT_PROGBITS' or not (sec['sh_flags'] & 2) or (sec['sh_flags'] & 4): continue
            d = sec.data(); base = sec['sh_addr']
            for k in range(0, len(d) - 7, 8):
                v = int.from_bytes(d[k:k + 8], 'little')
                for (ga, gn), flds in gseen.items():
                    gz = next(z for a, z, t in Im.byname[gn] if t == 'STT_OBJECT')
                    if not (ga <= v < ga + gz): continue
                    off = v - ga
                    if sec.name == '.got' and off == 0: kind, det = 'DATAPTR', '.got cell of the object base (followed by the code scan)'
                    elif off in flds: kind, det = 'UNRESOLVED', 'a data word points at the scanned field'
                    else: kind, det = 'DATAPTR', 'points at +%d, not a scanned field (%s)' % (off, ', '.join('+%d' % f for f in sorted(flds)))
                    out.append('\t'.join([label, 'data', kind, sec.name, '%#x' % (base + k), '-', '%s+%d: %s' % (gn, off, det)]))
    open(_argv[4], 'w').write('image\tescape\tkind\tfunction\tpc\tinstruction\tdetail\n' + '\n'.join(out) + '\n')
    c = collections.Counter((l.split('\t')[0], l.split('\t')[2]) for l in out)
    print('objscan: %s' % ', '.join('%s %s %d' % (k[0], k[1], v) for k, v in sorted(c.items())))

if __name__ == '__main__':
    main()
