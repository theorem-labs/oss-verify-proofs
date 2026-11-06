#!/usr/bin/env python3
"""luirows.py -- rule-8 (lui) exposure of one record made on cmpkit 4bbd3a74be89, and the re-run of every exposed
function on cmpkit 86da41d3ef68 (strictcmp3.tcmp, by address), with the dataflow of every lui-in-section value.
Read-only. Loads strictcmp3.py from its own directory.

1. COMPARED SET: the functions reached in X from the roots through any pc-relative target or .got cell that is the start
   of a sized FUNC symbol (calls and address-taking, transitively). This is a superset of the by-name closure and of
   paircl's target-paired closure. Each member's Y copy: the root by name; any other member at the same word of Y's
   counterpart of an X function that reaches it (the code decides which copy, as dupcheck.py does).
2. EXPOSED: a member whose luiscan exposure (LUISCAN_TSV, `luiscan.py --all X Y`) is > 0 in X or in its Y copy.
3. RERUN: strictcmp3.tcmp on (X copy, Y copy), both by address: the combined verdict and every differing target.
4. For each `lui-in-section` target, strictcmp3's own forward MAY dataflow (lui_scan's), re-run here to keep the states,
   lists every use of the lui value, or of the pair it forms, in X and in Y: USE rows with the word, the instruction and
   the class (operand of an R-type op / a branch compare / a call argument / left at a return / stored as data /
   a memory or jump base). A memory or jump base is an address use (luiscan's memfed); the other uses are listed for
   the hand argument that the value is not an address.
usage: luirows.py X_ELF Y_ELF LUISCAN_TSV ROOT1,ROOT2,...
Output TSV: MEMBERS, EXPOSED, RERUN, TARGET and USE rows, then TOTAL."""
import collections, importlib.util, inspect, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('strictcmp3', os.path.join(HERE, 'strictcmp3.py'))
s3 = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(s3)
RN = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
      's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']

# lui_scan, re-run with its dataflow states kept (its own text, with the states returned too)
_src = inspect.getsource(s3.lui_scan).replace('def lui_scan(', 'def lui_states(')
_src = _src.replace("    return {k: tuple(v) for k, v in tg.items()}, set()\n",
                    "    return {k: tuple(v) for k, v in tg.items()}, set(), ins, w\n")
_src = _src.replace("    if not lui: return {}, set()\n", "    if not lui: return {}, set(), None, w\n")
_src = _src.replace("    if any(n == 2 for o, x, n in w): return {}, set(lui)\n",
                    "    if any(n == 2 for o, x, n in w): return {}, set(lui), None, w\n")
assert _src.count('set(), ins, w') == 1 and _src.count('None, w') == 2
exec(compile(_src, 'lui_states', 'exec'), s3.__dict__)
lui_states = s3.__dict__['lui_states']

def sxv(v, b): return v - (1 << b) if v & (1 << (b - 1)) else v
def text(x, o):
    op = x & 0x7f; rd = (x >> 7) & 31; f3 = (x >> 12) & 7; r1 = (x >> 15) & 31; r2 = (x >> 20) & 31; f7 = x >> 25
    if op == 0x37: return 'lui %s,%#x' % (RN[rd], (x >> 12) & 0xfffff)
    if op in (0x13, 0x1b):
        m = (['addi', 'slli', 'slti', 'sltiu', 'xori', 'srli', 'ori', 'andi'] if op == 0x13 else
             ['addiw', 'slliw', '?', '?', '?', 'srliw', '?', '?'])[f3]
        if f3 == 5 and (x >> 30) & 1: m = 'srai' if op == 0x13 else 'sraiw'
        return '%s %s,%s,%d' % (m, RN[rd], RN[r1], sxv(x >> 20, 12) if f3 not in (1, 5) else (x >> 20) & 63)
    if op in (0x33, 0x3b):
        if f7 == 1: m = ['mul', 'mulh', 'mulhsu', 'mulhu', 'div', 'divu', 'rem', 'remu'][f3]
        else: m = {0: 'sub' if f7 == 0x20 else 'add', 1: 'sll', 2: 'slt', 3: 'sltu', 4: 'xor', 5: 'sra' if f7 == 0x20 else 'srl',
                   6: 'or', 7: 'and'}[f3]
        return '%s%s %s,%s,%s' % (m, 'w' if op == 0x3b else '', RN[rd], RN[r1], RN[r2])
    if op == 0x03: return '%s %s,%d(%s)' % (['lb', 'lh', 'lw', 'ld', 'lbu', 'lhu', 'lwu', '?'][f3], RN[rd], sxv(x >> 20, 12), RN[r1])
    if op == 0x23:
        return '%s %s,%d(%s)' % (['sb', 'sh', 'sw', 'sd', '?', '?', '?', '?'][f3], RN[r2],
                                 sxv(((x >> 25) << 5) | ((x >> 7) & 31), 12), RN[r1])
    if op == 0x63:
        t = sxv(((x >> 31) & 1) << 12 | ((x >> 7) & 1) << 11 | ((x >> 25) & 0x3f) << 5 | ((x >> 8) & 0xf) << 1, 13)
        return '%s %s,%s -> +%#x' % (['beq', 'bne', '?', '?', 'blt', 'bge', 'bltu', 'bgeu'][f3], RN[r1], RN[r2], o + t)
    if op == 0x67: return 'jalr %s,%d(%s)' % (RN[rd], sxv(x >> 20, 12), RN[r1])
    if op == 0x6f: return 'jal %s' % RN[rd]
    return 'op%#x' % op

def uses_of(I, a, z):
    """{(kind, k, j): [(use word, register, class)]} for every lui value ('L', j) and pair result ('P', k, j)"""
    b = s3.frd(I, a, z); tg, unm, ins, w = lui_states(b)
    out = collections.defaultdict(list)
    if ins is None: return tg, out, w
    for k, (o, x, n) in enumerate(w):
        s = ins[k]
        if s is None: continue
        op = x & 0x7f; rd = (x >> 7) & 31; rs1 = (x >> 15) & 31
        imm = s3._lo12(x); mv = op == 0x13 and (x >> 12) & 7 == 0 and x >> 20 == 0
        if imm is not None and rs1 and not mv:
            for t in s.get(rs1, ()):
                if t[0] == 'L': out[('L', t[1])].append((k, rs1, 'pair (forms the value of TARGET %s)' % hex(o)))
                else: out[t].append((k, rs1, 'memory or jump base' if op in s3.LUI_MEM else 'operand of an I-type op'))
        if mv and rs1 in s: continue
        reads = list(s3._raw_reads(x)); why = {}
        if s3._isret(x): reads += [10, 11]; why = {10: 'left in a0 at a return', 11: 'left in a1 at a return'}
        elif op == 0x67 or (op == 0x6f and (rd or not 0 <= o + s3._jal_off(x) < len(b))):
            dest = s3.qres(I, a + o + s3._jal_off(x))[:-4] if op == 0x6f else '(register-indirect)'
            for r in s3.ARGS: why[r] = 'argument a%d of a call to %s' % (r - 10, dest)
            reads += s3.ARGS
        for r in reads:
            for t in s.get(r, ()):
                if r in why: c = why[r]
                elif op == 0x63: c = 'operand of a branch compare'
                elif op in (0x23, 0x27): c = 'stored as data' if r == ((x >> 20) & 31) else 'memory base'
                elif op in (0x33, 0x3b): c = 'operand of an R-type op'
                elif op == 0x2f: c = 'AMO'
                else: c = 'read by op%#x' % op
                out[t].append((k, r, c))
    return tg, out, w

def preds_of(w):
    pr = collections.defaultdict(list)
    for i, ss in enumerate(s3._succ(w)):
        for t in ss: pr[t].append(i)
    return pr

def origin(I, a, w, tg_pc, pr, k, reg, depth=0, seen=None):
    """what reg holds at word k, by reaching definitions: a set of short descriptions"""
    seen = seen if seen is not None else set()
    out = set(); work = list(pr[k]); vis = set()
    if k == 0 and not pr[k]: work = []; out.add('parameter %s' % RN[reg]) if 10 <= reg <= 17 else out.add('entry %s' % RN[reg])
    while work:
        j = work.pop()
        if j in vis: continue
        vis.add(j)
        o, x, n = w[j]; op = x & 0x7f; rd = (x >> 7) & 31; r1 = (x >> 15) & 31
        if op in (0x6f, 0x67) and rd and reg in s3._bc['CALLER_SAVED']:
            out.add('return of %s' % (s3.qres(I, a + o + s3._jal_off(x)) or '?')[:-4] if op == 0x6f and reg == 10 else
                    'clobbered by a call'); continue
        if s3._writes(x) == reg and reg:
            if j in tg_pc:
                t = tg_pc[j]
                if I.sec(t) == '.got':
                    c = s3.frd(I, t, 8); v = int.from_bytes(c, 'little') if c else 0
                    out.add('address of %s (from the .got)' % s3.qres(I, v))
                else: out.add('address of %s' % s3.qres(I, t))
            elif op == 0x37: out.add('a lui constant %#x' % ((sxv(x >> 12, 20) << 12) & 0xffffffffffffffff))
            elif op == 0x13 and (x >> 12) & 7 == 0 and r1 == 2: out.add('a stack address')
            elif op in (0x13, 0x1b) and (x >> 12) & 7 == 0 and r1 and depth < 6 and (j, r1) not in seen:
                seen.add((j, r1)); out |= {o2 if o2.startswith(('address', 'a stack', 'parameter')) else o2
                                         for o2 in origin(I, a, w, tg_pc, pr, j, r1, depth + 1, seen)}
            elif op == 0x13 and (x >> 12) & 7 == 0 and not r1: out.add('the constant %d' % sxv(x >> 20, 12))
            elif op == 0x03: out.add('a value loaded by `%s` at +%#x' % (text(x, o), o))
            else: out.add('computed by `%s` at +%#x' % (text(x, o), o))
            continue
        if not pr[j]:
            out.add('parameter %s' % RN[reg] if 10 <= reg <= 17 else 'entry %s' % RN[reg])
        work += pr[j]
    return out

def dwarf_index(path):
    """low_pc -> (name, [(param name, type, artificial)], return type, variadic) from the DWARF of an unstripped image"""
    from elftools.elf.elffile import ELFFile
    def tstr(die, d=0):
        if die is None or d > 8: return 'void'
        t = die.tag; nm = die.attributes.get('DW_AT_name'); nm = nm.value.decode() if nm else None
        sub = die.get_DIE_from_attribute('DW_AT_type') if 'DW_AT_type' in die.attributes else None
        if t == 'DW_TAG_pointer_type': return tstr(sub, d + 1) + ' *'
        if t in ('DW_TAG_reference_type', 'DW_TAG_rvalue_reference_type'): return tstr(sub, d + 1) + ' &'
        if t in ('DW_TAG_const_type', 'DW_TAG_volatile_type', 'DW_TAG_restrict_type', 'DW_TAG_atomic_type'):
            return tstr(sub, d + 1)
        if t == 'DW_TAG_typedef': return (nm or '?') + '=' + tstr(sub, d + 1)
        if t == 'DW_TAG_base_type': return nm or '?'
        if t == 'DW_TAG_enumeration_type': return 'enum ' + (nm or '?')
        if t in ('DW_TAG_structure_type', 'DW_TAG_class_type', 'DW_TAG_union_type'): return 'struct ' + (nm or '?')
        if t == 'DW_TAG_array_type': return tstr(sub, d + 1) + ' []'
        return t
    out = {}
    di = ELFFile(open(path, 'rb')).get_dwarf_info()
    for cu in di.iter_CUs():
        for die in cu.iter_DIEs():
            if die.tag != 'DW_TAG_subprogram' or 'DW_AT_low_pc' not in die.attributes: continue
            spec = die
            for at in ('DW_AT_specification', 'DW_AT_abstract_origin'):
                if at in spec.attributes: spec = spec.get_DIE_from_attribute(at)
            if 'DW_AT_specification' in spec.attributes: spec = spec.get_DIE_from_attribute('DW_AT_specification')
            ps = []; var = False
            src = die if any(c.tag == 'DW_TAG_formal_parameter' for c in die.iter_children()) else spec
            for c in src.iter_children():
                if c.tag == 'DW_TAG_formal_parameter':
                    cc = c.get_DIE_from_attribute('DW_AT_abstract_origin') if 'DW_AT_abstract_origin' in c.attributes else c
                    nm = cc.attributes.get('DW_AT_name')
                    ps.append((nm.value.decode() if nm else None,
                               tstr(cc.get_DIE_from_attribute('DW_AT_type')) if 'DW_AT_type' in cc.attributes else '?',
                               bool(cc.attributes.get('DW_AT_artificial'))))
                elif c.tag == 'DW_TAG_unspecified_parameters': var = True
            rt = tstr(spec.get_DIE_from_attribute('DW_AT_type')) if 'DW_AT_type' in spec.attributes else 'void'
            nm = spec.attributes.get('DW_AT_linkage_name') or spec.attributes.get('DW_AT_name')
            out[die.attributes['DW_AT_low_pc'].value] = (nm.value.decode() if nm else None, ps, rt, var)
    return out

def is_ptr(t): return t.endswith(' *') or t.endswith(' &') or t.endswith(' []') or t.endswith('=uptr') or 'uintptr' in t

ANCHOR = ('address of', 'a stack address')

def taint(I, a, z, w, start, reg):
    """forward MAY dataflow of the value reg holds after word start, through every arithmetic result derived from it;
    events [(word, kind, detail, anchored)]: kind base (memory / jump base), store (data, with width), arg (call
    argument), ret, syscall, cmp, arith, amo; `anchored` when an add / sub combined the value with a pointer operand
    (an address formed by auipc or the .got, or a stack address): the value is then an offset into that object"""
    b = s3.frd(I, a, z); tpc = {i: t for i, (kd, t) in s3.targets(a, b).items()}; pr = preds_of(w); succ = s3._succ(w)
    CS = s3._bc['CALLER_SAVED']
    ins = collections.defaultdict(dict); ev = set(); work = []
    st0 = {reg: frozenset({False})}
    for t in succ[start]: ins[t] = dict(st0); work.append(t)
    jr = [i for i, (o, x, n) in enumerate(w) if x & 0x7f == 0x67 and (x >> 7) & 31 == 0 and not s3._isret(x)]
    roots = sorted(set(range(1, len(w))) - {t for ss in succ for t in ss})
    def anchor_of(k, r):
        org = origin(I, a, w, tpc, pr, k, r)
        return any(o.startswith(ANCHOR) for o in org), org
    while True:
        while work:
            i = work.pop(); S = ins[i]; o, x, n = w[i]
            op = x & 0x7f; rd = (x >> 7) & 31; r1 = (x >> 15) & 31; r2 = (x >> 20) & 31; f3 = (x >> 12) & 7; f7 = x >> 25
            out = dict(S); T = lambda r: S.get(r, frozenset())
            if op in (0x03, 0x07) and r1 in S: ev.add((i, 'base', text(x, o), any(T(r1))))
            if op in (0x23, 0x27):
                if r1 in S: ev.add((i, 'base', text(x, o), any(T(r1))))
                if r2 in S: ev.add((i, 'store', '%s (%d-byte store)' % (text(x, o), 1 << (f3 & 3)), any(T(r2))))
            if op == 0x2f:
                if r1 in S: ev.add((i, 'base', 'AMO address', any(T(r1))))
                if r2 in S: ev.add((i, 'amo', 'AMO data operand', any(T(r2))))
            if op == 0x63 and (r1 in S or r2 in S): ev.add((i, 'cmp', text(x, o), False))
            if op in (0x33, 0x3b) and (r1 in S or r2 in S):
                m = text(x, o).split(' ')[0]; anc = any(T(r1)) or any(T(r2))
                if m.rstrip('w') in ('add', 'sub') and not anc:
                    other = r2 if r1 in S else r1
                    if other and other not in S:
                        ok, org = anchor_of(i, other); anc = ok
                        ev.add((i, 'arith', '%s; other operand %s: %s' % (text(x, o), RN[other], '; '.join(sorted(org))), anc))
                    else: ev.add((i, 'arith', text(x, o), anc))
                else: ev.add((i, 'arith', text(x, o), anc))
                if rd: out[rd] = frozenset({anc})
            elif op in (0x13, 0x1b) and r1 in S:
                if rd: out[rd] = T(r1)
                if not (f3 == 0 and (x >> 20) == 0): ev.add((i, 'arith', text(x, o), any(T(r1))))
            elif op == 0x73 and f3 == 0:
                for r in s3.ARGS:
                    if r in S: ev.add((i, 'syscall', 'a%d live at an ecall' % (r - 10), any(T(r))))
            elif op == 0x67 and s3._isret(x):
                for r in (10, 11):
                    if r in S: ev.add((i, 'ret', 'a%d at a return' % (r - 10), any(T(r))))
            elif (op == 0x6f and (rd or not 0 <= o + s3._jal_off(x) < len(b))) or (op == 0x67 and rd):
                dest = (s3.qres(I, a + o + s3._jal_off(x)) or '?')[:-4] if op == 0x6f else '(register-indirect)'
                if op == 0x67 and r1 in S: ev.add((i, 'base', 'jump base', any(T(r1))))
                for r in s3.ARGS:
                    if r in S: ev.add((i, 'arg', '%s a%d' % (dest, r - 10), any(T(r))))
            elif op == 0x67 and r1 in S: ev.add((i, 'base', 'jump base', any(T(r1))))
            if op not in (0x13, 0x1b, 0x33, 0x3b) or not (r1 in S or r2 in S):
                wr = s3._writes(x)
                if wr: out.pop(wr, None)
            if op in (0x6f, 0x67) and rd:
                for r in CS: out.pop(r, None)
            if op == 0x73 and f3 == 0: out.pop(10, None); out.pop(11, None)
            out.pop(0, None)
            for t in succ[i]:
                new = {r: ins[t].get(r, frozenset()) | out.get(r, frozenset()) for r in ins[t].keys() | out.keys()}
                if new != ins[t] or t not in ins: ins[t] = new; work.append(t)
        u = {}
        for i in jr:
            if i in ins:
                for r, v in ins[i].items(): u[r] = u.get(r, frozenset()) | v
        changed = False
        for t in roots:
            new = {r: ins[t].get(r, frozenset()) | u.get(r, frozenset()) for r in ins[t].keys() | u.keys()}
            if u and new != ins.get(t): ins[t] = new; work.append(t); changed = True
        if not changed: break
    return sorted(ev)

def main():
    xp, yp, lp, roots = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4].split(',')
    X, Y = s3.Img(xp), s3.Img(yp); I = {'X': X, 'Y': Y}
    expo = {}
    for l in open(lp):
        f = l.rstrip('\n').split('\t')
        if f[0] == 'ROW' and f[1] != 'image': expo[(f[1], int(f[3], 16))] = int(f[12])
    tx, ty = os.path.basename(xp), os.path.basename(yp)
    def starts(Im):
        st = {}
        for v, z, n, t in Im.syms:
            if t == 'STT_FUNC' and z > 0: st.setdefault(v, []).append((n, z))
        return st
    SX, SY = starts(X), starts(Y)
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
        if len(cx) != 1 or len(cy) != 1: raise SystemExit('root %s: %d / %d copies' % (r, len(cx), len(cy)))
        yof[cx[0][0]] = cy[0][0]; seen.add(cx[0][0]); work.append(cx[0][0])
    while work:
        a = work.pop(); z = SX[a][0][1]; ya = yof.get(a)
        ry = refs(Y, SY, ya, z) if ya is not None and SY.get(ya, [(None, -1)])[0][1] == z else {}
        for i, t in refs(X, SX, a, z).items():
            if t not in yof and i in ry: yof[t] = ry[i]
            if t not in seen: seen.add(t); work.append(t)
    print('#\tX %s sha256 %s\tY %s sha256 %s\troots %s' % (tx, s3.sha(xp)[:12], ty, s3.sha(yp)[:12], ','.join(roots)))
    nmiss = sum(1 for a in seen if a not in yof)
    print('MEMBERS\t%d functions reached in X (calls and address-taking)\t%d with a Y copy by the code\t%d without' % (
        len(seen), len(seen) - nmiss, nmiss))
    tot = collections.Counter()
    for a in sorted(seen):
        nx, zx = sorted(SX[a])[0]; ya = yof.get(a)
        ex = expo.get((tx, a), 0); ey = expo.get((ty, ya), 0) if ya is not None else 0
        if ya is None:
            # no Y copy by the code (an address-taken function only): pair it by its unique qualified name
            c = s3.fcopies(Y, s3.qname(X, nx, a) or nx)
            if len(c) == 1: ya = c[0][0]; ey = expo.get((ty, ya), 0)
        if not (ex or ey): continue
        tot['exposed'] += 1
        qx = s3.qname(X, nx, a) or nx
        print('EXPOSED\t%s\tX %#x size %d exposure %d\tY %s exposure %d' % (qx, a, zx, ex, '%#x' % ya if ya else 'none', ey))
        if ya is None: tot['no-y'] += 1; continue
        v, c, cnt, diff = s3.tcmp(I, 'X', a, 'Y', ya, zx)
        vd = s3.verdict(v, diff)
        kinds = collections.Counter(d[3] for d in diff)
        print('RERUN\t%s\t%s\twords-only %s\tdiffering targets %d\t%s' % (qx, vd, v, len(diff),
              ', '.join('%s %d' % kv for kv in sorted(kinds.items())) or '-'))
        tot['rerun ' + vd] += 1
        if not any(d[3] == 'lui-in-section' for d in diff): continue
        tgx, ux, wx = uses_of(X, a, zx); tgy, uy, wy = uses_of(Y, ya, zx)
        for o, r1, r2, kind, info in diff:
            if kind != 'lui-in-section': continue
            tot['lui-in-section'] += 1
            k = next(i for i, (oo, x, n) in enumerate(wx) if oo == int(o, 16))
            keys = [kj for kj in tgx if kj[0] == k]
            for kk, j in keys:
                e = tgx[(kk, j)]
                print('TARGET\t%s\t%s\tlui at +%#x `%s`\t%s %#x\t%s\t%s | %s' % (
                    qx, o, wx[j][0], text(wx[j][1], wx[j][0]), e[0], e[1], info[0], r1, r2))
                val = ('L', j) if e[0] == 'luiv' else ('P', kk, j)
                for tag, U, w in (('X', ux, wx), ('Y', uy, wy)):
                    Im, aa = (X, a) if tag == 'X' else (Y, ya)
                    bb = s3.frd(Im, aa, zx); tpc = {i: t for i, (kd, t) in s3.targets(aa, bb).items()}; pr = preds_of(w)
                    for q, r, cl in sorted(set(U.get(val, []))):
                        xq = w[q][1]; extra = ''
                        if cl == 'operand of an R-type op':
                            other = (xq >> 20) & 31 if ((xq >> 15) & 31) == r else (xq >> 15) & 31
                            extra = 'other operand %s: %s' % (RN[other], '; '.join(sorted(origin(Im, aa, w, tpc, pr, q, other))))
                        print('USE\t%s\t%s\t%s\t+%#x `%s`\t%s\t%s\t%s' % (qx, o, tag, w[q][0], text(xq, w[q][0]), RN[r], cl, extra))
                        tot['use ' + cl.split(' (')[0].split(' a')[0].split(' of a call')[0]] += 0
                    if val[0] == 'P':
                        pass
                ux_s = sorted({(q, cl) for q, r, cl in ux.get(val, [])}); uy_s = sorted({(q, cl) for q, r, cl in uy.get(val, [])})
                print('USES-XY\t%s\t%s\t%s' % (qx, o, 'same in X and Y' if ux_s == uy_s else 'DIFFER between X and Y'))
                st = kk if e[0] != 'luiv' else j
                for tag, Im, aa, w in (('X', X, a, wx), ('Y', Y, ya, wy)):
                    rr = (w[st][1] >> 7) & 31
                    for q, kd, det, anc in taint(Im, aa, zx, w, st, rr):
                        print('EVENT\t%s\t%s\t%s\t+%#x\t%s\t%s\t%s' % (qx, o, tag, w[q][0], kd, 'offset into an anchored object' if anc else '-', det))
    print('TOTAL\t%s' % '\t'.join('%s %d' % kv for kv in sorted(tot.items())))

if __name__ == '__main__':
    main()
