#!/usr/bin/env python3
"""luiflow.py -- the dataflow behind each `lui-in-section` row of strictcmp3 (cmpkit 86da41d3ef68) on this record's
closure: for every such target (scans/lui-targets.tsv: member, X address, word, values), in BOTH images, the lui word and
every instruction its value reaches (capstone decode; the function's control flow followed through both arms of every
branch). A value is carried by copies (mv) and by ALU results computed from it (addi / addiw / add / sub / slli / srli /
srai / and(i) / or(i) / xor(i) / mul* / div* / rem*: the derived register is followed, marked with the operation); a
write of any other kind ends it. Each USE is classified:
  ARG <callee> <reg> <param type>  passed to a direct call (tail call: TAILARG); the parameter's C++ type is read from the
                                   callee's mangled name (Itanium: m unsigned long, j unsigned int, i int, y unsigned long long,
                                   P.. pointer, R.. reference, ...); for an unmangled callee: '?'
  INDIRECT-ARG <reg>               passed to an indirect call
  STORE-DATA <base>+<off> w<n>     stored as data
  MEM-BASE <op>                    the base register of a load / store (an address use)
  CMP <op>                         a branch / slt / sltu operand
  RET                              returned in a0
  JUMP                             a jalr / jr target (an address use)
Writes scans/luiflow.tsv (one row per target per image: the lui, the chain, the uses) and prints a per-target summary with
whether the two images give the same uses. usage: luiflow.py"""
import collections, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common, escape

ALU = {'addi', 'addiw', 'add', 'addw', 'sub', 'subw', 'slli', 'slliw', 'srli', 'srliw', 'srai', 'sraiw', 'sll', 'sllw', 'srl',
       'srlw', 'sra', 'sraw', 'and', 'andi', 'or', 'ori', 'xor', 'xori', 'mul', 'mulw', 'mulh', 'mulhu', 'mulhsu', 'div',
       'divu', 'divw', 'divuw', 'rem', 'remu', 'remw', 'remuw', 'sext.w', 'neg', 'negw', 'not', 'zext.b', 'zext.h', 'zext.w'}
CMP = {'slt', 'sltu', 'slti', 'sltiu', 'seqz', 'snez', 'sltz', 'sgtz'} | escape.BR
LD = set(escape.LD) if hasattr(escape, 'LD') else {'lb', 'lbu', 'lh', 'lhu', 'lw', 'lwu', 'ld'}
ST = set(escape.ST)
ARGS = ['a%d' % i for i in range(8)]
CLOB = set(ARGS) | {'ra'} | {'t%d' % i for i in range(7)}
MEMOP = re.compile(r'(-?(?:0x[0-9a-f]+|\d+))?\((\w+)\)\s*$')
BUDGET = 4000


BUILTIN = set('vwbcahstijlmxynofdegz')
NS = {'__sanitizer', '__asan', '__lsan', '__ubsan', '__interception', 'libunwind', 'std', '__cxxabiv1', '__sancov'}


class Demangle:
    """a small recursive parser of the Itanium mangled names in these images: enough to find a function's qualified name,
    whether it is a member (its scope is not a namespace of NS), and its parameter types. Substitutions (S_, S<n>_, St..)
    and template parameters (T_) are kept as opaque tokens."""
    def __init__(self, s):
        self.s = s

    def name(self, i):
        j = i
        while self.s[j].isdigit():
            j += 1
        n = int(self.s[i:j])
        return self.s[j:j + n], j + n

    def targs(self, i):                     # s[i] == 'I'
        i += 1
        while self.s[i] != 'E':
            if self.s[i] == 'L':            # a literal: L <type> <value> E, or L _Z <encoding> E
                j = self.s.index('E', i)
                i = j + 1
            else:
                _, i = self.type(i)
        return i + 1

    def sub(self, i):                       # s[i] == 'S'
        if self.s[i + 1] in 'tabsiod':
            return 'S' + self.s[i + 1], i + 2
        j = self.s.index('_', i)
        return self.s[i:j + 1], j + 1

    def nested(self, i):                    # s[i] == 'N'; returns (components, is_const, last_has_targs, i)
        i += 1
        const = False
        while self.s[i] in 'KVr':
            const = const or self.s[i] == 'K'; i += 1
        comps, last_t = [], False
        while self.s[i] != 'E':
            c = self.s[i]
            if c.isdigit():
                nm, i = self.name(i); comps.append(nm); last_t = False
            elif c == 'S':
                nm, i = self.sub(i); comps.append(nm); last_t = False
            elif c == 'I':
                i = self.targs(i); last_t = True
            elif c in 'CD' and self.s[i + 1] in '0123':
                comps.append(self.s[i:i + 2]); i += 2; last_t = False
            elif c == 'T':
                j = self.s.index('_', i); comps.append(self.s[i:j + 1]); i = j + 1
            elif c == 'L':
                i += 1
            else:
                raise ValueError('nested %r at %d' % (c, i))
        return comps, const, last_t, i + 1

    def type(self, i):
        c = self.s[i]
        if c in 'PROKV':
            t, j = self.type(i + 1)
            return c + t, j
        if c in BUILTIN:
            return c, i + 1
        if c == 'D':
            return 'D' + self.s[i + 1], i + 2
        if c == 'N':
            comps, _, _, j = self.nested(i)
            return 'N' + '::'.join(comps), j
        if c.isdigit():
            nm, j = self.name(i)
            if j < len(self.s) and self.s[j] == 'I':
                j = self.targs(j)
            return nm, j
        if c == 'S':
            nm, j = self.sub(i)
            if j < len(self.s) and self.s[j] == 'I':
                j = self.targs(j)
            return nm, j
        if c == 'T':
            j = self.s.index('_', i)
            return self.s[i:j + 1], j + 1
        if c == 'F':                        # function type F [Y] <ret> <params> E
            j = i + 1
            while self.s[j] != 'E':
                _, j = self.type(j)
            return 'F', j + 1
        if c == 'A':
            j = self.s.index('_', i)
            t, j = self.type(j + 1)
            return 'A' + t, j
        if c == 'M':
            _, j = self.type(i + 1)
            t, j = self.type(j)
            return 'M' + t, j
        raise ValueError('type %r at %d' % (c, i))

    def function(self):
        """(qualified name components, is_member, [parameter type codes]) of a mangled function name"""
        s, i = self.s, 2
        if s[i] == 'N':
            comps, const, last_t, i = self.nested(i)
        else:
            if s[i] == 'L':
                i += 1
            nm, i = self.name(i)
            comps, const, last_t = [nm], False, False
            if i < len(s) and s[i] == 'I':
                i = self.targs(i); last_t = True
        member = const or (len(comps) >= 2 and comps[-2] not in NS and not comps[-2].startswith('S'))
        if len(comps) >= 2 and comps[-2].startswith('S') and comps[-2] not in ('St',):
            member = True                   # a substituted scope in these images is a class (namespaces are spelled out)
        params = []
        if last_t:                          # a function template instance encodes its return type first
            _, i = self.type(i)
        while i < len(s) and s[i] not in '.':
            t, i = self.type(i)
            params.append(t)
        if params == ['v']:
            params = []
        return comps, member, params


def _fn(name):
    try:
        return Demangle(name).function()
    except (ValueError, IndexError):
        return None


def itanium_params(name):
    """the parameter type codes of a mangled function name, or None for an unmangled or unparsed name"""
    if not name.startswith('_Z'):
        return None
    f = _fn(name)
    return f[2] if f else None


def is_member(name):
    f = _fn(name) if name.startswith('_Z') else None
    return bool(f and f[1])


TYPES = {'m': 'unsigned long', 'j': 'unsigned int', 'i': 'int', 'l': 'long', 'y': 'unsigned long long', 'x': 'long long',
         'h': 'unsigned char', 'c': 'char', 'a': 'signed char', 't': 'unsigned short', 's': 'short', 'b': 'bool', 'v': 'void',
         'd': 'double', 'f': 'float', 'z': '...'}


def ptype(callee, reg, this_first):
    """the type of argument register `reg` of `callee`; this_first: the callee is a member (a0 = this)"""
    ps = itanium_params(callee)
    if ps is None:
        return '?'
    k = int(reg[1:]) - (1 if this_first else 0)
    if k < 0:
        return 'this'
    if k >= len(ps):
        return '(variadic / beyond the signature)' if ps and ps[-1] == 'z' else '(beyond the signature)'
    p = ps[k]
    if p[:1] in 'PRO':
        return 'pointer %s' % p
    return TYPES.get(p.lstrip('K'), p)


def flow(img, a, z, word):
    ins = img.dis(a, z)
    at = {o: k for k, (o, m, p, n) in enumerate(ins)}
    k0 = at[word]
    o, mn, op, n = ins[k0]
    rd = op.split(',')[0].strip()
    uses, chain = set(), set()
    seen, work, steps = set(), [(k0 + 1, frozenset({rd}))], 0
    while work:
        k, T = work.pop()
        while 0 <= k < len(ins) and T:
            if (k, T) in seen:
                break
            seen.add((k, T)); steps += 1
            if steps > BUDGET:
                uses.add(('LIMIT',)); return sorted(uses), sorted(chain), mn + ' ' + op
            o, m, p, nb = ins[k]
            ops = [x.strip() for x in p.split(',')] if p else []
            pc = a + o
            reads = [x for x in ops[1:] if x in T] if ops else []
            mm = MEMOP.search(p) if p else None
            if m in ('mv', 'sext.w') and len(ops) == 2:
                if ops[1] in T:
                    chain.add('+%#x %s %s' % (o, m, p)); T = T | {ops[0]}
                else:
                    T = T - {ops[0]}
                k += 1; continue
            if m in ALU and ops:
                if reads:
                    chain.add('+%#x %s %s' % (o, m, p)); T = T | {ops[0]}
                else:
                    T = T - {ops[0]}
                k += 1; continue
            if m in LD:
                if mm and mm.group(2) in T:
                    uses.add(('MEM-BASE', '+%#x %s %s' % (o, m, p)))
                T = T - {ops[0]}
                k += 1; continue
            if m in ST:
                if mm and mm.group(2) in T:
                    uses.add(('MEM-BASE', '+%#x %s %s' % (o, m, p)))
                if ops[0] in T:
                    uses.add(('STORE-DATA', '+%#x %s %s' % (o, m, p)))
                k += 1; continue
            if m in CMP:
                if any(x in T for x in ops):
                    uses.add(('CMP', '+%#x %s %s' % (o, m, p)))
                if m in escape.BR:
                    try:
                        tgt = o + int(ops[-1], 0)
                        if tgt in at:
                            work.append((at[tgt], T))
                    except ValueError:
                        pass
                elif ops:
                    T = T - {ops[0]}
                k += 1; continue
            if m == 'ret':
                if 'a0' in T:
                    uses.add(('RET',))
                break
            if m in ('j', 'jal', 'jr', 'jalr'):
                tgt = img.wtarget.get(pc) if img._callers is not None else None
                if tgt is None and m in ('j', 'jal'):
                    tgt = pc + int(ops[-1], 0)
                is_call = (m == 'jal' and (len(ops) == 1 or ops[0] == 'ra')) or (m == 'jalr' and (len(ops) == 1 or ops[0] == 'ra' or '(' in p))
                if m in ('jr', 'jalr') and any(x in T for x in re.findall(r'\w+', p) if x not in ('ra', 'zero')):
                    base = (re.findall(r'\((\w+)\)', p) or [ops[-1]])[0]
                    if base in T:
                        uses.add(('JUMP', '+%#x %s %s' % (o, m, p)))
                if not is_call and m == 'j' and a <= tgt < a + z and (tgt - a) in at:
                    k = at[tgt - a]; continue
                if not is_call and m in ('jr',) and img.cases.get(a):
                    for c in img.cases[a]:
                        if c in at:
                            work.append((at[c], T))
                    break
                name = img.name_at(tgt) if tgt is not None else None
                this_first = bool(name and is_member(name))
                for r in sorted(T & set(ARGS)):
                    if name and tgt in img.starts:
                        ty = ptype(name, r, this_first)
                        uses.add(('ARG' if is_call else 'TAILARG', name, r, ty))
                    else:
                        uses.add(('INDIRECT-ARG', r))
                if not is_call:
                    break
                T = T - CLOB
                k += 1; continue
            if ops and ops[0] in T and m not in ST:
                T = T - {ops[0]}
            k += 1
    return sorted(uses), sorted(chain), mn + ' ' + op


def main():
    X, Y = escape.Image(common.CGIF_B_TWIN), escape.Image(common.DECODE_B_TWIN)
    X._index(); Y._index()
    tg = [l.rstrip('\n').split('\t') for l in list(open(os.path.join(common.HERE, 'scans', 'lui-targets.tsv')))[1:]]
    fd = {}
    for l in list(open(os.path.join(common.HERE, 'scans', 'exposure.tsv')))[1:]:
        c = l.rstrip('\n').split('\t')
        fd[int(c[1], 16)] = (int(c[2], 16), int(c[3]))
    out, nsame = [], 0
    for member, ax, word, vals in tg:
        ax, w = int(ax, 16), int(word, 16)
        ay, z = fd[ax]
        ux, cx, lx = flow(X, ax, z, w)
        uy, cy, ly = flow(Y, ay, z, w)
        norm = lambda us: sorted(re.sub(r'\+0x[0-9a-f]+ ', '', ' | '.join(str(x) for x in u)) for u in us)
        same = norm(ux) == norm(uy)
        nsame += same
        out.append((member, '%#x' % ax, '%#x' % ay, word, vals, lx, ' ; '.join(cx) or '-',
                    ' ; '.join(' '.join(str(x) for x in u) for u in ux) or 'none', 'same' if same else
                    'DIFFER: ' + ' ; '.join(' '.join(str(x) for x in u) for u in uy)))
    with open(os.path.join(common.HERE, 'scans', 'luiflow.tsv'), 'w') as f:
        f.write('member\tX addr\tY addr\tword\tvalues (X | Y)\tlui word\tchain (copies, derived values)\tUSES in X\tuses in Y\n')
        for r in out:
            f.write('\t'.join(r) + '\n')
    print('lui-in-section targets %d; uses identical in both images: %d' % (len(out), nsame))
    kinds = collections.Counter()
    for r in out:
        for u in r[7].split(' ; '):
            kinds[u.split(' ')[0]] += 1
    print('use kinds:', dict(kinds))


if __name__ == '__main__':
    main()
