#!/usr/bin/env python3
"""vterm.py -- parse the start-up state files (A/AB01.v, A/AB03.v and their B twins) and give EVERY numeral its role.

The files are lists of `Definition NAME : TYPE := TERM.` whose terms are built from the constructors of
Reusable/YK0c.v (expr, saddr, kentry), Reusable/YK09.v (amap, acs, afd) and the `seg` helper of the file itself.
The parser reads the comment-stripped text token by token, so each numeral keeps the line number a reader sees
(comments are blanked character by character, newlines kept, as the gate does).

numerals(text) -> (nums, defs)
  nums: one dict per numeral: line, value, kind (hex/dec), sent (definition name), role, slot, ctx
    role  the constructor argument or record field the numeral fills, e.g. `SS.pc`, `EVar`, `ELit`, `KWord.w`,
          `KImg.lo`, `a_off`, `seg.i`, `a_totsz` (see ARGROLE)
    slot  for an `ELit`, where the literal sits: the enclosing field/argument chain, innermost operator last
          (e.g. `reg1`, `KWord.v`, `am_len`, `vis.base/EAlu.ALU_ADD.b`)
    ctx   the information the rules need: the a_base of an a_off, the KWord width, the enclosing definition
  defs: {name: AST} of every Definition
"""
import re

TOK = re.compile(r"0x[0-9a-fA-F]+|\d+|[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*|\{\||\|\}|:=|\+\+|\S")

# constructor -> roles of its NUMERAL arguments by position (an argument that is a term gets no role)
ARGROLE = {
    'ELit': {0: 'ELit'}, 'EVar': {0: 'EVar'},
    'EExt': {1: 'EExt.lo', 2: 'EExt.n'}, 'EBlob': {1: 'EBlob.k', 2: 'EBlob.i', 3: 'EBlob.n'},
    'KWord': {1: 'KWord.w'}, 'KBlob': {2: 'KBlob.k'}, 'KImg': {0: 'KImg.lo', 1: 'KImg.hi'},
    'KAlign': {1: 'KAlign.m'}, 'KRange': {1: 'KRange.lo', 2: 'KRange.hi'}, 'KFill': {2: 'KFill.c'},
    'SS': {0: 'SS.pc', 4: 'SS.next'}, 'seg': {1: 'seg.i', 2: 'seg.n'},
    'FdFile': {0: 'FdFile.k'},
}
# constructor -> names of its TERM arguments by position (used to build ELit slots)
ARGNAME = {
    'KWord': {0: 'KWord.a', 2: 'KWord.v'}, 'KZero': {0: 'KZero.a', 1: 'KZero.n'},
    'KBlob': {0: 'KBlob.a', 1: 'KBlob.n'}, 'KAlign': {0: 'KAlign.e'}, 'KRange': {0: 'KRange.e'},
    'KWr': {0: 'KWr.a', 1: 'KWr.n'}, 'KDisj': {0: 'KDisj.a1', 1: 'KDisj.n1', 2: 'KDisj.a2', 3: 'KDisj.n2'},
    'KFill': {0: 'KFill.a', 1: 'KFill.n'}, 'KUnk': {0: 'KUnk.a', 1: 'KUnk.n'},
    'SS': {1: 'regs', 2: 'log', 3: 'kn'}, 'FdFile': {1: 'FdFile.len', 2: 'FdFile.off'},
    'EExt': {3: 'EExt.e'},
}
NUMFIELD = {'a_off', 'a_totsz', 'a_ylo', 'a_eager', 'a_abytes'}


def strip_comments(s):
    """Blank Coq comments (nested) and strings character by character, keeping newlines."""
    out, i, n, depth = [], 0, len(s), 0
    buf = list(s)
    while i < n:
        if depth == 0 and s[i] == '"':
            j = s.index('"', i + 1)
            for k in range(i, j + 1):
                if buf[k] != '\n':
                    buf[k] = ' '
            i = j + 1
            continue
        if s.startswith('(*', i):
            depth += 1
            buf[i] = buf[i + 1] = ' '
            i += 2
            continue
        if depth and s.startswith('*)', i):
            depth -= 1
            buf[i] = buf[i + 1] = ' '
            i += 2
            continue
        if depth and buf[i] != '\n':
            buf[i] = ' '
        i += 1
    return ''.join(buf)


class Tok:
    __slots__ = ('t', 'line', 'pos')

    def __init__(self, t, line, pos):
        self.t, self.line, self.pos = t, line, pos


def tokenize(text):
    c = strip_comments(text)
    toks, line, last = [], 1, 0
    for m in TOK.finditer(c):
        line += c.count('\n', last, m.start())
        last = m.start()
        toks.append(Tok(m.group(0), line, m.start()))
    return toks


def is_num(t):
    return t[0].isdigit()


def numval(t):
    return int(t, 16) if t.startswith('0x') else int(t)


class P:
    """Recursive-descent parser of one sentence's term. AST nodes are tuples:
    ('num', value, tok, neg) ('id', name) ('app', headname, [args]) ('list', [items]) ('tuple', [items])
    ('rec', [(field, term)]) ('cat', [terms]) ('paren', term)"""
    STOP = {')', ']', '|}', ';', ',', '++', '.', ':='}

    def __init__(self, toks):
        self.toks, self.i = toks, 0

    def peek(self, k=0):
        j = self.i + k
        return self.toks[j].t if j < len(self.toks) else None

    def take(self, want=None):
        t = self.toks[self.i]
        if want is not None and t.t != want:
            raise SyntaxError(f'line {t.line}: expected {want!r}, got {t.t!r}')
        self.i += 1
        return t

    def term(self):
        items = [self.app()]
        while self.peek() == '++':
            self.take()
            items.append(self.app())
        return items[0] if len(items) == 1 else ('cat', items)

    def app(self):
        atoms = []
        while self.peek() is not None and self.peek() not in self.STOP:
            atoms.append(self.atom())
        if not atoms:
            raise SyntaxError(f'line {self.toks[self.i].line}: empty term at {self.peek()!r}')
        if len(atoms) == 1:
            return atoms[0]
        if atoms[0][0] != 'id':
            raise SyntaxError(f'application of a non-identifier at line {self.toks[self.i - 1].line}')
        return ('app', atoms[0][1], atoms[1:])

    def atom(self):
        t = self.take()
        if is_num(t.t):
            return ('num', numval(t.t), t, False)
        if t.t == '-' and self.peek() and is_num(self.peek()):
            n = self.take()
            return ('num', -numval(n.t), n, True)
        if t.t[0].isalpha() or t.t[0] == '_':
            return ('id', t.t)
        if t.t == '(':
            if self.peek() == '-' and self.peek(1) and is_num(self.peek(1)) and self.peek(2) == ')':
                self.take('-')
                n = self.take()
                self.take(')')
                return ('num', -numval(n.t), n, True)
            first = self.term()
            if self.peek() == ',':
                items = [first]
                while self.peek() == ',':
                    self.take()
                    items.append(self.term())
                self.take(')')
                return ('tuple', items)
            self.take(')')
            return ('paren', first)
        if t.t == '[':
            items = []
            if self.peek() == ']':
                self.take()
                return ('list', items)
            items.append(self.term())
            while self.peek() == ';':
                self.take()
                items.append(self.term())
            self.take(']')
            return ('list', items)
        if t.t == '{|':
            fields = []
            while True:
                f = self.take().t
                self.take(':=')
                fields.append((f, self.term()))
                if self.peek() == ';':
                    self.take()
                    continue
                self.take('|}')
                return ('rec', fields)
        raise SyntaxError(f'line {t.line}: unexpected token {t.t!r}')


def unparen(x):
    while x[0] == 'paren':
        x = x[1]
    return x


def show(x, lim=160):
    """Compact Coq text of a term (for measurements)."""
    def s(x):
        k = x[0]
        if k == 'num':
            return f'({x[1]})' if x[3] else str(x[1])
        if k == 'id':
            return x[1]
        if k == 'paren':
            return '(' + s(x[1]) + ')'
        if k == 'app':
            return x[1] + ' ' + ' '.join(('(' + s(a) + ')') if a[0] == 'app' else s(a) for a in x[2])
        if k == 'list':
            return '[' + '; '.join(s(i) for i in x[1]) + ']'
        if k == 'tuple':
            return '(' + ', '.join(s(i) for i in x[1]) + ')'
        if k == 'rec':
            return '{| ' + '; '.join(f'{f} := {s(v)}' for f, v in x[1]) + ' |}'
        if k == 'cat':
            return ' ++ '.join(s(i) for i in x[1])
        return '?'
    r = s(x)
    return r if len(r) <= lim else r[:lim - 3] + '...'


def sentences(toks):
    """[(name, [tokens of the term after :=], all tokens)] -- a sentence ends at a '.' token."""
    out, cur = [], []
    for t in toks:
        if t.t == '.':
            out.append(cur)
            cur = []
        else:
            cur.append(t)
    if cur:
        out.append(cur)
    return out


def numerals(text):
    toks = tokenize(text)
    nums, defs, order = [], {}, []
    for st in sentences(toks):
        if not st:
            continue
        if st[0].t == 'Definition':
            name = st[1].t
            k = next(i for i, t in enumerate(st) if t.t == ':=')
            ast = P(st[k + 1:]).term()
            defs[name] = ast
            order.append(name)
            # numerals before := (binders such as `(i n : Z)` hold none in these files)
            for t in st[:k]:
                if is_num(t.t):
                    nums.append(dict(line=t.line, value=numval(t.t), kind='hex' if t.t.startswith('0x') else 'dec',
                                     sent=name, role='decl-head', slot='', ctx={}, pos=t.pos))
            walk(ast, name, [], nums, {})
        else:
            for t in st:
                if is_num(t.t):
                    nums.append(dict(line=t.line, value=numval(t.t), kind='hex' if t.t.startswith('0x') else 'dec',
                                     sent=' '.join(x.t for x in st[:3]), role='vernac', slot='', ctx={},
                                     pos=t.pos, text=' '.join(x.t for x in st)))
    return nums, defs, order


def walk(x, sent, path, nums, ctx):
    """Give every numeral of x its role. path = names of the enclosing slots, outermost first."""
    k = x[0]
    if k == 'num':
        nums.append(dict(line=x[2].line, value=x[1], kind='hex' if x[2].t.startswith('0x') else 'dec', sent=sent,
                         role=ctx.get('role', 'bare'), slot='/'.join(path), ctx=dict(ctx.get('info', {})),
                         pos=x[2].pos))
        return
    if k == 'id':
        return
    if k == 'paren':
        return walk(x[1], sent, path, nums, ctx)
    if k in ('list', 'cat'):
        items = x[1]
        for j, it in enumerate(items):
            p = path
            if path and path[-1] == 'regs' and k == 'list':
                p = path[:-1] + [f'reg{j}']
            walk(it, sent, p, nums, {'info': ctx.get('info', {})})
        return
    if k == 'tuple':
        names = ['base', 'len'] if path and path[-1] in ('a_vis', 'a_ghost') else [f't{j}' for j in range(len(x[1]))]
        for j, it in enumerate(x[1]):
            walk(it, sent, path + [names[j]], nums, {'info': ctx.get('info', {})})
        return
    if k == 'rec':
        info = dict(ctx.get('info', {}))
        fields = dict(x[1])
        if 'a_base' in fields:
            info['a_base'] = show(fields['a_base'])
        for f, v in x[1]:
            vv = unparen(v)
            if f in NUMFIELD and vv[0] == 'num':
                walk(vv, sent, path + [f], nums, {'role': f, 'info': info})
            else:
                walk(v, sent, path + [f], nums, {'info': info})
        return
    if k == 'app':
        head, args = x[1], x[2]
        info = dict(ctx.get('info', {}))
        if head.startswith('K') and head in ARGNAME:
            info['kentry'] = head
            if head == 'KWord':
                w = unparen(args[1])
                info['w'] = w[1] if w[0] == 'num' else None
                info['v'] = show(args[2])
            if head in ('KZero', 'KWr', 'KFill', 'KUnk', 'KBlob'):
                info['n'] = show(args[1])
        if head == 'KImg':
            info['kentry'] = 'KImg'
            lo, hi = unparen(args[0]), unparen(args[1])
            info['lo'], info['hi'] = lo[1], hi[1]
        if head == 'KRange':
            info['kentry'] = 'KRange'
            info['e'] = show(args[0])
        if head == 'seg':
            info['seg_of'] = args[0][1] if args[0][0] == 'id' else show(args[0])
        for j, a in enumerate(args):
            aa = unparen(a)
            if aa[0] == 'num' and j in ARGROLE.get(head, {}):
                walk(aa, sent, path, nums, {'role': ARGROLE[head][j], 'info': info})
                continue
            if head in ('EAlu', 'EAluw', 'EMd', 'EMdw'):
                op = unparen(args[0])[1] if args[0][0] in ('id', 'paren') else '?'
                if j == 0:
                    continue
                p = path + [f'{head}.{op.split(".")[-1]}.{"ab"[j - 1]}']
            elif head == 'ELit':
                p = path
            else:
                nm = ARGNAME.get(head, {}).get(j)
                p = path + [nm] if nm else path + [f'{head}.{j}']
            if aa[0] == 'num':
                walk(aa, sent, p, nums, {'role': f'{head}.arg{j}', 'info': info})
            else:
                walk(a, sent, p, nums, {'info': info})
        return
    raise ValueError(k)
