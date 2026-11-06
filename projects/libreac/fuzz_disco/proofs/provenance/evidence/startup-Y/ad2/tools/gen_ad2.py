#!/usr/bin/env python3
"""gen_ad2.py -- cgif's ASan main-entry files for one image: lib/A/AD2i.v + lib/A/AD2j.v (image A, asan) or
lib/YD2i.v + lib/YD2j.v (image B, asan-ubsan), in the form of proofs/cgif/cgif_file_fuzzer at c8557374ad2e.

The donor's two files are the TEXT. This tool changes only their DATA items and computes each one from the image's
own inputs (the rule table of the donor control run):

  AD2i  sregs_main            the 50 hand-off states' s_regs (per register: one literal -> SLit; one VT spelling -> its
                              sv; otherwise SOff (9+i) 0, which rcheck accepts for any value)
        TIDV                  the n with KRange (EVar n) 1 4194303 in every hand-off state
        CANV                  the variable every state holds at the canary cells (the template's SOff CANARY_ATOM chunks)
        TFIB_MAIN             the states' pc (all equal; checked = `main` of the twin when one is given)
        0x10000 / 0x5fb000    img_lo / img_hi of the atable (AB12) -- cjust, img_regions_abs, img_region_shape
        0x9d000 / 0x5fb000    tfib_rw_window's bounds (AB1h) -- wjust
  AD2j  IMG_REGIONS           (1) below .data: the image's memory [img_lo, .data) minus Tfib_owned_static (AF0m), split at
                              the rw window's low bound (groups R_A1*, R_A2*), one CImg chunk per region; the owned
                              8-byte .got cell that holds the canary's address is kept (its own CImg chunk);
                              (2) from .data on: the donor's regions R_A3.. at the same offsets from the section anchor
                              they sit at (R_A3: asan_globals start; bss head: .bss start; bss tail: .bss end; a hi equal
                              to img_hi stays img_hi), with every CVal value read from the hand-off states.

Usage (image A; B: --side B and the Y files):
  gen_ad2.py --side A --states AB01.v --atable AB12.v --tsegs AB1h.v --owned AF0m.v --image IMG [--twin TWIN]
      --tmpl-ad2i DONOR/A/AD2i.v --tmpl-ad2j DONOR/A/AD2j.v --tmpl-image DONOR_IMG
      [--ns FROM=TO ...] [--modified TEXT] --out-ad2i OUT/AD2i.v --out-ad2j OUT/AD2j.v
"""
import argparse, hashlib, os, re, struct, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hsform  # noqa: E402  (donor_states: the AB01 kn deltas expanded)
from elftools.elf.elffile import ELFFile  # noqa: E402


# ---------------------------------------------------------------- Rocq term reader (the released data syntax)
TOK = re.compile(r'\s*(?:(\{\|)|(\|\})|(:=)|(-?\d+)|([A-Za-z_][A-Za-z0-9_\'.]*)|(%[A-Za-z]+)|([\[\]();,]))', re.S)


def tokens(s):
    out, i, s = [], 0, s.rstrip()
    while i < len(s):
        m = TOK.match(s, i)
        if not m:
            if s[i:].strip() == '':
                break
            raise SyntaxError('cannot read at %r' % s[i:i + 40])
        i = m.end()
        g = m.lastindex
        if g == 6:
            continue
        t = m.group(g)
        out.append(('n', int(t)) if g == 4 else ('s', t) if g in (1, 2, 3, 7) else ('i', t))
    return out


class _P:
    def __init__(self, t):
        self.t, self.i = t, 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else ('eof', None)

    def eat(self, v=None):
        tk = self.peek()
        if v is not None and tk[1] != v:
            raise SyntaxError('expected %r got %r' % (v, tk))
        self.i += 1
        return tk

    def starts(self):
        k, v = self.peek()
        return k in ('n', 'i') or v in ('(', '[', '{|')

    def term(self):
        k, v = self.peek()
        if k == 'i':
            self.eat()
            args = []
            while self.starts():
                args.append(self.atom())
            return (v,) + tuple(args)
        return self.atom()

    def atom(self):
        k, v = self.peek()
        if k == 'n':
            self.eat()
            return v
        if k == 'i':
            self.eat()
            return (v,)
        if v == '(':
            self.eat('(')
            x = self.term()
            items = [x]
            while self.peek()[1] == ',':
                self.eat(',')
                items.append(self.term())
            self.eat(')')
            return x if len(items) == 1 else ('tup',) + tuple(items)
        if v == '[':
            self.eat('[')
            items = []
            if self.peek()[1] != ']':
                items.append(self.term())
                while self.peek()[1] == ';':
                    self.eat(';')
                    items.append(self.term())
            self.eat(']')
            return ['L'] + items
        if v == '{|':
            self.eat('{|')
            fs = {}
            while self.peek()[1] != '|}':
                f = self.eat()[1]
                self.eat(':=')
                fs[f] = self.term()
                if self.peek()[1] == ';':
                    self.eat(';')
            self.eat('|}')
            return fs
        raise SyntaxError('unexpected %r' % ((k, v),))


def parse(s):
    p = _P(tokens(s))
    t = p.term()
    if p.peek()[0] != 'eof':
        raise SyntaxError('trailing input %r' % (p.t[p.i:p.i + 5],))
    return t


def unq(t):
    """drop module qualifiers from constructor names (AB01 spells Instr.ALU_ADD, AD2i ALU_ADD)"""
    if isinstance(t, tuple):
        return (t[0].rsplit('.', 1)[-1],) + tuple(unq(a) for a in t[1:])
    if isinstance(t, list):
        return ['L'] + [unq(a) for a in t[1:]]
    if isinstance(t, dict):
        return {k: unq(v) for k, v in t.items()}
    return t


def show(t):
    """a term in the released spelling: negative numbers and applications as arguments in parentheses"""
    if isinstance(t, int):
        return str(t) if t >= 0 else '(%d)' % t
    if isinstance(t, list):
        return '[' + '; '.join(show(a) for a in t[1:]) + ']'
    if len(t) == 1:
        return t[0]
    return t[0] + ' ' + ' '.join('(%s)' % show(a) if isinstance(a, tuple) and len(a) > 1 else show(a) for a in t[1:])


def hx(z):
    return '0x%x' % z


# ---------------------------------------------------------------- inputs
ACS_FIELDS = ('a_ss', 'a_maps', 'a_totsz', 'a_ylo', 'a_eager', 'a_vis', 'a_ghost', 'a_abytes', 'a_brk', 'a_fd', 'a_tidset')


def _limbs(it, n):
    v = 0
    for i in range(n):
        v |= next(it) << (30 * i)
    return v


def yr00_term(heads, nums, env):
    """a `ltac2:(YR00.build [heads] [data])` term (cgif_rgb_fuzzer's compressed data files; decoder = YR00.dec) in this
    reader's representation: lists ['L', ...], SA as the {a_base, a_off} record, ACS as the acs record"""
    it = iter(nums)

    def dec():
        t = next(it)
        k, q = t & 3, t >> 2
        if k == 0:
            h = heads[q >> 3]
            n = q & 7
            if n == 7:
                n = next(it)
            args = [dec() for _ in range(n)]
            return app(h, args)
        if k == 1:
            return q
        if k == 2:
            return q
        if q == 0:
            return -next(it)
        if q == 1:
            s, n = next(it), next(it)
            v = _limbs(it, n)
            return v if s == 1 else -v
        if q in (2, 4):
            return _limbs(it, next(it))
        if q == 3:
            return next(it)
        if q == 5:
            x = dec()
            dec()
            return x
        raise ValueError('YR00: bad escape %d' % t)

    def app(h, a):
        nm = h.strip()
        while nm.startswith('(') and nm.endswith(')'):
            nm = nm[1:-1].strip()
        nm = nm.lstrip('@').split()[0].rsplit('.', 1)[-1]
        if nm == 'cons':
            return ['L', a[0]] + a[1][1:]
        if nm == 'nil':
            return ['L']
        if nm == 'app':
            return a[0] + a[1][1:]
        if nm == 'seg':
            return ['L'] + a[0][1:][a[1]:a[1] + a[2]]
        if nm == 'pair':
            return ('tup', a[0], a[1])
        if nm == 'SA':
            return {'a_base': a[0], 'a_off': a[1]}
        if nm == 'ACS':
            assert len(a) == len(ACS_FIELDS), len(a)
            return dict(zip(ACS_FIELDS, a))
        if nm == 'SSR':
            return ('SS',) + tuple(a)
        if nm in env and not a:
            return env[nm]
        return (nm,) + tuple(a)
    t = dec()
    assert next(it, None) is None, 'YR00: trailing data'
    return t


def load_states(path):
    txt = open(path).read()
    m = re.search(r'Definition (\w+)_list : list acs :=\n\[(.*?)\]\.', txt, re.S)
    name = m.group(1)
    order = [int(x.strip().rsplit('_', 1)[1]) for x in m.group(2).split(';')]
    out = []
    if 'YR00.build' in txt:
        env = {}
        for d in re.finditer(r'Definition (\w+) : [^\n]*?:=\s*ltac2:\(YR00\.build \[(.*?)\] \[([0-9;\s-]*)\]\)\.', txt, re.S):
            heads = [h.strip().lstrip("'") for h in hsform.split_top(d.group(2))]
            env[d.group(1)] = yr00_term(heads, [int(x) for x in d.group(3).split(';') if x.strip()], env)
        for h in order:
            st = dict(env['%s_%d' % (name, h)])
            st['kn'] = st['a_ss'][4][1:]
            st['h'] = h
            out.append(st)
        return name, out
    ds = hsform.donor_states(path, name)
    for h in order:
        pre, kn, suf = ds[h]
        st = unq(parse(pre + 'HSKN' + suf))
        st['kn'] = [unq(parse(k)) for k in kn]
        st['h'] = h
        out.append(st)
    return name, out


CITE = r"0x[0-9a-f]+|[A-Za-z_][\w']*\.[A-Za-z_][\w']*"


def _cite(v, path):
    """a Z constant written either as a hex literal or as `<Module>.<NAME>` (fuzz_disco's AB12 / AB1h cite
    YImgTop.IMG_LO / YImgTop.IMG_TOP); the Definition is read from <Module>.v beside the citing file."""
    if v.startswith('0x'):
        return int(v, 16)
    mod, name = v.split('.', 1)
    src = os.path.join(os.path.dirname(os.path.abspath(path)), mod + '.v')
    d = re.search(r'Definition %s\s*:\s*Z\s*:=\s*(0x[0-9a-f]+|\d+)\s*\.' % re.escape(name), open(src).read())
    assert d, '%s not defined in %s' % (v, src)
    return int(d.group(1), 16) if d.group(1).startswith('0x') else int(d.group(1))


def atable_bounds(path):
    t = open(path).read()
    out = []
    for field in ('img_lo', 'img_hi'):
        m = re.search(r'%s := (%s)' % (field, CITE), t)
        assert m, 'atable: no %s' % field
        out.append(_cite(m.group(1), path))
    return tuple(out)


def rw_window(path):
    t = open(path).read()
    m = re.search(r'Lemma \w+_rw_window : forall m \(x : word\),\n(%s) <= bv_unsigned x < (%s) -> wview' % (CITE, CITE), t)
    assert m, 'no rw_window lemma in %s' % path
    return _cite(m.group(1), path), _cite(m.group(2), path)


def _zeval(s, path=None):
    """a `(addr, len)` arithmetic term of an owned-static / zero-shadow list. fuzz_disco's A/AF0m writes
    `YImgTop.IMG_TOP - 0xa5a00`, so a `<Module>.<NAME>` citation is resolved first (needs `path`)."""
    s = s.strip()
    if path:
        s = re.sub(r"[A-Za-z_][\w']*\.[A-Za-z_][\w']*", lambda m: str(_cite(m.group(0), path)), s)
    if not re.fullmatch(r'[0-9a-fA-Fx+\- ()]+', s):
        raise ValueError('owned_static: cannot evaluate %r' % s)
    return eval(s, {'__builtins__': {}}, {})


def _zterm(x):
    if isinstance(x, int):
        return x
    if x[0] == 'sub':
        return _zterm(x[1]) - _zterm(x[2])
    if x[0] == 'add':
        return _zterm(x[1]) + _zterm(x[2])
    raise ValueError('owned_static: cannot evaluate %r' % (x,))


def owned_static(path):
    t = open(path).read()
    m = re.search(r'Definition \w+_owned_static : list \(Z \* Z\) :=\n(.*?)\](?:\)\.|\.)\n', t, re.S)
    body = m.group(1)
    if 'YR00.build' in body:
        hm = re.search(r'YR00\.build \[(.*)\] \[([0-9;\s-]*)$', body, re.S)
        heads = [h.strip().lstrip("'") for h in hsform.split_top(hm.group(1))]
        lst = yr00_term(heads, [int(x) for x in hm.group(2).split(';') if x.strip()], {})
        return [(_zterm(p[1]), _zterm(p[2])) for p in lst[1:]]
    out = []
    for e in hsform.split_top(body.strip().lstrip('[').strip()):
        e = e.strip()
        assert e.startswith('(') and e.endswith(')'), e
        a, n = hsform.split_top(e[1:-1], ',')
        out.append((_zeval(a, path), _zeval(n, path)))
    return out


class Image:
    def __init__(self, path):
        self.path = path
        self.data = open(path, 'rb').read()
        self.sha = hashlib.sha256(self.data).hexdigest()
        f = ELFFile(open(path, 'rb'))
        self.loads = [(p['p_vaddr'], p['p_filesz'], p['p_memsz'], p['p_offset']) for p in f.iter_segments() if p['p_type'] == 'PT_LOAD']
        self.sec = {s.name: (s['sh_addr'], s['sh_addr'] + s['sh_size']) for s in f.iter_sections() if s['sh_addr']}

    def byte(self, a):
        for va, fs, ms, off in self.loads:
            if va <= a < va + fs:
                return self.data[off + a - va]
            if va <= a < va + ms:
                return 0
        # page-extended segment bytes (TSEGS maps whole pages from the file)
        for va, fs, ms, off in self.loads:
            pg = va & ~0xfff
            if pg <= a < va:
                return self.data[off - (va - a)]
        return None

    def word(self, a, n):
        bs = [self.byte(a + i) for i in range(n)]
        if None in bs:
            return None
        return int.from_bytes(bytes(bs), 'little')


def load_syms(path):
    """{name: [(addr, size), ...]} from an unstripped ELF (.symtab) or an `nm -S` listing (addr size type name)"""
    out = {}
    if open(path, 'rb').read(4) == b'\x7fELF':
        st = ELFFile(open(path, 'rb')).get_section_by_name('.symtab')
        it = ((s.name, s['st_value'], s['st_size']) for s in st.iter_symbols())
    else:
        it = []
        for l in open(path):
            f = l.split()
            if len(f) == 4:
                it.append((f[3], int(f[0], 16), int(f[1], 16)))
            elif len(f) == 3:
                it.append((f[2], int(f[0], 16), 0))
    for n, v, sz in it:
        if n and not n.startswith('$') and (v, sz) not in out.setdefault(n, []):
            out[n].append((v, sz))
    return out


# the objects the donor's regions from .data on are placed against (template point -> the object that starts there; the
# layout of cgif's runtime tail, identified on fuzz_ctrl's unstripped twins and checked on every run with a --twin)
ANCHOR_NAMES = [
    ('R_A3', 'lo', 'oft_arg0'), ('R_A3', 'hi', '__start_asan_globals'),
    ('R_A4', 'lo', '__do_init.__initialized'), ('R_A4', 'hi', '__do_fini.__finalized'),
    ('R_RS', 'lo', 'read_stage'), ('R_A5a', 'lo', 'target_run.initialized'), ('R_A5a', ('c', 1), 'oft_in_callback'),
    ('R_A5a', ('e', 2), '__environ'), ('R_A5a', ('c', 3), 'builtin_tls'),
    ('R_A7b', 'lo', '__thread_list_lock'), ('R_A7b', 'wlo', 'finished_atexit'), ('R_A7b', 'whi', 'exit.exit_lock'),
    ('R_A7c', ('e', 0), '__hwcap'), ('R_A7c', ('c', 1), 'freebuf_queue'),
    ('R_A8', 'lo', '__malloc_replaced'), ('R_A9a', 'lo', 'tl_lock_count'), ('R_A9a', 'hi', '__pthread_tsd_main')]


# ---------------------------------------------------------------- the donor's text pieces read back
def template_regions(txt):
    regs = []
    for m in re.finditer(r'Definition (R_\w+) : region :=\nmkRegion None (-?\d+) (-?\d+) (-?\d+) (-?\d+)\n\[(.*?)\]\.\n', txt, re.S):
        body = m.group(6).strip()
        chunks = []
        for c in (hsform.split_top(body) if body else []):
            t = parse(c)
            assert t[0] == 'mkChunk', c
            chunks.append((t[1], t[2]))
        regs.append({'name': m.group(1), 'lo': int(m.group(2)), 'hi': int(m.group(3)), 'wlo': int(m.group(4)),
                     'whi': int(m.group(5)), 'chunks': chunks})
    order = re.search(r'Definition IMG_REGIONS : smem := \[(.*?)\]\.', txt).group(1).split('; ')
    assert order == [r['name'] for r in regs], 'IMG_REGIONS order differs from the definitions'
    return regs


def render_regions(regs):
    out = []
    for r in regs:
        cs = ';\n'.join('mkChunk %d (%s)' % (o, show(k)) for o, k in r['chunks'])
        out.append('Definition %s : region :=\nmkRegion None %d %d %d %d\n[ %s ].' % (r['name'], r['lo'], r['hi'], r['wlo'], r['whi'], cs))
    out.append('Definition IMG_REGIONS : smem := [%s].' % '; '.join(r['name'] for r in regs))
    return '\n'.join(out) + '\n'


EXPR_DEFS = ('eSp0', 'B5', 'eArgv1', 'BR', 'eEnvp')
VT_TEXT = ('Definition VT (two : bool) : list (expr * sv) :=\n'
           '[ (EVar 1, SOff 3 0); (EVar TIDV, SOff 8 0); (EExt false 0 4 (EVar TIDV), SOff 8 0);\n'
           '(EAlu ALU_ADD B5 (ELit 184), SOff 1 0); (EAlu ALU_ADD B5 (ELit 24), SOff 5 0);\n'
           '(EVar 8, SData UID_DATOM 0 8); (EVar CANV, SOff CANARY_ATOM 0);\n'
           '(EAlu ALU_ADD eSp0 (ELit (-48)), SOff 0 (-48)); (EAlu ALU_ADD eSp0 (ELit 8), SOff 0 8); (eEnvp, SOff 4 0) ]\n'
           '++ (if two then [(eArgv1, SOff 2 0)] else []).')


def vt_table(ad2i, tidv, canv):
    """AD2i's VT (two = false and two = true), its expressions taken from the template's definitions"""
    assert VT_TEXT in ad2i, 'the template VT is not cgif\'s; update VT_TEXT and vt_table together'
    ex = {}
    for nm in EXPR_DEFS:
        m = re.search(r'Definition %s : expr :=\s*(.*?)\.\n' % nm, ad2i, re.S)
        ex[nm] = unq(parse(m.group(1)))
    atom = int(re.search(r'Definition CANARY_ATOM : nat := (\d+)\.', ad2i).group(1))

    def add(a, b):
        return ('EAlu', ('ALU_ADD',), a, b)
    one = [(('EVar', 1), ('SOff', 3, 0)), (('EVar', tidv), ('SOff', 8, 0)), (('EExt', ('false',), 0, 4, ('EVar', tidv)), ('SOff', 8, 0)),
           (add(ex['B5'], ('ELit', 184)), ('SOff', 1, 0)), (add(ex['B5'], ('ELit', 24)), ('SOff', 5, 0)),
           (('EVar', 8), ('SData', ('UID_DATOM',), 0, 8)), (('EVar', canv), ('SOff', atom, 0)),
           (add(ex['eSp0'], ('ELit', -48)), ('SOff', 0, -48)), (add(ex['eSp0'], ('ELit', 8)), ('SOff', 0, 8)), (ex['eEnvp'], ('SOff', 4, 0))]
    return one, one + [(ex['eArgv1'], ('SOff', 2, 0))], atom


def to_sv(e, vt):
    if isinstance(e, tuple) and e[0] == 'ELit':
        return ('SLit', e[1])
    for v, s in vt:
        if v == e:
            return s
    return None


# ---------------------------------------------------------------- knowledge reads (pre-check of AD2i's entry_check)
def absoff(a):
    return a['a_off'] if isinstance(a, dict) and a.get('a_base') == ('ELit', 0) else None


def kn_img(st, a, n):
    return any(k[0] == 'KImg' and k[1] <= a and a + n <= k[2] for k in st['kn'])


def kn_read(st, img, a, n):
    """the value of the n bytes at absolute a in a state: an exact KWord; a literal KWord containing them; else the
    image bytes under one KImg fact. (The Rocq kn_read is know_lookup; this is its case for these cells.)"""
    for k in st['kn']:
        if k[0] == 'KWord' and absoff(k[1]) == a and k[2] == n:
            return k[3]
    for k in st['kn']:
        if k[0] == 'KWord' and absoff(k[1]) is not None and absoff(k[1]) <= a and a + n <= absoff(k[1]) + k[2] and k[3][0] == 'ELit':
            v = (k[3][1] % (1 << 64)) >> (8 * (a - absoff(k[1])))
            return ('ELit', v % (1 << (8 * n)))
    for k in st['kn']:
        if k[0] == 'KWord' and absoff(k[1]) is not None and absoff(k[1]) < a + n and a < absoff(k[1]) + k[2]:
            return None
    if kn_img(st, a, n):
        w = img.word(a, n)
        return None if w is None else ('ELit', w)
    return None


def merge(ivs):
    out = []
    for a, b in sorted(ivs):
        if out and a <= out[-1][1]:
            out[-1][1] = max(out[-1][1], b)
        else:
            out.append([a, b])
    return [tuple(x) for x in out]


def complement(lo, hi, ivs):
    out, cur = [], lo
    for a, b in merge(ivs):
        if b <= cur or a >= hi:
            continue
        if a > cur:
            out.append((cur, a))
        cur = max(cur, b)
    if cur < hi:
        out.append((cur, hi))
    return out


def letters(i):
    s = ''
    i += 1
    while i:
        i, r = divmod(i - 1, 26)
        s = chr(97 + r) + s
    return s


# ---------------------------------------------------------------- the rules
def compute(a):
    name, states = load_states(a.states)
    img = Image(a.image)
    timg = Image(a.tmpl_image)
    img_lo, img_hi = atable_bounds(a.atable)
    rw_lo, rw_hi = rw_window(a.tsegs)
    owned = owned_static(a.owned)
    ad2i = open(a.tmpl_ad2i).read()
    ad2j = open(a.tmpl_ad2j).read()
    tregs = template_regions(ad2j)
    notes = []

    # TFIB_MAIN: the states' pc
    pcs = {st['a_ss'][1] for st in states}
    assert len(pcs) == 1, 'hand-off states at different pcs: %s' % sorted(pcs)
    main = pcs.pop()
    # TIDV: KRange (EVar n) 1 4194303 in every state
    tid = None
    for st in states:
        c = {k[1][1] for k in st['kn'] if k[0] == 'KRange' and k[1][0] == 'EVar' and k[2] == 1 and k[3] == 4194303}
        tid = c if tid is None else tid & c
    assert len(tid) == 1, 'TIDV not unique: %s' % sorted(tid)
    tidv = tid.pop()

    # template anchors (the donor's image) and the target's
    def anchors(im, imhi):
        return {'ag': im.sec['asan_globals'][0], 'bss0': im.sec['.bss'][0], 'bssend': im.sec['.bss'][1], 'data': im.sec['.data'][0], 'hi': imhi}
    tA = anchors(timg, int(re.search(r'Lemma img_region_shape : .*?r_hi r <= (0x[0-9a-f]+)\.', open(a.tmpl_ad2i).read()).group(1), 16))
    A = anchors(img, img_hi)

    def frame(r):
        if r['hi'] <= tA['ag']:
            return 'ag'
        return 'bss0' if r['lo'] < (tA['bss0'] + tA['bssend']) // 2 else 'bssend'
    syms = load_syms(a.twin) if a.twin else None
    if syms is not None and '__start_asan_globals' not in syms:   # linker-defined; an nm listing may omit it
        syms['__start_asan_globals'] = [(img.sec['asan_globals'][0], 0)]
        notes.append('__start_asan_globals not in --twin: taken as the asan_globals section start %#x' % img.sec['asan_globals'][0])
    # IMG_REGIONS (2): from .data on, the donor's regions. Every point (region bounds, write window, chunk starts and
    # ends) is placed at the same offset from the nearest preceding named object (ANCHOR_NAMES) when the image's symbols
    # are given (--twin: an unstripped ELF or an `nm -S` listing), else at the same offset from its section anchor; then
    # every region is cut around the owned static cells (a region the owned cells split becomes NAME_1, NAME_2, ...).
    tby = {r['name']: r for r in tregs}

    def tpoint(r, pt):
        if isinstance(pt, str):
            return r[pt]
        off, kk = r['chunks'][pt[1]]
        return off if pt[0] == 'c' else off + clen(kk)
    named = sorted((tpoint(tby[rn], pt), sym) for rn, pt, sym in ANCHOR_NAMES if rn in tby)
    override = {}
    if syms is None:
        ar3 = [r for r in tregs if r['lo'] >= tA['data'] and frame(r) == 'ag']
        o = [x for x in owned if x[0] == A['data']]
        for r in ar3:
            if o:
                if o[0][0] + o[0][1] != r['lo'] + A['ag'] - tA['ag']:
                    notes.append('%s: lo from the owned .data range %#x (the asan_globals offset gives %#x)' % (r['name'], o[0][0] + o[0][1], r['lo'] + A['ag'] - tA['ag']))
                override[r['lo']] = o[0][0] + o[0][1]
            else:
                notes.append('%s: no owned range at .data start; lo from the asan_globals offset' % r['name'])

    def place(p, r, by_sym=True):
        if p == tA['hi']:
            return A['hi']
        if p in override:
            return override[p]
        fo = p + A[frame(r)] - tA[frame(r)]
        if syms is None or not by_sym:
            return fo
        c = [(ta, s) for ta, s in named if ta <= p]
        assert c, 'no named object before %#x' % p
        ta, s = c[-1]
        assert s in syms, 'anchor symbol %s not in --twin' % s
        assert len(syms[s]) == 1, 'anchor symbol %s is not unique in --twin: %s' % (s, syms[s])
        return syms[s][0][0] + (p - ta)


    # CANV: the value every state holds at the template's canary cells (SOff CANARY_ATOM 0), placed as below
    atom = int(re.search(r'Definition CANARY_ATOM : nat := (\d+)\.', ad2i).group(1))
    canv = None
    for r in tregs:
        if r['lo'] < tA['data']:
            continue
        for off, k in r['chunks']:
            if k[0] == 'CVal' and k[2] == ('SOff', atom, 0):
                o2 = place(off, r)
                for st in states:
                    v = kn_read(st, img, o2, k[1])
                    assert v and v[0] == 'EVar', 'canary cell %#x: %r' % (o2, v)
                    assert canv in (None, v[1]), 'canary cells disagree: EVar %s / %r' % (canv, v)
                    canv = v[1]
    vt1, vt2, atom2 = vt_table(ad2i, tidv, canv)
    assert atom2 == atom

    # sregs_main
    sregs = []
    for i in range(32):
        es = [st['a_ss'][2][1 + i] for st in states]
        svs = {show(to_sv(e, vt1)) if to_sv(e, vt1) else None for e in es}
        if len(svs) == 1 and None not in svs:
            sregs.append(to_sv(es[0], vt1))
        else:
            sregs.append(('SOff', 9 + i, 0))

    # IMG_REGIONS (1): below .data, the complement of the owned static cells
    got = img.sec.get('.got', (0, 0))
    kept = []
    for lo_, n_ in owned:
        if n_ == 8 and got[0] <= lo_ < got[1]:
            w = img.word(lo_, 8)
            if all(any(k[0] == 'KWord' and absoff(k[1]) == w and k[2] == 8 and k[3] == ('EVar', canv) for k in st['kn']) for st in states):
                kept.append(lo_)
    assert len(kept) <= 1, 'more than one canary GOT cell: %s' % kept
    own = merge([(lo_, lo_ + n_) for lo_, n_ in owned if lo_ not in kept])
    regs = []
    for grp, glo, ghi in (('A1', img_lo, rw_lo), ('A2', rw_lo, A['data'])):
        runs = complement(glo, ghi, own)
        for j, (lo_, hi_) in enumerate(runs):
            cuts = sorted({lo_, hi_} | {x for s in kept for x in (s, s + 8) if lo_ < x < hi_})
            regs.append({'name': 'R_%s%s' % (grp, letters(j) if len(runs) > 1 else ''), 'lo': lo_, 'hi': hi_, 'wlo': 0, 'whi': 0,
                         'chunks': [(cuts[i], ('CImg', cuts[i + 1] - cuts[i])) for i in range(len(cuts) - 1)]})
    for r in tregs:
        if r['lo'] < tA['data']:
            continue
        f = frame(r)
        lo_, hi_ = place(r['lo'], r), place(r['hi'], r)
        if syms is not None:
            flo, fhi = place(r['lo'], r, False), place(r['hi'], r, False)
            if (flo, fhi) != (lo_, hi_):
                notes.append('%s: placed on symbols at [%#x, %#x); the section offset gives [%#x, %#x)' % (r['name'], lo_, hi_, flo, fhi))
        wl, wh = (0, 0) if (r['wlo'], r['whi']) == (0, 0) else (place(r['wlo'], r), place(r['whi'], r))
        chunks = []
        for off, k in r['chunks']:
            o2, e2 = place(off, r), place(off + clen(k), r)
            assert e2 > o2, '%s %#x: chunk placed empty' % (r['name'], off)
            if k[0] == 'CImg':
                chunks.append((o2, ('CImg', e2 - o2)))
            elif k[0] == 'CVal':
                assert e2 - o2 == k[1], '%s %#x: CVal %d placed over %d bytes' % (r['name'], off, k[1], e2 - o2)
                vals = {show(kn_read(st, img, o2, k[1])) for st in states}
                assert len(vals) == 1, '%s %#x: the states disagree: %s' % (r['name'], o2, sorted(vals)[:4])
                e = kn_read(states[0], img, o2, k[1])
                s = to_sv(e, vt1) if e else None
                assert s, '%s %#x: value %r has no spelling' % (r['name'], o2, e)
                if s[0] != k[2][0] or (s[0] == 'SOff' and s[1:] != k[2][1:]):
                    notes.append('%s %#x: donor %s, here %s' % (r['name'], o2, show(k[2]), show(s)))
                chunks.append((o2, ('CVal', k[1], s)))
            else:
                assert e2 - o2 == clen(k), '%s %#x: %s placed over %d bytes' % (r['name'], off, k[0], e2 - o2)
                chunks.append((o2, k))
        pieces = complement(lo_, hi_, own)
        if pieces != [(lo_, hi_)]:
            notes.append('%s [%#x, %#x): cut around the owned static cells into %d regions %s' % (
                r['name'], lo_, hi_, len(pieces), ' '.join('[%#x,%#x)' % p for p in pieces)))
        for j, (plo, phi) in enumerate(pieces):
            pc = []
            for o2, k in chunks:
                if k[0] == 'CImg':
                    a0, b0 = max(o2, plo), min(o2 + k[1], phi)
                    if a0 < b0:
                        pc.append((a0, ('CImg', b0 - a0)))
                elif plo <= o2 and o2 + clen(k) <= phi:
                    pc.append((o2, k))
                elif o2 < phi and plo < o2 + clen(k):
                    raise AssertionError('%s %#x: %s straddles an owned static cell' % (r['name'], o2, k[0]))
            pw = (0, 0) if (wl, wh) == (0, 0) else (max(wl, plo), min(wh, phi))
            if pw[1] <= pw[0]:
                pw = (0, 0)
            regs.append({'name': r['name'] if len(pieces) == 1 else '%s_%d' % (r['name'], j + 1), 'lo': plo, 'hi': phi,
                         'wlo': pw[0], 'whi': pw[1], 'chunks': pc, 'frame': f})
    return {'name': name, 'states': states, 'img': img, 'main': main, 'tidv': tidv, 'canv': canv, 'atom': atom, 'sregs': sregs,
            'regs': regs, 'img_lo': img_lo, 'img_hi': img_hi, 'rw': (rw_lo, rw_hi), 'owned': owned, 'own': own, 'kept': kept,
            'vt1': vt1, 'vt2': vt2, 'notes': notes, 'A': A, 'tA': tA, 'tregs': tregs, 'timg': timg}


def clen(k):
    return k[1] if k[0] in ('CImg', 'CVal', 'CZero') else 0


def gaps_of(r):
    return complement(r['lo'], r['hi'], [(o, o + clen(k)) for o, k in r['chunks']])


def strict_overhang(r, im):
    """the bytes of the region outside every PT_LOAD [vaddr, vaddr + memsz) (page-extended segment bytes)"""
    return complement(r['lo'], r['hi'], [(va, va + ms) for va, fs, ms, off in im.loads])


def gate(R):
    """the AD2j gate (2026-10-28): lo <= hi; regions ordered and disjoint; chunks ordered,
    disjoint and inside their region; every region inside the page-extended PT_LOADs (TSEGS); a gap in a region fails
    unless the donor's region of the same name has one. Returns (errors, table rows)."""
    errs, rows = [], []
    segs = [(va & ~0xfff, (va + ms + 0xfff) & ~0xfff) for va, fs, ms, off in R['img'].loads]
    tby = {r['name']: r for r in R['tregs']}
    prev = None
    for r in R['regs']:
        n = r['name']
        if r['lo'] > r['hi']:
            errs.append('%s: lo > hi' % n)
        if prev is not None and r['lo'] < prev['hi']:
            errs.append('%s: not after %s (regions must be ordered and disjoint)' % (n, prev['name']))
        prev = r
        a = r['lo']
        for o, k in r['chunks']:
            if o < a:
                errs.append('%s %#x: chunk overlaps or precedes the previous one' % (n, o))
            if o < r['lo'] or o + clen(k) > r['hi']:
                errs.append('%s %#x: chunk outside [%#x, %#x)' % (n, o, r['lo'], r['hi']))
            a = max(a, o + clen(k))
        if complement(r['lo'], r['hi'], segs):
            errs.append('%s [%#x, %#x): bytes outside the page-extended PT_LOADs: %s' % (n, r['lo'], r['hi'], complement(r['lo'], r['hi'], segs)))
        g = gaps_of(r)
        t = tby.get(n) or tby.get(re.sub(r'_\d+$', '', n))
        tg = gaps_of(t) if t else []
        if g and not tg:
            errs.append('NEW GAP: %s %s, the donor\'s %s %s is contiguous' % (
                n, [(hx(x), hx(y)) for x, y in g], n, ('[%#x, %#x)' % (t['lo'], t['hi'])) if t else '(no region of that name; every donor A1/A2 region is contiguous)'))
        rows.append((n, r['lo'], r['hi'], len(r['chunks']), g, tg, strict_overhang(r, R['img']), strict_overhang(t, R['timg']) if t else None))
    return errs, rows


def gate_table(rows):
    out = ['| region | lo | hi | chunks | gaps (here) | gaps (donor, same name) | outside PT_LOAD memsz (here) | (donor) |', '|---|---|---|---|---|---|---|---|']
    f = lambda ivs: '-' if ivs is None else (', '.join('[%#x,%#x)' % iv for iv in ivs) or 'none')
    for n, lo, hi, nc, g, tg, ov, tov in rows:
        out.append('| %s | %#x | %#x | %d | %s | %s | %s | %s |' % (n, lo, hi, nc, f(g), f(tg), f(ov), f(tov)))
    return '\n'.join(out) + '\n'


# ---------------------------------------------------------------- checks (Python reading of entry_check; the Rocq vm_compute decides)
def precheck(R):
    errs = []
    img, states, rw_lo, rw_hi = R['img'], R['states'], R['rw'][0], R['rw'][1]
    for r in R['regs']:
        if not (0 <= r['lo'] and r['hi'] <= 2 ** 47):
            errs.append('%s: bounds' % r['name'])
        if not (r['whi'] <= r['wlo'] or (rw_lo <= r['wlo'] and r['whi'] <= rw_hi)):
            errs.append('%s: write window outside the rw window' % r['name'])
        for off, k in r['chunks']:
            if not (r['lo'] <= off and off + (k[1] if k[0] == 'CImg' else k[1] if k[0] == 'CVal' else 0) <= r['hi']):
                errs.append('%s %#x: chunk outside its region' % (r['name'], off))
            for st in states:
                if k[0] == 'CImg':
                    if not (kn_img(st, off, k[1]) and R['img_lo'] <= off and off + k[1] <= R['img_hi']):
                        errs.append('%s %#x CImg %d: no KImg in state %d' % (r['name'], off, k[1], st['h'])); break
                elif k[0] == 'CVal':
                    e = kn_read(st, img, off, k[1])
                    if not e or to_sv(e, R['vt1']) != k[2]:
                        errs.append('%s %#x: state %d reads %r' % (r['name'], off, st['h'], e)); break
        for o in R['own']:
            if o[0] < r['hi'] and r['lo'] < o[1]:
                errs.append('%s overlaps owned static [%#x, %#x)' % (r['name'], o[0], o[1]))
    rs = sorted(R['regs'], key=lambda r: r['lo'])
    for x, y in zip(rs, rs[1:]):
        if x['hi'] > y['lo']:
            errs.append('%s and %s overlap' % (x['name'], y['name']))
    esp0 = R['vt1'][8][0][2]
    kwr = ('KWr', {'a_base': esp0, 'a_off': -8388608}, ('ELit', 8388608))
    for st in states:
        if st['a_fd'] != ('FdStd',):
            errs.append('state %d: a_fd %r' % (st['h'], st['a_fd']))
        if kwr not in st['kn']:
            errs.append('state %d: no KWR_STACK fact (R_stk unjustified)' % st['h'])
        if ('KRange', ('EVar', R['tidv']), 1, 4194303) not in st['kn']:
            errs.append('state %d: no KRange (EVar TIDV) 1 4194303' % st['h'])
        if st['a_ss'][1] != R['main']:
            errs.append('state %d: pc %#x' % (st['h'], st['a_ss'][1]))
    return errs


TWIN_NAMES = [  # template region (or chunk hole) boundary -> the object that starts there in cgif's runtime layout
    ('R_A3', 'lo', 'oft_arg0'), ('R_A3', 'hi', '__start_asan_globals'), ('R_A4', 'lo', '__do_init.__initialized'),
    ('R_A4', 'hi', '__do_fini.__finalized'), ('R_RS', 'lo', 'read_stage'), ('R_A5a', 'lo', 'target_run.initialized'),
    ('R_A7b', 'lo', '__thread_list_lock'), ('R_A7b', 'wlo', 'finished_atexit'), ('R_A7b', 'whi', 'exit.exit_lock'),
    ('R_A8', 'lo', '__malloc_replaced'), ('R_A9a', 'lo', 'tl_lock_count'), ('R_A9a', 'hi', '__pthread_tsd_main')]


def twin_checks(R, twin):
    sy = {n: v[0] for n, v in load_syms(twin).items()}
    sy.setdefault('__start_asan_globals', (R['img'].sec['asan_globals'][0], 0))
    out = []

    def pieces(rn):
        return [r for r in R['regs'] if r['name'] == rn or re.fullmatch(re.escape(rn) + r'_\d+', r['name'])]

    def get(rn, fld):
        p = pieces(rn)
        if not p:
            return None
        return p[0][fld] if fld in ('lo', 'wlo') else p[-1][fld]
    for rn, fld, sym in TWIN_NAMES:
        v = get(rn, fld)
        out.append((rn, fld, sym, v, sy.get(sym, (None,))[0], v is not None and sym in sy and v == sy[sym][0]))
    out.append(('TFIB_MAIN', 'pc', 'main', R['main'], sy['main'][0], R['main'] == sy['main'][0]))
    rs = get('R_RS', 'hi') - get('R_RS', 'lo')
    out.append(('R_RS', 'size', 'read_stage', rs, sy['read_stage'][1], rs == sy['read_stage'][1]))
    bt = sy['builtin_tls'][0]
    for off, k in [c for p in pieces('R_A5a') for c in p['chunks']]:
        if k[0] == 'CVal' and k[2] == ('SOff', 8, 0):
            out.append(('R_A5a', 'tid cell', 'builtin_tls+32', off, bt + 32, off == bt + 32))
    cells = [o for p in pieces('R_A7b') for o, k in p['chunks'] if k[0] == 'CVal' and k[2] == ('SOff', R['atom'], 0)]
    out.append(('R_A7b', 'canary cell', '__stack_chk_guard', cells, sy['__stack_chk_guard'][0], cells == [sy['__stack_chk_guard'][0]]))
    if R['kept']:
        w = R['img'].word(R['kept'][0], 8)
        out.append(('R_A2*', 'kept .got cell value', '__stack_chk_guard', w, sy['__stack_chk_guard'][0], w == sy['__stack_chk_guard'][0]))
    return out


# ---------------------------------------------------------------- the two files
def sub1(txt, pat, rep, count=1):
    new, n = re.subn(pat, rep, txt)
    assert n == count, 'template: %r matched %d times, expected %d' % (pat, n, count)
    return new


def header_mod(txt, ns, modified):
    for f_, t_ in ns:
        txt = txt.replace(f_, t_)
    if modified:
        ls = txt.split('\n')
        ls.insert(3, '(* Modified by Theorem Labs, 2026-10: %s *)' % modified)
        txt = '\n'.join(ls)
    return txt


def emit_ad2i(R, tmpl, ns, modified):
    t = open(tmpl).read()
    sv = [show(s) for s in R['sregs']]
    body = '[ ' + ';\n'.join('; '.join(sv[i:i + 8]) for i in range(0, 32, 8)) + ' ].'
    t = sub1(t, r'(Definition sregs_main : list sv :=\n)\[[^\]]*\]\.', lambda m: m.group(1) + body)
    t = sub1(t, r'Definition TIDV : nat := \d+\.', 'Definition TIDV : nat := %d.' % R['tidv'])
    t = sub1(t, r'Definition CANV : nat := \d+\.', 'Definition CANV : nat := %d.' % R['canv'])
    t = sub1(t, r'Definition TFIB_MAIN : Z := 0x[0-9a-f]+\.', 'Definition TFIB_MAIN : Z := %s.' % hx(R['main']))
    t = sub1(t, r'\(0x[0-9a-f]+ <=\? YP09\.c_off c\) && \(YP09\.c_off c \+ l <=\? 0x[0-9a-f]+\)',
             '(%s <=? YP09.c_off c) && (YP09.c_off c + l <=? %s)' % (hx(R['img_lo']), hx(R['img_hi'])))
    t = sub1(t, r'\| None => \(0x[0-9a-f]+ <=\? r_wlo r\) && \(r_whi r <=\? 0x[0-9a-f]+\)',
             '| None => (%s <=? r_wlo r) && (r_whi r <=? %s)' % (hx(R['rw'][0]), hx(R['rw'][1])))
    t = sub1(t, r'\(r_hi r <=\? 0x[0-9a-f]+\) \| _ => false end\)%bool IMG_REGIONS', '(r_hi r <=? %s) | _ => false end)%%bool IMG_REGIONS' % hx(R['img_hi']))
    t = sub1(t, r'r_base r = None /\\ r_hi r <= 0x[0-9a-f]+\.', 'r_base r = None /\\\\ r_hi r <= %s.' % hx(R['img_hi']))
    return header_mod(t, ns, modified)


def emit_ad2j(R, tmpl, ns, modified):
    t = open(tmpl).read()
    i = t.index('Definition R_')
    return header_mod(t[:i], ns, modified) + render_regions(R['regs'])


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    for k in ('states', 'atable', 'tsegs', 'owned', 'image', 'tmpl_ad2i', 'tmpl_ad2j', 'tmpl_image', 'out_ad2i', 'out_ad2j'):
        ap.add_argument('--' + k.replace('_', '-'), required=True)
    ap.add_argument('--side', choices=['A', 'B'], required=True)
    ap.add_argument('--twin')
    ap.add_argument('--ns', action='append', default=[], help='FROM=TO module path rewrite, applied in order')
    ap.add_argument('--modified', help='text of the added 4th header line')
    ap.add_argument('--report', help='write the computed data items and checks here')
    ap.add_argument('--gate-table', help='write the per-region gate table (markdown) here')
    a = ap.parse_args()
    R = compute(a)
    errs = precheck(R)
    rep = ['image %s sha256 %s' % (a.image, R['img'].sha), 'states %s (%s, %d)' % (a.states, R['name'], len(R['states'])),
           'TFIB_MAIN %s  TIDV %d  CANV %d  CANARY_ATOM %d' % (hx(R['main']), R['tidv'], R['canv'], R['atom']),
           'img %s..%s  rw window %s..%s  .data %s  asan_globals %s  .bss %s..%s' % (
               hx(R['img_lo']), hx(R['img_hi']), hx(R['rw'][0]), hx(R['rw'][1]), hx(R['A']['data']), hx(R['A']['ag']), hx(R['A']['bss0']), hx(R['A']['bssend'])),
           'sregs_main ' + '; '.join(show(s) for s in R['sregs']),
           'kept owned .got cell (canary address): %s' % [hx(x) for x in R['kept']],
           'regions %d: %s' % (len(R['regs']), ' '.join('%s[%d]' % (r['name'], len(r['chunks'])) for r in R['regs']))]
    rep += ['NOTE ' + n for n in R['notes']]
    rep += ['PRECHECK ' + (e) for e in errs] or ['PRECHECK ok: every chunk justified in all %d states (Python reading of cjust/wjust/rjust)' % len(R['states'])]
    gerrs, grows = gate(R)
    rep += ['GATE ' + e for e in gerrs] or ['GATE ok: %d regions: lo <= hi, ordered, disjoint; chunks ordered, disjoint, inside their region; '
                                           'inside the page-extended PT_LOADs; %d with gaps, each where the donor\'s region of that name has one'
                                           % (len(grows), sum(1 for x in grows if x[4]))]
    errs += gerrs
    if a.gate_table:
        open(a.gate_table, 'w').write(gate_table(grows))
    if a.twin:
        for row in twin_checks(R, a.twin):
            rep.append('TWIN %s %s = %s: %s vs %s %s' % (row[0], row[1], row[2], row[3], row[4], 'ok' if row[5] else 'MISMATCH'))
            if not row[5]:
                errs.append('twin: %s %s' % (row[0], row[1]))
    if errs:
        rep.append('NOT WRITTEN: %d check(s) failed' % len(errs))
    else:
        ns = [x.split('=', 1) for x in a.ns]
        open(a.out_ad2i, 'w').write(emit_ad2i(R, a.tmpl_ad2i, ns, a.modified))
        open(a.out_ad2j, 'w').write(emit_ad2j(R, a.tmpl_ad2j, ns, a.modified))
        rep.append('wrote %s, %s' % (a.out_ad2i, a.out_ad2j))
    txt = '\n'.join(rep) + '\n'
    if a.report:
        open(a.report, 'w').write(txt)
    sys.stdout.write(txt)
    if errs:
        sys.exit(1)


if __name__ == '__main__':
    main()
