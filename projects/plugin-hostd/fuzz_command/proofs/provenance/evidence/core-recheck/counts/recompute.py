#!/usr/bin/env python3
"""Recompute, from OUR image of each file's build, every candidate image-derived count that enumerate.py lists.

Inputs (all relative to this directory unless given):
  candidates.tsv   enumerate.py output (one row per file, line, kind, value)
  judgments.tsv    hand judgments: a row settles one candidate (file, line, value) or every candidate of a file glob /
                   value / name pattern; columns: match_file, match_line ('*' = any), match_value ('*' = any),
                   match_name (regex on the candidate's name, '*' = any), status, quantity, expr, img, reason
  the unit's lib tree, the donor lib tree, the gate runs (RA RB RU full.tsv), the images.

Each candidate is settled by the FIRST rule that applies (see RULES below). Every SAME / DIFFERS row carries the
expression it was recomputed with and the command that prints it:  python3 recompute.py --expr EXPR --img KEY
Output: counts.tsv, recompute.log (one printed line per quantity), controls.tsv (known-answer controls).

Usage:
  python3 recompute.py LIB DONOR_LIB RUNS_DIR IMG_DIR PLAIN_IMG_DIR          (full run)
  python3 recompute.py --expr EXPR --img KEY IMG_DIR PLAIN_IMG_DIR             (print one quantity)
Image keys: A = fuzz_command.asan c0661b96b5bd (+ twin 68db792d5fa7), B = fuzz_command.asan-ubsan bbe55d24d096
(+ twin 658cefbe806b), P = fuzz_command plain a20873dc7f0e (+ twin fbe3a48ad296); donors dA = cgif_file_fuzzer.asan
7093581aab04 (+ 488e39500746), dB = cgif_file_fuzzer.asan-ubsan 1c29845fe605 (+ ce511d541cda).
"""
import bisect
import collections
import fnmatch
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import imgq  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
NUMRE = re.compile(r'(?<![\w.\'])(0x[0-9a-fA-F]+|\d+)(?![\w\'])')
GEN = {'A/' + x + '.v' for x in 'AB01 AB03 AF0m AD2j AE3i ACej AB1w'.split()} | \
      {'B/' + x + '.v' for x in 'YB01 YB03 YF0m YD2j YE3i YCej YB1w'.split()}


def ival(s):
    return int(s, 16) if s.lower().startswith('0x') else int(s)


def load_images(imgd, plaind):
    spec = {'dA': (imgd, 'cgif.A'), 'dB': (imgd, 'cgif.B'), 'A': (imgd, 'cmd.A'), 'B': (imgd, 'cmd.B'),
            'P': (plaind, 'cmd.P')}
    return {k: imgq.Img(os.path.join(d, n + '.pin'), os.path.join(d, n + '.twin'), k) for k, (d, n) in spec.items()}


# ----------------------------------------------------------------------------------------------- catalogs
def header_q(I):
    q = {}
    for i, r in enumerate(I.loads):
        for fld in ('lo', 'memsz', 'filesz', 'hi', 'fhi', 'pglo', 'pghi'):
            q[f'seg({i}).{fld}'] = getattr(r, fld)
        q[f'seg({i}).pghi-seg({i}).pglo'] = r.pghi - r.pglo
        q[f'seg({i}).pghi-seg({i}).lo'] = r.pghi - r.lo
    for nm in ('tls', 'relro', 'ehfh'):
        r = getattr(I, nm)
        if r is None:
            continue
        for fld in ('lo', 'memsz', 'filesz', 'hi', 'pglo', 'pghi'):
            q[f'{nm}.{fld}'] = getattr(r, fld)
    for n, r in I.secs.items():
        for fld in ('lo', 'size', 'hi'):
            q[f"sec('{n}').{fld}"] = getattr(r, fld)
    q['top'] = I.top
    q['top-base'] = I.top - I.base
    for i in range(len(I.loads)):
        q[f'top-seg({i}).lo'] = I.top - I.loads[i].lo
        q[f'top-seg({i}).pglo'] = I.top - I.loads[i].pglo
    return q


# forms: (suffix, python form of the expression, function)
FORMS = [('', '{}', lambda v: v),
         ('/4', '({})//4', lambda v: v // 4 if v % 4 == 0 else None),
         ('/8', '({})//8', lambda v: v // 8 if v % 8 == 0 else None),
         ('>>3', '({})>>3', lambda v: v >> 3 if v >= 0x10000 and v % 8 else None),
         ('/4096', '({})//4096', lambda v: v // 4096 if v % 4096 == 0 else None),
         ('ceil/4096', '-(-({})//4096)', lambda v: -(-v // 4096) if v % 4096 else None),
         ('+0x7fff8000>>3', '(({})>>3)+0x7fff8000', lambda v: (v >> 3) + 0x7fff8000)]


def catalog(I):
    """{value: {expression}}: header quantities and their forms, symbol starts / ends / sizes (and size /4, /8),
    descriptor and entry counts.  An expression evaluates in any image with Img.eval."""
    cat = collections.defaultdict(set)
    for n, v in header_q(I).items():
        if v <= 0:
            continue
        for _, pyf, f in FORMS:
            fv = f(v)
            if fv:
                cat[fv].add(pyf.format(n))
    for name, lst in I.byname.items():
        for k, s in enumerate(lst):
            key = f"sym({name!r})" if len(lst) == 1 else f"sym({name!r}, {k})"
            cat[s.addr].add(key + '.addr')
            if s.size:
                cat[s.end].add(key + '.end')
                cat[s.size].add(key + '.size')
                for d in (4, 8):
                    if s.size % d == 0:
                        cat[s.size // d].add(f'{key}.size//{d}')
    for secn, sz in (('asan_globals', 64), ('.got', 8), ('.init_array', 8), ('.fini_array', 8), ('.preinit_array', 8)):
        if secn in I.secs:
            cat[I.secs[secn].size // sz].add(f"sec({secn!r}).size//{sz}")
    cat[I.phnum].add('phnum')
    return cat


def header_catalog(I, nforms=6):
    cat = collections.defaultdict(set)
    for n, v in header_q(I).items():
        if v <= 0:
            continue
        for _, pyf, f in FORMS[:nforms]:
            fv = f(v)
            if fv:
                cat[fv].add(pyf.format(n))
    return cat


# ----------------------------------------------------------------------------------------------- files
TOK = re.compile(r'\(\*|\*\)|"')


def split_code_comment(t):
    spans, depth, instr, start = [], 0, False, None
    for m in TOK.finditer(t):
        s = m.group()
        if instr:
            if s == '"':
                instr = False
            continue
        if depth == 0 and s == '"':
            instr = True
            continue
        if s == '(*':
            if depth == 0:
                start = m.start()
            depth += 1
        elif s == '*)' and depth > 0:
            depth -= 1
            if depth == 0:
                spans.append((start, m.end()))
    if depth > 0:
        spans.append((start, len(t)))
    code, com, prev = [], [], 0
    blank = lambda x: re.sub(r'[^\n]', ' ', x)
    for a, b in spans:
        code.append(t[prev:a]); com.append(blank(t[prev:a]))
        code.append(blank(t[a:b])); com.append(t[a:b])
        prev = b
    code.append(t[prev:]); com.append(blank(t[prev:]))
    return ''.join(code), ''.join(com)


def donor_rel(f):
    if '/Rt/' in f:
        return None
    if f.startswith('A/'):
        return f
    if f.startswith('B/'):
        return f[2:]
    if f.startswith('Reusable/'):
        return f[len('Reusable/'):]
    return None


class Files:
    def __init__(self, lib, dlib):
        self.lib, self.dlib, self.m, self.dm = lib, dlib, {}, {}

    def get(self, f):
        if f not in self.m:
            t = open(os.path.join(self.lib, f), errors='replace').read()
            code, com = split_code_comment(t)
            self.m[f] = (t, code.split('\n'), com.split('\n'), code)
        return self.m[f]

    def donor_code(self, f):
        dr = donor_rel(f)
        if not dr:
            return None
        if dr not in self.dm:
            p = os.path.join(self.dlib, dr)
            self.dm[dr] = split_code_comment(open(p, errors='replace').read())[0] if os.path.exists(p) else None
        return self.dm[dr]

    def window(self, c, w=60):
        key = (c['file'], c['line'], c['kind'], c['value'], c['vtext'], w)
        memo = self.__dict__.setdefault('_win', {})
        if key in memo and 'line_text' not in c:
            return memo[key]
        t, cl, ml, _ = self.get(c['file'])
        L = (cl if c['kind'] == 'code' else ml)[c['line'] - 1] if c['line'] <= len(cl) else ''
        if 'line_text' in c:
            L = c['line_text']
        out = None
        if ',' in c['vtext']:
            i = L.find(c['vtext'])
            if i >= 0:
                out = L[max(0, i - w):i], c['vtext'], L[i + len(c['vtext']):i + len(c['vtext']) + w]
        for m in NUMRE.finditer(L):
            if ival(m.group(1)) == c['value'] and m.group(1) == c['vtext']:
                out = L[max(0, m.start() - w):m.start()], m.group(1), L[m.end():m.end() + w]
                break
        if out is None:
            for m in NUMRE.finditer(L):
                if ival(m.group(1)) == c['value']:
                    out = L[max(0, m.start() - w):m.start()], m.group(1), L[m.end():m.end() + w]
                    break
        res = out or (L[:w], '?', '')
        if 'line_text' not in c:
            memo[key] = res
        return res


# ----------------------------------------------------------------------------------------------- gate index
def gate_index(runs):
    idx = collections.defaultdict(set)
    for run, pre in (('RA', 'A/'), ('RB', 'B/'), ('RU', 'Reusable/')):
        for l in open(os.path.join(runs, run, 'full.tsv')):
            if l.startswith('#') or l.startswith('verdict\t'):
                continue
            c = l.rstrip('\n').split('\t')
            if len(c) < 12 or not c[5] or not c[6] or not c[11] or not c[10]:
                continue
            try:
                idx[(pre + c[5], int(c[6]), int(c[11], 16))].add(int(c[10], 16))
            except ValueError:
                pass
    return idx


# ----------------------------------------------------------------------------------------------- context
OWNIMG = re.compile(r'images\s+Require\s+(?:Import|Export)\s+([\w ]+)')
DEFV = re.compile(r'\b(?:Definition|Let|Notation)\s+([A-Za-z_][\w\']*)\s*(?::\s*Z\s*)?:=\s*\(?\s*(0x[0-9a-fA-F]+|\d+)\s*\)?\s*\.(?=\s)')
DONOR = {'A': 'dA', 'B': 'dB'}


class Ctx:
    def __init__(self, imgs, files, gidx, judgments, lib):
        self.I, self.files, self.gidx, self.judg, self.lib = imgs, files, gidx, judgments, lib
        self.cat = {k: catalog(I) for k, I in imgs.items()}
        self.hcat = {k: header_catalog(I) for k, I in imgs.items()}
        self.hcat7 = {k: header_catalog(I, 7) for k, I in imgs.items()}
        self._keys, self._tables, self._defs = {}, {}, None

    def okeys(self, f):
        """Our image(s) a file states values of: lib/A -> A, lib/B -> B; a lib/Reusable file by its own `images
        Require` line, else P when it names the plain build's segments (src0), else both ASan builds."""
        if f not in self._keys:
            if f.startswith('A/'):
                k = ['A']
            elif f.startswith('B/'):
                k = ['B']
            else:
                code = self.files.get(f)[3]
                ws = {w for x in OWNIMG.findall(code) for w in x.split()}
                if 'AsanUbsan' in ws and 'Asan' not in ws:
                    k = ['B']
                elif 'Asan' in ws and 'AsanUbsan' not in ws:
                    k = ['A']
                elif 'Plain' in ws or 'src0' in code:
                    k = ['P']
                else:
                    k = ['A', 'B']
            self._keys[f] = k
        return self._keys[f]

    def defs(self):
        """{name: {file: value}} for every `Definition NAME (: Z) := NUMERAL.` of the unit's lib tree."""
        if self._defs is None:
            d = collections.defaultdict(dict)
            for root, _, fs in os.walk(self.lib):
                for fn in fs:
                    if not fn.endswith('.v'):
                        continue
                    rel = os.path.relpath(os.path.join(root, fn), self.lib)
                    for m in DEFV.finditer(self.files.get(rel)[3]):
                        d[m.group(1)][rel] = ival(m.group(2))
            self._defs = d
        return self._defs

    def resolve(self, name, f):
        d = self.defs().get(name)
        if not d:
            return None
        if f in d:
            return d[f]
        top = f.split('/')[0]
        for pick in (lambda k: k.split('/')[0] == top and ('/Rt/' in k) == ('/Rt/' in f), lambda k: k.split('/')[0] == top,
                     lambda k: True):
            vals = {v for k, v in d.items() if pick(k)}
            if len(vals) == 1:
                return vals.pop()
        return None

    def donor_values(self, c):
        s = set(self.gidx.get((c['file'], c['line'], c['value']), ()))
        m = re.search(r'donor (?:field )?\S+ := \(?\s*(0x[0-9a-fA-F]+|\d+)', c['notes'])
        if m:
            s.add(ival(m.group(1)))
        return s


def V(status, rule, quantity='-', expr='-', img='-', rec='-', reason='-'):
    return dict(status=status, rule=rule, quantity=quantity, expr=expr, img=img, rec=rec, reason=reason)


def wtext(ctx, c):
    p, n, q = ctx.files.window(c)
    return p + '\u27e6' + n + '\u27e7' + q


def prio(e):
    return (2 if '.size' in e else 1, len(e)) if e.startswith('sym(') else (0, len(e))


def symkey(I, s):
    lst = I.byname[s.name]
    if len(lst) == 1:
        return f"sym({s.name!r})"
    k = next(i for i, o in enumerate(lst) if o.addr == s.addr and o.size == s.size)
    return f"sym({s.name!r}, {k})"


def cover_obj(I, a, types=('STT_FUNC', 'STT_OBJECT')):
    i = bisect.bisect_right(I.symv, a)
    best = None
    for s in I.syms[max(0, i - 400):i]:
        if s.size and s.addr <= a < s.end and s.typ in types and (best is None or s.size < best.size):
            best = s
    return best


def evalq(I, expr):
    try:
        return I.eval(expr)
    except Exception:
        return None


# ----------------------------------------------------------------------------------------------- rules
def r_manual(ctx, c, generic=False):
    """A hand judgment of judgments.tsv: the first row whose file glob, line, value and name pattern match. Rows for
    a named file (or file glob) are tried before every other rule; rows for any file ('*') after the automatic
    rules, so a pattern judgment never overrides a measured quantity."""
    w = None
    for j in ctx.judg:
        if (j['file'] == '*' or '~' in j['rid']) != generic:
            continue
        if j['value'] != '*' and j['ival'] != c['value']:
            continue
        if j['line'] != '*' and int(j['line']) != c['line']:
            continue
        if j['file'] != '*' and not fnmatch.fnmatch(c['file'], j['file']):
            continue
        if j['name'] != '*':
            if w is None:
                w = c['name'] + ' ' + wtext(ctx, c)
            if not j['rx'].search(w):
                continue
        if j['status'] == 'NOT-IMAGE-DERIVED':
            if generic and j['value'] == '*' and in_image(ctx, c) and '!' not in j['rid']:
                continue
            return V('NOT-IMAGE-DERIVED', 'MANUAL:' + j['rid'], reason=j['reason'])
        img = j['img'] if j['img'] != '*' else ctx.okeys(c['file'])[0]
        expr = j['expr']
        rec = evalq(ctx.I[img], expr)
        if rec is None:
            return V('UNJUDGED', 'MANUAL:' + j['rid'], j['quantity'], expr, img, reason='expression fails: ' + expr)
        return V('SAME' if rec == c['value'] else 'DIFFERS', 'MANUAL:' + j['rid'], j['quantity'], expr, img, rec, j['reason'])
    return None


def in_image(ctx, c):
    """The value lies in [64 KiB, image top] of one of the file's images: it can be an address or size of the image,
    so no pattern judgment (judgments.tsv rows for any file and any value) may call it a model constant."""
    return any(0x10000 <= c['value'] <= ctx.I[k].top for k in ctx.okeys(c['file']))



MKG = re.compile(r'\bmkG\s+((?:(?:0x[0-9a-fA-F]+|\d+)\s+){7}(?:0x[0-9a-fA-F]+|\d+))')


def r_aglobtable(ctx, c):
    """A field of an `mkG beg size size_with_redzone name module dyn loc odr` row of the generated destructor table
    (lib/*/Rt/RtDtorTbl.v): row k of the list must be record k of our asan_globals section, field by field."""
    if not c['file'].endswith('Rt/RtDtorTbl.v') or c['kind'] != 'code':
        return None
    t, cl, ml, code = ctx.files.get(c['file'])
    rows = [(i + 1, m) for i, l in enumerate(cl) for m in MKG.finditer(l)]
    for k, (ln, m) in enumerate(rows):
        if ln != c['line']:
            continue
        vals = [ival(x) for x in m.group(1).split()]
        if c['value'] not in vals:
            continue
        fi = vals.index(c['value'])
        ok = ctx.okeys(c['file'])[0]
        expr = f"q64(sec('asan_globals').lo+64*{k}+{8 * fi})"
        rec = evalq(ctx.I[ok], expr)
        names = ['beg', 'size', 'size_with_redzone', 'name', 'module_name', 'has_dynamic_init', 'location', 'odr_indicator']
        return V('SAME' if rec == c['value'] else 'DIFFERS', 'AGLOBAL-ROW', f'{names[fi]} of asan_globals record {k}', expr, ok, rec,
                 f'row {k} of the generated table against record {k} of our asan_globals section')
    return None


ZCELL = re.compile(r'\bz([1248])\s+\(ANum\s+(0x[0-9a-fA-F]+)\)\s+\u27e6')
ZADDR = re.compile(r'\(ANum\s+\u27e6')


def r_zcell(ctx, c):
    """`zN (ANum ADDR) V` (a start-up memory cell of the generated cell lists): V must be the N-byte little-endian
    content of our image at ADDR (zero in .bss). The numeral ADDR itself is an address, not a count."""
    w = wtext(ctx, c)
    m = ZCELL.search(w)
    ok = ctx.okeys(c['file'])[0]
    if m:
        n, a = int(m.group(1)), ival(m.group(2))
        expr = {1: f'u8({a:#x})', 2: f'u8({a:#x})+256*u8({a + 1:#x})', 4: f'w32({a:#x})', 8: f'q64({a:#x})'}[n]
        O = ctx.I[ok]
        rec = evalq(O, expr)
        if rec is None:
            return None
        if rec == c['value']:
            return V('SAME', 'IMAGE-CELL', f'{n}-byte content of our image at {a:#x}', expr, ok, rec,
                     'the start-up cell holds the image bytes at its address')
        if any(r.lo <= a < r.hi for r in O.loads[2:]):
            return V('NOT-IMAGE-DERIVED', 'START-UP-VALUE',
                     reason=f'a value the start-up code writes into writable memory at {a:#x} ({O.describe(a)}); our image holds '
                            f'{rec:#x} there; the generated cell list records the hand-off memory, not image bytes')
        return V('DIFFERS', 'IMAGE-CELL', f'{n}-byte content of our image at {a:#x}', expr, ok, rec,
                 'a read-only start-up cell must hold the image bytes at its address')
    if ZADDR.search(w):
        return V('NOT-IMAGE-DERIVED', 'CELL-ADDRESS',
                 reason=f'the address of a start-up cell ({ctx.I[ok].describe(c["value"])} in our image); an address the gate checks, not a count')
    return None


AGRANGE = re.compile(r'\(\u27e6[^\u27e7]*\u27e7,\s*(0x[0-9a-fA-F]+)\s*-\s*(0x[0-9a-fA-F]+)\)|CImg\s*\((0x[0-9a-fA-F]+)\s*-\s*\u27e6|\u27e6[^\u27e7]*\u27e7\s*\(CImg\s*\((0x[0-9a-fA-F]+)\s*-')


def r_agrange(ctx, c):
    """`(BEG, END - BEG)` / `CImg (END - BEG)` with BEG the start of an instrumented global: BEG is that asan_globals
    record's beg, and END its beg + size (the object bytes before the redzone)."""
    w = wtext(ctx, c)
    m = AGRANGE.search(w)
    if not m:
        return None
    ok = ctx.okeys(c['file'])[0]
    end = ival(m.group(1) or m.group(3) or m.group(4))
    for k, (b, s, rz) in enumerate(ctx.I[ok].aglobs()):
        if b == c['value'] and abs(b + s - end) < 8:
            return V('SAME', 'AGLOBAL-BEG', f'beg of asan_globals record {k} (its object ends at {end:#x})',
                     f"q64(sec('asan_globals').lo+64*{k})", ok, b, f'record {k}: beg {b:#x}, size {s}')
    return None


def r_chunkfit(ctx, c):
    """A chunk of the generated region list (lib/A/AD2j.v, lib/B/YD2j.v): `mkChunk START (CImg LEN)`, the region's
    `mkRegion None LO HI`: the generator cut the read-only image bytes at the objects the program owns. The check
    measured here is that the chunk is image bytes: [START, START + LEN) lies inside the file-backed part of one
    PT_LOAD of our image."""
    if not re.search(r'[AB]/[AY]D2j\.v$', c['file']):
        return None
    p, n, q = ctx.files.window(c, 80)
    m1 = re.search(r'mkChunk\s+(\d+)\s+\(CImg\s+$', p)
    m2 = re.match(r'\s+\(CImg\s+(\d+)\)', q) if re.search(r'mkChunk\s+$', p) else None
    m3 = re.search(r'mkRegion\s+\S+\s+$', p)
    m4 = re.search(r'mkRegion\s+\S+\s+(\d+)\s+$', p)
    if m1:
        a, l = int(m1.group(1)), c['value']
    elif m2:
        a, l = c['value'], int(m2.group(1))
    elif m3 or m4:
        a, l = (c['value'], 1) if m3 else (int(m4.group(1)), max(1, c['value'] - int(m4.group(1))))
    else:
        return None
    O = ctx.I[ctx.okeys(c['file'])[0]]
    for i, r in enumerate(O.loads):
        if r.lo <= a and a + l <= r.pghi:
            part = ('file-backed part' if a + l <= r.fhi else 'zero-filled part' if a >= r.fhi else 'file-backed and zero-filled parts') + \
                   (' (to its page-rounded end)' if a + l > r.hi else '')
            return V('NOT-IMAGE-DERIVED', 'GEN-CHUNK-FIT',
                     reason=f'a cut of the generated region list (whole file written by the unit generator from our image): '
                            f'[{a:#x}, {a + l:#x}) is image memory, inside the {part} of PT_LOAD {i} ({r.lo:#x}..{r.pghi:#x})')
    return None

BTL = re.compile(r'build_table\s+\w+\s+\(?\s*(0x[0-9a-fA-F]+)\s*\)?\s+\(?\s*(\d+)(?:%nat)?')
RNGL = re.compile(r'\(\s*(0x[0-9a-fA-F]+)\s*,\s*(\d+)%nat\s*\)')


def table_pairs(code):
    out = []
    for rx in (BTL, RNGL):
        for m in rx.finditer(code):
            out.append((m.start(2), ival(m.group(1)), int(m.group(2))))
    return sorted(out)


def funcs(I):
    if not hasattr(I, '_fstart'):
        fs = sorted((s for s in I.syms if s.typ == 'STT_FUNC' and s.size), key=lambda s: (s.addr, -s.size))
        I._fstart, I._fend = collections.defaultdict(list), collections.defaultdict(list)
        for s in fs:
            I._fstart[s.addr].append(s)
            I._fend[s.end].append(s)
    return I


def sdesc(I, S):
    funcs(I)
    if I._fstart.get(S):
        return (symkey(I, I._fstart[S][0]) + '.addr', 0)
    s = cover_obj(I, S, ('STT_FUNC',))
    if s:
        return (symkey(I, s) + '.addr', S - s.addr)
    for n, r in I.secs.items():
        if r.lo == S:
            return (f"sec({n!r}).lo", 0)
    return None


def edesc(I, E):
    funcs(I)
    if I._fend.get(E):
        return (symkey(I, I._fend[E][0]) + '.end', 0)
    if I._fstart.get(E):
        return (symkey(I, I._fstart[E][0]) + '.addr', 0)
    s = cover_obj(I, E - 4, ('STT_FUNC',))
    if s:
        return (symkey(I, s) + '.addr', E - s.addr)
    return None


def dstr(d):
    return d[0] + (f'+{d[1]:#x}' if d[1] else '')


def r_table(ctx, c):
    """A word count of a code table: `build_table SEGS START N` or a `(START, N%nat)` range-list entry. The count
    is the number of 4-byte words from START to the end the DONOR file's own range has: the donor range's two ends
    are named by the donor twin's symbol table (function start / end, or function + offset), the same names give
    the two ends in our image, and N = (end - START) / 4 there. A file without a donor counterpart (lib/*/Rt):
    the range must start and end at our own function bounds (N = size / 4), else it is a chosen prefix."""
    if 't' not in c['src']:
        return None
    f, ok = c['file'], ctx.okeys(c['file'])[0]
    if f not in ctx._tables:
        ours = table_pairs(ctx.files.get(f)[3])
        dc = ctx.files.donor_code(f)
        dons = table_pairs(dc) if dc else []
        lines = [ctx.files.get(f)[3].count('\n', 0, p) + 1 for p, _, _ in ours]
        ctx._tables[f] = (ours, dons if len(dons) == len(ours) else None, lines)
    ours, dons, lines = ctx._tables[f]
    hits = [i for i, (p, S, N) in enumerate(ours) if lines[i] == c['line'] and N == c['value']]
    if not hits:
        return None
    i = hits[0]
    S, N = ours[i][1], ours[i][2]
    O = ctx.I[ok]
    if dons and ok in DONOR:
        D = ctx.I[DONOR[ok]]
        Sd, Nd = dons[i][1], dons[i][2]
        ds, de = sdesc(D, Sd), edesc(D, Sd + 4 * Nd)
        if ds and de:
            so, eo = evalq(O, ds[0]), evalq(O, de[0])
            if so is not None and eo is not None:
                expr = f'(({de[0]}+{de[1]:#x})-({ds[0]}+{ds[1]:#x}))//4'
                rec = evalq(O, expr)
                q = f'words from {dstr(ds)} to {dstr(de)} (the donor range {Sd:#x}+4*{Nd})'
                st = 'SAME' if rec == N else 'DIFFERS'
                return V(st, 'TABLE-DONOR', q, expr, ok, rec,
                         f'donor range {Sd:#x}..{Sd + 4 * Nd:#x} = {dstr(ds)}..{dstr(de)} in the donor twin; our start {S:#x}' +
                         ('' if so + ds[1] == S else f' (the same names give start {so + ds[1]:#x})'))
    ds, de = sdesc(O, S), edesc(O, S + 4 * N)
    if ds and de and ds[1] == 0 and de[1] == 0 and de[0].endswith('.end'):
        expr = f'({de[0]}-{ds[0]})//4'
        return V('SAME', 'TABLE-FUNC', f'words of {ds[0][:-5]} .. {de[0][:-4]} (whole functions)', expr, ok, evalq(O, expr),
                 'the range starts and ends at function bounds of our symbol table')
    if ds and de and de[0].split('.')[0] == ds[0].split('.')[0]:
        sz = evalq(O, ds[0][:-5] + '.size')
        return V('NOT-IMAGE-DERIVED', 'TABLE-PREFIX',
                 reason=f'a chosen part of one function: words {ds[1] // 4}..{ds[1] // 4 + N} of {ds[0][:-5]} '
                        f'({sz} bytes in our image; the part fits: {ds[1] + 4 * N} <= {sz})' if sz and ds[1] + 4 * N <= sz else
                        f'part of {ds[0][:-5]} that does not fit it')
    return None


SECNAME = re.compile(r'(?:tfib|src0|TFIB|SRC0)_(rodata|text|init_array|fini_array|preinit_array|data_rel_ro|got|data|'
                     r'asan_globals|bss|tbss|eh_frame|eh_frame_hdr|img)_(lo|hi)\s*(?::\s*Z\s*)?:=\s*\u27e6', re.I)


def r_secname(ctx, c):
    """A section-bound cell named for its section (`tfib_rodata_hi`, `tfib_got_lo`, `tfib_img_hi` ..): recomputed
    from our pin's section header (img: image base / top), whatever the donor's numeral was."""
    m = SECNAME.search(wtext(ctx, c))
    if not m:
        return None
    sec, end = m.group(1).lower(), m.group(2).lower()
    if sec == 'img':
        expr = 'base' if end == 'lo' else 'top'
    else:
        expr = f"sec({'.' + sec.replace('data_rel_ro', 'data.rel.ro') if sec != 'asan_globals' else 'asan_globals'!r}).{end}"
    ok = ctx.okeys(c['file'])[0]
    rec = evalq(ctx.I[ok], expr)
    if rec is None:
        return None
    return V('SAME' if rec == c['value'] else 'DIFFERS', 'SECTION-BOUND', f'{expr} (section header of our pin)', expr, ok, rec,
             'the cell is named for this section bound')


def r_page(ctx, c):
    if c['value'] != 4096:
        return None
    al = sorted({r.align for k in ctx.okeys(c['file']) for r in ctx.I[k].loads})
    return V('NOT-IMAGE-DERIVED', 'PAGE-SIZE',
             reason=f'4096 is the page size of the model (p_align of every PT_LOAD of our image: {",".join(hex(a) for a in al)})')


def r_anchor(ctx, c):
    """The port MOVED the value consistently: the donor's numeral at the paired place (gate row, or the donor
    file's same-named definition) is quantity Q of the donor image, and ours is the same Q of our image (Q a header
    quantity or form of one, a symbol start / end / size, a descriptor count, or symbol + offset of a symbol of the
    same size)."""
    v = c['value']
    dvs = [d for d in ctx.donor_values(c) if d != v]
    if not dvs or v < 16:
        return None
    res = []
    for ok in ctx.okeys(c['file']):
        dk = DONOR.get(ok)
        if not dk:
            return None
        O, D = ctx.I[ok], ctx.I[dk]
        hit = None
        for dv in dvs:
            common = ctx.cat[dk].get(dv, set()) & ctx.cat[ok].get(v, set())
            if common:
                es = sorted(common, key=prio)
                hit = (es[0], dv, es[1:3])
                break
            hit = map_address(D, O, dv, v)
            if hit:
                hit = (hit, dv, [])
                break
        if not hit:
            return None
        res.append((ok,) + hit)
    ok, e, dv, alt = res[0]
    return V('SAME', 'ANCHOR-MOVED', e + (' (also ' + ', '.join(alt) + ')' if alt else ''), e, '+'.join(r[0] for r in res),
             evalq(ctx.I[ok], e), f'donor numeral {dv:#x} is {e} of the donor image')


QUOT = re.compile(r'(?:change|replace)\s*\(\s*\(?\s*(0x[0-9a-fA-F]+|\d+)\s*\)?\s*(/|\*|-|\+)\s*\(?\s*(0x[0-9a-fA-F]+|\d+)\s*\)?\s*\)\s*with\s*\(?\s*\u27e6')


def r_quotient(ctx, c):
    """`change (X op Y) with N`: N is the arithmetic of the two numerals of the same step. When X is a header
    quantity of our image (image top, a segment end ..), N is that quantity op Y; else both are model constants."""
    w = wtext(ctx, c)
    m = QUOT.search(w)
    if not m:
        return None
    x, op, y = ival(m.group(1)), m.group(2), ival(m.group(3))
    ops = {'/': lambda a, b: a // b, '*': lambda a, b: a * b, '-': lambda a, b: a - b, '+': lambda a, b: a + b}
    ok = ctx.okeys(c['file'])[0]
    hq = sorted(ctx.hcat[ok].get(x, ()), key=len)
    if x >= 0x10000 and hq:
        expr = f'({hq[0]}){"//" if op == "/" else op}{y}'
        rec = evalq(ctx.I[ok], expr)
        return V('SAME' if rec == c['value'] else 'DIFFERS', 'QUOTIENT', f'{hq[0]} {op} {y}', expr, ok, rec,
                 f'the step computes {x:#x} {op} {y}; {x:#x} is {hq[0]} of our image')
    if ops[op](x, y) == c['value']:
        if 0x10000 <= x <= ctx.I[ok].top:
            expr = f'{x:#x}{"//" if op == "/" else op}{y}'
            return V('SAME', 'STEP-ARITH', f'{x:#x} {op} {y} of the step', expr, ok, ops[op](x, y),
                     f'the step computes this from {x:#x}, an address or size inside our image that is its own row')
        return V('NOT-IMAGE-DERIVED', 'LITERAL-ARITH',
                 reason=f'the step computes {x} {op} {y} from numerals that are not addresses or sizes of our image (model constants)')
    return None


def r_ourq(ctx, c):
    """A value of 64 KiB or more that is a header quantity (or a form of one, the shadow address form included) of
    our image, in every image the file states values of, where either no donor numeral pairs with it (OUR-HEADER) or
    the donor numeral is the same value and the same quantity of the donor image (KEPT-HEADER: unchanged quantity)."""
    v = c['value']
    if v < 0x10000:
        return None
    names = None
    for ok in ctx.okeys(c['file']):
        n = set(ctx.hcat7[ok].get(v, ()))
        names = n if names is None else names & n
    if not names:
        return None
    dvs = ctx.donor_values(c) if any(k in DONOR for k in ctx.okeys(c['file'])) else set()
    rule = 'OUR-HEADER'
    if dvs:
        if dvs != {v}:
            return None
        keep = {e for e in names if all(DONOR.get(ok) and evalq(ctx.I[DONOR[ok]], e) == v for ok in ctx.okeys(c['file']))}
        if not keep:
            return None
        names, rule = keep, 'KEPT-HEADER'
    es = sorted(names, key=len)
    e = es[0]
    q = e + (' (also ' + ', '.join(es[1:4]) + ')' if len(es) > 1 else '')
    return V('SAME', rule, q, e, '+'.join(ctx.okeys(c['file'])), evalq(ctx.I[ctx.okeys(c['file'])[0]], e),
             'the value is this header quantity of our image' + (' and the same quantity of the donor image (unchanged)'
                                                                 if rule == 'KEPT-HEADER' else ' (no donor numeral pairs with it)'))

BASE_CTX = re.compile(r'KImg|mkRegion|img_lo|IMG_LO|_lo\s*:=|<=\s*[\w\']+\s*<|\u27e6[^\u27e7]*\u27e7\s*<=\s*\w|in_img|_LO\b')


def r_base(ctx, c):
    """65536 = 0x10000. Written in hex, or in decimal where it stands as a range bound / image low end, it is the
    image base (first PT_LOAD start rounded down to 4096; 0x10000 in all four images). Elsewhere in decimal it is
    2^16 of the model arithmetic."""
    if c['value'] != 0x10000:
        return None
    bases = {ctx.I[k].base for k in ctx.okeys(c['file'])}
    if c['vtext'].lower().startswith('0x') or BASE_CTX.search(wtext(ctx, c)):
        return V('SAME', 'IMAGE-BASE', 'image base (first PT_LOAD start, page-rounded down)', 'base',
                 '+'.join(ctx.okeys(c['file'])), bases.pop() if len(bases) == 1 else '-',
                 'image low end; the same in the donor image')
    return V('NOT-IMAGE-DERIVED', 'POW2-16', reason='65536 written in decimal in model arithmetic (2^16), not a range bound')



SHOFF = 0x7fff8000


def map_address(D, O, dv, v):
    """An expression for our value v when donor value dv is an address (or its ASan shadow address) that the same
    symbol + offset (a symbol of the same size in both images) or the same NUL-terminated .rodata string + offset
    gives in our image; else None."""
    if dv < D.base:
        return None
    if SHOFF + (D.base >> 3) <= dv < SHOFF + (D.top >> 3):
        a0 = (dv - SHOFF) * 8
        for a in range(a0, a0 + 8):
            e = map_address(D, O, a, None)
            if e and evalq(O, e) is not None and (evalq(O, e) >> 3) + SHOFF == v:
                return f'(({e})>>3)+{SHOFF:#x}'
        return None
    s = cover_obj(D, dv)
    if s is not None:
        key = symkey(D, s)
        so = evalq(O, key)
        if so is not None and so.size == s.size and (v is None or so.addr + (dv - s.addr) == v):
            return f'{key}.addr+{dv - s.addr:#x}'
    r = D.secs.get('.rodata')
    if r is not None and r.lo <= dv < r.hi:
        cs = D.cstr_at(dv)
        if cs and len(cs[1]) >= 4:
            starts = O.find_cstr(cs[1])
            off = dv - cs[0]
            for k, st in enumerate(starts):
                if v is None or st + off == v:
                    return f'cstr({cs[1]!r})[{k}]+{off:#x}'
    return None


RNAME = r"(?:ms_\w+\s+B|[A-Za-z_][\w']*)"
REGION_RX = [re.compile(r'\b(' + RNAME + r')\s*<=\s*[\w\']+\s*<=?\s*\1\s*\+\s*\u27e6'),
             re.compile(r'\(\s*(' + RNAME + r')\s*,\s*\1\s*\+\s*\u27e6'),
             re.compile(r'\b(' + RNAME + r')\s*\+\s*\u27e6')]


def r_region(ctx, c):
    """`X <= a < X + N`, `(X, X + N)`, `X + N` where X names an image address (a definition of the unit's lib):
    N is the size of the object at X when X + N is that object's end in our image, else an offset / length inside
    the object (checked to fit)."""
    w = wtext(ctx, c)
    for rx in REGION_RX:
        m = rx.search(w)
        if not m:
            continue
        name = m.group(1).split()[0]
        res = []
        for ok in ctx.okeys(c['file']):
            O = ctx.I[ok]
            x = ctx.resolve(name, c['file'])
            if x is None or not (O.base <= x < O.top):
                return None
            s = cover_obj(O, x)
            if s is None:
                return None
            res.append((ok, x, s))
        ok, x, s = res[0]
        O = ctx.I[ok]
        v = c['value']
        if all(xx == ss.addr and xx + v == ss.end for _, xx, ss in res):
            e = symkey(O, s) + '.size'
            return V('SAME', 'REGION-SIZE', f'size of {s.name} (at {name})', e, '+'.join(r[0] for r in res), evalq(O, e),
                     f'{name} = {x:#x} is the start of {s.name}; {name} + {v} is its end')
        if all(xx + v <= ss.end for _, xx, ss in res):
            return V('NOT-IMAGE-DERIVED', 'FIELD-OFFSET',
                     reason=f'offset {v} from {name} = {x:#x} inside object {s.name} ({s.addr:#x}+{s.size:#x}); it fits in our image')
        return None
    return None


ROLES = [
    ('PC-OFFSET', r'(?:tfib_A_\w+|src0_A_\w+|[A-Z][A-Z0-9_]*_(?:PC|ENTRY|START|RET))\s*\+\s*\u27e6|(?:Lemma|Fact)\s+F\w*_\u27e6|fetch_word\s+\w+\s+\(Z_to_bv 64 \([^)]*\u27e6',
     'offset of an instruction from a named function start (an address; the gate checks the address and the fetched word), not a count'),
    ('SYMSTATE', r'\b(?:SLit|SOff|EVar|ELit|EEreg|HEn\d*|getr regs|ew E|ew Em|Er)\s*\(?\s*\u27e6|escale\s+\d+\s+\(EVar\s+\u27e6',
     'a literal or an index of the symbolic machine state (register number, state variable, symbolic literal), not an image count'),
    ('INDEX', r'\bnth\s+\u27e6|\bnth_error\s+\w+\s+\u27e6|\u27e6[^\u27e7]*\u27e7%(?:bv|nat)\s*(?:=|\)|,)|\bregs\s+\u27e6|\(\s*i\s*<\s*\u27e6',
     'a register number or a list index of the model, not an image count'),
    ('ALIGN', r'\bmod\s+\u27e6|\u27e6[^\u27e7]*\u27e7\s*\*\s*[a-zA-Z(]|[a-zA-Z)]\s*\*\s*\u27e6',
     'an alignment or a scale factor of the model arithmetic, not an image quantity'),
    ('STACK', r'\b(?:SP|sp|sp0|aSP|kStackSpan|ly_top ly|OSP_\w+)\s*-\s*\u27e6|\(\s*-\s*\u27e6|mkRegion\s+\(Some\s+\d+%nat\)\s+\(?-\s*\u27e6',
     'a stack-frame offset or stack window of the model, not an image quantity'),
    ('ALLOC-MODEL', r'(?:kBatch|class_size|class_id|req_size|size_classes|kSpace|kUserMap|kFreeArray|kMaxSize|kPrimResv|kThreadObj|kPtrArray|kNodes|kStore|med_cnt|small_cnt|chunk_atom|mkAF|AStore|cell_in|b_items|usage)[^\u27e6]{0,40}\u27e6|\u27e6[^\u27e7]*\u27e7[^\u27e6]{0,30}(?:kBatch|class_size|req_size|kSpace|kUserMap)',
     'a constant of the sanitizer allocator or musl malloc model (size class, batch, region, field layout), not an image quantity'),
]
ROLES = [(n, re.compile(r), why) for n, r, why in ROLES]


def r_roles(ctx, c):
    w = wtext(ctx, c)
    for n, rx, why in ROLES:
        if rx.search(w):
            return V('NOT-IMAGE-DERIVED', 'ROLE-' + n, reason=why)
    return None


def r_noq(ctx, c):
    """The value is a quantity of neither image: not in the catalog (header quantities and forms, symbol starts /
    ends / sizes and size /4, /8, descriptor counts) of the donor image nor of ours, and no donor numeral differs."""
    v = c['value']
    for ok in ctx.okeys(c['file']):
        if v in ctx.cat[ok]:
            return None
        dk = DONOR.get(ok)
        if dk and v in ctx.cat[dk]:
            return None
        if any(d != v for d in ctx.donor_values(c)):
            return None
    return V('NOT-IMAGE-DERIVED', 'NO-QUANTITY',
             reason='the value is no quantity of our image or of the donor image (header quantities and their /4 /8 /4096 forms, '
                    'symbol starts, ends and sizes, descriptor and entry counts)')


def r_manual_generic(ctx, c):
    return r_manual(ctx, c, generic=True)


PREVNUM = re.compile(r'(0x[0-9a-fA-F]+|\d+)\)?\s*,?\s*\(?\s*(?:CImg\s+)?$')


def r_lenpair(ctx, c):
    """(START, LEN) written next to each other (`CH R a n`, `img_rd_of_mem_ok .. R a n`, `mkChunk a (CImg n)`,
    `(a, n)`): LEN is a length in the image when START and START + LEN are both addresses that the donor's pair
    (paired by the gate) maps to by symbol + offset or by .rodata string + offset: LEN = end - start there."""
    p, n, q = ctx.files.window(c, 80)
    m = PREVNUM.search(p)
    if not m:
        return None
    S = ival(m.group(1))
    ok = ctx.okeys(c['file'])[0]
    dk = DONOR.get(ok)
    O = ctx.I[ok]
    if not dk or not (O.base <= S < O.top) or c['value'] <= 0:
        return None
    D = ctx.I[dk]
    sds = ctx.gidx.get((c['file'], c['line'], S), set()) or {S}
    for dv in ctx.donor_values(c) or {c['value']}:
        for Sd in sds:
            es = map_address(D, O, Sd, S)
            if not es:
                continue
            ee = map_address(D, O, Sd + dv, S + c['value'])
            if not ee:
                e1 = map_address(D, O, Sd + dv - 1, S + c['value'] - 1)
                ee = f'({e1})+1' if e1 else None
            if ee:
                expr = f'({ee})-({es})'
                rec = evalq(O, expr)
                if rec == c['value']:
                    return V('SAME', 'LEN-ANCHOR', f'length from {es} to {ee}', expr, ok, rec,
                             f'the donor pair ({Sd:#x}, {dv}) runs between the same two objects in the donor image')
    return None


GENCHUNK = re.compile(r'\b(R_\w+)\s+\(?(\d+)\)?\s+\u27e6')


def r_genchunk(ctx, c):
    """`.. R_X START LEN`: the pair restates chunk `mkChunk START (CImg LEN)` of region R_X of IMG_REGIONS, the region
    list the unit's generator writes whole from our image (lib/A/AD2j.v, lib/B/YD2j.v); the proof step checks the
    pair against that list by reflexivity."""
    p, n, q = ctx.files.window(c, 80)
    m = GENCHUNK.search(p + '\u27e6')
    ms = re.match(r'\s*(\d+)', q) if re.search(r'\b(R_\w+)\s+$', p) else None
    if not m and not ms:
        return None
    gen = {'A': 'A/AD2j.v', 'B': 'B/YD2j.v'}.get(ctx.okeys(c['file'])[0])
    if not gen:
        return None
    region = m.group(1) if m else re.search(r'\b(R_\w+)\s+$', p).group(1)
    code = ctx.files.get(gen)[3]
    d = re.search(r'Definition ' + re.escape(region) + r' : region :=(.*?)\]\.', code, re.S)
    if not d:
        return None
    for a, l in re.findall(r'mkChunk\s+(\d+)\s+\(CImg\s+(\d+)\)', d.group(1)):
        if m and int(a) == int(m.group(2)):
            st = 'SAME' if int(l) == c['value'] else 'DIFFERS'
            return V(st, 'GEN-CHUNK', f'length of chunk {a} of {region} in IMG_REGIONS ({gen}, generated from our image)', '-',
                     ctx.okeys(c['file'])[0], int(l), f'{gen} {region}: mkChunk {a} (CImg {l})')
        if ms and int(l) == int(ms.group(1)):
            st = 'SAME' if int(a) == c['value'] else 'DIFFERS'
            return V(st, 'GEN-CHUNK', f'start of chunk {a} of {region} in IMG_REGIONS ({gen}, generated from our image)', '-',
                     ctx.okeys(c['file'])[0], int(a), f'{gen} {region}: mkChunk {a} (CImg {l})')
    return None


STEPARITH = re.compile(r'change\s*\(((?:[^()]|\((?:[^()]|\([^()]*\))*\))*)\)\s*with\s*\(?\s*\u27e6')


def r_steparith(ctx, c):
    """`change (EXPR) with N` where EXPR is arithmetic on numerals only: N is that arithmetic. When one of the
    numerals is an address or size inside our image (64 KiB up to the image top), N follows from it (each numeral of
    the step is a candidate row of its own); else EXPR is model arithmetic."""
    p, n, q = ctx.files.window(c, 120)
    m = STEPARITH.search(p + '\u27e6')
    if not m:
        return None
    e = m.group(1)
    if not re.fullmatch(r'[\s()0-9a-fA-Fx+\-*/^]+', e):
        return None
    try:
        val = eval(re.sub(r'/', '//', e.replace('^', '**')), {'__builtins__': {}})
    except Exception:
        return None
    if val != c['value']:
        return None
    ok = ctx.okeys(c['file'])[0]
    O = ctx.I[ok]
    nums = [ival(x) for x in NUMRE.findall(e)]
    if any(0x10000 <= x <= O.top for x in nums):
        return V('SAME', 'STEP-ARITH', f'({e.strip()}) of the step', re.sub(r'/', '//', e.strip()).replace('^', '**'), ok, val,
                 'the step computes this from its own numerals; each of them is judged on its own row')
    return V('NOT-IMAGE-DERIVED', 'LITERAL-ARITH', reason=f'the step computes ({e.strip()}) from numerals that are not image addresses or sizes')


def r_addr(ctx, c):
    """A value inside our image (64 KiB up to the image top) that no other rule settled and that is no quantity of
    the catalog: an address of an instruction or a data byte (a pc where a walk stops, a return site, a cell), which
    the gate's address rows check against the symbol table. It is not a count."""
    v = c['value']
    descs = []
    for ok in ctx.okeys(c['file']):
        O = ctx.I[ok]
        if not (0x10000 <= v < O.top) or any(r.lo <= v < r.pghi for r in O.loads) is False:
            return None
        descs.append(O.describe(v))
    return V('NOT-IMAGE-DERIVED', 'ADDRESS',
             reason=f'an address in our image ({", ".join(descs)}): a pc, return site or data cell, which the gate checks against the symbol table; not a count')


RULES = [r_manual, r_secname, r_table, r_aglobtable, r_zcell, r_agrange, r_page, r_base, r_anchor, r_quotient, r_steparith, r_ourq,
         r_genchunk, r_lenpair, r_chunkfit, r_manual_generic, r_region, r_roles, r_addr, r_noq]


def judge(ctx, c):
    for r in RULES:
        v = r(ctx, c)
        if v:
            return v
    return V('UNJUDGED', 'NONE')


def twin_of(f):
    if f.startswith('A/A'):
        return 'B/Y' + f[3:]
    if f.startswith('B/Y'):
        return 'A/A' + f[3:]
    if f.startswith('A/Rt/'):
        return 'B/Rt/' + f[5:]
    if f.startswith('B/Rt/'):
        return 'A/Rt/' + f[5:]
    return None


def norm_window(ctx, c):
    p, n, q = ctx.files.window(c, 80)
    p, q = (NUMRE.sub('#', re.sub(r'AsanUbsan', 'Asan', x)) for x in (p, q))
    return p[-36:] + '@' + q[:36]


def judge_all(ctx, cands):
    """Pass 1: RULES. Pass 2 (TWIN): an unjudged row of an A file and its B twin (or the reverse) whose text around
    the numeral is the same (numerals masked) as a twin row that a rule settled SAME with an expression: the same
    expression, evaluated in THIS file's image, must give this value (SAME) - else the row stays unjudged."""
    for c in cands:
        c['v'] = judge(ctx, c)
    by = collections.defaultdict(list)
    for c in cands:
        if c['v']['status'] == 'SAME' and c['v']['expr'] not in ('-', ''):
            by[(c['file'], norm_window(ctx, c))].append(c)
    for c in cands:
        if c['v']['status'] != 'UNJUDGED':
            continue
        tf = twin_of(c['file'])
        if not tf:
            continue
        for t in by.get((tf, norm_window(ctx, c)), ()):
            ok = ctx.okeys(c['file'])[0]
            rec = evalq(ctx.I[ok], t['v']['expr'])
            if rec == c['value']:
                c['v'] = V('SAME', 'TWIN', t['v']['quantity'], t['v']['expr'], ok, rec,
                           f"the twin row {tf}:{t['line']} is {t['v']['expr']} ({t['v']['rule']}); the same quantity of this image")
                break
    return cands


JCOLS = ['rid', 'file', 'line', 'value', 'name', 'status', 'quantity', 'expr', 'img', 'reason']


def load_judgments(path):
    out = []
    for l in open(path, encoding='utf-8'):
        if l.startswith('#') or not l.strip():
            continue
        c = l.rstrip('\n').split('\t')
        c += [''] * (len(JCOLS) - len(c))
        j = dict(zip(JCOLS, c))
        j['ival'] = ival(j['value']) if j['value'] != '*' else None
        j['rx'] = re.compile(j['name']) if j['name'] != '*' else None
        out.append(j)
    return out


# ----------------------------------------------------------------------------------------------- output
def load_candidates(path):
    out = []
    for l in open(path, encoding='utf-8'):
        if l.startswith('#'):
            continue
        c = l.rstrip('\n').split('\t')
        out.append(dict(file=c[0], line=int(c[1]), kind=c[2], name=c[3], vtext=c[4], value=int(c[5]), src=c[6],
                        notes=c[7] if len(c) > 7 else ''))
    return out


IMGROLE = {'A': 'fuzz_command.asan', 'B': 'fuzz_command.asan-ubsan', 'P': 'fuzz_command plain',
           'dA': 'cgif_file_fuzzer.asan', 'dB': 'cgif_file_fuzzer.asan-ubsan'}


def command(v):
    if v['status'] in ('SAME', 'DIFFERS'):
        if v['expr'] not in ('-', ''):
            return f'python3 recompute.py --img {v["img"].split("+")[0]} --expr "{v["expr"]}"'
        if v['rule'] == 'GEN-CHUNK':
            return f'python3 recompute.py --chunk "{v["reason"]}"'
    return '-'


def read_by(ctx, c, lib):
    """The first statement or definition, in the unit's lib/, that uses the name the numeral is defined under (a
    `Definition NAME` line), else '-' (the numeral stands inside a statement or proof: its own line uses it)."""
    t, cl, ml, code = ctx.files.get(c['file'])
    m = re.search(r'\b(?:Definition|Let|Notation)\s+([A-Za-z_][\w\']*)[^:=]*(?::[^=]*)?:=[^.]*$', cl[c['line'] - 1][:200])
    if not m:
        return 'lib/' + c['file'] + ':' + str(c['line']) + ' (its own statement)'
    name = m.group(1)
    rx = re.compile(r'(?<![\w\'.])' + re.escape(name) + r'(?![\w\'])')
    for root, _, fs in sorted(os.walk(lib)):
        for fn in sorted(fs):
            if not fn.endswith('.v'):
                continue
            rel = os.path.relpath(os.path.join(root, fn), lib)
            for i, l in enumerate(ctx.files.get(rel)[1]):
                if rx.search(l) and not (rel == c['file'] and i + 1 == c['line']):
                    return f'lib/{rel}:{i + 1}'
    return '-'


def controls(ctx, cands):
    """Known-answer controls. Value-checking rules (a row recomputed SAME): the row re-judged with value + 4 must be
    refused (it differs from the recomputed quantity), and re-judged with the donor's numeral, where that differs,
    must be refused too (else the quantity has one value in both images and the row is uninformative). Pattern
    rules (NOT-IMAGE-DERIVED): the same rule is re-run on the line with the numeral replaced by value + 4; a rule
    that still settles it is a context rule (it reads the slot, not the value)."""
    rows = collections.defaultdict(lambda: collections.Counter())
    for c in cands:
        v = c['v']
        r = v['rule'].split(':')[0] + (':' + v['rule'].split(':')[1] if v['rule'].startswith('MANUAL') else '')
        rows[r]['rows'] += 1
        if v['status'] == 'SAME' and isinstance(v['rec'], int):
            rows[r]['plus4_refused' if c['value'] + 4 != v['rec'] else 'plus4_accepted'] += 1
            dvs = [d for d in ctx.donor_values(c) if d != c['value']]
            if not dvs:
                rows[r]['donor_value_same_or_absent'] += 1
            elif all(d != v['rec'] for d in dvs):
                rows[r]['donor_value_refused'] += 1
            else:
                rows[r]['donor_value_accepted'] += 1
        elif v['status'] == 'NOT-IMAGE-DERIVED':
            t, cl, ml, _ = ctx.files.get(c['file'])
            L = (cl if c['kind'] == 'code' else ml)[c['line'] - 1]
            p, n, q = ctx.files.window(c, 10 ** 6)
            newv = c['value'] + 4
            nt = hex(newv) if c['vtext'].lower().startswith('0x') else str(newv)
            c2 = dict(c, value=newv, vtext=nt, line_text=p + nt + q)
            fn = {'PAGE-SIZE': r_page, 'POW2-16': r_base, 'NO-QUANTITY': r_noq, 'FIELD-OFFSET': r_region,
                  'TABLE-PREFIX': None, 'LITERAL-ARITH': r_steparith}.get(v['rule'])
            if v['rule'].startswith('ROLE-'):
                fn = r_roles
            elif v['rule'].startswith('MANUAL'):
                fn = r_manual_generic if any(j['rid'] == v['rule'][7:] and (j['file'] == '*' or '~' in j['rid'])
                                             for j in ctx.judg) else r_manual
            elif v['rule'] in ('START-UP-VALUE', 'CELL-ADDRESS'):
                fn = r_zcell
            elif v['rule'] == 'GEN-CHUNK-FIT':
                fn = r_chunkfit
            got = fn(ctx, c2) if fn else None
            same = bool(got) and got['rule'] == v['rule'] and got['status'] == 'NOT-IMAGE-DERIVED'
            rows[r]['plus4_context_rule' if same else 'plus4_refused'] += 1
    return rows


def main():
    a = sys.argv[1:]
    if '--expr' in a or '--chunk' in a:
        if '--chunk' in a:
            spec = a[a.index('--chunk') + 1]
            gen, region, rest = re.match(r'(\S+) (R_\w+): mkChunk (\d+)', spec).groups()
            lib = os.environ.get('LIB', os.path.join(HERE, 'lib'))
            code = split_code_comment(open(os.path.join(lib, gen)).read())[0]
            d = re.search(r'Definition ' + region + r' : region :=(.*?)\]\.', code, re.S)
            print(dict(re.findall(r'mkChunk\s+(\d+)\s+\(CImg\s+(\d+)\)', d.group(1))).get(rest))
            return
        key, expr = a[a.index('--img') + 1], a[a.index('--expr') + 1]
        rest = [x for i, x in enumerate(a) if x not in ('--img', '--expr') and a[i - 1] not in ('--img', '--expr')]
        imgd, plaind = (rest + [os.path.join(HERE, 'img'), os.path.join(HERE, 'img')])[:2]
        I = load_images(imgd, plaind)[key]
        v = I.eval(expr)
        print(f'{v} ({v:#x})' if isinstance(v, int) else v, f'[{IMGROLE[key]} {I.sha[:12]}]')
        return
    lib, dlib, runs, imgd, plaind = a[:5]
    imgs = load_images(imgd, plaind)
    files = Files(lib, dlib)
    ctx = Ctx(imgs, files, gate_index(runs), load_judgments(os.path.join(HERE, 'judgments.tsv')), lib)
    cands = load_candidates(os.path.join(HERE, 'candidates.tsv'))
    judge_all(ctx, cands)
    with open(os.path.join(HERE, 'counts.tsv'), 'w', encoding='utf-8') as o, \
            open(os.path.join(HERE, 'recompute.log'), 'w', encoding='utf-8') as lg:
        o.write('#file\tline\tname\tvalue_in_file\tquantity\trecomputed\tcommand\tstatus\tkind\tread_by\n')
        for k, I in imgs.items():
            lg.write(f'# image {k}: {IMGROLE[k]} pin {I.sha[:12]} twin {I.twin_sha[:12]}\n')
        for c in cands:
            v = c['v']
            st = v['status']
            if st in ('SAME', 'DIFFERS'):
                quantity = f"{v['quantity']} [{v['rule']}; {v['reason']}]"
                rec = v['rec'] if isinstance(v['rec'], str) else f"{v['rec']} ({v['rec']:#x})"
                imgk = v['img'].split('+')[0]
                lg.write(f"lib/{c['file']}:{c['line']} {c['name']} {c['vtext']} = {v['expr']} -> {rec} "
                         f"[{'+'.join(IMGROLE.get(x, x) + ' ' + imgs[x].sha[:12] for x in v['img'].split('+') if x in imgs)}] {st}\n")
            else:
                quantity = f"{v['rule']}: {v['reason']}"
                rec = '-'
            rb = read_by(ctx, c, lib) if st == 'DIFFERS' else '-'
            o.write('\t'.join([f"lib/{c['file']}", str(c['line']), c['name'], c['vtext'], quantity.replace('\t', ' '), str(rec),
                               command(v), st, c['kind'], rb]) + '\n')
    ctl = controls(ctx, cands)
    keys = ['rows', 'plus4_refused', 'plus4_accepted', 'donor_value_refused', 'donor_value_accepted',
            'donor_value_same_or_absent', 'plus4_context_rule']
    with open(os.path.join(HERE, 'controls.tsv'), 'w') as o:
        o.write('#rule\t' + '\t'.join(keys) + '\n')
        for r in sorted(ctl, key=lambda r: -ctl[r]['rows']):
            o.write(r + '\t' + '\t'.join(str(ctl[r][k]) for k in keys) + '\n')
    cnt = collections.Counter(c['v']['status'] for c in cands)
    print('candidates', len(cands), dict(cnt))
    print('by rule', dict(collections.Counter(c['v']['rule'].split(':')[0] for c in cands)))


if __name__ == '__main__':
    main()
