#!/usr/bin/env python3
"""Enumerate every candidate image-derived count of the relocated core of plugin-hostd/fuzz_command.

Sources (a row may come from several; the `sources` column lists them):
  a  gate rows (port_addr_check 3d2eee813cce runs RA, RB, RU): src_class GEOM or EXTENT; verdict SAME-GEOMETRY,
     GEOMETRY-CHANGED, ROUND-CONSTANT-SAME, IMAGE-EXTENT-*; NON-ADDRESS-CHANGED with a value >= 2 (the port changed a
     non-address value); NON-ADDRESS-SAME whose value is a donor quantity that differs in our image (see c).
  b  a Definition / Let / Notation / record field whose name says count, len, length, size, n, num, words, pages,
     bytes, top, end, hi, lo, span, cap, bound (name parts split at `_` and case changes) with a literal value.
     Symbol cells *_A_SYM / *_E_SYM / *_D_SYM are left out (addresses the gate's named-symbol rule checks against
     the symbol table, not counts).
  c  any numeral (code or comment) equal to a quantity of the DONOR image of the file's build whose value in OUR
     image is different (or absent): header quantities (PT_LOAD / TLS / RELRO / EH_FRAME / section bounds and
     sizes, image top and spans) as such, /4, /8, >>3, /4096 and ceil /4096; object and function sizes from the
     donor twin's symtab as such, /4, /8; descriptor / entry counts (asan_globals / 64, .got / 8, .init_array / 8,
     .fini_array / 8). Powers of two are left to sources a, b, d, e; a header value from 16 to 255 and the descriptor
     count are taken only with a count word within 40 characters, a symbol size only from 256 up (see hazards()).
  d  a numeral in a comment next to a count word (instructions, insns, words, bytes, pages, entries, descriptors,
     globals, cells, slots, functions, symbols, rows, elements, traces).
  e  a literal length of a region over a named image object (`X <= a < X + N`, `(X, X + N)`, `(X, N)`,
     `img_covered rs X N`), and the right side of `change (..) with N` where the left side divides by 4, 8, 4096 or
     shifts.
  t  the word count N of every code table range: `build_table SEGS START N` and `(START, N%nat)` range-list entries.
  s  (lib/A/A*.v and lib/B/Y*.v) every numeral of 64 KiB or more equal to a section bound, a PT_LOAD / TLS / RELRO /
     PT_PHDR / EH_FRAME bound, the image base or the image top of our image or of the donor image of the build.

lib/Reusable/YH03.v is left out (a file another check owns).

Output: candidates.tsv (one row per file, line, kind, value; header line starts with #).
Run: python3 enumerate.py LIB DONOR_LIB RUNS_DIR IMG_DIR OUT
"""
import collections
import glob
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import imgq  # noqa: E402

LIB, DLIB, RUNS, IMGD, OUT = sys.argv[1:6]
SKIP = {'Reusable/YH03.v'}
BTL = re.compile(r'build_table\s+\w+\s+\(?\s*(0x[0-9a-fA-F]+)\s*\)?\s+\(?\s*(\d+)(?:%nat)?')
RNGL = re.compile(r'\(\s*(0x[0-9a-fA-F]+)\s*,\s*(\d+)%nat\s*\)')
BOUNDS = {}


def bounds(I):
    b = collections.defaultdict(set)
    for i, r in enumerate(I.loads):
        for fld in ('lo', 'hi', 'fhi', 'pglo', 'pghi'):
            b[getattr(r, fld)].add(f'seg({i}).{fld}')
    for nm in ('tls', 'relro', 'ehfh', 'phdr'):
        r = getattr(I, nm)
        if r is None:
            continue
        for fld in ('lo', 'hi', 'pglo', 'pghi'):
            b[getattr(r, fld)].add(f'{nm}.{fld}')
    for n, r in I.secs.items():
        b[r.lo].add(f"sec({n!r}).lo")
        b[r.hi].add(f"sec({n!r}).hi")
    b[I.top].add('top')
    b[I.base].add('base')
    return b


# ------------------------------------------------------------------ files and text
def target_files():
    fs = []
    for pat in ('A/A*.v', 'B/Y*.v', 'A/Rt/*.v', 'B/Rt/*.v', 'Reusable/*.v', 'Reusable/*/*.v'):
        fs += sorted(os.path.relpath(p, LIB) for p in glob.glob(os.path.join(LIB, pat)))
    return [f for f in fs if f not in SKIP]


def donor_rel(f):
    if f.startswith('A/Rt/') or f.startswith('B/Rt/'):
        return None
    if f.startswith('A/'):
        return f
    if f.startswith('B/'):
        return f[2:]
    if f.startswith('Reusable/'):
        return f[len('Reusable/'):]
    return None


def sides(f):
    if f.startswith('A/'):
        return ['A']
    if f.startswith('B/'):
        return ['B']
    return ['A', 'B']


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


class FileText:
    def __init__(self, path):
        self.text = open(path, errors='replace').read()
        self.code, self.com = split_code_comment(self.text)
        self.nl = [m.start() for m in re.finditer('\n', self.text)]
        self.lines = self.text.split('\n')
        self.codelines = self.code.split('\n')
        self.decls = [(m.start(), m.group(2) or m.group(1)) for m in DECL.finditer(self.code)]
        self.declpos = [d[0] for d in self.decls]

    def line(self, pos):
        import bisect
        return bisect.bisect_left(self.nl, pos) + 1

    def decl_at(self, pos):
        import bisect
        i = bisect.bisect_right(self.declpos, pos) - 1
        return self.decls[i][1] if i >= 0 else '-'


DECL = re.compile(r'(?m)(?:^|(?<=\.)\s)\s*(?:#\[[^\]]*\]\s*)?(?:Local |Global |Program )?'
                  r'(Definition|Lemma|Theorem|Fact|Corollary|Remark|Example|Let|Fixpoint|Record|Inductive|Notation|'
                  r'Hypothesis|Hypotheses|Variable|Variables|Instance|Axiom|Parameter|Goal|Ltac|Section|Module|Class|Structure)'
                  r'\s+([A-Za-z_][\w\']*)?')
NUM = r'(?:0x[0-9a-fA-F]+|\d+)'
NUMRE = re.compile(r'(?<![\w.\'])(0x[0-9a-fA-F]+|\d+)(?![\w\'])')


def ival(s):
    return int(s, 16) if s.lower().startswith('0x') else int(s)


# ------------------------------------------------------------------ (b) named literal definitions
DEFRE = re.compile(r'\b(?:Definition|Let|Notation|Local Definition|Local Notation|Global Definition)\s+'
                   r'([A-Za-z_][\w\']*)((?:[^.]|\.(?!\s))*?):=\s*((?:[^.]|\.(?=[A-Za-z0-9_]))*?)\.(?=\s|$)', re.S)
FIELDRE = re.compile(r'(?<![\w\'])([A-Za-z_][\w\']*)\s*:=\s*(\(?\s*' + NUM + r'(?:%[A-Za-z]+)?\s*\)?)\s*(?=[;|}])')
SCOPE = r'(?:%(?:Z|N|nat|bv|positive|word))'
EXPR_OK = re.compile(r'^(?:\s|\(|\)|' + NUM + SCOPE + r'?|[-+*/^]|\b(?:Z|N)\.(?:of_nat|to_nat|of_N|shiftl|shiftr|pow|div|mul|add|sub)\b'
                     r'|\bmod\b|\bdiv\b|:\s*(?:Z|N|nat|word)\b)*$')
SYMCELL = re.compile(r'^[A-Za-z0-9]*_(?:A|E|D|RA)_')
KWPART = re.compile(r'(?:n|num)?(count|cnt|len|length|size|sz|num|words?|pages?|bytes?|top|end|hi|lo|span|cap|bound)s?')


def name_parts(nm):
    s = re.sub(r'([a-z0-9])([A-Z])', r'\1_\2', nm)
    return [p for p in re.split(r"[_']+", s) if p]


def name_hit(nm):
    if SYMCELL.match(nm):
        return False
    for p in name_parts(nm):
        pl = p.lower()
        if pl == 'n' or KWPART.fullmatch(pl):
            return True
        if len(pl) > 4 and re.search(r'(count|len|length|size|words|pages|bytes|span|top|end)$', pl):
            return True
    return False


# ------------------------------------------------------------------ (c) donor quantities that differ in our image
def header_q(I):
    q = {}
    for i, r in enumerate(I.loads):
        for fld in ('lo', 'memsz', 'filesz', 'hi', 'fhi', 'pglo', 'pghi'):
            q[f'seg({i}).{fld}'] = getattr(r, fld)
        q[f'seg({i}).pghi-seg({i}).pglo'] = r.pghi - r.pglo
        q[f'seg({i}).pghi-seg({i}).lo'] = r.pghi - r.lo
    for nm in ('tls', 'relro', 'ehfh'):
        r = getattr(I, nm)
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


HFORMS = [('', lambda v: v), ('/4', lambda v: v // 4 if v % 4 == 0 else None),
          ('/8', lambda v: v // 8 if v % 8 == 0 else None),
          ('>>3', lambda v: v >> 3 if v >= 0x10000 and v % 8 else None),
          ('/4096', lambda v: v // 4096 if v % 4096 == 0 else None),
          ('ceil/4096', lambda v: -(-v // 4096) if v % 4096 else None)]
SFORMS = HFORMS[:3]


def sym_sizes(I):
    q = {}
    for name, lst in I.byname.items():
        for k, s in enumerate(lst):
            if s.typ in ('STT_FUNC', 'STT_OBJECT') and s.size:
                q[(f"sym('{name}')" if len(lst) == 1 else f"sym('{name}', {k})") + '.size'] = s.size
    return q


def hazards(D, O):
    """{value: [(description, needs_context)]} for donor quantities whose value in our image differs or is absent.
    Header quantities (and their /4, /8, >>3, /4096, ceil /4096 forms) from 256 up, and object / function sizes
    (and their /4, /8 forms) from 256 up, are taken wherever they stand. A header-quantity value from 16 to 255, and
    the asan_globals descriptor count, are taken only where a count word stands within 40 characters of the numeral
    (SMALL_CTX / GLOB_CTX). Smaller symbol-size values are not taken (a function or object size under 256 bytes
    equals some numeral of almost every file by chance)."""
    H = collections.defaultdict(list)
    for qd, qo, forms, minv in ((header_q(D), header_q(O), HFORMS, 16), (sym_sizes(D), sym_sizes(O), SFORMS, 256)):
        for name, dv in qd.items():
            ov = qo.get(name)
            for fn, f in forms:
                fv = f(dv)
                if fv is None or fv < minv or (fv & (fv - 1)) == 0:
                    continue
                fo = f(ov) if ov is not None else None
                if fo == fv:
                    continue
                H[fv].append((f'{name}{fn}: donor {fv:#x}, ours ' + (f'{fo:#x}' if fo is not None else 'absent'),
                              'count' if fv < 256 else None))
    for nm, sz, secn in (('asan_globals', 64, 'asan_globals'), ('.got', 8, '.got'), ('.init_array', 8, '.init_array'),
                         ('.fini_array', 8, '.fini_array')):
        dv, ov = D.secs[secn].size // sz, O.secs[secn].size // sz
        if dv != ov and dv >= 2:
            H[dv].append((f"sec('{secn}').size/{sz}: donor {dv}, ours {ov}", 'glob' if secn == 'asan_globals' else 'count'))
    return H


SMALL_CTX = re.compile(r'(?i)count|cnt|_len\b|length|size|words|pages|insn|instr|entries|nth\b|firstn|skipn|repeat|'
                       r'\bseq\b|glob|descr|span|bytes')
GLOB_CTX = re.compile(r'(?i)glob|descr')


def hz_take(hz, window):
    """The hazard descriptions of a value that apply here: context-gated ones need their word in `window` (the
    40 characters on each side of the numeral)."""
    out = []
    for d, need in hz:
        if need is None or (need == 'count' and SMALL_CTX.search(window)) or (need == 'glob' and GLOB_CTX.search(window)):
            out.append(d)
    return out


def window(text, a, b, w=40):
    return text[max(0, a - w):b + w]


# ------------------------------------------------------------------ (d) comment count phrases
COUNTWORD = r'(?:instructions?|insns?|words?|bytes?|pages?|entries|entry|descriptors?|globals?|cells?|slots?|functions?|symbols?|rows?|elements?|traces?|quads?|dwords?)'
COMRE = re.compile(r'(?<![\w.\'])(0x[0-9a-fA-F]+|\d[\d,]*)\s*(?:-\s*|\s)?(?:[A-Za-z_]+\s)?' + COUNTWORD + r'\b'
                   r'|\b' + COUNTWORD + r'\s*(?:=|:|count|of)\s*(0x[0-9a-fA-F]+|\d[\d,]*)(?![\w.])', re.I)

# ------------------------------------------------------------------ (e) region lengths over image objects, change .. with
# NAME: an ms_* table of the lib shape, a *_D_* / *_A_* cell, an ALL-CAPS image name, or a src0_ / tfib_ name
RNAME = r"(?:ms_\w+\s+B|\w+_[DA]_\w+|[A-Z][A-Z0-9_]{1,}|(?:src0|tfib|tf)_\w+)"
REGIONS = [
    re.compile(r'\b(' + RNAME + r')\s*<=\s*[\w\']+\s*<=?\s*\1\s*\+\s*(' + NUM + r')\b(?!\s*[*/])'),   # X <= a < X + N
    re.compile(r'\(\s*(' + RNAME + r')\s*,\s*\1\s*\+\s*(' + NUM + r')\s*\)'),                         # (X, X + N)
    re.compile(r'\(\s*(' + RNAME + r')\s*,\s*(' + NUM + r')\s*\)'),                                   # (X, N)
    re.compile(r'\bimg_covered\s+\w+\s+\(?(' + RNAME + r')\)?\s+\(?(' + NUM + r')\b'),                 # img_covered rs X N
]
CHANGE = re.compile(r'\bchange\s*\(((?:[^()]|\([^()]*\))*)\)\s*with\s*\(?\s*(' + NUM + r')\b', re.S)
QUOT = re.compile(r'/\s*(?:4|8|4096|0x1000)\b|shiftr|>>|Z\.div|/\s*\(')

# ------------------------------------------------------------------ (a) gate rows
GV = {'SAME-GEOMETRY', 'GEOMETRY-CHANGED', 'ROUND-CONSTANT-SAME', 'IMAGE-EXTENT-SAME', 'IMAGE-EXTENT-CHANGED'}
RUNDIR = {'RA': 'A/', 'RB': 'B/', 'RU': 'Reusable/'}


def gate_rows(H):
    out = collections.defaultdict(list)
    for run, pre in RUNDIR.items():
        side = 'A' if run == 'RA' else 'B'
        for l in open(os.path.join(RUNS, run, 'full.tsv')):
            if l.startswith('#') or l.startswith('verdict\t'):
                continue
            c = l.rstrip('\n').split('\t') + [''] * 16
            verdict, dst_file, dst_line, dv, sv, scls = c[0], c[5], c[6], c[11], c[10], c[12]
            if not dst_file or not dst_line or not dv:
                continue
            try:
                v = int(dv, 16)
            except ValueError:
                continue
            take = scls in ('GEOM', 'EXTENT') or verdict in GV
            if verdict == 'NON-ADDRESS-CHANGED' and v >= 2:
                take = True
            if not take and verdict == 'NON-ADDRESS-SAME' and v in H[side]:
                take = 'hz'
            if take:
                out[(pre + dst_file, int(dst_line), v)].append((run, verdict, sv, scls, c[13][:160], c[15][:200], c[7], take, side))
    return out


def main():
    imgs = {k: imgq.Img(os.path.join(IMGD, f'{v}.pin'), os.path.join(IMGD, f'{v}.twin'), k)
            for k, v in (('dA', 'cgif.A'), ('dB', 'cgif.B'), ('oA', 'cmd.A'), ('oB', 'cmd.B'))}
    H = {'A': hazards(imgs['dA'], imgs['oA']), 'B': hazards(imgs['dB'], imgs['oB'])}
    for side in ('A', 'B'):
        b = bounds(imgs['o' + side])
        for v, n in bounds(imgs['d' + side]).items():
            b[v] |= {x + ' (donor)' for x in n}
        BOUNDS[side] = b
    G = gate_rows(H)
    GF = collections.defaultdict(list)
    for (gf, gl, gv), lst in G.items():
        GF[gf].append((gl, gv, lst))
    files = target_files()
    cands = collections.OrderedDict()

    def add(f, line, kind, name, vtext, v, src, note=''):
        k = (f, line, kind, v)
        if k not in cands:
            cands[k] = dict(file=f, line=line, kind=kind, name=name, vtext=vtext, value=v, src=set(), notes=[])
        cands[k]['src'].add(src)
        if note and note not in cands[k]['notes']:
            cands[k]['notes'].append(note)

    donor_defs = {}
    for f in files:
        ft = FileText(os.path.join(LIB, f))
        dr = donor_rel(f)
        dtext = None
        if dr and os.path.exists(os.path.join(DLIB, dr)):
            dtext = split_code_comment(open(os.path.join(DLIB, dr), errors='replace').read())[0]
        dd = {}
        if dtext:
            for m in DEFRE.finditer(dtext):
                dd.setdefault(m.group(1), ' '.join(m.group(3).split()))
            for m in FIELDRE.finditer(dtext):
                dd.setdefault(m.group(1), m.group(2).strip())
        donor_defs[f] = dd
        # (b)
        for m in DEFRE.finditer(ft.code):
            nm, rhs = m.group(1), m.group(3)
            if not re.search(NUM, rhs) or not EXPR_OK.match(rhs) or not name_hit(nm):
                continue
            for n in NUMRE.finditer(rhs):
                pos = m.start(3) + n.start()
                add(f, ft.line(pos), 'code', nm, n.group(1), ival(n.group(1)), 'b',
                    'donor ' + nm + ' := ' + dd[nm] if nm in dd else 'donor: no definition ' + nm)
        for m in FIELDRE.finditer(ft.code):
            nm = m.group(1)
            if not name_hit(nm):
                continue
            n = NUMRE.search(m.group(2))
            if not n:
                continue
            pos = m.start(2) + n.start()
            add(f, ft.line(pos), 'code', nm, n.group(1), ival(n.group(1)), 'b',
                'donor field ' + nm + ' := ' + dd[nm] if nm in dd else '')
        # (c) and (d)
        for kind, txt in (('code', ft.code), ('comment', ft.com)):
            for n in NUMRE.finditer(txt):
                v = ival(n.group(1))
                raw = [h for sd in sides(f) for h in H[sd].get(v, ())]
                if not raw:
                    continue
                ln = ft.line(n.start())
                hz = hz_take(raw, window(txt, n.start(), n.end()))
                if hz:
                    add(f, ln, kind, ft.decl_at(n.start()) if kind == 'code' else '(comment)',
                        n.group(1), v, 'c', '; '.join(hz[:3]))
        for n in COMRE.finditer(ft.com):
            s = n.group(1) or n.group(2)
            s2 = s.replace(',', '')
            try:
                v = ival(s2)
            except ValueError:
                continue
            if v < 2:
                continue
            pos = n.start(1) if n.group(1) else n.start(2)
            add(f, ft.line(pos), 'comment', '(comment)', s, v, 'd', 'comment: ' + ' '.join(n.group(0).split())[:80])
        # (e)
        for rx in REGIONS:
            for m in rx.finditer(ft.code):
                base, s = m.group(1), m.group(2)
                v = ival(s)
                if v < 2:
                    continue
                pos = m.start(2)
                add(f, ft.line(pos), 'code', ft.decl_at(pos), s, v, 'e', 'region length over ' + ' '.join(base.split()))
        for m in CHANGE.finditer(ft.code):
            if not QUOT.search(m.group(1)):
                continue
            v = ival(m.group(2))
            add(f, ft.line(m.start(2)), 'code', ft.decl_at(m.start(2)), m.group(2), v, 'e',
                'change (' + ' '.join(m.group(1).split())[:60] + ') with')
        # (t) word counts of code tables: build_table SEGS START N, (START, N%nat) range-list entries
        for rx in (BTL, RNGL):
            for m in rx.finditer(ft.code):
                pos = m.start(2)
                add(f, ft.line(pos), 'code', ft.decl_at(pos), m.group(2), int(m.group(2)), 't', f'table range start {m.group(1)}')
        # (s) section / segment bound values (lib/A/A*.v, lib/B/Y*.v): a numeral of 64 KiB or more equal to a section or
        # PT_LOAD / TLS / RELRO bound, the image base or top of our image or of the donor image of the build
        if re.match(r'[AB]/[AY]', f):
            side = 'A' if f.startswith('A/') else 'B'
            for n in NUMRE.finditer(ft.code):
                v = ival(n.group(1))
                if v >= 0x10000 and v in BOUNDS[side]:
                    add(f, ft.line(n.start()), 'code', ft.decl_at(n.start()), n.group(1), v, 's',
                        'bound value: ' + ', '.join(sorted(BOUNDS[side][v])[:2]))
        # (a) gate rows of this file
        for gl, gv, lst in GF.get(f, ()):
            ln = ft.lines[gl - 1] if 0 < gl <= len(ft.lines) else ''
            vt = next((t for t in NUMRE.findall(ft.codelines[gl - 1]) if ival(t) == gv), None) if 0 < gl <= len(ft.lines) else None
            kind = 'code'
            if vt is None:
                vt = next((t for t in NUMRE.findall(ln) if ival(t) == gv), hex(gv))
            run, verdict, sv, scls, sres, note, sent, take, side = lst[0]
            if take == 'hz' and all(x[7] == 'hz' for x in lst):
                cl = ft.codelines[gl - 1] if 0 < gl <= len(ft.lines) else ''
                wins = [window(cl, m.start(), m.end()) for m in NUMRE.finditer(cl) if ival(m.group(1)) == gv]
                if not any(hz_take(H[side][gv], w) for w in wins):
                    continue
            vs = sorted({x[1] for x in lst})
            add(f, gl, kind, sent, vt, gv, 'a', f'gate {"/".join(vs)} src {sv or "-"} {scls}: {sres}')
    cols = ['file', 'line', 'kind', 'name', 'value_text', 'value', 'sources', 'notes']
    with open(OUT, 'w') as o:
        o.write('#' + '\t'.join(cols) + '\n')
        for c in sorted(cands.values(), key=lambda c: (c['file'], c['line'], c['kind'], c['value'])):
            o.write('\t'.join([c['file'], str(c['line']), c['kind'], c['name'].replace('\t', ' '), c['vtext'], str(c['value']),
                               ''.join(sorted(c['src'])), ' | '.join(c['notes']).replace('\t', ' ')]) + '\n')
    cnt = collections.Counter(''.join(sorted(c['src'])) for c in cands.values())
    print('candidates', len(cands), dict(sorted(cnt.items())))
    by = collections.Counter(s for c in cands.values() for s in c['src'])
    print('by source', dict(sorted(by.items())))


if __name__ == '__main__':
    main()
