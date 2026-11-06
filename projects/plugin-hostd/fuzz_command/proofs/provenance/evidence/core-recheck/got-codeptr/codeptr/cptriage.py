#!/usr/bin/env python3
"""cptriage.py - a measured reason for every literal codeptr 12348302dfd2 flags on fuzz_command's start-up / table
files (codeptr-{A,B}.out), and for every literal cplimit.py lists (the H13 rows codeptr does not judge).

Run from the directory codeptr-run.sh uses (ours/, cgif/, img/):
  cptriage.py --out codeptr-triage.tsv [--control codeptr-controls.out]

Each occurrence of the value in our file is given a ROLE from the file's own text, and the role's fact is measured:
  IDENT       the hex digits are part of an identifier (codeptr's literal pattern has no left word boundary); the
              same identifier in the donor's files of both images shows it is a name, not an address of either
  INSN-FIELD  the number is a field of the decoded instruction in `decode_any (W%bv : bv 32) = Some (Op .. v ..)`;
              the field is recomputed from W
  INSN-WORD   the number is a 32-bit instruction word `(W%bv : bv 32)`; where the file fetches it at a literal address
              (`fetch_word S (Z_to_bv 64 A) = Some (W%bv ...)`) our image holds W at A
  K-LENGTH    the length operand `(ELit v)` of a KZero / KFill write, or the value of a KWord write `|} n (ELit v)`
  K-RANGE     a bound of `KRange (EVar k) lo hi`
  CELL-VALUE  `z8 (ANum A) v` / `KWord {| a_base := ELit 0; a_off := A |} n (ELit v)`: our image holds v at A
  CELL-ADDR   `z8 (ANum v) W`: our image holds W at v
  OWN-STATIC  `(v, n)` in Tfib_owned_static: AF0m's own row `z8 (ANum v) W` holds our image's word
  RO-CHUNK    a region / chunk start (`mkRegion None v hi`, `mkChunk v (CImg n)`, `CH R v n`): the bytes [v - 8, v) and
              [end, end + 8) are owned statics of our AF0m list, so v is fixed by our layout
  ROW-START   `Definition N : Z := v.` (a table row): v is a symbol start of our image; the donor's same-named row
              holds another number (not a copy)
A value is OK when every occurrence has a role whose measurement holds; a quantity role (K-LENGTH, K-RANGE) also
needs the same text in the donor file at the same place (the generator kept it while it moved the line's image
addresses). Known-answer control (--control): the same rules re-judge the findings codeptr makes on cgif's own
UNRELOCATED AD1k / AD2i / AD2j against our images (the must-find run): the count each rule settles is printed; a rule
that settled a real stale donor address there would be shown.
"""
import argparse, csv, os, re, struct, sys
from elftools.elf.elffile import ELFFile

LIT = re.compile(r'0x[0-9a-fA-F]+|(?<![\w.])\d{5,}(?!\d|\.\d)')   # codeptr's own literal pattern


class Img:
    def __init__(self, pin, twin):
        e = ELFFile(open(pin, 'rb'))
        self.segs = [(s['p_vaddr'], s.data()) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD' and s['p_filesz']]
        self.loads = [(s['p_vaddr'], s['p_vaddr'] + s['p_memsz']) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
        t = ELFFile(open(twin, 'rb')).get_section_by_name('.symtab')
        self.syms = sorted((s['st_value'], s['st_size'], s.name) for s in t.iter_symbols()
                           if s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT') and s['st_value'] and s.name)
        self.starts = {}
        for s, sz, n in self.syms:
            self.starts.setdefault(s, []).append(n)
        # the ASan global descriptors (beg, size, size_with_redzone, ...: 8 words each) of the asan_globals section
        g = e.get_section_by_name('asan_globals')
        d = g.data() if g is not None else b''
        self.globals = {}
        for i in range(0, len(d) - 63, 64):
            beg, size = struct.unpack('<QQ', d[i:i + 16])
            self.globals[beg] = size

    def read(self, a, n):
        for va, d in self.segs:
            if va <= a and a + n <= va + len(d):
                return int.from_bytes(d[a - va:a - va + n], 'little')
        return None

    def sym(self, v):
        hit = [(v - s, n) for s, sz, n in self.syms if s <= v < s + max(sz, 1)]
        return min(hit) if hit else None

    def seg_bound(self, v):
        """v is a PT_LOAD start / end or its page floor / ceiling"""
        b = {x for lo, hi in self.loads for x in (lo, hi)}
        return v in b or v in {x // 4096 * 4096 for x in b} or v in {-(-x // 4096) * 4096 for x in b}

    def count_word(self, w):
        b = struct.pack('<I', w & 0xffffffff)
        return sum(d.count(b) for _, d in self.segs)


def num(s):
    return int(s, 16) if s.lower().startswith('0x') else int(s)


def occurrences(text, v):
    out = []
    for m in LIT.finditer(text):
        if num(m.group(0)) == v:
            out.append(m)
    return out


def owned(text):
    """the (start, length) rows of Tfib_owned_static of an AF0m.v text"""
    i = text.find('Tfib_owned_static')
    j = text.find('].', i)
    return {(num(a), num(b)) for a, b in re.findall(r'\((0x[0-9a-fA-F]+|\d+),\s*(0x[0-9a-fA-F]+|\d+)\)', text[i:j])}


def mask_x(s):
    """the text with every number replaced by # except EVar indices (`EVar 254`), which name the place in a trace;
    a partial token at the window's left edge is dropped"""
    s = re.sub(r'^[0-9a-fA-Fx]*\s?', '', s) if s[:1].isalnum() else s
    return re.sub(r'(?<!EVar )(?:0x[0-9a-fA-F]+|\d+)', '#', s)


mask = mask_x


def donor_twin_occ(dt, t, m, width=60):
    """the donor occurrence of the same numeral text with the same `width` characters BEFORE it (every number
    masked), or None"""
    win = mask(t[max(0, m.start() - width):m.start()])
    for dm in LIT.finditer(dt):
        if dm.group(0) == m.group(0) and mask(dt[max(0, dm.start() - width):dm.start()]) == win:
            return dm
    return None


def chunk_end_ok(img, ctx, s, end):
    """the end of the chunk [s, end) is fixed by our layout: an owned static starts there, or the ASan descriptor of
    the global at s gives size end - s"""
    if any(a == end for a, n in ctx['owned']):
        return True, 'an owned static of our AF0m list starts at %#x' % end
    if img.globals.get(s) == end - s:
        return True, 'our asan_globals descriptor of the global at %#x gives size %d' % (s, end - s)
    return False, 'no owned static starts at %#x and no descriptor at %#x gives size %d' % (end, s, end - s)


def role(t, m, v, img, ctx):
    """(role, ok, measurement) of one occurrence"""
    s, e = m.start(), m.end()
    before, after = t[max(0, s - 220):s], t[e:e + 120]
    if s > 0 and (t[s - 1].isalnum() or t[s - 1] == '_'):
        ident = re.search(r'[\w]*$', t[:s]).group(0) + re.match(r'[\w]*', t[e:]).group(0)
        same = [p for p in ctx['donor_all'] if ident in p[1]]
        return 'IDENT', len(same) == 2, 'part of the identifier %s; the donor files holding the same identifier: %s' % (
            ident, ', '.join(p[0].split('/', 1)[1] for p in same) or '-')
    mm = re.search(r'decode_any \((0x[0-9a-fA-F]+)%bv : bv 32\) = Some \((\w+)[^()]*$', before)
    if mm:
        w, op = int(mm.group(1), 16), mm.group(2)
        if op in ('Lui', 'Auipc'):
            f = w >> 12
            return 'INSN-FIELD', f == v, 'the %s immediate of the decoded word %#x is %#x (%d)' % (op, w, f, f)
        return 'INSN-FIELD', False, 'a field of %s %#x (not recomputed)' % (op, w)
    if re.match(r'%bv\s*:\s*bv 32', after):
        fetch = [(int(a, 16), int(w, 16)) for a, w in re.findall(
            r'fetch_word \w+ \(Z_to_bv 64 (0x[0-9a-fA-F]+)\) = Some \((0x[0-9a-fA-F]+)%bv', t) if int(w, 16) == v]
        got = [(a, img.read(a, 4)) for a, w in fetch]
        n = img.count_word(v)
        ok = all(x == v for _, x in got) and (bool(got) or n > 0)
        return 'INSN-WORD', ok, 'a 32-bit instruction word; %s; the word occurs %d time(s) in our image\'s loaded bytes' % (
            ('fetched at %s, our image holds %s there' % (', '.join('%#x' % a for a, _ in got), ', '.join(
                '%#x' % x if x is not None else '-' for _, x in got))) if got else 'fetched at a symbolic address', n)
    # the cell a value lives in: KWord at a literal address, z1 / z4 / z8 rows
    mm = re.search(r'KWord\s*\{\|\s*a_base\s*:=\s*ELit 0;\s*a_off\s*:=\s*(\d+)\s*\|\}\s*(\d+)\s*\(ELit\s+$', before) or \
        re.search(r'z([148]) \(ANum (0x[0-9a-fA-F]+)\)\s+$', before)
    if mm:
        if mm.re.pattern.startswith('KWord'):
            a, n = int(mm.group(1)), int(mm.group(2))
        else:
            n, a = int(mm.group(1)), int(mm.group(2), 16)
        x = img.read(a, n)
        if x is not None:
            return 'CELL-VALUE', x == v, 'the value of the %d-byte cell %#x; our image holds %#x there' % (n, a, x)
        # a NOBITS cell (written at start-up): the donor's cell at the same place must be the same object + offset
        dm = donor_twin_occ(ctx['dt'], t, m)
        da = None
        if dm:
            q = re.search(r'a_off\s*:=\s*(\d+)\s*\|\}\s*\d+\s*\(ELit\s+$|ANum (0x[0-9a-fA-F]+)\)\s+$', ctx['dt'][max(0, dm.start() - 120):dm.start()])
            da = int(q.group(1)) if q and q.group(1) else (int(q.group(2), 16) if q else None)
        so, sd = img.sym(a), (ctx['dimg'].sym(da) if da is not None else None)
        ok = so is not None and sd is not None and so == sd
        return 'CELL-VALUE', ok, ('the value of the %d-byte cell %#x (no file bytes: NOBITS, written at start-up) = %s+%#x; the '
                                  'donor writes the same value in its cell %s = %s; the same object and offset in both '
                                  'images' % (n, a, so[1] if so else '-', so[0] if so else 0, '%#x' % da if da is not None else '-',
                                              ('%s+%#x' % (sd[1], sd[0])) if sd else '-'))
    if re.search(r'z([148]) \(ANum\s+$', before):
        n = int(re.search(r'z([148]) \(ANum\s+$', before).group(1))
        mw = re.match(r'\)\s+(0x[0-9a-fA-F]+|\d+)', after)
        w = num(mw.group(1)) if mw else None
        x = img.read(v, n)
        return 'CELL-ADDR', w is not None and x == w, '`z%d (ANum %#x) %s`; our image holds %s there%s' % (
            n, v, '%#x' % w if w is not None else '-', '%#x' % x if x is not None else '-',
            (' (%s+%#x)' % (img.sym(v)[1], img.sym(v)[0])) if img.sym(v) else '')
    mm = re.search(r'a_base\s*:=\s*ELit 0;\s*a_off\s*:=\s*$', before)
    if mm:
        return 'K-ADDR', img.seg_bound(v), 'the absolute address of a K record; a PT_LOAD boundary or its page floor / ceiling in our image: %s' % img.seg_bound(v)
    if re.search(r'\|\}\s*\(ELit\s+$', before) or re.search(r'\bam_len := ELit\s+$', before) or \
            re.search(r'\(E(?:Md|Alu|Var|Lit)[^()]*(?:\([^()]*\)[^()]*)*, ELit\s+$', before):
        return 'K-LENGTH', True, 'the length of a region record (`|} (ELit n)`, `am_len := ELit n` or a (base, ELit n) pair): %d' % v
    if re.search(r'KWord\s*\{\|[^{}]*\|\}\s*\d+\s*\(ELit\s+$', before):
        return 'K-LENGTH', True, 'the value written by a KWord at a symbolic address'
    mm = re.search(r'(?:KRange )?\(EVar \w+\)(?: \d+)? $', before) or re.search(r'\(ev E \w+\) <= $', before) or \
        re.search(r'mkAF \d+ $', before)
    if mm:
        return 'K-RANGE', True, 'a bound: `%s%s`' % (mm.group(0).strip(), ' ...')
    mm = re.search(r'\b(a_(?!off\b|base\b)\w+) := $', before)
    if mm:
        return 'RECORD-FIELD', True, 'the value of the record field %s' % mm.group(1)
    mcl = re.search(r'mkChunk (0x[0-9a-fA-F]+) \(CImg \((0x[0-9a-fA-F]+) - $', before)
    if mcl and int(mcl.group(1), 16) == v:
        return 'RO-CHUNK', True, 'the chunk start %s repeated in its own length (%s - %s); judged at the mkChunk start' % (
            mcl.group(1), mcl.group(2), mcl.group(1))
    if (v, 8) in ctx['owned'] and re.match(r',\s*(0x8|8)\)', after):
        w = ctx['af0m_cells'].get(v)
        x = img.read(v, 8)
        return 'OWN-STATIC', w is not None and x == w, 'an owned static (%#x, 8) of our AF0m list; AF0m states %s, our image holds %s' % (
            v, '%#x' % w if w is not None else '-', '%#x' % x if x is not None else '-')
    # chunk / region starts and ends
    start = end = None
    mr = re.match(r'\s+(\d+)\s+0\s+0', after)
    if re.search(r'mkRegion None\s+$', before) and mr:
        start, end = v, int(mr.group(1))
    mc = re.match(r'\s*\(CImg (?:(\d+)|\((0x[0-9a-fA-F]+) - 0x[0-9a-fA-F]+\))\)', after)
    if re.search(r'mkChunk\s+$', before) and mc:
        start, end = v, (v + int(mc.group(1)) if mc.group(1) else int(mc.group(2), 16))
    mh = re.match(r'\s+(\d+)\)', after)
    if re.search(r'\(CH R_\w+\s+$', before) and mh:
        start, end = v, v + int(mh.group(1))
    if start is not None:
        lo_own = any(a + n == v for a, n in ctx['owned'])
        inside = [a for a, n in ctx['owned'] if v <= a < end]
        eok, emeas = chunk_end_ok(img, ctx, v, end)
        ok = (lo_own or img.globals.get(v) is not None) and not inside and eok
        return 'RO-CHUNK', ok, ('a read-only chunk [%#x, %#x); an owned static of our AF0m list ends at its start: %s; our '
                                'asan_globals has a global at its start: %s; owned statics inside it: %s; its end: %s' % (
                                    v, end, lo_own, img.globals.get(v) is not None, ', '.join('%#x' % a for a in inside) or 'none', emeas))
    mk = re.search(r'mkRegion None (\d+) $', before) or re.search(r'mkChunk (0x[0-9a-fA-F]+) \(CImg \($', before) or \
        re.search(r'\((0x[0-9a-fA-F]+), $', before)
    if mk and (mk.re.pattern.startswith('mkRegion') or mk.re.pattern.startswith('mkChunk') or re.match(r'\s*-\s*' + mk.group(1), after)):
        s0 = num(mk.group(1))
        zs = mk.re.pattern.startswith('\\(') and 'Tfib_zero_shadow' in ctx.get('defname', lambda p: '')(s)
        if zs:
            size = img.globals.get(s0)
            ok = size is not None and v == s0 + size // 8 * 8
            return 'ZERO-SHADOW', ok, 'a Tfib_zero_shadow row [%#x, %#x); our asan_globals descriptor at %#x gives size %s, whose full 8-byte granules end at %s' % (
                s0, v, s0, size, '%#x' % (s0 + size // 8 * 8) if size is not None else '-')
        eok, emeas = chunk_end_ok(img, ctx, s0, v)
        return 'RO-CHUNK-END', eok, 'the end of the read-only chunk [%#x, %#x): %s' % (s0, v, emeas)
    mm = re.search(r'Definition (\w+) : Z := $', before)
    if mm:
        names = img.starts.get(v, [])
        dv = ctx['donor_defs'].get(mm.group(1))
        return 'ROW-START', bool(names) and dv != v, 'row %s: %#x starts %s in our image; the donor\'s same-named row holds %s' % (
            mm.group(1), v, '|'.join(names[:2]) or 'no symbol', '%#x' % dv if dv is not None else 'no such row')
    return 'UNKNOWN', False, 'no role: ...%s[%s]%s...' % (before[-60:].replace('\n', ' '), m.group(0), after[:40].replace('\n', ' '))


def donor_same_text(dt, t, m):
    """does the donor text hold the numeral with the same 60 characters on each side, every number masked?"""
    return donor_twin_occ(dt, t, m) is not None


DEFS = re.compile(r'^\s*(?:Definition|Lemma|Example|Fixpoint|Let|Theorem)\s+(\w+)', re.M)
QTY_ROLES = ('K-LENGTH', 'K-RANGE', 'RECORD-FIELD')


def make_ctx(t, dt, af, dall, dimg):
    defs = [(m.start(), m.group(1)) for m in DEFS.finditer(t)]
    def defname(p):
        d = [n for q, n in defs if q <= p]
        return d[-1] if d else '-'
    return dict(owned=owned(af), af0m_cells={num(a): num(w) for a, w in re.findall(r'z8 \(ANum (0x[0-9a-fA-F]+)\)\s+(0x[0-9a-fA-F]+|\d+)', af)},
                donor_defs={n: num(x) for n, x in re.findall(r'Definition (\w+) : Z := (0x[0-9a-fA-F]+|\d+)\.', dt)},
                donor_all=dall, dt=dt, dimg=dimg, defname=defname)

XUNIT = {}
NUMALL = re.compile(r'(?<![\w.])(?:0x[0-9a-fA-F]+|\d+)(?![\w])')


def xunit_values(fname, t, m, width=60):
    """{unit: values} found in the other released units' same file (xunit/<unit>.<A file>) after the same `width`
    characters as this occurrence (every number masked except EVar indices): a quantity of the image would differ
    across units, a constant of the runtime or the OS would not"""
    af = fname.replace('Y', 'A', 1) if fname.startswith('Y') else fname
    if af not in XUNIT:
        idx = []
        for p in sorted(os.listdir(os.path.join('..', 'xunit'))):
            if p.endswith('.' + af) and not p.startswith(('plugin-hostd_fuzz_command', 'cgif_cgif_file_fuzzer')):
                ut = open(os.path.join('..', 'xunit', p)).read()
                d = {}
                for dm in NUMALL.finditer(ut):
                    d.setdefault(mask_x(ut[max(0, dm.start() - width):dm.start()]), set()).add(num(dm.group(0)))
                idx.append((p.split('.')[0], d))
        XUNIT[af] = idx
    win = mask_x(t[max(0, m.start() - width):m.start()])
    return {u: d[win] for u, d in XUNIT[af] if win in d}


def judge(side, fname, v, imgs, dimgs, cache):
    our = 'ours/lib/%s/%s' % (side, fname)
    don = 'cgif/lib/A/%s' % fname if side == 'A' else 'cgif/lib/%s' % fname
    if our not in cache:
        t = open(our).read()
        af = open('ours/lib/%s/%s' % (side, 'AF0m.v' if side == 'A' else 'YF0m.v')).read()
        dt = open(don).read()
        dall = [(p, open(p).read()) for p in ('cgif/lib/A/' + fname.replace('Y', 'A', 1), 'cgif/lib/' + fname.replace('A', 'Y', 1)) if os.path.exists(p)]
        cache[our] = (t, dt, make_ctx(t, dt, af, dall, dimgs[side]))
    t, dt, ctx = cache[our]
    occ = occurrences(t, v)
    parts, ok_all, roles = [], bool(occ), []
    for m in occ:
        r, ok, meas = role(t, m, v, imgs[side], ctx)
        ln = t.count('\n', 0, m.start()) + 1
        if r in QTY_ROLES:
            qok, qmeas = qty_check(fname, t, dt, m, v)
            meas += qmeas
            ok = ok and qok
        roles.append(r)
        ok_all = ok_all and ok
        parts.append(':%d %s %s' % (ln, r, meas))
    # one line per distinct measurement (KZero lengths repeat hundreds of times)
    uniq, seen = [], set()
    for p in parts:
        k = re.sub(r'^:\d+ ', '', p)
        if k not in seen:
            seen.add(k)
            uniq.append(p)
    return ok_all, sorted(set(roles)), '%d occurrence(s) in %s; ' % (len(occ), fname) + ' | '.join(uniq[:6]) + (
        ' | (+%d more of the same kinds)' % (len(uniq) - 6) if len(uniq) > 6 else '')


def qty_check(fname, t, dt, m, v):
    """a quantity must be the same at the same place in the donor's file and, for the start-up traces (B01 / B03), in
    every other released unit's trace that has the place (a kept donor image count would differ there)"""
    st = donor_same_text(dt, t, m)
    ok, meas = st, '; the donor file has it after the same text (numbers masked): %s' % st
    if fname[1:] in ('B01.v', 'B03.v'):
        xu = xunit_values(fname, t, m)
        agree = sorted(u for u, s in xu.items() if v in s)
        disagree = sorted('%s (%s)' % (u, ','.join(str(x) for x in sorted(s))) for u, s in xu.items() if v not in s)
        meas += '; the other units\' %s hold %d at the same place in %d of %d units%s' % (
            fname.replace('Y', 'A', 1), v, len(agree), len(xu), ('; others: ' + '; '.join(disagree)) if disagree else '')
        ok = ok and bool(agree) and not disagree
    return ok, meas


def parse_codeptr(path, side):
    out = []
    for line in open(path):
        mm = re.match(r'^(\S+\.v)\s+\d+ code .* (\d+) FINDINGS: ([^\[]+)\[stale.*?(\d+) STALE \(([^)]*)\)', line)
        if mm and int(mm.group(2)):
            stale = {x.strip() for x in mm.group(5).split(',')}
            for x in mm.group(3).split(','):
                x = x.strip()
                if x:
                    out.append((side, mm.group(1), int(x, 16), 'STALE' if x in stale else 'OUTSIDE/NOT-INSN'))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--control', default=None)
    ap.add_argument('--cpdir', default='..')
    a = ap.parse_args()
    imgs = {k: Img('img/cmd.%s.pin' % k, 'img/cmd.%s.twin' % k) for k in 'AB'}
    dimgs = {k: Img('img/cgif.%s.pin' % k, 'img/cgif.%s.twin' % k) for k in 'AB'}
    cache = {}
    items = []
    for side in 'AB':
        for s, f, v, kind in parse_codeptr(os.path.join(a.cpdir, 'codeptr-%s.out' % side), side):
            items.append((s, f, v, 'codeptr FINDING (%s)' % kind))
        for r in csv.reader(open(os.path.join(a.cpdir, 'cplimit-%s.tsv' % side)), delimiter='\t'):
            if r and not r[0].startswith('#') and r[0] != 'file':
                items.append((side, r[0], int(r[2], 16), 'cplimit %s (donor %s; ours %s)' % (r[3], r[4][:60], r[5][:60])))
    cols = ['image', 'file', 'value', 'source', 'roles', 'reason', 'measurement', 'result', 'finding_kind', 'new_value', 'read_by']
    rows, cnt = [], {}
    for side, f, v, src in items:
        ok, roles, meas = judge(side, f, v, imgs, dimgs, cache)
        reason = '+'.join(roles) if ok else 'OPEN-' + '+'.join(roles)
        rows.append(dict(image=side, file='lib/%s/%s' % (side, f), value='%#x' % v, source=src, roles=','.join(roles),
                         reason=reason, measurement=meas, result='OK' if ok else 'OPEN', finding_kind='-', new_value='-', read_by='-'))
        cnt[(src.split()[0], reason)] = cnt.get((src.split()[0], reason), 0) + 1
    with open(a.out, 'w') as fo:
        w = csv.DictWriter(fo, fieldnames=cols, delimiter='\t', lineterminator='\n')
        w.writeheader()
        w.writerows(rows)
    print('cptriage: %d rows' % len(rows))
    for k in sorted(cnt):
        print('  %-8s %-40s %d' % (k[0], k[1], cnt[k]))
    if a.control:
        # the known-answer control: re-judge the findings of the must-find run (cgif's own unrelocated files against
        # our images) with the same rules; a real stale donor address must not be settled
        txt = open(a.control).read()
        sec = {}
        for side in 'AB':
            blk = txt.split('== (2) MUST FIND, fuzz_command image %s' % side)[1].split('==')[0]
            for line in blk.split('\n'):
                mm = re.match(r'^\s+(\S+\.v)\s+\d+ code .* (\d+) FINDINGS: ([^\[]+)\[', line)
                if mm:
                    sec[(side, mm.group(1))] = [int(x.strip(), 16) for x in mm.group(3).split(',') if x.strip()]
        print('control: the rules on the must-find findings (cgif\'s unrelocated files checked against our images; each '
              'listed value is a donor literal the file carries unchanged):')
        tot, settled = 0, []
        for (side, f), vs in sorted(sec.items()):
            don = 'cgif/lib/A/%s' % f if side == 'A' else 'cgif/lib/%s' % f
            t = open(don).read()
            af = open('ours/lib/%s/%s' % (side, 'AF0m.v' if side == 'A' else 'YF0m.v')).read()
            ctx = make_ctx(t, t, af, [], dimgs[side])
            for v in vs:
                tot += 1
                occ = occurrences(t, v)
                rs = [role(t, m, v, imgs[side], ctx) for m in occ]
                if occ and all(ok for _, ok, _ in rs):
                    settled.append('%s %s %#x %s' % (side, f, v, ','.join(sorted({r for r, _, _ in rs}))))
        print('  %d findings shown (the first 12 per file in codeptr\'s line), %d settled by a rule: %s' % (
            tot, len(settled), '; '.join(settled) or '-'))
        # the quantity rule's known answers: image quantities of our own start-up trace that DIFFER per image must be
        # refused (the brk page-index bound = image top >> 12, and the length of the first rw KWr = the rw span)
        print('control: the quantity rule on known image quantities of lib/A/AB03.v (must be refused):')
        t = open('ours/lib/A/AB03.v').read()
        dt = open('cgif/lib/A/AB03.v').read()
        for pat in (r'KRange \(EVar 5\) \d+ (\d+)', r'KRange \(EVar 5\) (\d+)', r'KWr \{\| a_base := ELit 0; a_off := \d+ \|\} \(ELit (\d+)\)'):
            mm = re.search(pat, t)
            v = int(mm.group(1))
            m = next(x for x in NUMALL.finditer(t, mm.start(1)) if x.start() == mm.start(1))
            ok, meas = qty_check('AB03.v', t, dt, m, v)
            print('  %s = %d: %s%s' % (pat.split('(\\d+)')[0].replace('\\', '')[:40], v, 'ACCEPTED' if ok else 'refused', meas))


if __name__ == '__main__':
    main()
