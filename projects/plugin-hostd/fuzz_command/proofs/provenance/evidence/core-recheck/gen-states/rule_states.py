#!/usr/bin/env python3
"""rule_states.py -- measured judgement of EVERY numeral of a start-up state file (A/AB01.v, A/AB03.v and the B
twins), the triage of the value gate's flagged rows of that file, and the known-answer controls of the rules.

    rule_states.py --file F.v --rel lib/A/AB01.v --pin PIN --twin TWIN --kit KIT
                   --donor-file D.v --donor-pin DPIN --donor-twin DTWIN
                   --rows RUN.gen.tsv --out-rows OUT.tsv --out-nums NUMS.tsv --out-ctl CTL.tsv

Every numeral gets a role from vterm.py (the constructor argument or record field it fills) and one or more rule
results. A rule MEASURES: the image (PT_LOAD and section headers of the pin, symbol table of the twin, rvelf's decode
of .text), the file's own text (list lengths, s_next, the maps of the same state), or the donor's own state of the
same index in the donor's own image (a name-keyed difference: the same symbol + offset, never a numeric delta).
Each result keeps the function that re-judges it for another value of the same numeral; the controls re-judge the
flagged rows with value+4 and with the donor's value (the gate's src_value) and count how many the rules refuse.

Rules (id: what holds when the rule says OK)
  PC-INSN          s_pc is an instruction start (rvelf linear decode of .text) inside a FUNC symbol
  NEXT-FRESH       s_next = 1 + the largest EVar index the state uses
  EVAR-FRESH       an EVar index (a symbolic variable's name, no image quantity) is below s_next of every state using it
  SEG-BOUND        `seg L i n` lies inside the evaluated list L and does not overlap the neighbouring `seg L` pieces
  WIDTH            a KWord width is 1..8 bytes (the checker keeps trimmed words, YK0c.v ktrim)
  ADDR-IMG-RW      an absolute cell [a, a+size) lies inside one writable PT_LOAD (pages rounded out)
  ADDR-SHADOW      an absolute cell lies in the shadow of the image hull, (a - SO) * 8 in the hull; SO = the value the
                   file stores at the twin's __asan_shadow_memory_dynamic_address
  ADDR-LITMAP      an absolute cell / range lies inside the literal maps of the same state
  ADDR-HULL        an absolute range is exactly the image hull
  REL-MAP          a cell at (4096 * EVar n) + off lies in [0, length) of the state's map / ghost / vis / brk region with
                   that base
  REL-SHADOWMAP    a cell at (512 * EVar n) + off lies in the shadow of that region
  REL-STACK        a cell based on the entry sp lies in [sp - 8 MiB - 64 KiB, sp + 64 KiB]
  REL-STACKSHADOW  a cell based on the shadow of the entry sp lies in the shadow of that window
  DONOR-SAME-CELL  the absolute cell's symbol + offset (or the shadowed address's) is a cell of the donor's same-index
                   state at the same symbol + offset of the donor image
  KIMG-HULL        a KImg range lies inside the image hull and each bound is a PT_LOAD / section bound, a symbol bound,
                   the end (lo) / start (hi) of an absolute write of the same state, or the donor's KImg bound at the
                   same symbol + offset
  DONOR-SAME-RELCELL  a cell at a symbolic base + offset has a cell of the donor's same-index state at the same
                   symbolic base text and offset (the collector numbers its variables alike on both images)
  RANGE-BOUND      an absolute KWr / KZero / KFill / KUnk / KBlob range starts and ends at a PT_LOAD / section /
                   symbol bound, at the end / start of another absolute cell or KImg of the state, or at the shadow
                   of a symbol / section bound
  RANGE-IMGTOP / DONOR-SAME-RANGE   a KRange bound equals the donor's bound for the same expression in its
                   same-index state, or differs from it exactly by the two images' top pages (hull end / 4096)
  SHADOW-GLOBALS   an absolute KFill / KZero / KWord in the image's shadow holds exactly the bytes the registration of
                   the image's ASan globals writes there: per 64-byte __asan_global descriptor of the pin's
                   asan_globals section, 0xf9 on the redzone granules and size % 8 on a partial last granule, 0 else
  DONOR-SAME-SYM / -SECOFF / -STRING / -VALUE   a literal (register, KWord value, pc) and the donor's literal at the
                   same place resolve to the same symbol + offset / section + offset / NUL-terminated bytes, or are the
                   same image-independent value (see donor_key)
  TOTSZ            a_totsz = hull size + sum(am_len) + sum(ghost lengths)
  ABYTES / EAGER   a_abytes - sum(vis_cost(literal vis lengths)) and a_eager - sum(KRW map lengths < 2^36) equal the
                   donor's same-index state's residue (the image-dependent parts are recomputed from each own image)
  VIS-HULL         a visible entry (ELit lo, ELit n) equals the image hull
  MAP-PAGE / YLO   a literal map / vis / ghost bound or length, or a_ylo, is a multiple of 4096 (a map base also lies
                   outside the hull)
  SCALE / MASK     algebra constants: |k| a power of two below the image base (scale), 2^j-1 or -2^j (mask)
  VAL-SMALL / VAL-NEG / VAL-OUTSIDE / VAL-SHADOW / VAL-LITMAP / VAL-HULL / VAL-DATA / VAL-CODE
                   what a literal value is in our image: below the image base, negative, above the hull and in no map,
                   a shadow address of the image, inside a literal map, in the header bytes, inside a data section,
                   an instruction start inside a FUNC (VAL-CODE fails for a .text value that is not one)
  RANGE / ALIGN / BYTE / LEN / EXT / BLOB / BLOB-IX / STATE-COUNT   small structural numerals
"""
import argparse
import bisect
import collections
import csv
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import imgfacts  # noqa: E402
import vterm  # noqa: E402

PAGE = 4096
SADDR_HEADS = ('KWord', 'KZero', 'KWr', 'KFill', 'KUnk', 'KBlob', 'KDisj')
# rules that are descriptive (they say what a value IS; a perturbed value is usually still something) -- reported,
# never counted as a refusal or as the deciding reason when a measuring rule is present
DESCRIPTIVE = {'VAL-SMALL', 'VAL-NEG', 'VAL-OUTSIDE', 'VAL-SHADOW', 'VAL-LITMAP', 'VAL-HULL', 'VAL-DATA', 'BASE-LIT',
               'NO-DONOR-CELL'}
PRIORITY = ['TOTSZ', 'ABYTES', 'EAGER', 'NEXT-FRESH', 'PC-INSN', 'DONOR-SAME-SYM', 'DONOR-SAME-SECOFF',
            'DONOR-SAME-STRING', 'DONOR-SAME-CELL', 'SHADOW-GLOBALS', 'DONOR-SAME-RELCELL', 'KIMG-HULL', 'RANGE-BOUND',
            'RANGE-IMGTOP',
            'DONOR-SAME-RANGE',
            'VIS-HULL', 'SEG-BOUND', 'STATE-COUNT',
            'ADDR-HULL', 'ADDR-IMG-RW', 'ADDR-SHADOW', 'ADDR-LITMAP', 'REL-MAP', 'REL-SHADOWMAP', 'REL-STACK',
            'REL-STACKSHADOW', 'MAP-PAGE', 'YLO', 'DONOR-SAME-VALUE', 'VAL-CODE', 'EVAR-FRESH', 'SCALE', 'MASK',
            'WIDTH', 'LEN', 'RANGE', 'ALIGN', 'BYTE', 'EXT', 'BLOB', 'BLOB-IX', 'VAL-DATA', 'VAL-HULL', 'VAL-SHADOW',
            'VAL-LITMAP', 'VAL-OUTSIDE', 'VAL-SMALL', 'VAL-NEG', 'BASE-LIT', 'NO-DONOR-CELL']


def U(x):
    return vterm.unparen(x)


def lit(x):
    """The integer of `ELit z` or of a bare numeral, else None."""
    x = U(x)
    if x[0] == 'num':
        return x[1]
    if x[0] == 'app' and x[1] == 'ELit':
        y = U(x[2][0])
        return y[1] if y[0] == 'num' else None
    return None


def litpos(x):
    """Token position of the numeral of `ELit z` or of a bare numeral."""
    x = U(x)
    return x[2].pos if x[0] == 'num' else U(x[2][0])[2].pos


def evars(x, out):
    k = x[0]
    if k == 'app' and x[1] == 'EVar':
        y = U(x[2][0])
        out.append((y[1], y[2].pos))
        return out
    if k == 'paren':
        evars(x[1], out)
    elif k in ('list', 'cat', 'tuple'):
        for i in x[1]:
            evars(i, out)
    elif k == 'rec':
        for _, v in x[1]:
            evars(v, out)
    elif k == 'app':
        for a in x[2]:
            evars(a, out)
    return out


class File:
    """One state file: numerals, definitions, evaluated kn lists, states."""

    def __init__(self, text):
        self.nums, self.defs, self.order = vterm.numerals(text)
        self.memo = {}
        self.segchains = []        # per `++` chain: [(list name, i, n, pos_i, pos_n, length of the list)]
        self.states = [n for n in self.order if U(self.defs[n])[0] == 'rec'
                       and 'a_ss' in dict(U(self.defs[n])[1])]
        self._st = {}

    def entries(self, name):
        if name not in self.memo:
            self.memo[name] = self._ev(self.defs[name])
        return self.memo[name]

    def _seg(self, x):
        src = self.entries(U(x[2][0])[1])
        i, n = U(x[2][1]), U(x[2][2])
        return src, (U(x[2][0])[1], i[1], n[1], i[2].pos, n[2].pos, len(src))

    def _ev(self, x):
        x = U(x)
        if x[0] == 'list':
            return list(x[1])
        if x[0] == 'cat':
            out, chain = [], []
            for it in x[1]:
                u = U(it)
                if u[0] == 'app' and u[1] == 'seg':
                    src, info = self._seg(u)
                    chain.append(info)
                    out += src[info[1]:info[1] + info[2]]
                else:
                    out += self._ev(it)
            self.segchains.append(chain)
            return out
        if x[0] == 'id':
            return self.entries(x[1])
        if x[0] == 'app' and x[1] == 'seg':
            src, info = self._seg(x)
            self.segchains.append([info])
            return src[info[1]:info[1] + info[2]]
        raise ValueError(f'cannot evaluate a list from {x[0]}')

    def state(self, name):
        if name in self._st:
            return self._st[name]
        f = dict(U(self.defs[name])[1])
        ss = U(f['a_ss'])
        assert ss[0] == 'app' and ss[1] == 'SS', name
        a = ss[2]
        kn = U(a[3])
        knl = self.entries(kn[1]) if kn[0] == 'id' else self._ev(kn)
        maps = [dict(U(m)[1]) for m in U(f['a_maps'])[1]]
        vis = [tuple(U(t)[1]) for t in U(f['a_vis'])[1]]
        ghost = [tuple(U(t)[1]) for t in U(f['a_ghost'])[1]]
        self._st[name] = dict(name=name, f=f, pc=U(a[0]), regs=U(a[1])[1], kn=knl, next=U(a[4]), maps=maps,
                              vis=vis, ghost=ghost)
        return self._st[name]


def sym_at(img, a):
    """(name, offset) of the smallest OBJECT/FUNC symbol of the twin that holds a; else a named symbol of any type
    (NOTYPE included, e.g. __global_pointer$) whose value is exactly a; else None."""
    o = img.obj_of(a)
    if o:
        return o[2], a - o[0]
    f = img.func_of(a)
    if f:
        return f[2], a - f[0]
    for v, z, ty, n in img.syms[bisect.bisect_left(img.syms, (a,)):]:
        if v != a:
            break
        return n, 0
    return None


def sec_off(img, a):
    for lo, hi, n, nb, fl in img.sections:
        if lo <= a < hi:
            return n, a - lo
    return None


def cstr(img, a, lim=256):
    o = img.file_off(a)
    if o is None:
        return None
    b = img.data[o:o + lim]
    k = b.find(b'\0')
    return None if k < 0 else b[:k]


def hx(s):
    return f'{s[0]}+{s[1]:#x}' if s else 'no symbol'


class Judge:
    def __init__(self, F, img, D=None, dimg=None):
        self.F, self.img, self.D, self.dimg = F, img, D, dimg
        self.res = collections.defaultdict(list)     # pos -> [(rule, ok, measurement, fn or None)]
        self.lo, self.hi = img.hull
        self.bounds = set()
        for v, fs, m, fl, off in img.loads:
            self.bounds |= {v, v + fs, v + m, v & ~(PAGE - 1), (v + m + PAGE - 1) & ~(PAGE - 1)}
        for lo, hi, n, nb, fl in img.sections:
            self.bounds |= {lo, hi}
        self.symb = set()
        for v, z, ty, n in img.syms:
            if ty in ('STT_OBJECT', 'STT_FUNC', 'STT_TLS') and z:
                self.symb |= {v, v + z}
        self.SO = self.shadow_offset()
        self._dc = {}
        self.expshadow, self.nglobals = self.global_shadow()
        self.expkeys = sorted(self.expshadow)
        self._shc = {}

    def global_shadow(self):
        """{granule address: shadow byte} the registration of the image's ASan globals writes: for every 64-byte
        __asan_global descriptor (beg, size, size_with_redzone, ...) of the pin's asan_globals section, the granules
        of [beg + roundup(size, 8), beg + size_with_redzone) hold 0xf9 and, when size % 8 != 0, the granule at
        beg + rounddown(size, 8) holds size % 8 (ASan PoisonRedZones); the descriptor array itself (the whole
        asan_globals section) holds 0xf9 (the runtime poisons the metadata it registered; the donor's released
        A/AB01.v shows the same fill over the donor's own asan_globals section). Every other image granule's
        shadow is 0."""
        sec = [(lo, hi) for lo, hi, n, nb, fl in self.img.sections if n == 'asan_globals']
        out = {}
        if not sec:
            return out, 0
        lo, hi = sec[0]
        for g in range(lo, hi, 8):
            out[g] = 0xf9
        n = 0
        for a in range(lo, hi, 64):
            beg, size, szr = (self.img.word(a + 8 * k, 8) for k in range(3))
            n += 1
            al = (size + 7) & ~7
            for g in range(beg + al, beg + szr, 8):
                out[g] = 0xf9
            if size % 8:
                out[beg + (size & ~7)] = size % 8
        return out, n

    def shadow_check(self, s, kind, n, c=0):
        """(ok, measurement) for n shadow bytes at shadow address s that the entry says are all c (KFill / KZero,
        kind 'fill') or are the little-endian bytes of the word c (KWord, kind 'word'), against global_shadow."""
        key = (s, kind, n, c)
        if key in self._shc:
            return self._shc[key]
        g0, g1 = (s - self.SO) << 3, (s + n - self.SO) << 3
        i, j = bisect.bisect_left(self.expkeys, g0), bisect.bisect_left(self.expkeys, g1)
        inside = {g: self.expshadow[g] for g in self.expkeys[i:j]}
        if kind == 'fill':
            if c == 0:
                ok = not inside
                bad = sorted(inside.items())[:1]
            else:
                ok = len(inside) == n and all(b == c for b in inside.values())
                bad = [] if ok else [(g, inside.get(g, 0)) for g in range(g0, g1, 8) if inside.get(g, 0) != c][:1]
        else:
            want = [inside.get(g0 + 8 * k, 0) for k in range(n)]
            got = [(c >> (8 * k)) & 0xff for k in range(n)]
            ok = want == got
            bad = [(g0 + 8 * k, want[k]) for k in range(n) if want[k] != got[k]][:1]
        meas = (f'shadow [{s:#x}, +{n}) covers image [{g0:#x}, {g1:#x}); its bytes equal the global-redzone shadow '
                f'that the {self.nglobals} asan_globals descriptors of the pin give' if ok else
                f'shadow of image granule {bad[0][0]:#x} is {bad[0][1]:#x} by the asan_globals descriptors; the entry '
                f'says {"fill " + hex(c) if kind == "fill" else "word " + hex(c)}' if bad else
                'shadow range check failed')
        self._shc[key] = (ok, meas)
        return ok, meas

    def add(self, pos, rule, ok, meas, fn=None):
        """fn(w) re-judges this result for the value w of the same numeral (None: the rule only describes)."""
        self.res[pos].append((rule, bool(ok), meas, fn))

    def shadow_offset(self):
        a = self.img.byname.get('__asan_shadow_memory_dynamic_address')
        if not a:
            return None
        a = a[0][0]
        for e in self.F.state(self.F.states[0])['kn']:
            e = U(e)
            if e[0] == 'app' and e[1] == 'KWord':
                sa = dict(U(e[2][0])[1])
                if lit(sa['a_base']) == 0 and U(sa['a_off'])[1] == a and lit(e[2][2]) is not None:
                    return lit(e[2][2])
        return None

    # ---- what a literal value is in our image --------------------------------------------------------------------
    def value(self, v, maps=()):
        img = self.img
        if v < 0:
            return 'VAL-NEG', True, f'{v} < 0: no address'
        if v < self.lo:
            return 'VAL-SMALL', True, f'{v:#x} below the image base {self.lo:#x}: no address'
        if v <= self.hi:
            sec = img.section_of(v) or img.section_of(v, True)
            if sec == '.text' or (img.func_of(v) and not img.obj_of(v)):
                f = img.func_of(v)
                ok = f is not None and img.is_insn(v)
                return 'VAL-CODE', ok, (f'{v:#x} = {f[2]}+{v - f[0]:#x}, an instruction start' if ok else
                                        f'{v:#x} in .text but {"not an instruction start" if f else "in no FUNC"}')
            if sec:
                return 'VAL-DATA', True, f'{v:#x} in {sec} at {hx(sym_at(img, v))}'
            first = img.sections[0][0]
            if v < first:
                if img.phdr and v == img.phdr[0]:
                    return 'VAL-HULL', True, f'{v:#x} = PT_PHDR p_vaddr (the program headers)'
                return 'VAL-HULL', True, (f'{v:#x} lies in the ELF/program-header bytes [{self.lo:#x}, {first:#x}) '
                                          f'before the first section: no object starts there')
            ld = img.load_of(v, True)
            return 'VAL-HULL', True, (f'{v:#x} in the image hull, PT_LOAD {ld[0]}, no section' if ld else
                                      f'{v:#x} in a gap of the hull between PT_LOADs')
        if self.SO is not None and self.SO + (self.lo >> 3) <= v <= self.SO + (self.hi >> 3):
            a = (v - self.SO) << 3
            return 'VAL-SHADOW', True, f'{v:#x} = shadow of {a:#x} ({hx(sym_at(img, a))})'
        for lo, n, kind in maps:
            if lo <= v < lo + n:
                return 'VAL-LITMAP', True, f'{v:#x} inside the state\'s literal map [{lo:#x}, +{n:#x}) {kind}'
        return 'VAL-OUTSIDE', True, f'{v:#x} above the image hull end {self.hi:#x}, not its shadow, in no literal map'

    def add_value(self, p, v, maps, where):
        r = self.value(v, maps)
        fn = (lambda w, maps=maps: self.value(w, maps)[1]) if r[0] == 'VAL-CODE' else None
        self.add(p, r[0], r[1], f'{where}: {r[2]}', fn)

    # ---- the donor's literal at the same place ------------------------------------------------------------------
    def donor_key(self, v, d):
        """(rule, ok, measurement) for our literal v against the donor's literal d at the same place, or None when
        the comparison says nothing (both outside the hulls and different)."""
        img, dimg = self.img, self.dimg
        ins = lambda im, x: im.hull[0] <= x < im.hull[1]
        if ins(img, v) and ins(dimg, d):
            s, t = sym_at(img, v), sym_at(dimg, d)
            if s is not None and s == t:
                return 'DONOR-SAME-SYM', True, f'ours {v:#x} = {hx(s)}; the donor\'s {d:#x} = the same symbol + offset'
            so, to = sec_off(img, v), sec_off(dimg, d)
            nobits = so is not None and any(n == so[0] and nb for lo, hi, n, nb, fl in img.sections)
            same_bytes = nobits or (img.word(v, 8) is not None and img.word(v, 8) == dimg.word(d, 8))
            if so is not None and so == to and (s is None or t is None or s[0] == t[0]) and same_bytes:
                return 'DONOR-SAME-SECOFF', True, (f'ours {v:#x} = {hx(so)}; the donor\'s {d:#x} = the same section + '
                                                   f'offset' + (' (NOBITS)' if nobits else ', holding the same 8 bytes'))
            cs, cd = cstr(img, v), cstr(dimg, d)
            if so and to and so[0] == to[0] and cs is not None and cs == cd and (s is None or t is None):
                return 'DONOR-SAME-STRING', True, (f'ours {v:#x} and the donor\'s {d:#x} both point into {so[0]} at '
                                                   f'the same NUL-terminated bytes {cs[:40]!r}')
            if v == d and v < img.sections[0][0] and d < dimg.sections[0][0]:
                return 'DONOR-SAME-VALUE', True, (f'{v:#x} equals the donor\'s value and lies in the ELF/program-'
                                                  f'header bytes of both images (no object)')
            if v == d and s and t and s[0] == t[0]:
                return 'DONOR-SAME-VALUE', True, (f'{v:#x} equals the donor\'s value; it falls in {s[0]} in both images '
                                                  f'at different offsets ({s[1]:#x} / {t[1]:#x}), so it points at no '
                                                  f'fixed place of that object: an image-independent constant')
            return 'DONOR-DIFFERS', False, (f'ours {v:#x} = {hx(s) if s else so}; the donor\'s {d:#x} = '
                                            f'{hx(t) if t else to} in the donor image')
        if ins(img, v) != ins(dimg, d):
            if v == d:
                return 'DONOR-KEPT?', False, (f'ours {v:#x} equals the donor\'s value and is an image address in only '
                                              f'one of the two images ({hx(sym_at(img, v))})')
            return None
        if v == d:
            return 'DONOR-SAME-VALUE', True, f'{v:#x} equals the donor\'s value; outside both image hulls'
        return None

    def donor_cmp(self, p, v, d, where):
        if d is None or self.dimg is None:
            return
        r = self.donor_key(v, d)
        if r is None:
            return
        self.add(p, r[0], r[1], f'{where}: {r[2]}',
                 lambda w, d=d: (lambda q: q is not None and q[1] and q[0] != 'DONOR-SAME-VALUE' or
                                 (q is not None and q[0] == 'DONOR-SAME-VALUE' and w == d))(self.donor_key(w, d)))

    # ---- passes --------------------------------------------------------------------------------------------------
    def run(self):
        F = self.F
        for st in F.states:
            self.state_pass(F.state(st))
        for chain in F.segchains:
            for k, (nm, i, n, pi, pn, ln) in enumerate(chain):
                lo = max([c[1] + c[2] for c in chain[:k] if c[0] == nm] or [0])
                hi = min([c[1] for c in chain[k + 1:] if c[0] == nm] or [ln])
                ok = lo <= i and i + n <= hi
                m = (f'seg {nm} {i} {n}: [{i}, {i + n}) lies inside [{lo}, {hi}) = after the previous and before the '
                     f'next `seg {nm}` piece of the same definition, within the length {ln} of the evaluated {nm}')
                self.add(pi, 'SEG-BOUND', ok, m, lambda w, n=n, lo=lo, hi=hi: lo <= w and w + n <= hi)
                self.add(pn, 'SEG-BOUND', ok, m, lambda w, i=i, hi=hi: w >= 0 and i + w <= hi)
        for n in F.nums:
            if n['pos'] not in self.res:
                self.free(n)

    def state_pass(self, S):
        nm = S['name']
        nxt = S['next'][1]
        allv = []
        for part in [('list', S['regs']), ('list', S['kn'])] + [('rec', list(m.items())) for m in S['maps']] + \
                [('list', [('tuple', list(t)) for t in S['vis'] + S['ghost']])] + [S['f']['a_brk']]:
            evars(part, allv)
        mx = max((v for v, _ in allv), default=-1)
        for v, p in allv:
            self.add(p, 'EVAR-FRESH', 0 <= v < nxt, f'EVar {v} (a symbolic variable\'s index) < s_next {nxt} of {nm}',
                     lambda w, nxt=nxt: 0 <= w < nxt)
        self.add(S['next'][2].pos, 'NEXT-FRESH', nxt == mx + 1, f's_next {nxt} of {nm} = 1 + the largest EVar {mx} '
                                                                 f'the state uses', lambda w, mx=mx: w == mx + 1)
        pc = S['pc'][1]
        f = self.img.func_of(pc)
        S['at_main'] = f is not None and f[2] == 'main' and f[0] == pc
        insn = lambda w: self.img.func_of(w) is not None and self.img.is_insn(w)
        self.add(S['pc'][2].pos, 'PC-INSN', insn(pc), f's_pc {pc:#x} = {f[2]}+{pc - f[0]:#x}, an instruction start'
                 if insn(pc) else f's_pc {pc:#x} is not an instruction start inside a FUNC symbol', insn)
        if self.D is not None and nm in self.D.defs:
            self.donor_cmp(S['pc'][2].pos, pc, self.D.state(nm)['pc'][1], f's_pc of {nm}')
        litmaps, mapof = [], {}
        for m in S['maps']:
            b, ln = lit(m['am_base']), lit(m['am_len'])
            mapof[vterm.show(m['am_base'], 10 ** 6)] = ln
            if b is not None and ln is not None:
                litmaps.append((b, ln, U(m['am_kind'])[1]))
        # a region the state names outside a_maps: its a_ghost / a_vis entries (an unmapped or refused child's pages)
        # and the brk area [4096 * EVar n, a_brk); a base named several times takes its largest length
        extra = [(vterm.show(b, 10 ** 6), lit(n)) for b, n in S['ghost'] + S['vis'] if lit(n) is not None]
        brk = U(S['f']['a_brk'])
        if brk[0] == 'app' and brk[1] == 'EAlu' and lit(brk[2][2]) is not None:
            extra.append((vterm.show(U(brk[2][1]), 10 ** 6), lit(brk[2][2])))
        for k, n in extra:
            if mapof.get(k) is None or mapof[k] < n:
                mapof[k] = n
        self.maps_pass(S, litmaps)
        self.regs_pass(S, litmaps)
        self.totals_pass(S)
        writes = self.kn_pass(S, mapof, litmaps)
        self.kimg_pass(S, writes)

    def maps_pass(self, S, litmaps):
        nm = S['name']
        for m in S['maps']:
            ln = lit(m['am_len'])
            for fld in ('am_base', 'am_len'):
                v = lit(m[fld])
                if v is None:
                    self.expr_consts(m[fld], S, f'{fld} expression')
                    continue
                if fld == 'am_base':
                    okf = lambda w, ln=ln: w % PAGE == 0 and w >= 0 and ln is not None and \
                        (w + ln <= self.lo or w >= self.hi)
                    meas = f'am_base {v:#x} of {nm} is page aligned and [{v:#x}, +{ln:#x}) lies outside the image hull'
                else:
                    okf = lambda w: w % PAGE == 0 and w > 0
                    meas = f'am_len {v:#x} of {nm} is a positive multiple of 4096'
                self.add(litpos(m[fld]), 'MAP-PAGE', okf(v), meas, okf)
        for kind, lst in (('a_vis', S['vis']), ('a_ghost', S['ghost'])):
            for b, n in lst:
                bv, nv = lit(b), lit(n)
                if bv is not None and nv is not None and bv == self.lo and nv == self.hi - self.lo:
                    for x, want in ((b, self.lo), (n, self.hi - self.lo)):
                        self.add(litpos(x), 'VIS-HULL', True, f'{kind} entry ({bv:#x}, {nv:#x}) of {nm} = the image '
                                 f'hull [{self.lo:#x}, {self.hi:#x}) of the PT_LOADs', lambda w, want=want: w == want)
                    continue
                for x, what in ((b, 'base'), (n, 'len')):
                    v = lit(x)
                    if v is None:
                        self.expr_consts(x, S, f'{kind} {what} expression')
                        continue
                    okf = lambda w: w % PAGE == 0 and w >= 0
                    self.add(litpos(x), 'MAP-PAGE', okf(v), f'{kind} {what} {v:#x} of {nm} is a multiple of 4096', okf)
        self.expr_consts(S['f']['a_brk'], S, 'a_brk expression')

    def regs_pass(self, S, litmaps):
        dregs = None
        if self.D is not None and S['name'] in self.D.defs:
            dregs = [lit(r) for r in self.D.state(S['name'])['regs']]
        for i, r in enumerate(S['regs']):
            v = lit(r)
            if v is None:
                self.expr_consts(r, S, f'register x{i} expression')
                continue
            p = litpos(r)
            self.add_value(p, v, litmaps, f'x{i} of {S["name"]}')
            if dregs is not None and i < len(dregs):
                self.donor_cmp(p, v, dregs[i], f'x{i} of {S["name"]}')

    def totals_pass(self, S):
        f = S['f']
        nm = S['name']
        lens = [lit(m['am_len']) for m in S['maps']]
        kinds = [U(m['am_kind'])[1] for m in S['maps']]
        gl = [lit(b) for a, b in S['ghost']]
        vl = [lit(b) for a, b in S['vis']]
        y = U(f['a_ylo'])
        okf = lambda w: w % PAGE == 0 and w >= self.hi
        self.add(y[2].pos, 'YLO', okf(y[1]), f'a_ylo {y[1]:#x} of {nm} is page aligned and above the image hull end '
                                             f'{self.hi:#x}', okf)
        if None in lens or None in gl:
            return
        hullsz = self.hi - self.lo
        tot = U(f['a_totsz'])
        want = hullsz + sum(lens) + sum(gl)
        self.add(tot[2].pos, 'TOTSZ', tot[1] == want,
                 f'a_totsz {tot[1]} of {nm} = hull size {hullsz:#x} + sum(am_len) {sum(lens)} + sum(a_ghost lengths) '
                 f'{sum(gl)} = {want}', lambda w, want=want: w == want)
        if self.D is None or nm not in self.D.defs:
            return
        vis_cost = lambda n: n + n // 8 + 16384     # Reusable/YK09.v vis_cost
        sv = sum(vis_cost(x) for x in vl if x is not None)
        sk = sum(ln for ln, k in zip(lens, kinds) if k == 'KRW' and ln < (1 << 36))
        DS = self.D.state(nm)
        dl = [lit(m['am_len']) for m in DS['maps']]
        dk = [U(m['am_kind'])[1] for m in DS['maps']]
        dra = U(DS['f']['a_abytes'])[1] - sum(vis_cost(x) for x in (lit(b) for a, b in DS['vis']) if x is not None)
        dre = U(DS['f']['a_eager'])[1] - sum(ln for ln, k in zip(dl, dk) if k == 'KRW' and ln < (1 << 36))
        ab, eg = U(f['a_abytes']), U(f['a_eager'])
        self.add(ab[2].pos, 'ABYTES', ab[1] - sv == dra,
                 f'a_abytes {ab[1]} of {nm} - sum(vis_cost) of its literal a_vis lengths ({sv}) = {ab[1] - sv:#x}; the '
                 f'donor\'s {nm} gives {dra:#x} from its own image', lambda w, sv=sv, dra=dra: w - sv == dra)
        self.add(eg[2].pos, 'EAGER', eg[1] - sk == dre,
                 f'a_eager {eg[1]} of {nm} - sum(KRW am_len < 2^36) ({sk}) = {eg[1] - sk:#x}; the donor\'s {nm} gives '
                 f'{dre:#x}', lambda w, sk=sk, dre=dre: w - sk == dre)

    # ---- kn entries ----------------------------------------------------------------------------------------------
    def saddrs(self, e):
        h, a = e[1], e[2]
        if h == 'KWord':
            return [(a[0], U(a[1])[1], None)]
        if h == 'KDisj':
            return [(a[0], lit(a[1]), a[1]), (a[2], lit(a[3]), a[3])]
        return [(a[0], lit(a[1]), a[1])]

    def kn_pass(self, S, mapof, litmaps):
        writes = []
        nm = S['name']
        dkv, dcells = self.donor_cells(nm)
        # the absolute cells and KImg bounds of the state: what the end / start of an absolute range may meet
        starts, ends, klo, khi = set(), set(), set(), set()
        for e in S['kn']:
            e = U(e)
            if e[0] != 'app':
                continue
            if e[1] == 'KImg':
                klo.add(U(e[2][0])[1])
                khi.add(U(e[2][1])[1])
            elif e[1] in SADDR_HEADS and e[1] != 'KDisj':
                for sa, size, _ in self.saddrs(e):
                    dd = dict(U(sa)[1])
                    if lit(dd['a_base']) is not None and size is not None:
                        a0 = lit(dd['a_base']) + U(dd['a_off'])[1]
                        starts.add(a0)
                        ends.add(a0 + size)

        def rbound(x, side):
            """Why x may bound an absolute range on `side`, or None."""
            if x in self.bounds or x in (self.lo, self.hi):
                return 'a PT_LOAD / section / hull bound'
            if x in self.symb:
                return 'a symbol bound of the twin'
            if side == 'end' and (x in starts or x in klo):
                return 'the start of another absolute cell / KImg of the state'
            if side == 'start' and (x in ends or x in khi):
                return 'the end of another absolute cell / KImg of the state'
            if self.SO is not None and self.SO + (self.lo >> 3) <= x <= self.SO + (self.hi >> 3):
                ia = (x - self.SO) << 3
                if ia in self.symb or ia in self.bounds:
                    return f'the shadow of the symbol / section bound {ia:#x}'
            return None
        for e in S['kn']:
            e = U(e)
            if e[0] != 'app' or e[1] == 'KImg':
                continue
            h = e[1]
            if h == 'KRange':
                lo, hi = U(e[2][1]), U(e[2][2])
                ok = lo[1] <= hi[1]
                self.add(lo[2].pos, 'RANGE', ok, f'KRange bounds {lo[1]}..{hi[1]} of {nm} are ordered; lo: '
                         + self.value(lo[1], litmaps)[2], lambda w, hv=hi[1]: w <= hv)
                self.add(hi[2].pos, 'RANGE', ok, f'KRange bounds {lo[1]}..{hi[1]} of {nm} are ordered; hi: '
                         + self.value(hi[1], litmaps)[2], lambda w, lv=lo[1]: lv <= w)
                ev = lit(e[2][0])
                if ev is not None:
                    okf = lambda w, a=lo[1], b=hi[1]: a <= w <= b
                    self.add(litpos(e[2][0]), 'RANGE', okf(ev), f'KRange (ELit {ev}) {lo[1]} {hi[1]} of {nm}: the '
                             f'literal lies inside its own bounds; ' + self.value(ev, litmaps)[2], okf)
                else:
                    self.expr_consts(e[2][0], S, 'KRange expression')
                drs = self.donor_ranges(nm).get(vterm.show(e[2][0], 10 ** 6))
                if drs:
                    top, dtop = self.hi >> 12, self.dimg.hull[1] >> 12
                    for x, k, side in ((lo, 0, 'lo'), (hi, 1, 'hi')):
                        dvs = [d[k] for d in drs]
                        if x[1] in dvs:
                            self.add(x[2].pos, 'DONOR-SAME-RANGE', True,
                                     f'KRange {side} {x[1]} of {nm} = the donor\'s {side} for the same expression in '
                                     f'its same-index state (image-independent)', lambda w, dvs=dvs: w in dvs)
                        elif any(x[1] - top == dv - dtop for dv in dvs):
                            dv = next(dv for dv in dvs if x[1] - top == dv - dtop)
                            self.add(x[2].pos, 'RANGE-IMGTOP', True,
                                     f'KRange {side} {x[1]} of {nm} = our image top page {top} (hull end {self.hi:#x}'
                                     f' / 4096) {x[1] - top:+}; the donor\'s {side} {dv} = its top page {dtop} '
                                     f'{dv - dtop:+} for the same expression',
                                     lambda w, ks={dv - dtop for dv in dvs}, top=top: w - top in ks)
                        else:
                            self.add(x[2].pos, 'DONOR-RANGE-DIFFERS', False,
                                     f'KRange {side} {x[1]} of {nm}; the donor\'s {side} for the same expression is '
                                     f'{dvs} (top pages {top} / {dtop})')
                continue
            if h == 'KAlign':
                m = U(e[2][1])
                okf = lambda w: w > 0 and w & (w - 1) == 0
                self.add(m[2].pos, 'ALIGN', okf(m[1]), f'KAlign modulus {m[1]} is a power of 2', okf)
                self.expr_consts(e[2][0], S, 'KAlign expression')
                continue
            if h not in SADDR_HEADS:
                continue
            if h == 'KWord':
                w = U(e[2][1])
                okf = lambda x: 1 <= x <= 8
                self.add(w[2].pos, 'WIDTH', okf(w[1]), f'KWord width {w[1]} bytes (1..8)', okf)
            if h == 'KFill':
                c = U(e[2][2])
                okf = lambda x: 0 <= x <= 255
                self.add(c[2].pos, 'BYTE', okf(c[1]), f'KFill byte {c[1]}', okf)
            if h == 'KBlob':
                k = U(e[2][2])
                self.add(k[2].pos, 'BLOB-IX', 0 <= k[1] < 64, f'KBlob blob index {k[1]}')
            for sa, size, szx in self.saddrs(e):
                d = dict(U(sa)[1])
                base, off = d['a_base'], U(d['a_off'])
                rule, ok, meas, absa = self.cell(base, off[1], size, mapof, litmaps, S)
                self.add(off[2].pos, rule, ok, f'{h} in {nm}: ' + meas,
                         lambda w, base=base, size=size: self.cell(base, w, size, mapof, litmaps, S)[1])
                if absa is not None and dcells is not None:
                    key = self.cell_key(absa)
                    if key is not None:
                        if key in dcells:
                            self.add(off[2].pos, 'DONOR-SAME-CELL', True,
                                     f'{h} cell {absa:#x} = {key[0]} {hx(key[1:])} in ours; the donor\'s {nm} has a '
                                     f'cell at the same place of the donor image',
                                     lambda w, b=lit(base): self.cell_key(b + w) in dcells)
                        else:
                            self.add(off[2].pos, 'NO-DONOR-CELL', True,
                                     f'{h} cell {absa:#x} = {key[0]} {hx(key[1:])}: the donor\'s {nm} has no cell there')
                if lit(base) is None:
                    self.expr_consts(base, S, f'{h} base expression')
                    if dcells is not None:
                        bs = vterm.show(base, 10 ** 6)
                        if ('rel', bs, off[1]) in dcells:
                            self.add(off[2].pos, 'DONOR-SAME-RELCELL', True,
                                     f'{h} at {vterm.show(base, 60)} + {off[1]} in {nm}: the donor\'s {nm} has a cell '
                                     f'at the same symbolic base and offset', lambda w, bs=bs: ('rel', bs, w) in dcells)
                        else:
                            self.add(off[2].pos, 'NO-DONOR-CELL', True,
                                     f'{h} at {vterm.show(base, 60)} + {off[1]}: the donor\'s {nm} has no cell there')
                else:
                    self.add(litpos(base), 'BASE-LIT', True, f'{h} base ELit {lit(base)}: '
                             + ('absolute addressing' if lit(base) == 0 else self.value(lit(base), litmaps)[2]))
                if szx is not None:
                    if lit(szx) is not None:
                        okf = lambda w, base=base, o=off[1]: w >= 0 and self.cell(base, o, w, mapof, litmaps, S)[1]
                        self.add(litpos(szx), 'LEN', okf(size), f'{h} length {size} in {nm}; ' + meas, okf)
                    else:
                        self.expr_consts(szx, S, f'{h} length expression')
                if absa is not None and size is not None and h in ('KWr', 'KZero', 'KFill', 'KUnk', 'KBlob') \
                        and size > 0:
                    ws, we = rbound(absa, 'start'), rbound(absa + size, 'end')
                    m2 = (f'{h} range [{absa:#x}, {absa + size:#x}) of {nm}: start = {ws or "NO bound"}; end = '
                          f'{we or "NO bound"}')
                    b0 = lit(base)
                    self.add(off[2].pos, 'RANGE-BOUND', ws is not None and we is not None, m2,
                             lambda w, b0=b0, size=size: rbound(b0 + w, 'start') is not None and
                             rbound(b0 + w + size, 'end') is not None)
                    self.add(litpos(szx), 'RANGE-BOUND', ws is not None and we is not None, m2,
                             lambda w, a0=absa: w > 0 and rbound(a0 + w, 'end') is not None)
                if absa is not None and h != 'KDisj':
                    writes.append((absa, absa + (size if size is not None else 0), size is None))
                # the registration of the globals runs in the init_array before main: the rule holds in the hand-off
                # states (s_pc = main), not in the earlier join state of A/AB03.v
                if rule == 'ADDR-SHADOW' and self.expshadow and size is not None and h in ('KFill', 'KZero', 'KWord') \
                        and S.get('at_main'):
                    b0 = lit(base)
                    if h == 'KWord':
                        wv = lit(e[2][2])
                        if wv is not None:
                            ok2, m3 = self.shadow_check(absa, 'word', size, wv % (1 << (8 * size)))
                            self.add(off[2].pos, 'SHADOW-GLOBALS', ok2, f'{h} in {nm}: {m3}',
                                     lambda w, b0=b0, size=size, wv=wv: self.shadow_check(
                                         b0 + w, 'word', size, wv % (1 << (8 * size)))[0])
                            self.add(litpos(e[2][2]), 'SHADOW-GLOBALS', ok2, f'{h} value in {nm}: {m3}',
                                     lambda w, a0=absa, size=size: self.shadow_check(
                                         a0, 'word', size, w % (1 << (8 * size)))[0])
                    else:
                        c = U(e[2][2])[1] if h == 'KFill' else 0
                        ok2, m3 = self.shadow_check(absa, 'fill', size, c)
                        self.add(off[2].pos, 'SHADOW-GLOBALS', ok2, f'{h} in {nm}: {m3}',
                                 lambda w, b0=b0, size=size, c=c: self.shadow_check(b0 + w, 'fill', size, c)[0])
                        self.add(litpos(szx), 'SHADOW-GLOBALS', ok2, f'{h} length in {nm}: {m3}',
                                 lambda w, a0=absa, c=c: w > 0 and self.shadow_check(a0, 'fill', w, c)[0])
                        if h == 'KFill':
                            self.add(U(e[2][2])[2].pos, 'SHADOW-GLOBALS', ok2, f'{h} byte in {nm}: {m3}',
                                     lambda w, a0=absa, size=size: self.shadow_check(a0, 'fill', size, w)[0])
                if h == 'KWord' and absa is not None and self.lo <= absa < self.hi and dkv is not None:
                    s = sym_at(self.img, absa)
                    v = lit(e[2][2])
                    if s and v is not None and (s, size) in dkv:
                        self.donor_cmp(litpos(e[2][2]), v, dkv[(s, size)], f'KWord at {hx(s)} in {nm}')
            if h == 'KWord':
                v = e[2][2]
                if lit(v) is not None:
                    self.add_value(litpos(v), lit(v), litmaps, f'KWord value in {nm}')
                else:
                    self.expr_consts(v, S, 'KWord value expression')
        return writes

    def cell_key(self, a):
        """('img', symbol, offset) of an image address; ('shadow', symbol, offset) of the address a shadow cell
        covers; None otherwise."""
        if self.lo <= a < self.hi:
            s = sym_at(self.img, a)
            return ('img',) + s if s else None
        if self.SO is not None and self.SO + (self.lo >> 3) <= a < self.SO + (self.hi >> 3):
            s = sym_at(self.img, (a - self.SO) << 3)
            return ('shadow',) + s if s else None
        return None

    def donor_cells(self, name):
        """({(symbol+offset, width): value} of the donor's absolute KWords in its hull, {cell keys of every absolute
        cell}) of the donor's state `name`, in the donor image."""
        if self.D is None or name not in self.D.defs:
            return None, None
        if name in self._dc:
            return self._dc[name]
        dimg = self.dimg
        dSO = None
        a = dimg.byname.get('__asan_shadow_memory_dynamic_address')
        kv, keys = {}, set()
        DS = self.D.state(name)
        for e in DS['kn']:
            e = U(e)
            if e[0] == 'app' and e[1] == 'KWord' and a:
                sa = dict(U(e[2][0])[1])
                if lit(sa['a_base']) == 0 and U(sa['a_off'])[1] == a[0][0]:
                    dSO = lit(e[2][2])
        for e in DS['kn']:
            e = U(e)
            if e[0] != 'app' or e[1] not in SADDR_HEADS:
                continue
            for sa, size, _ in self.saddrs(e):
                d = dict(U(sa)[1])
                b = lit(d['a_base'])
                if b is None:
                    keys.add(('rel', vterm.show(d['a_base'], 10 ** 6), U(d['a_off'])[1]))
                    continue
                x = b + U(d['a_off'])[1]
                if dimg.hull[0] <= x < dimg.hull[1]:
                    s = sym_at(dimg, x)
                    if s:
                        keys.add(('img',) + s)
                        if e[1] == 'KWord':
                            kv[(s, size)] = lit(e[2][2])
                elif dSO is not None and dSO + (dimg.hull[0] >> 3) <= x < dSO + (dimg.hull[1] >> 3):
                    s = sym_at(dimg, (x - dSO) << 3)
                    if s:
                        keys.add(('shadow',) + s)
        self._dc[name] = (kv, keys)
        return self._dc[name]

    @staticmethod
    def union(litmaps):
        out = []
        for lo, n, _ in sorted(litmaps):
            if out and lo <= out[-1][1]:
                out[-1] = (out[-1][0], max(out[-1][1], lo + n))
            else:
                out.append((lo, lo + n))
        return out

    def cell(self, base, off, size, mapof, litmaps, S):
        """(rule, ok, measurement, absolute address or None) for the cell at base + off of `size` bytes."""
        b = lit(base)
        sz = size if size is not None else 1
        img = self.img
        if b is not None:
            a = b + off
            if self.lo <= a < self.hi:
                if a == self.lo and a + sz == self.hi:
                    return ('ADDR-HULL', True, f'[{a:#x}, +{sz:#x}) = the whole image hull of the PT_LOADs', a)
                rw = None
                for k, (v, fs, m, fl, _o) in enumerate(img.loads):
                    plo, phi = v & ~(PAGE - 1), (v + m + PAGE - 1) & ~(PAGE - 1)
                    if plo <= a < phi:
                        rw = (k, plo, phi, fl)
                ok = rw is not None and bool(rw[3] & 2) and a + sz <= rw[2]
                return ('ADDR-IMG-RW', ok, f'[{a:#x}, +{sz}) in {img.section_of(a) or "no section"} at '
                        f'{hx(sym_at(img, a))}' + (f', inside writable PT_LOAD {rw[0]} pages [{rw[1]:#x}, {rw[2]:#x})'
                                                   if ok else ', NOT inside one writable PT_LOAD'), a)
            if self.SO is not None and self.SO + (self.lo >> 3) <= a and a + sz <= self.SO + (self.hi >> 3):
                ia = (a - self.SO) << 3
                return ('ADDR-SHADOW', True, f'[{a:#x}, +{sz}) = shadow of image {ia:#x} ({hx(sym_at(img, ia))}), '
                                             f'shadow offset {self.SO:#x}', a)
            for lo, n, kind in litmaps:
                if lo <= a and a + sz <= lo + n:
                    return ('ADDR-LITMAP', True, f'[{a:#x}, +{sz:#x}) inside the literal map [{lo:#x}, +{n:#x}) {kind}',
                            a)
            for lo, hi in self.union(litmaps):
                if lo <= a and a + sz <= hi:
                    return ('ADDR-LITMAP', True, f'[{a:#x}, +{sz:#x}) inside the contiguous literal maps '
                                                 f'[{lo:#x}, {hi:#x}) of {S["name"]}', a)
            return ('ADDR-NONE', False, f'[{a:#x}, +{sz}) in no image section, not image shadow, in no literal map', a)
        bs = vterm.show(base, 10 ** 6)
        bx = U(base)
        if bx[0] == 'app' and bx[1] == 'EMd':
            k = lit(bx[2][1])
            var = U(bx[2][2])
            if k == 4096 and var[0] == 'app' and var[1] == 'EVar':
                ln = mapof.get(bs)
                if ln is None:
                    return ('REL-MAP', False, f'base {bs}: no map, a_ghost, a_vis or brk region of {S["name"]} has '
                                              f'this base', None)
                ok = off >= 0 and off + sz <= ln
                return ('REL-MAP', ok, f'off {off}+{sz} {"<=" if ok else ">"} length {ln} of the region at {bs}',
                        None)
            if k == 512 and var[0] == 'app' and var[1] == 'EVar':
                mb = f'EMd Instr.M_MUL (ELit 4096) ({vterm.show(var, 10 ** 6)})'
                ln = mapof.get(mb)
                if ln is None or self.SO is None:
                    return ('REL-SHADOWMAP', False, f'base {bs}: no region at {mb} in {S["name"]}', None)
                ok = self.SO <= off and off + sz <= self.SO + ln // 8
                return ('REL-SHADOWMAP', ok, f'off {off:#x}+{sz} within [SO {self.SO:#x}, SO + length/8 '
                                             f'{self.SO + ln // 8:#x}] of the region at {mb}', None)
        if 'EMd Instr.M_MUL (ELit 32768) (EVar 0)' in bs:
            ok = -(8 << 20) - 65536 <= off <= 65536
            return ('REL-STACK', ok, f'off {off} from the entry-stack base {"within" if ok else "OUTSIDE"} '
                                     f'[-8 MiB - 64 KiB, +64 KiB]', None)
        if 'EMd Instr.M_MUL (ELit 4096) (EVar 0)' in bs and self.SO is not None:
            lo, hi = self.SO - ((8 << 20) + 65536) // 8 - 65536, self.SO + 65536
            ok = lo <= off <= hi
            return ('REL-STACKSHADOW', ok, f'off {off:#x} from the shadow of the entry-stack base: SO {self.SO:#x} '
                                           f'{off - self.SO:+#x}, {"within" if ok else "OUTSIDE"} the shadow of '
                                           f'[sp - 8 MiB - 64 KiB, sp + 64 KiB]', None)
        m = re.match(r'EAlu Instr\.ALU_ADD \((EMd Instr\.M_MUL \(ELit (4096|512)\) \(EVar \d+\))\)', bs)
        if m:
            inner = m.group(1)
            if m.group(2) == '4096':
                ln = mapof.get(inner)
                ok = ln is not None and -ln <= off <= ln
                return ('REL-MAP', ok, f'off {off} from a base inside the region at {inner} (length {ln})', None)
            mb = inner.replace('(ELit 512)', '(ELit 4096)')
            ln = mapof.get(mb)
            ok = ln is not None and self.SO is not None and self.SO - ln // 8 <= off <= self.SO + ln // 8
            return ('REL-SHADOWMAP', ok, f'off {off:#x} from a base inside the shadow of the region at {mb} '
                                         f'(length {ln}, SO {self.SO:#x})', None)
        return ('REL-OTHER', False, f'base {vterm.show(base, 120)}: no rule for this base form', None)

    def expr_consts(self, x, S, where):
        x = U(x)
        if x[0] != 'app':
            return
        h, a = x[1], x[2]
        if h in ('ELit', 'EVar'):
            return
        if h in ('EMd', 'EMdw', 'EAlu', 'EAluw'):
            op = U(a[0])[1].split('.')[-1]
            for j in (1, 2):
                v = lit(a[j])
                if v is None:
                    self.expr_consts(a[j], S, where)
                    continue
                p = litpos(a[j])
                if op == 'M_MUL':
                    okf = lambda w: w != 0 and abs(w) & (abs(w) - 1) == 0 and abs(w) < self.lo
                    self.add(p, 'SCALE', okf(v), f'{where} in {S["name"]}: scale {v} of EMd M_MUL, a power of two '
                                                 f'below the image base', okf)
                elif op == 'ALU_AND':
                    def okf(w):
                        m = w % (1 << 64)
                        n = (-m) % (1 << 64)
                        return (m & (m + 1)) == 0 or (n & (n - 1)) == 0
                    self.add(p, 'MASK', okf(v), f'{where} in {S["name"]}: mask {v} (2^j-1 or -2^j)', okf)
                else:
                    self.add_value(p, v, [], f'{where} in {S["name"]}: {op} constant')
            return
        if h == 'EExt':
            for j, nm in ((1, 'lo'), (2, 'n')):
                y = U(a[j])
                self.add(y[2].pos, 'EXT', 0 <= y[1] <= 8, f'{where}: EExt {nm} {y[1]} (byte position <= 8)')
            self.expr_consts(a[3], S, where)
            return
        if h == 'EBlob':
            for j, nm in ((1, 'k'), (2, 'i'), (3, 'n')):
                y = U(a[j])
                self.add(y[2].pos, 'BLOB', 0 <= y[1] < 4096, f'{where}: EBlob {nm} {y[1]} (small index / offset)')
            return
        for y in a:
            self.expr_consts(y, S, where)

    def kimg_pass(self, S, writes):
        ends = {b for a, b, unk in writes if not unk}
        starts = {a for a, b, unk in writes}
        dkeys = self.donor_kimg_keys(S['name'])
        for e in S['kn']:
            e = U(e)
            if e[0] != 'app' or e[1] != 'KImg':
                continue
            lo, hi = U(e[2][0]), U(e[2][1])

            def why(v, side):
                s = sym_at(self.img, v if side == 'lo' else v - 1)
                key = (side, s[0], s[1] + (0 if side == 'lo' else 1)) if s else None
                if v in self.bounds or v in (self.lo, self.hi):
                    return 'a PT_LOAD / section / hull bound'
                if side == 'lo' and v in ends:
                    return 'the end of an absolute write of the same state'
                if side == 'hi' and v in starts:
                    return 'the start of an absolute write of the same state'
                if v in self.symb:
                    return 'a symbol bound of the twin'
                if key is not None and key in dkeys:
                    return 'the same symbol + offset as a KImg bound of the donor\'s same-index state'
                return None
            for x, side in ((lo, 'lo'), (hi, 'hi')):
                if side == 'lo':
                    okf = lambda w, h_=hi[1]: self.lo <= w < h_ and why(w, 'lo') is not None
                else:
                    okf = lambda w, l_=lo[1]: l_ < w <= self.hi and why(w, 'hi') is not None
                y = why(x[1], side)
                s = sym_at(self.img, x[1] if side == 'lo' else x[1] - 1)
                self.add(x[2].pos, 'KIMG-HULL', okf(x[1]),
                         f'KImg {lo[1]:#x}..{hi[1]:#x} of {S["name"]} lies inside the hull [{self.lo:#x}, {self.hi:#x})'
                         f'; {side} {x[1]:#x} ({hx(s)}) = {y or "NO image / write / symbol / donor bound"}', okf)

    def donor_ranges(self, name):
        """{expression text: [(lo, hi)]} of the KRange entries of the donor's state `name`."""
        if self.D is None or name not in self.D.defs:
            return {}
        key = ('ranges', name)
        if key not in self._dc:
            out = collections.defaultdict(list)
            for e in self.D.state(name)['kn']:
                e = U(e)
                if e[0] == 'app' and e[1] == 'KRange':
                    out[vterm.show(e[2][0], 10 ** 6)].append((U(e[2][1])[1], U(e[2][2])[1]))
            self._dc[key] = out
        return self._dc[key]

    def donor_kimg_keys(self, name):
        if self.D is None or name not in self.D.defs:
            return set()
        out = set()
        for e in self.D.state(name)['kn']:
            e = U(e)
            if e[0] == 'app' and e[1] == 'KImg':
                lo, hi = U(e[2][0])[1], U(e[2][1])[1]
                s, t = sym_at(self.dimg, lo), sym_at(self.dimg, hi - 1)
                if s:
                    out.add(('lo', s[0], s[1]))
                if t:
                    out.add(('hi', t[0], t[1] + 1))
        return out

    def free(self, n):
        if n['role'] == 'vernac':
            cnt = len(self.F.states)
            self.add(n['pos'], 'STATE-COUNT', n['value'] == cnt,
                     f'{n.get("text", "")[:80]}: {n["value"]} = number of acs definitions in the file ({cnt})',
                     lambda w: w == cnt)
        else:
            self.add(n['pos'], 'UNREACHED', False, f'{n["role"]} at {n["slot"]}: no state uses this numeral')


def summarize(J, F):
    """pos -> dict(ok, rules, primary, meas, k)"""
    out = {}
    for n in F.nums:
        rs = J.res.get(n['pos'], [])
        ok = bool(rs) and all(r[1] for r in rs)
        rules = sorted({r[0] for r in rs})
        meas_r = [r for r in rs if r[0] not in DESCRIPTIVE] or rs
        prim = min((r[0] for r in meas_r), key=lambda r: PRIORITY.index(r) if r in PRIORITY else 0) if rs else '-'
        bad = [r for r in rs if not r[1]]
        pm = next((r[2] for r in rs if r[0] == prim), '')
        desc = next((r[2] for r in rs if r[0] in DESCRIPTIVE and r[0] != prim), '')
        meas = bad[0][2] if bad else (pm + (f' | {desc}' if desc else ''))
        out[n['pos']] = dict(ok=ok, rules=rules, primary=prim, meas=meas, k=len(rs))
    return out


def rejudge(J, pos, w):
    """True when every perturbable result of the numeral at pos still holds for value w (None: nothing perturbable)."""
    fns = [r[3] for r in J.res.get(pos, []) if r[3] is not None]
    if not fns:
        return None
    return all(f(w) for f in fns)


def triage(rows, F, S, J, rel):
    """One triage row per flagged gate row of this file (matched by line and |value|), and its controls."""
    idx = collections.defaultdict(list)
    for n in F.nums:
        idx[(n['line'], abs(n['value']))].append(n)
    out, ctl, rules, seen = [], [], collections.Counter(), set()
    for r in rows:
        if not r[11]:
            out.append(r + ['NO-PORTED-VALUE',
                            f'dst_value is empty: the gate pairs no numeral of {rel} with the donor numeral {r[10]}; '
                            f'every numeral {rel} holds is judged by its own rule (numerals table)', 'OK', '-', '-',
                            '-'])
            continue
        occ = idx.get((int(r[6]), int(r[11], 16)), [])
        if not occ:
            out.append(r + ['OPEN-NOT-FOUND', f'no numeral {r[11]} on line {r[6]} of {rel}', 'OPEN', '-', '-', '-'])
            continue
        sm = [S[n['pos']] for n in occ]
        allok = all(o['ok'] for o in sm)
        prims = collections.Counter(o['primary'] for o in sm)
        reason = 'GEN-' + (prims.most_common(1)[0][0] if len(prims) == 1 else 'SEVERAL-ROLES')
        roles = collections.Counter((n['role'], o['primary']) for n, o in zip(occ, sm))
        rtxt = '; '.join(f'{c}x {role}->{p}' for (role, p), c in roles.most_common(5)) + \
            (f'; +{len(roles) - 5} more' if len(roles) > 5 else '')
        bad = [o for o in sm if not o['ok']]
        lead = (f'{rel}:{r[6]} holds {r[11]} {len(occ)} time(s) [{rtxt}]; '
                f'{"every occurrence holds its rule" if not bad else "an occurrence FAILS"}; first: ') \
            if len(occ) > 1 else ''
        meas = lead + (f'FAILS: {bad[0]["meas"]}' if bad else sm[0]['meas'])
        out.append(r + [reason, meas[:1200], 'OK' if allok else 'OPEN', '-', '-', '-'])
        # controls: value + 4 and the donor's value (the gate's src_value), every occurrence re-judged
        sign = lambda n, w: -w if n['value'] < 0 else w
        for kind, w0 in (('plus4', None), ('donor', int(r[10], 16) if r[10] else None)):
            if kind == 'donor' and w0 is None:
                ctl.append((rel, r[6], r[11], reason, kind, 'n/a'))
                continue
            if kind == 'donor' and w0 == int(r[11], 16):
                ctl.append((rel, r[6], r[11], reason, kind, 'same-value'))
                continue
            res = []
            for n in occ:
                w = n['value'] + 4 if kind == 'plus4' else sign(n, w0)
                res.append(rejudge(J, n['pos'], w))
                for rr in J.res.get(n['pos'], []):
                    if rr[3] is not None and (n['pos'], rr[0], kind, w) not in seen:
                        seen.add((n['pos'], rr[0], kind, w))
                        rules[(rr[0], kind, 'refused' if not rr[3](w) else 'accepted')] += 1
            if all(x is None for x in res):
                verdict = 'descriptive'
            elif all(x is False for x in res if x is not None):
                verdict = 'refused'
            elif any(x is False for x in res):
                verdict = 'refused-some'
            else:
                verdict = 'accepted'
            ctl.append((rel, r[6], r[11], reason, kind, verdict))
    return out, ctl, rules


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    for o in ('--file', '--rel', '--pin', '--twin', '--kit'):
        ap.add_argument(o, required=True)
    for o in ('--donor-file', '--donor-pin', '--donor-twin', '--rows', '--out-rows', '--out-nums', '--out-ctl'):
        ap.add_argument(o)
    a = ap.parse_args()
    img = imgfacts.Img(a.pin, a.twin, a.kit)
    if not img.same_link:
        sys.exit('pin and twin PT_LOAD headers differ')
    F = File(open(a.file).read())
    D = dimg = None
    if a.donor_file:
        D = File(open(a.donor_file).read())
        dimg = imgfacts.Img(a.donor_pin, a.donor_twin, a.kit)
    J = Judge(F, img, D, dimg)
    J.run()
    S = summarize(J, F)
    if a.out_nums:
        with open(a.out_nums, 'w') as fh:
            fh.write('file\tline\tvalue\trole\tslot\tok\tprimary\trules\tn_results\tmeasurement\n')
            for n in F.nums:
                s = S[n['pos']]
                fh.write(f'{a.rel}\t{n["line"]}\t{n["value"]}\t{n["role"]}\t{n["slot"][-60:]}\t'
                         f'{"OK" if s["ok"] else "FAIL"}\t{s["primary"]}\t{"+".join(s["rules"])}\t{s["k"]}\t'
                         f'{s["meas"]}\n')
    c = collections.Counter((S[n['pos']]['ok'], S[n['pos']]['primary']) for n in F.nums)
    print(f'{a.rel}: image {img.describe()} hull {img.hull[0]:#x}..{img.hull[1]:#x} SO {J.SO}; '
          f'{len(F.nums)} numerals, {len(F.states)} states; donor {dimg.describe() if dimg else "-"}')
    for k, v in sorted(c.items(), key=lambda kv: (kv[0][0], -kv[1])):
        print(f'  numerals {"OK" if k[0] else "FAIL"}\t{v}\t{k[1]}')
    if a.rows:
        base = os.path.basename(a.rel)
        rows = [r for r in csv.reader(open(a.rows), delimiter='\t') if r and r[5] == base]
        T, C, RC = triage(rows, F, S, J, a.rel)
        with open(a.out_rows, 'w') as fh:
            for r in T:
                fh.write('\t'.join(r) + '\n')
        if a.out_ctl:
            with open(a.out_ctl, 'w') as fh:
                for r in C:
                    fh.write('\t'.join(r) + '\n')
            with open(a.out_ctl.replace('.ctl.', '.ctlrules.'), 'w') as fh:
                for rule in sorted({k[0] for k in RC}):
                    for kind in ('plus4', 'donor'):
                        ref, acc = RC[(rule, kind, 'refused')], RC[(rule, kind, 'accepted')]
                        if ref or acc:
                            fh.write(f'{a.rel}\t{rule}\t{kind}\t{ref + acc}\t{ref}\t{acc}\n')
        for k, v in collections.Counter((r[16], r[18]) for r in T).most_common():
            print(f'  rows\t{v}\t{k[0]}\t{k[1]}')
        for k, v in sorted(collections.Counter((r[4], r[5]) for r in C).items()):
            print(f'  control-rows\t{k[0]}\t{k[1]}\t{v}')
        for k, v in sorted(RC.items()):
            print(f'  control-rule\t{k[0]}\t{k[1]}\t{k[2]}\t{v}')


if __name__ == '__main__':
    main()
