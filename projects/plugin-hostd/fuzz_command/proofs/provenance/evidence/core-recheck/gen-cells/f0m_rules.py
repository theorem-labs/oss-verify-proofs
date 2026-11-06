#!/usr/bin/env python3
"""Measured rules for every numeral of a generated per-binary cell file (lib/A/AF0m.v, lib/B/YF0m.v).

Each numeral of the file becomes a Slot with a judge(x) that says whether the value x is right for that place,
by a measurement of the image (pin bytes, section and segment headers, the twin's symbol table, the asan_globals
descriptors, the code's auipc references) or of the file's own text, never by a generator's output.  The same
judge re-judges perturbed values for the known-answer control.

Rules (reason ids):
  CELL-IMAGE-BYTES        z<w> (ANum A) V, [A, A+w) has file bytes: V = the pin's bytes at A, little endian.
  CELL-BSS-GUARD-ZERO     A is a guard byte (between end and the granule end) of a registered .bss global:
                          no file bytes, start-up leaves 0 (ASan poisons only the shadow).
  CELL-STARTUP-AS-DONOR   A has no file bytes (.bss) and the row sits at the donor row's position: the donor
                          cell's value is kept (V = donor V, not an address), or V points at the same thing as the
                          donor's V (same string bytes / same symbol+offset in the two twins).
  CELL-FLAG-BYTE          A = flag object + off (.bss), V = byte (off mod 8) of the word cell this file pins at
                          A - (off mod 8).
  ADDR-SAME-AS-DONOR-ROW  row k (k < 210) sits at donor row k: the twin names A the same way the donor twin names
                          the donor's A (symbol+offset, string bytes, section bound, GOT word target, .rodata bytes
                          and the functions that form the address, jump-table place), same width.
  ADDR-DESCRIPTOR-WORD    A = an 8-aligned word of the asan_globals section (a registered-global descriptor).
  ADDR-GUARD-BYTE         A in [beg+size, beg+roundup8(size)) of descriptor k (the global's guard bytes).
  ADDR-REAL-SLOT          A = start of an 8-byte twin symbol __interception::real_* (a REAL() slot).
  ADDR-FLAG-BYTE          A = flags object + off (common_flags / asan_flags twin symbol), read by a byte load
                          (lbu off(rs), rs holding the flags object: imgmeas.field_reads) in a named run-time
                          function, and V equals that byte of the word cell this file pins (no other cell at A).
  ADDR-OWNED-RO-BYTE      A lies in an owned read-only range (the file's Tfib_owned_static inside a read-only
                          PT_LOAD) and is not pinned by any other cell of the file (rom_viewO).
  SHADOW-CELL             z1 (ANum S) V of Tfib_const_shadow: S = 0x7fff8000 + g/8 for a granule g that start-up
                          poisons (descriptor k's redzone, or the asan_globals metadata), V = size%8 (partial
                          granule) or 0xf9; the file's list equals the recomputed set exactly.
  ZERO-SHADOW-BOUND       Tfib_zero_shadow entry j: the j-th run of [hull lo, hull hi) between the poisoned
                          granules, recomputed from the descriptors.
  OWNED-GUARD-RANGE       (beg+size, size_with_redzone-size) of descriptor k, in descriptor order.
  OWNED-SECTION           (asan_globals start, asan_globals size).
  OWNED-SAME-AS-DONOR-ROW the donor's owned row at the same position: lo named as the donor's lo, lo+size named
                          as the donor's end (symbol end / section end / last byte), every .got word paired.
  OWNED-RODATA-CONST      (A, w): .rodata constant A formed by a named function with a w-byte load.
  PROG-STATIC             (A, n): A = the twin symbol's start, n = that global's descriptor size field.
  HASH-OF-TR0             TFIB_HASH h = tfib_dhash (TFIB_TR0 h) (Reusable/YF0p.v's definition, recomputed here),
                          and the buckets are the hash mod d_tab_words = 2^20; A/AFek.v:14 and B/YFek.v:15 prove
                          the first by vm_compute, the file's Example the second.
  RECORD-BOUND            0xa5000 = page floor of PT_GNU_RELRO; 0x606000 = page ceiling of the last PT_LOAD end.
  MODEL-CONSTANT          the same numeral in the same place of the donor's record (40 = the junk length of
                          instance+o_comb_stats, __asan::instance having the same size in both twins; 2 = the
                          number of TFIB_TR0 traces, 2 ^ 64 = the word modulus).
  CONST-SAME-AS-DONOR     TFIB_* constant: the twin names it as the donor twin names the donor's constant of the same
                          name (object+offset; for code the function+offset);
                          TFIB_GP = the twin symbol __global_pointer$.
  CODE-SAME-AS-DONOR      DRV_TRACES / TFIB_TR0 pcs, by position: the same function+offset as the donor's.
  SYMCELL-SAME-AS-DONOR   Tfib_const_sym numerals, by position on the donor's line: offsets and plain values equal the
                          donor's, start-up pointers point at the same object+offset.
"""
import collections
import re

import imgmeas

SH = imgmeas.SHADOW_OFF
CELL = re.compile(r'\bz([1248]) \(ANum (0x[0-9a-fA-F]+|\d+)\) (0x[0-9a-fA-F]+|\d+)')
PAIR = re.compile(r'\((0x[0-9a-fA-F]+|\d+), (0x[0-9a-fA-F]+|\d+)(?: - (0x[0-9a-fA-F]+|\d+))?\)')
N_DONOR = 210
DESC_ROWS = range(156, 180)       # donor rows of cgif's 3 descriptors -> our first 3 descriptors
REAL_ROWS = (202, 203)            # donor REAL(fclose)/REAL(fopen) rows -> REAL slots of this image
GUARD_ROWS = range(205, 210)      # donor rows of a cgif literal's guard bytes -> this image's guard bytes
DONOR_GUARD_OWNED = 3             # donor Tfib_owned_static rows that are cgif's own guard rows (dropped)


def h(x):
    return f'{x:#x}'


class Slot:
    __slots__ = ('line', 'pos', 'value', 'kind', 'block', 'role', 'judge', 'donor')

    def __init__(self, line, pos, value, kind, block, role, judge, donor=None):
        self.line, self.pos, self.value, self.kind, self.block, self.role = line, pos, value, kind, block, role
        self.judge, self.donor = judge, donor


def blocks(text):
    out, cur = {}, None
    for i, t in enumerate(text.split('\n'), 1):
        m = re.match(r'(Definition|Record|Example) (\w+)', t)
        if m:
            cur = m.group(2)
            out.setdefault(cur, [])
        if cur:
            out[cur].append((i, t))
    return out


def cells(blk):
    r = []
    for ln, t in blk:
        ms = list(CELL.finditer(t))
        assert len(ms) <= 1, (ln, t)
        for m in ms:
            r.append((ln, int(m[1]), int(m[2], 0), int(m[3], 0)))
    return r


def pairs(blk):
    r = []
    for ln, t in blk:
        for m in PAIR.finditer(t):
            r.append((ln, int(m[1], 0), int(m[2], 0), int(m[3], 0) if m[3] else None))
    return r


def tfib_dhash(tr):
    """YF0p.v's tfib_dhash, transcribed: DH_M, DH_M8, DH_SEED, dh_mul, dh_step."""
    M = (1 << 64) - 1
    DH_M, DH_M8, DH_SEED = 14313749767032793493, 3829533694005038248, 10900877739976798860

    def mul(x):
        return (x * DH_M) & M

    def step(hh, w):
        k = mul(w)
        k ^= k >> 47
        k = mul(k)
        return mul(k ^ hh)
    hh = ((len(tr) * DH_M8) & M) ^ DH_SEED
    for w in tr:
        hh = step(hh, w)
    hh = step(hh, 0)
    hh ^= hh >> 47
    hh = mul(hh)
    return (hh ^ (hh >> 47)) & M


class F0m:
    def __init__(self, text, dtext, im, dm, tag):
        self.im, self.dm, self.tag = im, dm, tag
        self.b, self.db = blocks(text), blocks(dtext)
        self.abs = cells(self.b['Tfib_const_abs'])
        self.sh = cells(self.b['Tfib_const_shadow'])
        self.dabs = cells(self.db['Tfib_const_abs'])
        self.zs = pairs(self.b['Tfib_zero_shadow'])
        self.own = pairs(self.b['Tfib_owned_static'])
        self.down = pairs(self.db['Tfib_owned_static'])
        self.D = im.descriptors()
        self.glo, self.ghi = im.section('asan_globals')[1:3]
        self.guard = {}
        self.bss_guard = set()
        for k, (d, f) in enumerate(self.D):
            beg, size = f[0], f[1]
            for a in range(beg + size, beg + ((size + 7) // 8) * 8):
                self.guard[a] = k
        self.rom = im.rom()
        self.own_ro = set()
        for ln, lo, sz, _ in self.own:
            if any(l <= lo and lo + sz <= hh for l, hh in self.rom):
                self.own_ro.update(range(lo, lo + sz))
        self.word_cells = {a: (ln, v) for ln, w, a, v in self.abs if w == 8}
        self.addr_count = collections.Counter(a for ln, w, a, v in self.abs + self.sh)
        # bytes whose cover is required: descriptor words, guard bytes, owned read-only bytes
        self.cover = collections.Counter()
        for ln, w, a, v in self.abs:
            for j in range(w):
                self.cover[a + j] += 1
        self.required = set(range(self.glo, self.ghi)) | set(self.guard) | self.own_ro
        self.exp_sh, self.why_sh = self._expected_shadow()
        self.exp_zs, self.why_zs = self._expected_zero_shadow()
        self.flag_objs = {n: im.by_name[n][0] for n in ('_ZN11__sanitizer21common_flags_dont_useE',
                                                         '_ZN6__asan28asan_flags_dont_use_directlyE')}

    # ---- expected sets -------------------------------------------------------------------------------------------
    def _expected_shadow(self):
        exp, why = {}, {}
        for k, (d, f) in enumerate(self.D):
            beg, size, swr = f[0], f[1], f[2]
            lo = beg + 8 * (size // 8)
            for a in range(lo, beg + swr, 8):
                v = size % 8 if (a == lo and size % 8) else imgmeas.F9
                exp[(a >> 3) + SH] = v
                why[(a >> 3) + SH] = (f'granule {h(a)} of descriptor {k} (beg {h(beg)} size {h(size)} '
                                      f'size_with_redzone {h(swr)}): ' + ('partial granule, size%8' if v != 0xF9
                                                                           else 'redzone 0xf9'))
        for a in range(self.glo, self.ghi, 8):
            exp[(a >> 3) + SH] = imgmeas.F9
            why[(a >> 3) + SH] = f'granule {h(a)} of the asan_globals section (descriptor metadata): 0xf9'
        return exp, why

    def _expected_zero_shadow(self):
        holes = []
        for k, (d, f) in enumerate(self.D):
            beg, size, swr = f[0], f[1], f[2]
            holes.append((beg + 8 * (size // 8), beg + swr, f'descriptor {k} poisoned granules'))
        holes.append((self.glo, self.ghi, 'asan_globals section'))
        holes.sort()
        out, why, cur, cw = [], [], self.im.hull[0], 'hull start (page floor of the first PT_LOAD)'
        for lo, hi, w in holes:
            if lo > cur:
                out.append((cur, lo))
                why.append((cw, f'start of {w} ({h(lo)})'))
            if hi > cur:
                cur, cw = hi, f'end of {w} ({h(hi)})'
        if cur < self.im.hull[1]:
            out.append((cur, self.im.hull[1]))
            why.append((cw, 'hull end (page ceiling of the last PT_LOAD end)'))
        return out, why

    # ---- shared measurements ----------------------------------------------------------------------------------
    def img_word(self, a, w):
        return self.im.word(a, w) if self.im.filebacked(a, w) else None

    def ident_match(self, a, w, da, dw):
        if w != dw:
            return False, f'width {w} vs donor {dw}'
        mi = self.im.ident_set(a, w)
        md = self.dm.ident_set(da, dw)
        both = sorted(mi & md)
        if both:
            return True, both[0]
        return False, f'ours {sorted(mi)[:2]} donor {sorted(md)[:2]}'

    def ptr_name(self, im, v):
        """the thing a start-up value points at, when it reads as a pointer: a .rodata string (its bytes), a symbol
        start, or a place at most 0x1000 bytes into a named object; else None (a plain number)."""
        if not (im.hull[0] <= v < im.hull[1]) or not im.sec(v):
            return None
        s = im.sym_at(v)
        if s and (s[3].startswith('.str') or s[3].startswith('.L.str')):
            return f'string {im.cstr(s[0])!r}+{v - s[0]:#x}'
        if s and v - s[0] <= 0x1000:
            return f'{s[3]}+{v - s[0]:#x}'
        if not s and im.secname(v) == '.rodata':
            return f'.rodata C string {im.cstr(v)!r}'
        return None

    def dup_free(self, x, own_addr):
        """x is not the address of another cell of the file (cell_lookup keys on the address)."""
        n = self.addr_count.get(x, 0) - (1 if x == own_addr else 0)
        return n == 0

    def cover_kept(self, a, w):
        """removing the cell at (a, w) leaves every required byte of it covered by another cell."""
        return all(self.cover[a + j] >= 2 for j in range(w) if a + j in self.required)

    # ---- cell value rules -------------------------------------------------------------------------------------
    def val_judge(self, i, ln, w, a, v):
        im = self.im
        if im.filebacked(a, w):
            iv = im.word(a, w)
            return lambda x: (x == iv, 'CELL-IMAGE-BYTES',
                              f'pin bytes at {h(a)} ({w}, little endian, {im.secname(a)}) = {h(iv)}', iv)
        if a in self.guard:
            k = self.guard[a]
            d, f = self.D[k]
            return lambda x: (x == 0, 'CELL-BSS-GUARD-ZERO',
                              f'{h(a)} is guard byte {a - f[0] - f[1]} of descriptor {k} (beg {h(f[0])} size '
                              f'{h(f[1])}) in {im.secname(a)} (NOBITS): no file byte, load value 0', 0)
        for n, (fv, fs, ft) in self.flag_objs.items():
            if fv <= a < fv + fs and w == 1 and i >= N_DONOR:
                wa = a - (a - fv) % 8
                wl, wv = self.word_cells.get(wa, (None, None))
                if wv is None:
                    break
                bv = (wv >> (8 * (a - wa))) & 0xFF
                return lambda x: (x == bv, 'CELL-FLAG-BYTE',
                                  f'{n}+{a - fv:#x}: byte {a - wa} of the word cell z8 (ANum {h(wa)}) {h(wv)} at '
                                  f'line {wl} = {h(bv)}', bv)
        if i < N_DONOR:
            dl, dw, da, dv = self.dabs[i]
            dname = self.ptr_name(self.dm, dv)

            def j(x):
                if x == dv and (dname is None or self.ptr_name(im, x) == dname):
                    return True, 'CELL-STARTUP-AS-DONOR', (f'{im.secname(a)} (NOBITS) start-up value; donor row {i} '
                                                           f'(donor line {dl}) holds {h(dv)}, not an address'), dv
                on = self.ptr_name(im, x)
                if dname is not None and on == dname:
                    return True, 'CELL-STARTUP-AS-DONOR', (f'{im.secname(a)} (NOBITS) start-up pointer; ours points '
                                                           f'at {on}, donor row {i} (line {dl}) {h(dv)} at {dname}'), x
                return False, 'CELL-STARTUP-AS-DONOR', (f'donor row {i} (line {dl}) holds {h(dv)}'
                                                        + (f' = {dname}' if dname else '') + f'; {h(x)} is '
                                                        + (on or 'not the same thing')), None
            return j
        return lambda x: (False, 'OPEN', f'{h(a)} in {im.secname(a)}: no rule', None)

    # ---- cell address rules -----------------------------------------------------------------------------------
    def addr_judge(self, i, ln, w, a, v):
        im = self.im

        def value_ok_at(x):
            if im.filebacked(x, w):
                return im.word(x, w) == v
            return not im.filebacked(x, 1)

        if i < N_DONOR and i not in DESC_ROWS and i not in REAL_ROWS and i not in GUARD_ROWS:
            dl, dw, da, dv = self.dabs[i]

            def j(x):
                ok, why = self.ident_match(x, w, da, dw)
                ok = ok and value_ok_at(x) and self.dup_free(x, a)
                return ok, 'ADDR-SAME-AS-DONOR-ROW', (f'row {i}: twin name of {h(x)} = donor twin name of {h(da)} '
                                                      f'(donor line {dl}): {why}'), a
            return j
        if self.glo <= a < self.ghi:
            def j(x):
                ok = self.glo <= x < self.ghi and (x - self.glo) % 8 == 0 and w == 8 and value_ok_at(x) \
                    and self.dup_free(x, a) and (x == a or self.cover_kept(a, w))
                k, fld = (x - self.glo) // 64, ((x - self.glo) % 64) // 8
                return ok, 'ADDR-DESCRIPTOR-WORD', (f'asan_globals [{h(self.glo)}, {h(self.ghi)}) word: descriptor '
                                                    f'{k} field {fld}; 180 descriptors x 8 words all pinned'), a
            return j
        if a in self.guard:
            k = self.guard[a]
            d, f = self.D[k]

            def j(x):
                ok = x in self.guard and w == 1 and value_ok_at(x) and self.dup_free(x, a) and \
                    (x == a or self.cover_kept(a, w))
                return ok, 'ADDR-GUARD-BYTE', (f'{h(a)} in [{h(f[0] + f[1])}, {h(f[0] + ((f[1] + 7) // 8) * 8)}) of '
                                               f'descriptor {k} (beg {h(f[0])} size {h(f[1])}); all '
                                               f'{len(self.guard)} guard bytes pinned'), a
            return j
        reals = [x for x in im.sym_exact(a) if '__interception' in x[2] and 'real_' in x[2] and x[0] == 8]
        if reals:
            def j(x):
                r = [y for y in im.sym_exact(x) if '__interception' in y[2] and 'real_' in y[2] and y[0] == 8]
                ok = bool(r) and w == 8 and value_ok_at(x) and self.dup_free(x, a)
                return ok, 'ADDR-REAL-SLOT', (f'{h(a)} = start of twin symbol {reals[0][2]} (8 bytes); value = '
                                              f'{self.ptr_name(im, v)}'), a
            return j
        for n, (fv, fs, ft) in self.flag_objs.items():
            if fv <= a < fv + fs and w == 1:
                if not hasattr(self, '_freads'):
                    self._freads = {}
                if fv not in self._freads:
                    self._freads[fv] = im.field_reads(fv)
                rd = self._freads[fv]

                def j(x, n=n, fv=fv, fs=fs, rd=rd):
                    off = x - fv
                    rdr = [r for r in rd.get(off, []) if r[2] == 1]
                    ok = fv <= x < fv + fs and (x - off % 8) in self.word_cells and self.dup_free(x, a) and bool(rdr)
                    if ok:
                        wa = x - off % 8
                        ok = ((self.word_cells[wa][1] >> (8 * (x - wa))) & 0xFF) == v
                    who = f'{rdr[0][0]} at {h(rdr[0][1])}' + (f' and {len(rdr) - 1} more' if len(rdr) > 1 else '') \
                        if rdr else 'no byte load'
                    return ok, 'ADDR-FLAG-BYTE', (f'{n}+{off:#x} (twin symbol, {fs} bytes), read by a byte load in '
                                                  f'{who} (base register holds the flags object)'), a
                return j
        if a in self.own_ro:
            xr = im.xref_names(a)

            def j(x):
                ok = x in self.own_ro and value_ok_at(x) and self.dup_free(x, a) and (x == a or self.cover_kept(a, w))
                return ok, 'ADDR-OWNED-RO-BYTE', (f'{h(a)} in an owned read-only range of Tfib_owned_static '
                                                  f'(read-only PT_LOAD); every owned read-only byte pinned once'
                                                  + (f'; formed by {xr[0]}' if xr else '')), a
            return j
        return lambda x: (False, 'OPEN', f'{h(a)}: no rule', None)

    # ---- slots ------------------------------------------------------------------------------------------------
    def slots(self):
        out = []
        for i, (ln, w, a, v) in enumerate(self.abs):
            d = self.dabs[i] if i < N_DONOR else None
            out.append(Slot(ln, 0, a, 'hex', 'Tfib_const_abs', 'cell-addr', self.addr_judge(i, ln, w, a, v),
                            d[2] if d else None))
            out.append(Slot(ln, 1, v, 'hex', 'Tfib_const_abs', 'cell-val', self.val_judge(i, ln, w, a, v),
                            d[3] if d else None))
        sh_count = collections.Counter(a for ln, w, a, v in self.sh)
        for ln, w, a, v in self.sh:
            def ja(x, a=a, v=v, w=w):
                ok = x in self.exp_sh and self.exp_sh[x] == v and w == 1 and (x == a or sh_count[a] > 1) \
                    and (sh_count.get(x, 0) - (1 if x == a else 0)) == 0
                return ok, 'SHADOW-CELL', (f'shadow byte {h(a)} = 0x7fff8000 + g/8, {self.why_sh.get(a, "?")}; '
                                           f'{len(self.exp_sh)} expected = {len(self.sh)} in file'), a

            def jv(x, a=a):
                e = self.exp_sh.get(a)
                return x == e, 'SHADOW-CELL', f'shadow byte {h(a)}: {self.why_sh.get(a, "not poisoned")}', e
            out.append(Slot(ln, 0, a, 'hex', 'Tfib_const_shadow', 'shadow-addr', ja))
            out.append(Slot(ln, 1, v, 'hex', 'Tfib_const_shadow', 'shadow-val', jv))
        for j, (ln, lo, hi, lo2) in enumerate(self.zs):
            e = self.exp_zs[j] if j < len(self.exp_zs) else (None, None)
            wl, wh = self.why_zs[j] if j < len(self.why_zs) else ('?', '?')
            n = f'run {j} of {len(self.exp_zs)}'
            out.append(Slot(ln, 0, lo, 'hex', 'Tfib_zero_shadow', 'zsh-lo',
                            lambda x, e=e, wl=wl, n=n: (x == e[0], 'ZERO-SHADOW-BOUND', f'{n} lo = {wl}', e[0])))
            out.append(Slot(ln, 1, hi, 'hex', 'Tfib_zero_shadow', 'zsh-hi',
                            lambda x, e=e, wh=wh, n=n: (x == e[1], 'ZERO-SHADOW-BOUND', f'{n} hi = {wh}', e[1])))
            out.append(Slot(ln, 2, lo2, 'hex', 'Tfib_zero_shadow', 'zsh-lo',
                            lambda x, e=e, wl=wl, n=n: (x == e[0], 'ZERO-SHADOW-BOUND', f'{n} lo = {wl}', e[0])))
        out += self.owned_slots()
        out += self.misc_slots()
        out += self.text_slots()
        return out

    def owned_slots(self):
        im, dm = self.im, self.dm
        out = []
        n_don = len(self.down) - DONOR_GUARD_OWNED
        donor_rows = [r for r in self.down if r[1] not in self._donor_guard_los()]
        assert len(donor_rows) == n_don
        for j, (ln, lo, sz, _) in enumerate(self.own):
            if j < n_don:
                dl, dlo, dsz, dhi = donor_rows[j]
                dsz = dsz - dhi if dhi is not None else dsz
                dsz_lit = donor_rows[j][2] if dhi is None else None
                if lo == self.glo and sz == self.ghi - self.glo:
                    out.append(Slot(ln, 0, lo, 'hex', 'Tfib_owned_static', 'owned-lo',
                                    lambda x: (x == self.glo, 'OWNED-SECTION', f'asan_globals section start {h(self.glo)}',
                                               self.glo), dlo))
                    out.append(Slot(ln, 1, sz, 'hex', 'Tfib_owned_static', 'owned-sz',
                                    lambda x: (x == self.ghi - self.glo, 'OWNED-SECTION',
                                               f'asan_globals section size {h(self.ghi - self.glo)} = 180 x 64',
                                               self.ghi - self.glo), dsz))
                    continue
                out.append(Slot(ln, 0, lo, 'hex', 'Tfib_owned_static', 'owned-lo',
                                self._own_lo_judge(lo, sz, dlo, dsz, dl), dlo))
                out.append(Slot(ln, 1, sz, 'hex', 'Tfib_owned_static', 'owned-sz',
                                self._own_sz_judge(lo, sz, dlo, dsz, dl), dsz_lit if dsz_lit is not None else dsz))
                continue
            k = j - n_don
            if k < len(self.D):
                d, f = self.D[k]
                elo, esz = f[0] + f[1], f[2] - f[1]
                why = f'descriptor {k} at {h(d)}: beg {h(f[0])} size {h(f[1])} size_with_redzone {h(f[2])}'
                out.append(Slot(ln, 0, lo, 'hex', 'Tfib_owned_static', 'owned-lo',
                                lambda x, elo=elo, why=why: (x == elo, 'OWNED-GUARD-RANGE', f'beg+size; {why}', elo)))
                out.append(Slot(ln, 1, sz, 'hex', 'Tfib_owned_static', 'owned-sz',
                                lambda x, esz=esz, why=why: (x == esz, 'OWNED-GUARD-RANGE',
                                                             f'size_with_redzone-size; {why}', esz)))
                continue
            xr = im.xref_names(lo)
            wd = im.load_widths(lo)
            out.append(Slot(ln, 0, lo, 'hex', 'Tfib_owned_static', 'owned-lo',
                            lambda x, xr=xr: (im.secname(x) == '.rodata' and im.xref_names(x) == xr and bool(xr)
                                              and not im.sym_at(x), 'OWNED-RODATA-CONST',
                                              f'.rodata {h(lo)} formed by {",".join(xr)} (auipc pair)', lo)))
            out.append(Slot(ln, 1, sz, 'hex', 'Tfib_owned_static', 'owned-sz',
                            lambda x, wd=wd: (x in wd, 'OWNED-RODATA-CONST',
                                              f'the access width of {",".join(xr)} at {h(lo)}: {wd}',
                                              wd[0] if len(wd) == 1 else None)))
        return out

    def _donor_guard_los(self):
        """the donor's own guard rows: (beg+size, swr-size) of a donor descriptor."""
        out = set()
        for d, f in self.dm.descriptors():
            out.add(f[0] + f[1])
        return out

    def _own_lo_judge(self, lo, sz, dlo, dsz, dl):
        im, dm = self.im, self.dm

        def j(x):
            mi, md = im.ident_set(x, 1), dm.ident_set(dlo, 1)
            both = sorted(mi & md)
            return bool(both), 'OWNED-SAME-AS-DONOR-ROW', (f'lo {h(x)} named {both[0] if both else sorted(mi)[:2]}'
                                                           f' = donor lo {h(dlo)} (donor line {dl})'
                                                           if both else f'lo {h(x)} {sorted(mi)[:2]} vs donor '
                                                           f'{sorted(md)[:2]}'), lo
        return j

    def _own_sz_judge(self, lo, sz, dlo, dsz, dl):
        im, dm = self.im, self.dm

        def j(x):
            e, de = lo + x, dlo + dsz
            mi, md = im.end_ident_set(e), dm.end_ident_set(de)
            both = sorted(mi & md)
            ok = bool(both)
            got = ''
            if ok and im.secname(lo) == '.got':          # every GOT word of the range pairs with the donor's
                for k in range(0, x, 8):
                    if not (im.ident_set(lo + k) & dm.ident_set(dlo + k)):
                        ok, got = False, f'; GOT word {h(lo + k)} does not pair with {h(dlo + k)}'
                        break
                else:
                    got = f'; all {x // 8} GOT words pair'
            if ok and im.secname(lo) == '.rodata' and not im.sym_at(lo):
                jt = sorted(y for y in im.ident_set(lo) & dm.ident_set(dlo) if y.startswith('jt:'))
                if jt:              # a jump-table entry: its bytes are code offsets, the place is what pairs
                    ok = x == dsz
                    got = f'; jump-table entry {jt[0]}, width {x} = donor width {dsz}'
                else:
                    ok = im.read(lo, x) == dm.read(dlo, dsz) and x == dsz
                    got = f'; bytes equal ({x})' if ok else '; bytes differ'
            return ok, 'OWNED-SAME-AS-DONOR-ROW', (f'end {h(e)} named {both[0] if both else sorted(mi)[:2]} = donor '
                                                   f'end {h(de)} (donor line {dl}){got}'), sz
        return j

    # ---- text the gate paired without a flag: constants, traces, symbolic cells -------------------------------
    NUM = re.compile(r"(?<![\w'.])(0x[0-9a-fA-F]+|\d+)(?![\w'])")

    @staticmethod
    def code_ident(im, a):
        """a code address: its function and offset, and for a return address the call before it and its callee."""
        out = set()
        f = im.sym_at(a)
        if f:
            out.add(f'fn:{f[3]}+{a - f[0]:#x}')
        for back in (4, 2):
            b = im.read(a - back, back)
            if b is None:
                continue
            w = int.from_bytes(b, 'little')
            if back == 4 and w & 3 == 3 and w & 0x7F == 0x6F:            # jal
                off = imgmeas._sx(((w >> 31) << 20) | (((w >> 12) & 0xFF) << 12) | (((w >> 20) & 1) << 11)
                                  | (((w >> 21) & 0x3FF) << 1), 21)
                t = im.sym_at(a - 4 + off)
                out.add(f'ra:{f[3] if f else "?"}:call->{t[3] if t else hex(a - 4 + off)}')
            elif back == 4 and w & 3 == 3 and w & 0x7F == 0x67:          # jalr
                out.add(f'ra:{f[3] if f else "?"}:jalr')
            elif back == 2 and w & 3 == 2 and w >> 12 == 0b1001 and (w >> 7) & 31 and not (w >> 2) & 31:
                out.add(f'ra:{f[3] if f else "?"}:c.jalr')
        return out

    def text_slots(self):
        im, dm = self.im, self.dm
        out = []
        # TFIB_* constants, paired by name with the donor's
        dconst = {}
        for name in self.db:
            if name.startswith('TFIB_') and self.db[name]:
                for dl, dt in self.db[name]:
                    for m in re.finditer(r'Definition (TFIB_\w+) : Z := (0x[0-9a-fA-F]+)', dt):
                        dconst[m[1]] = int(m[2], 16)
        seen = set()
        for name in self.b:
            if not name.startswith('TFIB_'):
                continue
            for ln, t in self.b[name]:
                for k, m in enumerate(re.finditer(r'Definition (TFIB_\w+) : Z := (0x[0-9a-fA-F]+)', t)):
                    if (ln, m[1]) in seen:
                        continue
                    seen.add((ln, m[1]))
                    v, dv = int(m[2], 16), dconst.get(m[1])
                    out.append(Slot(ln, k, v, 'hex', m[1], 'const', self._const_judge(m[1], v, dv), dv))
        # DRV_TRACES and TFIB_TR0: code addresses, paired by position with the donor's
        for blk in ('DRV_TRACES', 'TFIB_TR0'):
            ours_n = [(ln, k, int(x, 0)) for ln, t in self.b[blk]
                      for k, x in enumerate(self.NUM.findall(t.split(':=')[-1] if 'Definition' in t else t))]
            don_n = [int(x, 0) for ln, t in self.db[blk]
                     for x in self.NUM.findall(t.split(':=')[-1] if 'Definition' in t else t)]
            for i, (ln, k, v) in enumerate(ours_n):
                dv = don_n[i] if i < len(don_n) else None
                out.append(Slot(ln, k, v, 'hex', blk, 'code', self._code_judge(v, dv), dv))
        # Tfib_const_sym: line by line with the donor's
        ol, dl_ = self.b['Tfib_const_sym'][1:], self.db['Tfib_const_sym'][1:]
        for (ln, t), (dln, dt) in zip(ol, dl_):
            ot, dn = self.NUM.findall(t), [int(x, 0) for x in self.NUM.findall(dt)]
            for k, tok in enumerate(ot):
                v = int(tok, 0)
                dv = dn[k] if k < len(dn) and len(ot) == len(dn) else None
                out.append(Slot(ln, k, v, 'hex' if tok.startswith('0x') else 'dec', 'Tfib_const_sym', 'sym-cell',
                                self._symcell_judge(v, dv, dln), dv))
        for ln, t in self.b['tfib_hash_buckets']:
            m = re.search(r'\[(\d+)%nat; (\d+)%nat\]', t)
            if m:
                for k in (0, 1):
                    out.append(Slot(ln, k, int(m[1 + k]), 'dec', 'tfib_hash_buckets', 'bucket-index',
                                    lambda x, k=k: (x == k, 'MODEL-CONSTANT', f'TFIB_TR0 case index {k}', k)))
        return out

    def _const_judge(self, name, v, dv):
        im, dm = self.im, self.dm

        def j(x):
            if dv is None:
                return False, 'CONST-SAME-AS-DONOR', 'no donor constant of that name', None
            if name == 'TFIB_GP':
                gp = im.by_name.get('__global_pointer$', [(None,)])[0][0]
                return x == gp, 'CONST-SAME-AS-DONOR', f'twin symbol __global_pointer$ = {h(gp)}', gp
            if im.secname(x) == '.text' or dm.secname(dv) == '.text':
                both = sorted(y for y in self.code_ident(im, x) & self.code_ident(dm, dv) if y.startswith('fn:'))
            else:
                both = sorted(im.ident_set(x) & dm.ident_set(dv))
            return bool(both), 'CONST-SAME-AS-DONOR', (f'{name} {h(x)} named {both[0]} = donor {h(dv)}' if both else
                                                       f'{name} {h(x)} not named as donor {h(dv)}'), None
        return j

    def _code_judge(self, v, dv):
        im, dm = self.im, self.dm

        def j(x):
            if dv is None:
                return False, 'CODE-SAME-AS-DONOR', 'no donor numeral at this position', None
            both = sorted(y for y in self.code_ident(im, x) & self.code_ident(dm, dv) if y.startswith('fn:'))
            return bool(both), 'CODE-SAME-AS-DONOR', (f'{h(x)} named {both[0]} = donor {h(dv)}' if both else
                                                      f'{h(x)} {sorted(self.code_ident(im, x))[:2]} vs donor '
                                                      f'{sorted(self.code_ident(dm, dv))[:2]}'), None
        return j

    def _symcell_judge(self, v, dv, dln):
        im, dm = self.im, self.dm

        def j(x):
            if dv is None:
                return False, 'SYMCELL-SAME-AS-DONOR', f'donor line {dln} has another shape', None
            dn = self.ptr_name(dm, dv) if dv >= dm.hull[0] else None
            if dn is None:
                return x == dv, 'SYMCELL-SAME-AS-DONOR', f'donor line {dln} has {dv} here (offset / plain value)', dv
            on = self.ptr_name(im, x)
            return on == dn, 'SYMCELL-SAME-AS-DONOR', f'start-up pointer at {on} = donor {h(dv)} at {dn}', None
        return j

    def misc_slots(self):
        im, dm = self.im, self.dm
        out = []
        # TFIB_PROG_STATIC
        for ln, t in self.b['TFIB_PROG_STATIC']:
            for k, m in enumerate(PAIR.finditer(t)):
                lo, n = int(m[1], 0), int(m[2], 0)
                sym = im.sym_exact(lo)
                desc = [f for d, f in self.D if f[0] == lo]
                name = sym[0][2] if sym else '?'
                dsize = desc[0][1] if desc else None
                out.append(Slot(ln, 2 * k, lo, 'hex', 'TFIB_PROG_STATIC', 'prog-lo',
                                lambda x, name=name: (any(y[2] == name for y in im.sym_exact(x)), 'PROG-STATIC',
                                                      f'twin symbol {name} starts at {h(lo)}', lo)))
                out.append(Slot(ln, 2 * k + 1, n, 'dec', 'TFIB_PROG_STATIC', 'prog-sz',
                                lambda x, dsize=dsize, name=name: (x == dsize, 'PROG-STATIC',
                                                                   f'descriptor size field of {name} = {dsize}', dsize)))
        # TFIB_HASH and the buckets
        tr0 = {}
        for ln, t in self.b['TFIB_TR0']:
            m = re.search(r'O => \[([^\]]*)\] \| _ => \[([^\]]*)\]', t)
            tr0 = {0: [int(x, 0) for x in m[1].split(';')], 1: [int(x, 0) for x in m[2].split(';')]}
        hs = {k: tfib_dhash(v) for k, v in tr0.items()}
        for ln, t in self.b['TFIB_HASH']:
            for k, m in enumerate(re.finditer(r'=> (\d+)', t)):
                out.append(Slot(ln, k, int(m[1]), 'dec', 'TFIB_HASH', 'hash',
                                lambda x, k=k: (x == hs[k], 'HASH-OF-TR0',
                                                f'tfib_dhash [{"; ".join(h(p) for p in tr0[k])}] = {hs[k]} '
                                                f'(Reusable/YF0p.v definition, recomputed; '
                                                f'{"A/AFek.v:14" if self.tag == "A" else "B/YFek.v:15"} '
                                                f'tfib_dhash_tr0 proves it by vm_compute)', hs[k])))
        for ln, t in self.b['tfib_hash_buckets']:
            m = re.search(r'= \[(\d+); (\d+)\]', t)
            if not m:
                continue
            for k in (0, 1):
                out.append(Slot(ln, 2 + k, int(m[1 + k]), 'dec', 'tfib_hash_buckets', 'bucket',
                                lambda x, k=k: (x == hs[k] % (1 << 20), 'HASH-OF-TR0',
                                                f'TFIB_HASH {k} mod d_tab_words (2^20) = {hs[k] % (1 << 20)} '
                                                f'(vm_compute Example)', hs[k] % (1 << 20))))
        # the record's numerals
        relro = im.relro[0][0] // imgmeas.PAGE * imgmeas.PAGE
        for ln, t in self.b['CmdBSyms']:
            if t.startswith('ts_junk :'):
                nums = [int(x, 0) for x in re.findall(r'0x[0-9a-fA-F]+', t)]
                out.append(Slot(ln, 0, nums[0], 'hex', 'CmdBSyms', 'rec-relro',
                                lambda x: (x == relro, 'RECORD-BOUND', f'page floor of PT_GNU_RELRO '
                                           f'{h(im.relro[0][0])} = {h(relro)}', relro)))
                out.append(Slot(ln, 1, nums[1], 'hex', 'CmdBSyms', 'rec-hull',
                                lambda x: (x == im.hull[1], 'RECORD-BOUND', f'page ceiling of the last PT_LOAD end '
                                           f'= {h(im.hull[1])}', im.hull[1])))
            elif t.startswith('ts_junk_comb') or t.startswith('ts_hash'):
                dnum = re.compile(r'(?<![\w.])(0x[0-9a-fA-F]+|\d+)(?![\w])')
                ours_n = [int(x, 0) for x in dnum.findall(t)]
                drec = self.db.get('TfibSyms') or self.db.get('CmdBSyms') or []
                dline = [dt for dl, dt in drec if dt.startswith(t.split(' ')[0] + ' ')]
                don_n = [int(x, 0) for x in dnum.findall(dline[0])] if dline else []
                ii = im.by_name['_ZN6__asanL8instanceE'][0][1]
                di = dm.by_name['_ZN6__asanL8instanceE'][0][1]
                whys = (['the junk length at instance+o_comb_stats; __asan::instance is '
                         f'{h(ii)} bytes in ours and {h(di)} in the donor twin'] if t.startswith('ts_junk_comb')
                        else ['the number of TFIB_TR0 traces (cases O and _ of the file\'s TFIB_TR0)',
                              'the word modulus 2 ^ 64', 'the word modulus 2 ^ 64'])
                for k, val in enumerate(ours_n):
                    e = don_n[k] if k < len(don_n) else None
                    same_obj = ii == di
                    out.append(Slot(ln, k, val, 'dec', 'CmdBSyms', 'rec-model',
                                    lambda x, e=e, why=whys[k], so=same_obj: (
                                        x == e and so, 'MODEL-CONSTANT',
                                        f'the donor record has {e} at the same place; {why}', e)))
        return out
