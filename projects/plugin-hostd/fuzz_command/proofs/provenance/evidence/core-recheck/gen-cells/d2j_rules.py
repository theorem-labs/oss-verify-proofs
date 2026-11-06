#!/usr/bin/env python3
"""Measured rules for every numeral of the start-up image regions file (lib/A/AD2j.v, lib/B/YD2j.v).

  RO-RUN          R_A1a..R_A1o: their CImg chunks, in order, are the runs of the read-only image
                  [first PT_LOAD vaddr, page ceiling of the last read-only PT_LOAD) that no Tfib_owned_static range of
                  the sibling cell file covers, cut at the .rodata end; a region's lo/hi are its first chunk's start
                  and its last chunk's end; no write window (0 0).
  RELRO-RUN       R_A2a..R_A2f: the same over [page floor of PT_GNU_RELRO, .data start); the owned .got word that
                  holds &__stack_chk_guard is kept as an image chunk before its run, as the donor's R_A2e keeps it.
  DATA-RUN        R_A3: [first .data byte no owned range covers, .data end), writable over the whole region.
  READ-STAGE      R_RS: the extent of the twin symbol read_stage, no chunk.
  PROG-STATICS    R_A5a: lo = read_stage end, hi and the chunks before g_rec and the builtin_tls words as the donor's
                  R_A5a (same twin names); the write window ends at g_rec (the file header's rule); over
                  [g_rec, builtin_tls) the chunks are GI_cmdA's five sub-ranges (lib/<A|B>/Prog/CmdGlob.v, g_rec /
                  record.spill / g_quitting from the symtab) and the runs outside cmd_PG, the owned ranges and the
                  bytes start-up writes (the descriptors' ODR-indicator bytes, __environ).
  SAME-AS-DONOR   R_A4, R_A5b..R_A9a, R_A9b's lo: every bound and chunk offset is named in our twin as the donor's
                  is in the donor twin (symbol+offset / end of symbol / section bound / GOT word target), every chunk
                  length ends where the donor's ends, CVal widths and SOff terms equal the donor's, SLit values point at
                  the same thing (or equal the donor's plain number).
  HULL-END        R_A9b's hi and chunk end: page ceiling of the last PT_LOAD end.
"""
import re

import imgmeas
from f0m_rules import Slot, blocks, pairs

REG = re.compile(r'Definition (R_\w+) : region :=\nmkRegion None (-?\d+) (-?\d+) (-?\d+) (-?\d+)\n\[([^\]]*)\]', re.S)
CHK = re.compile(r'mkChunk (\d+) \((CImg|CZero) (\d+)\)|mkChunk (\d+) \(CVal (\d+) \((SLit|SOff) (-?\d+)(?: (-?\d+))?\)\)')


def h(x):
    return f'{x:#x}'


def parse(text):
    out = []
    for m in REG.finditer(text):
        name = m[1]
        hdr_line = text[:m.start(2)].count('\n') + 1
        lo, hi, wlo, whi = map(int, m.group(2, 3, 4, 5))
        chunks = []
        for cm in CHK.finditer(m[6]):
            ln = text[:m.start(6) + cm.start()].count('\n') + 1
            if cm[1]:
                chunks.append(dict(line=ln, kind='CImg', off=int(cm[1]), n=int(cm[3]), nums=[int(cm[1]), int(cm[3])]))
            else:
                nums = [int(cm[4]), int(cm[5]), int(cm[7])] + ([int(cm[8])] if cm[8] else [])
                chunks.append(dict(line=ln, kind='CVal', off=int(cm[4]), n=int(cm[5]), sk=cm[6], sv=int(cm[7]),
                                   so=int(cm[8]) if cm[8] else None, nums=nums))
        lines = [c['line'] for c in chunks]
        assert len(lines) == len(set(lines)), name
        out.append(dict(name=name, line=hdr_line, lo=lo, hi=hi, wlo=wlo, whi=whi, chunks=chunks))
    return out


def runs(lo, hi, holes):
    holes = sorted((a, b) for a, b in holes if a < hi and b > lo)
    out, cur = [], lo
    for a, b in holes:
        if a > cur:
            out.append((cur, min(a, hi)))
        cur = max(cur, b)
    if cur < hi:
        out.append((cur, hi))
    return out


def cut(rs, at):
    res = []
    for a, b in rs:
        for c in sorted(at):
            if a < c < b:
                res.append((a, c))
                a = c
        res.append((a, b))
    return res


def ptr_name(im, v):
    if not (im.hull[0] <= v < im.hull[1]) or not im.sec(v):
        return None
    s = im.sym_at(v)
    if s and (s[3].startswith('.str') or s[3].startswith('.L.str')):
        return f'string {im.cstr(s[0])!r}+{v - s[0]:#x}'
    if s and v - s[0] <= 0x1000:
        return f'{s[3]}+{v - s[0]:#x}'
    if im.secname(v) == '.tbss' or (im.tls and v == im.tls[0][0]):
        return f'TLS block+{v - im.tls[0][0]:#x}'
    return None


class D2j:
    def __init__(self, text, dtext, f0m_text, glob_text, im, dm):
        self.im, self.dm = im, dm
        self.R, self.DR = parse(text), parse(dtext)
        self.dmap = {r['name']: r for r in self.DR}
        self.own = [(lo, lo + sz) for ln, lo, sz, _ in pairs(blocks(f0m_text)['Tfib_owned_static'])]
        ro_loads = [l for l in im.loads if not l[4] & 2]
        self.ro_lo = im.loads[0][0]
        self.ro_hi = -(-max(l[0] + l[2] for l in ro_loads) // imgmeas.PAGE) * imgmeas.PAGE
        self.relro_lo = im.relro[0][0] // imgmeas.PAGE * imgmeas.PAGE
        self.data_lo, self.data_hi = im.section('.data')[1:3]
        self.rodata_end = im.section('.rodata')[2]
        self.exp_ro = cut(runs(self.ro_lo, self.ro_hi, self.own), [self.rodata_end])
        rr = runs(self.relro_lo, self.data_lo, self.own)
        guard = im.by_name['__stack_chk_guard'][0][0]
        self.canary = [a for a in range(im.section('.got')[1], im.section('.got')[2], 8) if im.word(a) == guard]
        exp2 = []
        d2e = self.dmap.get('R_A2e')
        donor_keeps = bool(d2e) and d2e['chunks'] and d2e['chunks'][0]['n'] == 8 and \
            dm.word(d2e['chunks'][0]['off']) == dm.by_name['__stack_chk_guard'][0][0]
        for a, b in rr:
            if donor_keeps and self.canary and a == self.canary[0] + 8 and (self.canary[0], a) in self.own:
                exp2.append((self.canary[0], a))
            exp2.append((a, b))
        self.exp_relro = exp2
        self.rs = im.by_name['read_stage'][0]
        self.glob = self._gi(glob_text)
        self.descs = im.descriptors()

    def _gi(self, t):
        names = {'A_G_REC': 'g_rec', 'A_REC_SPILL': 'record.spill', 'A_G_QUITTING': 'g_quitting'}
        out = []
        for m in re.finditer(r'zero_atA rd \(?(A_\w+)(?: \+ (\d+))?\)? (\d+)', t):
            sym = self.im.by_name[names[m[1]]][0][0]
            out.append((sym + int(m[2] or 0), sym + int(m[2] or 0) + int(m[3]), f'{names[m[1]]}+{int(m[2] or 0)}'))
        pg = []
        for m in re.finditer(r'\((A_\w+), \1 \+ (\d+)\)', t):
            sym = self.im.by_name[names[m[1]]][0][0]
            pg.append((sym, sym + int(m[2])))
        self.cmd_pg = pg
        return out

    # ---- identity judges --------------------------------------------------------------------------------
    def same_start(self, x, dx):
        both = sorted(self.im.ident_set(x) & self.dm.ident_set(dx))
        return bool(both), (both[0] if both else f'{sorted(self.im.ident_set(x))[:1]} vs donor '
                                                  f'{sorted(self.dm.ident_set(dx))[:1]}')

    def same_end(self, x, dx):
        both = sorted(self.im.end_ident_set(x) & self.dm.end_ident_set(dx))
        return bool(both), (both[0] if both else 'no common end name')

    def j_start(self, dx, what):
        def j(x):
            ok, why = self.same_start(x, dx)
            return ok, 'SAME-AS-DONOR', f'{what} {h(x)} named {why} = donor {h(dx)}', None
        return j

    def j_end(self, dx, what, base=0):
        def j(x):
            ok, why = self.same_end(base + x, base and dx or dx)
            return ok, 'SAME-AS-DONOR', f'{what} end {h(base + x)} named {why} = donor end {h(dx)}', None
        return j

    def j_eq(self, e, reason, why):
        return lambda x: (x == e, reason, why, e)

    # ---- slots ------------------------------------------------------------------------------------------
    def slots(self):
        out = []
        ro = [r for r in self.R if re.fullmatch(r'R_A1[a-o]', r['name'])]
        rel = [r for r in self.R if re.fullmatch(r'R_A2[a-f]', r['name'])]
        out += self.run_group(ro, self.exp_ro, 'RO-RUN',
                              f'runs of [{h(self.ro_lo)}, {h(self.ro_hi)}) minus Tfib_owned_static, cut at .rodata end '
                              f'{h(self.rodata_end)}')
        out += self.run_group(rel, self.exp_relro, 'RELRO-RUN',
                              f'runs of [{h(self.relro_lo)} (PT_GNU_RELRO page), {h(self.data_lo)} (.data start)) minus '
                              f'Tfib_owned_static; the owned .got word {h(self.canary[0]) if self.canary else "-"} '
                              f'holding &__stack_chk_guard kept as an image chunk, as the donor\'s R_A2e keeps '
                              f'{h(self.dmap["R_A2e"]["lo"])} (holds the donor\'s &__stack_chk_guard: '
                              f'{self.dm.word(self.dmap["R_A2e"]["lo"]) == self.dm.by_name["__stack_chk_guard"][0][0]})')
        for r in self.R:
            n = r['name']
            if n in ('R_A3',):
                out += self.data_region(r)
            elif n == 'R_RS':
                out += self.read_stage(r)
            elif n == 'R_A5a':
                out += self.prog_region(r)
            elif n == 'R_A9b':
                out += self.tail_region(r)
            elif n in self.dmap and not re.fullmatch(r'R_A[12][a-o]', n):
                out += self.moved_region(r)
        return out

    def hdr_slots(self, r, jlo, jhi, jwlo, jwhi, block=None):
        b = block or r['name']
        return [Slot(r['line'], 0, r['lo'], 'dec', b, 'region-lo', jlo),
                Slot(r['line'], 1, r['hi'], 'dec', b, 'region-hi', jhi),
                Slot(r['line'], 2, r['wlo'], 'dec', b, 'region-wlo', jwlo),
                Slot(r['line'], 3, r['whi'], 'dec', b, 'region-whi', jwhi)]

    def bound_why(self, x, end):
        """what an expected run bound is: an owned range's end/start, a cut, or the range bound."""
        if x is None:
            return '-'
        if end:
            own = [(a, b) for a, b in self.own if a == x]
            if own:
                return f'{h(x)} = start of owned ({h(own[0][0])}, {h(own[0][1] - own[0][0])})'
        else:
            own = [(a, b) for a, b in self.own if b == x]
            if own:
                return f'{h(x)} = end of owned ({h(own[0][0])}, {h(own[0][1] - own[0][0])})'
        if x == self.rodata_end:
            return f'{h(x)} = .rodata end (cut)'
        if self.canary and x == self.canary[0]:
            return f'{h(x)} = the .got word holding &__stack_chk_guard'
        if self.canary and x == self.canary[0] + 8:
            return f'{h(x)} = end of the .got word holding &__stack_chk_guard'
        names = {self.ro_lo: 'first PT_LOAD vaddr', self.ro_hi: 'page ceiling of the last read-only PT_LOAD',
                 self.relro_lo: 'page floor of PT_GNU_RELRO', self.data_lo: '.data start'}
        return f'{h(x)} = {names.get(x, "?")}'

    def run_group(self, regs, exp, reason, desc):
        out = []
        k = 0
        for r in regs:
            cs = r['chunks']
            first, last = k, k + len(cs) - 1
            e_lo = exp[first][0] if first < len(exp) else None
            e_hi = exp[last][1] if last < len(exp) else None
            out += self.hdr_slots(r, self.j_eq(e_lo, reason, f'{r["name"]} lo = start of run {first} of {len(exp)}: '
                                                             f'{self.bound_why(e_lo, False)}; {desc}'),
                                  self.j_eq(e_hi, reason, f'{r["name"]} hi = end of run {last} of {len(exp)}: '
                                                          f'{self.bound_why(e_hi, True)}; {desc}'),
                                  self.j_eq(0, reason, 'no write window (read-only image)'),
                                  self.j_eq(0, reason, 'no write window (read-only image)'))
            for c in cs:
                e = exp[k] if k < len(exp) else (None, None)
                out.append(Slot(c['line'], 0, c['off'], 'dec', r['name'], 'chunk-off',
                                self.j_eq(e[0], reason, f'run {k} of {len(exp)} starts at '
                                                        f'{self.bound_why(e[0], False)}')))
                ln = (e[1] - e[0]) if e[0] is not None else None
                out.append(Slot(c['line'], 1, c['n'], 'dec', r['name'], 'chunk-len',
                                self.j_eq(ln, reason, f'run {k} = [{h(e[0]) if e[0] else "-"}, '
                                                      f'{self.bound_why(e[1], True)}), length {ln}')))
                k += 1
        self.n_runs = getattr(self, 'n_runs', {})
        self.n_runs[reason] = (k, len(exp))
        return out

    def data_region(self, r):
        lo = max([b for a, b in self.own if a <= self.data_lo < b] or [self.data_lo])
        hi = self.data_hi
        rr = runs(lo, hi, self.own)
        why = f'first .data byte no owned range covers {h(lo)}; .data end {h(hi)}; {len(rr)} run'
        out = self.hdr_slots(r, self.j_eq(lo, 'DATA-RUN', why), self.j_eq(hi, 'DATA-RUN', why),
                             self.j_eq(lo, 'DATA-RUN', 'write window = the region'),
                             self.j_eq(hi, 'DATA-RUN', 'write window = the region'))
        for c in r['chunks']:
            out.append(Slot(c['line'], 0, c['off'], 'dec', r['name'], 'chunk-off', self.j_eq(lo, 'DATA-RUN', why)))
            out.append(Slot(c['line'], 1, c['n'], 'dec', r['name'], 'chunk-len', self.j_eq(hi - lo, 'DATA-RUN', why)))
        return out

    def read_stage(self, r):
        v, sz, t = self.rs
        why = f'twin symbol read_stage [{h(v)}, {h(v + sz)})'
        return self.hdr_slots(r, self.j_eq(v, 'READ-STAGE', why), self.j_eq(v + sz, 'READ-STAGE', why),
                              self.j_eq(0, 'READ-STAGE', 'no write window'), self.j_eq(0, 'READ-STAGE', 'no write window'))

    def tail_region(self, r):
        d = self.dmap[r['name']]
        he = self.im.hull[1]
        why = f'page ceiling of the last PT_LOAD end {h(he)}'
        out = self.hdr_slots(r, self.j_start(d['lo'], 'lo'), self.j_eq(he, 'HULL-END', why),
                             self.j_eq(0, 'HULL-END', 'no write window'), self.j_eq(0, 'HULL-END', 'no write window'))
        for c in r['chunks']:
            out.append(Slot(c['line'], 0, c['off'], 'dec', r['name'], 'chunk-off', self.j_start(d['lo'], 'lo')))
            out.append(Slot(c['line'], 1, c['n'], 'dec', r['name'], 'chunk-len',
                            self.j_eq(he - r['lo'], 'HULL-END', f'{why} - lo')))
        return out

    def chunk_slots(self, r, c, dc):
        """a chunk named as the donor's chunk dc."""
        out = [Slot(c['line'], 0, c['off'], 'dec', r['name'], 'chunk-off', self.j_start(dc['off'], 'chunk'))]
        if c['kind'] == 'CImg':
            off = c['off']

            def jn(x, off=off, de=dc['off'] + dc['n']):
                ok, why = self.same_end(off + x, de)
                return ok and dc['kind'] == 'CImg', 'SAME-AS-DONOR', f'chunk end {h(off + x)} named {why} = donor ' \
                                                                    f'end {h(de)}', None
            out.append(Slot(c['line'], 1, c['n'], 'dec', r['name'], 'chunk-len', jn))
            return out
        out.append(Slot(c['line'], 1, c['n'], 'dec', r['name'], 'cval-w',
                        self.j_eq(dc['n'], 'SAME-AS-DONOR', f'CVal width = donor {dc["n"]}')))
        if c['sk'] == 'SLit':
            dv = dc['sv']
            dn = ptr_name(self.dm, dv)

            def jv(x, dv=dv, dn=dn):
                if dn is None:
                    tls = (f'; PT_TLS (filesz, memsz, align) ours {self.im.tls_hdr[0]} = donor {self.dm.tls_hdr[0]}'
                           if self.im.tls_hdr == self.dm.tls_hdr else '; PT_TLS DIFFERS from the donor')
                    ok = x == dv and self.im.tls_hdr == self.dm.tls_hdr
                    return ok, 'SAME-AS-DONOR', f'start-up word = donor plain value {dv} at the same object{tls}', dv
                on = ptr_name(self.im, x)
                return on == dn, 'SAME-AS-DONOR', f'start-up pointer at {on} = donor {h(dv)} at {dn}', None
            out.append(Slot(c['line'], 2, c['sv'], 'dec', r['name'], 'cval-lit', jv))
        else:
            out.append(Slot(c['line'], 2, c['sv'], 'dec', r['name'], 'cval-soff',
                            self.j_eq(dc['sv'], 'SAME-AS-DONOR', f'SOff symbol index = donor {dc["sv"]}')))
            out.append(Slot(c['line'], 3, c['so'], 'dec', r['name'], 'cval-soff',
                            self.j_eq(dc['so'], 'SAME-AS-DONOR', f'SOff offset = donor {dc["so"]}')))
        return out

    def moved_region(self, r):
        d = self.dmap[r['name']]
        out = self.hdr_slots(
            r, self.j_start(d['lo'], 'lo'), self.j_end(d['hi'], 'hi'),
            self.j_start(d['wlo'], 'wlo') if d['whi'] > d['wlo'] else self.j_eq(0, 'SAME-AS-DONOR', 'donor: no window'),
            self.j_end(d['whi'], 'whi') if d['whi'] > d['wlo'] else self.j_eq(0, 'SAME-AS-DONOR', 'donor: no window'))
        if len(r['chunks']) != len(d['chunks']):
            for c in r['chunks']:
                for p, v in enumerate(c['nums']):
                    out.append(Slot(c['line'], p, v, 'dec', r['name'], 'chunk',
                                    lambda x: (False, 'OPEN', 'chunk count differs from the donor', None)))
            return out
        for c, dc in zip(r['chunks'], d['chunks']):
            out += self.chunk_slots(r, c, dc)
        return out

    def prog_region(self, r):
        im = self.im
        d = self.dmap[r['name']]
        rs_end = self.rs[0] + self.rs[1]
        grec = im.by_name['g_rec'][0][0]
        tls = im.by_name['builtin_tls'][0][0]
        out = self.hdr_slots(
            r, self.j_eq(rs_end, 'PROG-STATICS', f'read_stage end {h(rs_end)} (= donor lo by name: '
                                                 f'{self.same_start(rs_end, d["lo"])[1]})'),
            self.j_end(d['hi'], 'hi'), self.j_eq(rs_end, 'PROG-STATICS', 'write window starts at lo (as the donor)'),
            self.j_eq(grec, 'PROG-STATICS', f'write window ends at g_rec {h(grec)} (the file header: the driver\'s own '
                                            f'statics before g_rec)'))
        # [lo, g_rec): the donor's head chunks by name; the last one ends at g_rec
        head = [c for c in r['chunks'] if c['off'] < grec]
        dhead = [c for c in d['chunks'] if c['off'] < d['chunks'][0]['off'] + (grec - r['lo'])]
        for i, c in enumerate(head):
            dc = dhead[i] if i < len(dhead) else None
            if i == len(head) - 1 and c['kind'] == 'CImg':
                out.append(Slot(c['line'], 0, c['off'], 'dec', r['name'], 'chunk-off', self.j_start(dc['off'], 'chunk')))
                out.append(Slot(c['line'], 1, c['n'], 'dec', r['name'], 'chunk-len',
                                self.j_eq(grec - c['off'], 'PROG-STATICS', f'ends at g_rec {h(grec)}: no byte of '
                                                                           f'cmd_PG outside GI_cmdA')))
            else:
                out += self.chunk_slots(r, c, dc)
        # [g_rec, builtin_tls): GI_cmdA's sub-ranges + runs outside cmd_PG, owned ranges, start-up-written bytes
        odr = sorted(f[7] for dd, f in self.descs if r['lo'] <= f[7] < r['hi'])
        env = im.by_name.get('__environ', [])
        holes = list(self.own) + [(a, b) for a, b in self.cmd_pg] + [(a, a + 1) for a in odr] + \
            [(v, v + sz) for v, sz, t in env]
        mid = sorted(runs(grec, tls, holes) + [(a, b) for a, b, n in self.glob])
        why_mid = (f'GI_cmdA sub-ranges {", ".join(n for a, b, n in self.glob)} and the runs of [g_rec, builtin_tls) '
                   f'outside cmd_PG, Tfib_owned_static, the ODR-indicator bytes {",".join(h(a) for a in odr)} and '
                   f'__environ')
        midc = [c for c in r['chunks'] if grec <= c['off'] < tls]
        for i, c in enumerate(midc):
            e = mid[i] if i < len(mid) else (None, None)
            out.append(Slot(c['line'], 0, c['off'], 'dec', r['name'], 'chunk-off',
                            self.j_eq(e[0], 'PROG-STATICS', f'piece {i} of {len(mid)} = [{h(e[0]) if e[0] else "-"}, '
                                                            f'{h(e[1]) if e[1] else "-"}): {why_mid}')))
            out.append(Slot(c['line'], 1, c['n'], 'dec', r['name'], 'chunk-len',
                            self.j_eq(e[1] - e[0] if e[0] is not None else None, 'PROG-STATICS',
                                      f'piece {i} length; {why_mid}')))
        self.prog_counts = (len(midc), len(mid))
        # builtin_tls words: the donor's, by name
        tail = [c for c in r['chunks'] if c['off'] >= tls]
        dtls = self.dm.by_name['builtin_tls'][0][0]
        dtail = [c for c in d['chunks'] if c['off'] >= dtls]
        for c, dc in zip(tail, dtail):
            out += self.chunk_slots(r, c, dc)
        return out
