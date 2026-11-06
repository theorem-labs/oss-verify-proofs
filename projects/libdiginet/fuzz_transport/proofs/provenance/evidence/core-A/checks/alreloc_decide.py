#!/usr/bin/env python3
"""Decide, against the two images, every numeral position of alreloc_compare.py's positions.tsv that the alreloc
cross-check must not take from either tool (libdiginet/fuzz_transport image-A core, asan pin e89be137db17). Kind:
measurement; it proves no function. Copied from libdiginet/fuzz_decode's record (alreloc_decide.py,
sha256 7ec2eb592622; internal record); changes: the target image's names, and the groups this unit's
run needs (each says so).

  alreloc_decide.py --positions OUT/positions.tsv --hub HUB --ref REF --src-lib proofs/libreac/fuzz_grant/lib
                    --stage-out STAGE_OUT --unit-lib LIB --grant-elf G --grant-syms GU --target-elf T --target-syms TU
                    --model-libs proofs/omx-clap-core/fuzz_manifest/lib,proofs/cgif/cgif_file_fuzzer/lib
                    --model-elfs LIB=ELF[,LIB=ELF]   (each model lib's pinned asan image, for model_line)
                    --out-rows ROWS.tsv --out-counts COUNTS.tsv [--file-prefix proofs/libdiginet/fuzz_transport/lib/]

Scope: a position is decided when any of these holds (column `scope`):
  nonagree   its class is not agree / both-kept (every disagreement, every alreloc-unmapped / -refused, not-covered
             and added position)
  got        a value of it lies in a .got: the donor's in fuzz_grant.asan's, or port_core's or alreloc's in
             fuzz_transport.asan's (alreloc's rule `gap` maps a .got cell by its OFFSET in .got, without a flag)
  symbol     alreloc's rule is `symbol` (it moves low / model constants to symbol offsets, without a flag)
  constant   a low / model constant: both kept the donor's value inside fuzz_grant.asan's image hull with an alreloc
             rule row (a rule of alreloc's read it as no address), or a value below the image both kept with a rule
             row
  shadow     both kept a value inside the shadow of fuzz_grant.asan's image hull
  derived    both kept a value whose line gives it an image-derived role that is no address (region-list counts,
             segment sizes, R_A3's length, shadow windows, section / function ends, quotients, the image span / top page)
  moved      port_core moved it and alreloc agreed (no tool value is evidence: port_core's value is re-measured)
The other positions (both kept the donor's value: below 0x10000 with no alreloc rule row, or at / above the image top
outside the image's shadow) are listed with decision `-`.

Each decided position is decided by the first group below whose test holds. The tests read the images (bytes of the
pinned files, symbol and section tables of the unstripped twins), the donor text, the relocated text and the unit's
own lib; they never take either tool's value as evidence. A .got cell is decided by the slot's CONTENT (the two .got
tables aligned by what each slot holds, the 8 bytes at the cell in each image), never by its offset in .got.
Decisions:
  port_core right    port_core's value is the value the role gives in fuzz_transport.asan (the measurement says how)
  port_core WRONG    it is not; the right value is named
  UNDECIDED          no group decides it from the inputs given (the row says what it needs); status 3
Column alreloc_verdict judges alreloc's value by the decision (agrees / kept / flagged / WRONG / right / undecided).
"""
import argparse, bisect, collections, difflib, functools, os, re, struct, subprocess, sys
from elftools.elf.elffile import ELFFile

TOK = re.compile(r'(?<![\w])(0x[0-9a-fA-F]+|\d+)(?![\w])')
SHADOW_OFF = 0x7fff8000


def val(t):
    return int(t, 16) if t[:2].lower() == '0x' else int(t)


def hx(v):
    return '0x%x' % v


class Img:
    """the loaded bytes of the pinned (stripped) ELF and the symbol / section tables of its unstripped twin"""

    def __init__(self, stripped, unstripped):
        self.data = open(stripped, 'rb').read()
        e = ELFFile(open(stripped, 'rb'))
        self.loads = [(p['p_vaddr'], p['p_memsz'], p['p_offset'], p['p_filesz'], p['p_flags'])
                      for p in e.iter_segments() if p['p_type'] == 'PT_LOAD']
        self.entry = e.header['e_entry']
        self.phoff = e.header['e_phoff']
        u = ELFFile(open(unstripped, 'rb'))
        self.secs = sorted((s['sh_addr'], s['sh_size'], s.name) for s in u.iter_sections()
                           if s['sh_flags'] & 2 and s['sh_addr'])
        self.syms = []
        for y in u.get_section_by_name('.symtab').iter_symbols():
            if y['st_value'] and y.name and y['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT', 'STT_NOTYPE'):
                self.syms.append((y['st_value'], y['st_size'], y.name, y['st_info']['type']))
        self.syms.sort()
        self.byname = collections.defaultdict(list)
        for v, sz, n, t in self.syms:
            self.byname[n].append((v, sz, t))
        self.ss = [x for x in self.syms if x[3] in ('STT_FUNC', 'STT_OBJECT') and x[1] > 0]
        self.ss_v = [x[0] for x in self.ss]
        self.big = [x for x in self.ss if x[1] > 0x4000]
        self.top = -(-max(v + m for v, m, _, _, _ in self.loads) // 0x1000) * 0x1000
        self.ends = collections.defaultdict(list)
        for v, sz, n, t in self.ss:
            self.ends[v + sz].append((v, sz, n, t))
        self.starts = collections.defaultdict(list)
        for v, sz, n, t in self.syms:
            if not n.startswith('$'):
                self.starts[v].append((v, sz, n, t))

    def copy_index(self, n, v):
        """(index, count) of the copy of symbol name n at v among the copies of n (address order)"""
        xs = sorted(x[0] for x in self.byname.get(n, []))
        return (xs.index(v), len(xs)) if v in xs else None

    def geometry(self):
        """[(name, value)] of the image's load geometry: each PT_LOAD's bounds, page-rounded bounds and lengths, the
        image top and span"""
        out = []
        for i, (v, m, o, f, fl) in enumerate(self.loads):
            lo, hi = v // 0x1000 * 0x1000, -(-(v + m) // 0x1000) * 0x1000
            out += [('PT_LOAD[%d] vaddr' % i, v), ('PT_LOAD[%d] vaddr + memsz' % i, v + m),
                    ('PT_LOAD[%d] vaddr + filesz' % i, v + f), ('PT_LOAD[%d] memsz' % i, m),
                    ('PT_LOAD[%d] page-rounded start' % i, lo), ('PT_LOAD[%d] page-rounded end' % i, hi),
                    ('PT_LOAD[%d] page-rounded length' % i, hi - lo)]
        out += [('the image top (last PT_LOAD end, page-rounded)', self.top),
                ('the image span (image top - 0x10000)', self.top - 0x10000)]
        return out

    def rd(self, a, n):
        for va, msz, off, fsz, _ in self.loads:
            if va <= a and a + n <= va + fsz:
                return self.data[off + a - va:off + a - va + n]
            if va <= a and a + n <= va + msz:
                return bytes(n) if a >= va + fsz else self.data[off + a - va:off + fsz] + bytes(a + n - va - fsz)
        return None

    def word(self, a, n=4):
        b = self.rd(a, n)
        return int.from_bytes(b, 'little') if b is not None else None

    def holders(self, a):
        i = bisect.bisect_right(self.ss_v, a)
        out, j = [], i - 1
        while j >= 0 and i - j < 300:
            v, sz, n, t = self.ss[j]
            if v <= a < v + sz:
                out.append(self.ss[j])
            j -= 1
        out += [x for x in self.big if x[0] <= a < x[0] + x[1] and x not in out]
        return out

    def uniq(self, n):
        xs = self.byname.get(n, [])
        return xs[0] if len(xs) == 1 else None

    def sec(self, a):
        s = [(n, a - v) for v, sz, n in self.secs if v <= a < v + sz]
        return s[0] if s else None

    def secrange(self, name):
        s = [(v, sz) for v, sz, n in self.secs if n == name]
        return s[0] if s else None

    def loc(self, a):
        if a is None:
            return '-'
        h = self.holders(a)
        parts = []
        if h:
            parts.append('/'.join(sorted({'%s+0x%x' % (n, a - v) for v, sz, n, t in h})[:2]))
        else:
            st = [n for v, sz, n, t in self.syms if v == a and not n.startswith('$')]
            if st:
                parts.append('at ' + '/'.join(st[:2]))
        s = self.sec(a)
        if s:
            parts.append('%s+0x%x' % s)
        else:
            ends = [n for v, sz, n in self.secs if v + sz == a]
            if ends:
                parts.append('end of ' + '/'.join(ends))
        return ', '.join(parts) or 'in no section'

    def strz(self, a, maxn=4096):
        out = b''
        while len(out) < maxn:
            c = self.rd(a + len(out), 1)
            if c is None or c == b'\0':
                return out
            out += c
        return out

    def str_start(self, a):
        s = a
        while s > 0 and self.rd(s - 1, 1) not in (b'\0', None) and a - s < 4096:
            s -= 1
        return s


class Raw:
    """the loaded file bytes of a pinned ELF, nothing else (the model units' images; added for fuzz_transport)"""

    def __init__(self, path):
        self.data = open(path, 'rb').read()
        self.loads = [(p['p_vaddr'], p['p_offset'], p['p_filesz']) for p in ELFFile(open(path, 'rb')).iter_segments()
                      if p['p_type'] == 'PT_LOAD']

    def rd(self, a, n):
        for va, off, fsz in self.loads:
            if va <= a and a + n <= va + fsz:
                return self.data[off + a - va:off + a - va + n]
        return None



class Ctx:
    def __init__(self, a):
        self.a = a
        self.G = Img(a.grant_elf, a.grant_syms)
        self.D = Img(a.target_elf, a.target_syms)
        self.don, self.out = {}, {}
        g, d = self.G, self.D
        # the longest common prefix of the two images' .rodata (both sections start at the same address)
        gr, dr = g.secrange('.rodata'), d.secrange('.rodata')
        assert gr[0] == dr[0], (gr, dr)
        gb, db = g.rd(gr[0], gr[1]), d.rd(dr[0], dr[1])
        k = next(i for i in range(min(len(gb), len(db))) if gb[i] != db[i])
        self.ro_lo, self.ro_same = gr[0], gr[0] + k
        self.g_top, self.d_top = g.top, d.top
        self.ggot, self.dgot = g.secrange('.got'), d.secrange('.got')
        self.model_hits = {}
        # the model units' pinned images, by model lib (--model-elfs LIB=ELF,...), for model_line's content test
        self.model_img = {k: Raw(p) for k, p in (x.split('=', 1) for x in a.model_elfs.split(',') if x)}
        self.fetch_memo, self.line_hits, self.depth_memo = {}, {}, {}
        dg = dict(d.geometry())
        self.geo = collections.defaultdict(list)   # grant value -> [(transport value, name)]
        for n, v in g.geometry():
            if n in dg:
                self.geo[v].append((dg[n], n))

    def sym_twin(self, v, sz, n):
        """the transport symbol of grant symbol (v, sz, n): the unique one of that name, else the copy of the same index
        when both images hold the same number of copies; (transport start, transport size, how) or None"""
        g, d = self.G, self.D
        gu, du = g.uniq(n), d.uniq(n)
        if gu and du:
            return du[0], du[1], n
        gi = g.copy_index(n, v)
        dx = sorted(d.byname.get(n, []))
        if gi and len(dx) == gi[1]:
            y = dx[gi[0]]
            return y[0], y[1], '%s (copy %d of %d in both, by address order)' % (n, gi[0] + 1, gi[1])
        return None

    def donor(self, f):
        if f not in self.don:
            self.don[f] = subprocess.run(['git', '-C', self.a.hub, 'show', '%s:%s/%s' % (self.a.ref, self.a.src_lib, f)],
                                         check=True, capture_output=True, text=True).stdout.split('\n')
        return self.don[f]

    def relocated(self, f):
        if f not in self.out:
            self.out[f] = open(os.path.join(self.a.stage_out, f)).read().split('\n')
        return self.out[f]

    @functools.lru_cache(maxsize=None)
    def ab1w(self):
        """{tfib_A_<f> / tfib_E_<f>: value} as stage-out's A/AB1w.v defines them (the function table)"""
        p = os.path.join(self.a.stage_out, 'A/AB1w.v')
        t = open(p).read() if os.path.isfile(p) else ''
        return {n: val(v) for n, v in re.findall(r'Definition (tfib_[AE]_\w+) : Z := (0x[0-9a-fA-F]+|\d+)\.', t)}

    def unit_file(self, rel):
        p = os.path.join(self.a.unit_lib, rel)
        return open(p).read() if os.path.isfile(p) else None

    @functools.lru_cache(maxsize=None)
    def rodata_find(self, pat):
        out = []
        for v, sz, n in self.D.secs:
            if n == '.rodata':
                d = self.D.rd(v, sz)
                i = d.find(pat)
                while i >= 0:
                    out.append(v + i)
                    i = d.find(pat, i + 1)
        return tuple(out)

    @functools.lru_cache(maxsize=None)
    def twins(self, x):
        """[(transport value, how)]: the fuzz_transport.asan value of fuzz_grant.asan value x by each role that gives one:
        section bounds, the load geometry (PT_LOAD bounds and lengths, image top and span), symbol + offset (the same
        name; the same size, or the entry / the same code bytes when sizes differ; a non-unique local name by its copy
        index), a symbol's end, a named point, the .rodata identical prefix or the same string, a .got cell by its
        content, and last a section-relative position where no symbol holds x"""
        g, d = self.G, self.D
        out = []
        gsec = {n: (v, s) for v, s, n in g.secs}
        dsec = {n: (v, s) for v, s, n in d.secs}
        for n, (gv, gs) in gsec.items():
            if n in dsec:
                if x == gv + gs:
                    out.append((dsec[n][0] + dsec[n][1], 'the end of section %s' % n))
                if x == gv:
                    out.append((dsec[n][0], 'the start of section %s' % n))
        for dv, n in self.geo.get(x, []):
            out.append((dv, n))
        hold = g.holders(x)
        for v, sz, n, t in hold:
            tw = self.sym_twin(v, sz, n)
            if not tw:
                continue
            dv, dsz, how = tw
            if dsz == sz:
                out.append((dv + x - v, '%s+0x%x' % (how, x - v)))
            elif x == v:
                out.append((dv, 'the entry of %s (size 0x%x in grant, 0x%x in transport)' % (how, sz, dsz)))
            elif x - v < dsz and g.rd(x - 8, 16) is not None and g.rd(x - 8, 16) == d.rd(dv + x - v - 8, 16):
                out.append((dv + x - v, '%s+0x%x (sizes 0x%x / 0x%x; the 16 bytes around it are equal)' % (
                    how, x - v, sz, dsz)))
        for v, sz, n, t in g.starts.get(x, []):
            if any(h[2] == n for h in hold):
                continue
            tw = self.sym_twin(v, sz, n)
            if tw:
                out.append((tw[0], 'the named point %s' % tw[2]))
        for v, sz, n, t in g.ends.get(x, []):
            tw = self.sym_twin(v, sz, n)
            if tw:
                out.append((tw[0] + tw[1], 'the end of %s (start + size)' % tw[2]))
        s = g.sec(x)
        if s and s[0] == '.rodata':
            if x < self.ro_same:
                out.append((x, '.rodata+0x%x, inside the identical .rodata prefix [0x%x, 0x%x)' % (
                    s[1], self.ro_lo, self.ro_same)))
            else:
                for glo_, ghi_, sh in self.ro_align():
                    if glo_ <= x < ghi_:
                        out.append((x + sh, '.rodata+0x%x in the 8-byte-word block [%s, %s) of fuzz_grant.asan\'s .rodata, '
                                            'whose %d bytes occur once in fuzz_transport.asan\'s .rodata, at [%s, %s) (shift '
                                            '%+d)' % (s[1], hx(glo_), hx(ghi_), ghi_ - glo_, hx(glo_ + sh), hx(ghi_ + sh), sh)))
                st = g.str_start(x)
                b = g.strz(st)
                if len(b) >= 2:
                    for fv in self.rodata_find(b'\0' + b + b'\0'):
                        out.append((fv + 1 + x - st, 'the string %r + %d' % (b.decode('latin1')[:60], x - st)))
        if self.ggot[0] <= x <= self.ggot[0] + self.ggot[1]:
            out += self.got_twin(x)
        if s and not hold and not out and s[0] in dsec:
            gv, gs = gsec[s[0]]
            dv, ds = dsec[s[0]]
            out.append((dv + s[1], '%s+0x%x (section-relative; no symbol holds it)' % s))
            out.append((dv + ds - (gv + gs - x), '%s end - 0x%x (section-relative; no symbol holds it)' % (
                s[0], gv + gs - x)))
        return out

    @functools.lru_cache(maxsize=None)
    def ro_align(self):
        """[(grant lo, grant hi, shift)]: blocks of the two .rodata sections that hold the same content, by aligning their
        8-byte words (difflib, equal runs); a run is kept when it is at least 8 words (64 bytes) long and its bytes occur
        exactly once in fuzz_transport.asan's .rodata (added for fuzz_transport: its merged 8-byte constants carry two
        constants fuzz_grant's lack, at 0x10350 and 0x10398, so the constants after them sit 8 / 16 bytes higher)"""
        g, d = self.G, self.D
        gl, gs = g.secrange('.rodata')
        dl, ds = d.secrange('.rodata')
        gw = [g.rd(gl + 8 * i, 8) for i in range(gs // 8)]
        dw = [d.rd(dl + 8 * i, 8) for i in range(ds // 8)]
        db = d.rd(dl, ds)
        out = []
        for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, gw, dw, autojunk=False).get_opcodes():
            if tag != 'equal' or i2 - i1 < 8:
                continue
            blk = b''.join(gw[i1:i2])
            k = db.find(blk)
            if k >= 0 and db.find(blk, k + 1) < 0 and dl + k == dl + 8 * j1:
                out.append((gl + 8 * i1, gl + 8 * i2, (dl + 8 * j1) - (gl + 8 * i1)))
        return tuple(out)

    def got_slot_key(self, I, s):
        """what a .got slot holds, image-independently: a section-bound name at the address it holds (__start_X /
        __stop_X, which may coincide with the next object in one image only), else (symbol, offset), else the named
        points at it, else its section; a non-address value is the literal"""
        w = I.word(s, 8)
        if 0x10000 <= w < I.top:   # an address of the image (each image's own top: fuzz_transport.asan's is above 0x600000)
            pts = tuple(sorted({n for v, sz, n, t in I.starts.get(w, [])}))
            bnd = tuple(n for n in pts if n.startswith(('__start_', '__stop_')))
            if bnd:
                return ('at', bnd)
            h = I.holders(w)
            if h:
                return ('sym', h[0][2], w - h[0][0])
            if pts:
                return ('at', pts)
            sc = I.sec(w)
            return ('sec', sc[0] if sc else None)
        return ('lit', w)

    def got_key_str(self, key):
        return ('%s+0x%x' % key[1:] if key[0] == 'sym' else 'the value %s' % hx(key[1]) if key[0] == 'lit'
                else 'the address of %s' % '/'.join(key[1]) if key[0] == 'at' else 'an address in %s' % key[1])

    @functools.lru_cache(maxsize=None)
    def got_align(self):
        """{grant slot: (transport slot, key)} by aligning the two .got tables' slot contents (difflib, equal runs)"""
        g, d = self.G, self.D
        glo, gsz = self.ggot
        dlo, dsz = self.dgot
        gk = [self.got_slot_key(g, s) for s in range(glo, glo + gsz, 8)]
        dk = [self.got_slot_key(d, s) for s in range(dlo, dlo + dsz, 8)]
        sm = difflib.SequenceMatcher(None, gk, dk, autojunk=False)
        m = {}
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag == 'equal':
                for k in range(i2 - i1):
                    m[glo + 8 * (i1 + k)] = (dlo + 8 * (j1 + k), gk[i1 + k])
        self.got_stats = (len(gk), len(dk), len(m))
        return m

    @functools.lru_cache(maxsize=None)
    def got_twin(self, x):
        """[(transport value, how)] of a grant .got cell x by the slot's CONTENT, never by the offset in .got"""
        glo, gsz = self.ggot
        if x == glo + gsz:
            return []
        slot = x - (x - glo) % 8
        m = self.got_align()
        if slot not in m:
            return []
        ds, key = m[slot]
        return [(ds + x - slot, 'the .got cell holding %s: grant cell %s holds %s (.got+0x%x), transport cell %s holds %s '
                                '(.got+0x%x); the two .got tables align slot by slot by content, %d of %d / %d slots' % (
                                    self.got_key_str(key), hx(slot), hx(self.G.word(slot, 8)), slot - glo, hx(ds),
                                    hx(self.D.word(ds, 8)), ds - self.dgot[0], self.got_stats[2], self.got_stats[0],
                                    self.got_stats[1]))]

    def got_offset_value(self, x):
        """the transport cell at the SAME .got offset as grant cell x (what alreloc's rule `gap` computes)"""
        return self.dgot[0] + x - self.ggot[0]

    def explain(self, d, p):
        """the first role under which grant value d is transport value p, else None"""
        for fv, how in self.twins(d):
            if fv == p:
                return 'address: %s in both images' % how
        if SHADOW_OFF <= d < SHADOW_OFF + 0x10000000:
            for k in range(8):
                x = (d - SHADOW_OFF) * 8 + k
                for fv, how in self.twins(x):
                    if SHADOW_OFF + fv // 8 == p:
                        return 'the shadow byte 0x7fff8000 + x / 8 of x = %s (grant x = %s, transport x = %s)' % (
                            how, hx(x), hx(fv))
        for m in (8, 4, 4096):
            if not 0x10000 <= d * m < 0x600000:
                continue
            for k in range(m if m <= 8 else 1):
                x = d * m + k
                for fv, how in self.twins(x):
                    if fv // m == p:
                        return 'the quotient x / %d of x = %s (grant x = %s, transport x = %s)' % (m, how, hx(x), hx(fv))
        return None

    def right_value(self, d):
        """the transport value(s) the address roles give for grant value d (for a WRONG row's right value)"""
        return sorted({fv for fv, how in self.twins(d)})

    def model_count(self, tok):
        """{model lib: occurrences of the numeral tok} in the other units' libs at REF (git grep -w)"""
        if tok not in self.model_hits:
            hits = {}
            for lib in self.a.model_libs.split(','):
                r = subprocess.run(['git', '-C', self.a.hub, 'grep', '-c', '-w', '-e', tok, self.a.ref, '--', lib],
                                   capture_output=True, text=True).stdout
                hits[lib] = sum(int(l.rsplit(':', 1)[1]) for l in r.split('\n') if l)
            self.model_hits[tok] = hits
        return self.model_hits[tok]


REGS = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
        's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']


def decode_insn(w):
    """the RV64 load / jal / jalr an instruction word encodes, else None"""
    if w is None or w & 3 != 3:
        return None
    op, rd, f3, rs1 = w & 0x7f, (w >> 7) & 31, (w >> 12) & 7, (w >> 15) & 31
    if op == 0x03 and f3 != 7:
        imm = w >> 20
        imm = imm - 4096 if imm & 0x800 else imm
        return '%s %s, %d(%s)' % (['lb', 'lh', 'lw', 'ld', 'lbu', 'lhu', 'lwu'][f3], REGS[rd], imm, REGS[rs1])
    if op == 0x6f:
        return 'jal %s' % REGS[rd]
    if op == 0x67 and f3 == 0:
        return 'jalr %s, (%s)' % (REGS[rd], REGS[rs1])
    return None


RIGHT, WRONG = 'port_core right', 'port_core WRONG'


def al_note(r, c):
    """what alreloc did with the position, for the record (never evidence)"""
    if r['class'] == 'alreloc-refused':
        return 'alreloc wrote no report for the file'
    if r['class'] == 'alreloc-unmapped':
        return 'alreloc flagged it (%s)%s' % (r['kind'], ' and would have written %s' % r['alreloc']
                                             if r['al'] is not None and r['al'] != r['d'] else '')
    if r['al'] is None or r['p'] is None:
        return ''
    if r['al'] == r['p']:
        return 'alreloc gives the same value (rule %s)' % r['rule'] if r['rule'] != '-' else 'alreloc kept it too'
    if r['al'] == r['d']:
        return 'alreloc kept %s (rule %s)' % (r['alreloc'], r['rule'])
    return 'alreloc wrote %s (rule %s; %s in fuzz_transport.asan)' % (
        r['alreloc'], r['rule'], c.D.loc(r['al']) if r['al'] >= 0x1000 else 'no address')


def al_verdict(r, decision):
    """alreloc's value judged by the decision (column alreloc_verdict): `agrees` (port_core's value), `kept` (both kept
    the donor's value), `flagged` (alreloc gave no value of its own), `WRONG` (not the value the decision gives),
    `right` (port_core WRONG and alreloc's value the right one), `undecided` / `-`"""
    if r['class'] in ('alreloc-unmapped', 'alreloc-refused'):
        return 'flagged'
    if r['al'] is None or r['p'] is None:
        return '-'
    if decision.startswith('UNDECIDED'):
        return 'undecided'
    if decision.startswith(WRONG):
        m = re.search(r'right value ((?:0x[0-9a-fA-F]+|\d+)(?: or (?:0x[0-9a-fA-F]+|\d+))*)', decision)
        return 'right' if m and r['al'] in {val(x) for x in m.group(1).split(' or ')} else 'WRONG'
    if r['al'] == r['p']:
        return 'kept' if r['al'] == r['d'] else 'agrees'
    return 'WRONG'


def use(r, w=45):
    t = r['text']
    return t[max(0, r['col'] - w):r['col'] + len(r['donor']) + 25].strip()


# ------------------------------------------------------------------------------------------------ groups
# Each group: (name, test(row, ctx) -> None | (decision, measurement)). A row is a dict of positions.tsv's columns plus
# `text` (the donor line), `pre` / `post` (the text before / after the numeral), `d` / `p` / `al` (integer values, None
# when absent).

def notice(r, c):
    """the numeral is in the donor's leading comment block (licence notice and its `Modified by` lines)"""
    L = c.donor(r['file'])
    i, depth = 0, 0
    block = set()
    while i < len(L) and (depth > 0 or L[i].strip().startswith('(*')):
        depth = max(0, depth + L[i].count('(*') - L[i].count('*)'))
        block.add(i + 1)
        i += 1
    if r['ln'] not in block:
        return None
    kept_line = L[r['ln'] - 1] in c.relocated(r['file'])
    if r['p'] != r['d'] or not kept_line:
        return (WRONG + ': a donor notice line was changed (the header rule keeps it byte for byte); right value %s'
                % r['donor'], 'donor notice line %d; stage-out holds it byte for byte: %s' % (r['ln'], kept_line))
    return (RIGHT + ': kept (a notice comment). The numeral is in the donor\'s licence-notice block (line %d), whose '
            '`Modified by` lines record the donor\'s own port history and name fuzz_grant.asan\'s (or cgif\'s) values; '
            'the header rule keeps those lines byte for byte and no proof reads a comment' % r['ln'],
            'donor line %d is in the notice block and stage-out holds it byte for byte; %s in fuzz_grant.asan is %s; %s'
            % (r['ln'], r['donor'], c.G.loc(r['d']) if r['d'] >= 0x1000 else 'no address', al_note(r, c)))


def got_cell(r, c):
    """a value inside a .got: decided by the cell's content (8 bytes at the cell in each image), never its offset"""
    glo, gsz = c.ggot
    dlo, dsz = c.dgot
    in_g = glo <= r['d'] < glo + gsz
    in_d = r['p'] is not None and dlo <= r['p'] < dlo + dsz
    in_da = r['al'] is not None and dlo <= r['al'] < dlo + dsz
    if not (in_g or in_d or in_da):
        return None
    if r['p'] is None:
        return None
    if in_g:
        tw = c.got_twin(r['d'])
        if not tw:
            return ('UNDECIDED: grant .got cell %s has no content twin in transport\'s .got' % r['donor'], '')
        right, how = tw[0]
        offv = c.got_offset_value(r['d'])
        alw = al_note(r, c)
        if r['al'] is not None and r['al'] != right and r['al'] != r['d'] and r['class'] != 'alreloc-unmapped':
            alw += '; alreloc wrong: the transport cell at the same .got offset is %s, which holds %s (%s)' % (
                hx(offv), hx(c.D.word(offv - (offv - dlo) % 8, 8)), c.got_key_str(c.got_slot_key(c.D, offv - (offv - dlo) % 8)))
        elif r['al'] == right and r['rule'].startswith('gap'):
            alw += '; alreloc\'s rule gap maps by .got offset: the same-offset cell %s is the content twin here' % hx(offv)
        if r['p'] == right:
            return (RIGHT, '%s; the line uses it as `%s`; %s' % (how, use(r), alw))
        if r['p'] == r['d']:
            # kept: a .got address the line does not use as this image's cell (a comment naming another image ...)
            return None
        return (WRONG + ': right value %s' % hx(right), '%s; port_core wrote %s (%s); %s' % (
            how, r['port_core'], c.D.loc(r['p']), alw))
    return None


def in_comment(r, c):
    """True when the numeral lies inside a Coq comment: an unclosed `(*` before it on its line, or a comment that an
    earlier donor line opened and that is still open"""
    f = r['file']
    if f not in c.depth_memo:
        dep, depth = [], 0
        for l in c.donor(f):
            dep.append(depth)
            depth = max(0, depth + l.count('(*') - l.count('*)'))
        c.depth_memo[f] = dep
    pre = r['pre']
    return c.depth_memo[f][r['ln'] - 1] + pre.count('(*') - pre.count('*)') > 0


def comment(r, c):
    """a kept numeral of a comment (not the leading notice block): no proof reads it"""
    if r['p'] != r['d'] or r['ln'] is None or not in_comment(r, c):
        return None
    t = r['text']
    names = re.findall(r'fuzz_grant|cgif\w*|fuzz_manifest|grant', t)
    return (RIGHT + ': kept (a comment). The numeral is inside a comment, which no proof reads; port_core keeps the '
            'donor\'s sentence%s' % (' (it names %s: it describes the donor\'s image)' % '/'.join(sorted(set(names)))
                                    if names else ''),
            'the comment: `%s`; read as an address of fuzz_grant.asan %s is %s; %s' % (
                t.strip()[:120], r['donor'], c.G.loc(r['d']) if r['d'] >= 0x1000 else 'no address', al_note(r, c)))


def insn_word(r, c):
    """an instruction word argument (icpt_ld8 W ... rd rs WORD ...): the load the wrapper executes"""
    if not re.search(r'\bicpt_ld8\b', r['text']) or not r['donor'].isdigit():
        return None
    m = re.search(r'(\d+)%bv\s+(\d+)%bv\s+' + r['donor'] + r'\b', r['text'])
    w = r['d']
    dd = decode_insn(w)
    if not m or dd is None:
        return None
    rd, rs = int(m.group(1)), int(m.group(2))
    if dd != 'ld %s, 0(%s)' % (REGS[rd], REGS[rs]):
        return None
    nf = c.D.data.count(struct.pack('<I', w))
    how = '%d = %s encodes `%s` (rd = rs1 = x%d, the line\'s %d%%bv %d%%bv); the word occurs %d times in ' \
          'fuzz_transport.asan; %s' % (w, hx(w), dd, rd, rd, rs, nf, al_note(r, c))
    if r['p'] != r['d']:   # added for fuzz_transport (the plant sweep): a changed instruction word is wrong
        return (WRONG + ': right value %s (an instruction word, unchanged)' % r['donor'],
                '%s; port_core wrote %s' % (how, r['port_core']))
    return (RIGHT + ': kept. An instruction word, not an address: icpt_ld8\'s word argument, the 8-byte load the code '
            'executes at that step; its encoding does not depend on where the code lies', how)


MODEL_PRE = re.compile(r'(\bmcheck\b.*(\)|\bend)\s*$|\bspin\s*$|\bFCheck\s*$|\bISpin\s*$|\bfail \(FCheck\s*$)')


def model_label(r, c):
    """a check-site label of the shared allocator model (mcheck ... N / spin N / FCheck N / ISpin N)"""
    if not MODEL_PRE.search(r['pre']) or r['p'] != r['d']:
        return None
    if not re.match(r'\s*(;;|\)|\s*$|else\b)', r['post']) and not re.match(r'\s*$', r['post']):
        return None
    h = c.model_count(r['donor'])
    if not all(h.values()):
        return None
    return (RIGHT + ': kept (a model constant). A check-site label of the shared allocator model (lib/Reusable YG00\'s '
            'mcheck / spin / FCheck labels), the same number in every unit whatever its image',
            'the same numeral %s at the same model text in %s at %s; read as an address in fuzz_grant.asan it would be '
            '%s; %s' % (r['donor'], ', '.join('%s (%d)' % (k, v) for k, v in h.items()), c.a.ref[:12],
                        c.G.loc(r['d']), al_note(r, c)))


# constants whose use on their line makes them no image position: ({donor tokens}, line pattern, role)
CONST_ROLES = [
    ({'65536'}, r'', '2^16 (a multiplier, modulus, 64 KiB alignment or length); as an address it would be the image '
                     'start 0x10000, the same in both images'),
    ({'262144'}, r'', '2^18, a size / modulus of the allocator model'),
    ({'131072'}, r'131072', '2^17, a region length of the allocator model (QSv + 131072)'),
    ({'524288', '1048576', '4194304'}, r'replace \(2 \* \d+\) with|\* 524288', 'a power of two in a size identity '
                                                                             '(2 * 524288 = 1048576 ...)'),
    ({'0x100000'}, r'NB \+ 0x100000', 'a 1 MiB block length (NB + 0x100000), not a position'),
    ({'0x104022'}, r'Definition FLR : word := Z_to_bv 64 0x104022', 'mmap flags (FLR = MAP_FIXED_NOREPLACE 0x100000 | '
                                                                    'MAP_NORESERVE 0x4000 | MAP_ANONYMOUS 0x20 | '
                                                                    'MAP_PRIVATE 0x2)'),
    ({'3727360'}, r'Definition AMETA_SIZE : Z := 3727360', 'a size (AMETA_SIZE)'),
    ({'65538'}, r'65538', 'a page-count bound (18 <= p <= 65538; Z.log2 65538 = 16)'),
    ({'65793'}, r'4311810305', 'the byte pattern 0x10101 in a lemma about 4311810305 = 0x101010101'),
    ({'100000'}, r'100000', 'a loop bound / fuel count of the quarantine model (do_recycle / pop_batches / irun '
                            '100000)'),
    ({'127070'}, r'TOT <= 127070', 'a bound of the depot model (TOT <= 127070)'),
    ({'1048575'}, r'mkAF 0 1048575 0', 'a fact range [0, 2^20 - 1] (mkAF 0 1048575 0)'),
    ({'2240000', '2107576'}, r'length bsb|cat_struct_size', 'a length bound of the start-up model (bsb / argument '
                                                             'bytes)'),
    ({'280000'}, r'W <= 280000|EVar V_W\) 0 280000', 'a length bound of the start-up model (W <= 280000)'),
    ({'524280'}, r'SHBv', 'SHADOW_OFF / 4096 = 0x7fff8000 / 4096 (the witness of (SHBv + x / 8) mod 4096 = 0)'),
    ({'4194240'}, r'exists \(4194240 \+ q', 'SHADOW_OFF / 512 = 0x7fff8000 / 512 (a witness of SHAv mod 2^9 = 0)'),
    ({'262136'}, r'SOff rADR 262136|q \* 8 \+ 262136', 'the offset 32767 * 8 from a symbolic base (SOff rADR 262136; '
                                                         'q * 8 + 262136 = (q + 32767) * 8)'),
    ({'1441792'}, r'\(\(11571200 - \(4096 \+ 32768\)\) / 8\) with 1441792', '(11571200 - (4096 + 32768)) / 8, the '
                                                                           'fake-stack layout arithmetic of the '
                                                                           'runtime (no image position)'),
    ({'0x20112D'}, r'KRange \(EVar V_HW\) 0x112D 0x20112D', 'an AT_HWCAP value range (0x112D = the RV64 letters '
                                                             'I M A F D C, 0x20112D adds V), not an address'),
]


def const(r, c):
    """a constant whose use on its line makes it no image position; port_core keeps its value"""
    for toks, pat, role in CONST_ROLES:
        if r['donor'] in toks and re.search(pat, r['text']):
            if r['p'] != r['d']:
                return (WRONG + ': right value %s (a constant, unchanged)' % r['donor'],
                        '%s; port_core wrote %s' % (role, r['port_core']))
            return (RIGHT + ': kept (a model constant). %s' % role,
                    'the line\'s use: `%s`; read as an address it would be %s in fuzz_grant.asan; %s' % (
                        use(r, 50), c.G.loc(r['d']) if r['d'] >= 0x1000 else 'below the image', al_note(r, c)))
    return None


def rodata_prefix(r, c):
    """a kept .rodata address inside the two images' identical .rodata prefix"""
    if r['p'] != r['d'] or not (c.ro_lo <= r['d'] < c.ro_same):
        return None
    gb, db = c.G.rd(r['d'], 8), c.D.rd(r['d'], 8)
    assert gb == db
    s = c.G.strz(r['d'])
    what = ('the string %r' % s.decode('latin1')[:60]) if len(s) >= 2 and all(32 <= b < 127 for b in s) else \
        'the 8 bytes %s' % gb.hex()
    return (RIGHT + ': kept. A .rodata address below 0x%x, where the two images\' .rodata is byte for byte the same, so '
            'the same address holds the same constant in fuzz_transport.asan' % c.ro_same,
            '%s holds %s in both images (.rodata+0x%x); first differing .rodata byte at 0x%x; %s' % (
                r['donor'], what, r['d'] - c.ro_lo, c.ro_same, al_note(r, c)))


def header(r, c):
    """the program headers' address: the first PT_LOAD maps the ELF header at 0x10000, e_phoff 0x40, in both"""
    if r['d'] != 0x10040 or r['p'] != r['d'] or 'ph_addr' not in r['text']:
        return None
    ok = c.G.phoff == c.D.phoff == 0x40 and c.G.loads[0][0] == c.D.loads[0][0] == 0x10000
    return ((RIGHT + ': kept. The program headers\' address (first PT_LOAD base 0x10000 + e_phoff 0x40), the same in both '
             'images') if ok else WRONG, 'e_phoff %s / %s, first PT_LOAD base %s / %s (grant / transport); %s' % (
        hx(c.G.phoff), hx(c.D.phoff), hx(c.G.loads[0][0]), hx(c.D.loads[0][0]), al_note(r, c)))


def notice_other_comment(r, c):
    """ACeg.v:27: a comment naming cgif_file's GOT words"""
    if not ('cgif_newgif' in r['text'] and r['p'] == r['d']):
        return None
    return (RIGHT + ': kept. The comment names cgif_file\'s three GOT words (cgif_newgif, cgif_raw_newgif, '
            'cgif_raw_addframe), another image\'s addresses; fuzz_grant.asan has no GOT word there',
            '%s in fuzz_grant.asan is %s, outside its .got [%s, %s); %s' % (
                r['donor'], c.G.loc(r['d']), hx(c.ggot[0]), hx(c.ggot[0] + c.ggot[1]), al_note(r, c)))


def span(r, c):
    """the image span (image top - 0x10000), a length next to its base 0x10000 / 65536: TFIB_IMG (lo, len), loc_ok lo
    len, keep_cell(s) _ lo len, ZONE p lo len, IMG_P (ELit 65536, ELit len), 0x10000 + len"""
    gs, ds = c.g_top - 0x10000, c.d_top - 0x10000
    if r['d'] != gs or not re.search(r'\b(0x10000|65536)\b', r['text']):
        return None
    ok = r['p'] == ds
    return (RIGHT if ok else WRONG + ': right value %s' % (hx(ds) if r['donor'].startswith('0x') else ds),
            'a length, not a bound (the line pairs it with the base 0x10000: `%s`); the image hull is [0x10000, %s) in '
            'fuzz_grant.asan and [0x10000, %s) in fuzz_transport.asan (last PT_LOAD end page-rounded), so len is %s -> %s; '
            '%s' % (use(r, 40), hx(c.g_top), hx(c.d_top), hx(gs), hx(ds), al_note(r, c)))


REGION_IMG = re.compile(r'\bIMG_(REGIONS|[A-Z]{1,3})\b')
REGION_MEM = re.compile(r'\bss_mem\b|\bsmem\b|pieces|\bL_mem\b|\bCM_mem\b|\bRT_REGIONS\b|\bsubmem\b|\bREG0\w*|\bTBLS\w*|'
                        r'\bM?K?TAIL\w*')


def region_role(r):
    """True when the numeral is a count or a list position on a line about the image region lists (IMG_REGIONS and
    the symbolic memories that hold it): any count on an IMG_* line, a count >= 20 on a symbolic-memory line"""
    t, tok = r['text'], re.escape(r['donor'])
    if not re.search(r'\b(firstn|skipn|dropAt|replAt|insAt)\s+\(?' + tok + r'\b|length [^=]*= \(?' + tok +
                     r'(%nat)?\b|length IMG_\w+ = ' + tok + r'\b', t):
        return False
    return bool(REGION_IMG.search(t)) or (bool(REGION_MEM.search(t)) and r['d'] >= 20)


IMG_RL = re.compile(r'Definition IMG_REGIONS : smem := \[(.*?)\]\.', re.S)
# the most regions any line of the donor puts before the image region list (`firstn 4 (ss_mem S) ++ IMG_REGIONS`)
REGION_PREFIX_MAX = 4


def region_lists(c):
    """(donor IMG_REGIONS, unit IMG_REGIONS or None, {model lib: its IMG_REGIONS}), memoised"""
    if not hasattr(c, 'region_memo'):
        show = lambda lib: subprocess.run(['git', '-C', c.a.hub, 'show', '%s:%s/A/AD2j.v' % (c.a.ref, lib)],
                                          capture_output=True, text=True).stdout
        rl = lambda t: [x.strip() for x in IMG_RL.search(t).group(1).split(';')] if t and IMG_RL.search(t) else None
        ml = {lib: rl(show(lib)) for lib in c.a.model_libs.split(',')}
        c.region_memo = (rl(show(c.a.src_lib)), rl(c.unit_file('A/AD2j.v')), {k: v for k, v in ml.items() if v})
        c.region_line_memo = {}
    return c.region_memo


def region_pos_map(gl, fl, p):
    """the unit list position of donor list position p (p regions before it): None when p is at or inside a block
    where the two lists differ (a firstn / skipn there has no single twin)"""
    shift = 0
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, gl, fl, autojunk=False).get_opcodes():
        if tag == 'equal':
            continue
        if i1 <= p <= i2:
            return None
        if p > i2:
            shift += (j2 - j1) - (i2 - i1)
    return p + shift


def region_count(r, c):
    """counts and positions in the image region lists (IMG_REGIONS of the unit's own A/AD2j.v). A count on a file that
    names no IMG_* list, whose whole line occurs in another unit whose IMG_REGIONS differs from the donor's before
    every position the count can denote, does not follow the list (it would have changed there). Else, on a file that
    names an IMG_* list, the count n is c + p with p a position in (or past) the list and c <= 4 regions before it
    (c = 0 when the list operand is an IMG_* list itself): the right value is c + the unit position of p, when every
    such c gives the same value"""
    if r['p'] is None or not region_role(r):
        return None
    gl, fl, ml = region_lists(c)
    names_img = bool(REGION_IMG.search('\n'.join(c.donor(r['file']))))
    line = r['text'].strip()
    other = []
    tw = {lib: (ln, x, v) for lib, ln, x, v in (twin_lines(r, c) if not names_img else [])}
    for lib, l in ([] if names_img else ml.items()):
        there = [region_pos_map(gl, l, r['d'] - k) for k in range(REGION_PREFIX_MAX + 1)]
        if not all(r['d'] - k >= 0 and q is not None and q != r['d'] - k for k, q in enumerate(there)):
            continue
        if (lib, line) not in c.region_line_memo:
            q = subprocess.run(['git', '-C', c.a.hub, 'grep', '-c', '-F', '-e', line, c.a.ref, '--', lib],
                               capture_output=True, text=True).stdout
            c.region_line_memo[(lib, line)] = sum(int(x.rsplit(':', 1)[1]) for x in q.split('\n') if x)
        how = ('the whole line occurs byte for byte there' if c.region_line_memo[(lib, line)] else
               'its %s:%d `%s` holds the same number at this place' % (r['file'], tw[lib][0], tw[lib][1][:90])
               if lib in tw and tw[lib][2] == r['d'] else None)
        if how:
            other.append('%s (%d regions; a count c + p of its list, c <= %d, would be %s there; %s)' % (
                lib, len(l), REGION_PREFIX_MAX, '/'.join(sorted({str(k + q) for k, q in enumerate(there)})), how))
    if other:
        return (RIGHT if r['p'] == r['d'] else WRONG + ': right value %s' % r['donor'],
                'a count that does not follow the image region list: the file names no IMG_* list, and the same line '
                'holds the same number in %s, whose IMG_REGIONS differs from the donor\'s %d regions before every '
                'position the number can denote; the line: `%s`; %s' % (', '.join(other), len(gl), use(r, 40),
                                                                        al_note(r, c)))
    if fl is None:
        return ('UNDECIDED: needs the unit\'s A/AD2j.v (start-up layer, not in the unit lib yet)',
                'a count / position in a list that holds the image region list IMG_REGIONS, which the unit\'s own '
                'A/AD2j.v (generated for fuzz_transport.asan) states; donor %s, port_core %s; the line: `%s`; %s' % (
                    r['donor'], r['port_core'], use(r, 40), al_note(r, c)))
    if gl == fl:
        return (RIGHT if r['p'] == r['d'] else WRONG + ': right value %s' % r['donor'],
                'IMG_REGIONS: the same %d regions in the donor A/AD2j.v at %s and the unit\'s A/AD2j.v, so the counts '
                'and positions of the lists that hold it are the donor\'s; the line: `%s`; %s' % (
                    len(gl), c.a.ref[:12], use(r, 40), al_note(r, c)))
    if not REGION_IMG.search('\n'.join(c.donor(r['file']))):
        return ('UNDECIDED: a list count on a file that names no IMG_* list, and no other unit with another region '
                'count holds the line', 'the line: `%s`; %s' % (use(r, 40), al_note(r, c)))
    tok = re.escape(r['donor'])
    direct = re.search(r'\b(firstn|skipn|dropAt)\s+' + tok + r'\s+IMG_\w+\b|\b(replAt|insAt)\s+' + tok +
                       r'\s+\w+\s+IMG_\w+\b|\blength IMG_\w+ = ' + tok + r'\b', r['text'])
    cs = [0] if direct else list(range(REGION_PREFIX_MAX + 1))
    vals = set()
    for k in cs:
        p = r['d'] - k
        q = r['d'] if p < 0 else region_pos_map(gl, fl, p)
        vals.add(None if q is None else (r['d'] if p < 0 else k + q))
    ops = [(t, i1, i2, j1, j2) for t, i1, i2, j1, j2 in difflib.SequenceMatcher(None, gl, fl, autojunk=False).get_opcodes()
           if t != 'equal']
    diff = '; '.join('%s donor [%d, %d) %s -> unit [%d, %d) %s' % (t, i1, i2, ' '.join(gl[i1:i2]) or '-', j1, j2,
                                                                    ' '.join(fl[j1:j2]) or '-') for t, i1, i2, j1, j2 in ops)
    if None in vals or len(vals) != 1:
        return ('UNDECIDED: the count %s is at a changed block of IMG_REGIONS for some offset c in %s' % (
            r['donor'], cs), 'IMG_REGIONS %d -> %d regions (%s); the line: `%s`; %s' % (
            len(gl), len(fl), diff, use(r, 40), al_note(r, c)))
    right = vals.pop()
    return (RIGHT if r['p'] == right else WRONG + ': right value %d' % right,
            'IMG_REGIONS: %d regions in the donor A/AD2j.v at %s, %d in the unit\'s A/AD2j.v (%s); the count %s is c + p '
            'with c regions before the list (%s) and p a position in or past it, so its value in the unit is %d; the '
            'line: `%s`; %s' % (len(gl), c.a.ref[:12], len(fl), diff, r['donor'],
                                'c = 0: its list is an IMG_* list' if direct else 'the same for every c <= %d' %
                                REGION_PREFIX_MAX, right, use(r, 40), al_note(r, c)))


REGION_DEF = re.compile(r'Definition (R_\w+) : region :=\s*mkRegion None (\d+) (\d+)')
# the unwinder's own functions (libunwind, unw_*, its log flags). PREMISE of img_b_eq, stated in its rows: the paths
# IMG_B_eq describes (the B block of target_run, the way to the target's entry function) call none of them; the lemma's
# own `vm_compute. repeat split; reflexivity.` checks the resulting positions when the closing build compiles A/AD2f.v
UNWINDER = re.compile(r'libunwind|^unw_|^_Unwind|^log(APIs|Unwinding|DWARF)$')


def code_refs(I):
    """[(address, function, instruction address)] of every address an auipc + addi / load / store pair (at most 8 bytes
    apart, 4-byte instructions) in I's .text forms, memoised"""
    if not hasattr(I, 'refs_memo'):
        sx = lambda v, b: v - (1 << b) if v & (1 << (b - 1)) else v
        t0, tsz = I.secrange('.text')
        a, last, out = t0, {}, []
        while a < t0 + tsz:
            h = I.word(a, 2)
            if h & 3 != 3:
                a += 2
                continue
            w = I.word(a, 4)
            op, rd, rs1 = w & 0x7f, (w >> 7) & 31, (w >> 15) & 31
            if op == 0x17:
                last[rd] = (a, a + sx(w & 0xfffff000, 32))
            elif op in (0x23, 0x03, 0x13) and rs1 in last and a - last[rs1][0] <= 8:
                imm = sx(((w >> 25) << 5) | ((w >> 7) & 31), 12) if op == 0x23 else sx(w >> 20, 12)
                f = [x for x in I.holders(a) if x[3] == 'STT_FUNC']
                out.append((last[rs1][1] + imm, f[0][2] if f else '?', a))
            a += 4
        I.refs_memo = out
    return I.refs_memo


def img_b_eq(r, c):
    """(added for fuzz_transport) A/AD2f.v's IMG_B_eq: firstn a X = firstn a Y /\\ firstn b (skipn s X) = firstn b
    (skipn s Y) /\\ skipn d X = skipn d Y /\\ length X = n, for (X, Y) = (IMG_B, IMG_REGIONS) and (IMG_E, IMG_B): the
    numbers give the list positions where the two lists differ (the regions the B path, resp. the path to the
    target's entry function, writes). The donor positions follow from the donor statement; each maps to the unit's
    IMG_REGIONS (lib/A/AD2j.v) through the list difference: by an equal block, or, where the unit splits one donor
    region into several, to the piece(s) holding the twins (symbol + offset) of the cells of the donor region that
    code other than the unwinder addresses (auipc pairs in fuzz_grant.asan's .text)"""
    if r['ln'] is None or r['p'] is None:
        return None
    L = c.donor(r['file'])
    i0 = next((i for i in range(r['ln'] - 1, max(-1, r['ln'] - 4), -1) if L[i].startswith('Lemma IMG_B_eq ')), None)
    if i0 is None:
        return None
    lines, i = [], i0
    while i < len(L) and not L[i].startswith('Proof'):
        lines.append(i)
        i += 1
    if r['ln'] - 1 not in lines:
        return None
    CJ = [(re.compile(r'firstn (\d+) (\w+) = firstn \1 (\w+)$'), ['prefix', 'prefix'], (2, 3)),
          (re.compile(r'firstn (\d+) \(skipn (\d+) (\w+)\) = firstn \1 \(skipn \2 (\w+)\)$'),
           ['gaplen', 'gapstart', 'gaplen', 'gapstart'], (3, 4)),
          (re.compile(r'skipn (\d+) (\w+) = skipn \1 (\w+)$'), ['suffix', 'suffix'], (2, 3)),
          (re.compile(r'length (\w+) = (\d+)%nat$'), ['len'], (1, 1))]
    roles, facts, lens = {}, collections.defaultdict(dict), {}
    for li in lines:
        k = 0
        for cj in re.sub(r'^Lemma IMG_B_eq :', '', L[li]).split('/\\'):
            cj = cj.strip().rstrip('.').strip()
            if not cj:
                continue
            hit = next(((m, rl, pr) for rx, rl, pr in CJ for m in [rx.match(cj)] if m), None)
            if not hit:
                return None
            m, rl, pr = hit
            pair = (m.group(pr[0]), m.group(pr[1]))
            for role in rl:
                roles[(li, k)] = (role, pair)
                k += 1
            if rl == ['len']:
                lens[m.group(1)] = int(m.group(2))
            elif rl[0] == 'gaplen':
                facts[pair].update(gaplen=int(m.group(1)), gapstart=int(m.group(2)))
            else:
                facts[pair][rl[0]] = int(m.group(1))
        if k != len(TOK.findall(L[li])):
            return None
    if (r['ln'] - 1, int(r['tok'])) not in roles:
        return None
    role, pair = roles[(r['ln'] - 1, int(r['tok']))]
    gl, fl, _ = region_lists(c)
    if fl is None:
        return None
    show = subprocess.run(['git', '-C', c.a.hub, 'show', '%s:%s/A/AD2j.v' % (c.a.ref, c.a.src_lib)],
                          capture_output=True, text=True).stdout
    gdef = {n: (int(lo), int(hi)) for n, lo, hi in REGION_DEF.findall(show)}
    fdef = {n: (int(lo), int(hi)) for n, lo, hi in REGION_DEF.findall(c.unit_file('A/AD2j.v') or '')}
    ops = difflib.SequenceMatcher(None, gl, fl, autojunk=False).get_opcodes()
    notes = []

    def unit_pos(i):
        for tag, i1, i2, j1, j2 in ops:
            if not i1 <= i < i2:
                continue
            if tag == 'equal':
                return [j1 + i - i1]
            if tag == 'replace' and i2 - i1 == 1 and gl[i] in gdef and all(x in fdef for x in fl[j1:j2]):
                lo, hi = gdef[gl[i]]
                refs = collections.defaultdict(list)
                for a, f, ia in code_refs(c.G):
                    if lo <= a < hi and not UNWINDER.search(f):
                        refs[a].append('%s (%s)' % (f, hx(ia)))
                pos, seen = set(), []
                for a in sorted(refs):
                    tw = [v for v, how in c.twins(a) if '+0x' in how and 'section-relative' not in how]
                    if len(set(tw)) != 1:
                        return None
                    ps = [j for j in range(j1, j2) if fdef[fl[j]][0] <= tw[0] < fdef[fl[j]][1]]
                    if len(ps) != 1:
                        return None
                    pos.add(ps[0])
                    seen.append('%s = %s (formed by an auipc pair in %s) -> %s in %s [%s, %s) at %d' % (
                        hx(a), c.G.loc(a).split(',')[0], ', '.join(refs[a]), hx(tw[0]), fl[ps[0]],
                        hx(fdef[fl[ps[0]]][0]), hx(fdef[fl[ps[0]]][1]), ps[0]))
                if not pos:
                    return None
                notes.append('donor %s [%s, %s) at %d is split into %s [%d, %d); the cells of it that code other than '
                             'the unwinder addresses: %s' % (gl[i], hx(lo), hx(hi), i, ' '.join(fl[j1:j2]), j1, j2,
                                                             '; '.join(seen)))
                return sorted(pos)
            return None
        return None

    def modified(p):
        f, n = facts[p], lens.get(p[0])
        if n is None or 'prefix' not in f or 'suffix' not in f:
            return None
        eq = set(range(f['prefix'])) | set(range(f['suffix'], n))
        if 'gapstart' in f:
            eq |= set(range(f['gapstart'], f['gapstart'] + f['gaplen']))
        return sorted(set(range(n)) - eq)
    dm = modified(pair) if role != 'len' else []
    if dm is None:
        return None
    um = []
    for i in dm:
        q = unit_pos(i)
        if q is None:
            return ('UNDECIDED: IMG_B_eq: donor list position %d (%s) has no single twin in the unit\'s IMG_REGIONS' % (
                i, gl[i]), 'the line: `%s`; %s' % (use(r, 40), al_note(r, c)))
        um += q
    um = sorted(set(um))
    if role == 'len':
        right = len(fl)
    elif len(um) != len(dm):
        return ('UNDECIDED: IMG_B_eq: donor positions %s map to %d unit positions %s, another statement shape' % (
            dm, len(um), um), '; '.join(notes))
    else:
        right = {'prefix': um[0], 'suffix': um[-1] + 1, 'gapstart': um[0] + 1,
                 'gaplen': um[-1] - um[0] - 1 if len(um) == 2 else None}[role]
        if right is None:
            return None
    readers = subprocess.run(['git', '-C', c.a.hub, 'grep', '-c', '-w', 'IMG_B_eq', c.a.ref, '--', c.a.src_lib],
                             capture_output=True, text=True).stdout
    return (RIGHT if r['p'] == right else WRONG + ': right value %d' % right,
            'IMG_B_eq (%s vs %s): the donor statement leaves positions %s of its %d-region lists unequal; in the unit\'s '
            'IMG_REGIONS (%d regions) they are %s%s; so the number with role %s is %d (donor %s); premise: those paths '
            'call no unwinder function (libunwind, unw_*); the lemma\'s proof is vm_compute, which checks the positions in '
            'the closing build, and %s line(s) besides its own read it, at %s; %s' % (
                pair[0], pair[1], dm, len(gl), len(fl), um, ' (' + '; '.join(notes) + ')' if notes else '', role, right,
                r['donor'], max(0, sum(int(x.rsplit(':', 1)[1]) for x in readers.split('\n') if x) - 1),
                c.a.ref[:12], al_note(r, c)))


def seg_table(r, c):
    """a list of (start, length) pairs equal to fuzz_grant.asan's page-rounded PT_LOAD segments"""
    pr = lambda I: [(v // 0x1000 * 0x1000, -(-(v + m) // 0x1000) * 0x1000 - v // 0x1000 * 0x1000)
                    for v, m, o, f, fl in I.loads]
    gp, dp = pr(c.G), pr(c.D)
    ms = list(re.finditer(r'\((0x[0-9a-fA-F]+|\d+),\s*(0x[0-9a-fA-F]+|\d+)\)', r['text']))
    if [(val(m.group(1)), val(m.group(2))) for m in ms] != gp:
        return None
    hit = [(k, j) for k, m in enumerate(ms) for j in (1, 2) if m.start(j) == r['col']]
    if not hit:
        return None
    k, j = hit[0]
    i = 2 * k + j - 1
    right = dp[k][j - 1]
    return (RIGHT if r['p'] == right else WRONG + ': right value %d' % right,
            'the list of the page-rounded PT_LOAD segments (start, length): fuzz_grant.asan %s, fuzz_transport.asan %s; the '
            'numeral is segment %d\'s %s; %s' % (gp, dp, i // 2, 'start' if i % 2 == 0 else 'length', al_note(r, c)))


FETCH = re.compile(r'fetch_word\s+\S+\s+\((?:Z_to_bv 64 \((\w+) \+ (0x[0-9a-fA-F]+|\d+)\)|Z_to_bv 64 (0x[0-9a-fA-F]+|\d+)|'
                   r'(0x[0-9a-fA-F]+)(?:%bv)?\s*:\s*word)\)\s*=\s*Some\s+\(?(?:(0x[0-9a-fA-F]+)%bv|(\w+))|'
                   r'\b\w+_tbl_ok\s+(0x[0-9a-fA-F]+)\s+(0x[0-9a-fA-F]+)\b')


def fetch_facts(c, f):
    """[(stage-out line, address, word, how the address was read)] of every fetch fact of stage-out file f
    (`fetch_word SEGS A = Some W`, A literal or `NAME + OFF` with NAME defined in the file or in A/AB1w.v; W literal
    or a `Definition W_x : bv 32 := V` of the file; `<table>_tbl_ok A W`), memoised"""
    if f in c.fetch_memo:
        return c.fetch_memo[f]
    L = c.relocated(f)
    defs = {n: val(v) for n, v in re.findall(r'Definition (\w+) : (?:Z|bv 32|word) := (0x[0-9a-fA-F]+|\d+)(?:%bv)?\.',
                                              '\n'.join(L))}
    out = []
    for i, l in enumerate(L):
        for m in FETCH.finditer(l):
            if m.group(7):
                A, W, how = val(m.group(7)), val(m.group(8)), 'a table lemma'
            else:
                if m.group(1):
                    base = defs.get(m.group(1), c.ab1w().get(m.group(1)))
                    if base is None:
                        continue
                    A, how = base + val(m.group(2)), '%s + %s, %s = %s' % (m.group(1), m.group(2), m.group(1), hx(base))
                else:
                    A, how = val(m.group(3) or m.group(4)), 'literal'
                W = val(m.group(5)) if m.group(5) else defs.get(m.group(6))
                if W is None:
                    continue
            out.append((i + 1, A, W, how))
    c.fetch_memo[f] = out
    return out


def insn(r, c):
    """an instruction word, its decoded operands, or the address it is fetched from: a fetch fact `fetch_word SEGS A =
    Some W` must hold in fuzz_transport.asan's bytes (A and W as stage-out writes them); a `decode_any W = ...` fact is a
    property of the 32-bit word alone; another mention of a word the file fetches is that word"""
    t = r['text']
    if r['out_line'] == '-' or r['p'] is None:
        return None
    m = re.search(r'decode_any\s+(\(?(0x[0-9a-fA-F]+)%bv\s*:\s*bv 32\)?|\w+)\s*=\s*Some', t)
    if m:
        if r['p'] != r['d']:
            return (WRONG + ': right value %s (a decode fact of an unchanged word)' % r['donor'], 'the line: `%s`' % t[:120])
        return (RIGHT + ': kept. A decode fact (`decode_any W = Some (...)`): the instruction a 32-bit word encodes, a '
                'property of the word, not of the image (its fetch fact is checked on its own line)',
                'the line: `%s`; %s' % (use(r, 50), al_note(r, c)))
    ff = fetch_facts(c, r['file'])
    ln = int(r['out_line'])
    here = [x for x in ff if x[0] == ln and r['p'] in (x[1], x[2])]
    wdef = re.match(r'\s*Definition (\w+) : bv 32 := (0x[0-9a-fA-F]+)\.', t)
    if not here and wdef:
        here = [x for x in ff if x[2] == r['p']]
    if not here:
        if r['p'] == r['d'] and 0 <= r['p'] < 2 ** 32 and FETCH.search(t) is None:
            same = [x for x in ff if x[2] == r['p'] and c.D.word(x[1]) == x[2]]
            if same and re.search(r'bv 32|Z_to_bv 32|_tbl', t):
                x = same[0]
                return (RIGHT + ': kept. The 32-bit instruction word %s, which the file\'s fetch fact (stage-out line %d) '
                        'reads at %s, where fuzz_transport.asan holds it' % (hx(x[2]), x[0], hx(x[1])),
                        'the line: `%s`; %s' % (use(r, 50), al_note(r, c)))
        return None
    x = here[0]
    held = c.D.word(x[1])
    return (RIGHT if held == x[2] else WRONG + ': fuzz_transport.asan holds %s at %s' % (hx(held or 0), hx(x[1])),
            'the fetch fact as stage-out line %d writes it: the word at %s (%s) is %s; fuzz_transport.asan\'s 4 bytes there: '
            '%s (%s, %s); %s' % (x[0], hx(x[1]), x[3], hx(x[2]), hx(held or 0), decode_insn(held) or 'word',
                                 c.D.loc(x[1]), al_note(r, c)))


def kept(r, c):
    """a value both tools kept: no image position (below the image), or a position that is the same in both images"""
    if r['p'] != r['d']:
        return None
    if r['d'] < 0x10000:
        return (RIGHT + ': kept. Not an image address: below 0x10000, the lowest PT_LOAD of both images (an offset, '
                'count, size or immediate on this line)', 'the line: `%s`; %s' % (use(r, 50), al_note(r, c)))
    same = [h for v, h in c.twins(r['d']) if v == r['d']]
    e = c.explain(r['d'], r['d']) if not same else None
    if same or e:
        return (RIGHT + ': kept. The same value in both images', 'as an image value it is %s in both images; the line: '
                '`%s`; %s' % ('; '.join(same[:2]) or e, use(r), al_note(r, c)))
    if r['d'] >= c.g_top and not (SHADOW_OFF + 0x10000 // 8 <= r['d'] < SHADOW_OFF + c.g_top // 8):
        return (RIGHT + ': kept. Not an image value: above both images (fuzz_grant.asan ends at %s, fuzz_transport.asan '
                'at %s) and outside the shadow of the image, [%s, %s)' % (
                    hx(c.g_top), hx(c.d_top), hx(SHADOW_OFF + 0x10000 // 8), hx(SHADOW_OFF + c.g_top // 8)),
                'the line: `%s`; %s' % (use(r), al_note(r, c)))
    return None


def model_line(r, c):
    """a kept value inside the image hull whose whole line occurs, byte for byte, in the libs of other units (other
    images) at REF: the number is part of the shared model text, not a position of fuzz_grant.asan. Added for
    fuzz_transport (the first run of its planted control MISSED a plant here): when the number, read as an address of
    fuzz_grant.asan, has file bytes (a section other than .bss / .tbss), each other unit whose lib holds the line must
    hold OTHER bytes at that address in its own pinned image (--model-elfs); a unit whose image holds the same 8 bytes
    there explains the identical line by an address both images share (A/AE2k.v FF_mask 0x103a0: cgif's image holds the
    same constant there), so the line is no evidence of a model constant and the group does not decide"""
    if r['p'] is None or r['class'] == 'added':
        return None
    line = r['text'].strip()
    if len(line) < 12:
        return None
    if line not in c.line_hits:
        hits = {}
        for lib in c.a.model_libs.split(','):
            q = subprocess.run(['git', '-C', c.a.hub, 'grep', '-c', '-F', '-e', line, c.a.ref, '--', lib],
                               capture_output=True, text=True).stdout
            hits[lib] = sum(int(l.rsplit(':', 1)[1]) for l in q.split('\n') if l)
        c.line_hits[line] = hits
    h = c.line_hits[line]
    if not any(h.values()):
        return None
    content = ''
    s = c.G.sec(r['d'])
    gb = c.G.rd(r['d'], 8) if s and s[0] not in ('.bss', '.tbss') else None
    if gb is not None and any(va <= r['d'] < va + fsz for va, msz, off, fsz, fl in c.G.loads):
        seen = []
        for lib in (k for k, v in h.items() if v):
            M = c.model_img.get(lib)
            mb = M.rd(r['d'], 8) if M else None
            if M is None or mb == gb:
                return None
            seen.append('%s: %s' % (lib.split('/')[2], mb.hex() if mb is not None else 'no file bytes'))
        content = '; the 8 file bytes at %s: fuzz_grant.asan %s, %s (other bytes in each image whose unit holds the line)' % (
            r['donor'], gb.hex(), ', '.join(seen))
    if r['p'] != r['d']:   # added for fuzz_transport (the plant sweep): port_core changed shared model text
        return (WRONG + ': right value %s (a model constant, unchanged)' % r['donor'],
                'the donor line `%s` occurs byte for byte in %s at %s%s; no address role gives port_core\'s %s; %s' % (
                    line[:90], ', '.join('%s (%d)' % (k, v) for k, v in h.items() if v), c.a.ref[:12], content,
                    r['port_core'], al_note(r, c)))
    return (RIGHT + ': kept (a model constant). The whole line, this number included, is shared model text: it occurs '
            'byte for byte in the libs of units built for other images',
            'the line `%s` occurs in %s at %s; read as an address of fuzz_grant.asan %s would be %s (fuzz_transport.asan twin '
            '%s)%s; %s' % (line[:90], ', '.join('%s (%d)' % (k, v) for k, v in h.items() if v), c.a.ref[:12], r['donor'],
                           c.G.loc(r['d']), ', '.join(hx(v) for v, _ in c.twins(r['d'])[:2]) or '-', content,
                           al_note(r, c)))


def model_skeleton(r, c):
    """a kept value whose line, with every numeral as a placeholder, occurs in the libs of other units (other images)
    with the SAME number at this place while other numerals of the line differ (their image addresses): the number does
    not follow the image"""
    if r['p'] is None or r['class'] == 'added':
        return None
    line = r['text'].strip()
    sk = TOK.sub('#', line)
    frags = sorted((x.strip() for x in TOK.split(line)[::2]), key=len, reverse=True)
    if not frags or len(frags[0]) < 8:
        return None
    key = (sk, frags[0])
    if key not in c.line_hits:
        seen = []
        for lib in c.a.model_libs.split(','):
            q = subprocess.run(['git', '-C', c.a.hub, 'grep', '-h', '-F', '-e', frags[0], c.a.ref, '--', lib],
                               capture_output=True, text=True).stdout
            seen += [(lib, x.strip()) for x in q.split('\n') if TOK.sub('#', x.strip()) == sk]
        c.line_hits[key] = seen
    same = [(lib, x) for lib, x in c.line_hits[key]]
    k = int(r['tok'])
    vals = {val(TOK.findall(x)[k]) for lib, x in same}
    other = [(lib, x) for lib, x in same if x != line]
    if vals != {r['d']} or not other:
        return None
    if r['p'] != r['d']:   # added for fuzz_transport (the plant sweep): port_core changed a model constant
        return (WRONG + ': right value %s (a model constant, unchanged)' % r['donor'],
                'e.g. %s: `%s` holds the same number here while its image addresses differ (donor line: `%s`); no '
                'address role gives port_core\'s %s; %s' % (other[0][0], other[0][1][:100], line[:100], r['port_core'],
                                                           al_note(r, c)))
    return (RIGHT + ': kept (a model constant). The same line of other units (other images) holds the same number here '
            'while its image addresses differ',
            'e.g. %s: `%s` (this line: `%s`); read as an address of fuzz_grant.asan %s would be %s; %s' % (
                other[0][0], other[0][1][:100], line[:100], r['donor'], c.G.loc(r['d']), al_note(r, c)))


def seg0_size(r, c):
    if r['d'] != 131072 or 'seg_size' not in r['text']:
        return None
    gsz = -(-(c.G.loads[0][0] + c.G.loads[0][1]) // 0x1000) * 0x1000 - c.G.loads[0][0]
    dsz = -(-(c.D.loads[0][0] + c.D.loads[0][1]) // 0x1000) * 0x1000 - c.D.loads[0][0]
    ok = r['p'] == dsz and r['d'] == gsz
    return (RIGHT if ok else WRONG + ': right value %d' % dsz,
            'the first segment\'s size: PT_LOAD 0 [0x10000, +%s) page-rounds to %s = %d in fuzz_grant.asan, '
            '[0x10000, +%s) to %s = %d in fuzz_transport.asan; %s' % (
                hx(c.G.loads[0][1]), hx(gsz), gsz, hx(c.D.loads[0][1]), hx(dsz), dsz, al_note(r, c)))


def ra3_len(r, c):
    if r['d'] != 832 or not re.search(r'658912|R_A3|img_cells_view|img_at_of_cimg', r['text']):
        return None
    gs, ds = c.G.uniq('__stderr_FILE'), c.D.uniq('__stderr_FILE')
    ga, da = c.G.uniq('__start_asan_globals'), c.D.uniq('__start_asan_globals')
    glo, dlo = gs[0] - 0x48, ds[0] - 0x48
    gl = (ga[0] if ga else c.G.secrange('asan_globals')[0]) - glo
    dl = (da[0] if da else c.D.secrange('asan_globals')[0]) - dlo
    ft = c.unit_file('A/AD2j.v')
    m = re.search(r'Definition R_A3 : region :=\s*mkRegion None (\d+) (\d+)', ft) if ft else None
    unit = ('the unit\'s A/AD2j.v states R_A3 = mkRegion None %s %s (%d bytes%s)' % (
        m.group(1), m.group(2), int(m.group(2)) - int(m.group(1)),
        '' if int(m.group(2)) - int(m.group(1)) == dl and int(m.group(1)) == dlo else ': DIFFERS from the image')
        if m else 'the unit\'s A/AD2j.v is not in the unit lib yet (start-up layer)')
    ok = gl == r['d'] and dl == r['p']
    return (RIGHT if ok else WRONG + ': right value %d' % dl,
            'R_A3\'s length: [__stderr_FILE - 0x48, asan_globals start) = [%s, %s) = %d bytes in fuzz_grant.asan, '
            '[%s, %s) = %d in fuzz_transport.asan; %s; %s' % (hx(glo), hx(glo + gl), gl, hx(dlo), hx(dlo + dl), dl, unit,
                                                          al_note(r, c)))


def shadow_window(r, c):
    """SH_LO / SH_HI: the 8-aligned shadow window of the format string FMT (A/AE2t..AE2w, A/AE35)"""
    m = re.match(r'Definition SH_LO : Z := (0x[0-9a-f]+)\.\s+Definition SH_HI : Z := (0x[0-9a-f]+)\.', r['text'])
    if not m:
        return None
    gfmt = [l for l in c.donor(r['file']) if re.match(r'Definition FMT : Z := 0x[0-9a-f]+\.', l)]
    dfmt = [l for l in c.relocated(r['file']) if re.match(r'Definition FMT : Z := 0x[0-9a-f]+\.', l)]
    gf, df = val(TOK.findall(gfmt[0])[0]), val(TOK.findall(dfmt[0])[0])
    gs, ds = c.G.strz(gf), c.D.strz(df)
    lo = lambda a: (SHADOW_OFF + a // 8) // 8 * 8
    hi = lambda a, n: (SHADOW_OFF + (a + n) // 8) // 8 * 8 + 8
    which = 'SH_LO' if r['tok'] == '0' else 'SH_HI'
    gv = lo(gf) if which == 'SH_LO' else hi(gf, len(gs) + 1)
    dv = lo(df) if which == 'SH_LO' else hi(df, len(ds) + 1)
    if gv != r['d'] or gs != ds:
        return None
    return (RIGHT if dv == r['p'] else WRONG + ': right value %s' % hx(dv),
            '%s = %s: FMT is %r at %s in fuzz_grant.asan (gives the donor\'s %s) and at %s in fuzz_transport.asan (FMT\'s '
            'relocated value, the same bytes) -> %s; %s' % (
                which, 'floor8(shadow(FMT))' if which == 'SH_LO' else 'floor8(shadow(FMT + strlen + 1)) + 8',
                gs.decode('latin1')[:60], hx(gf), hx(gv), hx(df), hx(dv), al_note(r, c)))


CZONE_HI = re.compile(r'0x7fff8000\s*(<=\?|<=)\s*\w+\s*\)?\s*(&&\s*\(.*)?(<|<=\?)\s*$')


def czone(r, c):
    """the upper bound HI of the CZONE shadow window `0x7fff8000 <= a < HI` (and its abs_cell_ok copy `... <=? HI`):
    the zone the constant cells may lie in, so HI must reach the end of the image's highest constant shadow byte; and
    (added for fuzz_transport's run of record) HI must stay at or below kLowShadowBeg + IMG_TOP / 8, the least shadow
    start of the secondary map that map_facts SM1 (A/AFjm.v) allows: a higher HI leaves addresses of the window where the
    map's shadow can start, and A/AFju.v CZ_untouched fails (kLowShadowBeg from stage-out Reusable/YG0f.v)"""
    if r['p'] is None or r['ln'] is None or not CZONE_HI.search(r['pre']) or r['d'] <= SHADOW_OFF:
        return None
    # the line belongs to the CZONE window: a CZONE* / abs_cell_ok* name within the 4 lines above it, or (added for
    # fuzz_transport, whose donor A/AFju.v names it `CZ` and `abs_cell_okS`, 2 and 8 lines up) the nearest Definition
    # at most 15 lines up is a CZ* / abs_cell_ok* definition
    above = c.donor(r['file'])[max(0, r['ln'] - 15):r['ln']]
    defs = [l for l in above if l.startswith('Definition ')]
    if not (re.search(r'\bCZONE\w*|\babs_cell_ok\w*', '\n'.join(above[-4:])) or
            (defs and re.match(r'Definition (CZ\w*|abs_cell_ok\w*)\b', defs[-1]))):
        return None
    def need(I):
        lo, sz = I.secrange('asan_globals')
        ge = max(I.word(a, 8) + I.word(a + 16, 8) for a in range(lo, lo + sz, 64))
        return lo + sz, ge, SHADOW_OFF + -(-(lo + sz) // 8), SHADOW_OFF + -(-ge // 8)
    gq, dq = need(c.G), need(c.D)
    ft = c.unit_file('A/AF0m.v') or ''
    m = re.search(r'Definition Tfib_const_shadow : list acell :=(.*?)\]\.', ft, re.S)
    cells = [val(x) for x in re.findall(r'\(ANum (0x[0-9a-fA-F]+)\)', m.group(1))] if m else []
    own = max(cells) + 1 if cells else None
    need_d = max(dq[2], dq[3], own or 0)
    kl = [val(x) for x in re.findall(r'^Definition kLowShadowBeg : Z := (0x[0-9a-fA-F]+)\.$',
                                     '\n'.join(c.relocated('Reusable/YG0f.v')), re.M)]
    sm1 = 'kLowShadowBeg + TFIB_IMG_END / 8 <= SMv' in '\n'.join(c.relocated('A/AFjm.v'))
    cap = kl[0] + c.D.top // 8 if len(kl) == 1 and sm1 else None
    ok = r['p'] >= need_d and (cap is None or r['p'] <= cap)
    others = ', '.join('%s %s' % (lib.split('/')[2], hx(v)) for lib, _, _, v in twin_lines(r, c))
    return ((RIGHT + ': kept (a bound above every constant shadow byte)' if r['p'] == r['d'] else RIGHT) if ok else
            WRONG + ': the bound must be >= %s%s' % (hx(need_d), ' and <= %s' % hx(cap) if cap is not None else ''),
            'the CZONE shadow window [0x7fff8000, HI) must hold every constant shadow byte of the image: '
            'fuzz_transport.asan\'s asan_globals [%s, %s) (shadow end %s), its highest global redzone end %s (shadow end '
            '%s)%s; fuzz_grant.asan\'s: asan_globals end %s (shadow end %s), redzone end %s (shadow end %s); HI = %s '
            '(the shadow of [0, %s)) is >= %s%s; the same line of the other units holds: %s; the line: `%s`; %s' % (
                hx(c.D.secrange('asan_globals')[0]), hx(dq[0]), hx(dq[2]), hx(dq[1]), hx(dq[3]),
                '; the unit\'s A/AF0m.v Tfib_const_shadow ends at %s' % hx(own) if own else
                '; the unit\'s A/AF0m.v is not in the unit lib', hx(gq[0]), hx(gq[2]), hx(gq[1]), hx(gq[3]),
                r['port_core'], hx((r['p'] - SHADOW_OFF) * 8), hx(need_d),
                ' and <= %s = kLowShadowBeg %s + IMG_TOP %s / 8 (map_facts SM1)' % (hx(cap), hx(kl[0]), hx(c.D.top))
                if cap is not None else '', others or '-', use(r, 50), al_note(r, c)))


def twin_lines(r, c):
    """[(model lib, line number, line, its numeral at the row's token index)]: in the SAME file of each model lib at
    REF, the line nearest the donor line whose skeleton (every numeral as a placeholder) equals the donor line's"""
    line = r['text'].strip()
    sk = TOK.sub('#', line)
    k = int(r['tok'])
    seen = []
    for lib in c.a.model_libs.split(','):
        key = (lib, r['file'])
        if key not in c.line_hits:
            q = subprocess.run(['git', '-C', c.a.hub, 'show', '%s:%s/%s' % (c.a.ref, lib, r['file'])],
                               capture_output=True, text=True)
            c.line_hits[key] = [x.strip() for x in q.stdout.split('\n')] if q.returncode == 0 else []
        cands = [(abs(i + 1 - r['ln']), i + 1, x) for i, x in enumerate(c.line_hits[key]) if TOK.sub('#', x) == sk]
        if cands:
            _, ln, x = min(cands)
            seen.append((lib, ln, x, val(TOK.findall(x)[k])))
    return seen


def model_twin(r, c):
    """a kept number whose line, in the SAME file of the units built for other images (the model libs at REF), holds
    the same number at the same place while another numeral of the line (an image address) differs: the number does
    not follow the image"""
    if r['p'] != r['d'] or r['class'] == 'added' or r['ln'] is None:
        return None
    line = r['text'].strip()
    seen = twin_lines(r, c)
    if not seen or any(v != r['d'] for _, _, _, v in seen) or all(x == line for _, _, x, _ in seen):
        return None
    facts = ''
    m = re.search(r'\bf?lit(\d) (0x[0-9a-fA-F]+) $', r['pre'])
    if m and r['out_line'] != '-':
        o = c.relocated(r['file'])[int(r['out_line']) - 1]
        mo = list(re.finditer(r'\bf?lit%s (0x[0-9a-fA-F]+) ' % m.group(1) + re.escape(r['port_core']) + r'\b', o))
        a_g, n = val(m.group(2)), int(m.group(1))
        a_d = val(mo[0].group(1)) if len(mo) == 1 else None
        fb = lambda I, a: 'none: .bss' if (I.sec(a) or ('',))[0] == '.bss' else hx(I.word(a, n) or 0)
        facts = '; the fact\'s cell: grant %s = %s (file bytes %s), transport %s = %s (file bytes %s)' % (
            m.group(2), c.G.loc(a_g), fb(c.G, a_g), hx(a_d) if a_d else '-', c.D.loc(a_d) if a_d else '-',
            fb(c.D, a_d) if a_d else '-')
    return (RIGHT + ': kept (a model constant). The same line of the same file in units built for other images holds '
            'the same number here while its image addresses differ',
            '%s; this line: `%s`%s; read as an address of fuzz_grant.asan %s would be %s; %s' % (
                '; '.join('%s/%s:%d: `%s`' % (lib, r['file'], ln, x[:100]) for lib, ln, x, _ in seen), line[:100], facts,
                r['donor'], c.G.loc(r['d']) if r['d'] >= 0x1000 else 'no address', al_note(r, c)))


# the jump-table words the donor's proofs read (A/AFih.v R_jt := lit4 0x20bfc 0x460f4, A/AFii.v R_scj := lit4 0x218c8
# 0x69f18): entry address -> the 4-byte word fuzz_grant.asan holds there
JUMP_WORDS = {0x20bfc: 0x460f4, 0x218c8: 0x69f18}


def label_diff(r, c):
    """a 4-byte jump-table word (a label difference: target - table base), its address, or the end of its 4 bytes,
    on a line that names the table entry"""
    toks = {val(x) for x in TOK.findall(r['text'])}
    hits = [x for x in JUMP_WORDS if x in toks or (JUMP_WORDS[x] in toks and r['d'] == JUMP_WORDS[x])]
    if len(hits) != 1:
        return None
    a_g = hits[0]
    if c.G.word(a_g) != JUMP_WORDS[a_g]:
        return None
    a_d = c.explain_table(a_g)
    wg, wd = c.G.word(a_g), c.D.word(a_d)
    tgt_g, tgt_d = a_g + wg, a_d + wd
    if r['d'] == a_g:
        right, what = a_d, 'the table entry\'s address'
    elif r['d'] == a_g + 4:
        right, what = a_d + 4, 'the end of the entry\'s 4 bytes'
    elif r['d'] == wg:
        right, what = wd, 'the 4-byte word the entry holds'
    else:
        return None
    return (RIGHT if r['p'] == right else WRONG + ': right value %s' % hx(right),
            '%s: grant %s holds %s, transport %s holds %s (its twin: the one .rodata word whose neighbours, read the same '
            'way, reach the same functions); each word is a label difference (target minus table base): entry + word = '
            '%s = %s in grant and %s = %s in transport, the same offset of the same function; read as a code address the '
            'grant word would be %s and the transport word %s, another function, so the word is no code address; %s' % (
                what, hx(a_g), hx(wg), hx(a_d), hx(wd), hx(tgt_g), c.G.loc(tgt_g), hx(tgt_d), c.D.loc(tgt_d),
                c.G.loc(wg), c.D.loc(wd), al_note(r, c)))


def section_end(r, c):
    """AB1w.v tfib_<sec>_hi := the section's end. Added for fuzz_transport: a donor value INSIDE the section but short of
    its end (fuzz_grant's tfib_rodata_hi 0x22c0c, 0x40 below .rodata's end 0x22c4c, inherited from cgif: a donor defect,
    the tool registry, 19:55Z) is still decided by the name's role, the section's end in fuzz_transport.asan"""
    m = re.search(r'Definition tfib_(\w+)_hi : Z := ' + r['donor'] + r'\.', r['text'])
    if not m:
        return None
    sec = {'data': '.data', 'tbss': '.tbss', 'tdata': '.tdata', 'bss': '.bss', 'rodata': '.rodata',
           'text': '.text', 'got': '.got'}.get(m.group(1))
    if not sec or not c.G.secrange(sec) or not c.D.secrange(sec):
        return None
    g, d = c.G.secrange(sec), c.D.secrange(sec)
    off = ''
    if g[0] + g[1] != r['d']:
        if not g[0] < r['d'] < g[0] + g[1]:
            return None
        off = ('; the donor\'s %s is NOT fuzz_grant.asan\'s %s end (%s, %d bytes higher): a donor defect, the name gives '
               'the role' % (r['donor'], sec, hx(g[0] + g[1]), g[0] + g[1] - r['d']))
    de = d[0] + d[1]
    return (RIGHT if r['p'] == de else WRONG + ': right value %s' % hx(de),
            'tfib_%s_lo / _hi are the bounds of section %s: it ends at %s in fuzz_grant.asan and %s in fuzz_transport.asan%s; '
            'port_core wrote %s (%s in fuzz_transport.asan); alreloc\'s %s is %s in fuzz_transport.asan; %s' % (
                m.group(1), sec, hx(g[0] + g[1]), hx(de), off, r['port_core'], c.D.loc(r['p']), r['alreloc'],
                c.D.loc(r['al']) if r['al'] else '-', al_note(r, c)))


def func_end(r, c):
    """AB1w.v tfib_E_<f> := the end of function f"""
    m = re.search(r'Definition tfib_E_(\w+) : Z := ' + r['donor'] + r'\.', r['text'])
    if not m:
        return None
    n = {'asan_module_dtor': 'asan.module_dtor', 'asan_module_ctor': 'asan.module_ctor'}.get(m.group(1))
    cands = [n] if n else [m.group(1), '__' + m.group(1), '_' + m.group(1)]
    for n in cands:
        g, d = c.G.uniq(n), c.D.uniq(n)
        if g and d and g[0] + g[1] == r['d']:
            de = d[0] + d[1]
            return (RIGHT if r['p'] == de else WRONG + ': right value %s' % hx(de),
                    'the end of %s: [%s, %s) in fuzz_grant.asan (at its end there: %s), [%s, %s) in fuzz_transport.asan; %s'
                    % (n, hx(g[0]), hx(r['d']), c.G.loc(r['d']), hx(d[0]), hx(de), al_note(r, c)))
    return None


def arith(r, c):
    """a quotient written next to its expression: change ((A - B) / 8) with N"""
    m = re.search(r'change \(\((\S+) - (\S+)\) / 8\) with ' + r['donor'] + r'\b', r['text'])
    if not m or r['out_line'] == '-':
        return None
    o = c.relocated(r['file'])[int(r['out_line']) - 1]
    mo = re.search(r'change \(\((\S+) - (\S+)\) / 8\) with ' + r['port_core'] + r'\b', o)
    if not mo:
        return None
    gv = (val(m.group(1)) - val(m.group(2))) // 8
    dv = (val(mo.group(1)) - val(mo.group(2))) // 8
    if gv != r['d']:
        return None
    x1, x2 = c.explain(val(m.group(1)), val(mo.group(1))), c.explain(val(m.group(2)), val(mo.group(2)))
    same = lambda g_, f_: 'the constant %s' % g_ if g_ == f_ else None
    x1 = x1 or same(m.group(1), mo.group(1))
    x2 = x2 or same(m.group(2), mo.group(2))
    if not (x1 and x2):
        return None
    return (RIGHT if dv == r['p'] else WRONG + ': right value %d' % dv,
            'the quotient of the line\'s own expression: donor ((%s - %s) / 8) = %d, relocated ((%s - %s) / 8) = %d; '
            'its operands: %s; %s; %s' % (m.group(1), m.group(2), gv, mo.group(1), mo.group(2), dv, x1, x2,
                                         al_note(r, c)))


def page_index(r, c):
    """a page number of the image top: 0x5fa000 / 4096"""
    if r['d'] != c.g_top // 4096:
        return None
    dv = c.d_top // 4096
    return (RIGHT if r['p'] == dv else WRONG + ': right value %d' % dv,
            'the page index of the image top (`KRange (EVar n) %d ...` / `4096 * %d <= ...`): %s / 4096 = %d in '
            'fuzz_grant.asan, %s / 4096 = %d in fuzz_transport.asan; %s' % (
                r['d'], r['d'], hx(c.g_top), r['d'], hx(c.d_top), dv, al_note(r, c)))


def program_rows(r, c):
    """A/AB1w.v's function table rows and A/AF0l.v's pc_stack_malloc: positions port_core rewrote with the unit's own
    functions (patched lines, and the lines they added)"""
    if r['file'] not in ('A/AB1w.v', 'A/AF0l.v'):
        return None
    if r['class'] not in ('not-covered', 'added'):
        return None
    g, d = c.G, c.D
    t = r['text'] if r['class'] == 'not-covered' else c.relocated(r['file'])[int(r['out_line']) - 1]
    if r['file'] == 'A/AF0l.v':
        if 'pc_stack_malloc' not in t and 'cid =?' not in t:
            return None
        if r['class'] == 'not-covered':
            gm = dict((int(a), val(b)) for a, b in re.findall(r'cid =\? (\d+) then (0x[0-9a-f]+)', t))
            return (RIGHT + ': the donor\'s pc_stack_malloc line, replaced by the unit\'s classes',
                    'donor pc_stack_malloc: %s (fuzz_grant.asan: %s)' % (
                        ', '.join('%d -> %s' % (k, hx(v)) for k, v in sorted(gm.items())),
                        ', '.join('%d = %s' % (k, g.loc(v)) for k, v in sorted(gm.items()))))
        dm = dict((int(a), val(b)) for a, b in re.findall(r'cid =\? (\d+) then (0x[0-9a-f]+)', t))
        bad = [k for k, v in dm.items() if not d.uniq('__asan_stack_malloc_%d' % k) or
               d.uniq('__asan_stack_malloc_%d' % k)[0] != v]
        vv = val(r['port_core'])
        mine = [k for k, v in dm.items() if v == vv] or ([vv] if str(vv) in t else [])
        return (RIGHT if not bad else WRONG + ': classes %s' % bad,
                'pc_stack_malloc in stage-out: %s; fuzz_transport.asan\'s __asan_stack_malloc_<cid> entries: %s' % (
                    ', '.join('%d -> %s' % (k, hx(v)) for k, v in sorted(dm.items())),
                    ', '.join('%s = %s' % (n, hx(d.byname[n][0][0])) for n in sorted(d.byname)
                              if re.match(r'__asan_stack_malloc_\d+$', n))))
    m = None
    for mm in re.finditer(r'Definition tfib_([AE])_(\w+) : Z := (0x[0-9a-fA-F]+|\d+)\.', t):
        if mm.start(3) <= r['col'] < mm.end(3):
            m = mm
    if not m:
        return None
    ae, n, v = m.group(1), m.group(2), val(m.group(3))
    if r['class'] == 'not-covered':
        gs = g.uniq(n)
        return (RIGHT + ': a donor row of fuzz_grant\'s own function %s, which port_core replaced by the unit\'s rows' % n,
                'tfib_%s_%s = %s: %s in fuzz_grant.asan; fuzz_transport.asan: %s' % (
                    ae, n, m.group(3), g.loc(v), ('[%s, %s)' % (hx(d.uniq(n)[0]), hx(sum(d.uniq(n)[:2]))))
                    if d.uniq(n) else 'no symbol %s' % n))
    cands = [n, '__' + n, n.replace('asan_module_', 'asan.module_')]
    s = next((d.uniq(x) for x in cands if d.uniq(x)), None)
    if not s:
        return ('UNDECIDED: added row tfib_%s_%s: no unique symbol of that name in fuzz_transport.asan' % (ae, n), '')
    right = s[0] if ae == 'A' else s[0] + s[1]
    return (RIGHT if v == right else WRONG + ': right value %s' % hx(right),
            'added row tfib_%s_%s = %s: the symbol\'s %s in fuzz_transport.asan [%s, %s)' % (
                ae, n, m.group(3), 'start' if ae == 'A' else 'end (start + size)', hx(s[0]), hx(s[0] + s[1])))


def patched_tactic(r, c):
    """a numeral of a tactic line that one of port_core's patches replaced (no image numeral)"""
    if r['class'] != 'not-covered':
        return None
    t = r['text']
    if r['donor'] == '8' and '/ 8' in t:
        return (RIGHT + ': not an address. The tactic `?x / 8` (the shadow quotient) of the case split '
                'zero-shadow-forallb.patch replaced by a forallb check; the replacement holds no donor numeral',
                'donor line: `%s`' % t.strip()[:120])
    if r['donor'] == '60' and 'nth_error_In _ 60' in t:
        return (RIGHT + ': not an address. The index 60 of the const cell in Tfib_const (nth_error_In _ 60); '
                'cell-lookup.patch replaces the lookup by index with a lookup by the cell\'s value, which does not '
                'depend on the list position', 'donor line: `%s`' % t.strip()[:150])
    # added for fuzz_transport: dead-arm-ad1g.patch removes A/AD1g.v's alternative `|| (change N with (P * 4096); apply
    # Z_mod_mult)`, which no run takes: N <> P * 4096, so `change` fails already in the donor (the first alternative
    # `apply Z_mod_mult` closes the goal)
    m = re.search(r' \|\| \(change (\d+) with \((\d+) \* 4096\); apply Z_mod_mult\)', t)
    if m and r['donor'] in (m.group(1), m.group(2), '4096'):
        n, p = int(m.group(1)), int(m.group(2))
        kept = t.replace(m.group(0), '') in c.relocated(r['file'])
        if n != p * 4096 and kept:
            return (RIGHT + ': not an image value in stage-out. The numeral is in the alternative `%s`, which '
                    'dead-arm-ad1g.patch removes; the arm can never succeed: %d * 4096 = %d <> %d, so `change` fails '
                    'already in the donor and the first alternative `apply Z_mod_mult` closes the goal' % (
                        m.group(0).strip(' |'), p, p * 4096, n),
                    'donor line %d: `%s`; stage-out holds the same line without the alternative (no numeral); %s is '
                    '%s in fuzz_grant.asan; %s' % (r['ln'], t.strip()[-120:], r['donor'],
                                                   c.G.loc(r['d']) if r['d'] >= 0x10000 else 'no address', al_note(r, c)))
    # added for fuzz_transport's run of record (the G patches, records/ghunks/GHUNKS-A-rec3.md): a donor line a patch
    # rewrote (the same sentence with the G names added, or the donor line with a conjunct appended) whose numeral, below
    # the image base, the rewritten line keeps; similarity 1.0 when the rewritten line holds the whole donor line
    if val(r['donor']) is not None and val(r['donor']) < 0x10000:
        tok = re.compile(r'(?<![\w.])%s(?![\w.])' % re.escape(r['donor']))
        best = max(((1.0 if t.strip() and t.strip() in x else difflib.SequenceMatcher(None, t.strip(), x.strip()).ratio(),
                     k, x) for k, x in enumerate(c.relocated(r['file']), 1) if tok.search(x)), default=None)
        if best and best[0] >= 0.8:
            return (RIGHT + ': not an address. The donor line was rewritten by a patch of the run (the same sentence '
                    'with names added); the rewritten line keeps %s (below the image start 0x10000)' % r['donor'],
                    'donor line %s: `%s`; stage-out line %d (similarity %.2f): `%s`' % (
                        r['ln'], t.strip()[:110], best[1], best[0], best[2].strip()[:110]))
    return None


def address(r, c):
    """port_core's value is the twin of the donor's under an address role (symbol + offset, string, section bound,
    image top, .got cell content, shadow byte or quotient of one)"""
    if r['p'] is None:
        return None
    e = c.explain(r['d'], r['p'])
    if not e:
        return None
    extra = ''
    # a memory fact on the line (lit8 A V): when fuzz_grant.asan's file bytes at A hold V (a fact about the loaded
    # image, not a run-time state), fuzz_transport.asan's bytes at port_core's A' must hold port_core's V'
    if r['out_line'] != '-':
        o = c.relocated(r['file'])[int(r['out_line']) - 1]
        gl = re.findall(r'\blit8 (0x[0-9a-f]+) (0x[0-9a-f]+)\b', r['text'])
        dl = re.findall(r'\blit8 (0x[0-9a-f]+) (0x[0-9a-f]+)\b', o)
        for k, (x, y) in enumerate(gl):
            if r['donor'] in (x, y) and k < len(dl):
                fA, fW = val(dl[k][0]), val(dl[k][1])
                static = c.G.word(val(x), 8) == val(y)
                extra = '; memory fact lit8 %s %s: fuzz_grant.asan\'s file bytes at %s hold %s (%s), fuzz_transport.asan\'s ' \
                        'at %s hold %s (stage-out writes lit8 %s %s)' % (
                            x, y, x, hx(c.G.word(val(x), 8) or 0), 'the fact is about the loaded image' if static else
                            'another value: the fact states a run-time content, not checked against the file',
                            hx(fA), hx(c.D.word(fA, 8) or 0), dl[k][0], dl[k][1])
                if static and c.D.word(fA, 8) != fW:
                    return (WRONG + ': the memory fact names a value fuzz_transport.asan does not hold at that address',
                            e + extra)
    if e.startswith('address') and (c.G.sec(r['d']) or ('',))[0] == '.text':
        wd = [c.G.word(r['d'] - 4), c.G.word(r['d'])]
        wp = [c.D.word(r['p'] - 4), c.D.word(r['p'])]
        extra += '; the instruction before it is `%s` in grant and `%s` in transport, the word at it %s / %s%s' % (
            decode_insn(wd[0]) or ('ecall' if wd[0] == 0x73 else hx(wd[0] or 0)),
            decode_insn(wp[0]) or ('ecall' if wp[0] == 0x73 else hx(wp[0] or 0)), hx(wd[1] or 0), hx(wp[1] or 0),
            ' (equal)' if wd[1] == wp[1] else '')
    locs = ' (grant %s = %s; transport %s = %s)' % (r['donor'], c.G.loc(r['d']), r['port_core'], c.D.loc(r['p'])) \
        if e.startswith('address') else ''
    return (RIGHT, '%s%s; the line uses it as `%s`%s; %s' % (e, locs, use(r), extra, al_note(r, c)))


def address_wrong(r, c):
    """port_core moved a value no address role explains: the twin by each role, else UNDECIDED"""
    if r['p'] is None or r['p'] == r['d']:
        return None
    rv = c.right_value(r['d'])
    if rv:
        return (WRONG + ': right value %s' % ' or '.join(hx(x) for x in rv),
                'grant %s = %s; its twin(s) in fuzz_transport.asan: %s; port_core wrote %s = %s; %s' % (
                    r['donor'], c.G.loc(r['d']), '; '.join('%s (%s)' % (hx(fv), h) for fv, h in c.twins(r['d'])),
                    r['port_core'], c.D.loc(r['p']), al_note(r, c)))
    return None


def kept_address(r, c):
    """port_core kept the donor's value although fuzz_grant.asan holds an object there whose twin in fuzz_transport.asan
    lies elsewhere (by symbol + offset, string, section bound or .got content), and no model / constant group explained
    the number: a donor address left in place"""
    if r['p'] is None or r['p'] != r['d'] or not 0x10000 <= r['d'] < c.g_top:
        return None
    tw = [(v, h) for v, h in c.twins(r['d']) if 'section-relative' not in h]
    if not tw or any(v == r['d'] for v, h in tw):
        return None
    return (WRONG + ': right value %s' % ' or '.join(sorted({hx(v) for v, h in tw})),
            'port_core kept %s = %s in fuzz_grant.asan; its twin(s) in fuzz_transport.asan: %s; at %s fuzz_transport.asan holds '
            '%s; no model text or constant role names the number; the line uses it as `%s`; %s' % (
                r['donor'], c.G.loc(r['d']), '; '.join('%s (%s)' % (hx(v), h) for v, h in tw[:3]), r['port_core'],
                c.D.loc(r['p']), use(r), al_note(r, c)))


def nonimage_moved(r, c):
    """(added for fuzz_transport, from the plant sweep) port_core changed a value that is no image value in either image:
    at or above both image tops and outside the shadow of both images; no earlier group (image span, page index, CZONE,
    shadow window, geometry) gave it a role, so no role moves it"""
    if r['p'] is None or r['p'] == r['d'] or r['d'] < max(c.g_top, c.d_top):
        return None
    lo, hi = SHADOW_OFF + 0x10000 // 8, SHADOW_OFF + max(c.g_top, c.d_top) // 8
    if lo <= r['d'] < hi:
        return None
    return (WRONG + ': right value %s (no image value, unchanged)' % r['donor'],
            '%s is at or above both image tops (%s, %s) and outside the image shadow [%s, %s); port_core wrote %s; the '
            'line: `%s`; %s' % (r['donor'], hx(c.g_top), hx(c.d_top), hx(lo), hx(hi), r['port_core'], use(r),
                                al_note(r, c)))


HDR_LINE = re.compile(r'^\(\* Modified by [^,]+, (\d{4})-(\d{2}): copied from proofs/libreac/fuzz_grant/lib/')


def added_line(r, c):
    """a numeral of a stage-out line with no donor partner: port_core's header line, or a line one of its patches
    added (the patches are reviewed as patches; here: is the numeral an image position?)"""
    if r['class'] != 'added':
        return None
    m = HDR_LINE.match(r['text'])
    if m and r['col'] in (m.start(1), m.start(2)):
        return (RIGHT + ': not an image value. The year / month of the header line port_core adds to each file',
                'stage-out line %s: `%s`' % (r['out_line'], r['text'][:110]))
    if r['d'] < 0x10000:
        return (RIGHT + ': not an image address. A number below 0x10000 on a line port_core\'s patches added (below the image '
                'start 0x10000, the lowest PT_LOAD vaddr of both images)', 'stage-out line %s: `%s`' % (
                    r['out_line'], r['text'][max(0, r['col'] - 60):r['col'] + 40].strip()))
    # added for fuzz_transport's run of record: a comment line a patch added that names an object of the target by its
    # symbol next to its address (g-AD2f.patch: `g_cfg [0x5df080, +60) to OW [0x5f3060, +304)`)
    if '(*' in r['text'] or r['text'].lstrip().startswith('*'):
        before = r['text'][max(0, r['col'] - 40):r['col']]
        for w in reversed(re.findall(r'[A-Za-z_][\w.]*', before)):
            s = c.D.uniq(w)
            if s and s[0] == r['d']:
                return (RIGHT + ': the comment names %s, whose symbol in fuzz_transport.asan\'s twin is at %s' % (
                    w, hx(s[0])), 'stage-out line %s: `%s`' % (r['out_line'], r['text'].strip()[:140]))
    return None


GROUPS = [
    ('notice', notice),
    ('comment', comment),
    ('program-rows', program_rows),
    ('added-line', added_line),
    ('patched-tactic', patched_tactic),
    ('got-cell', got_cell),
    ('insn', insn),
    ('insn-word', insn_word),
    ('model-label', model_label),
    ('other-image-comment', notice_other_comment),
    ('header', header),
    ('section-end', section_end),
    ('func-end', func_end),
    ('jump-table', label_diff),
    ('span', span),
    ('seg-table', seg_table),
    ('img-b-eq', img_b_eq),
    ('region-count', region_count),
    ('seg0-size', seg0_size),
    ('r_a3-length', ra3_len),
    ('shadow-window', shadow_window),
    ('czone', czone),
    ('arith', arith),
    ('page-index', page_index),
    ('rodata-prefix', rodata_prefix),
    ('constant', const),
    ('address', address),
    ('kept', kept),
    ('model-line', model_line),
    ('model-skeleton', model_skeleton),
    ('model-twin', model_twin),
    ('kept-address', kept_address),
    ('address-wrong', address_wrong),
    ('nonimage-moved', nonimage_moved),
]
ADDED_GROUPS = ('program-rows', 'added-line')

# the image-derived roles that are no address (counts and positions in the image region lists, segment sizes and
# tables, R_A3's length, shadow windows, section and function ends, quotients): such a numeral can be wrong while
# both tools keep it, so every position whose line gives it one of these roles is decided
DERIVED = re.compile(r'seg_size|R_A3|img_cells_view|img_at_of_cimg|Definition SH_(LO|HI)\b|Definition tfib_\w+_hi\b|'
                     r'Definition tfib_E_\w+|change \(\(\S+ - \S+\) / 8\) with|\(65536, 131072\)')


def scope(r, c):
    """why a position is decided ('' when it is not)"""
    s = []
    if r['class'] not in ('agree', 'both-kept'):
        s.append('nonagree')
    glo, gsz = c.ggot
    dlo, dsz = c.dgot
    if glo <= r['d'] < glo + gsz or (r['p'] is not None and dlo <= r['p'] < dlo + dsz) or \
            (r['al'] is not None and dlo <= r['al'] < dlo + dsz):
        s.append('got')
    if r['rule'].split(' (')[0] == 'symbol':
        s.append('symbol')
    if r['class'] == 'both-kept' and r['d'] < c.g_top and (r['rule'] != '-' or r['d'] >= 0x10000):
        s.append('constant')
    if r['class'] == 'both-kept' and SHADOW_OFF + 0x10000 // 8 <= r['d'] < SHADOW_OFF + c.g_top // 8:
        s.append('shadow')
    if r['class'] == 'both-kept' and (region_role(r) or DERIVED.search(r['text']) or
                                      r['d'] in (c.g_top // 4096, c.g_top - 0x10000)):
        s.append('derived')
    if r['class'] == 'agree':
        s.append('moved')
    return ','.join(s)


def main():
    ap = argparse.ArgumentParser()
    for k in ('positions', 'hub', 'ref', 'src-lib', 'stage-out', 'unit-lib', 'grant-elf', 'grant-syms',
              'target-elf', 'target-syms', 'model-libs', 'model-elfs', 'out-rows', 'out-counts'):
        ap.add_argument('--' + k, required=True)
    ap.add_argument('--file-prefix', default='', help='written before each lib-relative file name in OUT_ROWS (the '
                    'unit lib\'s repository path and a slash, so the rows name repository-relative files)')
    a = ap.parse_args()
    c = Ctx(a)

    def explain_table(a_g):
        """the transport twin of a grant jump-table address: the address whose table of label differences has the same
        targets (entry + word in the same function at the same offset), searched over .rodata"""
        wg = c.G.word(a_g)
        tg = a_g + wg
        hold = [x for x in c.G.holders(tg) if x[3] == 'STT_FUNC']
        fn = hold[0][2]
        off = tg - hold[0][0]
        fs = c.D.uniq(fn)
        ro = c.D.secrange('.rodata')
        cands = [x for x in range(ro[0], ro[0] + ro[1], 4) if c.D.word(x) is not None and
                 (x + c.D.word(x)) & 0xffffffff == fs[0] + off]
        good = [x for x in cands if all(c.D.word(x + 4 * k) is not None and c.G.word(a_g + 4 * k) is not None and
                                        c.D.loc(x + 4 * k + c.D.word(x + 4 * k)).split(',')[0] ==
                                        c.G.loc(a_g + 4 * k + c.G.word(a_g + 4 * k)).split(',')[0]
                                        for k in range(-2, 3))]
        assert len(good) == 1, (hex(a_g), [hex(x) for x in cands], [hex(x) for x in good])
        return good[0]
    c.explain_table = functools.lru_cache(maxsize=None)(explain_table)

    cols = open(a.positions).readline().rstrip('\n').split('\t')
    counts, undecided, wrong = collections.Counter(), [], []
    with open(a.out_rows, 'w') as fh:
        fh.write('\t'.join(['file', 'donor_line', 'out_line', 'tok', 'donor', 'port_core', 'alreloc', 'alreloc_rule',
                            'class', 'kind', 'scope', 'group', 'decision', 'elf_reading', 'alreloc_verdict']) + '\n')
        for l in open(a.positions).read().split('\n')[1:]:
            if not l:
                continue
            r = dict(zip(cols, l.split('\t')))
            r['col'] = int(r['column'])
            r['rule'] = r['alreloc_rule']
            if r['class'] == 'added':
                r['ln'] = None
                r['text'] = c.relocated(r['file'])[int(r['out_line']) - 1]
                r['d'] = val(r['port_core'])
                r['donor'] = r['port_core']
            else:
                r['ln'] = int(r['donor_line'])
                r['text'] = c.donor(r['file'])[r['ln'] - 1]
                r['d'] = val(r['donor'])
            r['pre'] = r['text'][:r['col']]
            r['post'] = r['text'][r['col'] + len(r['donor']):]
            r['p'] = val(r['port_core']) if r['port_core'] != '-' else None
            r['al'] = val(r['alreloc']) if r['alreloc'] != '-' else None
            sc = scope(r, c)
            name, res = '-', ('-', '')
            if sc:
                res = None
                for name, fn in GROUPS:
                    if r['class'] == 'added' and name not in ADDED_GROUPS:
                        continue
                    if r['p'] is None and name not in ('program-rows', 'patched-tactic'):
                        continue
                    res = fn(r, c)
                    if res:
                        break
                if not res:
                    name = '-'
                    res = ('UNDECIDED: no group decides it', 'grant %s = %s; port_core %s = %s; the line: `%s`; %s' % (
                        r['donor'], c.G.loc(r['d']) if r['d'] >= 0x1000 else 'below the image', r['port_core'],
                        c.D.loc(r['p']) if r['p'] and r['p'] >= 0x1000 else '-', use(r), al_note(r, c)))
                if res[0].startswith('UNDECIDED'):
                    undecided.append('%s:%s(out %s) %s pc=%s al=%s %s | %s' % (
                        r['file'], r['donor_line'], r['out_line'], r['donor'], r['port_core'], r['alreloc'],
                        r['class'], res[0]))
                elif res[0].startswith(WRONG):
                    wrong.append('%s:%s(out %s) %s -> %s: %s' % (r['file'], r['donor_line'], r['out_line'],
                                                                r['donor'], r['port_core'], res[0]))
            verdict = res[0].split(':')[0] if res[0] != '-' else '-'
            counts[(r['class'], r['kind'] or '-', name, verdict)] += 1
            fh.write('\t'.join(s.replace('\t', ' ').replace('\n', ' ') for s in [
                a.file_prefix + r['file'], r['donor_line'], r['out_line'], r['tok'],
                r['donor'] if r['class'] != 'added' else '-',
                r['port_core'], r['alreloc'], r['alreloc_rule'], r['class'], r['kind'], sc or '-', name, res[0],
                res[1], al_verdict(r, res[0])]) + '\n')
    with open(a.out_counts, 'w') as fh:
        fh.write('class\tkind\tgroup\tverdict\tcount\n')
        for k, n in sorted(counts.items()):
            fh.write('\t'.join(k) + '\t%d\n' % n)
    print('alreloc_decide.py: .got tables: %d / %d slots, %d aligned by content' % c.got_stats
          if hasattr(c, 'got_stats') else 'alreloc_decide.py: no .got row')
    vc = collections.Counter()
    for (cl, k, g, v), n in counts.items():
        vc[v] += n
    print('alreloc_decide.py: %d positions; decided: %s; not in scope: %d' % (
        sum(counts.values()), ', '.join('%s %d' % (v, n) for v, n in sorted(vc.items()) if v != '-'), vc['-']))
    for w in wrong:
        print('  WRONG ' + w)
    for u in undecided[:200]:
        print('  UNDECIDED ' + u)
    if len(undecided) > 200:
        print('  ... %d more UNDECIDED' % (len(undecided) - 200))
    sys.exit(1 if wrong else 3 if undecided else 0)


if __name__ == '__main__':
    main()
