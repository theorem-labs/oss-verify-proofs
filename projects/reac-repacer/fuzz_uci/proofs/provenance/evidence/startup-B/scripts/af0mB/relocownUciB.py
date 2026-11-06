#!/usr/bin/env python3
"""relocownUciB.py -- fuzz_decode B's relocownB.py (provenance/startup-gen/B/af0m/relocownB.py at -decB 7eb81ddb186, sha256
4a866ee29181) with fuzz_uci image B's inputs; only paths, the header text and the output names change, no rule.

relocownB.py -- derive libreac/fuzz_decode IMAGE B's Tfib_owned_static from decode B's OWN image, keyed by a NAME,
exactly as image A was derived (provenance/startup-gen/A/af0m/{relocown,patchbase,control,audit}.py), with the
DONOR = cgif (image B's donor, a10 COREB-STATUS), not grant.

The base (commit ca2cdd36b2e lib/B/YF0m.v) carries cgif's Tfib_owned_static VERBATIM (unrelocated: cgif .data
0x9ff18 vs decode .data 0x9aff8). Every donor row is mapped by a KEY and kept under decode's own key:
  asan_globals descriptor array / per-global redzone -> class c (af0m.py regenerates it)
  .got / .data.rel.ro entry  -> by_pointer: the POINTER TARGET's name; decode's slot holding decode's &target
                                (decode statically resolves these -> no decode .got slot -> DROP, class d)
  .rodata entry              -> by_symbol, else by_content (the unique / indexed .rodata bytes in decode)
  .data / .bss / other       -> by_symbol (cgif symbol name + offset -> decode symbol + same offset)
cgif is STRIPPED: its symbols come from the release's recovery cache (cgif.syms.v4.json, the file a10 names).
Decode's symbols come from the unstripped twin. Containment: every kept range lies in a decode section with the SAME
NAME as the donor's, first byte to last.
"""
import re, os, sys, json, bisect, collections
from elftools.elf.elffile import ELFFile

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from ucib_env import need  # noqa: E402
HERE = os.environ.get('UCIB_AF0MB') or os.path.dirname(os.path.abspath(__file__))   # inputs: base / donor YF0m, syms
DEC_PIN  = need('UCIB_UB')
DEC_TWIN = need('UCIB_UBS')
CG_IMG   = need('UCIB_CB')
CG_SYMS  = os.path.join(HERE, 'cgif.syms.v4.json')
BASE     = os.path.join(HERE, 'base.YF0m.v')
DONOR    = os.path.join(HERE, 'cgif.YF0m.v')

sys.path.insert(0, os.path.join(HERE, '..', 'frozen-set'))   # af0m 238598b380f1 (bundle of record)
from af0m import jt_twin  # noqa: E402


class Img:
    def __init__(self, elf_path, twin=None, cache=None):
        self.e = ELFFile(open(elf_path, 'rb'))
        self.secs = sorted((s['sh_addr'], s['sh_addr'] + s['sh_size'], s.name)
                           for s in self.e.iter_sections() if s['sh_addr'])
        self.sym = {}
        self.syms = []
        if cache:
            for a, sz, names, typ, cls in json.load(open(cache))['syms']:
                for nm in names:
                    self.sym.setdefault(nm, (a, sz))
                self.syms.append((a, sz, names[0]))
        else:
            src = ELFFile(open(twin, 'rb')) if twin else self.e
            for st in src.iter_sections():
                if st.header['sh_type'] in ('SHT_SYMTAB', 'SHT_DYNSYM'):
                    for s in st.iter_symbols():
                        t = s['st_info']['type']
                        if s['st_value'] and s.name and t in ('STT_OBJECT', 'STT_FUNC', 'STT_NOTYPE'):
                            self.sym.setdefault(s.name, (s['st_value'], s['st_size']))
                            self.syms.append((s['st_value'], s['st_size'], s.name))
        self.syms.sort()
        self.starts = [x[0] for x in self.syms]
        self.loads = [(sg['p_vaddr'], sg['p_offset'], sg['p_filesz'], sg['p_memsz'])
                      for sg in self.e.iter_segments() if sg['p_type'] == 'PT_LOAD']
        self.raw = open(elf_path, 'rb').read()

    def sec(self, z):
        for lo, hi, n in self.secs:
            if lo <= z < hi:
                return n
        return None

    def secrange(self, name):
        for lo, hi, n in self.secs:
            if n == name:
                return lo, hi
        return None

    def symof(self, z):
        i = bisect.bisect_right(self.starts, z)
        best = None
        for k in range(max(0, i - 80), i):
            a, sz, n = self.syms[k]
            if a <= z < a + max(sz, 1):
                if best is None or (sz and sz < best[2]) or (best[2] == 0 and sz):
                    best = (n, z - a, sz)
        return best

    def byte(self, z):
        for va, off, fs, ms in self.loads:
            if va <= z < va + fs:
                return self.raw[off + z - va]
            if va <= z < va + ms:
                return 0
        return None

    def word(self, z):
        b = [self.byte(z + k) for k in range(8)]
        return None if None in b else sum(x << (8 * k) for k, x in enumerate(b))

    def hull(self):
        lo = min(va for va, *_ in self.loads) & ~0xfff
        hi = max((va + ms + 0xfff) & ~0xfff for va, off, fs, ms in self.loads)
        return lo, hi


def descriptors(img):
    s = img.secrange('asan_globals')
    if not s:
        return None, 0, []
    lo, hi = s
    out = [[img.word(i + 8 * k) for k in range(8)] for i in range(lo, hi, 64)]
    return lo, hi - lo, out


def const_abs(path):
    t = open(path).read()
    i = t.index('Definition Tfib_const_abs'); j = t.index('].', i)
    out = []
    for r in t[i:j].split(';'):
        m = re.search(r'z(\d) \(ANum (0x[0-9a-fA-F]+|\d+)\) (0x[0-9a-fA-F]+|\d+)', r)
        if m:
            out.append((int(m.group(1)), int(m.group(2), 0), int(m.group(3), 0)))
    return out


class R:
    def __init__(self, D, G):
        self.D, self.G = D, G
        self.dmeta, self.dmlen, self.dgl = descriptors(D)
        self.gmeta, self.gmlen, self.ggl = descriptors(G)
        self.drz = sorted((g[0] + g[1], g[0] + g[2]) for g in self.dgl if g[2] > g[1])
        self.grz = sorted((g[0] + g[1], g[0] + g[2]) for g in self.ggl if g[2] > g[1])
        self.dro_lo, self.dro = self._secbytes(D, '.rodata')
        self.gro_lo, self.gro = self._secbytes(G, '.rodata')
        self.pairs = {}
        B, Gc = const_abs(BASE), const_abs(DONOR)
        for k in range(min(len(B), len(Gc))):
            if B[k][0] == Gc[k][0] and B[k][2] == Gc[k][2]:
                self.pairs.setdefault(Gc[k][1], set()).add(B[k][1])

    @staticmethod
    def _secbytes(img, name):
        lo, hi = img.secrange(name)
        return lo, bytes((img.byte(z) or 0) for z in range(lo, hi))

    def by_symbol(self, z):
        s = self.G.symof(z)
        if not s or s[0] in ('$d', '$x'):
            return None, None
        n, off, sz = s
        if n not in self.D.sym:
            return None, '%s+%#x: NOT in decode' % (n, off)
        return self.D.sym[n][0] + off, '%s+%#x (cgif %#x, decode %#x)' % (n, off, self.G.sym[n][0], self.D.sym[n][0])

    def mapval(self, v):
        if v is None:
            return None
        s = self.G.symof(v)
        if s and s[0] not in ('$d', '$x') and s[0] in self.D.sym:
            return self.D.sym[s[0]][0] + s[1], '&%s+%#x' % (s[0], s[1])
        sn = self.G.sec(v)
        if sn and self.D.secrange(sn):
            return self.D.secrange(sn)[0] + (v - self.G.secrange(sn)[0]), '%s+%#x' % (sn, v - self.G.secrange(sn)[0])
        for nm_ in ('asan_globals', '.rodata', '.data', '.bss'):
            r2 = self.G.secrange(nm_)
            if r2 and v == r2[1] and self.D.secrange(nm_):
                return self.D.secrange(nm_)[1], 'the one-past end of %s' % nm_
        return None

    def by_pointer(self, z, n):
        tgts, outs = [], []
        lo, hi = self.D.secrange(self.G.sec(z))
        for k in range(0, n, 8):
            v = self.G.word(z + k)
            mv = self.mapval(v) if v else None
            if mv is None:
                tgts.append((v, None)); outs.append(None); continue
            tgts.append((v, mv[1]))
            outs.append([q for q in range(lo, hi, 8) if self.D.word(q) == mv[0]])
        if not outs or any(h is None or len(h) == 0 for h in outs):
            return None, 'targets %s: no decode .got slot' % [(hex(v) if v else None, s) for v, s in tgts]
        cands = [h for h in outs[0] if all((h + 8 * i) in outs[i] for i in range(len(outs)))]
        if len(cands) != 1:
            return None, 'targets %s -> %d consistent starts' % ([s for _, s in tgts], len(cands))
        return cands[0], 'slots holding %s (cgif %#x -> decode %#x)' % (', '.join(s for _, s in tgts), z, cands[0])

    def by_content(self, z, n):
        b = bytes((self.G.byte(z + k) or 0) for k in range(n))
        hits = [self.dro_lo + i for i in range(len(self.dro) - n + 1) if self.dro[i:i + n] == b]
        ghits = [self.gro_lo + i for i in range(len(self.gro) - n + 1) if self.gro[i:i + n] == b]
        pair = sorted(self.pairs.get(z, ()))
        tag = b[:12].hex() + ('..' if n > 12 else '')
        if len(hits) == 1:
            ok = (not pair) or pair == [hits[0]]
            return hits[0], '.rodata content %s (unique; base const_abs pair %s %s)' % (tag, [hex(p) for p in pair], 'AGREES' if ok else 'DISAGREES')
        if z in ghits and len(ghits) == len(hits):
            k = ghits.index(z)
            return hits[k], '.rodata content %s, copy %d of %d (same count both images)' % (tag, k, len(hits))
        if pair and len(pair) == 1 and pair[0] in hits:
            return pair[0], '.rodata content %s (%d here / %d donor; base const_abs picks %#x)' % (tag, len(hits), len(ghits), pair[0])
        return None, '.rodata content %s: %d occurrences, donor %d, base pair %s' % (tag, len(hits), len(ghits), [hex(p) for p in pair])

    def by_anchor(self, z, n):
        """a .got range whose words are not all image pointers (a linker constant, &__start/__stop, -2048, 8, ...):
        key it by the NEAREST slot that IS a named pointer. decode's unique slot holding that name fixes the frame;
        every word of the entry must then agree (a pointer word through its name, a constant word literally)."""
        gsec = self.G.sec(z)
        lo, hi = self.D.secrange(gsec)
        cands = {}
        for k in sorted(list(range(-8, 0)) + list(range(1, 9)), key=abs):
            gv = self.G.word(z + 8 * k)
            mv = self.mapval(gv) if gv else None
            if not mv:
                continue
            hits = [p for p in range(lo, hi, 8) if self.D.word(p) == mv[0]]
            if len(hits) != 1:
                continue
            cands.setdefault(hits[0] - 8 * k, []).append('%s at %+d slots' % (mv[1], k))
        for start, why in cands.items():
            bad = None
            for k in range(0, n, 8):
                gv, dv = self.G.word(z + k), self.D.word(start + k)
                mv = self.mapval(gv)
                want = mv[0] if mv else gv
                if dv != want:
                    bad = 'word %+d: cgif %#x -> %s, decode holds %s' % (k, gv, hex(want) if want is not None else None, hex(dv) if dv is not None else None)
                    break
            if bad is None:
                return start, 'ANCHOR %s (cgif %#x -> decode %#x); every word agrees' % (' / '.join(why), z, start)
        return None, 'no anchor verifies (candidates %s)' % {hex(k): v for k, v in cands.items()}

    def entry(self, lo, n):
        if self.gmlen and self.gmeta <= lo < self.gmeta + self.gmlen:
            return 'c', self.dmeta, 'asan_globals descriptor array: decode (%#x, %#x), %d descriptors' % (self.dmeta, self.dmlen, len(self.dgl)), self.dmlen
        if (lo, lo + n) in self.grz:
            return 'c', None, 'cgif per-global redzone [%#x, %#x): replaced by decode\'s %d redzones' % (lo, lo + n, len(self.drz)), None
        sec = self.G.sec(lo)
        if sec in ('.got', '.data.rel.ro'):
            nv, how = self.by_pointer(lo, n)
            if nv is not None:
                return 'b', nv, 'POINTER ' + how, None
            nv2, how2 = self.by_anchor(lo, n)
            if nv2 is not None:
                return 'b', nv2, how2, None
            return 'd', None, 'POINTER %s ; %s' % (how, how2), None
        if sec == '.rodata':
            nv, how = self.by_symbol(lo)
            if nv is not None:
                return 'b', nv, 'SYMBOL ' + how, None
            nv, how = self.by_content(lo, n)
            return ('b', nv, 'CONTENT ' + how, None) if nv is not None else ('d', None, 'CONTENT ' + how, None)
        nv, how = self.by_symbol(lo)
        return ('b', nv, 'SYMBOL ' + how, None) if nv is not None else ('d', None, 'SYMBOL ' + (how or 'no cgif symbol at %#x (sec %s)' % (lo, sec)), None)


def owned_of_text(t):
    m = re.search(r'Definition Tfib_owned_static[^=]*:=\n\[(.*?)\]\.', t, re.S)
    return m.group(1), re.findall(r'\((0x[0-9a-f]+), ([^)]+)\)', m.group(1))


def main():
    D = Img(DEC_TWIN)
    G = Img(CG_IMG, cache=CG_SYMS)
    r = R(D, G)
    base = open(BASE).read(); donor = open(DONOR).read()
    own_txt, pairs = owned_of_text(base)
    _, dpairs = owned_of_text(donor)
    assert len(pairs) == len(dpairs), (len(pairs), len(dpairs))
    drz_txt = '; '.join('(%#x, %#x)' % (lo, hi - lo) for lo, hi in r.drz)
    newtxt = own_txt
    rows = []
    rz_done = False
    cand11 = {0x9e208, 0x9e260, 0x9e1e8, 0x9e210, 0x9e228, 0x9ed70, 0x9ee60, 0x9ee98, 0x9ef00, 0x9ef10, 0x9eea8}
    # the two owned .rodata cells that are JUMP-TABLE entries (cgif's; their bytes are an ADDRESS that differs per
    # image, so by_content cannot find them in decode). af0m.jt_twin maps them by table + entry index, as man-3's A
    # patchbase did for grant's 0x20bfc / 0x218c8. Applied as an explicit override (NOT inside entry()), so the
    # cgif->cgif identity control stays by_content-clean.
    JT = {0x20b40: jt_twin(CG_IMG, DEC_PIN, 0x20b40), 0x21408: jt_twin(CG_IMG, DEC_PIN, 0x21408)}
    for i, (a, l) in enumerate(pairs):
        lo, n = int(a, 16), int(eval(l.strip()))
        cls, nv, how, extra = r.entry(lo, n)
        if lo in JT and JT[lo] is not None:
            cls, nv, how, extra = 'b', JT[lo], 'JUMP-TABLE entry (af0m jt_twin %#x -> %#x, same table/index)' % (lo, JT[lo]), None
        repl = None
        if cls == 'c':
            if extra is not None:
                repl = '(%#x, %#x)' % (nv, extra); nvs = repl
            else:
                repl = drz_txt if not rz_done else ''; rz_done = True
                nvs = drz_txt if repl else '(folded into decode redzone block)'
        elif cls == 'b' and nv is not None:
            nn = n
            # KEY THE END too: a .data/.bss range runs to a boundary SYMBOL (cgif's __dso_handle ends at oft_arg0);
            # cgif's and decode's section contents differ, so the verbatim length is wrong. Map the end address by its
            # own symbol and take length = map(end) - map(lo). (.got/.rodata rows have intrinsic lengths: left as is.)
            if how.startswith('SYMBOL') and n > 8:
                nve, _he = r.by_symbol(lo + n)
                if nve is not None and D.sec(nve - 1) == G.sec(lo + n - 1):
                    nn = nve - nv
            end_ok = D.sec(nv) == G.sec(lo) and D.sec(nv + nn - 1) == G.sec(lo)
            repl = '(%#x, %#x)' % (nv, nn); nvs = repl + ('' if end_ok else ' SECTION-SPAN?')
        else:
            nvs = '-'
        rows.append((i, '(%s, %s)' % (a, l.strip()), cls, '%s cgif=%s' % (how, G.sec(lo)), nvs, lo in cand11))
        if repl is not None:
            if repl:
                newtxt = newtxt.replace('(%s, %s)' % (a, l.strip()), repl, 1)
            else:
                newtxt = (newtxt.replace('(%s, %s); ' % (a, l.strip()), '', 1)
                          .replace('(%s, %s);' % (a, l.strip()), '', 1)
                          .replace('(%s, %s)' % (a, l.strip()), '', 1))
        elif cls == 'd':
            newtxt = (newtxt.replace('(%s, %s); ' % (a, l.strip()), '', 1)
                      .replace('\n(%s, %s);' % (a, l.strip()), '', 1)
                      .replace('(%s, %s);' % (a, l.strip()), '', 1)
                      .replace('(%s, %s)' % (a, l.strip()), '', 1))
    newtxt = re.sub(r';\s*;', ';', newtxt)
    newtxt = re.sub(r'\[\s*;', '[', newtxt)
    newtxt = re.sub(r';\s*\]', ' ]', newtxt)
    newtxt = re.sub(r'\n\s*\n', '\n', newtxt)
    # musl __atexit cells: WITHDRAWN (decision of record, superseding an earlier one). `slot` (0x5f4330) and
    # `head` (0x5f4338) are NOT owned: an owned cell must hold its value for the whole run, but target_run's
    # post-main atexit registration rewrites slot 1 -> 2, and the driver window DRV_IVS covers that area, so AD1y's
    # DRVW_not_owned would be false (found on image A). They are therefore neither --add cells nor
    # Tfib_owned_static rows. Dropping the rows also leaves R_A7b uncut, which gen_ad1k's roles() needs.
    musl = ''
    # decode's 3 asan_globals have ODR indicators (descriptor field +56 = 0x5d39c0, 0x5d39c1, 0x5d39c2); cgif's 3
    # globals have odr_indicator = -1 (no ODR), so the cgif base has no such owned range. The 3 indicator bytes are
    # written 0 -> 1 by start-up at registration (determined = 1 in all 50 states); they are owned. Keyed by decode's
    # OWN descriptors' odr_indicator fields (read from this image's asan_globals), emitted as one contiguous range.
    import struct as _struct
    odr = []
    for i in range(r.dmeta, r.dmeta + r.dmlen, 64):
        a_ = D.word(i + 56)
        if a_ is not None and a_ != (1 << 64) - 1 and D.sec(a_):
            odr.append(a_)
    odr_row = ''
    if odr:
        olo, ohi = min(odr), max(odr) + 1
        assert all(D.sec(z) == D.sec(olo) for z in range(olo, ohi)), 'ODR range spans sections'
        odr_row = '; (%#x, %#x)' % (olo, ohi - olo)
    newtxt = newtxt.rstrip().rstrip(']').rstrip() + musl + odr_row + ' '
    out = base.replace(own_txt, newtxt)
    hdr = ('(* Modified by Theorem Labs: Tfib_owned_static DERIVED from reac-repacer/fuzz_uci.asan-ubsan\'s own '
           'section headers + twin symtab and its asan_globals, keyed by NAME (cgif donor symbols from the release '
           'recovery cache 978e0a06, pointer targets, .rodata content, jump-table index), not by address; every cgif '
           '.got indirection slot is KEPT at decode\'s own .got address (decode links them too). Plus decode\'s musl '
           '__atexit slot/head (--add cells a10 named). See provenance/startup-gen/B/af0m/baseaudit.tsv. *)')
    open(os.path.join(HERE, 'base.patched.YF0m.v'), 'w').write(out)
    tsv = ['row\tbase (cgif) value\tclass\tkey / how\tdecode value\tcand11']
    for x in rows:
        tsv.append('\t'.join(str(y) for y in x))
    open(os.path.join(HERE, 'baseaudit.tsv'), 'w').write('\n'.join(tsv) + '\n')
    print('rows %d, classes %s' % (len(rows), dict(collections.Counter(x[2] for x in rows))))
    print('decode asan_globals %#x/%#x, %d descriptors; redzones %s' % (r.dmeta, r.dmlen, len(r.dgl), [(hex(a), hex(b)) for a, b in r.drz]))
    print('cgif  asan_globals %#x/%#x, %d descriptors' % (r.gmeta, r.gmlen, len(r.ggl)))
    print('decode hull %s' % [hex(x) for x in D.hull()])
    print('--- all b/d rows ---')
    for x in rows:
        if x[2] in ('b', 'd'):
            print('  owned[%2d] %-26s %s  %-70s -> %s%s' % (x[0], x[1], x[2], x[3][:70], x[4], '   <<CAND11' if x[5] else ''))
    print('--- the 11 candidates ---')
    for x in rows:
        if x[5]:
            print('  owned[%2d] %-26s class %s  %s -> %s' % (x[0], x[1], x[2], x[3][:80], x[4]))
    # identity control cgif->cgif (section+offset is identity; symbols map to self)
    I = R(G, G)
    bad = []; ok = 0
    for a, l in dpairs:
        lo, n = int(a, 16), int(eval(l.strip()))
        cls, nv, how, extra = I.entry(lo, n)
        if cls == 'c':
            if extra is not None and (nv, extra) != (r.gmeta, r.gmlen):
                bad.append('(%#x,%#x) desc->%s' % (lo, n, nv))
            else:
                ok += 1
            continue
        if nv != lo:
            bad.append('(%#x,%#x)->%s' % (lo, n, hex(nv) if nv else None))
        else:
            ok += 1
    print('IDENTITY cgif->cgif owned: %d/%d map to themselves%s' % (ok, ok + len(bad), '' if not bad else '; WRONG ' + '; '.join(bad)))
    # containment: every patched row in ONE decode section, same name as its cgif source section
    _, pown = owned_of_text(out)
    badc = []
    for a, l in pown:
        lo, n = int(a, 16), int(eval(l.strip()))
        s0, s1 = D.sec(lo), D.sec(lo + n - 1)
        if s0 is None or s0 != s1:
            badc.append('(%#x,%#x):%s..%s' % (lo, n, s0, s1))
    print('CONTAINMENT: %d/%d patched rows in ONE decode section%s' % (len(pown) - len(badc), len(pown), '' if not badc else '; OUTSIDE ' + '; '.join(badc)))
    print('patched rows per decode section: %s' % dict(collections.Counter(D.sec(int(a, 16)) for a, l in pown)))
    print('donor rows per cgif section:     %s' % dict(collections.Counter(G.sec(int(a, 16)) for a, l in dpairs)))


if __name__ == '__main__':
    main()
