#!/usr/bin/env python3
"""af0m.py -- the unit's A/AF0m.v (the runtime's state at main) from the image and the COLLECTED hand-off states.

  af0m.py --base RELOCATED_AF0m.v --values STATES.tsv --image IMAGE --binaries index/binaries.tsv
          [--symbols SYMBOLS.tsv] --out AF0m.v [--modified TEXT]

Relocation gets four of its lists wrong, because they are products of the unit's own registration, not of the donor's
text (measured on pcap; the same on fuzz_reply):
  Tfib_const_shadow  the donor's cells are ITS globals' redzone shadow; regenerated here from the unit's asan_globals
                     descriptors (the shadowfacts model: for each descriptor the redzone [beg+size, beg+size_with_rz)
                     gets the partial granule size mod 8 and 0xf9 after it, then the metadata section itself is 0xf9).
  Tfib_zero_shadow   the image's shadow outside those cells, in the same cut.
  Tfib_owned_static  the descriptor-array entry takes the unit's own size, and the donor's per-global redzone ranges are
                     replaced by the unit's.
  Tfib_const_abs     every value is re-read from the collected states, IN --base's ORDER (consumers index this list by
                     position: A/AD24.v's tfib_const_val), with the regenerated descriptor cells appended (byte model: KWord / KFill / KZero, and KImg from
                     the image), and the asan_globals descriptor cells are regenerated for the unit's descriptors.
The other constants are DERIVED here too, never passed through (a check on pcap found them passing through): TFIB_MAIN,
TFIB_MAIN_RA, TFIB_GP and TFIB_TP are the pc and the ra / gp / tp registers of the collected states; TFIB_ERRNO is
TFIB_TP - 164 (__errno_location is `mv a0,tp ; addi a0,a0,-164 ; ret`); TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_TSD,
TFIB_IAL_FLAG and TFIB_OOM are nm symbols of THIS image; TFIB_IAL_LO / _HI / _W must lie inside a symbol of this image;
TFIB_TR0 / TFIB_HASH / the bucket example come from tr0.py + dphash.py on this image; DRV_TRACES from --universe. A
constant that differs from --base's is REWRITTEN and reported. Tfib_const_sym and the TfibSyms record are --base's text.
The run FAILS if a cell is not implied by every collected state.

This is a new version of af0m.py 2ac2dbe25a9a with the same rules and the same output. It reads no log and no file at a
fixed path: the collected states come as --values, the per-value extract that extract_pass2.py writes from the collector's
pass-2 log (the state count, the pc / ra / gp / tp of the first state, and one row per cell this run reads with the set of
values the states give it); the names come as --symbols, the shared symbol extract, read through symbols.nm_lines (the
names file the generator was written for, byte for byte); the pin table comes as --binaries. A cell the run reads that
--values lacks, or a --values row the run never reads, REFUSES the run: a run that completes shows that the extract holds
exactly the values this generator reads.
"""
import argparse, os, re, struct, sys
from elftools.elf.elffile import ELFFile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import symbols

SHOFF = 0x7FFF8000


class Mem:
    def __init__(self, image):
        e = ELFFile(open(image, 'rb'))
        self.segs = [(s['p_vaddr'], s['p_filesz'], s['p_memsz'], s.data()) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
        self.e = e

    def byte(self, a):
        for va, fs, ms, d in self.segs:
            if va <= a < va + ms:
                return d[a - va] if a - va < fs else 0
        return None


def descriptors(image):
    e = ELFFile(open(image, 'rb'))
    s = e.get_section_by_name('asan_globals')
    if s is None:
        return 0, 0, []
    d = s.data()
    out = [struct.unpack_from('<8Q', d, 64 * i) for i in range(len(d) // 64)]
    return s['sh_addr'], len(d), out


def image_hull(image):
    """the unit's own image hull: the first PT_LOAD's page-rounded start and the last one's page-rounded end. NEVER a
    literal: cgif's top is 0x5fb000, fuzz_reply.asan-ubsan's 0x5fc000, fuzz_manifest's 0x5f7000 (a start-up certificate
    check found this generator hard-coding cgif's)."""
    e = ELFFile(open(image, 'rb'))
    ls = [(s['p_vaddr'], s['p_vaddr'] + s['p_memsz']) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
    lo = min(a for a, _ in ls) & ~0xFFF
    hi = (max(b for _, b in ls) + 0xFFF) & ~0xFFF
    return lo, hi


def shadow_lists(image, hull):
    meta, mlen, gl = descriptors(image)
    cells = {}
    for beg, size, szr, *_ in gl:
        for off in range(size // 8 * 8, szr, 8):
            cells[((beg + off) >> 3) + SHOFF] = (size - off) if off < size else 0xF9
    for off in range(0, mlen, 8):
        cells[((meta + off) >> 3) + SHOFF] = 0xF9
    bad = sorted({(k - SHOFF) << 3 for k in cells})
    rng, lo = [], hull[0]
    for g in bad:
        if g > lo:
            rng.append((lo, g))
        lo = max(lo, g + 8)
    rng.append((lo, hull[1]))
    return cells, rng, (meta, mlen, gl)


def jt_twin(old_img, new_img, cell):
    """a donor .rodata cell that is a JUMP-TABLE ENTRY (a run of 4-byte .text addresses): find the table in the donor,
    find the table in the new image whose relative-offset sequence is identical (it must be unique), and return the new
    cell (same entry index). W-S1 / W-S2: cgif 0x20b7c (table 0x20b1c, 33 entries, index 24) -> fuzz_reply 0x20be8 (table
    0x20b88); cgif 0x21448 (table 0x20f94, 311 entries, index 301) -> 0x21524 (table 0x21070). Returns None when the
    cell is not in such a table or the twin is not unique."""
    import struct

    def load(p):
        e = ELFFile(open(p, 'rb'))
        s = e.get_section_by_name('.rodata'); t = e.get_section_by_name('.text')
        return s['sh_addr'], s.data(), t['sh_addr'], t['sh_addr'] + t['sh_size']
    ob, od, otl, oth = load(old_img)
    if not (ob <= cell < ob + len(od) - 3):
        return None
    w = lambda a: struct.unpack_from('<I', od, a - ob)[0]
    v = w(cell)
    if not (otl <= v < oth):
        return None
    lo = cell
    while lo - 4 >= ob and otl <= w(lo - 4) < oth and abs(w(lo - 4) - v) < 0x4000:
        lo -= 4
    hi = cell
    while hi + 8 <= ob + len(od) and otl <= w(hi + 4) < oth and abs(w(hi + 4) - v) < 0x4000:
        hi += 4
    vals = [w(a) for a in range(lo, hi + 4, 4)]
    if len(vals) < 4:
        return None
    rel = [x - vals[0] for x in vals]
    nb, nd, ntl, nth = load(new_img)
    nw = lambda i: struct.unpack_from('<I', nd, i)[0]
    hits = []
    for i in range(0, len(nd) - 4 * len(rel) + 1, 4):
        x0 = nw(i)
        if not (ntl <= x0 < nth):
            continue
        if all(nw(i + 4 * k) - x0 == rel[k] for k in range(len(rel))):
            hits.append(nb + i)
    if len(hits) != 1:
        return None
    return hits[0] + (cell - lo)


def list_parts(defn):
    """`Definition X : T :=\n[ e1; e2 ... ].` -> (text up to '[', raw elements split at ';', text from the final ']')"""
    i = defn.index('['); j = defn.rindex(']')
    return defn[:i + 1], defn[i + 1:j].split(';'), defn[j:]


def join_parts(head, elems, old_raws, tail):
    """re-join elements; the last one gets the original list's closing whitespace"""
    end_ws = old_raws[-1][len(old_raws[-1].rstrip()):] if old_raws else '\n'
    elems = list(elems)
    if elems:
        elems[-1] = elems[-1].rstrip() + end_ws
    return head + ';'.join(elems) + tail


def fill_slots(slots):
    """give every 'fill' slot a duplicate of the nearest kept cell (previous, else next): a true fact that keeps the index"""
    n = 0
    for k, sl in enumerate(slots):
        if sl[0] != 'fill':
            continue
        src = next((slots[q] for q in list(range(k - 1, -1, -1)) + list(range(k + 1, len(slots))) if slots[q][0] == 'cell'), None)
        if src is None:
            sys.exit('af0m: no kept cell to fill slot %d with' % k)
        w, ad, v, _ = src[1]
        sl[0], sl[1] = 'cell', (w, ad, v, None)
        sl[3] = (sl[3] or 'filled') + ' -> filled with a duplicate of %#x/%d' % (ad, w)
        n += 1
    return n


def parse_cell(raw):
    m = re.search(r'z(\d) \(ANum (0x[0-9a-fA-F]+|\d+)\) (0x[0-9a-fA-F]+|\d+)', raw)
    if not m:
        return None
    return int(m.group(1)), int(m.group(2), 0), int(m.group(3), 0)


def load_values(path):
    """extract_pass2.py's table: (state count, {register: value}, {(addr, width): frozenset of the states' values})"""
    nstates, regs, cells = None, {}, {}
    for line in open(path):
        if line.startswith('#') or not line.strip():
            continue
        p = line.rstrip('\n').split('\t')
        if p[0] == 'states':
            nstates = int(p[1])
        elif p[0] == 'reg':
            regs[p[1]] = None if p[2] == '-' else int(p[2], 16)
        elif p[0] == 'cell':
            cells[(int(p[1], 16), int(p[2]))] = frozenset(None if x == '-' else int(x, 16) for x in p[3].split(','))
        else:
            sys.exit('af0m: unreadable --values row %r' % line[:80])
    if nstates is None or set(regs) != {'pc', 'x1', 'x3', 'x4'}:
        sys.exit('af0m: --values %s lacks the states row or the pc / x1 / x3 / x4 rows' % path)
    return nstates, regs, cells


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--base', required=True); ap.add_argument('--values', required=True); ap.add_argument('--image', required=True)
    ap.add_argument('--binaries', required=True, help="the pin table (index/binaries.tsv): --image's sha256 must be a row of it")
    ap.add_argument('--symbols', default=None, help='the symbol extract of the unstripped twin of --image (TSV, .symtab order)')
    ap.add_argument('--out', required=True); ap.add_argument('--modified', default=None)
    ap.add_argument('--universe', default=None, help="universe.py's --json output: DRV_TRACES is taken from it")
    ap.add_argument('--ab12', default=None, help="the unit's AB12/YB12: its img_lo / img_hi are cross-checked against the image hull")
    ap.add_argument('--twin', default=None, help='the unstripped twin of --image (its sha256 goes into the header)')
    ap.add_argument('--tmpl-image', default=None, help='the DONOR image: base cells/entries copied from it unrelocated are found')
    ap.add_argument('--tmpl-af0m', default=None, help="the DONOR's AF0m: an owned entry equal to one of its entries is checked as an unrelocated copy")
    ap.add_argument('--reads', action='append', default=[], metavar='FILE',
                    help='a walk\'s read list (one ADDR/W per line, # comments): every cell must be pinned by the states, '
                         'and the ones --base lacks are emitted (the acceptance list for Tfib_const_abs)')
    ap.add_argument('--add-block', action='append', default=[], metavar='SYMBOL',
                    help='emit every 8-byte word of an nm symbol (e.g. _ZN11__sanitizer21common_flags_dont_useE) that all states pin')
    ap.add_argument('--refused-map', action='append', default=[], metavar='DONOR=NEW',
                    help='a port_core_refused_<DONOR> row of --base whose new address is NEW (hex)')
    ap.add_argument('--refused-drop', action='append', default=[], metavar='DONOR',
                    help='a port_core_refused_<DONOR> row that is donor program data: its slot is filled, not removed')
    ap.add_argument('--plan', default=None, help="the unit's start-up plan (AB05/YB05): its PMprotect node backs the RELRO read-only rule")
    ap.add_argument('--no-pin-owned-ro', action='store_true', help='do not pin owned read-only static bytes (default: pin)')
    ap.add_argument('--add', action='append', default=[], metavar='ADDR/W',
                    help='a const cell --base lacks (e.g. one whose relocation was dropped); its value is read from every '
                         'state and must agree; it must be covered by Tfib_owned_static like every other cell')
    a = ap.parse_args()
    import pins
    prov = pins.provenance(a.image, a.twin, a.binaries)   # REFUSES unless --image is the unit's pinned original
    txt = open(a.base).read()
    mem = Mem(a.image)
    nstates, regv, table = load_values(a.values)
    used = set()

    def stated(ad, w):
        """the set of values the collected states give the cell [ad, ad + w) (None: a state does not determine it)"""
        if (ad, w) not in table:
            sys.exit('af0m: REFUSED: cell %#x/%d is not in %s: the extract must hold every cell this run reads'
                     % (ad, w, a.values))
        used.add((ad, w))
        return set(table[(ad, w)])
    nm_lines = symbols.nm_lines(a.symbols) if a.symbols else None
    hull = image_hull(a.image)
    m_ab12 = re.search(r'img_lo := (0x[0-9a-f]+); img_hi := (0x[0-9a-f]+)', a.ab12 and open(a.ab12).read() or '')
    if m_ab12:
        ab = (int(m_ab12.group(1), 16), int(m_ab12.group(2), 16))
        if ab != hull:
            sys.exit('af0m: the image hull %s disagrees with %s\'s img_lo/img_hi %s' % (
                tuple(map(hex, hull)), a.ab12, tuple(map(hex, ab))))
    cells, zrng, (meta, mlen, gl) = shadow_lists(a.image, hull)
    tmpl_own, tmpl_cells = None, None
    if a.tmpl_af0m:
        tt = open(a.tmpl_af0m).read()
        i0 = tt.index('Definition Tfib_owned_static'); j0 = tt.index('].', i0)
        tmpl_own = {'(%s, %s)' % (x, y.strip()) for x, y in re.findall(r'\((0x[0-9a-f]+), ([^)]+)\)', tt[i0:j0])}
        i1 = tt.index('Definition Tfib_const_abs'); j1 = tt.index('].', i1)
        tmpl_cells = {(c[0], c[1]): c[2] for c in (parse_cell(x) for x in tt[i1:j1].split(';')) if c}
    rep = ['globals %d, metadata %#x/%#x, shadow cells %d, zero-shadow ranges %d, states %d'
           % (len(gl), meta, mlen, len(cells), len(zrng), nstates)]

    def grab(name):
        i = txt.index('Definition %s' % name); j = txt.index('].', i)
        return txt[i:j + 2]

    # --- Tfib_const_abs: re-read every value, regenerate the descriptor cells. TEXT-PRESERVING: a cell whose value the
    # states confirm keeps the base's exact spelling (decimal or hex, spacing), so the donor control is byte-equality.
    # (Values written in DECIMAL are cells too: the donor writes 0x137ba0's 18446744073709551615 that way, and an
    # earlier hex-only reading of this list dropped it - a missing common_flags cell.)
    head, raws, tail = list_parts(grab('Tfib_const_abs'))
    # INDEX-PRESERVING: consumers reference Tfib_const_abs BY POSITION (A/AD24.v's tfib_const_val 72 / 71 / 51), so the
    # position of a cell is part of this file's interface. Every base row keeps its index: a kept cell stays in its slot,
    # a descriptor slot takes the next regenerated descriptor word (extra words are APPENDED), and a row that cannot stay
    # (a refused relocation resolved as donor data, a 0-descriptor image's descriptor slot, a cell the xowned gate drops)
    # is FILLED with a duplicate of the nearest kept cell - a true fact - and reported. A `port_core_refused_<donor hex>`
    # row (the core relocation writes them) is never skipped: it is a descriptor slot, or mapped by
    # --refused-map DONOR=NEW, or declared donor program data by --refused-drop DONOR, or the run FAILS listing it.
    rmap = {int(x.split('=')[0], 16): int(x.split('=')[1], 16) for x in a.refused_map}
    rdrop = {int(x, 16) for x in a.refused_drop}
    tmeta = tmlen = None
    if a.tmpl_image:
        tmeta, tmlen, _ = descriptors(a.tmpl_image)
    slots, base_raw, fixed, unresolved, notpinned, jt_moves = [], {}, 0, [], [], []
    for raw in raws:
        if not raw.strip():
            continue
        c = parse_cell(raw)
        ref = re.search(r'z(\d) \(ANum port_core_refused_([0-9a-f]+)\)', raw)
        if c is None and ref:
            w, dad = int(ref.group(1)), int(ref.group(2), 16)
            if tmlen and tmeta <= dad < tmeta + tmlen:
                slots.append(['desc', None, raw, 'refused donor descriptor word %#x' % dad]); continue
            if dad in rmap:
                c = (w, rmap[dad], None)
            elif dad in rdrop:
                slots.append(['fill', None, raw, 'refused donor cell %#x declared donor program data (--refused-drop)' % dad]); continue
            else:
                unresolved.append('%#x (row %d: %s)' % (dad, len(slots), raw.strip()[:60])); slots.append(['fill', None, raw, 'unresolved']); continue
        elif c is None:
            sys.exit('af0m: unreadable Tfib_const_abs element %r' % raw[:80])
        w, ad, v = c
        if v is not None:
            base_raw[(w, ad)] = (v, raw)
        if a.tmpl_image and tmpl_cells and (w, ad) in tmpl_cells and w == 4:
            # the base kept the DONOR's address: if it is a jump-table entry there, move it to its twin in this image
            tw = jt_twin(a.tmpl_image, a.image, ad)
            if tw is not None and tw != ad:
                jt_moves.append((ad, tw))
                ad, v, raw = tw, None, None
                c = (w, ad, None)
        if (mlen and meta <= ad < meta + mlen) or (tmlen and tmeta <= ad < tmeta + tmlen):
            slots.append(['desc', None, raw, 'descriptor word %#x' % ad]); continue
        vals = stated(ad, w)
        if len(vals) != 1 or None in vals:
            notpinned.append('%#x/%d' % (ad, w)); slots.append(['fill', None, raw, 'not pinned']); continue
        nv = vals.pop()
        fixed += (v is not None and nv != v)
        slots.append(['cell', (w, ad, nv, raw if (raw is not None and nv == v) else None), raw, None])
    if unresolved:
        sys.exit('af0m: REFUSED: %d port_core_refused rows in --base are not accounted for (give --refused-map DONOR=NEW or '
                 '--refused-drop DONOR for each; a skipped row would shift every later index): %s' % (len(unresolved), unresolved[:8]))
    if notpinned:
        sys.exit('af0m: REFUSED: base cells the states do not pin to one value: %s' % notpinned[:8])
    have = {(sl[1][0], sl[1][1]) for sl in slots if sl[0] == 'cell'}
    specs = list(a.add)
    for f in a.reads:
        for line in open(f):
            line = line.split('#')[0].strip()
            if line:
                specs.append(line)
    blocks = []
    for sym in a.add_block:
        if not a.symbols:
            sys.exit('af0m: --add-block needs --symbols')
        row = [l.split() for l in nm_lines if l.split() and l.split()[-1] == sym]
        if not row or len(row[0]) < 4:
            sys.exit('af0m: --add-block %s: not in %s (or no size column)' % (sym, a.symbols))
        lo, sz = int(row[0][0], 16), int(row[0][1], 16)
        for z in range(lo & ~7, lo + sz, 8):
            sv = stated(z, 8)
            if None not in sv and len(sv) == 1:
                specs.append('%#x/8' % z)
        blocks.append('%s [%#x, %#x)' % (sym, lo, lo + sz))
    appended = []
    for spec in specs:
        ad, w = spec.split('/'); ad, w = int(ad, 0), int(w)
        if (w, ad) in have:
            continue
        vals = stated(ad, w)
        if len(vals) != 1 or None in vals:
            sys.exit('af0m: REFUSED: cell %s is not pinned to one value by every state (%s): a walk that reads it cannot '
                     'take it from the start-up' % (spec, sorted(x for x in vals if x is not None)[:3]))
        v = vals.pop()
        appended.append((w, ad, v, None)); have.add((w, ad))
    desc = []
    for i, dsc in enumerate(gl):
        for k in range(8):
            ad = meta + 64 * i + 8 * k
            vals = stated(ad, 8)
            if len(vals) != 1 or None in vals:
                sys.exit('af0m: descriptor word %#x is not known in every state: %s' % (ad, vals))
            v = vals.pop()
            b = base_raw.get((8, ad))
            desc.append((8, ad, v, b[1] if b and b[0] == v else None))
    di = 0
    for sl in slots:
        if sl[0] == 'desc':
            if di < len(desc):
                sl[0], sl[1] = 'cell', desc[di]; di += 1
            else:
                sl[0], sl[3] = 'fill', (sl[3] or '') + ' (this image has fewer descriptor words)'
    extra_desc = desc[di:]
    nfill = fill_slots(slots)
    rep.append('const_abs: %d base rows kept in place (%d values corrected), %d descriptor words (%d in the base\'s slots, %d '
               'appended), %d slots filled with a duplicate, %d cells appended (reads / --add / blocks %s)'
               % (sum(1 for sl in slots if sl[3] is None), fixed, len(desc), di, len(extra_desc), nfill, len(appended), blocks or '-'))
    for sl in slots:
        if sl[3] and sl[3] != 'descriptor word' and sl[0] == 'cell' and sl[3].startswith(('refused', 'not', 'unresolved')):
            rep.append('  slot: %s' % sl[3])
    if jt_moves:
        rep.append('jump-table cells the base kept at the DONOR address, moved to their twins (same table, same entry index): %s'
                   % ', '.join('%#x -> %#x' % m for m in jt_moves))
    allc = [sl[1] for sl in slots] + extra_desc + appended
    txt = txt.replace(grab('Tfib_const_abs'), join_parts(head, [r if r is not None else '\nz%d (ANum %#x) %#x  ' % (w, ad, v)
                                                                for w, ad, v, r in allc], raws, tail))
    base_index = [(k, sl[1][1]) for k, sl in enumerate(slots) if sl[3] is None]
    jt_map = dict(jt_moves)
    # --- shadow lists
    bad = [(k, v) for k, v in cells.items() if stated(k, 1) != {v}]
    if bad:
        sys.exit('af0m: %d shadow cells are not implied by every state, first %s' % (len(bad), bad[:3]))
    txt = txt.replace(grab('Tfib_const_shadow'), 'Definition Tfib_const_shadow : list acell :=\n[ ' +
                      '  ;\n'.join('z1 (ANum %#x) %#x' % (k, v) for k, v in sorted(cells.items())) + '   ].')
    txt = txt.replace(grab('Tfib_zero_shadow'), 'Definition Tfib_zero_shadow : list (Z * Z) :=\n[ ' +
                      '; '.join('(%#x, %#x - %#x)' % (lo, hi, lo) for lo, hi in zrng) + ' ].')
    # --- owned_static: KEEP --base's ORDER (the donor control is byte-equality). The descriptor-array entry is replaced in
    # place by the unit's (or DROPPED when the unit has no asan_globals); the base's per-global redzone entries are
    # replaced, at the position of the first one, by the unit's redzones in address order. An entry the base copied from
    # the donor UNRELOCATED (same address as a --tmpl-image registration object, or bytes that differ from the donor's at
    # that address) is a relocation miss: registration entries are dropped, any other one REFUSES the run.
    own = grab('Tfib_owned_static')
    ohead, oraws, otail = list_parts(own)
    pairs = []
    for raw in oraws:
        mm = re.search(r'\((0x[0-9a-f]+), ([^)]+)\)', raw)
        if mm:
            pairs.append((mm.group(1), mm.group(2), raw))
    rz = sorted((beg + size, beg + szr) for beg, size, szr, *_ in gl if szr > size)
    unit_rz = ['\n(%#x, %#x)' % (lo, hi - lo) for lo, hi in rz]
    trz, tmem = [], None
    if a.tmpl_image:
        _, _, tgl = descriptors(a.tmpl_image)
        trz = [(beg + size, beg + szr) for beg, size, szr, *_ in tgl if szr > size]
        tmem = Mem(a.tmpl_image)
    out, rz_at, dropped_own, refused_own, base_rz = [], None, [], [], []
    for ad, ln, raw in pairs:
        v, n = int(ad, 16), int(eval(ln.strip()))
        if v in jt_map:
            nv_ = jt_map[v]
            raw = raw.replace('(%s, %s)' % (ad, ln), '(%#x, %s)' % (nv_, ln))
            ad, v = '%#x' % nv_, nv_
            out.append(raw)
            continue
        if (mlen and meta <= v < meta + mlen) or (tmlen and tmeta <= v < tmeta + tmlen):
            if mlen:
                same = (v, n) == (meta, mlen)
                out.append(raw if same else raw.replace('(%s, %s)' % (ad, ln), '(%#x, %#x)' % (meta, mlen)))
            else:
                dropped_own.append('%s/%s (descriptor array; this image has no asan_globals)' % (ad, ln.strip()))
            continue
        if any(lo <= v < hi for lo, hi in rz) or any((lo, hi - lo) == (v, n) for lo, hi in trz):
            if rz_at is None:
                rz_at = len(out)
            base_rz.append(raw)
            continue                      # a per-global redzone (the unit's, or the donor's copied): replaced wholesale
        if tmem is not None and not (mlen and meta <= v < meta + mlen):
            tb = [tmem.byte(v + k) for k in range(min(n, 64))]
            nb = [mem.byte(v + k) for k in range(min(n, 64))]
            secn = lambda m_, z: next((sc.name for sc in m_.e.iter_sections() if sc['sh_addr'] <= z < sc['sh_addr'] + sc['sh_size']), None)
            same_entry = ('(%s, %s)' % (ad, ln.strip())) in (tmpl_own or set())
            if same_entry and (tb != nb and secn(tmem, v) in ('.rodata', '.got', '.data.rel.ro') or secn(tmem, v) != secn(mem, v)):
                # a READ-ONLY donor entry that no const cell of the new list uses is donor PROGRAM data (fuzz_reply: cgif's
                # .rodata 0x20b7c / 0x21448): dropped and reported. Anything else - a cell uses it, or it is in .got /
                # a writable section - is a runtime object that moved and was not relocated: REFUSE.
                cab_now = [parse_cell(x) for x in list_parts(grab('Tfib_const_abs'))[1]]
                users = [c for c in cab_now if c and v <= c[1] < v + n]
                # a user that is itself the donor's cell at the same address with a DIFFERENT value is donor program data
                # copied by address too (fuzz_reply: cgif's .rodata 0x20b7c / 0x21448 cells); once the entry goes, the
                # xowned gate drops those cells as uncovered read-only cells
                used = any(not (tmpl_cells and (c[0], c[1]) in tmpl_cells and tmpl_cells[(c[0], c[1])] != c[2]) for c in users)
                if secn(mem, v) == '.rodata' and not used:
                    dropped_own.append('%s/%s (the donor\'s .rodata entry, unrelocated, bytes differ here; %s)'
                                       % (ad, ln.strip(), 'its only users are the donor\'s cells copied by address'
                                          if users else 'no const cell uses it'))
                else:
                    refused_own.append('%s/%s (the donor\'s entry, unrelocated: %s in the donor, %s here%s%s)' % (
                        ad, ln.strip(), secn(tmem, v), secn(mem, v), '' if tb == nb else ', bytes differ',
                        ', const cells use it' if used else ''))
                continue
        out.append(raw)
    if refused_own:
        sys.exit('af0m: REFUSED: owned entries copied from the donor without relocation: %s' % refused_own[:6])
    if rz_at is None:
        rz_at = len(out)
    # the unit's redzones replace the base's: when they are the same ranges (the donor control) keep the base's text
    base_rz_vals = [re.search(r'\((0x[0-9a-f]+), ([^)]+)\)', r).groups() for r in base_rz]
    if [(int(x, 16), int(eval(y))) for x, y in base_rz_vals] == [(lo, hi - lo) for lo, hi in rz]:
        unit_rz = base_rz
    out[rz_at:rz_at] = unit_rz
    txt = txt.replace(own, join_parts(ohead, out, oraws, otail))
    rep.append('owned_static: %d entries (base order kept; descriptor array %s; %d per-global redzones)%s'
               % (len(out), '(%#x, %#x)' % (meta, mlen) if mlen else 'ABSENT (no asan_globals)', len(unit_rz),
                  '' if not dropped_own else '; dropped: ' + ', '.join(dropped_own)))
    # --- PIN every OWNED read-only static byte (the rom_clean ruling, the AE2y rodata_chk pattern): AR's const law then
    # gives aview = image byte there, so an entry can discharge `rom_view SEGS W mem` from the start-up data. Owned =
    # Tfib_owned_static; read-only = a PT_LOAD without PF_W. Bytes some const cell already covers are skipped; the rest are
    # APPENDED (index-preserving) as aligned cells with the IMAGE's bytes, and each must equal what every state pins.
    if not a.no_pin_owned_ro:
        rosegs = [(sg['p_vaddr'], sg['p_vaddr'] + sg['p_memsz']) for sg in mem.e.iter_segments()
                  if sg['p_type'] == 'PT_LOAD' and not (sg['p_flags'] & 2)]
        owned_now = [(int(x, 16), int(eval(y))) for x, y in re.findall(r'\((0x[0-9a-f]+), ([^)]+)\)', grab('Tfib_owned_static'))]
        cur = [parse_cell(r) for r in list_parts(grab('Tfib_const_abs'))[1] if r.strip()]
        covered_b = set()
        for w, ad, v in cur:
            covered_b.update(range(ad, ad + w))
        need = sorted({z for lo, n in owned_now for z in range(lo, lo + n)
                       if any(rl <= z < rh for rl, rh in rosegs) and z not in covered_b})
        runs, pins = [], []
        for z in need:
            if runs and runs[-1][1] == z:
                runs[-1][1] = z + 1
            else:
                runs.append([z, z + 1])
        for lo, hi in runs:
            z = lo
            while z < hi:
                w = next(w for w in (8, 4, 2, 1) if z % w == 0 and z + w <= hi)
                iv = sum(mem.byte(z + k) << (8 * k) for k in range(w))
                sv = stated(z, w)
                if sv != {iv}:
                    sys.exit('af0m: REFUSED: owned read-only cell %#x/%d: image %#x, states %s' % (z, w, iv, sorted(x for x in sv if x is not None)[:3]))
                pins.append((w, z, iv)); z += w
        if pins:
            ch2, craws2, ctail2 = list_parts(grab('Tfib_const_abs'))
            body = [r for r in craws2 if r.strip()] + ['\nz%d (ANum %#x) %#x  ' % p for p in pins]
            txt = txt.replace(grab('Tfib_const_abs'), join_parts(ch2, body, craws2, ctail2))
        # SELF-CHECK (scene / boxreg regressions): every registered global whose redzone tail lies in a read-only PT_LOAD
        # must have the WHOLE tail [beg + size, beg + size_with_redzone) - its length from the descriptor, never assumed
        # (scene's placeholder: 0x8b8) - covered by const cells. A pin that covers part of a tail REFUSES.
        cur2 = [parse_cell(r) for r in list_parts(grab('Tfib_const_abs'))[1] if r.strip()] + [(w, z, v) for w, z, v in pins]
        cov2 = set()
        for w, ad, v in cur2:
            cov2.update(range(ad, ad + w))
        tails = [(beg + size, szr - size) for beg, size, szr, *_ in gl if szr > size and any(rl <= beg + size < rh for rl, rh in rosegs)]
        short = [(hex(t0), hex(n), sum(1 for z in range(t0, t0 + n) if z not in cov2)) for t0, n in tails
                 if any(z not in cov2 for z in range(t0, t0 + n))]
        if short:
            sys.exit('af0m: REFUSED: read-only redzone tails not fully pinned (start, size_with_redzone - size, bytes missing): %s'
                     % short[:6])
        rep.append('redzone-tail self-check: PASS (%d read-only tails, %d bytes, each covered at its full descriptor length: %s)'
                   % (len(tails), sum(n for _, n in tails), ', '.join('(%#x, %#x)' % t for t in tails[:8])))
        npin_bytes = len(need)
        rep.append('owned read-only pins: %d owned bytes in read-only PT_LOADs not covered by a const cell -> %d cells appended '
                   '(%d runs), each equal to the image byte and to every state' % (npin_bytes, len(pins), len(runs)))
        ro_pin_line = '(* owned read-only static bytes pinned as const cells from the image: %d bytes in %d cells *)' % (npin_bytes, len(pins))
    else:
        ro_pin_line = None
    # --- every TFIB_* constant: derived, not passed through
    def const(name):
        m = re.search(r'Definition %s : Z := (0x[0-9a-f]+)' % name, txt)
        return int(m.group(1), 16) if m else None
    # the pc and the ra / gp / tp registers (x1 / x3 / x4) of the first collected state, as --values gives them
    derived = {'TFIB_MAIN': regv['pc'],                   # the pc of every hand-off state
               'TFIB_MAIN_RA': regv['x1'],                 # ra at main: the return into __libc_start_main's stage 2
               'TFIB_GP': regv['x3'],                      # gp at main
               'TFIB_TP': regv['x4']}                      # tp at main
    if derived['TFIB_TP'] is not None:
        derived['TFIB_ERRNO'] = derived['TFIB_TP'] - 164   # __errno_location is `mv a0,tp ; addi a0,a0,-164 ; ret`
    nm, nmsz = {}, []
    if a.symbols:
        for line in nm_lines:
            p = line.split()
            if len(p) >= 4:
                nmsz.append((int(p[0], 16), int(p[1], 16), p[3]))
                nm.setdefault(p[3], int(p[0], 16))
        nmsz.sort()
    SYMS = {'TFIB_INST': '_ZN6__asanL8instanceE', 'TFIB_DEPOT': '_ZN11__sanitizerL8theDepotE',
            'TFIB_STORE': '_ZN11__sanitizerL10stackStoreE', 'TFIB_TSD': '__pthread_tsd_main',
            'TFIB_IAL_FLAG': '_ZN11__sanitizerL30internal_allocator_initializedE',
            'TFIB_OOM': '_ZN11__sanitizerL23allocator_out_of_memoryE'}
    for cname, sym in SYMS.items():
        if sym in nm:
            derived[cname] = nm[sym]
    bad = []
    for cname, want in sorted(derived.items()):
        have = const(cname)
        rep.append('%-14s base %s derived %s %s' % (cname, hex(have) if have is not None else '-',
                                                    hex(want) if want is not None else '-',
                                                    'OK' if have == want else 'DIFFERS'))
        if want is None or have is None:
            continue
        if have != want:
            txt = re.sub(r'(Definition %s : Z := )0x[0-9a-f]+' % cname, lambda m: m.group(1) + ('%#x' % want), txt)
            bad.append(cname)
    # the constants with no symbol of their own (interior addresses) must at least lie in a symbol of THIS image
    for cname in (('TFIB_IAL_LO', 'TFIB_IAL_HI', 'TFIB_IAL_W') if nmsz else ()):
        v = const(cname)
        own = [(ad, sz, n) for ad, sz, n in nmsz if ad <= v < ad + max(sz, 1)]
        rep.append('%-14s %#x in %s' % (cname, v, own[-1][2] if own else 'NO SYMBOL OF THIS IMAGE'))
        if not own:
            sys.exit('af0m: %s = %#x is not inside any symbol of %s' % (cname, v, a.image))
    if bad:
        rep.append('CORRECTED from the states/nm: %s' % ', '.join(bad))
    # --- TFIB_TR0 / TFIB_HASH from the image, through tr0's rule and the depot hash. An image with NO asan_globals never
    # enters __asan_register_globals, so it makes no start-up depot trace (d_nuniq = 0): the three items are REMOVED.
    if not mlen:
        for pat in (r'Definition TFIB_TR0 \(h : nat\) : list Z :=[^\n]*\n', r'Definition TFIB_HASH \(h : nat\) : Z :=[^\n]*\n',
                    r'Example tfib_hash_buckets :[^\n]*\n(?:Proof\.[^\n]*\n)?'):
            txt = re.sub(pat, '', txt)
        rep.append('TFIB_TR0 / TFIB_HASH / tfib_hash_buckets: ABSENT (no asan_globals: no start-up depot trace, d_nuniq = 0)')
    elif a.symbols:
        import subprocess
        out = subprocess.run([sys.executable, os.path.join(HERE, 'tr0.py'), a.image, '--symbols', a.symbols],
                             capture_output=True, text=True)
        m = re.search(r'TFIB_TR0 0 = \[(0x[0-9a-f]+); (0x[0-9a-f]+)\]', out.stdout)
        h = re.search(r'TFIB_HASH 0 = (\d+); TFIB_HASH _ = (\d+)', out.stdout)
        b = re.search(r'buckets \(mod d_tab_words = \d+\): (\d+) / (\d+)', out.stdout)
        if m and h and b:
            txt = re.sub(r'Definition TFIB_TR0 \(h : nat\) : list Z := match h with O => \[[^\]]*\] \| _ => \[[^\]]*\] end\.',
                         'Definition TFIB_TR0 (h : nat) : list Z := match h with O => [%s; %s] | _ => [%s] end.'
                         % (m.group(1), m.group(2), m.group(1)), txt)
            txt = re.sub(r'Definition TFIB_HASH \(h : nat\) : Z := match h with O => \d+ \| _ => \d+ end\.',
                         'Definition TFIB_HASH (h : nat) : Z := match h with O => %s | _ => %s end.' % (h.group(1), h.group(2)), txt)
            txt = re.sub(r'(Example tfib_hash_buckets : map \(fun h => \(TFIB_HASH h\) mod d_tab_words\) \[0%nat; 1%nat\] = )\[\d+; \d+\]',
                         lambda mm: mm.group(1) + '[%s; %s]' % (b.group(1), b.group(2)), txt)
            rep.append('TFIB_TR0 [%s; %s] / [%s], TFIB_HASH %s / %s, buckets %s / %s (tr0.py on this image)'
                       % (m.group(1), m.group(2), m.group(1), h.group(1), h.group(2), b.group(1), b.group(2)))
        else:
            sys.exit('af0m: tr0.py gave no trace/hash: %s' % (out.stdout or out.stderr)[:300])
    # --- DRV_TRACES from the generated universe, when one is given
    if a.universe:
        import json
        U = json.load(open(a.universe))
        drv = [t for f in ('main', 'target_run') for t in U['traces'].get(f, [])]
        pc0 = sorted({t[0] for t in drv})
        drv = [t for t in drv if len(t) > 1] + [[p] for p in pc0]
        body = ';\n'.join('[%s]' % '; '.join(t) for t in drv)
        txt = re.sub(r'Definition DRV_TRACES : list \(list Z\) :=\n\[.*?\]\.', 
                     'Definition DRV_TRACES : list (list Z) :=\n[%s].' % body, txt, flags=re.S)
        rep.append('DRV_TRACES: %d traces from the generated universe' % len(drv))
    # --- GATE xowned (A/AD1g.v:1243-1274 xowned_all): every ANum cell of Tfib_const_abs ++ Tfib_const_shadow lies in a
    # Tfib_owned_static range or in such a range's shadow. A cell that does not, in a READ-ONLY section, is a donor
    # program constant copied by address (fuzz_reply: cgif's sink-string bytes 0x20e63..0x20e67): it is
    # dropped and reported. A failing cell anywhere else refuses the run.
    owned = [(int(x, 16), int(eval(y))) for x, y in re.findall(r'\((0x[0-9a-f]+), ([^)]+)\)', grab('Tfib_owned_static'))]
    sha = lambda z: (z >> 3) + SHOFF
    covered = lambda z, w: (any(lo <= z and z + w <= lo + n for lo, n in owned) or
                            any(sha(lo) <= z and z + w <= sha(lo) + (n + 7) // 8 for lo, n in owned))
    secs = [(sc['sh_addr'], sc['sh_addr'] + sc['sh_size'], sc['sh_flags'], sc.name) for sc in mem.e.iter_sections() if sc['sh_addr']]
    # read-only AT THE HAND-OFF: (a) a non-writable section, or (b) inside PT_GNU_RELRO AND outside the unit's writable
    # image window [rw_lo, rw_lo + rw_len) of its atable (AB12/YB12: the checker's model of what start-up left writable,
    # i.e. after the RELRO mprotect), with the plan's PMprotect node present when --plan is given. RELRO is read-only only
    # after that mprotect, so the ELF's PT_GNU_RELRO alone is not trusted (boxreg B's .got cells 0x99300/0x99318/0x99328).
    relro = [(sg['p_vaddr'], sg['p_vaddr'] + sg['p_memsz']) for sg in mem.e.iter_segments() if sg['p_type'] == 'PT_GNU_RELRO']
    rww = None
    if a.ab12:
        m_rw = re.search(r'rw_lo := (0x[0-9a-f]+); rw_len := (0x[0-9a-f]+)', open(a.ab12).read())
        if m_rw:
            rww = (int(m_rw.group(1), 16), int(m_rw.group(1), 16) + int(m_rw.group(2), 16))
    has_mprotect = (a.plan is None) or ('PMprotect' in open(a.plan).read())
    def ro(z):
        if any(lo <= z < hi and not (f & 1) for lo, hi, f, _ in secs):
            return True
        return bool(rww and has_mprotect and any(lo <= z < hi for lo, hi in relro) and not (rww[0] <= z < rww[1]))
    rep.append('read-only rule: non-writable sections, plus PT_GNU_RELRO %s outside the atable rw window %s%s' % (
        [tuple(map(hex, r)) for r in relro], tuple(map(hex, rww)) if rww else '(no --ab12: RELRO not counted)',
        '' if a.plan else ' (no --plan given: the PMprotect node was not checked)'))
    ch, craws, ctail = list_parts(grab('Tfib_const_abs'))
    rows = [r for r in craws if r.strip()]
    keep2, gone, refuse, outraw = [], [], [], []
    for raw in rows:
        c = parse_cell(raw)
        w, z, v = c
        if covered(z, max(1, w)):
            keep2.append(('%d' % w, '%#x' % z, '%#x' % v)); outraw.append(raw)
        elif ro(z):
            gone.append(len(outraw)); outraw.append(None)
        else:
            refuse.append('%#x' % z); outraw.append(raw)
    for k in cells:
        if not covered(k, 1):
            refuse.append('shadow %#x' % k)
    if refuse:
        sys.exit('af0m: REFUSED: %d cells outside Tfib_owned_static and its shadow, not read-only: %s' % (len(refuse), refuse[:8]))
    if gone:
        names = []
        for k in gone:
            src = next((outraw[q] for q in list(range(k - 1, -1, -1)) + list(range(k + 1, len(outraw))) if outraw[q] is not None
                        and q not in gone), None)
            names.append('%#x' % parse_cell(rows[k])[1])
            c = parse_cell(src)
            outraw[k] = '\nz%d (ANum %#x) %#x  ' % c
        txt = txt.replace(grab('Tfib_const_abs'), join_parts(ch, outraw, craws, ctail))
        rep.append('xowned gate: %d read-only cells no owned range covers (donor program constants) FILLED in place with a '
                   'duplicate of a neighbour, so no index moves: %s' % (len(gone), ', '.join(names)))
    # GATE index map: every base row the run kept is at the SAME index in the output, with the same address
    outcells = [parse_cell(r) for r in list_parts(grab('Tfib_const_abs'))[1] if r.strip()]
    moved = [(k, hex(adr), hex(outcells[k][1]) if k < len(outcells) else None) for k, adr in base_index
             if k >= len(outcells) or (outcells[k][1] != adr and k not in gone)]
    if moved:
        sys.exit('af0m: REFUSED: Tfib_const_abs index map changed for %d kept rows, first %s' % (len(moved), moved[:4]))
    rep.append('index gate: PASS (%d kept base rows at their base index; %d output rows)' % (len(base_index), len(outcells)))
    rep.append('xowned gate: PASS (%d const_abs cells, %d shadow cells, all inside Tfib_owned_static or its shadow)'
               % (len(keep2), len(cells)))
    # --- GATE file-backed cells: a cell whose bytes the states take from the IMAGE (KImg) must equal the pinned file
    # read afresh here (the pin gate above guarantees --image is the original; this re-reads it)
    raw = open(a.image, 'rb').read()
    e2 = ELFFile(open(a.image, 'rb'))
    loads = [(sg['p_vaddr'], sg['p_offset'], sg['p_filesz']) for sg in e2.iter_segments() if sg['p_type'] == 'PT_LOAD']
    def fbyte(z):
        for va, off, fs in loads:
            if va <= z < va + fs:
                return raw[off + z - va]
        return None
    nfile = 0
    for w, ad, v in keep2:
        z, wz, vv = int(ad, 16), int(w), int(v, 16)
        fb = [fbyte(z + i) for i in range(wz)]
        if None in fb:
            continue
        fv = sum(b << (8 * i) for i, b in enumerate(fb))
        if fv == vv:
            nfile += 1
    rep.append('file-backed cells equal to the pinned file: %d (the rest are start-up writes, read from the states)' % nfile)
    # --- GATE malloc_context_size (signature 14 of the toolchain check): the common_flags cell CF+36 is 30 in the originals and 1 in
    # the toolchain-N image. Refuse if any state shows anything but 30.
    if a.symbols:
        nmv = {}
        for l in nm_lines:
            p = l.split()
            if p:
                nmv.setdefault(p[-1], int(p[0], 16))
        for sym, off, w, want, gate in (('_ZN6__asanL19malloc_context_sizeE', 0, 4, 30, True), ('_ZN6__asanL11asan_initedE', 0, 1, 1, True),
                                        ('_ZN11__sanitizer21common_flags_dont_useE', 36, 4, 30, False)):
            if sym not in nmv:
                continue
            vals = stated(nmv[sym] + off, w)
            if gate and vals != {want}:
                sys.exit('af0m: REFUSED: %s (%#x) reads %s in the states, not %d' % (sym, nmv[sym] + off, sorted(vals, key=str), want))
            rep.append('%s: %s (%#x) = %s in all %d states' % ('symbol gate PASS' if gate else 'info', sym, nmv[sym] + off,
                                                               sorted(vals, key=str), nstates))
    lines = txt.split('\n')
    lines = [l for l in lines if not l.startswith('(* Read from: ')]
    last = max(i for i, l in enumerate(lines[:12]) if l.startswith('(*'))
    if a.modified:
        lines.insert(last + 1, '(* Modified by Theorem Labs, 2026-10: %s *)' % a.modified)
        last += 1
    if a.modified:
        lines.insert(last + 1, prov)
        if ro_pin_line:
            lines.insert(last + 2, ro_pin_line)
    txt = '\n'.join(lines)
    unread = sorted(set(table) - used)
    if unread:
        sys.exit('af0m: REFUSED: %d rows of %s were never read by this run (the extract must hold only the values read), '
                 'first %s' % (len(unread), a.values, ['%#x/%d' % k for k in unread[:6]]))
    rep.append('values gate: PASS (every one of the %d cells of %s read, none missing)' % (len(table), a.values))
    open(a.out, 'w').write(txt)
    rep.append('wrote %s' % a.out)
    print('\n'.join(rep))


if __name__ == '__main__':
    main()
