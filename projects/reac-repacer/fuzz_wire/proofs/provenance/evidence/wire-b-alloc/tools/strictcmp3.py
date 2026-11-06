#!/usr/bin/env python3
"""strictcmp3.py -- strictcmp2.py 16982e3ef42b (the one compare of cmpkit 4bbd3a74be89) with these changes
(strictcmp/lui/LUI.md): rule 8 (a lui-built absolute value is a target); rule 2 (compiler string labels: NAME-ONLY,
the unit owner's ruling); rule 3 (ESC counts as printable in the C-string rule, the unit owner's ruling); `cmp` prints the COMBINED
verdict (words and targets) with the word-only verdict in its own column, prints every differing target with a
`printed M of N` count, and refuses an FNLIST name that several functions carry (usage below). Everything else is
strictcmp2's.

Rule: every pc-relative target, and every lui-built absolute address (rule 8), is the same symbol+offset on both sides,
or (when NEITHER side has a symbol) the same bytes as defined below; never a NUL-cut of code or of a load, a jump-table
prefix or an 8-byte prefix. Changes against strictcmp.py 77daee258b95:
  1. a symbol on ONE side only is a difference with no content compare (strictcmp sent it to the string / jump-table /
     const fallbacks when the target was data);
  2. a name that several symbols carry in one image (e.g. musl's five `lock` objects) is qualified by its STT_FILE,
     `lock{atexit.c}+0x0`; a name the file does not make unique is a difference (strictcmp compared bare names);
     no naming path uses an STT_TLS symbol (its st_value is a TP offset, not an address). A COMPILER STRING LABEL
     (`.str`, `.str.N`, `.L.str`, `.L.str.N`, qualified or not) is TU-private numbering, not an identity: a target that
     names one on either side is equal iff BOTH sides name LOCAL compiler string labels in read-only data of the same
     STT_FILE, at the same offset from the label, with the same bytes over the read extent (a load's width; else up to
     and including the first NUL inside the object), whatever the label numbers; equal labels then give `name`, differing
     labels give `NAME-ONLY`, listed like an acceptance (fuzz_preset B: `.str.3{preset_file.c}` vs `.str.3`,
     both 32-byte objects holding LF, NUL). A program symbol on the other side, or different bytes / file / offset, is a
     difference (`names`, `strlabel-differs`), whatever the labels;
  3. two unnamed DATA targets: for a load, the bytes it reads (its width: all the instruction can observe); for a
     non-load target (an address taken by addi, a store), by DEFAULT the C-string rule (the pool owner's option B,
     the unit owner's ruling): if every byte before the first NUL is printable ASCII, tab, LF, CR or ESC (0x1b, the unit owner's ruling;
     strictcmp2 had no ESC), there is at least one such byte (an EMPTY string, first byte NUL, takes the full-region
     rule) and that NUL lies inside the target's region, the target is compared as that C string INCLUDING its NUL, and
     every such acceptance is listed (`cstr` in the fallback list; one `CSTR` row per acceptance from `cstr_rows`:
     function, pair, word offset, addr1, addr2, length, hex, repr) for the audit of its consumers; otherwise the full
     region: from the target to the next FUNC / OBJECT symbol or the end of its section. Same length on both sides,
     every byte FILE bytes (frd), and both targets in READ-ONLY data (a section without SHF_WRITE, or inside
     PT_GNU_RELRO): an unnamed target in writable data (.data, .bss) is a difference, because its initial bytes are not
     what a load reads at run time and two writable objects with equal initial bytes are still two objects.
     STRICT_LITERAL=1 in the environment (or LITERAL = True on the module) turns the C-string rule off: every non-load
     target then needs its full region (the criterion read literally);
  4. an unnamed CODE target is a difference (strictcmp: 32 raw bytes; raw bytes at two addresses do not fix a callee);
  5. a .got cell READ by an 8-byte load holds an address or a value. A held value inside a section is an address and is
     named (rule 2). A held value of 0 or outside every section is a VALUE: equal values are equal (in an image with
     PT_TLS, a value inside PT_TLS's size must also name the same STT_TLS symbol on both sides), different values are a
     difference — never named through Img.res / exact-address symbols (strictcmp named them, so an absolute symbol or an
     STT_TLS symbol could make two different values "equal"). A .got cell whose ADDRESS is taken (addi, a store) is a
     16-byte tls_index {module, offset - 0x800} (general-dynamic TLS): equal iff the module words are raw-equal and the
     two offsets name the same STT_TLS symbol+offset (a GD plant: strictcmp read only the module word, 1, and
     passed fake_stack_tls -> dtls). A load of another width compares the raw cell bytes;
  6. not measured = a difference: a target word on one side only; an auipc whose result no compared target consumes; an
     I/S-type word that is no compared target and whose base register was last written (in address order) by an
     auipc (a consumer the MUST dataflow does not bind, e.g. one in a jump-table case); every lui of a function that
     holds a 2-byte parcel (rule 8 does not follow registers through undecoded parcels);
  7. every content read is of FILE bytes only (frd: all n bytes inside one PT_LOAD's p_filesz), whatever Img.rd does past
     p_filesz (the kit's Img.rd zero-fills up to p_memsz); function bytes that are not file bytes are the verdict
     UNREADABLE;
  8. a lui-built ABSOLUTE value is a target (a plant: `lui t0,0x5f3; ld t1,0x750(t0)`, the same bytes in two
     images, reads __stack_chk_guard+0 in one and builtin_tls+0x1fac0 in the other; strictcmp2 compared the words raw).
     A forward MAY dataflow over the function's control-flow graph (bytecmp's successors) carries each lui's value V
     (imm << 12, sign-extended) to every word some path brings it to unchanged (`mv` copies it; any other write, a call
     for the caller-saved registers, an ecall for a0 / a1 ends it; a word only an indirect jump reaches starts with
     every value live at the function's indirect jumps). Each addi / addiw / load / store / jalr whose base register may
     hold V is a lui PAIR with value P = V + its 12-bit immediate (addiw: sign-extended from 32 bits), one pair per lui
     that reaches it. V itself is a target when no pair consumes the lui, or when V is read in any other way: an R-type
     / branch / other OP-IMM operand, a store's data, a0-a7 at a call, jr, ecall or tail call, a0 / a1 at a return. A
     lui target is an ADDRESS when it is MEMORY-FED (a load / store / jalr pair, an addi / addiw pair whose result may
     be the base of a load / store / jalr / AMO, or V used as an AMO address), or when on EITHER side its value lies in
     an allocated SECTION of that image AND the dataflow does not settle it as a constant. It is settled as a CONSTANT,
     `lui-const (dataflow)` - listed like an acceptance, no difference - when it is not memory-fed and EVERY use of its
     value in the function is a logical / shift / compare read: and / or / xor / sll / srl / sra / slt / sltu (R-type or
     OP-IMM, 32- and 64-bit) or a branch compare (the unit owner's ruling). An add / sub / mul / div operand, a store's data, a
     call argument, a return value, a memory base or any other read is not logical, so the value may be an address and
     the target is judged. A difference at a target that is in a section but NOT memory-fed is reported in its own class
     `lui-in-section`, with both values, both sections and the underlying kind, because such a row is settled only by
     showing by hand that the value is not used as an address. (the unit owner ruled, "inside any PT_LOAD"; the shipped
     test is the SECTION, that rule minus the bytes no section covers - the ELF header and inter-section padding -
     because those name no object in ANY image: under the PT_LOAD reading uci.asan's `main`, which builds 0x10000 =
     65536 with a lui, differs from ITSELF, both sides `(None) (unnamed, writable)`, and two C0 baselines of the plant
     suite break; the unit owner confirmed the section test. luiscan.py counts both, LUI.md measures both.) An address
     is compared under rules 1-5 and 7 exactly as a pc-relative target (a memory-fed address in no section names no
     image object: `writable-unnamed`, a difference). Any other lui value is a CONSTANT: bytecmp compares its words raw
     (a lui is never pc-relative there), so equal words are equal and different words are REAL. A lui target on one
     side only is a difference.
VERDICT (cmp's verdict column; closure_strict3's per-member verdict; `verdict()`): words AND targets. bytecmp's EQUAL /
EQUAL-mod-pcrel only when no target differs; a differing target gives DIFFERENT-target, a target only not measured
UNMEASURED-target (both differences; an acceptance is not a difference); bytecmp's DIFFERENT / UNMEASURED / SIZE /
SHAPE / UNREADABLE stay. The word-only verdict is the last column, `words-only` (tcmp still returns it as its first
value, as strictcmp2's tcmp did).
Kept: repin_check 9cbc3553c09e's `targets` (with the kit's bytecmp, below), the exact-address naming of strictcmp (size-0
`dlsym`), the .got cell replacement.
KIT SHAPE: strictcmp3 loads `drvcmp.py` from its own directory and uses only these names of it: Img (Img(path) with .e
(the ELFFile), .syms [(value, size, name, type)] sorted, .addrs, .secs [(name, addr, size)], .byname {name: [(value, size,
type)]}, .segs [(p_vaddr, p_filesz, bytes)], .sec(a) -> section name or None), _g['targets'] (base, bytes -> {word index:
(kind, target)}), _g['w_off'], _g['sx'], _bc['WRITES_RD'], _bc['CALLER_SAVED'], bc_words, bc_cmp, bc_states, sha. It
does not use Img.rd, Img.res, Img.tls, Img.fsym or a lax tcmp (the kit exports none): bytes come from frd, names from
qres / atname / tlsname below, PT_LOAD p_memsz from Img.e. Exposes Img, tcmp, _g, _bc, bc_words, bc_cmp, bc_states,
`tsame` (one target pair under these rules) for jtcheck, `lui_scan` (rule 8 over one function), `fcopies` (what an
FNLIST item names) and `verdict` for luiscan.py / closure_strict3.py. Read-only.
usage: [STRICT_LITERAL=1] strictcmp3.py cmp FNLIST TAG1=ELF1 ... PAIRS   (drvcmp.py cmp's columns, with verdict = the
       combined verdict; then the value / full-bytes / NAME-ONLY acceptances, the C-string acceptances, `printed M of N`
       differing targets (all of them are in the target-differ column), and words-only; then one CSTR row per C-string
       acceptance)
  FNLIST: comma-separated items, each NAME, NAME{FILE} (the local function of that STT_FILE, e.g.
  `_ZN6__asanL11MemToShadowEm{asan_fake_stack.cpp}`) or 0xADDR (the function symbol starting at that address in each
  image). An item that names several functions in any image of PAIRS (a NAME that several local functions carry) is
  REFUSED: every copy is listed on stderr (AMBIGUOUS, item, image tag, address, size, STT_FILE, the name{file} or address
  to give instead), nothing is compared, exit status 1 (strictcmp2 silently took the lowest address)."""
import sys, os, re, bisect, collections, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('drvcmp_kit', os.path.join(HERE, 'drvcmp.py'))
_dc = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(_dc)
Img, _g, _bc, bc_words, bc_cmp, bc_states, sha = _dc.Img, _dc._g, _dc._bc, _dc.bc_words, _dc.bc_cmp, _dc.bc_states, _dc.sha
targets, w_off = _g['targets'], _g['w_off']
LITERAL = os.environ.get('STRICT_LITERAL') == '1'
LO12 = (0x13, 0x03, 0x23, 0x67, 0x07, 0x27)
PRINTABLE = frozenset(range(32, 127)) | {9, 10, 13, 27}

def execsec(I, a):
    for s in I.e.iter_sections():
        if s['sh_addr'] and s['sh_addr'] <= a < s['sh_addr'] + s['sh_size']:
            return bool(s['sh_flags'] & 0x4)
    return False

def frd(I, a, n):
    """the n bytes at a only when all of them are FILE bytes of one PT_LOAD (never the loader's zero-fill); else None"""
    return next((d[a - v:a - v + n] for v, fz, d in I.segs if v <= a and a + n <= v + fz), None)

def readonly(I, a):
    """a lies in a section without SHF_WRITE or inside a PT_GNU_RELRO segment"""
    m = _meta(I)
    return any(v <= a < v + z for v, z in m['ro'])

def _meta(I):
    """per image, cached: STT_FILE of every local symbol, the names several addresses carry, STT_TLS symbols (offset 0
    included, which Img.syms drops), PT_TLS size, the sorted start addresses of FUNC / OBJECT symbols, read-only ranges,
    PT_LOAD ranges [p_vaddr, p_vaddr + p_memsz)"""
    m = getattr(I, '_sc3', None)
    if m is not None: return m
    cur = None; fil = {}; tls = []
    for y in I.e.get_section_by_name('.symtab').iter_symbols():
        t = y['st_info']['type']
        if t == 'STT_FILE': cur = y.name; continue
        if y.name and y['st_info']['bind'] == 'STB_LOCAL': fil[(y['st_value'], y.name)] = cur
        if t == 'STT_TLS' and y.name: tls.append((y['st_value'], y['st_size'], y.name))
    at = collections.defaultdict(set)
    for v, z, nm, ty in I.syms:
        if ty != 'STT_TLS': at[nm].add(v)
    dup = {nm for nm, s in at.items() if len(s) > 1}
    nf = collections.defaultdict(set)
    for v, z, nm, ty in I.syms:
        if nm in dup and ty != 'STT_TLS': nf[(nm, fil.get((v, nm)))].add(v)
    tseg = [g['p_memsz'] for g in I.e.iter_segments() if g['p_type'] == 'PT_TLS']
    starts = sorted({v for v, z, nm, ty in I.syms if ty in ('STT_FUNC', 'STT_OBJECT')})
    ro = [(s['sh_addr'], s['sh_size']) for s in I.e.iter_sections() if s['sh_addr'] and not s['sh_flags'] & 0x1]
    ro += [(g['p_vaddr'], g['p_memsz']) for g in I.e.iter_segments() if g['p_type'] == 'PT_GNU_RELRO']
    load = [(g['p_vaddr'], g['p_memsz']) for g in I.e.iter_segments() if g['p_type'] == 'PT_LOAD']
    m = I._sc3 = dict(fil=fil, dup=dup, nf=nf, tls=tls, tlsz=tseg[0] if tseg else None, starts=starts, ro=ro, load=load)
    return m

def qname(I, nm, v):
    """nm, or nm{file} when several symbols carry nm; None when the file does not make it unique"""
    m = _meta(I)
    if nm not in m['dup']: return nm
    f = m['fil'].get((v, nm))
    return None if f is None or len(m['nf'][(nm, f)]) > 1 else '%s{%s}' % (nm, f)

def inload(I, a):
    """a lies in a PT_LOAD [p_vaddr, p_vaddr + p_memsz) of I"""
    return any(v <= a < v + z for v, z in _meta(I)['load'])

def insec(I, a):
    """a lies in an allocated SECTION of I, i.e. it can name an object. A PT_LOAD byte in no section (the ELF header,
    inter-section padding) names nothing in any image: rule 8 leaves such a value a constant, so that an image compared
    with itself stays EQUAL (uci.asan `main` builds 0x10000 = 65536 with a lui; with the PT_LOAD test both sides read
    `(None) (unnamed, writable)` and the C0 baseline broke)"""
    return I.sec(a) is not None

def qres(I, a):
    """Img.res (the smallest FUNC / OBJECT symbol containing a, + offset; '(section)' if none) with qualified names and
    without STT_TLS; None when a name is ambiguous"""
    i = bisect.bisect_right(I.addrs, a); cont = []
    for j in range(i - 1, max(-1, i - 400), -1):
        v, z, nm, t = I.syms[j]
        if v <= a < v + z and t in ('STT_FUNC', 'STT_OBJECT'): cont.append((z, v, nm))
    if not cont: return '(%s)' % I.sec(a)
    z0 = min(c[0] for c in cont); v0 = [c[1] for c in cont if c[0] == z0][0]
    q = [qname(I, c[2], v0) for c in cont if c[0] == z0 and c[1] == v0]
    return None if None in q else '%s+%#x' % ('/'.join(sorted(set(q))), a - v0)

def atname(I, a):
    """the symbols exactly at a (any size; mapping symbols and STT_TLS dropped), qualified; None if none, '?' if
    ambiguous"""
    q = {qname(I, nm, v) for (v, z, nm, ty) in I.syms if v == a and not nm.startswith('$') and ty != 'STT_TLS'}
    return None if not q else '?' if None in q else '/'.join(sorted(q)) + '@exact'

def tlsname(I, off):
    """the STT_TLS symbol off is an offset into, as name+off@tls; None if the image has no PT_TLS or off is past it"""
    m = _meta(I)
    if m['tlsz'] is None or not 0 <= off < m['tlsz']: return None
    c = sorted((z, v, nm) for v, z, nm in m['tls'] if v <= off < v + max(z, 1))
    return '%s+%#x@tls' % (c[0][2], off - c[0][1]) if c else '(tls+%#x)' % off

def region(I, a):
    """the bytes from a to the next FUNC / OBJECT symbol start or the end of a's section; None if not all file-backed"""
    s = next(((v, z) for nm, v, z in I.secs if v <= a < v + z), None)
    if s is None: return None
    st = _meta(I)['starts']; k = bisect.bisect_right(st, a)
    end = min(s[0] + s[1], st[k]) if k < len(st) else s[0] + s[1]
    return frd(I, a, end - a)

def cstring(I, a):
    """the C string at a including its NUL, if every byte before the first NUL is printable and the NUL lies inside a's
    region; else None"""
    d = region(I, a)
    k = d.find(b'\0') if d else -1
    return d[:k + 1] if k > 0 and all(ch in PRINTABLE for ch in d[:k]) else None

STRLABEL = re.compile(r'\.(L\.)?str(\.\d+)?$')

def strlabel(I, a):
    """(STT_FILE, offset, object end) when the symbols qres names at a (else, the symbols exactly at a) are all LOCAL
    compiler string labels (`.str`, `.str.N`, `.L.str`, `.L.str.N`) of one known STT_FILE and a is read-only data; else
    None"""
    i = bisect.bisect_right(I.addrs, a); cont = []
    for j in range(i - 1, max(-1, i - 400), -1):
        v, z, nm, t = I.syms[j]
        if v <= a < v + z and t in ('STT_FUNC', 'STT_OBJECT'): cont.append((z, v, nm))
    if cont:
        z0 = min(c[0] for c in cont); v0 = [c[1] for c in cont if c[0] == z0][0]; end = v0 + z0
        names = {c[2] for c in cont if c[0] == z0 and c[1] == v0}
    else:
        v0 = a; names = {nm for v, z, nm, t in I.syms if v == a and not nm.startswith('$') and t != 'STT_TLS'}
        r = region(I, a); end = a + len(r) if r else a
    files = {_meta(I)['fil'].get((v0, nm)) for nm in names}
    if not names or not all(STRLABEL.match(nm) for nm in names) or len(files) != 1 or None in files or not readonly(I, a):
        return None
    return files.pop(), a - v0, end

def strextent(I, a, end, word):
    """the bytes a string-label target's consumer reads: a load's width; else up to and including the first NUL before
    the object's end (the whole rest of the object if it holds no NUL); None if not all file bytes"""
    wd = loadwidth(word)
    if wd: return frd(I, a, wd)
    d = frd(I, a, end - a) if end > a else None
    k = d.find(b'\0') if d else -1
    return d[:k + 1] if k >= 0 else d

def loadwidth(word):
    op, f3 = word & 0x7f, (word >> 12) & 7
    if op == 0x03: return {0: 1, 1: 2, 2: 4, 3: 8, 4: 1, 5: 2, 6: 4}.get(f3)
    if op == 0x07: return {1: 2, 2: 4, 3: 8, 4: 16}.get(f3)
    return None

TLS_DTV_OFFSET = 0x800      # RISC-V: a tls_index's offset word is the TP offset - 0x800

def tsame(Ia, xa, Ib, xb, word):
    """one target pair under rules 1-5 and 7 -> (ok, kind, ra, rb, info). ok kinds: name, NAME-ONLY, gotval, tlsindex,
    full, cstr. not-ok kinds: got-unreadable, got-value, got-tls, got-tls-index, ambiguous, names, strlabel-differs,
    unnamed-code, cstr-differs, data-differs"""
    if Ia.sec(xa) == Ib.sec(xb) == '.got':
        wd = loadwidth(word)
        if wd is None:
            # the cell's ADDRESS is taken (addi; a store): a 16-byte tls_index {module, offset - TLS_DTV_OFFSET}, as a
            # general-dynamic access passes to __tls_get_addr. Equal iff the module words are raw-equal and the offsets
            # name the same STT_TLS symbol+offset on both sides; anything else is a difference
            ca, cb = frd(Ia, xa, 16), frd(Ib, xb, 16)
            if ca is None or cb is None: return False, 'got-unreadable', hex(xa), hex(xb), None
            oa = (int.from_bytes(ca[8:], 'little') + TLS_DTV_OFFSET) & 0xffffffffffffffff
            ob = (int.from_bytes(cb[8:], 'little') + TLS_DTV_OFFSET) & 0xffffffffffffffff
            ga, gb = tlsname(Ia, oa), tlsname(Ib, ob)
            if ca[:8] != cb[:8] or ga is None or ga.startswith('(') or ga != gb:
                return False, 'got-tls-index', 'module %s %s' % (ca[:8].hex(), ga or hex(oa)), 'module %s %s' % (cb[:8].hex(), gb or hex(ob)), None
            return True, 'tlsindex', ga, gb, None
        if wd != 8:
            ca, cb = frd(Ia, xa, wd), frd(Ib, xb, wd)
            return (True, 'gotval', ca.hex(), cb.hex(), None) if ca is not None and ca == cb else \
                (False, 'got-value', ca and ca.hex(), cb and cb.hex(), None)
        ca, cb = frd(Ia, xa, 8), frd(Ib, xb, 8)
        if ca is None or cb is None: return False, 'got-unreadable', hex(xa), hex(xb), None
        va, vb = int.from_bytes(ca, 'little'), int.from_bytes(cb, 'little')
        aa, ab = va != 0 and Ia.sec(va) is not None, vb != 0 and Ib.sec(vb) is not None
        if not (aa and ab):
            if aa or ab or va != vb: return False, 'got-value', hex(va), hex(vb), None
            ga, gb = tlsname(Ia, va), tlsname(Ib, vb)
            if ga != gb: return False, 'got-tls', ga or hex(va), gb or hex(vb), None
            return True, 'gotval', ga or hex(va), gb or hex(vb), None
        xa, xb = va, vb
    ra, rb = qres(Ia, xa), qres(Ib, xb)
    if ra is not None and ra.startswith('('): ra = atname(Ia, xa) or ra
    if rb is not None and rb.startswith('('): rb = atname(Ib, xb) or rb
    la, lb = strlabel(Ia, xa), strlabel(Ib, xb)
    if la or lb:
        # rule 2: a compiler string label is TU-private numbering, not an identity: the same TU, the same offset and the
        # same bytes over the read extent, NUL included, whatever the label; a program symbol on the other side differs
        if not (la and lb): return False, 'names', ra or 'ambiguous name', rb or 'ambiguous name', None
        ea, eb = strextent(Ia, xa, la[2], word), strextent(Ib, xb, lb[2], word)
        if la[:2] != lb[:2] or ea is None or ea != eb:
            return False, 'strlabel-differs', ra or '?', rb or '?', ('TU %s|%s offset %#x|%#x' % (la[0], lb[0], la[1], lb[1]),
                                                                       (ea or b'')[:24], (eb or b'')[:24])
        return (True, 'name', ra, rb, None) if ra is not None and ra == rb else (True, 'NAME-ONLY', ra, rb, ea)
    if ra in (None, '?') or rb in (None, '?'):
        return False, 'ambiguous', ra or 'ambiguous name', rb or 'ambiguous name', None
    na, nb = not ra.startswith('('), not rb.startswith('(')
    if na or nb:
        return (True, 'name', ra, rb, None) if na and nb and ra == rb else (False, 'names', ra, rb, None)
    if execsec(Ia, xa) or execsec(Ib, xb):
        return False, 'unnamed-code', ra + ' (unnamed code)', rb + ' (unnamed code)', None
    if not (readonly(Ia, xa) and readonly(Ib, xb)):
        return False, 'writable-unnamed', ra + ' (unnamed, writable)', rb + ' (unnamed, writable)', None
    wd = loadwidth(word)
    if wd:
        da, db = frd(Ia, xa, wd), frd(Ib, xb, wd)
    else:
        sa, sb = (None, None) if LITERAL else (cstring(Ia, xa), cstring(Ib, xb))
        if sa is not None or sb is not None:
            return (True, 'cstr', ra, rb, sa) if sa == sb else (False, 'cstr-differs', ra, rb, (sa, sb))
        da, db = region(Ia, xa), region(Ib, xb)
    if da is not None and da == db: return True, 'full', ra, rb, len(da)
    return False, 'data-differs', ra, rb, ((da or b'')[:24], (db or b'')[:24])

def auipc_reg_words(w):
    """indices of I/S-type words whose base register was last written, in address order, by an auipc"""
    last = {}; out = set()
    WR, CS = _bc['WRITES_RD'], _bc['CALLER_SAVED']
    for k, (o, x, nb) in enumerate(w):
        if nb != 4: last.clear(); continue
        op = x & 0x7f; rd = (x >> 7) & 31; rs1 = (x >> 15) & 31
        if op in LO12 and rs1 and last.get(rs1, -1) >= 0: out.add(k)
        if op == 0x17: last[rd] = k
        elif op in WR or op == 0x2f or (op == 0x53 and ((x >> 27) & 31) in (0x14, 0x18, 0x1c)): last[rd] = -1
        if op in (0x6f, 0x67) and rd != 0:
            for r in CS: last[r] = -1
        if op == 0x73 and ((x >> 12) & 7) == 0: last[10] = last[11] = -1
    return out

LUI_MEM = (0x03, 0x07, 0x23, 0x27, 0x67)    # load, FP load, store, FP store, jalr: rs1 is a memory / jump base
ARGS = tuple(range(10, 18))                  # a0-a7: what a call or ecall takes, what a return or tail call leaves
M64 = (1 << 64) - 1

def _lo12(x):
    """the 12-bit immediate of an addi / addiw / load / FP load / store / FP store / jalr (rs1 + imm); else None"""
    op, f3 = x & 0x7f, (x >> 12) & 7
    if op in (0x23, 0x27): return _g['sx'](((x >> 25) << 5) | ((x >> 7) & 31), 12)
    if op in (0x03, 0x07, 0x67) or (op in (0x13, 0x1b) and f3 == 0): return _g['sx'](x >> 20, 12)
    return None

def _raw_reads(x):
    """the integer registers x reads other than as the base of an addi / addiw / load / store / jalr (x0 left out)"""
    op, f3 = x & 0x7f, (x >> 12) & 7; rs1, rs2 = (x >> 15) & 31, (x >> 20) & 31
    if op in (0x33, 0x3b, 0x63, 0x2f): r = (rs1, rs2)                    # R-type, branch, AMO (rs1: its address)
    elif op == 0x23: r = (rs2,)                                          # a store's data
    elif op in (0x13, 0x1b): r = () if f3 == 0 else (rs1,)               # OP-IMM other than addi / addiw
    elif op == 0x53: r = (rs1,) if (x >> 27) in (0x1a, 0x1e) else ()     # fcvt / fmv from an integer register
    elif op == 0x73: r = ARGS if f3 == 0 else (rs1,) if f3 in (1, 2, 3) else ()   # ecall / ebreak; csrrw / s / c
    else: r = ()
    return [q for q in r if q]

def _writes(x):
    """the integer register x writes (as auipc_reg_words / flow_states count it), else None"""
    op = x & 0x7f
    return (x >> 7) & 31 if op in _bc['WRITES_RD'] or (op == 0x53 and (x >> 27) in (0x14, 0x18, 0x1c)) else None

def _jal_off(x):
    return _g['sx'](((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11 | ((x >> 21) & 0x3ff) << 1, 21)

def _br_off(x):
    return _g['sx'](((x >> 31) & 1) << 12 | ((x >> 7) & 1) << 11 | ((x >> 25) & 0x3f) << 5 | ((x >> 8) & 0xf) << 1, 13)

def _succ(w):
    """the decoded successors of each word, as bytecmp's flow_states takes them: the next word; a jal's in-function target
    (and the next word only for a call); a branch's target and the next word; for a jalr only the next word of a call"""
    off = {o: i for i, (o, x, n) in enumerate(w)}; out = []
    for i, (o, x, n) in enumerate(w):
        op, rd = x & 0x7f, (x >> 7) & 31; nxt = [i + 1] if i + 1 < len(w) else []
        if n == 2: out.append(nxt)
        elif op == 0x6f: out.append([off[t] for t in (o + _jal_off(x),) if t in off] + (nxt if rd else []))
        elif op == 0x67: out.append(nxt if rd else [])
        elif op == 0x63: out.append([off[t] for t in (o + _br_off(x),) if t in off] + nxt)
        else: out.append(nxt)
    return out

def _isret(x):
    return x & 0x7f == 0x67 and (x >> 7) & 31 == 0 and (x >> 15) & 31 == 1 and x >> 20 == 0

def _logical(x):
    """x reads its register operands ONLY as a logical / shift / compare value, never as an address or a value that
    leaves the function: and / or / xor / sll / srl / sra / slt / sltu (R-type and OP-IMM, 32- and 64-bit) and a
    branch compare (the unit owner's ruling). add / sub / mul / div, a store's data, a call argument, a memory base and
    anything else are NOT logical: the value may be an address"""
    op, f3, f7 = x & 0x7f, (x >> 12) & 7, x >> 25
    if op in (0x33, 0x3b): return (f3, f7) in ((7, 0), (6, 0), (4, 0), (1, 0), (5, 0), (5, 0x20), (2, 0), (3, 0))
    if op in (0x13, 0x1b): return f3 != 0
    return op == 0x63

def lui_scan(b):
    """rule 8 over one function's bytes -> (tg, unm). tg {(word index, lui index): (kind, value, memory-fed, logical)}:
    kind 'lui' (an I-type pair: addi / addiw / load / jalr, keyed by the consumer), 'luis' (a store pair) or 'luiv' (the
    lui's own value, keyed (lui, lui)); value modulo 2**64; `logical` is True when EVERY use of that value in the
    function is a logical / shift / compare read (`_logical`), i.e. the dataflow settles it as a constant. unm: the lui
    indices of a function that holds a 2-byte parcel (its registers are not followed through undecoded parcels: not
    measured).
    The registers are followed by a forward MAY dataflow over the function's control-flow graph (bytecmp's successors):
    a lui's value reaches every word some path carries it to unchanged (`mv` = addi rd, rs, 0 copies it; any other write
    of the register, a call for the caller-saved registers, an ecall for a0 / a1 ends it); a word that no decoded edge
    reaches (a jump-table case) starts with every value live at the function's indirect jumps. So a consumer reached
    by several luis (two arms, a loop) has one pair per lui, and none is left unbound."""
    w = bc_words(b); sx = _g['sx']
    lui = [j for j, (o, x, n) in enumerate(w) if n == 4 and x & 0x7f == 0x37 and (x >> 7) & 31]
    if not lui: return {}, set()
    if any(n == 2 for o, x, n in w): return {}, set(lui)
    V = lambda j: sx(w[j][1] >> 12, 20) << 12
    succ = _succ(w); CS = _bc['CALLER_SAVED']

    def step(i, s):
        """the state after word i; values: ('L', j) lui j's value, ('P', k, j) the result of addi / addiw pair k of lui j"""
        o, x, n = w[i]; op = x & 0x7f; rd = (x >> 7) & 31; rs1 = (x >> 15) & 31; out = dict(s)
        if op == 0x37: out[rd] = frozenset({('L', i)})
        elif op == 0x13 and (x >> 12) & 7 == 0 and x >> 20 == 0 and rs1 in s: out[rd] = s[rs1]      # mv: a copy
        elif op in (0x13, 0x1b) and (x >> 12) & 7 == 0 and any(t[0] == 'L' for t in s.get(rs1, ())):
            out[rd] = frozenset(('P', i, t[1]) for t in s[rs1] if t[0] == 'L')
        elif _writes(x) is not None: out.pop(_writes(x), None)
        if op in (0x6f, 0x67) and rd:
            for r in CS: out.pop(r, None)
        if op == 0x73 and (x >> 12) & 7 == 0: out.pop(10, None); out.pop(11, None)
        out.pop(0, None)
        return out

    def join(a, c):
        return {r: a.get(r, frozenset()) | c.get(r, frozenset()) for r in a.keys() | c.keys()}
    ins = [None] * len(w); ins[0] = {}
    roots = sorted(set(range(1, len(w))) - {t for s in succ for t in s})
    jr = [i for i, (o, x, n) in enumerate(w) if x & 0x7f == 0x67 and (x >> 7) & 31 == 0 and not _isret(x)]
    work = [0]
    while True:
        while work:
            i = work.pop(); out = step(i, ins[i])
            for t in succ[i]:
                new = out if ins[t] is None else join(ins[t], out)
                if new != ins[t]: ins[t] = new; work.append(t)
        u = {}
        for i in jr:
            if ins[i] is not None: u = join(u, step(i, ins[i]))
        for t in roots:
            new = u if ins[t] is None else join(ins[t], u)
            if new != ins[t]: ins[t] = new; work.append(t)
        if not work: break
    tg = {}; paired = set(); raw = set(); amo = set(); memp = set(); uses = collections.defaultdict(set)
    for k, (o, x, n) in enumerate(w):
        s = ins[k]
        if s is None: continue
        op = x & 0x7f; rd = (x >> 7) & 31; rs1 = (x >> 15) & 31; imm = _lo12(x)
        mv = op == 0x13 and (x >> 12) & 7 == 0 and x >> 20 == 0
        if imm is not None and rs1 and not mv:
            for t in s.get(rs1, ()):
                if t[0] == 'L':
                    p = V(t[1]) + imm
                    if op == 0x1b: p = sx(p & 0xffffffff, 32)
                    tg[(k, t[1])] = ['luis' if op in (0x23, 0x27) else 'lui', p & M64, op in LUI_MEM]
                    paired.add(t[1])                         # forming a pair is not a USE of the lui's own value
                else:
                    uses[t].add(False)                       # an addi / load / store / jalr on a pair's result
                    if op in LUI_MEM: memp.add(t[1:])
        reads = _raw_reads(x)
        if _isret(x): reads += [10, 11]                      # a return leaves a0 / a1
        elif op == 0x67 or (op == 0x6f and (rd or not 0 <= o + _jal_off(x) < len(b))):
            reads += ARGS                                    # a call, a jr, a jal out of the function: a0-a7
        for r in reads:
            for t in s.get(r, ()):
                uses[t].add(_logical(x))
                if t[0] == 'L':
                    raw.add(t[1])
                    if op == 0x2f and r == rs1: amo.add(t[1])
                elif op == 0x2f and r == rs1:
                    memp.add(t[1:])
    for (k, j), e in tg.items():
        if (k, j) in memp: e[2] = True
        e.append(all(uses[('P', k, j)]))
    for j in lui:
        if j not in paired or j in raw: tg[(j, j)] = ['luiv', V(j) & M64, j in amo, all(uses[('L', j)])]
    return {k: tuple(v) for k, v in tg.items()}, set()

def tcmp(I, i1, a1, i2, a2, n, fb=None):
    b1 = frd(I[i1], a1, n); b2 = frd(I[i2], a2, n); diff = []; cnt = collections.Counter()
    if b1 is None or b2 is None:
        return 'UNREADABLE', None, (0, 0, 0), [('0x0', 'function bytes not all file-backed', '', 'unreadable', None)]
    v, c = bc_cmp(b1, b2)
    if c is None: return v, c, (0, 0, 0), diff      # SIZE / SHAPE: the words do not align, no target pass
    t1 = targets(a1, b1); t2 = targets(a2, b2); w1 = bc_words(b1); st1 = bc_states(w1); consumed = set()

    def judge(i, x1, x2):
        off = hex(w1[i][0])
        ok, kind, r1, r2, info = tsame(I[i1], x1, I[i2], x2, w1[i][1])
        if not ok: diff.append((off, r1, r2, kind, info)); return
        cnt[kind] += 1
        if fb is not None and kind != 'name':
            fb.append((kind, off, x1, x2, r1 if kind in ('gotval', 'tlsindex') else '%s|%s %r' % (r1, r2, info)
                       if kind == 'NAME-ONLY' else info))
    for i in sorted(set(t1) | set(t2)):
        if i not in t1 or i not in t2:
            diff.append((hex(w1[i][0]), 'target on one side only', '', 'one-side', None)); continue
        if t1[i][0] != 'jal': consumed.add(st1[i][(w1[i][1] >> 15) & 31])
        judge(i, t1[i][1], t2[i][1])
    for k, (o, x, nb) in enumerate(w1):
        if nb == 4 and x & 0x7f == 0x17 and k not in consumed:
            diff.append((hex(o), 'auipc result consumed by no compared target', '', 'unmeasured', None))
    for k in sorted(auipc_reg_words(w1) - set(t1)):
        diff.append((hex(w1[k][0]), 'I/S-type word on an auipc register, not a compared target', '', 'unmeasured', None))
    # rule 8: lui-built values. A value in a section of either image, or memory-fed, is an ADDRESS and is judged like a
    # pc-relative target; a value the dataflow proves is only read by logical / shift / compare words is a CONSTANT
    # (`lui-const (dataflow)`, listed, no difference); anything else is a constant bytecmp already compared raw
    l1, u1 = lui_scan(b1); l2, u2 = lui_scan(b2)
    for k, j in sorted(set(l1) | set(l2)):
        if (k, j) not in l1 or (k, j) not in l2:
            diff.append((hex(w1[k][0]), 'lui value on one side only', '', 'one-side', None)); continue
        (k1, x1, m1, g1), (k2, x2, m2, g2) = l1[(k, j)], l2[(k, j)]
        sec = insec(I[i1], x1) or insec(I[i2], x2)
        if not (m1 or m2 or sec): continue                  # outside every section and no memory use: a raw constant
        if not (m1 or m2) and g1 and g2:
            # in a section, but every use is logical / shift / compare: the dataflow settles it as a constant
            cnt['lui-const'] += 1
            if fb is not None:
                fb.append(('lui-const', hex(w1[k][0]), x1, x2, 'dataflow: %s | %s' % (I[i1].sec(x1), I[i2].sec(x2))))
            continue
        n0 = len(diff); judge(k, x1, x2)
        if len(diff) > n0 and not (m1 or m2):
            o, r1, r2, kind, info = diff[-1]
            diff[-1] = (o, r1, r2, 'lui-in-section', ('%#x in %s | %#x in %s' % (x1, I[i1].sec(x1), x2, I[i2].sec(x2)),
                                                      kind, info))
    for j in sorted(u1 | u2):
        diff.append((hex(w1[j][0]), 'lui in a function with 2-byte parcels (registers not followed)', '', 'unmeasured', None))
    return v, c, (cnt['full'], cnt['gotval'] + cnt['tlsindex'], cnt['cstr']), diff

def cstr_rows(fn, pair, fb):
    """one machine-readable row per C-string acceptance: CSTR fn pair word-offset addr1 addr2 length hex repr"""
    return ['CSTR\t%s\t%s\t%s\t%#x\t%#x\t%d\t%s\t%r' % (fn, pair, o, x1, x2, len(s), s.hex(), s)
            for k, o, x1, x2, s in fb if k == 'cstr']

def fb_text(fb, kinds=('gotval', 'tlsindex', 'full', 'NAME-ONLY', 'lui-const')):
    return ' '.join('%s+%s[%#x|%#x]=%s' % (k, o, x1, x2, s) for k, o, x1, x2, s in fb if k in kinds)

def verdict(v, diff):
    """the printed VERDICT, words AND targets: bytecmp's EQUAL / EQUAL-mod-pcrel only with no target difference; a
    differing target makes DIFFERENT-target, a target that is only not measured UNMEASURED-target (both differences; an
    acceptance - NAME-ONLY, C string, full bytes, value - is no difference); bytecmp's DIFFERENT, UNMEASURED, SIZE,
    SHAPE and UNREADABLE stay (UNMEASURED with a differing target: DIFFERENT-target)"""
    real = any(d[3] != 'unmeasured' for d in diff)
    if v in ('EQUAL', 'EQUAL-mod-pcrel') and diff: return 'DIFFERENT-target' if real else 'UNMEASURED-target'
    return 'DIFFERENT-target' if v == 'UNMEASURED' and real else v

def fcopies(I, f):
    """the sized FUNC symbols an FNLIST item names in I -> sorted [(addr, size, name)]: NAME every copy of that name,
    NAME{FILE} the local copy that qname names so, 0xADDR every FUNC symbol starting at that address"""
    if f.lower().startswith('0x'):
        a = int(f, 16)
        return sorted({(v, z, nm) for v, z, nm, t in I.syms if v == a and t == 'STT_FUNC' and z > 0})
    nm = f.split('{', 1)[0]
    c = sorted({(v, z, nm) for v, z, t in I.byname.get(nm, []) if t == 'STT_FUNC' and z > 0})
    return [e for e in c if qname(I, nm, e[0]) == f] if '{' in f else c

def cmp(fns, imgs, pairs):
    I = {k: Img(p) for k, p in imgs.items()}
    # an item that names several functions (different address or size) in an image is refused, never resolved to one copy
    # (strictcmp2 took the lowest address: `MemToShadow` = the asan_errors.cpp copy of five)
    got = {(f, k): fcopies(I[k], f) for f in fns for k in sorted({k for p in pairs for k in p})}
    amb = [(f, k, c) for (f, k), c in got.items() if len({(v, z) for v, z, nm in c}) > 1]
    for f, k, c in amb:
        for v, z, nm in c:
            sys.stderr.write('AMBIGUOUS\t%s\t%s\t%#x\tsize %d\tSTT_FILE %s\tgive %s or %#x\n'
                             % (f, k, v, z, _meta(I[k])['fil'].get((v, nm)), qname(I[k], nm, v) or '(no unique name)', v))
    if amb: raise SystemExit('strictcmp3.py: %d FNLIST item(s) name several functions; nothing compared' % len(amb))
    for k, p in imgs.items():
        print('# %s = %s sha256 %s' % (k, p, sha(p)[:12]))
    print('# C-string rule %s' % ('OFF (STRICT_LITERAL=1)' if LITERAL else 'ON (default)'))
    print('fn\tpair\taddr1\taddr2\tsize1\tsize2\tverdict\tpcrel\treal\tunmeasured\ttargets(full-bytes-eq,got-value-or-tls-index-eq,cstr-eq)'
          '\ttarget-differ\tvalue/full-bytes/NAME-ONLY acceptances\tC-string acceptances (also one CSTR row each)'
          '\tdiffering targets printed (in target-differ, this row)\twords-only')
    for f in fns:
        for k1, k2 in pairs:
            s1, s2 = [got[(f, k)][0][:2] if got[(f, k)] else None for k in (k1, k2)]
            if not s1 or not s2:
                print('%s\t%s:%s\t%s\t%s\t\t\tABSENT' % (f, k1, k2, s1 and hex(s1[0]), s2 and hex(s2[0]))); continue
            if s1[1] != s2[1]:
                print('%s\t%s:%s\t%#x\t%#x\t%d\t%d\tSIZE' % (f, k1, k2, s1[0], s2[0], s1[1], s2[1])); continue
            fb = []
            v, c, t3, diff = tcmp(I, k1, s1[0], k2, s2[0], s1[1], fb)
            print('%s\t%s:%s\t%#x\t%#x\t%d\t%d\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\tprinted %d of %d targets\t%s'
                  % (f, k1, k2, s1[0], s2[0], s1[1], s2[1], verdict(v, diff), c[0] if c else '', c[1] if c else '',
                     c[2] if c else '', t3, diff if diff else 0, fb_text(fb),
                     ' '.join('%s@%#x|%#x=%r' % (o, x1, x2, s) for k, o, x1, x2, s in fb if k == 'cstr'), len(diff), len(diff), v))
            for r in cstr_rows(f, '%s:%s' % (k1, k2), fb): print(r)

if __name__ == '__main__':
    fns = sys.argv[2].split(',')
    imgs = dict(x.split('=', 1) for x in sys.argv[3:-1])
    pairs = [tuple(x.split(':')) for x in sys.argv[-1].split(',')]
    cmp(fns, imgs, pairs)
