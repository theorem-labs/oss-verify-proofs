#!/usr/bin/env python3
"""strictcmp2.py -- strictcmp.py 77daee258b95 with the fixes of its review (REVIEW.md).

Rule: every pc-relative target is the same symbol+offset on both sides, or (when NEITHER side has a symbol) the same
bytes as defined below; never a NUL-cut of code or of a load, a jump-table prefix or an 8-byte prefix. Changes against
strictcmp.py 77daee258b95:
  1. a symbol on ONE side only is a difference with no content compare (strictcmp sent it to the string / jump-table /
     const fallbacks when the target was data);
  2. a name that several symbols carry in one image (e.g. musl's five `lock` objects) is qualified by its STT_FILE,
     `lock{atexit.c}+0x0`; a name the file does not make unique is a difference (strictcmp compared bare names);
     no naming path uses an STT_TLS symbol (its st_value is a TP offset, not an address);
  3. two unnamed DATA targets: for a load, the bytes it reads (its width: all the instruction can observe); for a
     non-load target (an address taken by addi, a store), by DEFAULT the C-string rule (the pool owner's option B,
     r-decbox 12:55Z): if every byte before the first NUL is printable ASCII (or tab / LF / CR) and that NUL lies inside
     the target's region, the target is compared as that C string INCLUDING its NUL, and every such acceptance is
     listed (`cstr` in the fallback list; one `CSTR` row per acceptance from `cstr_rows`: function, pair, word offset,
     addr1, addr2, length, hex, repr) for the audit of its consumers; otherwise the full region: from the target to the
     next FUNC / OBJECT symbol or the end of its section. Same length on both sides, every byte FILE bytes (frd), and
     both targets in READ-ONLY data (a section without SHF_WRITE, or inside PT_GNU_RELRO): an unnamed target in writable
     data (.data, .bss) is a difference, because its initial bytes are not what a load reads at run time and two writable
     objects with equal initial bytes are still two objects. STRICT_LITERAL=1 in the environment (or LITERAL = True on
     the module) turns the C-string rule off: every non-load target then needs its full region (the criterion read
     literally);
  4. an unnamed CODE target is a difference (strictcmp: 32 raw bytes; raw bytes at two addresses do not fix a callee);
  5. a .got cell READ by an 8-byte load holds an address or a value. A held value inside a section is an address and is
     named (rule 2). A held value of 0 or outside every section is a VALUE: equal values are equal (in an image with
     PT_TLS, a value inside PT_TLS's size must also name the same STT_TLS symbol on both sides), different values are a
     difference — never named through Img.res / exact-address symbols (strictcmp named them, so an absolute symbol or an
     STT_TLS symbol could make two different values "equal"). A .got cell whose ADDRESS is taken (addi, a store) is a
     16-byte tls_index {module, offset - 0x800} (general-dynamic TLS): equal iff the module words are raw-equal and the
     two offsets name the same STT_TLS symbol+offset (the GD plant: strictcmp read only the module word, 1, and
     passed fake_stack_tls -> dtls). A load of another width compares the raw cell bytes;
  6. not measured = a difference: a target word on one side only; an auipc whose result no compared target consumes; an
     I/S-type word that is no compared target and whose base register was last written (in address order) by an
     auipc (a consumer the MUST dataflow does not bind, e.g. one in a jump-table case);
  7. every content read is of FILE bytes only (frd: all n bytes inside one PT_LOAD's p_filesz), whatever Img.rd does past
     p_filesz (the kit's Img.rd zero-fills up to p_memsz); function bytes that are not file bytes are the verdict
     UNREADABLE.
Kept: repin_check 9cbc3553c09e's `targets` (with the kit's bytecmp, below), the exact-address naming of strictcmp (size-0
`dlsym`), the .got cell replacement.
KIT SHAPE: strictcmp2 loads `drvcmp.py` from its own directory and uses only these names of it: Img (Img(path) with .e
(the ELFFile), .syms [(value, size, name, type)] sorted, .addrs, .secs [(name, addr, size)], .byname {name: [(value, size,
type)]}, .segs [(p_vaddr, p_filesz, bytes)], .sec(a) -> section name or None, .fsym(name) -> (addr, size) or None),
_g['targets'] (base, bytes -> {word index: (kind, target)}), _g['w_off'], _g['sx'], _bc['WRITES_RD'],
_bc['CALLER_SAVED'], bc_words, bc_cmp, bc_states, sha. It does not use Img.rd, Img.res, Img.tls or a lax tcmp (the kit
exports none): bytes come from frd, names from qres / atname / tlsname below. Exposes Img, tcmp, _g, _bc, bc_words, bc_cmp,
bc_states, and `tsame` (one target pair under these rules) for jtcheck_strict2.py. Read-only.
usage: [STRICT_LITERAL=1] strictcmp2.py cmp FNLIST TAG1=ELF1 ... PAIRS   (same as drvcmp.py cmp; extra columns: the value
       / full-bytes acceptances, the C-string acceptances; then one CSTR row per C-string acceptance)"""
import sys, os, bisect, collections, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('drvcmp_kit', os.path.join(HERE, 'drvcmp.py'))
_dc = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(_dc)
Img, _g, _bc, bc_words, bc_cmp, bc_states, sha = _dc.Img, _dc._g, _dc._bc, _dc.bc_words, _dc.bc_cmp, _dc.bc_states, _dc.sha
targets, w_off = _g['targets'], _g['w_off']
LITERAL = os.environ.get('STRICT_LITERAL') == '1'
LO12 = (0x13, 0x03, 0x23, 0x67, 0x07, 0x27)
PRINTABLE = frozenset(range(32, 127)) | {9, 10, 13}

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
    included, which Img.syms drops), PT_TLS size, the sorted start addresses of FUNC / OBJECT symbols"""
    m = getattr(I, '_sc2', None)
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
    m = I._sc2 = dict(fil=fil, dup=dup, nf=nf, tls=tls, tlsz=tseg[0] if tseg else None, starts=starts, ro=ro)
    return m

def qname(I, nm, v):
    """nm, or nm{file} when several symbols carry nm; None when the file does not make it unique"""
    m = _meta(I)
    if nm not in m['dup']: return nm
    f = m['fil'].get((v, nm))
    return None if f is None or len(m['nf'][(nm, f)]) > 1 else '%s{%s}' % (nm, f)

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

def loadwidth(word):
    op, f3 = word & 0x7f, (word >> 12) & 7
    if op == 0x03: return {0: 1, 1: 2, 2: 4, 3: 8, 4: 1, 5: 2, 6: 4}.get(f3)
    if op == 0x07: return {1: 2, 2: 4, 3: 8, 4: 16}.get(f3)
    return None

TLS_DTV_OFFSET = 0x800      # RISC-V: a tls_index's offset word is the TP offset - 0x800

def tsame(Ia, xa, Ib, xb, word):
    """one target pair under rules 1-5 and 7 -> (ok, kind, ra, rb, info). ok kinds: name, gotval, tlsindex, full, cstr.
    not-ok kinds: got-unreadable, got-value, got-tls, got-tls-index, ambiguous, names, unnamed-code, cstr-differs,
    data-differs"""
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

def tcmp(I, i1, a1, i2, a2, n, fb=None):
    b1 = frd(I[i1], a1, n); b2 = frd(I[i2], a2, n); diff = []; cnt = collections.Counter()
    if b1 is None or b2 is None:
        return 'UNREADABLE', None, (0, 0, 0), [('0x0', 'function bytes not all file-backed', '', 'unreadable', None)]
    v, c = bc_cmp(b1, b2)
    if c is None: return v, c, (0, 0, 0), diff      # SIZE / SHAPE: the words do not align, no target pass
    t1 = targets(a1, b1); t2 = targets(a2, b2); w1 = bc_words(b1); st1 = bc_states(w1); consumed = set()
    for i in sorted(set(t1) | set(t2)):
        off = hex(w1[i][0])
        if i not in t1 or i not in t2:
            diff.append((off, 'target on one side only', '', 'one-side', None)); continue
        x1, x2 = t1[i][1], t2[i][1]
        if t1[i][0] != 'jal': consumed.add(st1[i][(w1[i][1] >> 15) & 31])
        ok, kind, r1, r2, info = tsame(I[i1], x1, I[i2], x2, w1[i][1])
        if ok:
            cnt[kind] += 1
            if fb is not None and kind != 'name': fb.append((kind, off, x1, x2, r1 if kind in ('gotval', 'tlsindex') else info))
            continue
        diff.append((off, r1, r2, kind, info))
    for k, (o, x, nb) in enumerate(w1):
        if nb == 4 and x & 0x7f == 0x17 and k not in consumed:
            diff.append((hex(o), 'auipc result consumed by no compared target', '', 'unmeasured', None))
    for k in sorted(auipc_reg_words(w1) - set(t1)):
        diff.append((hex(w1[k][0]), 'I/S-type word on an auipc register, not a compared target', '', 'unmeasured', None))
    return v, c, (cnt['full'], cnt['gotval'] + cnt['tlsindex'], cnt['cstr']), diff

def cstr_rows(fn, pair, fb):
    """one machine-readable row per C-string acceptance: CSTR fn pair word-offset addr1 addr2 length hex repr"""
    return ['CSTR\t%s\t%s\t%s\t%#x\t%#x\t%d\t%s\t%r' % (fn, pair, o, x1, x2, len(s), s.hex(), s)
            for k, o, x1, x2, s in fb if k == 'cstr']

def fb_text(fb, kinds=('gotval', 'tlsindex', 'full')):
    return ' '.join('%s+%s[%#x|%#x]=%s' % (k, o, x1, x2, s) for k, o, x1, x2, s in fb if k in kinds)

def cmp(fns, imgs, pairs):
    I = {k: Img(p) for k, p in imgs.items()}
    for k, p in imgs.items():
        print('# %s = %s sha256 %s' % (k, p, sha(p)[:12]))
    print('# C-string rule %s' % ('OFF (STRICT_LITERAL=1)' if LITERAL else 'ON (default)'))
    print('fn\tpair\taddr1\taddr2\tsize1\tsize2\tverdict\tpcrel\treal\tunmeasured\ttargets(full-bytes-eq,got-value-or-tls-index-eq,cstr-eq)'
          '\ttarget-differ\tvalue/full-bytes acceptances\tC-string acceptances (also one CSTR row each)')
    for f in fns:
        for k1, k2 in pairs:
            s1, s2 = I[k1].fsym(f), I[k2].fsym(f)
            if not s1 or not s2:
                print('%s\t%s:%s\t%s\t%s\t\t\tABSENT' % (f, k1, k2, s1 and hex(s1[0]), s2 and hex(s2[0]))); continue
            if s1[1] != s2[1]:
                print('%s\t%s:%s\t%#x\t%#x\t%d\t%d\tSIZE' % (f, k1, k2, s1[0], s2[0], s1[1], s2[1])); continue
            fb = []
            v, c, t3, diff = tcmp(I, k1, s1[0], k2, s2[0], s1[1], fb)
            print('%s\t%s:%s\t%#x\t%#x\t%d\t%d\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s'
                  % (f, k1, k2, s1[0], s2[0], s1[1], s2[1], v, c[0] if c else '', c[1] if c else '',
                     c[2] if c else '', t3, diff if diff else 0, fb_text(fb),
                     ' '.join('%s@%#x|%#x=%r' % (o, x1, x2, s) for k, o, x1, x2, s in fb if k == 'cstr')))
            for r in cstr_rows(f, '%s:%s' % (k1, k2), fb): print(r)

if __name__ == '__main__':
    fns = sys.argv[2].split(',')
    imgs = dict(x.split('=', 1) for x in sys.argv[3:-1])
    pairs = [tuple(x.split(':')) for x in sys.argv[-1].split(',')]
    cmp(fns, imgs, pairs)
