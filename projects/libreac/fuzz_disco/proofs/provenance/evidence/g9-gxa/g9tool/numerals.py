#!/usr/bin/env python3
"""Turn a port_addr_check predict TSV into the per-line numeral substitutions to apply, and judge each one.

MAPS rows carry the prediction (column `expected`).  Kept as fm wrote them:
  * KEY position: the address argument of `sym` (`@sym A_img 0x22e18`, `@CJR.sym RTA.A_img 0x21920`) or the key of a
    `KV key value` row: a key into the donor key space that disco's record (lib/CJ/RL/I/RecAsanVf{A,B}.v over
    IImg{A,B}) maps, not an address of this image;
  * BY_HAND KEEP rows (bounds the predictor keys to a symbol by position only);
  * anything the tool does not call MAPS (NON-ADDRESS: sizes, counts, masks, bounds; UNRESOLVED-SOURCE).
Every other MAPS row is applied only if the same-name rule (judge) accepts it; otherwise it is REFUSED and
assemble stops.  Substitutions apply to code only, never inside comments.
New version of the G9 tool's numerals.py of record (sha256 0a3bdd93f6be2a9f4e9ead847f5af37f04a1a71f981a62259f6e0e0696791e68;
the runs of record used 0d627686208d, which differs only in GLRN / GLRS key positions that change no shipped file): the
address checker directory, the images and P0's numeral table are environment variables (PAC_DIR; FM_IMAGE / FM_DEBUG,
A_IMAGE / A_DEBUG, Y_IMAGE / Y_DEBUG: each stripped image and its unstripped twin; P0_NUMERALS) instead of constants.
"""
import csv, os, re, sys, struct, subprocess, collections, functools
TOOLDIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLDIR)
import reloc

# ---- by-hand numerals: one row each (row holders: add a row here AND a line in USAGE.md) -----------------------------
# (fm path under lib/A without .v, fm value as written, disco-A value, disco-Y value, why)
#   KEEP: fm's literal stays on that target and its MAPS rows are not applied (a bound or size the predictor keyed to a
#         symbol by position only).  A value: every code occurrence of the fm value in that file takes it (a numeral the
#         predictor cannot key: NO-PREDICTION / UNRESOLVED).
KEEP = 'KEEP'
_ZSH = ("end of the first Tfib_zero_shadow row (fm lib/A/AF0m.v:644 (0x10000, 0x20d00 - 0x10000)); disco "
        "lib/A/AF0m.v:1394 and lib/Reusable/YF0m.v:1471 both start (0x10000, 0x20f98 - 0x10000); "
        "boxreg's 0x20cc0 is boxreg's own row")
BY_HAND = [
    ('FMsnprintfGvsni0', '0x140000', KEEP, KEEP,
     'a round bound over vsni_rodata (ro_low: r_hi <= 0x140000), not an address; the tool keys it to '
     '__sanitizer::useCounts+0xc3c0 by position only'),
    ('FMsnprintfMck', '0x200000', KEEP, KEEP,
     'a round bound over icpt_rodata (Hrange: start + size <= 0x200000), not an address; the tool keys it to '
     '__sanitizer::theDepot+0x7c3a8 by position only (A 0x207340, Y 0x207700)'),
    ('FMgxaSeamReady', '0x20d00', '0x20f98', '0x20f98', _ZSH),
    ('FMgxaSeamShadow', '0x20d00', '0x20f98', '0x20f98', _ZSH),
    ('FMpfArmPdCtl', '0x20fe0', KEEP, KEEP,
     'already a disco address (fm 0ddf65fd8cc): ctl_f is disco\'s own "%dx%d" (fuzz_disco.c:621), bytes 25 64 78 25 64 00 '
     'at 0x20fe0 in both disco images; fm.asan has other bytes there'),
]
TARGETS = ('disco-A', 'disco-Y')


def by_hand(path, val, target):
    """(disco value or KEEP, why) of the BY_HAND row for this numeral on this target, or None."""
    for p, v, a, y, why in BY_HAND:
        if (p, v) == (path, val) and target in TARGETS:
            return (a, y)[TARGETS.index(target)], why
    return None


def key_position(code_line, val):
    """True when `val` is a donor KEY on this code line: the argument of `sym`, the key of a `KV` row, or an argument
    of the relocation-record lookups `GLRN key key` / `GLRS key` (RT_IImgA_ok; P3's hand relocation keeps them)."""
    v = re.escape(val) + r'(?![0-9A-Za-z_])'
    return bool(re.search(r'\bsym\s+(?:[A-Za-z0-9_.\']+\s+)?' + v, code_line) or re.search(r'\bKV3?\s+' + v, code_line)
                or re.search(r'\bGLR[NS]\s+(?:(?:0x[0-9a-fA-F]+|\d+)\s+)?' + v, code_line))


def read_table(tsv):
    """(rows, raw bytes) of a predict table, read once."""
    with open(tsv, 'rb') as fh:
        raw = fh.read()
    return list(csv.DictReader(raw.decode().splitlines(), delimiter='\t')), raw


def literal(r):
    """(fm value, predicted value) as written in the file."""
    val, exp = r['src_value'], r['expected']
    if r['kind'] == 'dec':
        return str(int(val, 16)), str(int(exp, 16))
    return val, exp


# ---- the same-name rule --------------------------------------------------------------------------------------------
def _env(name):
    return os.environ.get(name) or sys.exit('numerals.py: set %s' % name)


PAC_DIR = os.environ.get('PAC_DIR', '')
_IMG_ENV = {'fm': 'FM', 'disco-A': 'A', 'disco-Y': 'Y'}    # key -> prefix of <P>_IMAGE (stripped) and <P>_DEBUG (twin)
OBJ_MAX = 4096          # an offset > 0 inside a data object maps only when the object is at most this size


@functools.lru_cache(maxsize=None)
def pac():
    sys.path.insert(0, PAC_DIR or _env('PAC_DIR'))
    import port_addr_check
    return port_addr_check


@functools.lru_cache(maxsize=None)
def image(key):
    """port_addr_check's view of an image: symbols from its .debug twin, sections, named bounds, xrefs."""
    return pac().Image(_env(_IMG_ENV[key] + '_IMAGE'), _env(_IMG_ENV[key] + '_DEBUG'), key)


@functools.lru_cache(maxsize=None)
def load_flags(key):
    from elftools.elf.elffile import ELFFile
    with open(_env(_IMG_ENV[key] + '_IMAGE'), 'rb') as fh:
        return [s['p_flags'] for s in ELFFile(fh).iter_segments() if s['p_type'] == 'PT_LOAD']


def _named(T, n):
    return T.byname.get(pac().norm_name(n), ())


def judge(target, v, t):
    """('MAP' | 'STOP', why) for a predicted pair fm v -> disco t.  MAP only when the donor resolution is a same-name
    symbol of the target: a function start or code offset in a same-name function, an object start, an offset inside a
    same-name object of <= 4 KiB, the end of a same-name symbol, a GOT slot that holds the same-name symbol, a named
    bound of the same name (segment index and flags, or section name), or a string whose bytes (with the NUL) are the
    same and that a same-name function references in the target."""
    P, S, T = pac(), image('fm'), image(target)
    s = S.covering(v)
    if s:                               # inside (or at the start of) a symbol: that symbol decides
        a, sz, ns, typ, _ = s
        off = v - a
        for n in ns:
            for ta, tsz in _named(T, n):
                if ta + off == t and (off == 0 or off < tsz):
                    if typ != 'STT_FUNC' and off and max(sz, tsz) > OBJ_MAX:
                        return 'STOP', ('offset %#x inside the %d-byte data object %s (> 4 KiB): a bound or a position, '
                                        'not an address' % (off, max(sz, tsz), P.pretty(n)))
                    return 'MAP', 'same-name %s %s+%#x' % ('function' if typ == 'STT_FUNC' else 'object', P.pretty(n), off)
        if not any(_named(T, n) for n in ns):
            return 'STOP', 'fm %s+%#x: the target image has no symbol of that name' % (P.pretty(ns[0]), off)
        return 'STOP', 'fm %s+%#x: the predicted %#x is not that symbol + %#x in the target' % (P.pretty(ns[0]), off, t, off)
    sc = S.sec(v)
    if sc and sc[0] == '.got':
        slot = v - (v - sc[1]) % 8
        p = S.q(slot)
        ps = S.covering(p) if p else None
        tslot = t - (v - slot)
        tsc = T.sec(tslot)
        if ps and tsc and tsc[0] == '.got' and (tslot - tsc[1]) % 8 == 0:
            pt = T.q(tslot)
            for n in ps[2]:
                if any(ta + (p - ps[0]) == pt for ta, _ in _named(T, n)):
                    return 'MAP', 'GOT slot of same-name %s+%#x' % (P.pretty(n), p - ps[0])
        return 'STOP', 'GOT slot %#x (fm pointee %s): the target slot %#x does not hold the same-name symbol' % (
            slot, P.pretty(ps[2][0]) + '+%#x' % (p - ps[0]) if ps else hex(p or 0), tslot)
    names = S.bd.get(v, ())
    for b in names:
        if T.bdname.get(b) != t:
            continue
        m = re.match(r'(?:seg|load)(\d+)\.', b)
        if m and load_flags('fm')[int(m.group(1))] != load_flags(target)[int(m.group(1))]:
            continue
        return 'MAP', 'named bound %s' % b
    e = S.covering(v - 1)
    if e and e[0] + e[1] == v:          # the exclusive end of a sized symbol
        for n in e[2]:
            if any(ta + tsz == t for ta, tsz in _named(T, n)):
                return 'MAP', 'end of same-name %s' % P.pretty(n)
        return 'STOP', 'end of fm %s: the predicted %#x is not the end of that symbol in the target' % (P.pretty(e[2][0]), t)
    if names:
        return 'STOP', 'bound %s: the target has no bound of that name at %#x' % ('/'.join(names), t)
    st = S.str_at(v)
    if st:
        s0, txt = st
        t0 = t - (v - s0)
        same = T.read(t0, len(txt) + 1) == txt.encode() + b'\0'
        fx = {r.rsplit('+', 1)[0] for r in S.xrefs().get(s0, set()) | S.xrefs().get(v, set())}
        tx = {r.rsplit('+', 1)[0] for r in T.xrefs().get(t0, set()) | T.xrefs().get(t, set())}
        if same and fx & tx:
            return 'MAP', 'string %r, referenced from same-name %s' % (txt[:40], sorted(fx & tx)[0])
        return 'STOP', 'string %r: %s' % (txt[:40], '(a) its bytes with the NUL differ at %#x' % t0 if not same else
                                           '(b) no xref to it from a same-name function in the target')
    return 'STOP', 'no same-name resolution (not in a symbol, not a GOT slot, named bound, symbol end or string)'


# ---- the substitutions -----------------------------------------------------------------------------------------------
def build(rows, srctext, path=None, target=None, rule=True):
    """(subs {line: [(old, new)]}, kept [(line, val, exp, why, how)]) for one file.  how: applied, propagated, hand,
    sym-key, kept-by-hand, same-value, refused (the same-name rule said STOP; the fm value stays)."""
    lines = reloc.code_text(srctext).split('\n')
    subs = collections.defaultdict(list)
    kept = []
    for p, val, a, y, why in BY_HAND:
        exp = by_hand(path, val, target)
        if p != path or exp is None or exp[0] == KEEP:
            continue
        for i, text in enumerate(lines, start=1):
            if reloc.numeral_re(val).search(text) and not key_position(text, val):
                subs[i].append((val, exp[0]))
                kept.append((i, val, exp[0], 'by hand: ' + why, 'hand'))
    verdicts = {}
    for r in rows:
        if r['verdict'] != 'MAPS' or not r['expected']:
            continue
        ln = int(r['src_line'])
        val, exp = literal(r)
        if r['kind'] == 'ident':          # a hex run inside an identifier (m2s_54d48_spec) is part of a name
            kept.append((ln, val, exp, 'identifier, a name: kept', 'ident'))
            continue
        hand = by_hand(path, val, target)
        if hand and hand[0] != KEEP:
            continue
        text = lines[ln - 1]
        if key_position(text, val):
            kept.append((ln, val, exp, r['src_res'], 'sym-key'))
            continue
        if hand:
            kept.append((ln, val, exp, 'NON-ADDRESS by hand: ' + hand[1], 'kept-by-hand'))
            continue
        if val == exp:
            kept.append((ln, val, exp, r['src_res'], 'same-value'))
            continue
        if rule:
            if (val, exp) not in verdicts:
                verdicts[(val, exp)] = judge(target, int(r['src_value'], 16), int(r['expected'], 16))
            how, why = verdicts[(val, exp)]
            if how == 'STOP':
                kept.append((ln, val, exp, 'REFUSED: ' + why, 'refused'))
                continue
        subs[ln].append((val, exp))
        kept.append((ln, val, exp, r['src_res'], 'applied'))
    # Every code occurrence of a numeral the tool applied takes the same value, also where the table has no MAPS row
    # for it (whole literals, not in comments, not in KEY position).
    mapping = {}
    for ln, pairs in subs.items():
        for val, exp in pairs:
            mapping[val] = exp
    for i, text in enumerate(lines, start=1):
        for val, exp in mapping.items():
            if reloc.numeral_re(val).search(text) and (val, exp) not in subs.get(i, []):
                if key_position(text, val):
                    kept.append((i, val, exp, 'sym-key occurrence', 'sym-key'))
                    continue
                subs[i].append((val, exp))
                kept.append((i, val, exp, 'same numeral, not reported by the tool', 'propagated'))
    return subs, kept


# ---- P0's numeral table (class (c) files; P0_NUMERALS: the extract of it with the columns read here) -------------------
@functools.lru_cache(maxsize=None)
def p0_rows():
    with open(_env('P0_NUMERALS')) as fh:
        body = [l for l in fh.read().split('\n') if l and not l.startswith('#')]
    out = collections.defaultdict(dict)
    for r in csv.DictReader(body, delimiter='\t'):
        out[r['file']][r['numeral']] = r
    return out


P0_REF = '3e35620c52e'                 # the fm text numerals.tsv describes


def p0_check(path, target, srctext, kept):
    """STOP lines: every substitution the tool makes must be P0's resolved disco value for that file and image; a
    numeral P0 left UNRESOLVED (decided DROP in g9/P0/numerals-rest.md) stops wherever it is in the code.  P0 describes
    fm 3e35620c52e: for a file whose text changed since (or is new), only the numerals P0 has a row for are compared."""
    rows = p0_rows().get('A/%s.v' % path)
    col = 'disco A' if target == 'disco-A' else 'disco Y'
    made = sorted({(k[1], k[2]) for k in kept if k[4] in ('applied', 'propagated', 'hand')})
    p0text = subprocess.run(['git', '-C', reloc.HUB, 'show', '%s:%s/A/%s.v' % (P0_REF, reloc.SRC_LIB, path)],
                            capture_output=True, text=True, env=dict(os.environ, GIT_NO_LAZY_FETCH='1')).stdout
    same_text = p0text == srctext
    if rows is None:
        return ['P0 numerals.tsv has no rows for A/%s.v (not a class (c) file) but the tool moves %s' % (
            path, ', '.join('%s -> %s' % p for p in made))] if made and same_text else []
    out = []
    for val, exp in made:
        r = rows.get(val)
        if r is None:
            if same_text:
                out.append('%s -> %s: P0 numerals.tsv has no row for %s' % (val, exp, val))
        elif r['status'] in ('UNRESOLVED', 'DROP'):
            out.append('%s -> %s: P0 status %s (%s)' % (val, exp, r['status'], r['how'][:120]))
        elif r['status'] == 'same':
            out.append('%s -> %s: P0 keeps %s (%s)' % (val, exp, val, r['kind']))
        elif int(r[col].split()[0], 0) != int(exp, 0):
            out.append('%s -> %s: P0 resolved %s to %s on %s' % (val, exp, val, r[col], target))
    code = reloc.code_text(srctext).split('\n')
    touched = {k[1] for k in kept if k[4] in ('applied', 'propagated', 'hand', 'refused', 'kept-by-hand')}
    for val, r in rows.items():
        at = [i for i, l in enumerate(code, 1) if reloc.numeral_re(val).search(l) and not key_position(l, val)]
        if not at:
            continue
        if r['status'] in ('UNRESOLVED', 'DROP'):
            out.append('%s at line %s: P0 status %s, decided DROP (g9/P0/numerals-rest.md): a hand removes it' % (
                val, ','.join(map(str, at)), r['status']))
        elif r['status'] == 'resolved' and int(r[col].split()[0], 0) != int(val, 0) and val not in touched:
            out.append('%s at line %s: P0 resolved it to %s on %s, the tool leaves it' % (
                val, ','.join(map(str, at)), r[col], target))
    return out


# ---- (start, N%nat) code ranges ----------------------------------------------------------------------------------------
RANGE = re.compile(r'\(\s*(0x[0-9a-fA-F]+)\s*,\s*(\d+)\s*%nat\s*\)')


def range_words(I, start, names):
    """Words (4 bytes) from `start` while the function covering each word has a name in `names`."""
    n, a = 0, start
    while True:
        s = I.covering(a)
        if not s or s[3] != 'STT_FUNC' or not {pac().norm_name(x) for x in s[2]} & names:
            return n
        n, a = n + 1, a + 4


def range_check(srctext, subs, kept, target):
    """STOP lines for code ranges `(start, N%nat)` whose word count differs on the target.  fm's N must first equal
    the measurement on fm.asan (words until the first function the range does not cover); only then is the target
    measured from the relocated start over the same-name functions."""
    S, T = image('fm'), image(target)
    out = []
    moved = {(ln, v): e for ln, pairs in subs.items() for v, e in pairs}
    same = {(k[0], k[1]) for k in kept if k[4] == 'same-value'}
    for i, text in enumerate(reloc.code_text(srctext).split('\n'), start=1):
        for m in RANGE.finditer(text):
            v, n = int(m.group(1), 16), int(m.group(2))
            if not S.in_exec(v):
                continue
            names = set()
            for a in range(v, v + 4 * n, 4):
                s = S.covering(a)
                if s:
                    names |= {pac().norm_name(x) for x in s[2]}
            if range_words(S, v, names) != n:
                continue                # fm's N is not "up to the next function": nothing to compare
            if (i, m.group(1)) in moved:
                t = int(moved[(i, m.group(1))], 16)
            elif (i, m.group(1)) in same:
                t = v
            else:
                continue                # the start itself stops elsewhere
            n2 = range_words(T, t, names)
            if n2 != n:
                out.append('line %d range (%s, %d%%nat): fm.asan measures %d words to the next function; %s from %#x '
                           'measures %d: a hand sets the count' % (i, m.group(1), n, n, target, t, n2))
    return out
