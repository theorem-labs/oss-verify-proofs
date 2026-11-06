#!/usr/bin/env python3
"""SECHI-B.py [--control]: every section `_hi` cell (and its `_lo` partner) of libdiginet/fuzz_transport's image B
(asan-ubsan, pin 41113a03c82f) against the unstripped twin e217cb0a84f1's section headers. Extends
provenance/evidence/core-B/tfibcells-B.py (same name -> section rule, same lo / hi test) in five ways:
any prefix and either case (not only tfib_), record-field cells (`name := v;`), the trees read straight from git
refs, the padded / abuts test, and each cell's readers and writer.

Environment: HUB (a clone of the proofs repository holding the three refs below), TWIN and PIN (the unstripped twin
e217cb0a84f1 and the pin 41113a03c82f of fuzz_transport.asan-ubsan), OUT (the directory the outputs are written to;
default the current directory).

Trees (git refs in the hub HUB):
  core    2d48500794db (this core's branch, run of record r14): lib/B/**.v and lib/Reusable/**.v
  address a83315552115 (the image-B address-table branch, the run merged): lib/B/Prog/**.v (DgnTransportBAddr.v and kit)
          and lib/B/**.v, lib/Reusable/**.v again, to show the merge changed no cell
  donor   88154566652a (ossv/recipes): proofs/libreac/fuzz_decode/lib/{B,Reusable}/ (the released donor lib)

ENUMERATED: every parameterless cell of type Z whose name ends in _hi / _lo (any case), outside comments:
  `Definition|Notation|Let N [: Z] := V.` and record fields `N := V;` / `N := V |}`.
  Parameterised definitions (`N (x : T) ...`) and non-Z types are not cells; they are counted under EXCLUDED.
SECTION: name minus _hi/_lo, lowercased, split at '_'; the longest underscore suffix first; each joint '_' or '.';
  with a leading '.' and without (asan_globals has no dot). The first spelling that names an SHF_ALLOC section
  of the twin wins. No spelling: NO-SECTION. A numeral cell whose name ends in lo / hi without naming a section
  (TRANS_RLO / TRANS_RHI) is a section cell when its own comment (ending at most 3 lines above) says `X to the end
  of Y`: lo -> X, hi -> Y. A sweep lists every other numeral cell whose value is a section bound (the net).
VERDICT (a cell with a section):
  hi: value must be sh_addr + sh_size; lo: value must be sh_addr. Else FALSE.
  MATCH-ABUTS: right value, but some other ALLOC section STARTS at it (hi) / ENDS at it (lo): the alreloc defect
    (a _hi written as the next section's sh_addr) gives the same number, so the value proves nothing about the tool.
  MATCH-PADDED: right value and no other ALLOC section starts (hi) / ends (lo) there: real evidence.
READERS: `git grep -nw N` over lib/ at the cell's sha, minus the cell's own definition and minus other
  definitions of the same name (image A's twin cells); a hit under lib/A/ of an image-B cell reads image A's
  namesake and is listed with those; each other hit is split into code readers and comment mentions.
WRITER: donor text (the definition is byte-equal in the donor file) / port_core alreloc (a run-r14/fixed.tsv row
  wrote it over remap's value) / hand override (overrides-B.tsv) / port_core remap (a run-r14/check.tsv row
  moved it; no fixed row) / not relocated (file kept from the target or hand-written; git log -1 on the file).
COMMENTS: every comment block of B/YB1w.v (core), the two header lines of B/YB12.v (TFIB_TEXT_LO's file), every
  comment block of B/Prog/DgnTransportBAddr.v, and the header and the TRANS_RLO / TRANS_RHI blocks of
  B/Prog/DgnTransportBCg.v (address tree). A block covers a cell when it encloses or trails the cell's line, ends
  on the line above it, or names it. comment-image: which image it names (this image in the registered form 'the
  pinned fuzz_transport.asan-ubsan image (sha256 41113a03c82f)', by name only, or ANOTHER unit / sha);
  comment-numbers-ok: each 0x number against the covered cells' values and the twin's section / PT_LOAD headers
  (and the DgnTransportBCg.v header's global counts against TRANS_RO_GLOBALS). A proposed comment's numbers are
  read from the twin by this script, never copied; the script checks the proposal the same way. Outputs:
  SECHI-B.tsv (cells), SECHI-B.comments.tsv (comment blocks), B-sec-cells.patch (B/YB1w.v at 2d48500794db: comment
  fixes and the 0-reader FALSE-cell deletions, paths relative to lib/ as provenance/evidence/core-B/B-*.patch),
  B-addr-sec.diff (the lib/B/Prog kit at a83315552115: DgnTransportBAddr.v and DgnTransportBCg.v).
--control: the same classifier on planted cells (a _hi equal to the next section's sh_addr where sections are
  padded must show FALSE; the same planting where they abut must show MATCH-ABUTS) and exits non-zero on a miss.
"""
import os, re, subprocess, sys, textwrap
from collections import defaultdict
from elftools.elf.elffile import ELFFile

HUB = os.environ['HUB']
TWIN = os.environ['TWIN']
PIN = os.environ['PIN']
OUT = os.environ.get('OUT', '.')
CORE, INT, DONOR = '2d48500794db', 'a83315552115', '88154566652a'
U = 'proofs/libdiginet/fuzz_transport'
LIB = U + '/lib'
DLIB = 'proofs/libreac/fuzz_decode/lib'
EV = U + '/provenance/evidence/core-B'
SCOPE = [(CORE, LIB + '/B/'), (CORE, LIB + '/Reusable/'), (INT, LIB + '/B/Prog/')]
RECHECK = [(INT, LIB + '/B/'), (INT, LIB + '/Reusable/')]
OUT_TSV = os.path.join(OUT, 'SECHI-B.tsv')


def git(*a):
    return subprocess.run(['git', *a], cwd=HUB, capture_output=True, text=True, errors='replace').stdout


_blob = {}


def show(sha, path):
    k = (sha, path)
    if k not in _blob:
        r = subprocess.run(['git', 'show', '%s:%s' % k], cwd=HUB, capture_output=True, text=True, errors='replace')
        _blob[k] = r.stdout if r.returncode == 0 else None
    return _blob[k]


def ls(sha, prefix):
    return [p for p in git('ls-tree', '-r', '--name-only', sha, '--', prefix).split('\n') if p.endswith('.v')]


def blank_comments(t):
    """t with every Coq comment (nested) replaced by spaces, newlines kept: offsets and line numbers survive."""
    out, i, d, n = list(t), 0, 0, len(t)
    while i < n:
        if t.startswith('(*', i):
            d += 1; out[i] = out[i + 1] = ' '; i += 2; continue
        if d and t.startswith('*)', i):
            d -= 1; out[i] = out[i + 1] = ' '; i += 2; continue
        if d and t[i] != '\n':
            out[i] = ' '
        i += 1
    return ''.join(out)


def lineno(t, off):
    return t.count('\n', 0, off) + 1


_blank = {}


def blanked(sha, path):
    k = (sha, path)
    if k not in _blank:
        _blank[k] = blank_comments(show(sha, path) or '')
    return _blank[k]


# ---------------------------------------------------------------- sections
def sections(path):
    e = ELFFile(open(path, 'rb'))
    return {s.name: (s['sh_addr'], s['sh_size'], s['sh_type']) for s in e.iter_sections()
            if s.name and (s['sh_flags'] & 2)}


SEC = sections(TWIN)
SEC_PIN = sections(PIN)
STARTS = defaultdict(list)
ENDS = defaultdict(list)
for _n, (_a, _z, _t) in SEC.items():
    STARTS[_a].append(_n)
    ENDS[_a + _z].append(_n)
ORDER = sorted(SEC, key=lambda n: (SEC[n][0], SEC[n][0] + SEC[n][1]))


def neighbour(sec, side):
    i = ORDER.index(sec)
    if side == 'hi':
        return ORDER[i + 1] if i + 1 < len(ORDER) else None
    return ORDER[i - 1] if i > 0 else None


def spellings(parts):
    k = len(parts)
    for mask in range(1 << (k - 1)):          # mask 0: all dots first
        s = parts[0]
        for j in range(1, k):
            s += ('_' if mask >> (j - 1) & 1 else '.') + parts[j]
        yield s


def section_of(name):
    base = re.sub(r'_(hi|lo)$', '', name, flags=re.I).lower()
    parts = base.split('_')
    for i in range(len(parts)):
        for sp in spellings(parts[i:]):
            for c in ('.' + sp, sp):
                if c in SEC:
                    return c
    return None


# ---------------------------------------------------------------- enumeration
NUM = r'(?:0x[0-9a-fA-F]+|\d+)'
DEF = re.compile(r'(?<![\w.])(?:#\[[^\]]*\]\s*)?(?:Local\s+|Global\s+)?(Definition|Notation|Let)\s+(\w+_(?i:hi|lo))\b'
                 r'(\s*[^:=\s][^:=]*?)?\s*(?::\s*([^=]+?))?\s*:=\s*(.+?)\.(?=\s|$)', re.S)
FIELD = re.compile(r'(?<![\w.])(\w+_(?i:hi|lo))\s*:=\s*(' + NUM + r')(?:%Z)?\s*(?=[;|])')


def value_of(v, sha, path):
    v = v.strip()
    m = re.fullmatch(r'(' + NUM + r')(?:%Z)?(?:\s*\(only parsing\))?', v)
    if m:
        return int(m.group(1), 0)
    m = re.fullmatch(r'ltac:\(let v := eval vm_compute in (\w+) in exact v\)', v)
    if m:                                     # the B/YImgTop.v notations the unit's tfib_img_* read
        t = show(sha, LIB + '/B/YImgTop.v') or ''
        n = re.search(r'Notation\s+%s\s*:=\s*(%s)' % (m.group(1), NUM), t)
        if n:
            return int(n.group(1), 0)
    return None


def enumerate_cells(sha, prefix):
    cells, excluded = [], []
    for p in ls(sha, prefix):
        raw = show(sha, p)
        t = blanked(sha, p)
        seen = set()
        for m in DEF.finditer(t):
            kw, name, binders, ty, val = m.group(1), m.group(2), m.group(3), m.group(4), m.group(5)
            ln = lineno(t, m.start(2))
            seen.add((ln, name))
            if binders and binders.strip():
                excluded.append((p, ln, name, 'parameterised: ' + ' '.join(binders.split())[:40])); continue
            tys = (ty or '').strip()
            if tys and tys != 'Z':
                excluded.append((p, ln, name, 'type ' + tys)); continue
            if not tys and not re.fullmatch(NUM + r'(?:%Z)?(?:\s*\(only parsing\))?', val.strip()):
                excluded.append((p, ln, name, 'untyped non-numeral (%s alias)' % kw)); continue
            text = raw[m.start():m.end()].strip()
            cells.append(dict(sha=sha, path=p, line=ln, name=name, vtext=' '.join(val.split()),
                              value=value_of(val, sha, p), text=text, form=kw))
        for m in FIELD.finditer(t):
            ln = lineno(t, m.start(1))
            if (ln, m.group(1)) in seen:
                continue
            cells.append(dict(sha=sha, path=p, line=ln, name=m.group(1), vtext=m.group(2), value=int(m.group(2), 0),
                              text=raw[m.start():m.end()].strip(), form='field'))
    return cells, excluded


GEN = re.compile(r'(?<![\w.])(?:Definition|Notation)\s+(\w+)\s*(?::\s*Z\s*)?:=\s*(' + NUM + r')(?:%Z)?\s*'
                 r'(?:\(only parsing\)\s*)?\.(?=\s|$)')
GFIELD = re.compile(r'(?<![\w.])(\w+)\s*:=\s*(' + NUM + r')(?:%Z)?\s*(?=[;|])')


def bound_valued(sha, prefix, skip):
    """Every other parameterless numeral Z cell (any name) whose value is an ALLOC section's sh_addr or end:
    a section cell under another name would show here."""
    out = []
    for p in ls(sha, prefix):
        t = blanked(sha, p)
        for rx in (GEN, GFIELD):
            for m in rx.finditer(t):
                n, v = m.group(1), int(m.group(2), 0)
                if n in skip or not (STARTS.get(v) or ENDS.get(v)):
                    continue
                out.append((sha, p, lineno(t, m.start(1)), n, v,
                            ' '.join(['%s sh_addr' % s for s in STARTS.get(v, [])] +
                                     ['%s end' % s for s in ENDS.get(v, [])])))
    return sorted(set(out))


RANGE_CMT = re.compile(r'(\.[a-z][\w.]*[a-z]|asan_globals) to the end of (\.[a-z][\w.]*[a-z]|asan_globals)')


def comment_named_cells(sha, prefix, have):
    """Cells whose NAME names no section but whose own comment (the block ending at most 3 lines above) names a
    section range `X to the end of Y` (B/Prog/DgnTransportBCg.v TRANS_RLO / TRANS_RHI): lo -> X, hi -> Y.
    Only names ending in lo / hi (any case); the bound-valued sweep below is the net for anything else."""
    out = []
    for p in ls(sha, prefix):
        raw, t = show(sha, p), blanked(sha, p)
        blocks = comment_blocks(raw)
        for m in GEN.finditer(t):
            n = m.group(1)
            side = n[-2:].lower()
            if (p, n) in have or side not in ('lo', 'hi'):
                continue
            ln = lineno(t, m.start(1))
            for f, l, txt in blocks:
                r = RANGE_CMT.search(' '.join(txt.split()))
                if ln - 3 <= l < ln and r and r.group(1) in SEC and r.group(2) in SEC:
                    out.append(dict(sha=sha, path=p, line=ln, name=n, vtext=m.group(2), value=int(m.group(2), 0),
                                    text=raw[m.start():m.end()].strip(), form='Definition',
                                    secby=(r.group(1) if side == 'lo' else r.group(2), f)))
    return out


# ---------------------------------------------------------------- readers
def readers(sha, cells):
    names = sorted({c['name'] for c in cells})
    args = ['grep', '-nw']
    for n in names:
        args += ['-e', n]
    hits = defaultdict(list)
    for line in git(*args, sha, '--', LIB + '/').split('\n'):
        m = re.match(r'[0-9a-f]+:([^:]+):(\d+):(.*)', line)
        if not m:
            continue
        p, ln, txt = m.group(1), int(m.group(2)), m.group(3)
        for n in names:
            if re.search(r'(?<!\w)%s(?!\w)' % re.escape(n), txt):
                hits[n].append((p, ln))
    defs = defaultdict(set)                   # every definition site of a name in the tree: not a reader
    for p in {p for v in hits.values() for p, _ in v}:
        t = blanked(sha, p)
        for m in DEF.finditer(t):
            defs[m.group(2)].add((p, lineno(t, m.start(2))))
        for m in FIELD.finditer(t):
            defs[m.group(1)].add((p, lineno(t, m.start(1))))
        for m in re.finditer(r'(?m)^\s*(\w+_(?i:hi|lo))\s*:\s*Z\s*;', t):     # record field declarations
            defs[m.group(1)].add((p, lineno(t, m.start(1))))
    res = {}
    for n in names:
        code, cmt, other = [], [], []
        for p, ln in hits[n]:
            if (p, ln) in defs[n]:
                other.append((p, ln)); continue
            t = blanked(sha, p).split('\n')[ln - 1]
            (code if re.search(r'(?<!\w)%s(?!\w)' % re.escape(n), t) else cmt).append((p, ln))
        res[n] = (code, cmt, other)
    return res


# ---------------------------------------------------------------- writers
def tsv(sha, path):
    rows = []
    for l in (show(sha, path) or '').split('\n'):
        if l and not l.startswith('file\t'):
            rows.append(l.split('\t'))
    return rows


FIXED = tsv(CORE, EV + '/run-r14/fixed.tsv')
CHECK = tsv(CORE, EV + '/run-r14/check.tsv')
OVR = tsv(CORE, EV + '/overrides-B.tsv') + tsv(CORE, EV + '/run-r14/overrides.tsv')


def ival(s):
    try:
        return int(s, 0)
    except (ValueError, TypeError):
        return None


_off = {}


def stage_offset(rel, sha, path):
    """final line - stage line for a relocated file: the d in -3..3 under which most check.tsv rows of the file
    find their new value on final line (row line + d)."""
    if rel not in _off:
        lines = (show(sha, path) or '').split('\n')
        best, bd = 0, 0
        for d in range(-3, 4):
            k = 0
            for r in CHECK:
                if r[0] == rel and r[1].isdigit() and int(r[1]) > 0 and ival(r[3]) is not None:
                    i = int(r[1]) + d - 1
                    if 0 <= i < len(lines) and re.search(r'(?<![\w])%s(?![\w])' % re.escape(r[3]), lines[i]):
                        k += 1
            if k > best:
                best, bd = k, d
        _off[rel] = bd
    return _off[rel]


def donor_path(rel):
    return DLIB + '/' + rel if rel.startswith(('B/', 'Reusable/')) and not rel.startswith('B/Prog/') else None


def writer(c):
    rel = c['path'][len(LIB) + 1:]
    dp = donor_path(rel)
    dt = show(DONOR, dp) if dp else None
    dval = None
    if dt is not None:
        dtc = blank_comments(dt)
        m = re.search(r'(?<![\w.])%s\s*(?::\s*Z\s*)?:=\s*(%s)' % (re.escape(c['name']), NUM), dtc)
        dval = int(m.group(1), 0) if m else None
        if c['text'] in dt:
            k = dt.index(c['text'])
            return 'donor text (byte-equal %s:%s:%d)' % (DONOR, dp, lineno(dt, k)), dval
    if c['value'] is not None:
        d = stage_offset(rel, c['sha'], c['path'])
        sl = c['line'] - d
        v = c['value']
        fx = [r for r in FIXED if r[0] == rel and r[1] == str(sl) and ival(r[4]) == v
              and (dval is None or ival(r[2]) == dval)]
        ck = [r for r in CHECK if r[0] == rel and r[1] == str(sl) and ival(r[3]) == v
              and (dval is None or ival(r[2]) == dval)]
        ov = [r for r in OVR if r[0] == rel and r[1] == str(sl) and ival(r[3]) == v]
        lab = '; check.tsv says "%s" class %s' % (ck[0][4], ck[0][5]) if ck else ''
        if fx:
            r = fx[0]
            return ('port_core alreloc (run-r14/fixed.tsv %s:%s donor %s remap %s new %s new_sym %s%s)'
                    % (rel, r[1], r[2], r[3], r[4], r[5], lab)), dval
        if ov:
            return 'hand override (%s)' % ' | '.join('\t'.join(r) for r in ov), dval
        if ck:
            r = ck[0]
            return 'port_core remap (run-r14/check.tsv %s:%s %s -> %s "%s" class %s; no fixed.tsv row)' % (
                rel, r[1], r[2], r[3], r[4], r[5]), dval
    lg = git('log', '-1', '--format=%h %ad %s', '--date=short', c['sha'], '--', c['path']).strip()
    head = (show(c['sha'], c['path']) or '').split('\n')
    gen = next((h.strip()[:110] for h in head[:6] if 'Generated' in h), '')
    kept = 'donor file has no such definition' if dt is not None and dval is None else (
        'donor value %#x' % dval if dval is not None else 'no donor file (lib/B/Prog kit)' if dp is None else
        'no donor file')
    return 'not relocated (%s; %sgit log -1 %s)' % (kept, gen + '; ' if gen else '', lg), dval


# ---------------------------------------------------------------- classify
def classify(name, value, sec):
    side = 'hi' if name[-2:].lower() == 'hi' else 'lo'     # every cell name ends in hi / lo (TRANS_RHI too)
    if sec is None:
        return side, None, None, 'NO-SECTION', ''
    a, z, _ = SEC[sec]
    want = a + z if side == 'hi' else a
    if value is None:
        return side, a, a + z, 'UNEVALUATED', ''
    nb = neighbour(sec, side)
    nbs = '%s %s %#x' % (('next' if side == 'hi' else 'prev'), nb,
                         (SEC[nb][0] if side == 'hi' else SEC[nb][0] + SEC[nb][1])) if nb else \
        ('no next ALLOC section' if side == 'hi' else 'no prev ALLOC section')
    if value != want:
        tags = []
        if side == 'hi' and nb and value == SEC[nb][0]:
            tags.append('= next section %s sh_addr (the alreloc pattern)' % nb)
        tags += ['= %s sh_addr' % s for s in STARTS.get(value, []) if not (side == 'hi' and s == nb)]
        tags += ['= %s end' % s for s in ENDS.get(value, [])]
        return side, a, a + z, 'FALSE', nbs + '; value ' + ('; '.join(tags) or 'is no section bound')
    if side == 'hi':
        hit = [s for s in STARTS.get(value, []) if s != sec]
        return side, a, a + z, ('MATCH-ABUTS' if hit else 'MATCH-PADDED'), nbs + (
            '; %s starts at it: abuts, unproven by value' % '/'.join(hit) if hit else '; no section starts at it')
    hit = [s for s in ENDS.get(value, []) if s != sec]
    return side, a, a + z, ('MATCH-ABUTS' if hit else 'MATCH-PADDED'), nbs + (
        '; %s ends at it: abuts, unproven by value' % '/'.join(hit) if hit else '; no section ends at it')


def control():
    """Planted cells on the twin's own headers: the classifier must call each as stated."""
    plants = [
        ('ctl_text_hi', SEC['.tbss'][0], 'FALSE'),                          # .text pads to .tbss: next sh_addr
        ('ctl_asan_globals_hi', SEC['.bss'][0], 'FALSE'),                   # asan_globals pads to .bss
        ('ctl_tbss_hi', SEC['.init_array'][0], 'FALSE'),
        ('ctl_text_hi', SEC['.text'][0] + SEC['.text'][1], 'MATCH-PADDED'),
        ('ctl_init_array_hi', SEC['.fini_array'][0], 'MATCH-ABUTS'),        # abuts: next sh_addr is the end
        ('ctl_got_hi', SEC['.relro_padding'][0], 'MATCH-ABUTS'),
        ('ctl_data_rel_ro_lo', SEC['.data.rel.ro'][0], 'MATCH-ABUTS'),
        ('ctl_bss_lo', SEC['.bss'][0], 'MATCH-PADDED'),
        ('ctl_rodata_hi', SEC['.rodata'][0] + SEC['.rodata'][1] + 4, 'FALSE'),
        ('ctl_at_img_hi', 0x616000, 'NO-SECTION'),
    ]
    bad = 0
    for n, v, want in plants:
        s = section_of(n)
        got = classify(n, v, s)[3]
        ok = got == want
        bad += not ok
        print('CONTROL %-4s %-20s %#9x section %-14s %-12s (want %s)' % ('ok' if ok else 'MISS', n, v, s, got, want))
    print('CONTROL %s' % ('PASS' if not bad else 'FAIL %d' % bad))
    return bad

# ---------------------------------------------------------------- comments (Main 2026-10-31: comment-image,
# comment-numbers-ok, proposed comment; patch of comment fixes and 0-reader FALSE-cell deletions)
REG = 'the pinned fuzz_transport.asan-ubsan image (sha256 41113a03c82f)'
OUR_SHAS = ('41113a03c82f', 'e217cb0a84f1')
_LOADS = [p for p in ELFFile(open(TWIN, 'rb')).iter_segments() if p['p_type'] == 'PT_LOAD']
LOAD0 = _LOADS[0]['p_vaddr']
LOAD_END = max(p['p_vaddr'] + p['p_memsz'] for p in _LOADS)
IMG_TOP_N = (LOAD_END + 4095) // 4096 * 4096


def comment_blocks(text):
    """[(first_line, last_line, text)] of the top-level Coq comments of text."""
    out, i, d, start, n = [], 0, 0, 0, len(text)
    while i < n:
        if text.startswith('(*', i):
            if d == 0:
                start = i
            d += 1; i += 2; continue
        if d and text.startswith('*)', i):
            d -= 1; i += 2
            if d == 0:
                out.append((lineno(text, start), lineno(text, i - 1), text[start:i]))
            continue
        i += 1
    return out


def image_named(c):
    c = ' '.join(c.split())                   # a wrapped comment still states the registered form
    shas = re.findall(r'sha256 ([0-9a-f]{12,64})', c)
    other = sorted(set(re.findall(r'\b(fuzz_(?!transport\b)\w+(?:\.[\w-]+)?|cgif\w*|libreac/\w+)', c)))
    if re.match(r'\(\*\s*decode:', c):
        other.insert(0, "'decode:' tag (libreac/fuzz_decode's own note)")
    ours = 'fuzz_transport' in c
    oshas = [s for s in shas if s[:12] in OUR_SHAS]
    xshas = [s[:12] for s in shas if s[:12] not in OUR_SHAS]
    parts = []
    if REG in c:
        parts.append('this image, registered form')
    elif ours and oshas:
        parts.append('this image (sha256 %s)' % '/'.join(s[:12] for s in oshas))
    elif ours:
        parts.append('this image by name, no sha256')
    if other or xshas:
        parts.append('ANOTHER: ' + ', '.join(other + ['sha256 ' + s for s in xshas]))
    return '; '.join(parts) or 'none named'


def numbers_ok(c, cellvals):
    """every 0x number of the comment against the cells' values and the twin's section / PT_LOAD headers."""
    nums = [int(x, 16) for x in re.findall(r'0x[0-9a-fA-F]+', c)]
    if not nums:
        return 'n/a (no address in it)', True
    known = {}
    for n, (a, z, _) in SEC.items():
        known.setdefault(a, []).append('%s sh_addr' % n)
        known.setdefault(z, []).append('%s sh_size' % n)
        known.setdefault(a + z, []).append('%s end' % n)
    known.setdefault(LOAD0, []).append('PT_LOAD[0] p_vaddr')
    known.setdefault(LOAD_END, []).append('last PT_LOAD end')
    known.setdefault(IMG_TOP_N, []).append('last PT_LOAD end page-rounded (IMG_TOP)')
    res, ok = [], True
    for v in nums:
        w = (['cell value'] if v in cellvals else []) + known.get(v, [])
        ok &= bool(w)
        res.append('%#x=%s' % (v, '/'.join(w) if w else 'NO MATCH'))
    return ('ok: ' if ok else 'WRONG: ') + ', '.join(res), ok


def proposals():
    """(lib-relative path, first line) -> (old text, new text, why) for the comments found wrong; every number in a
    new text is read from the twin here, none is copied; each why is measured on the trees."""
    a, z, _ = SEC['.bss']
    assert a + z == LOAD_END, 'the last PT_LOAD does not end at .bss end'
    yb1w = show(CORE, LIB + '/B/YB1w.v')
    dyb1w = show(DONOR, DLIB + '/B/YB1w.v')
    addr = show(INT, LIB + '/B/Prog/DgnTransportBAddr.v')
    imgtop = show(CORE, LIB + '/B/YImgTop.v')
    reads = re.search(r'lib\.(\w+) Require Import YImgTop', yb1w).group(1)
    dreads = re.search(r'lib\.(\w+) Require Import YImgTop', dyb1w).group(1)
    nlo = int(re.search(r'Notation IMG_LO := (%s)' % NUM, imgtop).group(1), 0)
    ntop = int(re.search(r'Notation IMG_TOP := (%s)' % NUM, imgtop).group(1), 0)
    facts = ('YB1w.v reads lib.%s YImgTop (B/YImgTop.v: Notation IMG_LO %#x, IMG_TOP %#x; twin: PT_LOAD[0] p_vaddr '
             '%#x, last PT_LOAD end %#x page-rounded %#x: %s); the donor read lib.%s YImgTop'
             % (reads, nlo, ntop, LOAD0, LOAD_END, IMG_TOP_N,
                'EQUAL' if (nlo, ntop) == (LOAD0, IMG_TOP_N) else 'DIFFER', dreads))
    out = {}
    for f, l, old in comment_blocks(yb1w):
        donor = 'donor text, byte-equal in %s:%s/B/YB1w.v' % (DONOR, DLIB) if old in dyb1w else 'not donor text'
        if 'Reusable/YImgTop.v IMG_LO / IMG_TOP' in old and 'tfib_img_lo / tfib_img_hi' in old:
            out[('B/YB1w.v', f)] = (old, (
                "(* Modified by Theorem Labs, 2026-10: tfib_img_lo / tfib_img_hi are the numerals vm_compute gives for "
                "the unit's B/YImgTop.v IMG_LO / IMG_TOP (%#x / %#x for %s), as image A's A/AB1w.v does with "
                "Reusable/YImgTop.v (RELOC-GATES G17). *)") % (LOAD0, IMG_TOP_N, REG),
                "NOT PATCHED (a Modified-by notice line: the licence-lines tool owns it; Main 2026-10-31). Finding: "
                "names the donor's file Reusable/YImgTop.v; %s; %s" % (facts, donor))
        if re.match(r'\(\*\s*decode: YImgTop COMPUTES', old):
            out[('B/YB1w.v', f)] = (old, '\n'.join(textwrap.wrap((
                "(* B/YImgTop.v (written by port_core) states IMG_LO / IMG_TOP as numerals for %s: %#x, its first "
                "PT_LOAD p_vaddr, and %#x, the .bss end (sh_addr %#x + sh_size %#x = %#x) rounded up to a page; the "
                "body here is the numeral vm_compute gives for that notation (no numeral written), so the donor's "
                "`unfold ...; lia` proofs see a number. *)") % (REG, LOAD0, IMG_TOP_N, a, z, a + z),
                width=118, subsequent_indent='   ', break_long_words=False, break_on_hyphens=False)),
                "'decode:' is libreac/fuzz_decode's note; 'YImgTop COMPUTES' is false here (B/YImgTop.v states "
                "numerals); %s; %s" % (facts, donor))
    cg = show(INT, LIB + '/B/Prog/DgnTransportBCg.v')
    for f, l, old in comment_blocks(cg):
        r = RANGE_CMT.search(old)
        if old.startswith('(* The RELRO range: ') and r:
            s1, s2 = SEC[r.group(1)], SEC[r.group(2)]
            out[('B/Prog/DgnTransportBCg.v', f)] = (old, '\n'.join(textwrap.wrap(
                '(* The RELRO range of %s: %s (sh_addr %#x) to the end of %s (sh_addr %#x + sh_size %#x = %#x). *)'
                % (REG, r.group(1), s1[0], r.group(2), s2[0], s2[1], s2[0] + s2[1]), width=118,
                subsequent_indent='   ', break_long_words=False, break_on_hyphens=False)),
                'the cells\' own comment names no image and no number: registered form and the twin\'s section '
                'header numbers added; its section names are right (see the verdicts)')
        if old.startswith('(* DgnTransportBCg: the definitions every program statement of fuzz_transport.asan-ubsan '
                          '(lib/B/Prog/*_cg.v) shares.\n'):
            out[('B/Prog/DgnTransportBCg.v', f)] = (old, old.replace(
                '(* DgnTransportBCg: the definitions every program statement of fuzz_transport.asan-ubsan '
                '(lib/B/Prog/*_cg.v) shares.\n',
                '(* DgnTransportBCg: the definitions every program statement (lib/B/Prog/*_cg.v) of the pinned\n'
                '   fuzz_transport.asan-ubsan image (sha256 41113a03c82f) shares.\n', 1),
                'the file\'s image statement names this image by name only: registered form; '
                'hand-written kit (no generator)')
    for f, l, old in comment_blocks(addr):
        if old.startswith('(* The addresses fuzz_transport.asan-ubsan gives'):
            out[('B/Prog/DgnTransportBAddr.v', f)] = (old, old.replace(
                "The addresses fuzz_transport.asan-ubsan gives the listing's names, objects and auipc values.",
                "The addresses %s gives the listing's\n   names, objects and auipc values." % REG, 1),
                'names this image by name only (palist.py --img fuzz_transport.asan-ubsan; prog-gen/B/run.sh refuses '
                'any image but sha256 41113a03c82f): registered form only, no wrong fact')
    return out


def make_patch(sha, rel, props, deletions):
    """unified diff (paths relative to lib/, as provenance/evidence/core-B/B-*.patch) of rel at sha with the
    proposals replaced and the deletions (cell definition texts) removed."""
    import difflib
    old = show(sha, LIB + '/' + rel)
    new = old
    for (r, _), (o, n, _why) in sorted(props.items(), key=lambda kv: -kv[0][1]):
        if r == rel and not o.startswith('(* Modified by'):   # notice lines: the licence-lines tool's, not ours
            assert new.count(o) == 1, (rel, o[:60])
            new = new.replace(o, n, 1)
    lines = new.split('\n')
    for text in deletions:                    # a cell's `Definition ... .`; its line goes if nothing else is on it
        hit = [i for i, l in enumerate(lines) if text in l]
        assert len(hit) == 1, (rel, text)
        rest = lines[hit[0]].replace(text, '', 1)
        lines[hit[0]] = rest.strip()          # cells sit at column 0, two spaces between two on a line
        if not lines[hit[0]]:
            del lines[hit[0]]
    new = '\n'.join(lines)
    d = difflib.unified_diff(old.split('\n'), new.split('\n'), rel, rel, lineterm='', n=3)
    return '\n'.join(d) + '\n' if old != new else ''


def main():
    if '--control' in sys.argv:
        sys.exit(1 if control() else 0)
    pin_same = {k: v for k, v in SEC_PIN.items()} == {k: v for k, v in SEC.items()}
    print('twin %s (sha256 e217cb0a84f1); pin %s (41113a03c82f): ALLOC section headers %s'
          % (TWIN, PIN, 'IDENTICAL' if pin_same else 'DIFFER'))
    for n in ORDER:
        a, z, ty = SEC[n]
        print('  %-16s %-18s [%#9x, %#9x) size %#x' % (n, ty, a, a + z, z))
    cells, excl = [], []
    for sha, pre in SCOPE:
        c, e = enumerate_cells(sha, pre)
        cells += c
        excl += [(sha,) + x for x in e]
    have = {(c['path'], c['name']) for c in cells}
    for sha, pre in SCOPE:
        cells += comment_named_cells(sha, pre, have)
    # the merge (address tree) restates lib/B and lib/Reusable: each cell there must equal the core's
    core_key = {(c['path'], c['name']): c['value'] for c in cells if c['sha'] == CORE}
    drift = []
    for sha, pre in RECHECK:
        for c in enumerate_cells(sha, pre)[0]:
            if c['path'].startswith(LIB + '/B/Prog/'):
                continue                      # B/Prog is read from this tree in SCOPE already
            k = (c['path'], c['name'])
            if k not in core_key or core_key[k] != c['value']:
                drift.append('%s:%s:%d %s = %s (core: %s)' % (sha, c['path'], c['line'], c['name'], c['vtext'],
                                                              core_key.get(k, 'absent')))
            core_key.pop(k, None)
    drift += ['%s %s absent in %s' % (p, n, INT) for (p, n) in core_key]
    rd = {}
    for sha in (CORE, INT):
        rd[sha] = readers(sha, cells)
    rows = []
    for c in cells:
        sec = c['secby'][0] if c.get('secby') else section_of(c['name'])
        side, a, end, verdict, nbs = classify(c['name'], c['value'], sec)
        w, dval = writer(c)
        code, cmt, other = rd[c['sha']][c['name']]
        own = lambda x: x[0] == c['path'] and x[1] == c['line']
        # an image-B cell has no reader in lib/A/: a hit there reads image A's namesake (A/AB1w.v, A/Prog/...)
        alien = lambda x: c['path'].startswith(LIB + '/B/') and x[0].startswith(LIB + '/A/')
        other = [x for x in other + [y for y in code if alien(y)] if not own(x)]
        code = [x for x in code if not own(x) and not alien(x)]
        icode = [x for x in rd[INT][c['name']][0] if not own(x) and not alien(x)]
        rows.append(dict(c, sec=sec, side=side, a=a, end=end, verdict=verdict, nbs=nbs, writer=w, dval=dval,
                         code=code, cmt=cmt, other=other, icode=icode))
    # comments: each section cell, each lo/hi pair of YB1w.v and every cell of lib/B/Prog
    props = proposals()
    yb1w, addr = LIB + '/B/YB1w.v', LIB + '/B/Prog/DgnTransportBAddr.v'
    names = {r['name'] for r in rows}

    def lrel(p):
        return p[len(LIB) + 1:]

    def covers(sha, p, f, l, t):
        hits = set()
        for r in rows:
            if r['sha'] == sha and r['path'] == p and (f <= r['line'] <= l or r['line'] == l + 1 or
                                                        (r.get('secby') and r['secby'][1] == f) or
                                                        re.search(r'(?<!\w)%s(?!\w)' % re.escape(r['name']), t)):
                hits.add(r['name'])
        return sorted(hits)

    cmts = []                                 # every comment block checked
    cgp = LIB + '/B/Prog/DgnTransportBCg.v'
    for sha, p in ((CORE, yb1w), (CORE, LIB + '/B/YB12.v'), (INT, addr), (INT, cgp)):
        for f, l, t in comment_blocks(show(sha, p)):
            if p.endswith('YB12.v') and l > 2:
                continue                      # YB12.v: its two header lines are the comment of TFIB_TEXT_LO
            cov = covers(sha, p, f, l, t)
            if p == addr and 'auipc' in t:
                cov.append('transportb_hi (auipc table; parameterised, not a cell)')
            if p == cgp and not cov and f != 1:
                continue                      # DgnTransportBCg.v: the blocks about its section cells, and its header
            kind = 'cell/pair comment' if cov and not t.startswith(('(* Copyright', '(* SPDX')) else 'file notice'
            if kind != 'file notice' and t.startswith('(* Modified by'):
                kind += ' (Modified-by notice line)'
            if p.endswith('YB12.v'):
                kind, cov = 'file header of the cell', ['TFIB_TEXT_LO']
            vals = {r['value'] for r in rows if r['name'] in cov and r['value'] is not None}
            nmsg, nok = numbers_ok(t, vals)
            m = re.search(r"the image's (\d+) registered read-only globals \((\d+) in (\.[\w.]+), (\d+) in (\.[\w.]+)\)",
                          ' '.join(t.split()))
            if m:                             # the counts this header states, against TRANS_RO_GLOBALS on the twin
                ct = blanked(sha, p)
                lst_ = re.search(r'Definition TRANS_RO_GLOBALS[^=]*:=\s*\[(.*?)\]\.', ct, re.S).group(1)
                gn = re.findall(r'\((TRANS_\w+),', lst_)
                gv = {k: int(v, 0) for k, v in re.findall(r'Definition (TRANS_\w+) : Z := (%s)\.' % NUM, ct)}
                insec = lambda v, s: SEC[s][0] <= v < SEC[s][0] + SEC[s][1]
                c1 = sum(insec(gv[g], m.group(3)) for g in gn)
                c2 = sum(insec(gv[g], m.group(5)) for g in gn)
                good = (len(gn), c1, c2) == (int(m.group(1)), int(m.group(2)), int(m.group(4)))
                nok &= good
                nmsg += '; counts %s %s / %s %s / %s %s: TRANS_RO_GLOBALS has %d, %d in %s, %d in %s on the twin: %s' % (
                    m.group(1), 'globals', m.group(2), m.group(3), m.group(4), m.group(5), len(gn), c1, m.group(3), c2,
                    m.group(5), 'ok' if good else 'WRONG')
            pr = props.get((lrel(p), f))
            pchk = '-'
            if pr:
                pm, pok = numbers_ok(pr[1], vals)
                pchk = '%s; %s' % (image_named(pr[1]), pm)
            cmts.append(dict(sha=sha, path=p, f=f, l=l, text=t, kind=kind, cov=cov, img=image_named(t), nmsg=nmsg,
                             nok=nok, prop=pr[1] if pr else None, why=pr[2] if pr else '-', pchk=pchk))
    one = lambda s: ' '.join(x.strip() for x in s.split('\n'))
    for r in rows:
        r['c_img'] = r['c_num'] = r['c_prop'] = r['c_loc'] = '-'
        if not (r['sec'] or r['path'] == yb1w or r['path'].startswith(LIB + '/B/Prog/')):
            continue
        mine = [c for c in cmts if c['path'] == r['path'] and r['name'] in c['cov']]
        if not mine:
            r['c_loc'], r['c_img'], r['c_num'], r['c_prop'] = 'none', 'no comment on the cell', 'n/a', \
                '- (no comment: nothing to fix)'
            continue
        r['c_loc'] = ', '.join('%s:%d-%d (%s)' % (lrel(c['path']), c['f'], c['l'], c['kind']) for c in mine)
        r['c_img'] = ' | '.join(c['img'] for c in mine)
        r['c_num'] = ' | '.join(c['nmsg'] for c in mine)
        r['c_prop'] = ' | '.join(one(c['prop']) if c['prop'] else '- (keep)' for c in mine)
    with open(OUT_TSV.replace('.tsv', '.comments.tsv'), 'w') as f:
        f.write('\t'.join(['sha', 'file:lines', 'kind', 'cells covered', 'comment-image', 'comment-numbers-ok',
                           'finding', 'proposed comment', 'proposed: image / numbers', 'comment text']) + '\n')
        for c in cmts:
            f.write('\t'.join([c['sha'], '%s:%d-%d' % (lrel(c['path']), c['f'], c['l']), c['kind'],
                               ', '.join(c['cov']) or '-', c['img'], c['nmsg'], c['why'],
                               one(c['prop']) if c['prop'] else '-', c['pchk'], one(c['text'])[:400]]) + '\n')
    dels = [r['text'] for r in rows if r['verdict'] == 'FALSE' and r['path'] == yb1w
            and not [x for x in r['code']] and not [x for x in r['icode']]]
    pa = make_patch(CORE, 'B/YB1w.v', props, dels)
    pb = make_patch(INT, 'B/Prog/DgnTransportBAddr.v', props, []) + make_patch(INT, 'B/Prog/DgnTransportBCg.v',
                                                                                props, [])
    open(os.path.join(OUT, 'B-sec-cells.patch'), 'w').write(pa)
    open(os.path.join(OUT, 'B-addr-sec.diff'), 'w').write(pb)
    cc = [c for c in cmts if c['kind'] != 'file notice']
    print('COMMENTS: cell/pair comments checked %d; naming another image %d; wrong numbers %d; fixed (proposed) %d; '
          'file notices checked %d (naming another image %d); deletions in the patch %d' % (
              len(cc), sum('ANOTHER' in c['img'] for c in cc), sum(not c['nok'] for c in cc),
              sum(bool(c['prop']) for c in cc), len(cmts) - len(cc),
              sum('ANOTHER' in c['img'] for c in cmts if c['kind'] == 'file notice'), len(dels)))
    for c in cmts:
        print('  %s:%d-%d %-24s covers %s; image: %s; numbers: %s; %s' % (
            lrel(c['path']), c['f'], c['l'], c['kind'], ', '.join(c['cov']) or '-', c['img'], c['nmsg'],
            'PROPOSED (%s) -- %s' % (c['pchk'], c['why']) if c['prop'] else 'kept'))
    rel = lambda p: p[len(U) + 1:]
    hx = lambda v: '-' if v is None else '%#x' % v

    def lst(r, k, cap=20):                    # every reader of a section cell; the first 20 of a NO-SECTION cell
        xs = ['%s:%d' % (rel(p), l) for p, l in r[k]]
        if not r['sec'] and len(xs) > cap:
            xs = xs[:cap] + ['... (+%d more)' % (len(xs) - cap)]
        return ', '.join(xs) or '-'

    with open(OUT_TSV, 'w') as f:
        f.write('\t'.join(['cell', 'side', 'sha', 'file:line', 'value', 'section', 'sh_addr', 'sh_addr+sh_size',
                           'want', 'verdict', 'neighbour (padding evidence)', 'readers_n',
                           'readers (code, lib/ at the cell sha)', 'readers_n_at_a833', 'comment_mentions',
                           'same-name defs elsewhere', 'writer', 'donor_value', 'comment location', 'comment-image',
                           'comment-numbers-ok', 'proposed comment', 'definition']) + '\n')
        for r in rows:
            want = None if r['a'] is None else (r['end'] if r['side'] == 'hi' else r['a'])
            f.write('\t'.join([
                r['name'], r['side'], r['sha'], '%s:%d' % (rel(r['path']), r['line']),
                hx(r['value']) if r['value'] is not None else r['vtext'],
                (r['sec'] + (' (named by the comment at line %d)' % r['secby'][1] if r.get('secby') else ''))
                if r['sec'] else '-', hx(r['a']), hx(r['end']),
                hx(want), r['verdict'], r['nbs'] or '-', str(len(r['code'])),
                lst(r, 'code'), str(len(r['icode'])), lst(r, 'cmt'), lst(r, 'other'),
                r['writer'], hx(r['dval']), r['c_loc'], r['c_img'], r['c_num'], r['c_prop'],
                r['text'].replace('\t', ' ').replace('\n', ' ')]) + '\n')
    sec_rows = [r for r in rows if r['sec']]
    his = [r for r in sec_rows if r['side'] == 'hi']
    false = [r for r in sec_rows if r['verdict'] == 'FALSE']
    abut = [r for r in sec_rows if r['verdict'] == 'MATCH-ABUTS']
    padd = [r for r in sec_rows if r['verdict'] == 'MATCH-PADDED']
    unev = [r for r in sec_rows if r['verdict'] == 'UNEVALUATED']
    dele = [r for r in false if not r['code'] and not r['icode']]
    print('scope: %s' % '; '.join('%s %s' % (s, p[len(U) + 1:]) for s, p in SCOPE))
    print('ENUMERATED %d (_hi/_lo Z cells)  SECTION %d (hi %d, lo %d)  NO-SECTION %d  EXCLUDED %d (not Z cells)'
          % (len(rows), len(sec_rows), len(his), len(sec_rows) - len(his), len(rows) - len(sec_rows), len(excl)))
    print('CHECKED %d  FALSE %d (hi %d)  MATCH-ABUTS %d (hi %d)  MATCH-PADDED %d (hi %d)  UNEVALUATED %d  '
          'TO-DELETE %d  valid=%s' % (
              len(sec_rows), len(false), sum(r['side'] == 'hi' for r in false), len(abut),
              sum(r['side'] == 'hi' for r in abut), len(padd), sum(r['side'] == 'hi' for r in padd), len(unev),
              len(dele), len(sec_rows) == len(false) + len(abut) + len(padd) + len(unev)))
    print('merge drift (%s lib/B, lib/Reusable vs %s): %s' % (INT, CORE, '; '.join(drift) or 'none'))
    for r in sorted(sec_rows, key=lambda r: (r['path'], r['line'], r['side'] == 'hi')):
        print('  %-12s %-24s %s:%d = %s; %s %s = %s; %s; readers %d (a833 %d); %s' % (
            r['verdict'], r['name'], rel(r['path']), r['line'], hx(r['value']), r['sec'],
            'end' if r['side'] == 'hi' else 'sh_addr', hx(r['end'] if r['side'] == 'hi' else r['a']), r['nbs'],
            len(r['code']), len(r['icode']), r['writer'][:140]))
    for r in false:
        print('  FALSE %s %s:%d readers: %s' % (r['name'], rel(r['path']), r['line'],
                                               ', '.join('%s:%d' % (rel(p), l) for p, l in r['code']) or 'none'))
    print('NO-SECTION cells:')
    for r in rows:
        if not r['sec']:
            print('  %-22s %s:%d = %s  (%s)' % (r['name'], rel(r['path']), r['line'],
                                               hx(r['value']) if r['value'] is not None else r['vtext'], r['form']))
    print('EXCLUDED (not parameterless Z cells):')
    for x in excl:
        print('  %s %s:%d %s  %s' % (x[0], rel(x[1]), x[2], x[3], x[4]))
    names = {c['name'] for c in cells}
    bv = []
    for sha, pre in SCOPE:
        bv += bound_valued(sha, pre, names)
    syms = defaultdict(set)
    st = ELFFile(open(TWIN, 'rb')).get_section_by_name('.symtab')
    for s in st.iter_symbols():
        if s.name and s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT', 'STT_NOTYPE', 'STT_SECTION', 'STT_TLS'):
            syms[s['st_value']].add(s.name)
    print('OTHER CELLS WHOSE VALUE IS A SECTION BOUND (not named _hi/_lo; %d; symbols at the value from the twin):'
          % len(bv))
    for sha, p, ln, n, v, what in bv:
        print('  %s %s:%d %s = %#x  (%s; symbols: %s)' % (sha, rel(p), ln, n, v, what,
                                                         ', '.join(sorted(syms.get(v, [])))[:120] or '-'))
    t = show(INT, LIB + '/B/Prog/DgnTransportBAddr.v') or ''
    m = re.search(r'Definition transportb_text : Z := (%s)\.' % NUM, t)
    if m:
        v = int(m.group(1), 0)
        print('ADDRESS FILE: DgnTransportBAddr.v defines no _hi/_lo cell (transportb_hi is the auipc table, a '
              'function of j); transportb_text = %#x: symbols %s; section bound: %s' % (
                  v, ', '.join(sorted(syms.get(v, []))) or '-',
                  ' '.join(['%s sh_addr' % s for s in STARTS.get(v, [])] + ['%s end' % s for s in ENDS.get(v, [])])
                  or 'none'))
    yb12 = show(CORE, LIB + '/B/YB12.v') or ''
    n = re.search(r'Definition TFIB_TEXT_N : nat := (\d+)\.', yb12)
    lo = re.search(r'Definition TFIB_TEXT_LO : Z := (%s)\.' % NUM, yb12)
    if n and lo:
        e = int(lo.group(1), 0) + 4 * int(n.group(1))
        print('YB12.v TFIB_TEXT_LO + 4 * TFIB_TEXT_N = %#x; .text end %#x: %s' % (
            e, SEC['.text'][0] + SEC['.text'][1], 'EQUAL' if e == SEC['.text'][0] + SEC['.text'][1] else 'DIFFER'))


if __name__ == '__main__':
    main()
