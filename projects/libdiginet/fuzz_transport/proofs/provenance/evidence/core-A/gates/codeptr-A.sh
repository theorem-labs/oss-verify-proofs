#!/bin/bash
# codeptr-A.sh WORK LIB OUT: gate (b) of the libdiginet/fuzz_transport image-A core relocation (pool row TCA). codeptr
# 12348302dfd2 of the start-up set 2026-10-30d, run only through its frozen-run.sh, over every staged image-A core file of
# a port_core run directory (WORK/stage-out/A/*.v), as libdiginet/fuzz_decode's image-A core gate of record codeptr-A.sh
# (sha256 a3d8d77e1550; internal record) did; only the pins, the names, the paths and the per-image values changed.
# codeptr takes no --month (the set's README gives --month only to the writers gen_ad2, gen_ad1k, hsform, universe, af0m).
# Runs:
#   donor           the donor's own text (stage/A) on the donor's own image, no stale check: the tool's baseline
#   plant           a copy of stage-out/A/AE3m.v whose STDOUT_BUFA is put back to the donor's value (stage/A/AE3m.v,
#                   0x5f81e0 = fuzz_grant's stdout buffer; in fuzz_transport.asan it lies inside the last PT_LOAD
#                   [0xa5d88, 0x6153d0), so only the stale check can catch it): must be a finding (STALE)
#   base            stage-out/A/*.v on fuzz_transport.asan, --stale-image fuzz_grant.asan, --stale-dir stage (each
#                   file's donor text)
#   roles           every occurrence, in every checked file, of each value codeptr-notaddr.tsv declares is measured
#                   (the image word at the paired pc, the decoded field, the kernel definition, the place in its
#                   sentence) -> records/codeptr-occurrences.tsv; plus the defect check of tfib_at_rw_lo / tfib_at_rw_len
#   declared        base with every value of codeptr-notaddr.tsv declared (--not-address VALUE=REASON)
#   plant-declared  all of stage-out/A with the plant, under the same declarations: the plant must still be a finding
# Arguments: WORK = the port_core run directory (stage/, stage-out/); LIB = the target lib the run used (its A/ is the
# image-A start-up layer: A/AF0m.v's TFIB_DEPOT is read; a stand-in in the dry run); OUT = the output root.
# Inputs (env, required; no host path is written here): TIMG = fuzz_transport's image dir (stripped/, unstripped/); PG = libreac's fuzz_grant image
# tree (bin/, unstripped/); DON = fuzz_grant's released lib, normalised (Reusable/* at the lib root); SET = the extracted
# tools/startup-set/2026-10-30d directory (default: OUT/tools/startup-set/2026-10-30d, extracted from the hub HUB at
# TOOLS_REF when absent; its SHA256SUMS must pass); NOTADDR = the declarations (default codeptr-notaddr.tsv beside this
# script).
# Output: OUT/work/codeptr/{donor,plant,base,roles,declared,plant-declared}.out (+ the plant copies, plant.diff),
# OUT/records/codeptr-occurrences.tsv, OUT/records/codeptr.txt.
# rule: proves no function (kind: measurement).
set -uo pipefail
[ $# -eq 3 ] || { echo "usage: codeptr-A.sh WORK LIB OUT" >&2; exit 2; }
WORK=$(readlink -f "$1") LIB=$(readlink -f "$2") OUT0=$(mkdir -p "$3" && readlink -f "$3")
OUT=$OUT0/work/codeptr REC=$OUT0/records
HUB=${HUB:-} TOOLS_REF=${TOOLS_REF:-91ef630666824d85906ae28a461aec2ae1e9653d}
TIMG=${TIMG:?set TIMG to the fuzz_transport image dir}
PG=${PG:?set PG to the fuzz_grant image tree}
DON=${DON:?set DON to the released fuzz_grant lib, normalised}
STARTUP=$LIB/A
SS=${SET:-$OUT0/tools/startup-set/2026-10-30d}
BUNDLE=startup-set-2026-10-30d.tsv
if [ ! -d "$SS" ] && [ -z "${SET:-}" ]; then
  mkdir -p "$OUT0/tools" && git -C "$HUB" archive "$TOOLS_REF" tools/startup-set/2026-10-30d | tar -x -C "$OUT0/tools" --strip-components=1 \
    || { echo "codeptr-A: cannot extract tools/startup-set/2026-10-30d from $HUB at $TOOLS_REF" >&2; exit 2; }
fi
SUMS=$(cd "$SS" && sha256sum -c SHA256SUMS 2>&1 | grep -c ': OK$'); SUMN=$(grep -c . "$SS/SHA256SUMS")
[ "$SUMS" = "$SUMN" ] || { echo "codeptr-A: $SS: SHA256SUMS $SUMS of $SUMN OK" >&2; exit 2; }
NOTADDR=${NOTADDR:-$(dirname "$(readlink -f "$0")")/codeptr-notaddr.tsv}
GB=$PG/bin/fuzz_grant/fuzz_grant.asan; GT=$PG/unstripped/fuzz_grant/fuzz_grant.asan
FB=$TIMG/stripped/fuzz_transport.asan; FT=$TIMG/unstripped/fuzz_transport.asan
CP=$SS/frozen/codeptr.py.frozen-12348302dfd2
for f in "$GB" "$GT" "$FB" "$FT" "$CP" "$NOTADDR" "$SS/$BUNDLE" "$WORK/stage-out/A/AE3m.v" "$WORK/stage/A/AE3m.v" "$STARTUP/AF0m.v"; do
  [ -f "$f" ] || { echo "codeptr-A: missing $f" >&2; exit 2; }
done
[ -d "$DON" ] || { echo "codeptr-A: DON is not a directory" >&2; exit 2; }
# the pins of record: the four images and the tool (the bundle must name the same codeptr)
PINS=""
for x in "$GB:c2c7559b29bd" "$GT:57c26f993615" "$FB:e89be137db17" "$FT:86efc3a80314" "$CP:12348302dfd2"; do
  f=${x%:*} want=${x##*:} got=$(sha256sum < "${x%:*}" | cut -c1-12)
  [ "$got" = "$want" ] || { echo "codeptr-A: $(basename "$f") is $got, not the pinned $want" >&2; exit 2; }
  PINS="$PINS $(basename "$(dirname "$(dirname "$f")")")/$(basename "$(dirname "$f")")/$(basename "$f") $got;"
done
[ "$(awk -F'\t' '$1 == "codeptr.py" {print $2}' "$SS/$BUNDLE")" = 12348302dfd2 ] || { echo "codeptr-A: $BUNDLE does not pin codeptr.py 12348302dfd2" >&2; exit 2; }
INSHA="stage-out/A $(cd "$WORK/stage-out/A" && sha256sum ./*.v | sha256sum | cut -c1-12) ($(ls "$WORK"/stage-out/A/*.v | wc -l) files);"
INSHA="$INSHA stage/A $(cd "$WORK/stage/A" && sha256sum ./*.v | sha256sum | cut -c1-12) ($(ls "$WORK"/stage/A/*.v | wc -l) files);"
INSHA="$INSHA LIB/A/AF0m.v $(sha256sum < "$STARTUP/AF0m.v" | cut -c1-12); $(basename "$NOTADDR") $(sha256sum < "$NOTADDR" | cut -c1-12)"
rm -rf "$OUT"; mkdir -p "$OUT/plant/A" "$OUT/plant-all/A" "$REC"
fr() { bash "$SS/frozen-run.sh" "$SS/$BUNDLE" codeptr.py "$@"; }
# the plant: the donor's own STDOUT_BUFA (stage/A/AE3m.v) written into the relocated file; exactly one line changes
RE='^Definition STDOUT_BUFA : Z := \(0x[0-9a-f]*\)\.$'
DV=$(sed -n "s/$RE/\1/p" "$WORK/stage/A/AE3m.v")
[ -n "$DV" ] || { echo "codeptr-A: no STDOUT_BUFA line in stage/A/AE3m.v" >&2; exit 2; }
plant() { sed "s/$RE/Definition STDOUT_BUFA : Z := $DV./" "$WORK/stage-out/A/AE3m.v" > "$1"; }
plant "$OUT/plant/A/AE3m.v"
diff "$WORK/stage-out/A/AE3m.v" "$OUT/plant/A/AE3m.v" > "$OUT/plant.diff"
[ "$(grep -c '^>' "$OUT/plant.diff")" = 1 ] || { echo "codeptr-A: the plant did not change exactly one line" >&2; exit 2; }
cp "$WORK"/stage-out/A/*.v "$OUT/plant-all/A/" && plant "$OUT/plant-all/A/AE3m.v"
NA=()
while IFS=$'\t' read -r v why; do case "$v" in ''|'#'*) continue;; esac; NA+=(--not-address "$v=$why"); done < "$NOTADDR"
STALE=(--stale-image "$GB" --stale-names "$GT" --stale-dir "$WORK/stage")
fr --image "$GB" --names "$GT" "$WORK"/stage/A/*.v > "$OUT/donor.out" 2>&1; echo "rc=$?" >> "$OUT/donor.out"
fr --image "$FB" --names "$FT" "${STALE[@]}" "$OUT/plant/A/AE3m.v" > "$OUT/plant.out" 2>&1; echo "rc=$?" >> "$OUT/plant.out"
fr --image "$FB" --names "$FT" "${STALE[@]}" "$WORK"/stage-out/A/*.v > "$OUT/base.out" 2>&1; echo "rc=$?" >> "$OUT/base.out"
python3 - "$WORK" "$FB" "$FT" "$CP" "$SS/pautrlen" "$NOTADDR" "$REC/codeptr-occurrences.tsv" "$DON" "$STARTUP" > "$OUT/roles.out" 2>&1 <<'PY'
import glob, os, re, sys
from importlib.machinery import SourceFileLoader
from elftools.elf.elffile import ELFFile
# argv: WORK IMAGE NAMES CODEPTR PAUTRLEN NOTADDR OUT_TSV DONOR_LIB [STARTUP_DIR]
WORK, IMAGE, NAMES, CODEPTR, PAUTR, NOTADDR, OUT, DON = sys.argv[1:9]
STARTUP = sys.argv[9] if len(sys.argv) > 9 and sys.argv[9] else None
sys.path.insert(0, PAUTR)
cp = SourceFileLoader('codeptr_frozen', CODEPTR).load_module()       # the literal rules of the gate itself

# ---- the image: words, the page-rounded top, symbols of the unstripped twin
E = ELFFile(open(IMAGE, 'rb'))
LOADS = [(s['p_vaddr'], s['p_vaddr'] + s['p_memsz'], s.data()) for s in E.iter_segments() if s['p_type'] == 'PT_LOAD']
IMG_END = max(b for _, b, _ in LOADS); IMG_TOP = -(-IMG_END // 4096) * 4096
def word(pc):
    for a, b, d in LOADS:
        if a <= pc and pc + 4 <= a + len(d):
            return int.from_bytes(d[pc - a:pc - a + 4], 'little')
    return None
SYMS = [(s['st_value'], s['st_size'], s.name) for s in ELFFile(open(NAMES, 'rb')).get_section_by_name('.symtab').iter_symbols()
        if s.name and s['st_value'] and s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT')]
def symat(v):
    c = [(a, n) for a, z, n in SYMS if a <= v < a + max(z, 1)]
    return '%s+%#x' % (max(c)[1], v - max(c)[0]) if c else 'no symbol'
def symaddr(n):
    c = {a for a, _, m in SYMS if m == n}
    return c.pop() if len(c) == 1 else None

def blank(t):                       # comments to blanks, newlines kept: codeptr drops comments, positions stay
    return re.sub(r'\(\*.*?\*\)', lambda m: re.sub(r'[^\n]', ' ', m.group(0)), t, flags=re.S)
SO = os.path.join(WORK, 'stage-out')
FILES = sorted(glob.glob(os.path.join(SO, 'A', '*.v')))
TXT = {f: blank(open(f).read()) for f in FILES}
RAW = {f: open(f).read() for f in FILES}
def rel(f): return os.path.relpath(f, SO)

def evalz(e):
    e = e.strip()
    while e.startswith('(') and e.endswith(')'):
        e = e[1:-1].strip()
    m = re.fullmatch(r'zcanon\s+(\d+)', e)                       # zcanon z = z mod 2^64
    if m: return int(m.group(1)) % 2 ** 64
    m = re.fullmatch(r'page_round_up_Z\s+(\d+)', e)
    if m: return -(-int(m.group(1)) // 4096) * 4096
    if e.startswith('0x') and re.fullmatch(r'0x[0-9a-fA-F]+', e): return int(e, 16)
    if re.fullmatch(r'[\d\s+\-*/^()]+', e):
        try: return eval(re.sub(r'\^', '**', re.sub(r'(?<!/)/(?!/)', '//', e)))
        except Exception: return None
    return None
KD = {}                             # kernel / file definitions NAME : Z|nat := EXPR, from the run's own text
for p in glob.glob(os.path.join(SO, 'Reusable', '*.v')) + FILES:
    for m in re.finditer(r'Definition (\w+) : (?:Z|nat) := ([^.]+?)(?:%nat)?\.\s', blank(open(p).read())):
        KD.setdefault(m.group(1), []).append((rel(p), m.group(2)))
def kdef(n):
    xs = {evalz(x) for _, x in KD.get(n, [])}
    return xs.pop() if len(xs) == 1 and None not in xs else None
def kwhere(n): return ', '.join(sorted({f for f, _ in KD.get(n, [])}))

def at(txt, pos, lit, pat, win=400):
    r = re.compile(pat.replace('V', '(?P<v>' + re.escape(lit) + r')(?![\w])'))
    for m in r.finditer(txt, max(0, pos - win), min(len(txt), pos + win)):
        if m.start('v') == pos:
            return m
    return None

FETCH = r'fetch_word [\w.]+ \((?:Z_to_bv 64 \((?P<sym>\w+) \+ (?P<off>0x[0-9a-fA-F]+)\)|(?P<lit>0x[0-9a-fA-F]+)(?:%bv)? : word)\) = Some '
def fetch_pc(m):
    if m.group('lit'): return int(m.group('lit'), 16), m.group('lit')
    b = kdef(m.group('sym'))
    return (None, m.group('sym') + ' unresolved') if b is None else (b + int(m.group('off'), 16), '%s + %s' % (m.group('sym'), m.group('off')))
def insn_word(txt, pos, lit, v):
    m = at(txt, pos, lit, r'Definition (?P<w>W_\w+) : bv 32 := V\.')
    if m:
        f = re.search(FETCH + re.escape(m.group('w')) + r'\b', txt)
        if not f: return None
    else:
        f = at(txt, pos, lit, FETCH + r'\(V%bv : bv 32\)')
        if not f:
            d = at(txt, pos, lit, r'Lemma (?P<d>DM?)_(?P<s>\w+) : decode_any \(V%bv : bv 32\)')
            if not d: return None
            fn = ('FM' if d.group('d') == 'DM' else 'F') + '_' + d.group('s')
            f = re.search(r'Lemma ' + fn + r'\s*:\s*' + FETCH + r'\((?P<w>0x[0-9a-fA-F]+)%bv : bv 32\)', txt)
            if not f or int(f.group('w'), 16) != v: return None
    pc, how = fetch_pc(f)
    if pc is None or word(pc) != v: return None
    return 'the word at %#x (%s, %s) is %#010x' % (pc, how, symat(pc), v)
def jimm(w): return (((w >> 31) & 1) << 20) | (((w >> 12) & 0xff) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3ff) << 1)
def decode_result(txt, pos, lit, v):
    m = at(txt, pos, lit, r'Lemma (?P<d>DM?)_(?P<s>\w+) : decode_any (?:(?P<wn>W_\w+)|\((?P<wl>0x[0-9a-fA-F]+)%bv : bv 32\)) = Some \((?P<op>Lui|Jal) (?P<rd>\d+) V, 4%Z\)')
    if not m: return None
    if m.group('wn'):
        d = re.search(r'Definition ' + m.group('wn') + r' : bv 32 := (0x[0-9a-fA-F]+)\.', txt)
        if not d: return None
        w = int(d.group(1), 16); f = re.search(FETCH + re.escape(m.group('wn')) + r'\b', txt)
    else:
        w = int(m.group('wl'), 16)
        f = re.search(r'Lemma ' + ('FM' if m.group('d') == 'DM' else 'F') + '_' + m.group('s') + r'\s*:\s*' + FETCH
                      + r'\((?P<w>0x[0-9a-fA-F]+)%bv : bv 32\)', txt)
        if f and int(f.group('w'), 16) != w: return None
    if not f: return None
    pc, how = fetch_pc(f)
    if pc is None or word(pc) != w or (w >> 7) & 31 != int(m.group('rd')): return None
    if m.group('op') == 'Lui':
        if w & 0x7f != 0x37 or w >> 12 != v: return None
        fld = 'imm[31:12]'
    else:
        if w & 0x7f != 0x6f or jimm(w) != v: return None
        fld = 'the 21-bit J offset'
    return '%s of the word %#010x at %#x (%s, %s)' % (fld, w, pc, how, symat(pc))

OPA = r'\s*(?:\+|\*|-(?!>)|/(?!\\))'
OPB = r'(?:\+|\*|(?<![<\\])-|(?<!\\)/(?!\\))\s*'
NEST = r'\((?:[^()]|\((?:[^()]|\([^()]*\))*\))*\)'
CLS = [            # first match wins; each pattern names the literal's place in its sentence
 ('rw-len', [r'Definition tfib_at_rw_len : Z := V\.',
             r'segments_reserved tfibsegs\)\s*=\s*\[(?:\(\d+, \d+\);\s*)*\((?P<b>\d+), V\)\]']),
 ('opaque-label', [r'\b(?:spin|ISpin|FCheck) V', r'\bmcheck\b(?:[^;]|;(?!;))*?\s(?<![\w.])V\s*;;']),
 ('in-identifier', [r'[A-Za-z_]\w*_V\b']),
 ('imm20', [r'\(V%bv : bv 20\)']),
 ('flit8-value', [r'\bflit8 (?P<a>0x[0-9a-f]+) V']),
 ('witness', [r'\bexists \((?:[^()]|\([^()]*\))*?(?<![\w.])V']),
 ('fuel', [r'\b(?:pop_batches|do_recycle) V']),
 ('length-arg', [r'kn_zero ch \((?:[^()]|\([^()]*\))*\) \d+ V', r'KZero \(SA \w+ \d+\) \(ELit V\)', r'\(epg \d+, ELit V\)',
                 r'\bKZ _ \d+%nat (?:\d+ )?V', r'\bPG \d+%nat V', r'\bmk e\w+ V K\w+', r'\bdm e\w+ V K\w+', r'\(u e\w+, V\)',
                 r'\(w64 V\)', r'\(w64 \w+\) V\b', r'tfib_region_free_reserved \w+ V', r'do_stretch HS \d+%nat 0x[0-9a-f]+ V',
                 r'\bthen V else\b', r'page_round_up_Z V']),
 ('register', [r'\b11%bv = SLit V', r'\b13%bv = SLit V', r'\bpin ' + NEST + r' \d+%bv \(SLit V\)', r'r3_pin HR \(\d+%bv : bv 5\) \(SLit V\)',
               r'getr regs 11 = Z_to_bv 64 V', r'\(SOff \w+ 0, SLit V, SLit 0, SLit 0x104022',
               r'SLit 0, SLit V, SLit 18446744073709551615, SLit 0, SLit 222\)',
               r'SLit V; SLit 3; SLit \d+; SLit 18446744073709551615; SLit 0; SLit 222\]', r'Definition FLR : word := Z_to_bv 64 V\.']),
 ('offset', [r'\bSOff \w+ V', r'\bU_atom_off \w+ \d+ \w+ V']),
 ('mkAF-bound', [r'\bmkAF\s+V', r'\bmkAF\s+(?:\w+|\([^()]*\))\s+V']),
 ('identity', [r'\b(?:change|replace)\s+(?P<e>\w+|' + NEST + r')\s+with\s+V', r'\bzcanon\s+\(?-?V\)?', r'bv_unsigned \(w64 V\) = \d+',
               r'bv_unsigned \(w64 \d+\) = V', r'page_round_up_Z \d+ = V']),
 ('bound', [r'(?:<=|<|<\?|<=\?)\s*V', r'(?<![\w.])V\s*(?:<=|<)(?!-)']),
 ('arith', [OPB + 'V', r'(?<![\w.])V' + OPA, r'\bmod\s+V', r'(?<![\w.])V\s+mod\b', r'\(-V\)', r'\bZ\.(?:mod_pos_bound|div_mod)\s+\w+\s+V',
            r'\bSAlu ALU_\w+ (?:' + NEST + r'|\w+) \(SLit V\)']),
]
def classify(txt, pos, lit, v):
    r = insn_word(txt, pos, lit, v)
    if r: return 'insn-word', r
    r = decode_result(txt, pos, lit, v)
    if r: return 'decode-result', r
    for c, pats in CLS:
        for p in pats:
            m = at(txt, pos, lit, p)
            if not m: continue
            g = m.groupdict()
            if g.get('e'):
                ev = evalz(g['e'])
                src = 'evaluates to'
                if ev is None:
                    ev, src = kdef(g['e']), 'is defined (%s) as' % kwhere(g['e'])
                if ev != v: continue
                return c, '%s %s %d' % (g['e'], src, ev)
            if g.get('a'):
                a = int(g['a'], 16)
                return c, 'the 8-byte value of the cell %#x (%s)' % (a, symat(a))
            if g.get('b'):                  # the last (base, length) pair of segments_reserved: the image's last page range
                lo = max(a for a, _, _ in LOADS) // 4096 * 4096
                if int(g['b']) != lo or lo + v != IMG_TOP: continue
                return c, 'the pair (%s, %d) = [%#x, %#x): the page range of the image\'s last PT_LOAD' % (g['b'], v, lo, IMG_TOP)
            return c, ''
    return None, ''

# ---- per value: the roles every occurrence may have, and the measured identity of the number
def eqk(v, n, f, expr):
    """v must equal f(kernel definition n); expr names the formula, e.g. '{n} / 4096'"""
    def g():
        x = kdef(n)
        return (x is not None and f(x) == v, '%s = %s with %s := %s (%s)' % (
            hex(v), expr.format(n=n), n, x, kwhere(n) or 'not defined in the run'))
    return g
def tot_bound(v):
    def g():
        m = [(rel(p), re.search(r'lo_tr0 : \(1 <= length \(ly_tr0 ly\) <= (\d+)\)', open(p).read())) for p in glob.glob(os.path.join(SO, 'Reusable', '*.v'))]
        m = [(p, x) for p, x in m if x]
        t0, um, dm = (int(m[0][1].group(1)) if m else None), kdef('kUnwindMax'), kdef('DEPOT_MAX')
        if None in (t0, um, dm): return False, 'lo_tr0 / kUnwindMax / DEPOT_MAX not found'
        b = t0 + 1 + (um + 1) * dm
        return b <= v, 'TOT = length ly_tr0 + 1 + depot_frames <= %d + 1 + (kUnwindMax %d + 1) * DEPOT_MAX %d = %d <= %d (lo_tr0: %s; kUnwindMax: %s; DEPOT_MAX: %s)' % (
            t0, um, dm, b, v, m[0][0], kwhere('kUnwindMax'), kwhere('DEPOT_MAX'))
    return g
def depot_q(v):
    def g():
        a = symaddr('_ZN11__sanitizerL8theDepotE')
        ok = a is not None and a % 4 == 0 and a // 4 == v
        t = 'theDepot of the image = %s, / 4 = %s' % (hex(a) if a is not None else 'none', hex(a // 4) if a is not None else '-')
        sf = os.path.join(STARTUP, 'AF0m.v') if STARTUP else None
        if sf and os.path.exists(sf):
            m = re.search(r'Definition TFIB_DEPOT : Z := (0x[0-9a-fA-F]+)\.', open(sf).read())
            ok = ok and m is not None and int(m.group(1), 16) == a
            t += '; A/AF0m.v TFIB_DEPOT = %s' % (m.group(1) if m else 'absent')
        else:
            t += '; needs A/AF0m.v (TFIB_DEPOT must be %s)' % (hex(a) if a is not None else '?')
        return ok, t
    return g
def label_consumers():
    trees = [('stage-out', glob.glob(os.path.join(SO, '*', '*.v'))), ('donor lib', glob.glob(os.path.join(DON, '**', '*.v'), recursive=True))]
    if STARTUP: trees.append(('start-up dir', glob.glob(os.path.join(STARTUP, '*.v'))))
    out, ok = [], True
    for name, fs in trees:
        use = bind = 0; where = set(); own = set()
        for p in fs:
            t = blank(open(p).read())
            if os.path.basename(p) == 'YG00.v':             # its own definitions do not count
                t = re.sub(r'Fixpoint aspins\b.*?\nend\.', ' ', t, flags=re.S)
                t = re.sub(r'\|\s*ISpin pc => ISpin pc\b|\|\s*ISpin pc => Some \(inr pc\)', ' ', t)   # ibind, irun
                use += len(re.findall(r'\baspins\b|\binr\b', t))  # irun's users in YG00 take Some (inl _) only
            elif re.search(r'Fixpoint irun\b', t):            # a model with its own irun (no ISpin): not YG00's
                own.add(os.path.basename(p)); use += len(re.findall(r'\baspins\b', t))
            else:
                use += len(re.findall(r'\b(?:aspins|irun)\b', t))
            b = re.findall(r'\b(?:ISpin|FCheck) (?!_)[a-z]\w*\'?\s*(?:,[^=]*)?=>', t)
            bind += len(b); where |= {os.path.basename(p)} if b else set()
        ok = ok and use == 0 and bind == 0
        out.append('%s %d files: YG00 aspins / irun used %d, label bound by a match arm %d%s%s' % (
            name, len(fs), use, bind, (' (' + ', '.join(sorted(where)) + ')') if where else '',
            (', own irun (not YG00\'s) in ' + ', '.join(sorted(own))) if own else ''))
    return ok, out
_LC = None
def labels():
    global _LC
    if _LC is None: _LC = label_consumers()
    return _LC[0], ('Reusable/YG00.v types it FCheck (pc : Z) / ISpin (pc : Z); only YG00 reads it (ibind passes it, irun returns it, '
                    'aspins compares it), and nothing else uses aspins or irun: ' + '; '.join(_LC[1]))
INSN = (['insn-word'], lambda: (True, 'checked at each occurrence against the image'))
DEC = (['decode-result'], lambda: (True, 'checked at each occurrence: the field of the image\'s word'))
LAB = (['opaque-label'], labels)
SPEC = {
 0x10101: DEC, 0x1fad34: DEC, 0x1fadbc: DEC, 0x1fff94: DEC, 0x1ffff0: DEC,
 0x31294: LAB, 0x312a0: LAB, 0x31614: LAB, 0x33180: LAB, 0x35830: LAB, 0x35f78: LAB, 0x5f844: LAB, 0x6dd44: LAB, 0x706dc: LAB, 0x729f0: LAB,
 0x12000: (['mkAF-bound', 'arith', 'bound'], lambda: (73728 == 18 * 4096, '= 18 * 4096')),
 0x186a0: (['fuel', 'bound'], lambda: (True, '= 100000')),
 0x1f05e: (['bound'], tot_bound(0x1f05e)),
 0x1ffff: (['bound'], lambda: (True, '= 2^17 - 1')),
 0x20000: (['length-arg', 'mkAF-bound', 'identity', 'register', 'arith', 'bound'], eqk(0x20000, 'kPtrArrayCommit', lambda x: x, '{n} = 2^17')),
 0x3fff8: (['offset', 'arith'], eqk(0x3fff8, 'kUserMapSize', lambda x: x - 8, '{n} - 8')),
 0x40000: (['length-arg', 'mkAF-bound', 'identity', 'register', 'offset', 'arith', 'bound'], eqk(0x40000, 'kUserMapSize', lambda x: x, '{n} = 2^18')),
 0x40248: (['length-arg'], lambda: (True, 'the len argument of Ltac do_stretch HS k d len retpc')),
 0x63a36: (['witness'], depot_q(0x63a36)),
 0x65c98: (['in-identifier'], lambda: (True, 'part of a name')),
 0x7fff8: (['witness'], eqk(0x7fff8, 'SHADOW_OFF', lambda x: x // 4096, '{n} / 4096')),
 0x80000: (['witness'], eqk(0x80000, 'kBatchBytes', lambda x: 2 ** 32 // x, '2^32 / {n}')),
 0xe0000: (['witness'], eqk(0xe0000, 'kFreeArrayOffset', lambda x: x // 4096, '{n} / 4096')),
 0x3fffc0: (['witness'], eqk(0x3fffc0, 'SHADOW_OFF', lambda x: x // 512, '{n} / 512')),
 0xfffff: (['decode-result', 'imm20', 'mkAF-bound'], lambda: (True, '= 2^20 - 1')),
 0x100000: (['length-arg', 'identity', 'arith', 'bound', 'flit8-value', 'mkAF-bound'], eqk(0x100000, 'kNodesBlockSize', lambda x: x, '{n} = 2^20')),
 0x104022: (['register'], lambda: (0x2 | 0x20 | 0x4000 | 0x100000 == 0x104022, '= MAP_PRIVATE 0x2 | MAP_ANONYMOUS 0x20 | MAP_NORESERVE 0x4000 | MAP_FIXED_NOREPLACE 0x100000')),
 0x160000: (['identity'], lambda: (True, 'checked at the occurrence')),
 0x161200: (['length-arg'], lambda: (11571200 // 8 == 0x161200, '= 11571200 / 8 (the shadow length of map 424)')),
 0x200000: (['bound'], lambda: (True, '= 2^21')),
 0x38e000: (['length-arg'], eqk(0x38e000, 'AMETA_SIZE', lambda x: x, '{n}')),
 0x3fffff: (['bound', 'mkAF-bound'], lambda: (True, '= 2^22 - 1')),
}
for v in (0x28693, 0x28a63, 0xa0593, 0xa0993, 0xa2603, 0xa3703, 0xb2583, 0x100793, 0x100813, 0x150513, 0x150793, 0x158593, 0x15859b,
          0x158713, 0x15c783, 0x167613, 0x168693, 0x168793, 0x170713, 0x178793, 0x200813, 0x258593, 0x25c803, 0x267713, 0x268693,
          0x268813, 0x300713, 0x300813, 0x357793, 0x35c883, 0x35f693, 0x368693, 0x36f693, 0x36f793, 0x377293, 0x458593, 0x459713,
          0x45a783, 0x45a803, 0x45c283, 0x45f793, 0x461a13, 0x467713, 0x468293, 0x468693, 0x4a0a13, 0x4b0b13, 0x4c8c93, 0x53e2b3,
          0x55c303, 0x568223, 0x568623, 0x56a423, 0x56a623):
    SPEC[v] = INSN

DECL = {}
for line in open(NOTADDR):
    if line.strip() and not line.startswith('#'):
        a, _, b = line.rstrip('\n').partition('\t'); DECL[int(a, 0)] = b

# ---- every occurrence the gate reads of a declared value, in every checked file
def occurrences(f, wanted, lo=0x10000):
    txt = TXT[f]
    brk = {int(x) for p in re.findall(r'KRange \(EVar 5\) (\d+) (\d+)', txt) for x in p}
    brk |= {int(x) for x in re.findall(r'C(?:Img|Val) (\d+)', txt)}
    brk |= {int(x) for x in re.findall(r'\(CH R_\w+ \d+ (\d+)\)', txt)}
    brk |= {int(x) for x in re.findall(r'IMG_REGIONS R_\w+ \d+ (\d+) HM', txt)}
    defs = [(m.start(), '%s %s' % (m.group(1), m.group(2))) for m in cp.DEF_RE.finditer(txt)]
    qs = cp.quantity_spans(txt, defs)
    for m in re.finditer(r'0x[0-9a-fA-F]+|(?<![\w.])\d{5,}(?!\d|\.\d)', txt):
        s = m.group(0); v = int(s, 16) if s.startswith('0x') else int(s)
        if v < lo or v in brk or v not in wanted: continue
        if txt.startswith('%nat', m.end()) or any(a <= m.start() < b for a, b, _ in qs): continue
        yield v, m.start(), s
RES = {v: SPEC[v][1]() for v in DECL if v in SPEC}       # the value-level measurement, once
def brief(v):
    if v not in RES: return ''
    if SPEC[v] is LAB: return 'the pc argument of YG00 mcheck / spin / FCheck / ISpin; no consumer compares it (roles.out)'
    return RES[v][1]
rows, bad, perv, mism = [], [], {}, []
for f in FILES:
    seen = set()
    for v, pos, lit in occurrences(f, set(DECL)):
        seen.add(v)
        c, meas = classify(TXT[f], pos, lit, v)
        ln = RAW[f].count('\n', 0, pos) + 1
        a = RAW[f].rfind('\n', 0, pos) + 1; b = RAW[f].find('\n', pos); b = len(RAW[f]) if b < 0 else b
        ctx = RAW[f][max(a, pos - 70):min(b, pos + 70)].strip().replace('\t', ' ')
        ok = v in SPEC and c in SPEC[v][0]
        rows.append((v, rel(f), ln, c if ok else 'UNEXPLAINED' + ('(' + c + ')' if c else ''), ctx, meas or brief(v)))
        perv.setdefault(v, []).append(ok)
        if not ok: bad.append('%#x %s:%d %s' % (v, rel(f), ln, ctx))
    lits = cp.literals(f, 0x10000)[0] & set(DECL)          # the gate's own literal set must be the one measured here
    if lits != seen: mism.append('%s: gate %s, measured %s' % (rel(f), sorted(map(hex, lits - seen)), sorted(map(hex, seen - lits))))

# ---- the defect check: tfib_at_rw_lo / tfib_at_rw_len are the page range [floor(last PT_LOAD), IMG_TOP) of the image
LAST = max(a for a, _, _ in LOADS)
dv = []
for f in FILES:
    lo = re.search(r'Definition tfib_at_rw_lo : Z := (0x[0-9a-fA-F]+)\.', TXT[f]); ln_ = re.search(r'Definition tfib_at_rw_len : Z := (0x[0-9a-fA-F]+)\.', TXT[f])
    if lo and ln_:
        want_lo = LAST // 4096 * 4096; want = IMG_TOP - want_lo; have = int(ln_.group(1), 16)
        line = RAW[f].count('\n', 0, ln_.start()) + 1
        good = want == have and int(lo.group(1), 16) == want_lo
        print('roles: %s %s:%d tfib_at_rw_lo %s, tfib_at_rw_len %s; the image: last PT_LOAD %#x..%#x, page range [%#x, %#x) of length %#x' % (
            'OK' if good else 'DEFECT', rel(f), line, lo.group(1), ln_.group(1), LAST, IMG_END, want_lo, IMG_TOP, want))
        if not good:
            dv.append(have)
            if have != want:
                rows.append((have, rel(f), line, 'DEFECT', RAW[f].splitlines()[line - 1].strip(),
                             'stale donor length: the image gives IMG_TOP %#x - tfib_at_rw_lo %s = %#x' % (IMG_TOP, lo.group(1), want)))
with open(OUT, 'w') as o:
    o.write('# every occurrence, in every checked stage-out/A file, of each value codeptr-notaddr.tsv declares (and each DEFECT\n'
            '# row of the defect check); class = the measured role of that occurrence; measured = what was read from the image or\n'
            '# the text; written by codeptr-A.sh\n')
    o.write('value\tfile\tline\tclass\tcontext\tmeasured\n')
    for r in sorted(rows):
        o.write('%#x\t%s\t%d\t%s\t%s\t%s\n' % r)
nv_bad, needs = 0, set()
for v in sorted(DECL):
    if v not in SPEC:
        print('roles: %#x UNEXPLAINED: no role is specified for it' % v); nv_bad += 1; continue
    ok, txt = RES[v]
    needs |= set(re.findall(r'needs (\S+)', txt))
    n = len(perv.get(v, [])); good = sum(perv.get(v, []))
    st = 'MEASURED' if ok and n and good == n else 'UNEXPLAINED'
    nv_bad += st != 'MEASURED'
    print('roles: %#x %d occurrence(s), %d with a measured role (%s); %s: %s' % (v, n, good, '/'.join(SPEC[v][0]), st, txt))
for b in bad: print('roles: UNEXPLAINED occurrence %s' % b)
for m in mism: print('roles: LITERAL-SET MISMATCH %s' % m)
print('roles: %d declared value(s), %d occurrence(s): %d UNEXPLAINED value(s), %d UNEXPLAINED occurrence(s), %d literal-set mismatch(es), '
      '%d DEFECT(s)%s' % (len(DECL), sum(map(len, perv.values())), nv_bad, len(bad), len(mism), len(dv),
                          ''.join(', needs %s' % n for n in sorted(needs))))
sys.exit(1 if nv_bad or bad or mism else 0)
PY
echo "rc=$?" >> "$OUT/roles.out"
fr --image "$FB" --names "$FT" "${STALE[@]}" "${NA[@]}" "$WORK"/stage-out/A/*.v > "$OUT/declared.out" 2>&1; echo "rc=$?" >> "$OUT/declared.out"
fr --image "$FB" --names "$FT" "${STALE[@]}" "${NA[@]}" "$OUT"/plant-all/A/*.v > "$OUT/plant-declared.out" 2>&1; echo "rc=$?" >> "$OUT/plant-declared.out"
# the controls: the plant is a finding, in AE3m.v only, STALE; the same file unplanted has none
found() { grep -E '^[^ ]+ .* [1-9][0-9]* FINDINGS' "$1"; }
PLANTED="^AE3m\.v .* 1 FINDINGS: $DV \[stale against fuzz_grant\.asan, .*: 1 STALE \($DV\)"
ctl() {   # ctl NAME FILE [BASELINE]: the finding lines are BASELINE's (none if not given) plus exactly the planted AE3m.v line
  local l b n extra gone base=""
  l=$(found "$2" | sort); n=$(printf '%s' "$l" | grep -c .); b=""
  if [ -n "${3:-}" ]; then b=$(found "$3" | sort); base="the $(basename "$3" .out) run: $(printf '%s' "$b" | grep -c .) + "; fi
  extra=$(comm -23 <(printf '%s\n' "$l") <(printf '%s\n' "$b") | grep .); gone=$(comm -13 <(printf '%s\n' "$l") <(printf '%s\n' "$b") | grep .)
  if [ "$(printf '%s' "$extra" | grep -c .)" = 1 ] && printf '%s' "$extra" | grep -qE "$PLANTED" && [ -z "$gone" ]; then
    echo "$1: $n finding line(s) = ${base}the planted AE3m.v $DV, STALE against fuzz_grant.asan: PASS"
  else echo "$1: $n finding line(s), not ${base}exactly the planted AE3m.v $DV STALE: FAIL"; fi
}
rel() { sed -E 's#donor file [^ :]*/(A/[^ :]*)#donor file stage/\1#'; }
{
  echo "# command: $(readlink -f "$0") $WORK $LIB $OUT0 (TIMG=$TIMG PG=$PG DON=$DON SET=$SS)"
  echo "# pins:$PINS bundle $BUNDLE (set SHA256SUMS: $SUMS of $SUMN OK); plant $DV (stage/A/AE3m.v STDOUT_BUFA)"
  echo "# inputs (sha256 of the sorted per-file sha256sum list): $INSHA"
  for f in donor plant; do echo "# $f"; { found "$OUT/$f.out"; grep -E '^codeptr: (UNMEASURED|REFUSED)|^rc=' "$OUT/$f.out"; } | rel; done
  echo "# base"
  awk '/^[^ ]+ .* [0-9]+ FINDINGS/ { for (i = 1; i < NF; i++) if ($(i + 1) ~ /^FINDINGS:?$/ && $i > 0) { n += $i; m++ } }
       END { printf "base: %d finding(s) in %d file(s); every value, each occurrence measured: codeptr-occurrences.tsv\n", n, m }' "$OUT/base.out"
  grep -E '^codeptr: (UNMEASURED|REFUSED)|^rc=' "$OUT/base.out"
  for f in declared plant-declared; do echo "# $f"; { found "$OUT/$f.out"; grep -E '^codeptr: (UNMEASURED|REFUSED)|^rc=' "$OUT/$f.out"; } | rel; done
  echo "# roles"
  grep -E '^roles: (DEFECT|OK|UNEXPLAINED|LITERAL|[0-9]+ declared)|^rc=' "$OUT/roles.out"
  grep -E '^roles: 0x63a36 |^roles: 0x[0-9a-f]+ (UNEXPLAINED|.*\); UNEXPLAINED)' "$OUT/roles.out"
  echo "# controls"
  ctl plant "$OUT/plant.out"
  ctl plant-declared "$OUT/plant-declared.out" "$OUT/declared.out"
  grep -E '^AE3m\.v ' "$OUT/base.out" | grep -q ' 0 FINDINGS' && echo "base: AE3m.v unplanted, 0 FINDINGS: PASS" || echo "base: AE3m.v unplanted has a finding: FAIL"
} > "$REC/codeptr.txt"
cat "$REC/codeptr.txt"
# the gate passes when the roles step explains every declared value and occurrence (rc 0), the declared run refuses nothing
# and finds nothing (rc 0, or 2 = only files with no address literal), and every control says PASS
RRC=$(awk -F= '/^rc=/ { r = $2 } END { print r }' "$OUT/roles.out")
DRC=$(awk -F= '/^rc=/ { r = $2 } END { print r }' "$OUT/declared.out")
if grep -q ': FAIL$' "$REC/codeptr.txt" || [ "$RRC" != 0 ] || { [ "$DRC" != 0 ] && [ "$DRC" != 2 ]; } \
   || grep -q '^codeptr: REFUSED' "$OUT/declared.out"; then
  echo "codeptr-A: gate (b) not passed (roles rc $RRC, declared rc $DRC; OUT/records/codeptr.txt)" >&2
  exit 1
fi
