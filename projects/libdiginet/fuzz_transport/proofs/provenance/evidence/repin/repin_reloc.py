#!/usr/bin/env python3
"""repin_reloc.py -- move libdiginet/fuzz_transport's proof tree from one pair of plain / UBSan binary pins to another.

usage:
  repin_reloc.py all  --unit UNIT_DIR --kit CMPKIT_DIR --old-plain PIN:TWIN --old-ubsan PIN:TWIN --new-plain PIN:TWIN
                      --new-ubsan PIN:TWIN --work DIR --git CLONE --src-unstripped DIR [--leave REL ...] [--month 2026-10]
                      [--k2-old DIR --k2-new DIR | --pac PATH --decode-bin DIR --donor-bin DIR --k2-pythonpath DIR]
  repin_reloc.py own  --unit UNIT_DIR --kit CMPKIT_DIR --old-plain ... --new-ubsan ... --work DIR --k2-lib DIR
                      [--leave REL ...] [--dry-run]
  repin_reloc.py kit  --unit UNIT_DIR --kit CMPKIT_DIR --k2-old DIR --k2-new DIR --new-plain PIN:TWIN --new-ubsan PIN:TWIN
CMPKIT_DIR is the comparison kit (cmpkit 4bbd3a74be89: strictcmp2.py, jtcheck.py; codedelta.py checks it). The
options after --git are the inputs of the K2 run (kit_relocate.py's --pac, --decode-bin, --donor-bin, and the PYTHONPATH
that gives it pyelftools); `all` needs them unless --k2-old and --k2-new give both K2 outputs. --src-unstripped is
relocate.py's --unstripped (the donor units' unstripped twins).
UNIT_DIR is <worktree>/proofs/libdiginet/fuzz_transport; PIN is a stripped binary, TWIN its unstripped twin (.symtab,
DWARF). REL paths are relative to UNIT_DIR/lib. `all` is the one command of a re-pin; the others are its steps.

`all` runs, stopping at the first step that fails:
  1. K2 (the shared kit relocation, provenance/evidence/kit-relocation/kit_relocate.py, with this unit's arguments of
     provenance/evidence/kit-relocation/MANIFEST) at the OLD pins (the control; --k2-old DIR reuses such an output) and
     at the NEW pins, into WORK/k2-old and WORK/k2-new.
  2. kit: every kit file (a file K2 writes) of the tree is the old K2 output plus the unit's own edits after K2; each
     becomes the new K2 output plus the same edits (git merge-file; a conflict stops the run). A kit file K2 no longer
     writes, or a new one, is reported (and removed / added). Then the image-geometry facts of the post-K2 edits
     (commit b3942fa436c) are MEASURED on the new images and must hold (GEOMETRY below).
  3. own: every OTHER .v file of lib/ (written neither by K2 nor by srcreloc: Prog/T, U/Prog/T, TModel, TSim, Spec, ...)
     by the rules below.
  4. src/: provenance/evidence/srcreloc/relocate.py with --target-plain / --target-ubsan = the new pins (after own:
     its S4 check reads U/Prog/T/TContract.v's RELRO_BASE, which own moves). A src/ file the tree edited after
     srcreloc wrote it (its sha256 is not its row's in srcreloc/relocate-list.tsv; e.g. the walk kit's
     diginet_cursor_init.v edits) gets the same edits on the new output: a line-level 3-way merge from the git blob
     with that row's sha256.

OWN FILE RULES. A file's build is ubsan under U/, else plain; a code line that names W_BASE_UBSAN / ubsan is ubsan.
Numerals are hex (0x...) or decimal tokens; only those inside the old image's load range [first PT_LOAD page,
last PT_LOAD end rounded up to a page) are image candidates.
  CODE (outside comments), hex: an image numeral, moved by the first rule that applies, else the run STOPS:
    (s) a line about segments_reserved: the value is a reserved segment's page base or page size (PT_LOAD p_vaddr
        rounded down, p_vaddr + p_memsz rounded up): the same segment's value in the new image;
    (k) a numeral inside `Definition W_LEN / OFF_* / SZ_*` is a length or offset, never an address: kept;
    (f) inside a sized STT_FUNC symbol F at offset o: new F + o; F must be EQUAL or EQUAL-mod-pcrel old -> new by the
        comparison kit (cmpkit 4bbd3a74be89: strictcmp2 16982e3ef42b; a jump-table target the kit leaves 'data-differs'
        is settled by its jtcheck.py, every entry the same function-relative offset); o > 0 inside a DIFFERENT function
        STOPS the run; o = 0 (the function's entry, a symbol) moves and is reported;
    (o) inside a sized STT_OBJECT symbol S at offset o: new S + o (same size, or o = 0);
    (e) the end of a sized symbol (an exclusive bound) that is no symbol's start: the new end;
    (c) a section's start or end: the new section's; inside a section in no symbol: the same section offset, when the
        bytes from it to the next symbol or the section end are equal in both images (.bss: the same size), or, in
        .rodata, when the NUL-terminated string at it is the same at the same section offset;
    (h) inside the ELF header / program headers before the first section: unchanged, when the new first section
        starts at the same address;
    (l) a PT_LOAD start or end, or its page rounding: the new segment's;
    duplicated names are paired by (name, STT_FILE, address order).
    (a) a value that rules (o) / (c) place inside data at no symbol start and that is the result of auipc
        instructions of the old image (a register a walk states, e.g. check_latest_sent's loop register s11): the
        result of the same auipc in the new image (its pc moved by rule (f)), since it moves with the code.
  CODE, decimal: a decimal of DEC_KEEP (constants of the model and of the harness: 2^16, W_LEN, ...) stays; (w) a
    decimal below W_LEN = 0x10050 is an offset into the world B (TWorld.v), never an address (that page holds the ELF
    header), and stays; any other decimal in the range is an address written in decimal (a Z_to_bv 64 argument, or a
    rewrite / change / ret_pc_even / bytes_at argument of a walk) and moves by rules (f)..(l), as a hex numeral does.
  CODE, (n) hex or decimal in [2^64 - range end, 2^64 - range start]: the 64-bit complement ~a or negation -a of an
    image address a (e.g. U/Prog/T/diginet_session_deadline.v's xori -1 of &g_s + 1760); it moves by the delta of a
    (both readings must give the same delta), else the run STOPS.
  COMMENTS: hex numerals that are a pc of an EQUAL / EQUAL-mod-pcrel function, a function's entry, or the start of a
    data symbol move (on a line naming auipc, only the first numeral, the pc); every other image numeral in a comment
    stays and is listed (WORK/own-comments-left.tsv). A numeral of a made-up demo image (a statement about demo*_segs)
    stays; when it equals a pinned-image address that moves, it is listed as BRITTLE (WORK/own-brittle.tsv).
  --leave REL: that file is not touched (a file of a DIFFERENT function's walk, for the re-pin's own work list).
Every moved numeral goes to WORK/own-values.tsv (file, line, code|comment, old, new, rule). A run with any STOP writes
no file and exits 1, printing every stop.

GEOMETRY (step 2, measured; each must hold on the new images or the run stops naming the new value):
  G1 Reusable/YL0k.v, U/Reusable/YL0k.v: image top 0x64000 = the last PT_LOAD end rounded up to 0x1000, both builds;
  G2 U/Reusable/YN0a(_cf).v block 0x1000: every ubsan reserved segment base is on a 0x1000 grid from 0x10000;
  G3 Reusable/YN1n(_cf).v R_tabs: plain __malloc_size_classes - DEB = 208 and size_classes 96 + small_cnt_tab 27 +
     med_cnt_tab 4 contiguous (127), DEB = the YH03 src0_D_debruijn32 of the new K2 output;
  G4 FrameAPI.v ms_debruijn = the new YH03 src0_D_debruijn32 (plain), U/FrameAPI.v the ubsan one.
"""
import argparse, bisect, collections, hashlib, importlib.util, os, re, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
KIT = None  # --kit: the comparison kit directory (set in main, after codedelta.load_kit has checked it)
# K2: the unit's kit relocation script, shipped beside this directory; its sha256 must be K2_SHA
K2 = os.path.join(os.path.dirname(HERE), 'kit-relocation', 'kit_relocate.py')
K2_SHA = 'b3f6713fe96aff2c0a508238be941648ae604031a26d353e9f60d787e83ab773'
# this unit's K2 arguments (provenance/evidence/kit-relocation/MANIFEST); --git, --pac, --decode-bin and --donor-bin
# follow them from this script's own options
K2_ARGS = ['--project', 'libdiginet', '--unit', 'fuzz_transport', '--donor-ref', 'bf7779f81ed764787b77895d2f5c0db2627f33f3',
           '--kit-ref', '25e3d17bdb5059606131377a3722d585415ab5d6']
PAGE = 0x1000
NUM = re.compile(r'(?<![0-9A-Za-z_\'.])(0x[0-9a-fA-F]+|[0-9]+)(?![0-9A-Za-z_\'])')
DEC_KEEP = {65536: '2^16 (u16 modulus, config bounds, SLOT_STACK)', 65616: 'W_LEN (the world length 0x10050)',
            100000: 'LLVMFuzzerTestOneInput_SCALE entry (a time scale of the harness)',
            255000: 'the harness back-off bound in ms (fuzz_transport.c)'}
KEEP_DEF = re.compile(r'Definition\s+(W_LEN|OFF_\w+|SZ_\w+)\b')
W_LEN_DEC = 0x10050  # TModel/TWorld.v W_LEN, the same in both builds and both pins

def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()

_spec = importlib.util.spec_from_file_location('codedelta', os.path.join(HERE, 'codedelta.py'))
cd = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(cd)
sc = None  # codedelta's strictcmp2 module (cd.sc), set in main

# ---------------------------------------------------------------- images
class Pair:
    """one build: old and new unstripped twins, symbol pairing, function verdicts"""
    def __init__(s, build, old, new):
        s.build, s.paths = build, {'O': old, 'N': new}
        s.I = {'O': sc.Img(old), 'N': sc.Img(new)}
        s.verdicts = {}
        s.key = {k: s._keys(k) for k in 'ON'}
        s.loads = {k: [(g['p_vaddr'], g['p_memsz']) for g in s.I[k].e.iter_segments() if g['p_type'] == 'PT_LOAD']
                   for k in 'ON'}
        s.lo = min(v for v, z in s.loads['O']) // PAGE * PAGE
        s.hi = -(-max(v + z for v, z in s.loads['O']) // PAGE) * PAGE

    def _keys(s, k):
        """{(type, name, file, index): (addr, size)} and the reverse, for sized FUNC / OBJECT symbols"""
        I = s.I[k]; m = sc._meta(I); grp = collections.defaultdict(list)
        for v, z, n, t in I.syms:
            if t in ('STT_FUNC', 'STT_OBJECT') and z > 0:
                grp[(t, n, m['fil'].get((v, n)) if n in m['dup'] else None)].append((v, z))
        fwd = {}
        for (t, n, f), lst in grp.items():
            for i, vz in enumerate(sorted(set(lst))): fwd[(t, n, f, i)] = vz
        rev = collections.defaultdict(list)
        for key, (v, z) in fwd.items(): rev[v].append((key, z))
        return fwd, rev

    def containing(s, k, a):
        """[(key, start, size)] of the sized FUNC / OBJECT symbols containing a, smallest first"""
        I = s.I[k]; i = bisect.bisect_right(I.addrs, a); out = []
        for j in range(i - 1, max(-1, i - 600), -1):
            v, z, n, t = I.syms[j]
            if t in ('STT_FUNC', 'STT_OBJECT') and z > 0 and v <= a < v + z:
                m = sc._meta(I); f = m['fil'].get((v, n)) if n in m['dup'] else None
                idx = sorted(set(vz for kk, vz in s.key[k][0].items() if kk[:3] == (t, n, f))).index((v, z))
                out.append(((t, n, f, idx), v, z))
        return sorted(set(out), key=lambda x: x[2])

    def verdict(s, key):
        """EQUAL / EQUAL-mod-pcrel / DIFFERENT@off of a function, old -> new, by the comparison kit (+ jtcheck)"""
        if key in s.verdicts: return s.verdicts[key]
        o, n = s.key['O'][0].get(key), s.key['N'][0].get(key)
        if n is None: r = ('ABSENT', '', 'no such function in the new image')
        else:
            r = cd.compare({'O': s.I['O'], 'N': s.I['N']}, 'O', o[0], o[1], 'N', n[0], n[1])
            if r[0] == 'DIFFERENT' and 'data-differs' in r[2] and '(pcrel,real,unk)=' in r[2] and ', 0, 0)' in r[2]:
                r = s._jt(key, r)
        s.verdicts[key] = r
        return r

    def _jt(s, key, r):
        nm = key[1] if key[2] is None else '%s{%s}' % (key[1], key[2])
        out = subprocess.run([sys.executable, os.path.join(KIT, 'jtcheck.py'), s.paths['O'], s.paths['N'], nm],
                             capture_output=True, text=True).stdout
        head = out.splitlines()[0] if out else ''
        ok = (head.startswith(nm + '\tX ') and '\ttarget differs 0\t' in head and '\ttarget unmeasured 0\t' in head
              and '\tunpaired 0\t' in head and '   DIFF ' not in out and 'REAL' not in out)
        if ok:
            return ('EQUAL-mod-pcrel', '', 'jtcheck settled: ' + ' | '.join(l.strip() for l in out.splitlines()[1:]
                                                                          if l.strip().startswith('ACCEPT')))
        return r

    def secs(s, k):
        return [(n, v, z) for n, v, z in s.I[k].secs]

    def reserved(s, k):
        return [(v // PAGE * PAGE, -(-(v + z) // PAGE) * PAGE - v // PAGE * PAGE) for v, z in s.loads[k]]

    # ---- the rules (f) (o) (e) (c) (h) (l) for one value
    def resolve(s, a):
        """-> (new, rule, detail) or (None, 'STOP', why)"""
        cont = s.containing('O', a)
        if cont:
            res = set(); det = []
            for key, v, z in cont:
                off = a - v; t = key[0]
                nv = s.key['N'][0].get(key)
                if nv is None: return None, 'STOP', '%s %s+%#x: no such symbol in the new image' % (t, key[1], off)
                if t == 'STT_FUNC':
                    vd = s.verdict(key)
                    if vd[0] not in ('EQUAL', 'EQUAL-mod-pcrel'):
                        if off == 0:
                            res.add(nv[0]); det.append('f-entry %s (function %s %s)' % (key[1], vd[0], vd[1])); continue
                        return None, 'STOP', 'pc %s+%#x inside a function that is %s %s (%s)' % (key[1], off, vd[0], vd[1], vd[2][:120])
                    res.add(nv[0] + off); det.append('f %s+%#x %s' % (key[1], off, vd[0]))
                else:
                    if nv[1] != z and off != 0:
                        return None, 'STOP', 'object %s+%#x changed size %d -> %d' % (key[1], off, z, nv[1])
                    res.add(nv[0] + off); det.append('o %s+%#x' % (key[1], off))
            if len(res) != 1: return None, 'STOP', 'symbols disagree: %s -> %s' % (det, sorted(map(hex, res)))
            return res.pop(), det[0].split()[0], '; '.join(det)
        # (c) section boundaries first (a section start is also the end of the symbol before it)
        so, sn = {n: (v, z) for n, v, z in s.secs('O')}, {n: (v, z) for n, v, z in s.secs('N')}
        for n, (v, z) in so.items():
            if a == v and n in sn: return sn[n][0], 'c', 'start of %s' % n
            if a == v + z and n in sn: return sn[n][0] + sn[n][1], 'c', 'end of %s' % n
        # (e) end of a sized symbol
        ends = [(key, v, z) for key, (v, z) in s.key['O'][0].items() if v + z == a]
        if ends:
            res = {s.key['N'][0][key][0] + s.key['N'][0][key][1] for key, v, z in ends if key in s.key['N'][0]}
            if len(res) == 1 and all(key in s.key['N'][0] for key, v, z in ends):
                return res.pop(), 'e', 'end of ' + ','.join(sorted({k[1] for k, v, z in ends}))
            return None, 'STOP', 'end of %s: disagreeing new ends' % [k[1] for k, v, z in ends]
        for n, (v, z) in so.items():
            if v <= a < v + z and n in sn:
                nv, nz = sn[n]
                if nz != z and not n.startswith('.rodata'):
                    return None, 'STOP', 'unnamed %s+%#x: section size %d -> %d' % (n, a - v, z, nz)
                ro = sc.region(s.I['O'], a); rn = sc.region(s.I['N'], nv + a - v)
                if n == '.bss' or (ro is not None and ro == rn):
                    return nv + a - v, 'c', 'unnamed %s+%#x' % (n, a - v)
                if n in ('.got', '.data.rel.ro', '.init_array', '.fini_array') and (a - v) % 8 == 0:
                    # a pointer cell: the new cell holds the old cell's pointer moved by these rules
                    wo = int.from_bytes(sc.frd(s.I['O'], a, 8), 'little')
                    wn = int.from_bytes(sc.frd(s.I['N'], nv + a - v, 8), 'little')
                    tgt = wo if wo == wn else (s.resolve(wo)[0] if s.lo <= wo < s.hi else None)
                    if tgt == wn:
                        return nv + a - v, 'c', 'unnamed %s+%#x, a cell holding %#x -> %#x' % (n, a - v, wo, wn)
                if n.startswith('.rodata'):
                    # a string literal: the NUL-terminated bytes from a are the same at the same section offset (the
                    # region's tail may differ, e.g. a jump table whose table-relative entries changed)
                    so_ = sc.frd(s.I['O'], a, 256) or b''; nul = so_.find(b'\0')
                    if nul > 0 and sc.frd(s.I['N'], nv + a - v, nul + 1) == so_[:nul + 1]:
                        return nv + a - v, 'c', 'unnamed %s+%#x, the string %r equal in both images' % (n, a - v, so_[:nul].decode('latin-1'))
                return None, 'STOP', 'unnamed %s+%#x: bytes differ in the new image' % (n, a - v)
        # (h) header
        f0 = min(v for n, v, z in s.secs('O')); f1 = min(v for n, v, z in s.secs('N'))
        if s.lo <= a < f0 and f0 == f1: return a, 'h', 'ELF header / program headers'
        # (l) segments
        for (v, z), (nv, nz) in zip(s.loads['O'], s.loads['N']):
            for x, y, what in ((v, nv, 'start'), (v + z, nv + nz, 'end'), (v // PAGE * PAGE, nv // PAGE * PAGE, 'page start'),
                               (-(-(v + z) // PAGE) * PAGE, -(-(nv + nz) // PAGE) * PAGE, 'page end')):
                if a == x: return y, 'l', 'PT_LOAD %s' % what
        return None, 'STOP', 'in no symbol, section or segment boundary'

    def auipc_map(s, k):
        """{result: [pc, ...]} of every auipc in .text of image k (a linear sweep: a 32-bit parcel ends in 0b11)"""
        c = s.__dict__.setdefault('_au', {})
        if k in c: return c[k]
        I = s.I[k]; out = collections.defaultdict(list)
        tv, tz = next((v, z) for n, v, z in s.secs(k) if n == '.text')
        d = sc.frd(I, tv, tz) or b''; i = 0
        while i + 2 <= len(d):
            if int.from_bytes(d[i:i + 2], 'little') & 3 != 3: i += 2; continue
            w = int.from_bytes(d[i:i + 4], 'little')
            if w & 0x7f == 0x17:
                imm = w & 0xfffff000
                if imm >> 31: imm -= 1 << 32
                out[(tv + i + imm) % (1 << 64)].append(tv + i)
            i += 4
        c[k] = out
        return out

    def auipc_move(s, v):
        """(a) v is the result of auipc instructions of the old image: each pc moves by rule (f) to an auipc of the new
        image with the same rd, and v becomes that auipc's result (one for all of them). None when v is no auipc
        result; (None, why) when a pc does not move so or the results disagree."""
        pcs = s.auipc_map('O').get(v)
        if not pcs: return None
        res, det = set(), []
        for pc in pcs:
            npc, rule, d = s.resolve(pc)
            if npc is None or rule != 'f': return None, 'auipc at %#x: %s' % (pc, d)
            wo = int.from_bytes(sc.frd(s.I['O'], pc, 4), 'little')
            w = int.from_bytes(sc.frd(s.I['N'], npc, 4) or bytes(4), 'little')
            if w & 0xfff != wo & 0xfff: return None, 'auipc at %#x: the new image has %#010x at %#x' % (pc, w, npc)
            imm = w & 0xfffff000
            if imm >> 31: imm -= 1 << 32
            res.add((npc + imm) % (1 << 64)); det.append('auipc %#x -> %#x' % (pc, npc))
        if len(res) != 1: return None, 'auipc readings disagree: %s' % det
        return res.pop(), '; '.join(det)

    def comment_ok(s, a):
        """a comment numeral moves only when it is a pc of an EQUAL / EQUAL-mod-pcrel function, the entry of any
        function, or a data symbol start"""
        cont = s.containing('O', a)
        if not cont: return None, 'not a pc or symbol start'
        new, rule, det = s.resolve(a)
        if new is None: return None, det
        if rule in ('f', 'f-entry'): return new, det
        if rule == 'o' and all(a == v for key, v, z in cont): return new, det
        return None, 'data, not a symbol start (%s)' % det

    def reserved_map(s, a):
        out = set()
        for (b, z), (nb, nz) in zip(s.reserved('O'), s.reserved('N')):
            if a == b: out.add(nb)
            if a == z: out.add(nz)
        return out.pop() if len(out) == 1 else None

# ---------------------------------------------------------------- text
def split_comments(text):
    """[(is_comment, start, chunk)]: Coq's nested (* *) comments; "..." strings stay code"""
    out, i, n, depth, start, instr = [], 0, len(text), 0, 0, False
    while i < n:
        if depth == 0 and text[i] == '"':
            instr = not instr; i += 1; continue
        if instr: i += 1; continue
        if text.startswith('(*', i):
            if depth == 0: out.append((False, start, text[start:i])); start = i
            depth += 1; i += 2; continue
        if depth and text.startswith('*)', i):
            depth -= 1; i += 2
            if depth == 0: out.append((True, start, text[start:i])); start = i
            continue
        i += 1
    out.append((depth > 0, start, text[start:]))
    return out

def line_of(text, pos):
    a = text.rfind('\n', 0, pos) + 1; b = text.find('\n', pos)
    return text.count('\n', 0, pos) + 1, text[a:b if b >= 0 else len(text)]

def fmt(old_tok, new):
    return ('%#x' % new) if old_tok.startswith('0x') else str(new)

STMT = re.compile(r'(?m)^[ \t]*(Lemma|Theorem|Definition|Example|Fact|Corollary|Proposition|Module|Abbreviation|Notation)\b')

def stmt_of(text, pos):
    """the vernacular statement holding pos: from the last Lemma / Definition / ... keyword before pos to its Proof."""
    st = [m.start() for m in STMT.finditer(text, 0, pos)]
    a = st[-1] if st else 0
    b = text.find('Proof.', pos)
    return text[a:b if b >= 0 else min(len(text), pos + 2000)]

def k2_files(d):
    out = set()
    for r, _, fs in os.walk(d):
        for f in fs: out.add(os.path.relpath(os.path.join(r, f), d))
    return out

def own_files(unit, kit, rlist):
    sr = set(l.split()[0][4:] for l in open(rlist) if l.startswith('lib/'))
    out = []
    for r, _, fs in os.walk(os.path.join(unit, 'lib')):
        for f in fs:
            if not f.endswith('.v'): continue
            rel = os.path.relpath(os.path.join(r, f), os.path.join(unit, 'lib'))
            if rel not in kit and rel not in sr: out.append(rel)
    return sorted(out)

DEMO = re.compile(r'Module (Demo\w*)\.(.*?)End \1\.', re.S)
SEGB = re.compile(r'seg_base := (0x[0-9a-fA-F]+)%N')
SEGX = re.compile(r'seg_bytes := \["([0-9a-fA-F]+)"%pstring\]')

def world(P, k):
    """[M, end of OW) of image k: the harness's world (TModel/TWorld.v W_BASE_*, W_LEN)"""
    m = P.key[k][0][('STT_OBJECT', 'M', None, 0)]; o = P.key[k][0][('STT_OBJECT', 'OW', None, 0)]
    return m[0], o[0] + o[1]

def demo_reencode(rel, text, P):
    """the made-up demo images (Module Demo*: seg_base / seg_bytes) of a file reach world globals through auipc + lo12
    pairs. When the world moves, each lo12 immediate is re-encoded so that it reaches the same world offset; every
    auipc stays (so the demo lemmas' auipc results stay). The instruction comment `0x<pc> ... <imm>(<reg>)` of each
    re-encoded word gets the new immediate. A target that would need another auipc, or a compressed parcel, is BRITTLE."""
    (wo, we), (wn, _) = world(P, 'O'), world(P, 'N')
    vals, brit = [], []
    if wo == wn: return text, vals, brit
    def sx(x, n): return x - (1 << n) if x >> (n - 1) & 1 else x
    def hx(i): return '%#x' % i if i >= 0 else '-%#x' % -i
    for name in [mm.group(1) for mm in DEMO.finditer(text)]:
        m = re.search(r'Module (%s)\.(.*?)End \1\.' % re.escape(name), text, re.S)
        body = m.group(2); b = SEGB.search(body); x = SEGX.search(body)
        if not b or not x: continue
        base = int(b.group(1), 16); raw = bytes.fromhex(x.group(1)); out = bytearray(raw); regs = {}; fix = []
        ln = text.count('\n', 0, m.start()) + 1
        for i in range(0, len(raw), 4):
            w = int.from_bytes(raw[i:i + 4], 'little'); pc = base + i; op = w & 0x7f
            rd, rs1, f3 = (w >> 7) & 31, (w >> 15) & 31, (w >> 12) & 7
            if w & 3 != 3: brit.append((rel, ln, hex(pc), 'demo %s: a compressed parcel; not re-encoded' % m.group(1))); break
            if op == 0x17: regs[rd] = pc + sx(w >> 12, 20) * 4096; continue
            if op in (0x03, 0x13, 0x23) and rs1 in regs and (op != 0x13 or f3 == 0):
                imm = sx(w >> 20, 12) if op != 0x23 else sx(((w >> 25) << 5) | ((w >> 7) & 31), 12)
                t = regs[rs1] + imm
                if wo <= t < we:
                    ni = t - wo + wn - regs[rs1]
                    if not -2048 <= ni < 2048:
                        brit.append((rel, ln, hex(pc), 'demo %s: the new target %#x needs another auipc' % (m.group(1), t - wo + wn)))
                    else:
                        if op == 0x23: nw = (w & 0x01fff07f) | ((ni & 0xfe0) << 20) | ((ni & 0x1f) << 7)
                        else: nw = (w & 0x000fffff) | ((ni & 0xfff) << 20)
                        out[i:i + 4] = nw.to_bytes(4, 'little'); fix.append((pc, imm, ni, t, t - wo + wn))
                if op != 0x23 and rd in regs: del regs[rd]
                continue
            if op in (0x6f, 0x67): regs = {}
            elif op not in (0x23, 0x63) and rd in regs: del regs[rd]
        if not fix: continue
        text = text[:m.start()] + text[m.start():m.end()].replace(x.group(1), out.hex(), 1) + text[m.end():]
        vals.append((rel, ln, 'code', x.group(1), out.hex(), 'demo-reencode %s: %s' % (m.group(1), ', '.join(
            'pc %#x imm %s -> %s (target %#x -> %#x)' % (pc, hx(oi), hx(ni), t, nt) for pc, oi, ni, t, nt in fix))))
        ms = m.start(); head = text.rfind('(*', 0, ms)
        for pc, oi, ni, t, nt in fix:
            pat = re.compile(r'(?m)^(\s*%#x\s+[^\n]*?)%s(\(\w+\))' % (pc, re.escape(hx(oi))))
            seg = text[head:ms]
            seg2, n = pat.subn(lambda mm: mm.group(1) + hx(ni) + mm.group(2), seg, count=1)
            if n: text = text[:head] + seg2 + text[ms:]; ms += len(seg2) - len(seg)
    return text, vals, brit

def own_step(a, pairs, kit):
    unit = a.unit; rlist = os.path.join(unit, 'provenance/evidence/srcreloc/relocate-list.tsv')
    files = own_files(unit, kit, rlist)
    values, comments, stops, writes, left, brittle = [], [], [], {}, [], []
    for rel in files:
        if rel in (a.leave or []): left.append(rel); continue
        text = open(os.path.join(unit, 'lib', rel)).read()
        fbuild = 'ubsan' if rel.startswith('U/') else 'plain'
        edits = []
        for iscom, base, chunk in split_comments(text):
            seen_auipc = set()
            for m in NUM.finditer(chunk):
                tok = m.group(1); pos = base + m.start()
                v = int(tok, 16) if tok.startswith('0x') else int(tok)
                ln, line = line_of(text, pos)
                b = fbuild
                if not iscom and fbuild == 'plain' and re.search(r'W_BASE_UBSAN|\bubsan\b', line): b = 'ubsan'
                P = pairs[b]
                M64 = 1 << 64
                if not iscom and M64 - P.hi <= v < M64 - P.lo + 1:
                    # (n) the 64-bit complement (~a = 2^64 - 1 - a) or negation (2^64 - a) of an image address a, as
                    # code computes it (xori -1 / sub from 0): moves by the delta of a; both readings must agree
                    ds = set(); why = []
                    for a_, k in ((M64 - 1 - v, 'not'), (M64 - v, 'neg')):
                        if P.lo <= a_ < P.hi:
                            na, rule, det = P.resolve(a_)
                            if na is not None: ds.add(na - a_); why.append('%s %#x (%s: %s)' % (k, a_, rule, det))
                    if len(ds) != 1:
                        stops.append((rel, ln, tok, 'complement / negation of an image address: %s' % (why or 'no reading resolves'))); continue
                    d = ds.pop()
                    if d: edits.append((pos, tok, fmt(tok, v - d)))
                    values.append((rel, ln, 'code', tok, fmt(tok, v - d), 'n: ' + '; '.join(why))); continue
                if not P.lo <= v < P.hi: continue
                if iscom:
                    if not tok.startswith('0x'): continue
                    if 'auipc' in line:
                        if ln in seen_auipc: comments.append((rel, ln, tok, 'auipc line: only its pc moves')); continue
                        seen_auipc.add(ln)
                    new, why = P.comment_ok(v)
                    if new is None: comments.append((rel, ln, tok, why)); continue
                    if new != v: edits.append((pos, tok, fmt(tok, new)))
                    values.append((rel, ln, 'comment', tok, fmt(tok, new), why)); continue
                # code
                if KEEP_DEF.search(line):
                    values.append((rel, ln, 'code', tok, tok, 'k: length / offset definition')); continue
                st = stmt_of(text, pos)
                if re.search(r'\bdemo\w*_segs\b|Module Demo', st):
                    # a machine state of a made-up image: its auipc results stay (demo_reencode keeps every auipc and
                    # moves only the lo12 immediates), so the numeral stays
                    values.append((rel, ln, 'code', tok, tok, 'd: a value of a made-up demo image, not of the pinned image; stays'))
                    continue
                if not tok.startswith('0x'):
                    pre = text[max(0, pos - 14):pos]
                    if not re.search(r'Z_to_bv 64 \(?$', pre):
                        if v in DEC_KEEP: values.append((rel, ln, 'code', tok, tok, 'decimal kept: ' + DEC_KEEP[v])); continue
                        if v < W_LEN_DEC:
                            # (w) an offset into the world B (TWorld.v A_* / OFF_*: below W_LEN, the same in both builds
                            # and both pins); an address there would be in the ELF header page
                            values.append((rel, ln, 'code', tok, tok, 'w: a world offset (< W_LEN), kept')); continue
                        # any other decimal in the image range is an address written in decimal (the walks' rewrite /
                        # change / ret_pc_even / bytes_at arguments): the rules below, as for hex
                if 'segments_reserved' in line:
                    nv = P.reserved_map(v)
                    if nv is None: stops.append((rel, ln, tok, 'segments_reserved value not a reserved base / size')); continue
                    if nv != v: edits.append((pos, tok, fmt(tok, nv)))
                    values.append((rel, ln, 'code', tok, fmt(tok, nv), 's: reserved segment')); continue
                new, rule, det = P.resolve(v)
                if rule in ('o', 'c') and all(v != st for key, st, z in P.containing('O', v)):
                    # inside data but at no symbol start: a register value an auipc computed (the walks state the
                    # registers of a loop: check_latest_sent's s11 = auipc result 0x43790 inside builtin_tls) moves
                    # with the code, not with the data
                    am = P.auipc_move(v)
                    if am is not None:
                        if am[0] is None: stops.append((rel, ln, tok, am[1] + ': ' + line.strip()[:120])); continue
                        new, rule, det = am[0], 'a', am[1]
                if new is None: stops.append((rel, ln, tok, det + ': ' + line.strip()[:120])); continue
                if new != v: edits.append((pos, tok, fmt(tok, new)))
                values.append((rel, ln, 'code', tok, fmt(tok, new), '%s: %s' % (rule, det)))
        new_text = text
        if edits:
            out = []; last = 0
            for pos, tok, rep in sorted(edits):
                out.append(text[last:pos]); out.append(rep); last = pos + len(tok)
            out.append(text[last:]); new_text = ''.join(out)
        new_text, dv, ds = demo_reencode(rel, new_text, pairs[fbuild])
        values += dv; brittle += ds
        if new_text != text: writes[rel] = new_text
    os.makedirs(a.work, exist_ok=True)
    with open(os.path.join(a.work, 'own-values.tsv'), 'w') as f:
        f.write('file\tline\twhere\told\tnew\trule\n')
        for r in values: f.write('\t'.join(map(str, r)) + '\n')
    with open(os.path.join(a.work, 'own-comments-left.tsv'), 'w') as f:
        f.write('file\tline\tnumeral\twhy it stays\n')
        for r in comments: f.write('\t'.join(map(str, r)) + '\n')
    with open(os.path.join(a.work, 'own-brittle.tsv'), 'w') as f:
        f.write('file\tline\tnumeral\twhy\n')
        for r in brittle: f.write('\t'.join(map(str, r)) + '\n')
    for r in brittle: print('BRITTLE %s:%s %s %s' % r)
    moved = sum(1 for r in values if r[3] != r[4])
    print('own: %d files, %d left (--leave), %d image numerals, %d moved (%d code, %d comment), %d comment numerals left, '
          '%d files changed' % (len(files), len(left), len(values), moved, sum(1 for r in values if r[3] != r[4] and r[2] == 'code'),
                                sum(1 for r in values if r[3] != r[4] and r[2] == 'comment'), len(comments), len(writes)))
    for b in ('plain', 'ubsan'):
        for key, vd in sorted(pairs[b].verdicts.items(), key=lambda x: x[0][1]):
            if vd[0] not in ('EQUAL', 'EQUAL-mod-pcrel'): print('own: %s function %s is %s %s' % (b, key[1], vd[0], vd[1]))
    if stops:
        for r in stops: print('STOP %s:%s %s %s' % r)
        print('own: %d stops, nothing written' % len(stops)); return 1
    if not a.dry_run:
        for rel, t in writes.items(): open(os.path.join(a.unit, 'lib', rel), 'w').write(t)
    return 0

# ---------------------------------------------------------------- kit
def k2_run(a, which, plain, ubsan, out):
    if sha(K2) != K2_SHA: raise SystemExit('repin_reloc: %s is not K2 %s' % (K2, K2_SHA[:12]))
    if os.path.exists(out): shutil.rmtree(out)
    os.makedirs(out)
    cmd = [sys.executable, K2] + K2_ARGS + ['--git', a.git, '--pac', a.pac, '--decode-bin', a.decode_bin,
                                            '--donor-bin', a.donor_bin] + ['--month', a.month, '--plain', plain, '--ubsan', ubsan,
                                            '--out', os.path.join(out, 'lib'), '--work', os.path.join(out, 'work')]
    print('kit: K2 %s: %s' % (which, ' '.join(cmd)))
    with open(os.path.join(out, 'run.log'), 'w') as log:
        rc = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, cwd=out,
                            env=dict(os.environ, PYTHONPATH=a.k2_pythonpath)).returncode
    print('kit: K2 %s rc=%d, log %s' % (which, rc, os.path.join(out, 'run.log')))
    return rc

def merge3(ours, base, theirs):
    """line-level 3-way merge: the edits of base->ours and base->theirs applied together when they touch different base
    lines (adjacent edits are fine; an insertion is anchored to its position). Where ours deletes lines that theirs
    only rewrites in place (the same base lines, as many lines: the new K2 output moved a numeral of a header line
    the tree removed, a8ba5c079e62), the deletion wins. None on any other overlap that differs."""
    import difflib
    def edits(x):
        return [(i1, i2, x[j1:j2]) for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, base, x, autojunk=False).get_opcodes()
                if tag != 'equal']
    eo, et = edits(ours), edits(theirs)
    et = [(b1, b2, rb) for b1, b2, rb in et
          if not any(not ra and (a1, a2) == (b1, b2) and len(rb) == b2 - b1 for a1, a2, ra in eo)]
    for a1, a2, ra in eo:
        for b1, b2, rb in et:
            overlap = (a1 < b2 and b1 < a2) or (a1 == a2 == b1 == b2) or (a1 == a2 and b1 < a1 < b2) or (b1 == b2 and a1 < b1 < a2)
            if overlap and not (a1, a2, ra) == (b1, b2, rb): return None
    allx = sorted({(i1, i2, tuple(r)) for i1, i2, r in eo + et})
    out, k = [], 0
    for i1, i2, r in allx:
        out += base[k:i1]; out += list(r); k = i2
    return out + base[k:]

def kit_step(a, k2old, k2new):
    """the new K2 output plus the unit's own post-K2 edits, for every kit file; writes nothing when anything conflicts"""
    lib = os.path.join(a.unit, 'lib'); fo, fn = k2_files(k2old), k2_files(k2new)
    same = edited = 0; conflicts = []; writes = {}; removes = []
    for rel in sorted(fo | fn):
        t = os.path.join(lib, rel); o = os.path.join(k2old, rel); n = os.path.join(k2new, rel)
        if rel not in fn:
            if os.path.exists(t):
                if open(t, 'rb').read() != open(o, 'rb').read(): conflicts.append((rel, 'K2 no longer writes it, and the tree edited it'))
                else: removes.append(rel); print('kit: %s: K2 no longer writes it, removed' % rel)
            continue
        if rel not in fo:
            if os.path.exists(t): conflicts.append((rel, 'new K2 file exists in the tree')); continue
            writes[rel] = open(n, 'rb').read(); print('kit: %s: new K2 file, added' % rel); continue
        if not os.path.exists(t): conflicts.append((rel, 'the tree lacks this K2 file')); continue
        tb, ob, nb = open(t, 'rb').read(), open(o, 'rb').read(), open(n, 'rb').read()
        if tb == ob:
            same += 1
            if tb != nb: writes[rel] = nb
            continue
        edited += 1
        m = merge3(tb.decode().splitlines(True), ob.decode().splitlines(True), nb.decode().splitlines(True))
        if m is None: conflicts.append((rel, 'the post-K2 edits and the new K2 output change the same lines')); continue
        print('kit: %s: the unit\'s post-K2 edits carried onto the new K2 output (%s)' % (rel, 'K2 output unchanged' if ob == nb else 'merged'))
        mb = ''.join(m).encode()
        if mb != tb: writes[rel] = mb
    print('kit: %d K2 files equal to the old K2 output, %d carry post-K2 edits, %d conflicts, %d files to write, %d to remove'
          % (same, edited, len(conflicts), len(writes), len(removes)))
    for rel, why in conflicts: print('STOP kit %s: %s' % (rel, why))
    if conflicts: return 1
    if not a.dry_run:
        for rel, b in writes.items():
            os.makedirs(os.path.dirname(os.path.join(lib, rel)), exist_ok=True); open(os.path.join(lib, rel), 'wb').write(b)
        for rel in removes: os.remove(os.path.join(lib, rel))
    return 0

def geometry(a, pairs, k2new):
    """G1..G4 on the new images and the merged tree"""
    lib = os.path.join(a.unit, 'lib'); bad = 0
    def yh03(rel):
        m = re.search(r'Definition src0_D_debruijn32\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+)', open(os.path.join(k2new, rel)).read())
        return int(m.group(1), 16) if m else None
    top = {b: -(-max(v + z for v, z in pairs[b].loads['N']) // PAGE) * PAGE for b in pairs}
    for b, rel in (('plain', 'Reusable/YL0k.v'), ('ubsan', 'U/Reusable/YL0k.v')):
        t = open(os.path.join(lib, rel)).read()
        ok = top[b] <= 0x64000 and t.count('0x64000') == 3
        print('geometry G1 %s: last PT_LOAD end rounded up to a page %#x <= image top 0x64000 used 3 times in %s: %s'
              % (b, top[b], rel, 'OK' if ok else 'FAILS')); bad += not ok
    res = pairs['ubsan'].reserved('N')
    ok = all((v - 0x10000) % 0x1000 == 0 for v, z in res)
    print('geometry G2 ubsan reserved segments %s on a 0x1000 grid: %s' % ([(hex(v), hex(z)) for v, z in res], 'OK' if ok else 'FAILS'))
    bad += not ok
    I = pairs['plain'].I['N']; deb = yh03('Reusable/YH03.v')
    def fs(n):
        c = [(v, z) for v, z, t in I.byname.get(n, []) if t == 'STT_OBJECT']
        return c[0] if c else (None, None)
    scv, scz = fs('__malloc_size_classes'); smv, smz = fs('small_cnt_tab'); mdv, mdz = fs('med_cnt_tab')
    ok = (deb is not None and scv is not None and scv - deb == 208 and (scz, smz, mdz) == (96, 27, 4)
          and smv == scv + 96 and mdv == smv + 27)
    print('geometry G3 plain DEB %s size_classes %s/%s small_cnt_tab %s/%s med_cnt_tab %s/%s: DEB+208, 127 contiguous: %s'
          % (deb and hex(deb), scv and hex(scv), scz, smv and hex(smv), smz, mdv and hex(mdv), mdz, 'OK' if ok else 'FAILS'))
    bad += not ok
    for rel, yrel in (('FrameAPI.v', 'Reusable/YH03.v'), ('U/FrameAPI.v', 'U/Reusable/YH03.v')):
        d = yh03(yrel); t = open(os.path.join(lib, rel)).read()
        got = set(int(x, 16) for x in re.findall(r'ms_debruijn B = (0x[0-9a-fA-F]+)', t))
        ok = d is not None and got == {d}
        print('geometry G4 %s ms_debruijn %s = %s src0_D_debruijn32 %s: %s' % (rel, sorted(map(hex, got)), yrel, d and hex(d), 'OK' if ok else 'FAILS'))
        bad += not ok
    return 1 if bad else 0

# ---------------------------------------------------------------- main
def pin(s):
    p, t = s.split(':', 1)
    return p, t

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('mode', choices=('all', 'own', 'kit'))
    ap.add_argument('--unit', required=True)
    ap.add_argument('--kit', required=True, help='the comparison kit directory (cmpkit 4bbd3a74be89)')
    for k in ('old-plain', 'old-ubsan', 'new-plain', 'new-ubsan'): ap.add_argument('--' + k)
    ap.add_argument('--work', default=os.path.join(HERE, 'work'))
    ap.add_argument('--leave', action='append', default=[])
    ap.add_argument('--k2-old'); ap.add_argument('--k2-new'); ap.add_argument('--k2-lib')
    ap.add_argument('--git', help='a git clone holding the donor refs (all: K2 and the src step)')
    ap.add_argument('--pac', help='port_addr_check.py frozen at 5033540ba83b (K2)')
    ap.add_argument('--decode-bin', help='dir with bin/fuzz_decode/ and unstripped/fuzz_decode/, the decode pins (K2)')
    ap.add_argument('--donor-bin', help='dir with the second donors\' pins (K2)')
    ap.add_argument('--k2-pythonpath', help='PYTHONPATH of the K2 run (a pyelftools install)')
    ap.add_argument('--src-unstripped', help='relocate.py --unstripped: dir with <unit>/<unit>.{plain,ubsan} twins (src step)')
    ap.add_argument('--month', default='2026-10')
    ap.add_argument('--dry-run', action='store_true')
    a = ap.parse_args()
    global KIT, sc
    cd.load_kit(a.kit); KIT, sc = cd.KIT, cd.sc
    if a.mode == 'all':
        need = ['git', 'src_unstripped'] + ([] if a.k2_old and a.k2_new else ['pac', 'decode_bin', 'donor_bin', 'k2_pythonpath'])
        miss = ['--' + k.replace('_', '-') for k in need if not getattr(a, k)]
        if miss: raise SystemExit('repin_reloc: all needs %s' % ' '.join(miss))
    a.unit = os.path.abspath(a.unit); os.makedirs(a.work, exist_ok=True)
    for k in ('old_plain', 'old_ubsan', 'new_plain', 'new_ubsan'):
        if getattr(a, k): print('pin %s %s' % (k, '  '.join('%s sha256 %s' % (p, sha(p)) for p in pin(getattr(a, k)))))
    def pairs():
        return {b: Pair(b, pin(getattr(a, 'old_' + b))[1], pin(getattr(a, 'new_' + b))[1]) for b in ('plain', 'ubsan')}
    if a.mode == 'own':
        return own_step(a, pairs(), k2_files(a.k2_lib))
    if a.mode == 'kit':
        rc = kit_step(a, a.k2_old, a.k2_new)
        return rc or geometry(a, pairs(), a.k2_new)
    # all
    k2old = a.k2_old or os.path.join(a.work, 'k2-old', 'lib')
    if not a.k2_old and k2_run(a, 'old (control)', a.old_plain, a.old_ubsan, os.path.join(a.work, 'k2-old')): return 1
    k2new = a.k2_new or os.path.join(a.work, 'k2-new', 'lib')
    if not a.k2_new and k2_run(a, 'new', a.new_plain, a.new_ubsan, os.path.join(a.work, 'k2-new')): return 1
    if kit_step(a, k2old, k2new): return 1
    P = pairs()
    if geometry(a, P, k2new): return 1
    # K2's evidence tables of record (provenance/evidence/kit-relocation/MANIFEST) follow the new run
    ev = os.path.join(a.unit, 'provenance/evidence/kit-relocation')
    for f, g in (('k2-values.tsv', 'values.tsv'), ('k2-conflicts.tsv', 'conflicts.tsv'), ('k2-cells.tsv', 'cells.tsv')):
        src = os.path.join(os.path.dirname(k2new), 'work', f)
        if os.path.exists(src) and not a.dry_run: shutil.copyfile(src, os.path.join(ev, g)); print('kit: %s <- %s' % (os.path.join(ev, g), src))
    # own before src/: srcreloc's S4 requires the T files it shares (U/Prog/T/TContract.v RELRO_BASE) to be at the new
    # pins already (measured: on the old T tree it stops "RELRO_BASE would be 0x21ef8, TContract.v RELRO_BASE is 0x21f10")
    if own_step(a, P, k2_files(k2new)): return 1
    carry = src_edited(a)
    if carry is None: return 1
    rel = os.path.join(a.unit, 'provenance/evidence/srcreloc/relocate.py')
    (pp, pt), (up, ut) = pin(a.new_plain), pin(a.new_ubsan)
    cmd = [sys.executable, rel, '--git', a.git, '--unstripped', a.src_unstripped, '--out', a.unit, '--month', a.month,
           '--target-plain', '%s:%s' % (pp, pt),
           '--target-ubsan', '%s:%s' % (up, ut)] + (['--dry-run'] if a.dry_run else [])
    print('src: ' + ' '.join(cmd))
    with open(os.path.join(a.work, 'srcreloc.log'), 'w') as log:
        rc = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT).returncode
    print('src: relocate.py rc=%d, log %s' % (rc, os.path.join(a.work, 'srcreloc.log')))
    if rc: return 1
    return 0 if a.dry_run else src_carry(a, carry)

def src_edited(a):
    """the src/ files the tree edited after srcreloc wrote them (a srcreloc/relocate-list.tsv row relocated / rewritten
    whose file's sha256 is no longer the row's): {the row's path: (the tree's text, srcreloc's text the edit started
    from)}. The latter is the newest git blob of that path whose sha256 is the row's. None (a STOP) when it is not
    found."""
    rlist = os.path.join(a.unit, 'provenance/evidence/srcreloc/relocate-list.tsv'); out = {}; bad = 0
    top = subprocess.run(['git', '-C', a.unit, 'rev-parse', '--show-toplevel'], capture_output=True, text=True).stdout.strip()
    for l in open(rlist):
        f = l.split()
        if len(f) < 3 or not f[0].startswith('lib/') or f[1] not in ('relocated', 'rewritten'): continue
        p = os.path.join(a.unit, f[0])
        if not os.path.exists(p) or sha(p) == f[2]: continue
        base = None
        if top:
            gp = os.path.relpath(p, top)
            revs = subprocess.run(['git', '-C', top, 'rev-list', 'HEAD', '--', gp], capture_output=True, text=True).stdout.split()
            for r in revs:
                blob = subprocess.run(['git', '-C', top, 'show', '%s:%s' % (r, gp)], capture_output=True).stdout
                if hashlib.sha256(blob).hexdigest() == f[2]: base = blob.decode(); break
        if base is None:
            print('STOP src %s: edited after srcreloc, and no git blob of it has the relocate-list.tsv sha256 %s' % (f[0], f[2][:12])); bad += 1
            continue
        out[f[0]] = (open(p).read(), base)
        print('src: %s: edited after srcreloc (sha256 %s, relocate-list.tsv %s); the edit is carried onto the new output'
              % (f[0], sha(p)[:12], f[2][:12]))
    return None if bad else out

def src_carry(a, carry):
    """the tree's post-srcreloc edits onto relocate.py's new output (the line-level 3-way merge of the kit step); a
    conflict STOPS the run (relocate.py has written its files then: `git checkout` the unit to retry)"""
    bad = 0
    for rel, (ours, base) in sorted(carry.items()):
        p = os.path.join(a.unit, rel); theirs = open(p).read()
        m = merge3(ours.splitlines(True), base.splitlines(True), theirs.splitlines(True))
        if m is None: print('STOP src %s: the post-srcreloc edits and the new output change the same lines' % rel); bad += 1; continue
        open(p, 'w').write(''.join(m))
        print('src: %s: post-srcreloc edits carried (%s)' % (rel, 'srcreloc output unchanged' if base == theirs else 'merged'))
    return 1 if bad else 0

if __name__ == '__main__':
    sys.exit(main())
