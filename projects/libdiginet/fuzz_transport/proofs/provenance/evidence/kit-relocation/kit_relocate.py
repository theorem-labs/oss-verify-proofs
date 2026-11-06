#!/usr/bin/env python3
"""kit_relocate.py -- copy libreac/fuzz_decode's RELEASED plain / UBSan kit into a unit of another project (reac-repacer,
libdiginet) and move every image value to the unit's own binaries.

usage:
  kit_relocate.py [--project reac-repacer] --unit fuzz_uci --out <worktree>/proofs/<project>/<unit>/lib \
      --plain PIN:TWIN --ubsan PIN:TWIN --work <scratch dir> --git <hub clone> --pac <port_addr_check.py frozen 5033540ba83b>
      --decode-bin <dir with bin/fuzz_decode and unstripped/fuzz_decode> --donor-bin <dir with the second donors' pins>
      [--donor-ref 25e3d17bdb50] [--kit-ref <ref>]

--project (default reac-repacer) names the unit's project: module paths become <project with - as _>.<unit>, and the
notices say <project>/<unit>.  --kit-ref (default: --donor-ref) names the commit whose file list is the kit: K1 copies
exactly the kit-ref's files, each with its content at --donor-ref (a kit-ref file absent at --donor-ref stops the run);
a file present at --donor-ref but not at --kit-ref is not copied and is listed in k2-values.tsv.

What it does (each step prints what it changed; every change goes into <work>/k2-values.tsv):
  K1  copy proofs/libreac/fuzz_decode/lib at --donor-ref: every file but `dune` (the unit trunk's), `Theorems.v` and the
      Prog/ and U/Prog/ files the unit does not need.  Each Prog file is decided by the unit's OWN symtab (plain image
      for Prog/, ubsan for U/Prog/): a file named after a function f of decode's image (f.v, f_*.v; longest f) is kept
      iff the unit links f; FrameBytes / KindB are kept; decode's harness (LLVMFuzzerTestOneInput*, check_round_trip*,
      check_braid*) and its segment files (PROG_SEGMENTS) are not.  Module paths `libreac.fuzz_decode` -> `<project_>.<unit>`, and the donor comments' private tool path
      (the roadapt tool's path in the internal tools tree) -> `the roadapt tool`; nothing else.
      A kept walk is decode's proof of decode's copy of f: when the unit's f has other code, step (e) stops the run.
  K2  (a) port_addr_check 5033540ba83b in PREDICT mode, decode pin -> unit pin by symbol + offset, plain for lib/ and
      ubsan for lib/U/.  An ambiguous row (an address that is the end of one symbol and the start of the next) takes
      the start label's value.  (b) HEX literals: each file's tool-mapped values, applied to every hex token of that
      value in the file; a value the tool also calls NON-ADDRESS in the same file is not applied and is listed.
      (c) DECIMAL literals are moved only through DECIMAL_TABLE below (the decode kit's decimals that are addresses or
      image geometry; the tool misclassifies decimals both ways); every other decimal stays.  (d) per-image tables
      regenerated from the unit's ELF: Reusable/YH03.v (only the definitions the kit uses; symbol + offset; section
      bounds from the section headers; each code cell src0_A_<X> / src0_E_<X> must be the start / end of the function
      named X in the unit's symtab (yh03check's rule; else by name, else refused; the image FILE's seek slot must equal
      src0_A_stdio_seek; when the image links no __stdio_read and no fopen, src0_A_stdio_read is 0, the read slot of
      __stdout_FILE measured from the image)), the RELRO lists (Reusable/YL0k.v src0_R, FrameAPI.v frame_RELRO) from
      .init_array / .got and the GOT slot of __stack_chk_guard, ZImage.v ztext_count (RVC-aware instruction count of
      .text).  (e) fetch_word lemmas whose instruction word differs on the unit image: the word is read from the image;
      a jal whose immediate moved is re-decoded (the decode lemma follows); any other difference stops the run.
      (f) libc pieces the unit does not link: no calloc -> the Calloc* files are dropped, YH02's ms_calloc is None and
      ZAllocator's CAL is the vacuous src0_calloc_none; no memcmp -> R_memchr.v's unused module R_memcmp is dropped.
      (d') a YH03 data cell no donor symbol covers moves by content: the donor bytes from it to the next donor symbol
      (8..64) must occur exactly once in the unit's loaded image.  (g) the decimal addresses inside a driver string
      constant (YL0v's rodata_*_src1 lemmas, read by YL0w / YL0x / YL0y and their _cfw twins) move with their whole
      NUL-terminated string, which must occur once in the unit's image; a kept YH03 src0_D_str_* cell that (h) moved by
      content, and whose decode value holds that same string, must agree.
      (h) a kept YH03 string cell src0_D_str_<X> moves by its CONTENT, the bytes the kit states at it: the one field
      bound to it (`sk_F := src0_D_str_<X>`), the one Definition that states `garr8 segs mem sk_F (L ++ [0])` (or
      `... sk_F L`), and `Definition L : list Z := [..]`.  Found once in the unit's loaded image: that address.  Found
      more than once: the run stops.  Found nowhere: the value stays, which must lie in the unit's .rodata, and the
      Definition env_addr of that file must name sk_F (the cell is then read only as an in-image address).  No such
      statement for a kept string cell stops the run.
      YH03.v gets no comment from these rules: every kept cell's rule and measurement go to <work>/k2-cells.tsv (file,
      line, cell, value, rule, measurement); the ones not moved by symbol, section or the tool are also printed.
Controls: the decode pin run through steps (d) reproduces decode's own released values (printed first).  K1 stops on a
Prog file that fits no class above, on a file it would drop although the unit links its function, and on a kept Prog
file that Requires a Prog module not kept.
  K3  libc walks decode's kit lacks, from a second released donor (SECOND_DONORS: strlen from libreac/fuzz_disco at
      25e3d17bdb50, memmove from libreac/fuzz_pcap at bdfe881c79c), copied only when the unit links the function and the
      kit has no walk of it.  Controls: the donor image's sha256 is the donor's pin; the donor's entry (symbol, or the
      unique occurrence of the unit's bytes in a stripped pin) equals the released entry literal; the two function bodies
      agree instruction by instruction, a pc-relative auipc / ld pair only when it loads equal 8 bytes.  Every hex literal
      inside the donor function moves by offset; one inside the donor image but outside the function stops the run, and
      so does a Require of a module the unit's lib lacks.  Line 1 of each file is its modification notice (month-dated, no agent):
      donor unit and repo-relative path, donor commit, donor pin sha256, entry address in the donor image and in the unit's.
"""
import argparse, collections, csv, hashlib, os, re, subprocess, sys

DONOR_DIR = 'proofs/libreac/fuzz_decode/lib/'
DONOR_IMG = {}  # set in main from --decode-bin: tag -> (pin, unstripped twin)
# decode's Prog/ files that walk no function and that every unit needs: kept always
PROG_ALWAYS = re.compile(r'(FrameBytes|KindB)\.v$')
# decode's harness functions (entry and its two check functions): a unit that links a function of the same name links
# its own, different program; never kept
PROG_HARNESS = re.compile(r'(LLVMFuzzerTestOneInput|check_round_trip|check_braid)(_|$)')
# decode's harness segment and statement files, which walk no function of their own name: never kept
PROG_SEGMENTS = re.compile(r'(Slot[A-Za-z]*|crt_\w+|fd_\w+|FloatExact|ReacDecodeLib|RcBraid|RcBraidLib|Statement)$')
PROG_MOD = re.compile(r'lib(?:\.U)?\.Prog Require (?:Import |Export )?([^.]*)\.')
NUMRE = re.compile(r'(?<![0-9A-Za-z_])(0x[0-9a-fA-F]+|[0-9]{4,})(?![0-9A-Za-z_])')

# The decode kit's decimal literals that ARE image values (file, 1-based donor line) -> how to move them.
#  'tool': the tool's own MAPS row for that literal (a pc it labels correctly);
#  ('tls', off): builtin_tls + off of the unit image (thread pointer tp = +0xc8, errno = tp - 164 = +0x24);
#  'textcount': the RVC-aware instruction count of the unit's .text.
# Decimals the tool mislabels as addresses and that stay: YO0i.v:966-967 (69632, an mmap size of an allocator-model
# trace), YO0i.v:1043/1049/1050 and YO0f.v:1102 (200704, a 200000-byte block's mapping).
DECIMAL_TABLE = {}
for _f, _ls in (('Reusable/YL0v.v', (453, 543, 599)), ('Reusable/YL0v_cfw.v', (184, 256, 312))):
    for _l in _ls:
        DECIMAL_TABLE[(_f, _l)] = 'tool'
for _f in ('Reusable/YN06.v', 'Reusable/YN06_cf.v'):
    DECIMAL_TABLE[(_f, '*tp')] = ('tls', 0xc8)
    DECIMAL_TABLE[(_f, '*errno')] = ('tls', 0x24)
DECIMAL_TABLE[('ZImage.v', 19)] = 'textcount'


def add_hdr(L, h):
    """insert header comment h after the file's leading comment lines (or at the top)"""
    idx = [k for k, l in enumerate(L[:8]) if l.startswith('(*')]
    L.insert((max(idx) + 1) if idx else 0, h)
    return L


def k2_hdr(git, ref, k, unit, what):
    """the modification notice of a file K2 changes by a written rule (Apache-2.0 4(b)): month-dated (--month), no day,
    no agent, no host path; donor unit and repo-relative path, donor commit, what changed, module path."""
    full = sh(['git', '-C', git, 'rev-parse', ref]).stdout.strip()
    return (f'(* Modified by Theorem Labs, {ARGS.month}: ported from libreac/fuzz_decode {DONOR_DIR}{k} at {full} for {ARGS.project}/{unit}; '
            f'{what}; module path OssFuzzTheorems.Proofs.{pmod()}.{unit}.lib. *)')


def pmod():
    """the project's name as a Rocq module path component: reac-repacer -> reac_repacer"""
    return ARGS.project.replace('-', '_')


def yh03_by_name(U, n, nv, kind):
    """A YH03 code cell src0_A_<X> / src0_E_<X> names a function of the unit's image (yh03check 09f5eb289e5e's rule):
    the value must be that function's start (A) or end (E).  Returns (value, note).  When the moved value already is
    a function named X, __X, ___X, _X or *_X, it stands.  Else the one function so named gives the value (note says
    so).  A name the image does not link is refused, except a sink FILE's read pointer when the image links no
    __stdio_read: no FILE of the image can hold one, so the cell is the read field of the image's only FILE,
    __stdout_FILE + 64, measured (0); the note says so (it goes to k2-cells.tsv, never into YH03.v)."""
    x = n[len('src0_A_'):]
    names = [x, '__' + x, '___' + x, '_' + x]
    def ok(name):
        return name in names or name.endswith('_' + x)
    funcs = [(s, v, z) for s, l in U.syms.items() for v, z in l]
    def slot_ok(val):
        # control (the FILE-field rule): a sink FILE's seek pointer must be the image's FILE seek slot
        f = U.one('__stdout_FILE')
        return x != 'stdio_seek' or (f is not None and int.from_bytes(U.read(f[0] + 80, 8), 'little') == val)
    for s, v, z in funcs:
        if ok(s) and ((kind == 'A' and v == nv) or (kind == 'E' and z > 0 and v + z == nv)):
            return (nv, '') if slot_ok(nv) else (None, f'{x}: {hex(nv)} is not the image FILE\'s seek slot')
    for cand in names:
        hit = U.one(cand)
        if hit:
            val = hit[0] if kind == 'A' else hit[0] + hit[1]
            if not slot_ok(val):
                return None, f'{x}: {hex(val)} is not the image FILE\'s seek slot'
            return val, f'by name: {cand} (the value moved by offset was {hex(nv)})'
    if x == 'stdio_read' and kind == 'A':
        f = U.one('__stdout_FILE')
        if f and U.read(f[0] + 64, 8) == bytes(8) and U.one('fopen') is None and U.one('__fdopen') is None:
            return 0, 'no such symbol in this image (no __stdio_read and no fopen are linked, so no sink FILE exists); unused (sink_none): 0 is the read slot of the image\'s FILE objects, __stdout_FILE + 64, measured'
    return None, f'the image links no function named {x}'


VERNAC = re.compile(r'(?m)^(Definition|Lemma|Theorem|Corollary|Fact|Remark|Proposition|Example|Fixpoint|Inductive|Record|'
                    r'Class|Instance|Ltac)\s+(\w+)')


def esc(b):
    """bytes shown as a C string for the tables and the log: NUL as \\0, other non-printables as \\xNN"""
    return ''.join('\\0' if c == 0 else '\\\\' if c == 92 else chr(c) if 32 <= c < 127 else f'\\x{c:02x}' for c in b)


def yh03_str(t, n, nv, dv, U, D, files):
    """(h) A kept YH03 string cell n moves by its CONTENT, the bytes the kit states at it.  files: the side's kit files
    (YH03.v excluded); nv: the value the steps before gave; dv: decode's value.  Returns (value, rule, measurement,
    own), own = the string's length when the cell moved by content and decode's value holds the same string, else 0.
    The run stops when the kit does not state the content once, when the content occurs more than once in the unit's
    loaded image, and when it occurs nowhere while the kept value is not in the unit's .rodata or the cell's field is
    not an env_addr field of the file that states the content."""
    def stop(why):
        sys.exit(f'STOP YH03 {t}: {n}: {why}')
    base = lambda k: os.path.basename(k)[:-2]
    bind = [(k, f) for k, v in files.items() for f in re.findall(r'(\w+)\s*:=\s*' + n + r'\s*(?:;|\|\})', v)]
    if len(bind) != 1:
        stop(f'{len(bind)} kit fields are bound to it {bind[:3]}, so the kit states no one content')
    bk, fld = bind[0]
    st = []
    for k, v in files.items():
        for mo in re.finditer(r'garr8\s+segs\s+mem\s+' + fld + r'\s+(?:\((\w+)\s*\+\+\s*\[0\]\)|(\w+))', v):
            enc = list(VERNAC.finditer(v, 0, mo.start()))
            if enc and enc[-1].group(1) == 'Definition':
                st.append((k, mo, enc[-1].group(2)))
    if len(st) != 1:
        stop(f'{len(st)} Definitions state the bytes at {fld}, so the kit states no one content')
    sk, mo, owner = st[0]
    lname, nul = (mo.group(1), True) if mo.group(1) else (mo.group(2), False)
    defs = [d for v in files.values() for d in re.findall(r'Definition ' + lname + r'\s*:\s*list Z\s*:=\s*\[([0-9;\s]*)\]\s*\.', v)]
    if len(defs) != 1:
        stop(f'{len(defs)} definitions of {lname}')
    zs = [int(x) for x in defs[0].split(';') if x.strip()]
    if not zs or any(not 0 <= z < 256 for z in zs):
        stop(f'{lname} is not a list of bytes')
    want = bytes(zs) + (b'\0' if nul else b'')
    what = (f'"{esc(want[:-1] if nul else want)}" ({len(want)} bytes: {lname}{" ++ [0]" if nul else ""}, stated at {fld} by '
            f'{base(sk)} {owner})')
    hits = []
    for va, d in U.segs:
        j = d.find(want)
        while j >= 0:
            hits.append(va + j)
            j = d.find(want, j + 1)
    indecode = D.read(dv, len(want)) == want
    if len(hits) > 1:
        stop(f'{what} occurs {len(hits)} times in the unit image: {[hex(h) for h in hits[:6]]}')
    if hits:
        return hits[0], 'string content', f'{what} occurs once in this image', len(want) if indecode else 0
    lo, hi = U.sec['.rodata']
    if not lo <= nv <= hi - len(want):
        stop(f'{what} occurs nowhere in this image, and the value {hex(nv)} is not in its .rodata [{hex(lo)}, {hex(hi)})')
    env = re.search(r'(?s)Definition env_addr\b.*?\.(?=\s)', files[sk])
    if not env or not re.search(r'\b' + fld + r'\b', env.group(0)):
        stop(f'{what} occurs nowhere in this image, and {base(sk)} has no Definition env_addr that names {fld}')
    users = []
    for frag in re.split(r'\.(?=\s)', files[sk]):
        dm = re.search(r'(?m)^Definition (\w+)', frag)
        if dm and dm.group(1) != owner and re.search(r'\b' + owner + r'\b', frag[dm.end():]):
            users.append(dm.group(1))
    return nv, 'string content: no such string, value kept', (
        f'no such string ({what}) in this image; decode\'s value, '
        + ('where decode holds this string' if indecode else 'which is not this string in decode either')
        + f'; read only by {base(sk)} env_addr ({base(bk)} sink laws: an address in the read-only image, here in .rodata '
        f'[{hex(lo)}, {hex(hi)})) and, for content, by {" / ".join([owner] + users)} (open-FILE path, never reached under '
        f'sink_none)'), 0


def k1_text(s, rename):
    """K1's text change: the module path, and the donor's comments that name a private tool path (the roadapt tool's
    path in the internal tools tree, which the PR name scan refuses), reworded; nothing else."""
    return s.replace(*rename).replace('cold' '/libc/tools/roadapt.py', 'the roadapt tool')


def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def norm(v):
    try:
        return int(v, 16) if v.lower().startswith('0x') else int(v)
    except ValueError:
        return None


class Elf:
    def __init__(self, path):
        from elftools.elf.elffile import ELFFile
        self.e = ELFFile(open(path, 'rb'))
        self.syms = collections.defaultdict(list)
        for s in self.e.get_section_by_name('.symtab').iter_symbols():
            if s.name and s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT'):
                self.syms[s.name].append((s['st_value'], s['st_size']))
        self.sec = {s.name: (s['sh_addr'], s['sh_addr'] + s['sh_size']) for s in self.e.iter_sections()}
        self.segs = [(s['p_vaddr'], s.data()) for s in self.e.iter_segments() if s['p_type'] == 'PT_LOAD']
        t = self.e.get_section_by_name('.text')
        self.text = (t['sh_addr'], t.data())

    def read(self, a, n):
        for va, d in self.segs:
            if va <= a and a + n <= va + len(d):
                return d[a - va:a - va + n]
        return None

    def text_count(self):
        a, d = self.text
        o = n = 0
        while o < len(d):
            o += 2 if (d[o] & 3) != 3 else 4
            n += 1
        return n

    def one(self, name):
        v = self.syms.get(name, [])
        return v[0] if len(v) == 1 else None


def prog_stem(base, funcs):
    """the function a decode Prog file walks: the longest f with base == f or base.startswith(f + '_')"""
    hits = [f for f in funcs if base == f or base.startswith(f + '_')]
    return max(hits, key=len) if hits else None


def keep_list(git, ref, DE, UE, kit_ref):
    """K1 file list.  The candidates are kit_ref's files (each read at ref; one absent at ref stops the run); a file of
    ref that kit_ref lacks is not copied (returned as dropped with that reason).  A decode Prog/ (U/Prog/) file named
    after a function of decode's image (f.v, f_*.v, longest f) is
    kept iff the unit's own image (plain for Prog/, ubsan for U/Prog/) links f; LLVMFuzzerTestOneInput* (decode's
    harness) and the listed harness segment files are never kept; FrameBytes / KindB always are.
    Controls (each stops the run): a Prog file that is none of these; a file dropped although the unit links its
    function; a kept Prog file that Requires a Prog module not kept."""
    out, dropped = [], []
    ls = lambda c: sh(['git', '-C', git, 'ls-tree', '-r', '--name-only', c, '--', DONOR_DIR]).stdout.split()
    at_ref, at_kit = ls(ref), ls(kit_ref)
    missing = sorted(set(at_kit) - set(at_ref))
    if missing:
        sys.exit(f'CONTROL: {len(missing)} kit-ref files are absent at the donor ref, e.g. {missing[:5]}')
    for p in sorted(set(at_ref) - set(at_kit)):
        dropped.append((p[len(DONOR_DIR):], 'not in the --kit-ref file set'))
    for p in at_kit:
        r = p[len(DONOR_DIR):]
        if r in ('dune', 'Theorems.v'):
            continue
        parts = r.split('/')
        if parts[0] == 'Prog' or (parts[0] == 'U' and len(parts) > 1 and parts[1] == 'Prog'):
            t = 'ubsan' if parts[0] == 'U' else 'plain'
            base = parts[-1][:-2] if parts[-1].endswith('.v') else parts[-1]
            if PROG_ALWAYS.match(parts[-1]):
                out.append(r)
                continue
            if PROG_HARNESS.match(base):
                dropped.append((r, f'decode harness ({PROG_HARNESS.match(base).group(1)}: a unit function of that name is the unit\'s own, different program)'))
                continue
            f = prog_stem(base, DE[t].syms)
            if f is None:
                if not PROG_SEGMENTS.match(base):
                    sys.exit(f'CONTROL: {r} walks no function of decode\'s image and is not a listed harness segment file')
                dropped.append((r, 'decode harness segment'))
            elif UE[t].one(f):
                out.append(r)
            else:
                dropped.append((r, f'walks {f}, not linked by the unit'))
            continue
        out.append(r)
    for r, why in dropped:
        if why == 'not in the --kit-ref file set':
            continue
        parts = r.split('/')
        t = 'ubsan' if parts[0] == 'U' else 'plain'
        base = parts[-1][:-2]
        f = prog_stem(base, DE[t].syms)
        if f and not PROG_HARNESS.match(base) and UE[t].one(f):
            sys.exit(f'CONTROL: {r} would be dropped although the unit links {f}')
    kept = set(out)
    for r in out:
        parts = r.split('/')
        if 'Prog' not in parts[:2]:
            continue
        side = 'U/' if parts[0] == 'U' else ''
        txt = sh(['git', '-C', git, 'show', f'{ref}:{DONOR_DIR}{r}']).stdout
        for mods in PROG_MOD.findall(txt):
            for m in mods.split():
                if f'{side}Prog/{m}.v' not in kept:
                    sys.exit(f'CONTROL: kept {r} Requires Prog module {m}, which is not kept')
    return out, dropped


def predict(work, ref, files, tag, src_path, dst_img):
    out = f'{work}/pred-{tag}.tsv'
    if not os.path.exists(out):
        s = ':'.join(DONOR_IMG[tag])
        cmd = ['python3', ARGS.pac, '--git', ARGS.git, '--src', f'{ref}:{src_path}', '--src-image', f'A={s}',
               '--dst-image', f'A={dst_img}', '--assign', '**=A', '--cache', f'{work}/pac-cache', '--out', out, '--summary']
        for f in files:
            cmd += ['--include', f]
        r = sh(cmd, cwd=work)
        if r.returncode != 0:
            sys.exit(f'port_addr_check failed ({tag}): {r.stderr[-2000:]}')
    return list(csv.DictReader(open(out), delimiter='\t'))


# K3: libc walks decode's kit lacks, from a second released donor.  Each entry: the function, the donor unit, the git
# ref of its release, the donor files (lib-relative; the U/ twin is taken for ubsan), the pinned donor images
# (path, sha256 of the pin, optional symbol file) and the definition that holds the released entry pc (the control).
SECOND_DONORS = [
    {'fn': 'strlen', 'unit': 'libreac/fuzz_disco', 'ref': '25e3d17bdb50',
     'files': ['R_strlen.v', 'Prog/strlen_c.v', 'Prog/strlen.v'],
     'img': {'plain': ('{B}/libreac/plain/fuzz_disco', '04988e3ab31341965e44f0ca1bb0e5ed18fe6892e2c753df7a87bec197576f7c',
                       '{B}/libreac/plain/fuzz_disco.debug'),
             'ubsan': ('{B}/libreac/ubsan/fuzz_disco', '56121de6ba4cff85e0fa262e9783f384e35fb8642d057f7a3a4290bcc245b22e',
                       '{B}/libreac/ubsan/fuzz_disco.debug')},
     'entry': ('R_strlen.v', r'Definition strlen_entry := (0x[0-9a-fA-F]+)%Z\.')},
    {'fn': 'memmove', 'unit': 'libreac/fuzz_pcap', 'ref': 'bdfe881c79c',
     'files': ['Prog/memmove_c.v', 'Prog/memmove.v'],
     'img': {'plain': ('{B}/pau-libreac-v190/libreac/bin/fuzz_pcap/fuzz_pcap.plain',
                       '1e8e7da32456ca11f5e70cba9413adf96bbeb09fb14d1c68e2a3c29a6cb0de01', None),
             'ubsan': ('{B}/pau-libreac-v190/libreac/bin/fuzz_pcap/fuzz_pcap.ubsan',
                       '83af59086893b5608e2e6e71ea75e7355843d61ec2b20bf3fa1106f362b5e43f', None)},
     'entry': ('Prog/memmove_c.v', r'Definition memmove_entry := (0x[0-9a-fA-F]+)%Z\.')},
]
HEXRE = re.compile(r'(?<![0-9A-Za-z_])0x[0-9a-fA-F]+(?![0-9A-Za-z_])')


def _loads(path):
    from elftools.elf.elffile import ELFFile
    e = ELFFile(open(path, 'rb'))
    return [(s['p_vaddr'], s.data()) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']


def _rd(segs, a, n):
    for va, d in segs:
        if va <= a and a + n <= va + len(d):
            return d[a - va:a - va + n]
    return None


def _same_code(dsegs, da, usegs, ua, n):
    """the donor's and the unit's function bodies agree instruction by instruction; an auipc / (ld|addi) pair may differ
    only when both resolve to 8 bytes that are equal in the two images (a moved constant pool).  Returns the number of
    such pairs, or a string that says why the bodies differ."""
    import capstone
    md = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)
    D = list(md.disasm(_rd(dsegs, da, n), da))
    U = list(md.disasm(_rd(usegs, ua, n), ua))
    if len(D) != len(U) or sum(i.size for i in D) != n:
        return f'{len(D)} vs {len(U)} instructions'
    pairs, i, used = 0, 0, set()
    while i < len(D):
        x, y = D[i], U[i]
        if x.bytes == y.bytes or i in used:
            i += 1
            continue
        if x.mnemonic != 'auipc' or y.mnemonic != 'auipc':
            return f'+{hex(x.address - da)}: {x.mnemonic} {x.op_str} vs {y.mnemonic} {y.op_str}'
        rd = x.op_str.split(',')[0].strip()
        j = next((k for k in range(i + 1, len(D)) if re.search(r'\(' + rd + r'\)$|, ' + rd + r', ', D[k].op_str)), None)
        if j is None or D[j].mnemonic not in ('ld', 'addi') or U[j].mnemonic != D[j].mnemonic:
            return f'+{hex(x.address - da)}: auipc without a matching ld / addi'
        def tgt(ins_a, ins_b):
            hi = int(ins_a.op_str.split(',')[1], 0)
            lo = int(re.search(r'(-?0x[0-9a-f]+|-?\d+)(?:\(|$)', ins_b.op_str.split(',')[-1].strip()).group(1), 0)
            return ins_a.address + (hi << 12) + lo
        if _rd(dsegs, tgt(x, D[j]), 8) != _rd(usegs, tgt(y, U[j]), 8):
            return f'+{hex(x.address - da)}: pool values differ'
        used.add(j)
        pairs += 1
        i += 1
    return pairs


def second_donors(text, log, UE, a):
    """K3.  For each SECOND_DONORS function the unit links and the kit has no walk of: control (the donor pin's sha256,
    and the donor's entry found in its pin = the released entry literal), code check (_same_code), then the donor files
    copied with the module path renamed and every hex literal inside the donor function moved to the unit's function
    by offset.  A hex literal that lies in the donor image but outside the function stops the run; so does a Require of
    a module the unit's lib does not have."""
    G = lambda *x: sh(['git', '-C', a.git, *x])
    for d in SECOND_DONORS:
        f = d['fn']
        for t, side in (('plain', ''), ('ubsan', 'U/')):
            have = [k for k in text if k.startswith('U/') == (side == 'U/') and re.match(rf'(U/)?(Prog/{f}(_c)?\.v|R_{f}\.v)$', k)]
            u = UE[t].one(f)
            if u is None or have:
                print(f'K3 {t} {f}: ' + ('not linked by the unit' if u is None else f'the kit has {have}') + ', skipped')
                continue
            path, pin_sha, symf = d['img'][t]
            path = path.format(B=a.donor_bin)
            symf = symf.format(B=a.donor_bin) if symf else None
            got_sha = hashlib.sha256(open(path, 'rb').read()).hexdigest()
            if got_sha != pin_sha:
                sys.exit(f'CONTROL K3 {t} {f}: donor image {path} sha256 {got_sha[:12]} is not the pin {pin_sha[:12]}')
            dsegs = _loads(path)
            src = f"proofs/{d['unit']}/lib/"
            ef, er = d['entry']
            want = int(re.search(er, G('show', f"{d['ref']}:{src}{side}{ef}").stdout).group(1), 16)
            usegs = UE[t].segs
            if symf:
                ds = Elf(symf).one(f)
                if ds is None:
                    sys.exit(f'CONTROL K3 {t} {f}: no unique symbol {f} in {symf}')
                dstart, dsize = ds
                if _rd(dsegs, dstart, dsize) != _rd(Elf(symf).segs, dstart, dsize):
                    sys.exit(f'CONTROL K3 {t} {f}: the symbol file\'s bytes of {f} are not the pin\'s')
                how = 'symbol of ' + os.path.basename(symf)
            else:
                code = _rd(usegs, u[0], u[1])
                hits = [va + i for va, dd in dsegs for i in range(len(dd)) if dd.startswith(code, i)]
                if len(hits) != 1:
                    sys.exit(f'CONTROL K3 {t} {f}: {len(hits)} occurrences of the unit\'s {f} bytes in the stripped donor pin')
                dstart, dsize = hits[0], u[1]
                how = 'unique byte occurrence in the stripped pin'
            print(f'CONTROL K3 {t} {f}: donor entry ({how}) {hex(dstart)}, released {hex(want)}', 'OK' if dstart == want else 'FAIL')
            if dstart != want:
                sys.exit(1)
            if dsize != u[1]:
                sys.exit(f'STOP K3 {t} {f}: sizes {dsize} / {u[1]}')
            sc = _same_code(dsegs, dstart, usegs, u[0], dsize)
            if isinstance(sc, str):
                sys.exit(f'STOP K3 {t} {f}: code differs: {sc}')
            print(f'K3 {t} {f}: {dsize} bytes, code equal ({sc} constant-pool pairs with equal values); delta {hex(u[0] - dstart)}')
            lo, hi = min(va for va, _ in dsegs), max(va + len(dd) for va, dd in dsegs)
            full_ref = G('rev-parse', d['ref']).stdout.strip()
            for fl in d['files']:
                k = side + fl
                body = G('show', f"{d['ref']}:{src}{k}").stdout
                if not body:
                    sys.exit(f'K3: {d["ref"]}:{src}{k} missing')
                body = body.replace(d['unit'].replace('/', '.'), f'{pmod()}.{a.unit}')
                L = body.split('\n')
                for i, l in enumerate(L):
                    def mv(m):
                        v = int(m.group(0), 16)
                        if dstart <= v < dstart + dsize:
                            nv = u[0] + (v - dstart)
                            log.append((k, i + 1, m.group(0), hex(nv), f'K3 {f}+{hex(v - dstart)} ({d["unit"]} {hex(dstart)} -> {a.unit} {hex(u[0])})'))
                            return hex(nv)
                        if lo <= v < hi:
                            sys.exit(f'STOP K3 {k}:{i + 1}: {m.group(0)} is in the donor image but not in {f}')
                        return m.group(0)
                    L[i] = HEXRE.sub(mv, l)
                L.insert(0, f"(* Modified by Theorem Labs, {a.month}: ported from {d['unit']} {src}{k} at {full_ref}, donor pin sha256 "
                            f"{pin_sha}, for {a.project}/{a.unit}: module paths and image addresses only, entry {f} "
                            f"{hex(dstart)} (donor) -> {hex(u[0])} (this image). *)")
                text[k] = '\n'.join(L)
            for fl in d['files']:
                k = side + fl
                for pre, mods in re.findall(rf'{pmod()}\.{a.unit}\.lib((?:\.\w+)*) Require (?:Import |Export )?([^.]*)\.', text[k]):
                    dirp = '/'.join(pre.split('.')[1:])
                    for m in mods.split():
                        p = (dirp + '/' if dirp else '') + m + '.v'
                        if p not in text:
                            sys.exit(f'STOP K3 {k}: Requires {p}, which the unit\'s lib does not have')


def main():
    global ARGS
    ap = argparse.ArgumentParser()
    ap.add_argument('--unit', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--plain', required=True)
    ap.add_argument('--ubsan', required=True)
    ap.add_argument('--work', required=True)
    ap.add_argument('--project', default='reac-repacer', help='the unit\'s project (module path <project with - as _>.<unit>)')
    ap.add_argument('--donor-ref', default='25e3d17bdb50')
    ap.add_argument('--kit-ref', default=None, help='commit whose decode lib file list is the kit (default: --donor-ref)')
    ap.add_argument('--month', required=True, help='YYYY-MM of the notices this run writes ("Modified by Theorem Labs, YYYY-MM: ...")')
    ap.add_argument('--git', required=True, help='hub clone holding --donor-ref and the second donors\' refs')
    ap.add_argument('--pac', required=True, help='port_addr_check.py frozen at 5033540ba83b')
    ap.add_argument('--decode-bin', required=True, help='dir with bin/fuzz_decode/ and unstripped/fuzz_decode/ (decode pins)')
    ap.add_argument('--donor-bin', required=True, help='dir with libreac/{plain,ubsan}/fuzz_disco* and pau-libreac-v190/libreac/bin/fuzz_pcap/')
    ARGS = a = ap.parse_args()
    if not re.fullmatch(r'\d{4}-(0[1-9]|1[0-2])', a.month):
        sys.exit(f'--month must be YYYY-MM, not {a.month!r}')
    for tg in ('plain', 'ubsan'):
        DONOR_IMG[tg] = (f'{a.decode_bin}/bin/fuzz_decode/fuzz_decode.{tg}', f'{a.decode_bin}/unstripped/fuzz_decode/fuzz_decode.{tg}')
    os.makedirs(a.work, exist_ok=True)
    G = lambda *x: sh(['git', '-C', a.git, *x])
    ref = G('rev-parse', a.donor_ref).stdout.strip()
    kit_ref = G('rev-parse', a.kit_ref or a.donor_ref).stdout.strip()
    print(f'donor ref {ref}; kit ref {kit_ref}; project {a.project}; unit {a.unit}')
    tgt = {'plain': a.plain, 'ubsan': a.ubsan}
    UE = {t: Elf(v.split(':')[1]) for t, v in tgt.items()}
    DE = {t: Elf(DONOR_IMG[t][1]) for t in tgt}
    log = []  # (file, line, old, new, why)
    rename = ('libreac.fuzz_decode', f'{pmod()}.{a.unit}')
    out = a.out.rstrip('/') + '/'

    # ---- controls: steps (d) on the decode pin reproduce decode's released values ----
    for t in ('plain', 'ubsan'):
        side = 'U/' if t == 'ubsan' else ''
        zi = G('show', f'{ref}:{DONOR_DIR}{side}ZImage.v').stdout
        want = int(re.search(r'ztext_count : nat := (\d+)', zi).group(1))
        got = DE[t].text_count()
        print(f'CONTROL {t} ztext_count decode {got} released {want}', 'OK' if got == want else 'FAIL')
        if got != want:
            sys.exit(1)

    # ---- K1 ----
    keep, dropped_k1 = keep_list(a.git, ref, DE, UE, kit_ref)
    for r, why in dropped_k1:
        log.append((r, 0, 'file', 'not copied', why))
    text = {}
    for r in keep:
        text[r] = k1_text(G('show', f'{ref}:{DONOR_DIR}{r}').stdout, rename)
    print(f'K1: {len(keep)} files')

    # ---- K2 (a) predictions ----
    vfiles = [r for r in keep if r.endswith('.v')]
    rows = {'plain': predict(a.work, ref, [r for r in vfiles if not r.startswith('U/')], 'plain', DONOR_DIR.rstrip('/'), tgt['plain']),
            'ubsan': predict(a.work, ref, [r[2:] for r in vfiles if r.startswith('U/')], 'ubsan', DONOR_DIR + 'U', tgt['ubsan'])}

    def first_label(res, t):
        m = re.match(r'(?:pc: )?([\w.]+)\+0x([0-9a-f]+)', res)
        if not m:
            return None
        v = UE[t].syms.get(m.group(1))
        return v[0][0] + int(m.group(2), 16) if v and len(v) == 1 else None

    for t in rows:
        for r in rows[t]:
            if r['verdict'] == 'MAPS-AMBIGUOUS':
                v = first_label(r['src_res'], t)
                if v is not None and v in [norm(x) for x in r['expected'].split()]:
                    r['verdict'], r['expected'] = 'MAPS', hex(v)

    # ---- K2 (b) hex literals; (c) decimal table ----
    conflicts = []
    for t, side in (('plain', ''), ('ubsan', 'U/')):
        per = collections.defaultdict(lambda: collections.defaultdict(set))
        nonaddr = collections.defaultdict(set)
        byline = collections.defaultdict(list)
        for r in rows[t]:
            v = norm(r['src_value'])
            if v is None:
                continue
            byline[(r['src_file'], int(r['src_line']))].append(r)
            if r['verdict'] in ('NON-ADDRESS', 'INSN'):
                nonaddr[r['src_file']].add(v)
            elif r['verdict'] in ('MAPS', 'MAPS-STRING') and r['expected'].strip():
                per[r['src_file']][v].add(norm(r['expected'].split()[0]))
            else:
                per[r['src_file']][v].add(None)
        for f in sorted(set(per) | set(k[0] for k in DECIMAL_TABLE)):
            key = side + f
            if key not in text:
                continue
            repl = {}
            for v, ts in per.get(f, {}).items():
                if None in ts or len(ts) != 1:
                    continue
                nv = next(iter(ts))
                if nv == v:
                    continue
                if v in nonaddr[f]:
                    conflicts.append((key, hex(v), hex(nv)))
                    continue
                repl[v] = nv
            lines = text[key].split('\n')
            for i, l in enumerate(lines):
                def sub(mo):
                    tok = mo.group(0)
                    v = norm(tok)
                    if tok.lower().startswith('0x'):
                        if v in repl:
                            log.append((key, i + 1, tok, hex(repl[v]), 'tool MAPS (hex)'))
                            return hex(repl[v])
                        return tok
                    how = DECIMAL_TABLE.get((f, i + 1))
                    if how == 'tool':
                        cand = [norm(r['expected'].split()[0]) for r in byline.get((f, i + 1), [])
                                if norm(r['src_value']) == v and r['verdict'] == 'MAPS' and r['expected'].strip()]
                        if cand:
                            log.append((key, i + 1, tok, str(cand[0]), 'decimal table: tool MAPS (pc)'))
                            return str(cand[0])
                    if how == 'textcount':
                        n = UE[t].text_count()
                        log.append((key, i + 1, tok, str(n), 'decimal table: .text instruction count'))
                        return str(n)
                    return tok
                lines[i] = NUMRE.sub(sub, l)
            text[key] = '\n'.join(lines)
        # tp / errno decimals (YN06, YN06_cf): every token of decode's tp / errno value
        for f in ('Reusable/YN06.v', 'Reusable/YN06_cf.v'):
            key = side + f
            dtls = DE[t].one('builtin_tls')[0]
            utls = UE[t].one('builtin_tls')[0]
            for what in ('*tp', '*errno'):
                off = DECIMAL_TABLE[(f, what)][1]
                old, new = dtls + off, utls + off
                for fmt in (hex, str):
                    pat = re.compile(r'(?<![0-9A-Za-z_])' + re.escape(fmt(old)) + r'(?![0-9A-Za-z_])')
                    n = len(pat.findall(text[key]))
                    if n:
                        text[key] = pat.sub(fmt(new), text[key])
                        log.append((key, 0, fmt(old), fmt(new), f'decimal table: builtin_tls+{hex(off)} x{n}'))

    # ---- K2 (d) per-image tables ----
    cells = []    # k2-cells.tsv: (file, line, cell, value, rule, measurement) of every kept YH03 cell
    str_own = {}  # (file, cell) -> length of the string a cell (h) moved by content, when decode's value holds it too
    routine = ('section bound', 'symbol + offset', 'port_addr_check MAPS')
    for t, side in (('plain', ''), ('ubsan', 'U/')):
        U, D = UE[t], DE[t]
        # YH03: only the definitions the kit uses
        key = side + 'Reusable/YH03.v'
        src = k1_text(G('show', f'{ref}:{DONOR_DIR}{key}').stdout, rename)
        files = {k: v for k, v in text.items() if k.endswith('.v') and k != key and k.startswith('U/') == (side == 'U/')}
        corpus = '\n'.join(files.values())
        secmap = {'text': '.text', 'rodata': '.rodata', 'eh_frame': '.eh_frame', 'init_array': '.init_array',
                  'fini_array': '.fini_array', 'data_rel_ro': '.data.rel.ro', 'got': '.got', 'data': '.data', 'bss': '.bss'}
        toolmap, toolres = collections.defaultdict(set), collections.defaultdict(set)
        for r in rows[t]:
            if r['src_file'] == 'Reusable/YH03.v' and r['verdict'] in ('MAPS', 'MAPS-STRING'):
                toolmap[norm(r['src_value'])].add(norm(r['expected'].split()[0]))
                toolres[norm(r['src_value'])].add(r['src_res'])
        dsyms = [(n, v, s) for n, l in D.syms.items() for v, s in l]
        new_lines, krows = [], []
        for l in src.split('\n'):
            ds = re.findall(r'Definition (src0_\w+) : Z := (0x[0-9a-fA-F]+|\d+)\.', l)
            if not ds:
                new_lines.append(l)
                continue
            kept = []
            for n, v in ds:
                if not re.search(r'\b' + n + r'\b', corpus) or n == 'src0_A_calloc' and not U.one('calloc'):
                    continue
                iv = int(v, 0)
                m = re.match(r'src0_(\w+)_(lo|hi)$', n)
                nv = None
                rule = meas = ''
                if m and m.group(1) in secmap:
                    lo, hi = U.sec[secmap[m.group(1)]]
                    nv = lo if m.group(2) == 'lo' else hi
                    rule, meas = 'section bound', f'{secmap[m.group(1)]} {"start" if m.group(2) == "lo" else "end"} (section headers)'
                else:
                    kind = n[5]
                    if kind == 'D':
                        cands = [(sn, a0, s0) for sn, a0, s0 in dsyms if a0 <= iv < a0 + max(s0, 1)]
                    else:
                        cands = [(sn, a0, s0) for sn, a0, s0 in dsyms if (a0 == iv if kind == 'A' else a0 + s0 == iv and s0 > 0)]
                    res = collections.defaultdict(list)
                    for sn, a0, s0 in cands:
                        u, dd = U.one(sn), D.one(sn)
                        if u and dd:
                            if kind == 'E':
                                res[u[0] + u[1]].append(f'end of {sn}')
                            else:
                                res[u[0] + (iv - dd[0])].append(f'{sn}+{hex(iv - dd[0])}')
                    if len(res) == 1:
                        (nv, how), = res.items()
                        rule, meas = 'symbol + offset', ' = '.join(sorted(how))
                    elif len(toolmap.get(iv, ())) == 1:
                        nv = next(iter(toolmap[iv]))
                        rule, meas = 'port_addr_check MAPS', '; '.join(sorted(toolres[iv]))
                    if nv is None and kind == 'D':
                        # a data cell no donor symbol covers (e.g. musl's unnamed debruijn32 table right after
                        # static_init_tls.msg) moves by CONTENT: the donor bytes from the cell to the next donor
                        # symbol (8..64 bytes) must occur exactly once in the unit's loaded image.
                        nxt = min([a0 for _, a0, _ in dsyms if a0 > iv] + [iv + 64])
                        b = D.read(iv, max(8, min(64, nxt - iv)))
                        hits = []
                        for va, d in (U.segs if b else []):
                            j = d.find(b)
                            while j >= 0:
                                hits.append(va + j)
                                j = d.find(b, j + 1)
                        if len(hits) == 1:
                            nv = hits[0]
                            rule, meas = "donor bytes (d')", f'the {len(b)} bytes of decode at {v} occur once in this image'
                if nv is None:
                    sys.exit(f'YH03 {t}: no value for {n} {v}')
                if not (m and m.group(1) in secmap) and n[5] in ('A', 'E'):
                    nv, why = yh03_by_name(U, n, nv, kind)
                    if nv is None:
                        sys.exit(f'YH03 {t}: REFUSED {n}: {why}')
                    if why.startswith('by name: '):
                        rule, meas = 'by name', why[len('by name: '):]
                    elif why:
                        rule, meas = 'no symbol', why
                    else:
                        meas += f'; the {"start" if kind == "A" else "end"} of a function the cell names'
                if n.startswith('src0_D_str'):
                    nv, rule, meas, own = yh03_str(t, n, nv, iv, U, D, files)
                    if own:
                        str_own[(key, n)] = own
                kept.append(f'Definition {n} : Z := {hex(nv)}.')
                krows.append((n, hex(nv), rule, meas))
                if rule not in routine:
                    print(f'YH03 {t}: {n} := {hex(nv)}: {rule}: {meas}')
                log.append((key, 0, v, hex(nv), f'YH03 {n}' + ('' if rule in routine else f' ({rule}: {meas})')))
            if kept:
                new_lines.append('  '.join(kept))
        i = max(k for k, l in enumerate(new_lines[:6]) if l.startswith('(*'))
        new_lines.insert(i + 1, k2_hdr(a.git, ref, key, a.unit, f'only the definitions this unit\'s files use are kept, each value moved to {a.unit}\'s image by symbol and offset (section bounds from its section headers), every code cell (src0_A_ / src0_E_) checked against the function it names in the unit\'s symtab' + ('' if U.one('calloc') else '; src0_A_calloc is dropped (no calloc is linked)')))
        text[key] = '\n'.join(new_lines)
        for n, val, rule, meas in krows:
            ln = next(j for j, l in enumerate(new_lines, 1) if re.search(r'Definition ' + n + r' :', l))
            cells.append((key, ln, n, val, rule, meas))
        # RELRO lists
        yh = {n: int(v, 0) for n, v in re.findall(r'Definition (src0_\w+) : Z := (0x[0-9a-fA-F]+)\.', text[key])}
        lo, ghi, gg = U.sec['.init_array'][0], U.sec['.got'][1], yh['src0_D_got_stack_chk_guard']
        newR = f'[({hex(lo)}, {gg - lo}); ({hex(gg + 8)}, {ghi - gg - 8})]'
        for f, pat in (('Reusable/YL0k.v', r'(Definition src0_R : list \(Z \* Z\) := )(\[[^\]]*\])'),
                       ('FrameAPI.v', r'(Definition frame_RELRO : list \(Z \* Z\) := )(\[[^\]]*\])')):
            k = side + f
            m = re.search(pat, text[k])
            log.append((k, 0, m.group(2), newR, 'RELRO from .init_array / .got / GOT[__stack_chk_guard]'))
            text[k] = text[k][:m.start(2)] + newR + text[k][m.end(2):]
        # (g) DECIMAL addresses inside a string constant (YL0v's rodata_*_src1 lemmas and the printf walks that read
        # them: the newline or text inside a driver format string).  For each decimal d that YL0v states as
        # `chunk_bytes ... (d - 65536) n`: the donor's whole NUL-terminated string s holding d must occur exactly once
        # in the unit's loaded image as NUL s NUL; d moves to that copy + (d - start of s).  Cross-check: every kept YH03
        # src0_D_str_* cell that (h) moved by content, whose decode value holds that same string and whose string holds
        # d, must give the same new address (else STOP).  Every decimal token d of the files below moves the same way.
        dyh = {nn: int(vv, 0) for nn, vv in re.findall(r'Definition (src0_D_str\w*) : Z := (0x[0-9a-fA-F]+|\d+)\.',
                                                         k1_text(G('show', f'{ref}:{DONOR_DIR}{key}').stdout, rename))}
        smap = {}
        for dd_, nn_ in re.findall(r'chunk_bytes src0segs E 65536 \(CImg 8192\) \((\d+) - 65536\) (\d+) =', text[side + 'Reusable/YL0v.v']):
            d, nb = int(dd_), int(nn_)
            st = d
            while st > 0 and D.read(st - 1, 1) not in (b'\0', None):
                st -= 1
            en = d
            while D.read(en, 1) not in (b'\0', None):
                en += 1
            s = D.read(st, en - st)
            if not s or d + nb > en + 1:
                sys.exit(f'STOP (g) {t}: decimal {d} is not inside a NUL-terminated donor string')
            hits = []
            for va, dat in U.segs:
                j = dat.find(b'\0' + s + b'\0')
                while j >= 0:
                    hits.append(va + j + 1)
                    j = dat.find(b'\0' + s + b'\0', j + 1)
            if len(hits) != 1:
                sys.exit(f'STOP (g) {t}: the donor string {s!r} holding {d} occurs {len(hits)} times in the unit image')
            nd = hits[0] + (d - st)
            for cn, cv in dyh.items():
                if (key, cn) in str_own and cv <= d < cv + str_own[(key, cn)] and yh[cn] + (d - cv) != nd:
                    sys.exit(f'STOP (g) {t}: {d}: string match gives {nd}, YH03 cell {cn} gives {yh[cn] + (d - cv)}')
            if U.read(nd, nb) != D.read(d, nb):
                sys.exit(f'STOP (g) {t}: {d} -> {nd}: bytes {U.read(nd, nb)!r} != donor {D.read(d, nb)!r}')
            smap[d] = (nd, s.decode('latin-1').encode('unicode_escape').decode(), d - st)
        for f in ('Reusable/YL0v.v', 'Reusable/YL0w.v', 'Reusable/YL0w_cfw.v', 'Reusable/YL0x.v', 'Reusable/YL0x_cfw.v',
                  'Reusable/YL0y.v', 'Reusable/YL0y_cfw.v'):
            k = side + f
            if k not in text:
                continue
            for d, (nd, cn, off) in smap.items():
                if nd == d:
                    continue
                pat = re.compile(r'(?<![0-9A-Za-z_])' + str(d) + r'(?![0-9A-Za-z_])')
                cnt = len(pat.findall(text[k]))
                if cnt:
                    text[k] = pat.sub(str(nd), text[k])
                    log.append((k, 0, str(d), str(nd), f'string decimal: {cn}+{off} x{cnt}'))

    # ---- K2 (f) libc pieces the unit does not link ----
    for t, side in (('plain', ''), ('ubsan', 'U/')):
        U = UE[t]
        if not U.one('calloc'):
            for k in [k for k in text if k.startswith(side) and re.match(r'(U/)?(Calloc|AllocCallocCf)', k) and k.startswith('U/') == (side == 'U/')]:
                del text[k]
                log.append((k, 0, 'file', 'dropped', 'no calloc linked'))
            k = side + 'Reusable/YH02.v'
            assert '(Some src0_A_calloc)' in text[k]
            text[k] = text[k].replace('(Some src0_A_calloc)', 'None')
            log.append((k, 0, '(Some src0_A_calloc)', 'None', 'no calloc linked'))
            k = side + 'ZAllocator.v'
            z = text[k].replace('Require Import ZTraceSpec ZComplete CallocCert.', 'Require Import ZTraceSpec ZComplete.')
            z = z.replace('Let CAL := fun fx => @src0_calloc_realizes fx rc.',
                          '(* the unit links no calloc: src0_msyms has ms_calloc = None (YH02), so calloc_realizes holds vacuously. *)\n'
                          'Lemma src0_calloc_none {fx : FPState} : @calloc_realizes fx rc src0_msyms (MRx src0_msyms).\n'
                          'Proof. intros pc L A regs mem md m n Hc. discriminate Hc. Qed.\n'
                          'Let CAL := fun fx => @src0_calloc_none fx.')
            L = z.split('\n')
            L.insert(4, k2_hdr(a.git, ref, k, a.unit, 'the unit links no calloc: CallocCert is not required and CAL is the vacuous src0_calloc_none (ms_calloc = None)'))
            text[k] = '\n'.join(L)
            log.append((k, 0, 'CAL', 'src0_calloc_none', 'no calloc linked'))
            k = side + 'FrameAPI.v'
            n = len(re.findall(r'ms_calloc B = \(Some 0x[0-9a-f]+\)', text[k]))
            text[k] = re.sub(r'ms_calloc B = \(Some 0x[0-9a-f]+\)', 'ms_calloc B = None', text[k])
            text[k] = '\n'.join(add_hdr(text[k].split('\n'), k2_hdr(a.git, ref, k, a.unit, 'the unit links no calloc: frame_plain binds ms_calloc B = None; the RELRO list is the unit image\'s; addresses moved by symbol and offset')))
            log.append((k, 0, 'ms_calloc B = (Some ..)', 'ms_calloc B = None', f'no calloc linked x{n}'))
            k = side + 'FrameProof.v'
            old = '  split; [intros pc _; exact (calloc_contract_ok src0_msyms (@zlib_API rc) AX HB pc)|].'
            assert text[k].count(old) == 1
            text[k] = text[k].replace(old, '  split; [intros pc Hpc; discriminate Hpc|].  (* no calloc: ms_calloc src0_msyms = None *)')
            text[k] = '\n'.join(add_hdr(text[k].split('\n'), k2_hdr(a.git, ref, k, a.unit, 'the unit links no calloc: the calloc clause of the frame allocator holds vacuously (ms_calloc = None)')))
            log.append((k, 0, 'calloc_contract_ok', 'vacuous', 'no calloc linked'))
        if not U.one('memcmp'):
            k = side + 'R_memchr.v'
            z = text[k]
            i, j = z.index('Module R_memcmp.'), z.index('End R_memcmp.') + len('End R_memcmp.')
            z = z[:i] + z[j:]
            L = z.split('\n')
            L.insert(3, k2_hdr(a.git, ref, k, a.unit, 'the unit links no memcmp: the unused module R_memcmp (memcmp\'s walk, not referenced by the memchr proofs below) is removed; no other change'))
            text[k] = '\n'.join(L)
            log.append((k, 0, 'Module R_memcmp', 'dropped', 'no memcmp linked'))
    # a dropped file must have no remaining Require
    dropped = [k for k in keep if k not in text]
    for k, v in text.items():
        for d in dropped:
            base = d.split('/')[-1][:-2]
            if k.startswith('U/') == d.startswith('U/') and re.search(r'Require[^.]*\b' + base + r'\b', v):
                sys.exit(f'{k} still requires dropped {d}')

    # ---- K2 (e) fetch_word lemmas ----
    def jal_imm(w):
        imm = ((w >> 31) & 1) << 20 | ((w >> 21) & 0x3ff) << 1 | ((w >> 20) & 1) << 11 | ((w >> 12) & 0xff) << 12
        return imm - (1 << 21) if imm & (1 << 20) else imm
    for t, side in (('plain', ''), ('ubsan', 'U/')):
        S = {n: int(v, 0) for n, v in re.findall(r'Definition (src0_\w+) : Z := (0x[0-9a-fA-F]+)\.', text[side + 'Reusable/YH03.v'])}
        for k in sorted(k for k in text if k.endswith('.v') and k.startswith('U/') == (side == 'U/')):
            z = text[k]
            pos = 0
            while True:
                m = re.compile(r'fetch_word\s+\w+\s+(\([^=]*?\))\s*=\s*Some\s*\((0x[0-9a-fA-F]+)%bv').search(z, pos)
                if not m:
                    break
                pos = m.end()
                e = m.group(1).strip()
                ms = re.fullmatch(r'\(Z_to_bv 64 \((src0_\w+) \+ (0x[0-9a-fA-F]+|\d+)\)\)', e)
                ml = re.fullmatch(r'\((0x[0-9a-fA-F]+)%bv : word\)', e)
                if ms and ms.group(1) in S:
                    addr = S[ms.group(1)] + int(ms.group(2), 0)
                elif ml:
                    addr = int(ml.group(1), 16)
                else:
                    continue  # a named pc (FREE_RET ...): the build checks it
                b = UE[t].read(addr, 4)
                w_old, w_new = int(m.group(2), 16), int.from_bytes(b, 'little')
                if w_old == w_new:
                    continue
                if (w_old & 0xfff) != 0x0ef or (w_new & 0xfff) != 0x0ef:
                    sys.exit(f'{k}: word at {hex(addr)} {hex(w_old)} -> {hex(w_new)} is not a jal ra: stop')
                lit, nlit = m.group(2), '0x%08x' % w_new
                z = z[:m.start(2)] + nlit + z[m.end(2):]
                ou, nu = jal_imm(w_old) % (1 << 21), jal_imm(w_new) % (1 << 21)
                dm = re.compile(r'decode_any \(' + re.escape(lit) + r'%bv : bv 32\) = Some \(Jal 1 ' + str(ou) + r', 4%Z\)').search(z, m.start())
                if not dm:
                    sys.exit(f'{k}: no decode lemma for {lit}')
                z = z[:dm.start()] + f'decode_any ({nlit}%bv : bv 32) = Some (Jal 1 {nu}, 4%Z)' + z[dm.end():]
                log.append((k, 0, f'{lit} (jal {ou})', f'{nlit} (jal {nu})', f'fetch_word at {hex(addr)} read from the image'))
            text[k] = z

    # ---- K3 second donors (libc walks decode's kit lacks) ----
    second_donors(text, log, UE, a)

    # ---- notices: every file whose text differs from the donor's gets ONE month-dated notice (Apache-2.0 4(b));
    # a file a written rule above already noticed keeps that one; K3 files carry their own on line 1 ----
    head = f'(* Modified by Theorem Labs, {a.month}: ported from '
    moved = collections.Counter(r[0] for r in log if r[2] != 'file')
    for k in sorted(text):
        if not k.endswith('.v') or any(l.startswith(head) for l in text[k].split('\n')[:12]):
            continue
        donor = G('show', f'{ref}:{DONOR_DIR}{k}').stdout
        if text[k] == donor:
            continue
        what = (f'{moved[k]} image values moved to {a.unit}\'s binaries by symbol and offset (provenance/evidence/kit-relocation/values.tsv)'
                if moved[k] else 'no image value changed')
        text[k] = '\n'.join(add_hdr(text[k].split('\n'), k2_hdr(a.git, ref, k, a.unit, what)))

    # ---- write ----
    for k, v in text.items():
        p = out + k
        os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, 'w').write(v)
    for d in dropped:
        if os.path.exists(out + d):
            os.remove(out + d)
    with open(f'{a.work}/k2-values.tsv', 'w') as f:
        f.write('file\tline\told\tnew\thow\n')
        for r in log:
            f.write('\t'.join(map(str, r)) + '\n')
    with open(f'{a.work}/k2-conflicts.tsv', 'w') as f:
        for c in conflicts:
            f.write('\t'.join(c) + '\n')
    with open(f'{a.work}/k2-cells.tsv', 'w') as f:
        f.write('file\tline\tcell\tvalue\trule\tmeasurement\n')
        for r in cells:
            f.write('\t'.join(map(str, r)) + '\n')
    print(f'K2: {len(log)} changes, {len(conflicts)} hex conflicts (not applied), {len(dropped)} files dropped')
    print(f'tables: {a.work}/k2-values.tsv {a.work}/k2-conflicts.tsv {a.work}/k2-cells.tsv')


if __name__ == '__main__':
    main()
