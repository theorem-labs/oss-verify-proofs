#!/usr/bin/env python3
"""relocate.py -- copy the PROVED walks and contracts of the libdiginet src/ functions that fuzz_transport reaches
from the units that proved them into fuzz_transport's lib, and move every image numeral to fuzz_transport's images by
SYMBOL + OFFSET.  Rerunnable: a new donor commit is one --frame-ref / --codec-ref / --widep-ref / --wideu-ref away.

usage (from anywhere; the default refs are the donors of 2026-10-30):
  relocate.py --unstripped <dir> [--pins <dir>] [--git <repo holding the donor commits>] [--frame-ref <sha>]
              [--codec-ref <sha>] [--widep-ref <sha>] [--wideu-ref <sha>] [--month 2026-10]
              [--target-plain <stripped pin>:<unstripped twin>] [--target-ubsan <stripped pin>:<unstripped twin>]
              [--out <proofs/libdiginet/fuzz_transport>] [--dry-run]
--unstripped names the directory of the unstripped twins <unit>/<unit>.{plain,ubsan} of fuzz_frame, fuzz_codec and
fuzz_transport (sha256 TWIN_SHA); --pins the directory of fuzz_transport's stripped pins fuzz_transport/fuzz_transport.
{plain,ubsan} (sha256 PIN_SHA), needed unless both --target-* are given.  --target-plain / --target-ubsan choose
fuzz_transport's images of that build instead; their expected sha256s (PIN_SHA, TWIN_SHA) become the sha256s of the
given files, printed in S0.

Donors (one machine walk per src/ function and build, relocated to the other targets when the code is equal modulo
pc-relative addresses; measured by the source-equality comparison src-equality-v2.md, cmpkit 4bbd3a74be89: every pair
EQUAL or EQUAL-mod-pcrel):
  fuzz_frame  proofs/libdiginet/fuzz_frame/lib/{,U/}Prog/<f>{,_c}.v for the FRAME functions of FUNCS;
  fuzz_codec  proofs/libdiginet/fuzz_codec/lib/{,U/}Prog/diginet_personality_from_name{,_c}.v, the libc
              strcmp walk it calls (strcmp{,_c}.v; libc, so not in src-equality: its bytes are compared here), and
              its helpers codec_cells.v (copied) and codec_img.v (rewritten: only the facts the walk reads, see
              HELPERS).
A file absent at the donor commit is listed as "missing in the donor"; nothing else is skipped.
Default refs: fuzz_frame 9bd29914ffde, the tip of the fuzz_frame proof's integration on 2026-10-30 16:00Z (a descendant
of e807056547ed with the same contracts; it adds the walks of diginet_frame_build, both builds, and the ubsan walk of
diginet_body_check); fuzz_codec d8e4e696562a, the fuzz_codec proof's lib.

WIDE donors (fuzz_frame's widened contracts of 2026-10-30: body = NULL with length 0, any int mode).  They
are two branches that ADD <f>_w.v (the walk of the wide contract, with <f>_contract_of_w: the wide contract gives the
narrow one) and <f>_w_c.v (the wide contract) to the fuzz_frame tree of --frame-ref, nothing else:
  --widep-ref b8f2ecf2c3ff  lib/Prog/{diginet_body_check,diginet_frame_build}_w{,_c}.v
  --wideu-ref bb3053036017  lib/U/Prog/{diginet_sum16,diginet_msg_next,
                            diginet_body_check,diginet_frame_build}_w{,_c}.v
The WIDE list names them (function, build, donor unit, wide ref).  Each (function, build) must be a FUNCS row of that
build, so S1's equality control already covers its code; the files go through S2-S5 as the other files do.

Steps (each prints what it did; the run stops on the first thing it cannot do, printing it):
  S0  controls on the images: each unstripped twin's sha256 is the pin of src-equality-v2.md (TWIN_SHA; for a
      --target-<build> twin, that file's sha256); for fuzz_transport, the PT_LOAD bytes of the twin equal those of
      the stripped pin that Img0 reads (PIN_SHA, or the --target-<build> pin's sha256), except the ELF header's
      section-header fields and the .note.gnu.build-id descriptor (no numeral may point there).
  S1  equality control per relocated function and build: same size in the donor's and transport's image; every
      instruction byte-equal except pc-relative ones (auipc + its lo12 use, jal, c.j), and at each of those the
      transport target is the donor target moved by symbol + offset (rule (a) below).  strcmp: byte-equal.
  S2  file set: per function and build {,U/}Prog/<f>.v (walk) and <f>_c.v (contract) at the donor commit, and per
      WIDE row {,U/}Prog/<f>_w.v and <f>_w_c.v at its wide ref (absent there stops the run: a WIDE row is named by
      hand); a present file must have no Admitted / admit / Axiom / Parameter / Conjecture outside comments.
  S3  per file (a helper of mode trim first keeps only TRIM_KEEP): EDITS (exact text or regex, each must match
      exactly once), PROSE (fuzz_frame's "The caller is <its harness function> (pcs);" -> "In fuzz_frame the caller
      is ...;"), the module paths OssFuzzTheorems.Proofs.libdiginet.<donor unit>.lib and
      OssFuzzTheorems.libdiginet.<donor unit> -> fuzz_transport's, the image names
      <donor unit>.plain / .ubsan -> fuzz_transport.plain / .ubsan (the numerals beside them now name that image),
      then every numeral (hex, or decimal) inside the donor image's PT_LOAD range of the file's build (U/ = ubsan) is
      moved by the first rule that applies:
        (a) inside a sized FUNC / OBJECT symbol S of the donor: S + off -> transport's S + off (S unique by name and
            size in transport; a size change is allowed only at off 0);
        (b) the end of a sized symbol S (an exclusive bound): transport's end of S; when it is also the start of a
            symbol T, T + 0 must give the same value;
        (c) in the donor's .rodata and in no symbol: the NUL-terminated string there, which must occur exactly once
            (with its NUL) in transport's .rodata;
        (d) SECTION rules (file, Definition name or literal), for codec's RELRO block: a start must be the donor
            section's start and becomes transport's; a block length must cover the donor's personalities[] inside
            the donor section and becomes transport's section size; both must equal Prog/T/TContract.v's values;
      anything else stops the run.  A numeral outside the PT_LOAD range is left as it is.
  S4  Require closure: every lib module a written file requires is written here or already in transport's tree; a
      pre-existing one that the donor also has must be the donor's file modulo the module path and Modified-by lines
      (Spec/ and Lib/: transport's copy may only insert lines; Lib/Step.v gained the le1 case of cell_of_bytes), or,
      for a callee contract (*_c.v), the donor's file after S3.
  S5  write: line 1 (after the donor's leading one-line comments, which stay) is the notice
      (* Modified by Theorem Labs, <month>: relocated from libdiginet/<unit> <path> at <sha> to fuzz_transport's images *)
      with "; <what else>" when EDITS changed text.  A target path that exists and was not written by this script
      (no row in relocate-list.tsv) stops the run.  Then relocate-list.tsv (<path> <kind> <sha256> <role...>, one row
      per lib/ file written), MANIFEST (the same columns, one row per file of srcreloc/), values.tsv (every moved
      numeral), files.tsv (function x build x file: relocated / missing in the donor) and sample20.tsv (20 moved
      numerals spread over the files, for the hand cross-check in crosscheck.md).
"""
import argparse, collections, difflib, hashlib, os, re, subprocess, sys
from elftools.elf.elffile import ELFFile

# the twins' and pins' directories come from --unstripped / --pins (main)
# src-equality-v2.md "ELFs"
TWIN_SHA = {
    ('fuzz_frame', 'plain'): 'd28c8cc658e47348929d2edcbdea6f3cfbf0c52d7a90341fbc9ca1fb97a3bcdd',
    ('fuzz_frame', 'ubsan'): 'a32c718f58f705616bf8b7d2ecf4180b6ba71707a06d11d61c053467e72f2c82',
    ('fuzz_codec', 'plain'): 'fc6379b62efef317a4851d4f0e6ddaddc136dbc82615daec3c039d0f572ae223',
    ('fuzz_codec', 'ubsan'): 'c0987f7c0263ac0ad73c12681addc67fb7b73d142e5bc4b4a79f2e3dd21b934e',
    ('fuzz_transport', 'plain'): '6910a26aa1ea56eae5132e9bc6ba214337014cf2854cd1114e35830b09d2413b',
    ('fuzz_transport', 'ubsan'): '363a964065a2d016ed5b3526820ec6778b7bb0fc112b5118db9c3e0a13dc3b07',
}
# provenance/PROVENANCE.yaml "binaries"
PIN_SHA = {
    'plain': '81d5585d6e5c54a3bcd78f29ccbaf477ac6949fa7253b977e4d60618dbd540b0',
    'ubsan': '9743b17ae4e0077df225ced728f295d5446473b1666c1a6a04a256fd306a373b',
}
DONORS = {
    'fuzz_frame': dict(ref='9bd29914ffdef650a37285056a472ff186b4331a'),
    'fuzz_codec': dict(ref='d8e4e696562a3ec070d61f99e264ce9d80f5a5bd'),
}
BOTH = ('plain', 'ubsan')
# (function, donor unit, builds that hold the function in fuzz_transport and the donor)
FUNCS = [
    ('diginet_frame_parse', 'fuzz_frame', BOTH),
    ('diginet_frame_build', 'fuzz_frame', BOTH),
    ('diginet_announce_parse', 'fuzz_frame', BOTH),
    ('diginet_body_check', 'fuzz_frame', BOTH),
    ('diginet_frame_is_keepalive', 'fuzz_frame', BOTH),
    ('diginet_mac_is_digidesign', 'fuzz_frame', BOTH),
    ('diginet_msg_next', 'fuzz_frame', BOTH),
    ('diginet_cursor_init', 'fuzz_frame', BOTH),
    ('rd32', 'fuzz_frame', ('ubsan',)),
    ('diginet_sum16', 'fuzz_frame', ('ubsan',)),
    ('copy_strz', 'fuzz_frame', ('ubsan',)),
    ('diginet_personality_from_name', 'fuzz_codec', BOTH),
    ('strcmp', 'fuzz_codec', BOTH),
]
# The widened contracts and their walks.  WIDE_DONORS: the wide ref name -> the branch tip that adds those files to
# the fuzz_frame tree of --frame-ref.  WIDE: (function, build, donor unit, wide ref name); the files relocated are
# {,U/}Prog/<function>_w_c.v (the wide contract) and _w.v (its walk and <function>_contract_of_w).
WIDE_DONORS = {
    'widep': dict(ref='b8f2ecf2c3ff0406d93584348ebba6e5957c14ce'),
    'wideu': dict(ref='bb3053036017d1d92db6eca9e973ce610be16c08'),
}
WIDE = [
    ('diginet_body_check', 'plain', 'fuzz_frame', 'widep'),
    ('diginet_frame_build', 'plain', 'fuzz_frame', 'widep'),
    ('diginet_sum16', 'ubsan', 'fuzz_frame', 'wideu'),
    ('diginet_msg_next', 'ubsan', 'fuzz_frame', 'wideu'),
    ('diginet_body_check', 'ubsan', 'fuzz_frame', 'wideu'),
    ('diginet_frame_build', 'ubsan', 'fuzz_frame', 'wideu'),
]
LIBC = {'strcmp'}  # not src/: S1 asks for equal bytes
UNIT = 'fuzz_transport'
MODP = 'OssFuzzTheorems.Proofs.libdiginet.%s.lib'


def modpath(t, u):
    """the unit's module paths (proof library OssFuzzTheorems.Proofs.libdiginet.<u>.lib..., statement / image
    library OssFuzzTheorems.libdiginet.<u>...) renamed to fuzz_transport's"""
    return re.sub(r'\bOssFuzzTheorems\.(Proofs\.)?libdiginet\.%s\b' % u, r'OssFuzzTheorems.\1libdiginet.' + UNIT, t)

# Helper files of the donors (what the walks Require that transport's tree lacks).
#  copy: the whole file through S3.  trim: the file's head up to TRIM_HEAD_END and the items named in TRIM_KEEP,
#  through S3; its other items are about fuzz_codec's own harness tables, which fuzz_transport has not.
HELPERS = [
    ('fuzz_codec', 'Prog/codec_cells.v', 'copy'),
    ('fuzz_codec', 'U/Prog/codec_cells.v', 'copy'),
    ('fuzz_codec', 'Prog/codec_img.v', 'trim'),
    ('fuzz_codec', 'U/Prog/codec_img.v', 'trim'),
]
TRIM_HEAD_END = '(** * Read-only data (.rodata) *)'
TRIM_KEEP = ['CODEC_STR_C24', 'codec_str_c24', 'CODEC_STR_PC', 'codec_str_pc',
             'codec_str_c24_at', 'codec_str_c24_nz', 'codec_str_pc_at', 'codec_str_pc_nz', 'codec_str_pc_ne_c24',
             'codec_relro_base', 'CODEC_PERS', 'codec_pers_cells', 'codec_pers_image', 'codec_pers_at']

# (d) SECTION rules.  codec_cells' RELRO_BASE / RELRO_LEN and codec_img's codec_relro_base / the 568 of codec_pers_at
# name the donor's RELRO block: from the start of its .data.rel.ro to the end of personalities[] (568 of its 584
# bytes; stderr / stdout follow).  In fuzz_transport the block is Prog/T/TContract.v's RELRO_BASE / RELRO_LEN: the
# whole .data.rel.ro (SPEC_C24, SPEC_PC, op_announce's NAME, personalities[], stderr, stdout), so that one relro_img
# premise serves check_state_desk, notice and diginet_personality_from_name.
#  'start': the donor value must be the donor section's start; the new value is transport's section start.
#  'span' : the donor block [start, start + value) must lie in the donor section and hold the donor's personalities;
#           the new value is transport's section size, whose block holds transport's personalities.
SECTION_DEFS = {
    'codec_cells.v': {'RELRO_BASE': ('.data.rel.ro', 'start'), 'RELRO_LEN': ('.data.rel.ro', 'span')},
    'codec_img.v': {'codec_relro_base': ('.data.rel.ro', 'start')},
}
# the block length written as a literal in codec_img.v's premises: `0 <= i < 568`, `codec_relro_base 568`
SECTION_LITERALS = {
    'codec_img.v': [(r'(?<=0 <= i < )(\d+)(?= ->)', '.data.rel.ro', 'span'),
                    (r'(?<=codec_relro_base )(\d+)(?=\);)', '.data.rel.ro', 'span')],
}
SPAN_HOLDS = 'personalities'
# PROSE: (donor unit) -> [(regex, replacement, what)], applied to every file of the unit, any number of times.  A
# contract that names its caller in fuzz_frame's harness (LLVMFuzzerTestOneInput or a check_* function, with the
# caller's pcs in the ubsan contracts) now says "In fuzz_frame the caller is ..."; the pcs are dropped (no such
# function, or another one of that name, in fuzz_transport).  Callers inside libdiginet (diginet_body_check calling
# diginet_cursor_init, ...) stay as they are: those calls are the same in fuzz_transport.
def _caller(m):
    """the replacement of one PROSE caller match; a line break inside the dropped pcs moves after the ';'"""
    brk = m.group(3) or ''
    tail = brk[brk.rindex('\n'):] if '\n' in brk else (m.group(4) or '')
    return f'In fuzz_frame the caller is{m.group(1)}{m.group(2)};' + tail


PROSE = {
    'fuzz_frame': [
        (re.compile(r'The caller is(\s+)(check_\w+|LLVMFuzzerTestOneInput)'
                    r'(?:(\s+)\(0x[0-9a-f]+(?:,\s+0x[0-9a-f]+)*\))?;( ?)'),
         _caller, 'the caller named is fuzz_frame\'s (its pcs dropped)'),
    ],
}
# EDITS: (donor unit, file) -> [(old, new, what)] exact text, each old must occur exactly once in the donor file.
EDITS = {
    ('fuzz_codec', 'Prog/diginet_personality_from_name_c.v'): [
        ('Called by check_personality (0x14ab0, 0x14ac0, 0x14ad0, 0x14ae0, 0x14af0) with a0 one of the\n',
         'In fuzz_codec it is called by check_personality with a0 one of the\n',
         'the pcs of fuzz_codec\'s caller check_personality (no such function here) dropped'),
        ('From OssFuzzTheorems.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.\n', '',
         'its unused Require of fuzz_codec\'s harness model codec_owe dropped'),
    ],
    ('fuzz_codec', 'U/Prog/diginet_personality_from_name_c.v'): [
        ('Called by check_personality (0x14c90, 0x14ca0, 0x14cb0, 0x14cc0, 0x14cd0) with the five .rodata\n',
         'In fuzz_codec it is called by check_personality with the five .rodata\n',
         'the pcs of fuzz_codec\'s caller check_personality (no such function here) dropped'),
        ('From OssFuzzTheorems.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.\n', '',
         'its unused Require of fuzz_codec\'s harness model codec_owe dropped'),
    ],
    ('fuzz_codec', 'Prog/codec_cells.v'): [
        ('(** ---- the RELRO tables: SPEC_DESK, SPEC_C24, SPEC_PC, GLYPH and personalities[] lie in\n'
         '    [RELRO_BASE, RELRO_BASE + RELRO_LEN), inside a writable PT_LOAD,',
         '(** ---- the RELRO tables: .data.rel.ro of fuzz_transport (SPEC_C24, SPEC_PC, op_announce\'s NAME,\n'
         '    personalities[], stderr, stdout; the values of Prog/T/TContract.v) lies in\n'
         '    [RELRO_BASE, RELRO_BASE + RELRO_LEN), inside a writable PT_LOAD,',
         'the RELRO block [RELRO_BASE, RELRO_BASE + RELRO_LEN) is fuzz_transport\'s whole .data.rel.ro, '
         'Prog/T/TContract.v\'s values'),
    ],
    ('fuzz_codec', 'U/Prog/codec_cells.v'): [
        ('(** ---- the RELRO tables: SPEC_DESK, SPEC_C24, SPEC_PC, GLYPH and personalities[] lie in\n'
         '    [RELRO_BASE, RELRO_BASE + RELRO_LEN), inside a writable PT_LOAD,',
         '(** ---- the RELRO tables: .data.rel.ro of fuzz_transport (SPEC_C24, SPEC_PC, op_announce\'s NAME,\n'
         '    personalities[], stderr, stdout; the values of U/Prog/T/TContract.v) lies in\n'
         '    [RELRO_BASE, RELRO_BASE + RELRO_LEN), inside a writable PT_LOAD,',
         'the RELRO block [RELRO_BASE, RELRO_BASE + RELRO_LEN) is fuzz_transport\'s whole .data.rel.ro, '
         'U/Prog/T/TContract.v\'s values'),
    ],
}
# codec_img: the file comment and the RELRO comment name fuzz_codec's own tables; both are replaced (regex, DOTALL,
# exactly one match).  The new text holds no numeral (the RELRO comment names its values by Definition).
for _b, _bb in (('', 'plain'), ('U/', 'UBSan')):
    EDITS[('fuzz_codec', _b + 'Prog/codec_img.v')] = [
        (re.compile(r'\(\*\* The facts of the %s image of fuzz_codec that.*?a u16\)\. \*\)\n' % _bb, re.S),
         '(** The facts of the %s image of fuzz_transport that the walk of diginet_personality_from_name reads, each\n'
         '    proved by computation over the image (Img0): the announce names "CNTRL|24" and "MAINUNIT" in .rodata (so\n'
         '    [mem_inv] makes every load read the image), and the library\'s personalities[] in .data.rel.ro (a writable\n'
         '    segment, so a premise says that memory there still holds the image bytes). Kept from fuzz_codec\'s file of\n'
         '    the same name, whose other facts are about fuzz_codec\'s own harness tables. *)\n' % _bb,
         'only the facts of the announce names and personalities[] are kept; the RELRO block of codec_pers_at is '
         'fuzz_transport\'s whole .data.rel.ro'),
        ('(** ** The strings check_personality passes to strcmp and diginet_personality_from_name\n',
         '(** ** The announce names diginet_personality_from_name passes to strcmp\n', None),
        (re.compile(r'\(\*\* \* The tables in \.data\.rel\.ro\n.*?reads as the image\. \*\)\n', re.S),
         '(** * personalities[] in .data.rel.ro\n\n'
         '    fuzz_transport\'s .data.rel.ro starts at codec_relro_base; it holds, with other tables, the library\'s\n'
         '    personalities[] (CODEC_PERS, 2 x 24). The segment is writable, so each lemma below takes the premise that\n'
         '    memory there still reads as the image. *)\n', None),
    ]

NUMRE = re.compile(r'(?<![0-9A-Za-z_])(0x[0-9a-fA-F]+|[0-9]+)(?![0-9A-Za-z_])')
BAD = re.compile(r'\b(Admitted|admit|Axiom|Axioms|Parameter|Parameters|Conjecture)\b')


def die(msg):
    print('STOP: ' + msg, file=sys.stderr)
    sys.exit(2)


def sh(args, **kw):
    r = subprocess.run(args, capture_output=True, **kw)
    return r


def sha256b(b):
    return hashlib.sha256(b).hexdigest()


def strip_comments(t):
    """Rocq text with nested comments and string literals blanked (newlines kept)."""
    out, i, depth, n = [], 0, 0, len(t)
    instr = False
    while i < n:
        c2 = t[i:i + 2]
        if not depth and not instr and t[i] == '"':
            instr = True; out.append(' '); i += 1; continue
        if instr:
            if t[i] == '"':
                instr = False
            out.append('\n' if t[i] == '\n' else ' '); i += 1; continue
        if c2 == '(*':
            depth += 1; out.append('  '); i += 2; continue
        if c2 == '*)' and depth:
            depth -= 1; out.append('  '); i += 2; continue
        out.append(t[i] if not depth or t[i] == '\n' else ' ')
        i += 1
    return ''.join(out)


class Img:
    def __init__(self, path):
        self.path = path
        self.raw = open(path, 'rb').read()
        self.sha = sha256b(self.raw)
        e = ELFFile(open(path, 'rb'))
        self.loads = [(s['p_vaddr'], s['p_memsz'], s['p_filesz'], s.data()) for s in e.iter_segments()
                      if s['p_type'] == 'PT_LOAD']
        self.secs = {s.name: (s['sh_addr'], s['sh_size']) for s in e.iter_sections() if s['sh_addr']}
        self.syms = collections.defaultdict(list)   # name -> [(value, size, type)]
        self.sized = []                             # (value, size, name, type)
        st = e.get_section_by_name('.symtab')
        if st is not None:
            for s in st.iter_symbols():
                t = s['st_info']['type']
                if not s.name or s['st_shndx'] == 'SHN_UNDEF' or t not in ('STT_FUNC', 'STT_OBJECT'):
                    continue
                self.syms[s.name].append((s['st_value'], s['st_size'], t))
                if s['st_size'] > 0:
                    self.sized.append((s['st_value'], s['st_size'], s.name, t))
        self.lo = min(v for v, m, f, d in self.loads)
        self.hi = max(v + m for v, m, f, d in self.loads)

    def in_range(self, a):
        return any(v <= a < v + m for v, m, f, d in self.loads)

    def read(self, a, n):
        for v, m, f, d in self.loads:
            if v <= a and a + n <= v + f:
                return d[a - v:a - v + n]
        return None

    def containing(self, a):
        return [(v, z, nm, t) for v, z, nm, t in self.sized if v <= a < v + z]

    def ending(self, a):
        return [(v, z, nm, t) for v, z, nm, t in self.sized if v + z == a]

    def one(self, name, size=None):
        c = [x for x in self.syms.get(name, []) if size is None or x[1] == size]
        c = sorted(set(c))
        return c[0] if len(c) == 1 else None

    def func(self, name):
        x = self.one(name)
        if x is None:
            return None
        return x[0], x[1], self.read(x[0], x[1])


class Mover:
    """Moves numerals of a donor image to transport's image (rules (a)-(c) of S3)."""

    def __init__(self, D, T, dname, tname):
        self.D, self.T, self.dname, self.tname = D, T, dname, tname

    def sym_map(self, a):
        """(new value, how) by rule (a) / (b), or (None, why)"""
        cs = self.D.containing(a)
        if cs:
            res = set()
            hows = []
            for v, z, nm, t in cs:
                off = a - v
                tt = self.T.one(nm, z) or (self.T.one(nm) if off == 0 else None)
                if tt is None:
                    hows.append(f'{nm}+{off:#x}: no unique {nm} of size {z} in {self.tname}')
                    continue
                res.add(tt[0] + off)
                hows.append(f'{nm}+{off:#x}')
            if len(res) == 1 and not any('no unique' in h for h in hows):
                return res.pop(), 'sym ' + hows[0]
            if len(res) == 1:
                # an alias without a twin, the others agree
                return res.pop(), 'sym ' + [h for h in hows if 'no unique' not in h][0]
            return None, '; '.join(hows) if hows else 'no symbol'
        es = self.D.ending(a)
        if es:
            res = {}
            for v, z, nm, t in es:
                tt = self.T.one(nm, z)
                if tt is None:
                    return None, f'end of {nm}: no unique {nm} of size {z} in {self.tname}'
                res[tt[0] + z] = f'end {nm}'
            if len(res) != 1:
                return None, 'ends disagree: ' + str(res)
            return next(iter(res.items()))
        return None, 'in no symbol'

    def str_map(self, a):
        """rule (c): an unsymbolized .rodata string, by content"""
        sa, sz = self.D.secs.get('.rodata', (0, 0))
        if not (sa <= a < sa + sz):
            return None, 'not in .rodata'
        b = self.D.read(a, sa + sz - a)
        k = b.find(b'\0')
        if k < 0:
            return None, 'no NUL'
        s = b[:k + 1]
        ta, tz = self.T.secs['.rodata']
        tb = self.T.read(ta, tz)
        hits = [m.start() for m in re.finditer(re.escape(s), tb)]
        if len(hits) != 1:
            return None, f'string {s!r} occurs {len(hits)} times in {self.tname} .rodata'
        return ta + hits[0], f'str {s[:-1].decode("latin-1")!r}'

    def move(self, a):
        v, how = self.sym_map(a)
        if v is not None:
            return v, how
        v2, how2 = self.str_map(a)
        if v2 is not None:
            return v2, how2
        return None, f'{how}; {how2}'


# ---------- RISC-V pc-relative aware compare (S1) ----------

def sext(x, b):
    x &= (1 << b) - 1
    return x - (1 << b) if x >> (b - 1) else x


def insns(code):
    i = 0
    while i < len(code):
        h = int.from_bytes(code[i:i + 2], 'little')
        if h & 3 == 3:
            yield i, 4, int.from_bytes(code[i:i + 4], 'little')
            i += 4
        else:
            yield i, 2, h
            i += 2


def pcrel_sites(base, code):
    """{offset: target} for auipc+lo12 pairs (at both offsets), jal and c.j"""
    L = list(insns(code))
    out = {}
    for idx, (o, n, w) in enumerate(L):
        if n == 4 and w & 0x7f == 0x17:          # auipc
            rd = (w >> 7) & 31
            hi = sext(w & 0xfffff000, 32)
            for o2, n2, w2 in L[idx + 1: idx + 9]:
                if n2 != 4:
                    continue
                op = w2 & 0x7f
                rs1 = (w2 >> 15) & 31
                if rs1 != rd:
                    if op not in (0x23, 0x27, 0x63) and ((w2 >> 7) & 31) == rd:
                        break                   # rd overwritten
                    continue
                if op in (0x13, 0x03, 0x07, 0x67):
                    lo = sext(w2 >> 20, 12)
                elif op in (0x23, 0x27):
                    lo = sext(((w2 >> 25) << 5) | ((w2 >> 7) & 31), 12)
                else:
                    break
                out[o] = out[o2] = base + o + hi + lo
                break
        elif n == 4 and w & 0x7f == 0x6f:        # jal
            imm = ((w >> 31) << 20) | (((w >> 12) & 0xff) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3ff) << 1)
            out[o] = base + o + sext(imm, 21)
        elif n == 2 and (w & 3) == 1 and (w >> 13) == 0b101:   # c.j
            b = lambda k: (w >> k) & 1
            imm = (b(12) << 11) | (b(8) << 10) | (b(10) << 9) | (b(9) << 8) | (b(6) << 7) | (b(7) << 6) | \
                  (b(2) << 5) | (b(11) << 4) | (b(5) << 3) | (b(4) << 2) | (b(3) << 1)
            out[o] = base + o + sext(imm, 12)
    return out


def eq_mod_pcrel(fn, mv):
    d, t = mv.D.func(fn), mv.T.func(fn)
    if d is None or t is None:
        return False, f'{fn}: absent ({mv.dname}: {d is not None}, {mv.tname}: {t is not None})'
    if d[1] != t[1]:
        return False, f'{fn}: size {d[1]} vs {t[1]}'
    if fn in LIBC:
        return (d[2] == t[2]), f'{fn}: {d[1]} bytes {"equal" if d[2] == t[2] else "DIFFER"} ({d[0]:#x} -> {t[0]:#x})'
    ds, ts = pcrel_sites(d[0], d[2]), pcrel_sites(t[0], t[2])
    if set(ds) != set(ts):
        return False, f'{fn}: pc-relative sites differ'
    nd = 0
    for (o, n, w1), (_, _, w2) in zip(insns(d[2]), insns(t[2])):
        if w1 == w2 and o not in ds:
            continue
        if o not in ds:
            return False, f'{fn}+{o:#x}: {w1:#x} vs {w2:#x}, not pc-relative'
        nv, how = mv.move(ds[o])
        if nv != ts[o]:
            return False, f'{fn}+{o:#x}: target {ds[o]:#x} moves to {nv} ({how}) but {mv.tname} has {ts[o]:#x}'
        nd += w1 != w2
    return True, f'{fn}: {d[1]} bytes at {d[0]:#x} / {t[0]:#x}, {len(ds)} pc-relative words ({nd} differ), all targets move'


# ---------- main ----------

# S5's per-file list of the lib/ files written: its header lines
LIST_HEAD = ("# relocate.py's per-file list, one row per lib/ file it wrote: <path> <kind> <sha256> <role...> from <donor>@<commit>.\n"
             "# The path is relative to the unit folder proofs/libdiginet/fuzz_transport; the sha256 is the file as relocate.py\n"
             "# wrote it. relocate.py and repin/repin_reloc.py read this list; a later edit of the tree shows as a different sha256,\n"
             "# and repin_reloc.py carries such edits onto a new output.\n")


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser()
    ap.add_argument('--git', default=None)
    ap.add_argument('--unstripped', required=True, metavar='DIR',
                    help='dir with <unit>/<unit>.{plain,ubsan}, the unstripped twins of fuzz_frame, fuzz_codec, fuzz_transport')
    ap.add_argument('--pins', default=None, metavar='DIR',
                    help='dir with fuzz_transport/fuzz_transport.{plain,ubsan}, the stripped pins (unless both --target-*)')
    ap.add_argument('--frame-ref', default=DONORS['fuzz_frame']['ref'])
    ap.add_argument('--codec-ref', default=DONORS['fuzz_codec']['ref'])
    ap.add_argument('--widep-ref', default=WIDE_DONORS['widep']['ref'])
    ap.add_argument('--wideu-ref', default=WIDE_DONORS['wideu']['ref'])
    ap.add_argument('--month', default='2026-10')
    ap.add_argument('--out', default=os.path.normpath(os.path.join(here, '..', '..', '..')))
    ap.add_argument('--target-plain', metavar='PIN:TWIN', default=None)
    ap.add_argument('--target-ubsan', metavar='PIN:TWIN', default=None)
    ap.add_argument('--dry-run', action='store_true')
    A = ap.parse_args()
    git = A.git or sh(['git', 'rev-parse', '--show-toplevel'], cwd=here, text=True).stdout.strip()
    # a SOURCE is a donor commit: a unit's own ref, or a wide ref of the unit named in WIDE
    refs = {'fuzz_frame': A.frame_ref, 'fuzz_codec': A.codec_ref, 'widep': A.widep_ref, 'wideu': A.wideu_ref}
    for s in refs:
        r = sh(['git', '-C', git, 'rev-parse', '--verify', refs[s] + '^{commit}'], text=True)
        if r.returncode:
            die(f'{s}: {refs[s]} is not a commit of {git}')
        refs[s] = r.stdout.strip()
    for fn, b, u, rk in WIDE:
        if rk not in refs:
            die(f'WIDE {fn} {b}: no ref {rk}')
        if not any(fn == f2 and u == u2 and b in bs for f2, u2, bs in FUNCS):
            die(f'WIDE {fn} {b} ({u}): no FUNCS row, so S1 does not control its code')
    out = A.out
    lib = os.path.join(out, 'lib')
    evid = os.path.join(out, 'provenance', 'evidence', 'srcreloc')
    toprel = os.path.relpath(out, git)

    def show(u, k, src=None):
        r = sh(['git', '-C', git, 'show', f'{refs[src or u]}:proofs/libdiginet/{u}/lib/{k}'])
        return r.stdout.decode() if r.returncode == 0 else None

    # S0
    print('== S0 images')
    # fuzz_transport's images: --pins / --unstripped, or per build --target-<build> PIN:TWIN, whose files' sha256s are then
    # the pinned values
    twin_path = {(u, b): f'{A.unstripped}/{u}/{u}.{b}' for u, b in TWIN_SHA}
    pin_path = {b: f'{A.pins}/{UNIT}/{UNIT}.{b}' for b in BOTH}
    if A.pins is None and None in (A.target_plain, A.target_ubsan):
        die('--pins DIR is needed unless both --target-plain and --target-ubsan are given')
    twin_sha, pin_sha = dict(TWIN_SHA), dict(PIN_SHA)
    for b, arg in (('plain', A.target_plain), ('ubsan', A.target_ubsan)):
        if arg is None:
            continue
        pp, sep, tp = arg.partition(':')
        if not (sep and pp and tp):
            die(f'--target-{b} {arg!r}: not PIN:TWIN')
        pin_path[b], twin_path[(UNIT, b)] = pp, tp
        pin_sha[b], twin_sha[(UNIT, b)] = sha256b(open(pp, 'rb').read()), sha256b(open(tp, 'rb').read())
        print(f'  --target-{b}: pin {pp} sha256 {pin_sha[b]}; twin {tp} sha256 {twin_sha[(UNIT, b)]}')
    I = {}
    for (u, b), want in twin_sha.items():
        p = twin_path[(u, b)]
        I[(u, b)] = Img(p)
        if I[(u, b)].sha != want:
            die(f'{p}: sha256 {I[(u, b)].sha}, pinned {want}')
        print(f'  {u}.{b} twin sha256 {want[:12]} ok')
    for b in BOTH:
        pin = Img(pin_path[b])
        if pin.sha != pin_sha[b]:
            die(f'{pin.path}: sha256 {pin.sha}, pinned {pin_sha[b]}')
        tw = I[(UNIT, b)]
        bid = tw.secs['.note.gnu.build-id']
        ndiff = 0
        for (v, m, f, d), (v2, m2, f2, d2) in zip(tw.loads, pin.loads):
            if (v, m, f) != (v2, m2, f2):
                die(f'{b}: PT_LOAD {v:#x} differs in shape from the pin')
            for i in range(f):
                if d[i] != d2[i]:
                    a = v + i
                    if not (0x10028 <= a < 0x10040 or bid[0] + 16 <= a < bid[0] + bid[1]):
                        die(f'{b}: twin and pin differ at {a:#x}')
                    ndiff += 1
        print(f'  {UNIT}.{b}: pin sha256 {pin_sha[b][:12]}; twin PT_LOAD bytes = pin\'s but {ndiff} bytes in the ELF '
              f'header section fields and the build-id')
    NOPOINT = [(0x10000, 0x10040)] + [(I[(UNIT, b)].secs['.note.gnu.build-id'][0],
                                       I[(UNIT, b)].secs['.note.gnu.build-id'][0] + 0x24) for b in BOTH]

    movers = {(u, b): Mover(I[(u, b)], I[(UNIT, b)], f'{u}.{b}', f'{UNIT}.{b}') for u in DONORS for b in BOTH}

    # S1
    print('== S1 equality (donor vs fuzz_transport)')
    eqrows = []
    for fn, u, builds in FUNCS:
        for b in builds:
            ok, msg = eq_mod_pcrel(fn, movers[(u, b)])
            print(f'  {b:5} {u} {msg}')
            if not ok:
                die(msg)
            eqrows.append((fn, b, u, msg))

    # S2
    print('== S2 file set')
    jobs = []      # (unit, donor relpath, kind, role, source of the donor commit)
    frows = []
    for fn, u, builds in FUNCS:
        for b in builds:
            pre = 'U/' if b == 'ubsan' else ''
            for suf, role in (('_c', 'contract'), ('', 'walk')):
                k = f'{pre}Prog/{fn}{suf}.v'
                t = show(u, k)
                if t is None:
                    frows.append((fn, b, role, k, 'missing in the donor', u, ''))
                    print(f'  {k}: missing in the donor {u}')
                    continue
                if BAD.search(strip_comments(t)):
                    die(f'{u} {k}: {BAD.search(strip_comments(t)).group(0)} outside comments')
                nq = len(re.findall(r'\b(Qed|Defined)\.', strip_comments(t)))
                frows.append((fn, b, role, k, 'relocated', u, f'{nq} Qed/Defined'))
                jobs.append((u, k, 'relocated', f'{role} {fn} {b}', u))
    for fn, b, u, rk in WIDE:
        pre = 'U/' if b == 'ubsan' else ''
        for suf, role in (('_w_c', 'wide contract'), ('_w', 'wide walk')):
            k = f'{pre}Prog/{fn}{suf}.v'
            t = show(u, k, rk)
            if t is None:
                die(f'{u} {k}: absent at {rk} {refs[rk]}')
            if BAD.search(strip_comments(t)):
                die(f'{u} {k}: {BAD.search(strip_comments(t)).group(0)} outside comments')
            nq = len(re.findall(r'\b(Qed|Defined)\.', strip_comments(t)))
            frows.append((fn, b, role, k, 'relocated', f'{u} {rk}', f'{nq} Qed/Defined'))
            jobs.append((u, k, 'relocated', f'{role} {fn} {b}', rk))
    for u, k, mode in HELPERS:
        if show(u, k) is None:
            die(f'{u} {k}: helper absent at {refs[u]}')
        jobs.append((u, k, 'relocated' if mode == 'copy' else 'rewritten', f'helper {mode}', u))

    # S3
    print('== S3 transform')
    tcon = {}
    for b in BOTH:
        p = os.path.join(lib, ('U/' if b == 'ubsan' else '') + 'Prog/T/TContract.v')
        txt = open(p).read()
        tcon[b] = {n: int(re.search(r'Definition %s : Z := (0x[0-9a-fA-F]+|\d+)\.' % n, txt).group(1), 0)
                   for n in ('RELRO_BASE', 'RELRO_LEN')}
    written = {}   # target relpath (under lib/) -> (text, unit, donor relpath, kind, role, source)
    vrows = []
    unmovable = []   # --dry-run only: every numeral the rules cannot move

    def transform(u, k, t, rows):
        """S3 on the text t of donor file k of unit u; every moved numeral goes to rows as (k, line, old, new, how),
        line counted in the returned text"""
        b = 'ubsan' if k.startswith('U/') else 'plain'
        mv = movers[(u, b)]
        D, T = mv.D, mv.T
        notes = []
        for old, new, what in EDITS.get((u, k), []):
            if isinstance(old, re.Pattern):
                n = len(old.findall(t))
                if n != 1:
                    die(f'{u} {k}: EDIT pattern matches {n} times: {old.pattern!r}')
                t = old.sub(lambda _m: new, t)
            else:
                if t.count(old) != 1:
                    die(f'{u} {k}: EDIT text occurs {t.count(old)} times: {old!r}')
                t = t.replace(old, new)
            if what:
                notes.append(what)
        for rx, rep_, what in PROSE.get(u, []):
            t, n = rx.subn(rep_, t)
            if n:
                notes.append(what)
        base = os.path.basename(k)
        # (d) section rules, before the generic pass: their values go in as placeholders, out of its reach
        ph = {}

        def hold(lit, line, old, how):
            key = '@@SR%d@@' % len(ph)
            ph[key] = (lit, line, old, how)
            return key
        def sec_value(name, sec, att, old):
            """rule (d): the transport value of donor value old, after the controls"""
            ds, dz = D.secs[sec]
            ts, tz = T.secs[sec]
            if att == 'start':
                if old != ds:
                    die(f'{u} {k}: {name} = {old:#x} is not {u}.{b} {sec} start {ds:#x}')
                nv, cname = ts, 'RELRO_BASE'
            else:
                dp, tp = D.one(SPAN_HOLDS), T.one(SPAN_HOLDS)
                if not (0 < old <= dz and dp and ds <= dp[0] and dp[0] + dp[1] <= ds + old):
                    die(f'{u} {k}: {name} = {old} is not a block of {u}.{b} {sec} holding {SPAN_HOLDS}')
                if not (tp and ts <= tp[0] and tp[0] + tp[1] <= ts + tz):
                    die(f'{k}: {UNIT}.{b} {sec} does not hold {SPAN_HOLDS}')
                nv, cname = tz, 'RELRO_LEN'
            if sec == '.data.rel.ro' and tcon[b][cname] != nv:
                die(f'{k}: {name} would be {nv:#x}, TContract.v {cname} is {tcon[b][cname]:#x}')
            return nv
        for name, (sec, att) in SECTION_DEFS.get(base, {}).items():
            m = re.search(r'(Definition %s : Z := )(0x[0-9a-fA-F]+|\d+)(\.)' % name, t)
            if not m:
                die(f'{u} {k}: no Definition {name}')
            nv = sec_value(name, sec, att, int(m.group(2), 0))
            lit = hex(nv) if m.group(2).startswith('0x') else str(nv)
            t = t[:m.start(2)] + hold(lit, 0, m.group(2), f'section {sec} {att}') + t[m.end(2):]
        for rx, sec, att in SECTION_LITERALS.get(base, []):
            def srep(m):
                nv = sec_value('literal', sec, att, int(m.group(1), 0))
                return hold(str(nv), 0, m.group(1), f'section {sec} {att}')
            t = re.sub(rx, srep, t)
        # module path and image names
        t = modpath(t, u)
        t = re.sub(r'\b%s\.(plain|ubsan)\b' % u, UNIT + r'.\1', t)
        # numerals
        lines = t.split('\n')
        for i, l in enumerate(lines):
            def rep(m):
                tok = m.group(1)
                a = int(tok, 0)
                if not D.in_range(a):
                    return tok
                nv, how = mv.move(a)
                if nv is None:
                    msg = f'{u} {k}:{i + 1}: cannot move {tok} ({how})\n    {l.strip()}'
                    if A.dry_run:
                        unmovable.append(msg)
                        return tok
                    die(msg)
                if any(lo <= nv < hi for lo, hi in NOPOINT):
                    die(f'{u} {k}:{i + 1}: {tok} moves to {nv:#x}, inside the ELF header or build-id')
                new = hex(nv) if tok.startswith('0x') else str(nv)
                rows.append((k, i + 1, tok, new, how))
                return new
            lines[i] = NUMRE.sub(rep, l)
            for key in re.findall(r'@@SR\d+@@', lines[i]):
                lit, _, old, how = ph[key]
                lines[i] = lines[i].replace(key, lit)
                rows.append((k, i + 1, old, lit, f'{how} ({u}.{b} -> {UNIT}.{b})'))
        return '\n'.join(lines), notes

    STARTRE = re.compile(r'^(\(\*|Definition|Lemma|Fixpoint|Theorem|Corollary|Example|Section|End|Hint|Ltac|Local'
                         r'|Global|#|Arguments|Opaque|Transparent|Notation|Import|Open)')
    NAMERE = re.compile(r'^(?:Definition|Lemma|Fixpoint|Theorem|Corollary|Example)\s+([A-Za-z0-9_\']+)')

    def trim(u, k, t):
        """codec_img: the head up to TRIM_HEAD_END, then the items named in TRIM_KEEP, each with the comment right
        before it.  An item starts at a column-0 line outside a comment that opens a comment or a vernacular command,
        and runs to the next such line."""
        h = t.index(TRIM_HEAD_END)
        head, rest = t[:h], t[h + len(TRIM_HEAD_END):]
        items, depth = [], 0
        for line in rest.split('\n'):
            if depth == 0 and STARTRE.match(line):
                items.append([line])
            elif items:
                items[-1].append(line)
            depth += line.count('(*') - line.count('*)')
            if depth < 0:
                die(f'{u} {k}: unbalanced comment')
        out_items, prev_comment = [], None   # (index in items, had a blank line after it in the donor, text)
        for idx, it in enumerate(items):
            gap = bool(it) and not it[-1].strip()
            while it and not it[-1].strip():
                it.pop()
            txt = '\n'.join(it)
            m = NAMERE.match(it[0])
            if it[0].startswith('(*'):
                prev_comment = (idx, gap, txt)
                continue
            if m and m.group(1) in TRIM_KEEP:
                if prev_comment is not None:
                    out_items.append(prev_comment)
                out_items.append((idx, gap, txt))
            prev_comment = None
        found = [NAMERE.match(x).group(1) for _, _, x in out_items if NAMERE.match(x)]
        if sorted(found) != sorted(TRIM_KEEP):
            die(f'{u} {k}: kept items {sorted(found)} are not TRIM_KEEP {sorted(TRIM_KEEP)}')
        # an item that followed the previous kept item with no blank line in the donor follows it so here
        body, last = '', None
        for idx, gap, x in out_items:
            body += ('\n' if last is not None and last[0] == idx - 1 and not last[1] else '\n\n') + x
            last = (idx, gap)
        return head + TRIM_HEAD_END + body + '\n'

    for u, k, kind, role, rk in jobs:
        t = show(u, k, rk)
        if kind == 'rewritten':
            t = trim(u, k, t)
        rows = []
        t2, notes = transform(u, k, t, rows)
        donor_path = f'proofs/libdiginet/{u}/lib/{k}'
        notice = (f'(* Modified by Theorem Labs, {A.month}: relocated from libdiginet/{u} {donor_path} at {refs[rk]} '
                  f'to fuzz_transport\'s images' + ''.join('; ' + n for n in notes) + ' *)')
        L = t2.split('\n')
        j = 0
        while j < len(L) and re.match(r'^\(\*.*\*\)\s*$', L[j]) and L[j].count('(*') == L[j].count('*)'):
            j += 1
        L.insert(j, notice)
        vrows.extend((r[0], r[1] + (r[1] > j), r[2], r[3], r[4]) for r in rows)
        written[k] = ('\n'.join(L), u, donor_path, kind, role, rk)
        print(f'  {k} <- {u} ({kind}): {len(rows)} numerals moved')
    for msg in unmovable:
        print('UNMOVABLE ' + msg)

    # S4
    print('== S4 Require closure')
    reqre = re.compile(r'From\s+' + re.escape(MODP % UNIT) + r'((?:\.[A-Za-z0-9_]+)*)\s+Require\s+(?:Import\s+|Export\s+)?([^.]*)\.(?=\s)')
    reused = {}
    for k, (t, u, dp, kind, role, rk) in sorted(written.items()):
        for m in reqre.finditer(strip_comments(t).replace('\n', ' ') + ' '):
            sub = m.group(1).lstrip('.').replace('.', '/')
            for mod in m.group(2).split():
                rp = (sub + '/' if sub else '') + mod + '.v'
                if rp in written:
                    continue
                tp = os.path.join(lib, rp)
                if not os.path.exists(tp):
                    die(f'{k}: requires {rp}, absent from {UNIT} and not written here')
                if (rk, rp) in reused:
                    continue
                dt = show(u, rp, rk)
                if dt is None:
                    reused[(rk, rp)] = f'transport\'s own ({u} at {rk} has no such file)'
                    continue
                tt = open(tp).read()
                norm = lambda s, uu: [x for x in modpath(s, uu).split('\n')
                                      if not x.startswith('(* Modified by Theorem Labs')]
                a, bb = norm(dt, u), norm(tt, UNIT)
                if a == bb:
                    reused[(rk, rp)] = f'= {u}\'s at {rk} modulo module path'
                    continue
                ops = [o for o in difflib.SequenceMatcher(None, a, bb, autojunk=False).get_opcodes() if o[0] != 'equal']
                if rp.startswith(('Spec/', 'Lib/')) and all(o[0] == 'insert' for o in ops):
                    reused[(rk, rp)] = f'extends {u}\'s at {rk} ({sum(o[4] - o[3] for o in ops)} lines inserted)'
                    continue
                if rp.endswith('_c.v'):
                    moved, _ = transform(u, rp, dt, [])
                    if norm(moved, UNIT) == bb:
                        reused[(rk, rp)] = f'= {u}\'s at {rk} after the numeral move'
                        continue
                die(f'{k}: requires {rp}; {UNIT}\'s differs from {u}\'s at {refs[rk][:12]} ({len(ops)} hunks)')
    for (rk, rp), why in sorted(reused.items()):
        print(f'  reused {rp}: {why}')

    if A.dry_run:
        for r in vrows:
            print('  ' + '\t'.join(map(str, r)))
        print('dry run: nothing written' + (f'; {len(unmovable)} numerals cannot move' if unmovable else ''))
        return

    # S5
    print('== S5 write')
    man_path = os.path.join(evid, 'MANIFEST')
    list_path = os.path.join(evid, 'relocate-list.tsv')
    prev = {}
    if os.path.exists(list_path):
        for l in open(list_path):
            f = l.split()
            if len(f) >= 2 and not f[0].startswith('#'):
                prev[f[0]] = f[1]
    for k in written:
        rel = 'lib/' + k
        tp = os.path.join(lib, k)
        if os.path.exists(tp) and rel not in prev:
            die(f'{rel} exists and was not written by this script')
    for rel, kind in prev.items():
        if kind in ('relocated', 'rewritten') and rel[4:] not in written:
            os.remove(os.path.join(out, rel))
            print(f'  removed {rel} (written by an earlier run, not produced now)')
    os.makedirs(evid, exist_ok=True)
    for k, (t, u, dp, kind, role, rk) in written.items():
        tp = os.path.join(lib, k)
        os.makedirs(os.path.dirname(tp), exist_ok=True)
        open(tp, 'w').write(t)
    with open(os.path.join(evid, 'values.tsv'), 'w') as f:
        f.write('file\tline\told\tnew\thow\n')
        for r in vrows:
            f.write('\t'.join(map(str, r)) + '\n')
    with open(os.path.join(evid, 'files.tsv'), 'w') as f:
        f.write('function\tbuild\trole\tdonor file\tstatus\tdonor\tproofs\n')
        for r in frows:
            f.write('\t'.join(r) + '\n')
        for fn, b, u, msg in eqrows:
            f.write(f'{fn}\t{b}\tequality\t-\t{msg}\t{u}\t\n')
    # 20 moved numerals spread over the files: distinct (file, old) pairs, every n-th of the sorted list
    cand = sorted({(r[0], r[2]): r for r in vrows if r[4].startswith(('sym', 'end', 'str'))}.values())
    step = max(1, len(cand) // 20)
    sample = cand[::step][:20]
    with open(os.path.join(evid, 'sample20.tsv'), 'w') as f:
        f.write('file\tline\told\tnew\thow\n')
        for r in sample:
            f.write('\t'.join(map(str, r)) + '\n')
    lrows = []
    for k, (t, u, dp, kind, role, rk) in sorted(written.items()):
        lrows.append(f'lib/{k} {kind} {sha256b(t.encode())} {role} from {dp}@{refs[rk][:12]}')
    open(list_path, 'w').write(LIST_HEAD + '\n'.join(lrows) + '\n')
    rows = []
    for nm, kind, role in (('relocate.py', 'script', 'the script of record'),
                           ('relocate-list.tsv', 'evidence', 'the per-file list of the lib/ files written'),
                           ('values.tsv', 'evidence', 'every moved numeral (file line old new how)'),
                           ('files.tsv', 'evidence', 'function x build x file status, and the S1 equality rows'),
                           ('sample20.tsv', 'evidence', 'the 20 moved numerals of the hand cross-check'),
                           ('crosscheck.md', 'evidence', 'the hand cross-check of sample20.tsv against the ELF')):
        p = os.path.join(evid, nm)
        if os.path.exists(p):
            rows.append(f'{os.path.relpath(p, out)} {kind} {sha256b(open(p, "rb").read())} {role}')
    open(man_path, 'w').write('\n'.join(rows) + '\n')
    print(f'  {len(written)} files, {len(vrows)} numerals moved; relocate-list.tsv {len(lrows)} rows, MANIFEST {len(rows)} rows')
    for s in refs:
        print(f'  donor {s} at {refs[s]}')


if __name__ == '__main__':
    main()
