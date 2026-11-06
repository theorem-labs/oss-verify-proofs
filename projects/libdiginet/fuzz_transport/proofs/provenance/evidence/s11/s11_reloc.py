#!/usr/bin/env python3
"""s11_reloc.py -- piece S11 of libdiginet/fuzz_transport's ASan walks: relocate the 19 src/ walks that exist in the
sibling units libdiginet/fuzz_frame and libdiginet/fuzz_decode onto fuzz_transport's two ASan images (image A =
fuzz_transport.asan, image B = fuzz_transport.asan-ubsan). A DRY RUN: it writes the relocated files outside the tree,
the numeral tables, the name tables and one bycmp record per function and image; it builds nothing.

It generalizes libdiginet/fuzz_decode's arel_reloc.py (sha256 24f154f3dec8: frame A -> decode A, two functions) to
frame -> transport and decode -> transport, both images, and keeps the conventions of the image-A kit's relocation
kreloc.py (decode A kit -> transport A kit, sha256 in this directory's MANIFEST) for every name both touch.

usage: s11_reloc.py --repo REPO --img IMGDIR --out OUTDIR --tables TABDIR [--cmpkit KITDIR] [--keep-going]
  REPO    a clone holding the three commits below (read with `git show`, never the working copy)
  IMGDIR  the twelve images under role names: fuzz_{frame,decode,transport}.{asan,asan-ubsan}.{pin,unstripped};
          every sha256 is checked against the constants below, and each unstripped twin against its pin (PT_LOAD
          bytes equal outside the ELF header's section-header fields and the .note.gnu.build-id descriptor)
  OUTDIR  the relocated files: OUTDIR/<image>/proofs/libdiginet/fuzz_transport/lib/<image>/Prog/<file>.v
  TABDIR  reloc-numerals-{A,B}.tsv, namemap-{A,B}.tsv (every rename), names-{A,B}.tsv (only what the base does not
          define yet, by piece), files.tsv, summary.json and, with
          --cmpkit, bycmp_<f>_<image>.txt (cmpkit 86da41d3ef68 strictcmp3.py `cmp`, run with paths relative to
          IMGDIR's parent so no host path is printed); every code row of the numeral tables cites the record
  --keep-going  an unmapped numeral stops only its function (the function is reported, its files are not written);
          without it the first unmapped numeral stops the script. Either way the exit status is 1 when anything stopped.

What changes, in CODE only (outside comments and strings, kreloc.py's split_code):
  1. module paths libdiginet.fuzz_frame / libdiginet.fuzz_decode -> libdiginet.fuzz_transport;
  2. names (each map is built from the files, never from a pattern guess):
     - the listing's names, from the six listing files (source DgnFrame{Syms,Addr,List} / FrameB* / DgnDecode* /
       DgnDecodeB*, target DgnTransport{,B}{Syms,Addr,List} on the base): the symbol type (dfsym / fbsym / ddsym /
       ddbsym -> tsym / tbsym), each constructor X_<s> -> TS_<s> / TB_<s> (exact constructor sets, so frame_build's
       own FB_AT / FB_EPI ... are untouched), and <prefix>_<field> -> transport_<field> / transportb_<field>;
     - the kit's module names: DgnFrame* / DgnDecode* -> DgnTransport*, FrameB* / DgnDecodeB* / B's DgnFrameCg and
       DgnFrameLeafb -> DgnTransportB*, FrameFevt / DecodeFevt -> TransportFevt (frame -> decode by the counterpart
       defined in decode's tree, then kreloc.py's decode -> transport);
     - the kit's names: a frame_ / FRAME_ name defined in frame's kit -> its decode_ / DECODE_ counterpart when decode's
       kit of the same image defines it (arel_reloc.py's rule), then kreloc.py's renames (decode_cells -> transport_cells,
       decode_leaf_at -> transport_leaf_at, decode_leaf_wr_at -> transport_leaf_wr_at, DECODE_RO_RD -> TRANS_RO_RD,
       decode_ro_rd_unowned -> trans_ro_rd_unowned, decode_rom_no_errno -> trans_rom_no_errno, decodesegs0 ->
       transportsegs0); every other decode_ kit name is kept (kreloc.py and the kit-A inventory keep them);
       a listing-prefix name of the kit (PI_dgnframe, dgndec_tpi, frameb_segs_low, ...) -> frame -> decode by the
       counterpart decode's kit defines, then dgndec -> transport / dgndecb -> transportb;
     - the walks' own names: a frame_ / decode_ name a relocated file of the same image defines -> transport_ (the
       statement names frame_diginet_<f>_cg* / decode_diginet_<f>_cg* among them, design section 1.2);
     - image B's rule table (step 3, the names the image-B walks were patched by hand on the base with kit B):
       frame B's leaf-bridge names dgn_leafb_<x> -> decode_leafb_<x> when decode B's kit defines it (DgnDecodeBLeafb,
       relocated by kreloc.py to DgnTransportBLeafb), and LEAFB_B (dgn_leafb_segs_low -> DecodeFevt's decode_segs_low,
       the same statement); the core-B names CORE_B (decode B's DecodeTFIB / decodesegsB0
       -> transport B's YB1v / tfibsegs; the records FrameB (frame B) and TfibB (decode B) -> TransportB, lib/B/YD2l.v),
       each only where the source unit's lib/B (outside lib/B/Prog) defines it; and the module homes MOD_HOME_B
       (frame B's lib/B YCbq / YC5d -> transport's lib/Reusable, frame B's lib/B/Prog PaJournal -> transport's
       lib/A/Prog, image-free): a Require statement whose modules all move takes the new directory, and a module a
       rename makes twice on one Require line is kept once;
  3. numerals: every hex or decimal numeral in a source image's address range (>= 0x10000, inside a PT_LOAD) is
     mapped to the same symbol + offset of the target image, read from the unstripped twins' .symtab: the containing
     FUNC / OBJECT symbol (same name, same size on both sides), or a .got slot (the slot that holds the same symbol);
     for code the instruction at that offset is compared (equal, or a pc-relative jal / auipc / branch / lo12 of an
     auipc pair with every other field equal); anything else STOPS (file, line, value);
     decimal listing positions BASE + n inside the walk's function (n in [AF_f, AF_f + size) of the source listing)
     -> the same offset from the target listing's AF_f; listing object indices A_OBJ i (and the <x>_ew_obj index
     argument, and its `(i < N)%nat` bound = the listing's object count) -> the target index of the same object,
     keyed by symbol (a .got slot by the symbol it holds), as kreloc.py's A_OBJ 16 -> 93 / 17 -> 94;
  4. nothing else: every comment, every Copyright / SPDX / Modified-by line stays byte for byte, and no line is added
     (the integration owner's rule: no new Modified-by line); the script checks it (same line count, comments identical).
Hypothesis names that carry an object number (V16, E16, R16 in DgnBcHead.v) are binder names, not indices: kept
(arel_reloc.py renamed them; in decode B's DgnBcHead.v R18 / V18 also name register 18, so a rename would mislead).
Comments keep the source images' addresses (kreloc.py's comment rule); summary.json counts them per walk.
"""
import argparse
import bisect
import collections
import difflib
import hashlib
import io
import json
import os
import re
import struct
import subprocess
import sys

from elftools.elf.elffile import ELFFile

FRAME_REV = '02fe409d4aedd004fa028b5815c9f0fa8868ced5'    # libdiginet/fuzz_frame's ASan trunk branch (brief)
DECODE_REV = '7b6185922a15c0a042393f270448dd8af24a7ce4'   # libdiginet/fuzz_decode's ASan branch (brief)
BASE_REV = '41cf46de4c3084f1b3d4568ba60ac927cb1c8f47'     # the image-B ASan integration branch (step 3): the image-B
#                                                           kit (S07), S10 B, the image-B statements, the ASan line with
#                                                           image A's S11 walks; the listing files are c8ebc3afb25's,
#                                                           unchanged. Steps 1 and 2 ran on c8ebc3afb25 and 66fa526ea390
UNIT_ROOT = {'frame': 'proofs/libdiginet/fuzz_frame/lib/', 'decode': 'proofs/libdiginet/fuzz_decode/lib/',
             'transport': 'proofs/libdiginet/fuzz_transport/lib/'}
UNIT_REV = {'frame': FRAME_REV, 'decode': DECODE_REV, 'transport': BASE_REV}
# Image B's rule table (step 3). CORE_B: core-B names of a source unit's lib/B (outside lib/B/Prog) -> transport B's.
CORE_B = {'DecodeTFIB': 'YB1v', 'decodesegsB0': 'tfibsegs', 'FrameB': 'TransportB', 'TfibB': 'TransportB'}
# MOD_HOME_B: (directory under lib/, module) of a source unit's image-B Require -> transport's directory.
MOD_HOME_B = {('B', 'YCbq'): 'Reusable', ('B', 'YC5d'): 'Reusable', ('B.Prog', 'PaJournal'): 'A.Prog'}
# LEAFB_B: a frame B leaf-bridge name whose decode B counterpart is not decode_leafb_<x>: dgn_leafb_segs_low states
# DecodeFevt's decode_segs_low (in_img tfibsegs a -> 0 <= a < kLowMemEnd; TransportFevt on the base).
LEAFB_B = {'dgn_leafb_segs_low': 'decode_segs_low'}
REQ_RE = re.compile(r"(From OssFuzzTheorems\.Proofs\.libdiginet\.fuzz_transport\.lib\.)(\w+(?:\.\w+)*)"
                    r"(\s+Require(?:\s+(?:Import|Export))?)((?:\s+[A-Za-z_][\w']*)+)(\s*\.)")
BUILD = {'A': 'asan', 'B': 'asan-ubsan'}
SHA = {  # (unit, build, kind) -> sha256 (out-port2.SHA256SUMS; the proofs' own "Read from" lines)
    ('frame', 'asan', 'pin'): '34f028d3dec4b4236a88b3039fc878008179fb6d0b01d952f6669b418f394e70',
    ('frame', 'asan', 'unstripped'): '67d7e481d74edac58be0e018835f577491192d461b4a35bd4109dc4ab0494fd5',
    ('frame', 'asan-ubsan', 'pin'): '2574b26fc98e110739c61430d72921be4995c34c1a38f8b1ed258898809ae264',
    ('frame', 'asan-ubsan', 'unstripped'): 'ee3ea72a063b5cbb4537ebffeeb8b997226ecba44ac2e727839e55926b352371',
    ('decode', 'asan', 'pin'): '47bd808e8cb9d29fe1fbac5254b0cfe93d458f2dcc1dd19817566c94943a13e5',
    ('decode', 'asan', 'unstripped'): 'a7133a6c74e53c5a326c0a451e06329cc6a94185b4e83d1a1f4c86b8c45bd187',
    ('decode', 'asan-ubsan', 'pin'): '1c8e7ec206824fd70cb4247dcdc2f122b5d8dba1571da738ab1f3eac35f5a30a',
    ('decode', 'asan-ubsan', 'unstripped'): '50d7282d5a4b7c7e67ba8be8d3cf46866073ee6ec207bb5dd664fca33dd691ba',
    ('transport', 'asan', 'pin'): 'e89be137db17b720e0310addc2dcc601998945478a9102e6a9850b0566106350',
    ('transport', 'asan', 'unstripped'): '86efc3a80314981197619c115e313dbde50e8b86a6c5fefad4e5cc420250c792',
    ('transport', 'asan-ubsan', 'pin'): '41113a03c82fde8282db830ab5f4fbe376e392a38d22670b8cb8c9f02969ece4',
    ('transport', 'asan-ubsan', 'unstripped'): 'e217cb0a84f1e1810805155304b281a259ef83a85f50efcf0c65b40697bfa4dc',
}
CMPKIT_ID = '86da41d3ef68'
STRICTCMP3_SHA = '65688e94214a74664ffa83a21c283412a64b81f8a7eaa40f970a91f4eb1319b7'

# The 19 walks (design ASAN-WALKS.md section 3): (image, function) -> (source unit, file patterns). A pattern is a
# suffix of `<function>`; `*` = every file with that prefix; `DgnBc*` = the eight body_check pieces. `_c` (the image
# contract) is added for the footprint rows because their _F_c / .v / _cg Require it.
F_ROW = ['_c', '_F_c', '_F', '_cg', '']
WALKS = [
    ('A', 'diginet_mac_is_digidesign', 'frame', F_ROW),
    ('A', 'diginet_frame_is_keepalive', 'frame', F_ROW),
    ('A', 'diginet_frame_parse', 'frame', ['_cg', '_kit', '_seg_*', '_segs', '_walk']),
    ('A', 'diginet_frame_build', 'frame', ['_cg', '_iface', '_kit', '_seg_*', '_walk']),
    ('A', 'diginet_announce_parse', 'frame', F_ROW),
    ('A', 'diginet_cursor_init', 'decode', F_ROW),
    ('A', 'diginet_msg_next', 'decode', ['_cg', '_walk_lib', '_seg_*', '_segs', '_walk']),
    ('A', 'diginet_body_check', 'decode', ['_cg', '_cgW', 'DgnBc*']),
    ('B', 'diginet_mac_is_digidesign', 'frame', F_ROW),
    ('B', 'diginet_frame_is_keepalive', 'frame', F_ROW),
    ('B', 'diginet_frame_parse', 'frame', ['_cg', '_kit', '_seg_*', '_segs', '_walk']),
    ('B', 'diginet_frame_build', 'frame', ['_cg', '_cgW', '_cuts', '_iface', '_seg_*', '_w_*']),
    ('B', 'diginet_announce_parse', 'frame', ['_cg', '_cgW']),
    ('B', 'diginet_cursor_init', 'decode', F_ROW + ['_cgW']),
    ('B', 'diginet_msg_next', 'decode', ['_cg', '_cgW', '_walk_lib', '_seg_*', '_segs']),
    ('B', 'diginet_body_check', 'decode', ['_cg', '_cgW', 'DgnBc*']),
    ('B', 'diginet_sum16', 'frame', F_ROW),
    ('B', 'rd32', 'frame', F_ROW),
    ('B', 'copy_strz', 'frame', F_ROW),
]
FUNCS = sorted(set(w[1] for w in WALKS))

# Listing files: (unit, image) -> file stem (Syms / Addr / List follow).
LISTING = {('frame', 'A'): 'A/Prog/DgnFrame', ('frame', 'B'): 'B/Prog/FrameB', ('decode', 'A'): 'A/Prog/DgnDecode',
           ('decode', 'B'): 'B/Prog/DgnDecodeB', ('transport', 'A'): 'A/Prog/DgnTransport',
           ('transport', 'B'): 'B/Prog/DgnTransportB'}
# kreloc.py's decode -> transport renames of kit / S10 names (applied to decode's names of both images).
KRELOC_NAMES = {'decode_cells': 'transport_cells', 'decode_leaf_at': 'transport_leaf_at',
                'decode_leaf_wr_at': 'transport_leaf_wr_at', 'DECODE_RO_RD': 'TRANS_RO_RD',
                'decode_ro_rd_unowned': 'trans_ro_rd_unowned', 'decode_rom_no_errno': 'trans_rom_no_errno',
                'decodesegs0': 'transportsegs0'}
KRELOC_MODS = ['Img', 'PaLib', 'Pa', 'WalkKit', 'CJ', 'Kept', 'Leafb', 'CgRun', 'Cg', 'Syms', 'Addr', 'List']
LTAC_WORDS = {'try', 'repeat', 'first', 'solve', 'do', 'now', 'idtac', 'fail', 'progress', 'once', 'exactly_once'}
NOTICE = re.compile(r'^\(\* (Copyright|SPDX-License-Identifier|Modified by Theorem Labs)')
IDRE = re.compile(r"(?<![0-9A-Za-z_'])[A-Za-z_][A-Za-z0-9_']*")
COMB = re.compile(r"(?P<obj>\bA_OBJ\s+)(?P<objn>\d+)\b"
                  r"|(?P<ewobj>\b[A-Za-z_][\w']*_ew_obj\s+[A-Za-z_][\w']*\s+)(?P<ewn>\d+)\b"
                  r"|(?P<bnd>\(i < )(?P<bndn>\d+)(?=\)%nat)"
                  r"|(?P<id>(?<![0-9A-Za-z_'])[A-Za-z_][A-Za-z0-9_']*)"
                  r"|(?P<num>(?<![\w.'])(?:0x[0-9a-fA-F]+|\d+)(?![\w']))")
DEFRE = re.compile(r"^\s*(?:#\[[^\]]*\]\s*)?(?:Local\s+|Global\s+|Program\s+)?(Definition|Lemma|Theorem|Fixpoint|"
                   r"Inductive|Record|Ltac|Corollary|Fact|Remark|Let|Instance|Class|Variable|Variables|Hypothesis|"
                   r"Hypotheses|Example|Notation|Structure|CoFixpoint|Function|Abbreviation)\s+([A-Za-z_][A-Za-z0-9_']*)",
                   re.M)
FIELDRE = re.compile(r"(?:\{|;)\s*([A-Za-z_][\w']*)\s*:(?!=)")
TOKC = re.compile(r'\(\*|\*\)|"')


class Stop(Exception):
    pass


# ---------------------------------------------------------------------------------------------------------- sources
class Repo:
    def __init__(self, path):
        self.path = path

    def git(self, *a, inp=None):
        return subprocess.run(['git', '-C', self.path, *a], input=inp, capture_output=True, check=True).stdout

    def show(self, rev, path):
        return self.git('show', '%s:%s' % (rev, path)).decode()

    def ls(self, rev, path):
        return [l.decode() for l in self.git('ls-tree', '-r', '--name-only', rev, path).split()]

    def batch(self, rev, paths):
        out = self.git('cat-file', '--batch', inp=''.join('%s:%s\n' % (rev, p) for p in paths).encode())
        res, i = {}, 0
        for p in paths:
            nl = out.index(b'\n', i)
            hdr = out[i:nl].split()
            if hdr[-1] == b'missing':
                res[p], i = None, nl + 1
                continue
            n = int(hdr[2])
            res[p] = out[nl + 1:nl + 1 + n].decode('utf-8', 'replace')
            i = nl + 1 + n + 1
        return res


def split_code(s):
    """[(is_code, text)] -- kreloc.py's lexer: Rocq comments (nested; a string inside a comment is lexed as a
    string) and strings are not code."""
    out, i, n, start, depth = [], 0, len(s), 0, 0
    while i < n:
        if depth == 0 and s[i] == '"':
            out.append((True, s[start:i]))
            j = i + 1
            while j < n and not (s[j] == '"' and not (j + 1 < n and s[j + 1] == '"')):
                j += 2 if s[j] == '"' else 1
            out.append((False, s[i:j + 1]))
            i = start = j + 1
            continue
        if s.startswith('(*', i):
            if depth == 0:
                out.append((True, s[start:i]))
                start = i
            depth += 1
            i += 2
            continue
        if depth and s.startswith('*)', i):
            depth -= 1
            i += 2
            if depth == 0:
                out.append((False, s[start:i]))
                start = i
            continue
        if depth and s[i] == '"':
            j = s.find('"', i + 1)
            i = (j + 1) if j >= 0 else n
            continue
        i += 1
    out.append((depth == 0, s[start:]))
    return out


def strip_comments(s):
    out, depth, last, i, n = [], 0, 0, 0, len(s)
    while True:
        m = TOKC.search(s, i)
        if not m:
            if depth == 0:
                out.append(s[last:])
            break
        tok, j = m.group(0), m.start()
        if tok == '"':
            k = j + 1
            while True:
                q = s.find('"', k)
                if q < 0:
                    k = n
                    break
                if q + 1 < n and s[q + 1] == '"':
                    k = q + 2
                    continue
                k = q + 1
                break
            i = k
            continue
        if tok == '(*':
            if depth == 0:
                out.append(s[last:j])
            depth += 1
            i = j + 2
            continue
        if depth > 0:
            depth -= 1
            if depth == 0:
                last = j + 2
        i = j + 2
    return ''.join(out)


def defs(text, global_only=False):
    """Names a file defines; global_only drops Section binders (Variable / Hypothesis / Let / Context)."""
    t = strip_comments(text)
    s = set(m.group(2) for m in DEFRE.finditer(t)
            if not (global_only and m.group(1) in ('Variable', 'Variables', 'Hypothesis', 'Hypotheses', 'Let')))
    s |= set(m.group(1) for m in re.finditer(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)", t, re.M))
    for m in re.finditer(r'(?:Record|Structure|Class)\b', t):
        seg = t[m.start():m.start() + 4000]
        b, e = seg.find('{'), seg.find('}.')
        if 0 <= b < e:
            s |= set(f.group(1) for f in FIELDRE.finditer(seg[b:e]))
    return s


def requires(text):
    res = []
    for sent in re.split(r'\.(?=\s|$)', strip_comments(text)):
        s = ' '.join(sent.split())
        m = re.match(r'^(?:From ([\w.]+) )?Require (?:Import |Export )?(.*)$', s)
        if m:
            res += [((m.group(1) + '.') if m.group(1) else '') + x for x in m.group(2).split()]
    return res


# ----------------------------------------------------------------------------------------------------------- images
class Img:
    def __init__(self, path):
        self.path = path
        self.data = open(path, 'rb').read()
        self.sha = hashlib.sha256(self.data).hexdigest()
        e = ELFFile(io.BytesIO(self.data))
        self.loads = [(p['p_vaddr'], p['p_memsz'], p['p_offset'], p['p_filesz']) for p in e.iter_segments()
                      if p['p_type'] == 'PT_LOAD']
        self.secs = {s.name: (s['sh_addr'], s['sh_size'], s['sh_offset'], s['sh_type']) for s in e.iter_sections()}
        st = e.get_section_by_name('.symtab')
        self.syms = []
        if st is not None:
            for y in st.iter_symbols():
                self.syms.append((y.name, y['st_value'], y['st_size'], y['st_info']['type']))
        self.sized = sorted((a, z, n, t) for (n, a, z, t) in self.syms
                            if z > 0 and a > 0 and t in ('STT_FUNC', 'STT_OBJECT'))
        self.starts = [s[0] for s in self.sized]

    def in_image(self, v):
        return v >= 0x10000 and any(va <= v < va + ms for (va, ms, _, _) in self.loads)

    def rd(self, a, n):
        for (va, ms, off, fs) in self.loads:
            if va <= a and a + n <= va + fs:
                return self.data[off + a - va:off + a - va + n]
        return None

    def containing(self, v):
        i = bisect.bisect_right(self.starts, v)
        res = [s for s in self.sized[max(0, i - 64):i] if s[0] <= v < s[0] + s[1]]
        funcs = [s for s in res if s[3] == 'STT_FUNC']
        return funcs or res

    def named(self, name):
        return [s for s in self.sized if s[2] == name]

    def in_sec(self, v, name):
        s = self.secs.get(name)
        return s is not None and s[0] <= v < s[0] + s[1]


def twin_check(pin, twin):
    """PT_LOAD bytes of the unstripped twin equal its pin's, outside the ELF header's section-header fields
    (e_shoff 0x28-0x2f, e_shnum / e_shstrndx 0x3c-0x3f) and the .note.gnu.build-id descriptor."""
    if [l[:2] + l[3:] for l in pin.loads] != [l[:2] + l[3:] for l in twin.loads]:
        return False, 'PT_LOAD headers differ'
    bid = twin.secs.get('.note.gnu.build-id')
    allowed = set(range(0x28, 0x30)) | set(range(0x3c, 0x40))
    if bid:
        allowed |= set(range(bid[2] + 16, bid[2] + bid[1]))
    nd = 0
    for (p, t) in zip(pin.loads, twin.loads):
        a, b = pin.data[p[2]:p[2] + p[3]], twin.data[t[2]:t[2] + t[3]]
        if a != b:
            for k in range(len(a)):
                if a[k] != b[k]:
                    if p[2] + k not in allowed:
                        return False, 'PT_LOAD byte at file offset %#x differs' % (p[2] + k)
                    nd += 1
    return True, ('%d PT_LOAD(s) equal outside the ELF header section-header fields and the build-id descriptor '
                  '(%d bytes differ there)' % (len(pin.loads), nd))


def ins_len(b):
    return 4 if (b[0] & 3) == 3 else 2


def ins_check(si, sv, ti, tv):
    """The instruction at sv (source) and tv (target): equal, or pc-relative with every other field equal."""
    a, b = si.rd(sv, 4), ti.rd(tv, 4)
    if a is None or b is None:
        raise Stop('no file bytes at %#x / %#x' % (sv, tv))
    n = ins_len(a)
    if a[:n] == b[:n]:
        return 'instruction word equal (0x%s)' % a[:n][::-1].hex()
    if n != ins_len(b):
        raise Stop('instruction lengths differ at %#x / %#x' % (sv, tv))
    if n == 2:
        x, y = struct.unpack('<H', a[:2])[0], struct.unpack('<H', b[:2])[0]
        op = (x & 3, x >> 13)
        if op == (1, 5) and (y & 3, y >> 13) == op:
            return 'pc-relative instruction (c.j), parcels %#06x / %#06x' % (x, y)
        if op in ((1, 6), (1, 7)) and (y & 3, y >> 13) == op and (x >> 7) & 7 == (y >> 7) & 7:
            return 'pc-relative instruction (c.beqz/c.bnez), parcels %#06x / %#06x' % (x, y)
        raise Stop('2-byte parcels differ at %#x / %#x (%#06x / %#06x), not pc-relative' % (sv, tv, x, y))
    x, y = struct.unpack('<I', a)[0], struct.unpack('<I', b)[0]
    opc = x & 0x7f
    if opc != y & 0x7f:
        raise Stop('opcodes differ at %#x / %#x' % (sv, tv))
    if opc == 0x6f and (x >> 7) & 31 == (y >> 7) & 31:
        return 'pc-relative instruction (jal), words %#010x / %#010x' % (x, y)
    if opc == 0x17 and (x >> 7) & 31 == (y >> 7) & 31:
        return 'pc-relative instruction (auipc), words %#010x / %#010x' % (x, y)
    if opc == 0x63 and (x & 0x01fff000) == (y & 0x01fff000):
        return 'pc-relative instruction (branch), words %#010x / %#010x' % (x, y)
    if opc in (0x03, 0x13, 0x67, 0x23, 0x07, 0x27):
        same = (x & 0x000ff07f) == (y & 0x000ff07f) and (opc == 0x23 or (x >> 7) & 31 == (y >> 7) & 31)
        rs1 = (x >> 15) & 31
        pa, pb = si.rd(sv - 4, 4), ti.rd(tv - 4, 4)
        if same and pa and pb:
            px, py = struct.unpack('<I', pa)[0], struct.unpack('<I', pb)[0]
            if px & 0x7f == 0x17 and (px >> 7) & 31 == rs1 and py & 0x7f == 0x17 and (py >> 7) & 31 == rs1:
                return ('the pc-relative lo12 of the auipc pair at -4 (words %#010x / %#010x, every field but the '
                        'immediate equal)' % (x, y))
    raise Stop('instruction words differ at %#x / %#x (%#010x / %#010x), not a pc-relative field' % (sv, tv, x, y))


class AddrMap:
    """Source image -> target image, by symbol + offset."""

    def __init__(self, si, ti, image):
        self.si, self.ti, self.image = si, ti, image

    def got_holder(self, img, v):
        if not img.in_sec(v, '.got') or v % 8:
            return None
        w = struct.unpack('<Q', img.rd(v, 8))[0]
        at = [s for s in img.sized if s[0] == w]
        return at[0] if len(at) == 1 else None

    def map(self, v, bycmp):
        si, ti = self.si, self.ti
        cs = si.containing(v)
        if len(cs) == 1:
            a, z, name, typ = cs[0]
            tn = ti.named(name)
            if len(tn) != 1:
                raise Stop('symbol %s: %d sized copies in the target' % (name, len(tn)))
            ta, tz, _, ttyp = tn[0]
            if (tz, ttyp) != (z, typ):
                raise Stop('symbol %s: size / type %#x %s vs %#x %s' % (name, z, typ, tz, ttyp))
            tv = ta + (v - a)
            chk = 'same symbol+offset, symbol size %#x on both sides' % z
            if typ == 'STT_FUNC':
                chk += '; ' + ins_check(si, v, ti, tv) + ' (' + bycmp(name) + ')'
            return tv, '%s+%#x' % (name, v - a), chk
        if len(cs) > 1:
            raise Stop('%#x lies in %d symbols' % (v, len(cs)))
        h = self.got_holder(si, v)
        if h is not None:
            tn = ti.named(h[2])
            if len(tn) != 1:
                raise Stop('.got slot %#x holds %s: %d copies in the target' % (v, h[2], len(tn)))
            slots = [a for a in range(ti.secs['.got'][0], ti.secs['.got'][0] + ti.secs['.got'][1], 8)
                     if struct.unpack('<Q', ti.rd(a, 8))[0] == tn[0][0]]
            if len(slots) != 1:
                raise Stop('.got slot of %s: %d slots in the target' % (h[2], len(slots)))
            return slots[0], 'GOT[%s]' % h[2], ('the .got slot that holds %s (%#x / %#x), read from both images'
                                               % (h[2], h[0], tn[0][0]))
        raise Stop('%#x is in no sized symbol and no .got slot' % v)


# --------------------------------------------------------------------------------------------------------- listings
class Listing:
    def __init__(self, repo, unit, image):
        stem = UNIT_ROOT[unit] + LISTING[(unit, image)]
        rev = UNIT_REV[unit]
        self.files = {k: repo.show(rev, stem + k + '.v') for k in ('Syms', 'Addr', 'List')}
        syms = self.files['Syms']
        m = re.search(r'Inductive (\w+) : Type :=', syms)
        self.symtype = m.group(1)
        self.ctors = re.findall(r'^\| (\w+)', syms[m.end():], re.M)
        self.cpre = self.ctors[0].split('_')[0] + '_'
        assert all(c.startswith(self.cpre) for c in self.ctors)
        addr = self.files['Addr']
        self.prefix = re.search(r'Definition (\w+)_sigma', addr).group(1)
        self.sigma = {c: int(v, 16) for c, v in re.findall(r'^\| (\w+) => (0x[0-9a-f]+)', addr, re.M)
                      if c in self.ctors}
        ob = re.search(r'Definition \w+_obj \(i : nat\) : Z :=\nmatch i with\n(.*?)\nend\.', addr, re.S).group(1)
        self.obj = {int(i): int(v, 16) for i, v in re.findall(r'\| (\d+)%nat => (0x[0-9a-f]+)', ob)}
        self.nobj = int(re.search(r'_nobj : nat := (\d+)%nat', addr).group(1))
        self.af = {f: int(v, 16) for f, v in re.findall(r'Definition AF_(\w+) : Z := (0x[0-9a-f]+)\.',
                                                         self.files['List'])}
        self.names = set()
        for t in self.files.values():
            self.names |= defs(t)

    def obj_key(self, img, i):
        v = self.obj[i]
        cs = img.containing(v)
        if len(cs) == 1:
            return '%s+%#x' % (cs[0][2], v - cs[0][0])
        if img.in_sec(v, '.got') and v % 8 == 0:
            w = struct.unpack('<Q', img.rd(v, 8))[0]
            at = [s for s in img.sized if s[0] == w]
            if len(at) == 1:
                return 'GOT[%s]' % at[0][2]
        return None


# ------------------------------------------------------------------------------------------------------------ names
class Names:
    """The name map of one (unit, image) and its classification for the report."""

    def __init__(self, unit, image, src_l, tgt_l, kitdefs, dec_kitdefs, own_src, own_tgt, srcdef_where):
        self.unit, self.image = unit, image
        self.src_l, self.tgt_l = src_l, tgt_l
        self.kit, self.dkit = kitdefs, dec_kitdefs
        self.own_src, self.own_tgt = own_src, own_tgt
        self.where = srcdef_where
        self.tgt_defs = set()                   # the base's names a walk of this image sees (set by Reloc.run)
        self.tgt_defs_all = set()               # every name the base defines, both images (set by Reloc.run)
        tp = tgt_l.prefix                       # transport / transportb
        sp = src_l.prefix                       # dgnframe / frameb / dgndec / dgndecb
        self.dp = 'dgndec' if image == 'A' else 'dgndecb'
        self.tp, self.sp = tp, sp
        self.mods = {}
        if unit == 'frame':
            fm = {}
            if image == 'A':
                for x in KRELOC_MODS:
                    fm['DgnFrame' + x] = 'DgnDecode' + x
            else:
                for x in ['Addr', 'CJ', 'Img', 'List', 'Pa', 'PaLib', 'Syms']:
                    fm['FrameB' + x] = 'DgnDecodeB' + x
                fm['DgnFrameCg'] = 'DgnDecodeBCg'
                fm['DgnFrameLeafb'] = 'DgnDecodeBLeafb'
            fm['FrameFevt'] = 'DecodeFevt'
            self.frame_to_decode_mod = fm
        dmods = {}
        for x in KRELOC_MODS:
            if image == 'A':
                dmods['DgnDecode' + x] = 'DgnTransport' + x
            else:
                dmods['DgnDecodeB' + x] = 'DgnTransportB' + x
        dmods['DecodeFevt'] = 'TransportFevt'
        self.decode_to_transport_mod = dmods
        self.log = collections.Counter()      # (src, dst, rule) -> count
        self.kept = collections.Counter()     # kit names kept unchanged with no counterpart (rule)
        self.core_b_mods = set()              # modules of the source unit's lib/B/*.v (set by Reloc.run)

    def ren(self, t):
        u, image = self.unit, self.image
        if t in ('fuzz_frame', 'fuzz_decode'):
            return t, None                      # module paths are rewritten as a string before tokens
        # the listing's names
        if t == self.src_l.symtype:
            return self.tgt_l.symtype, 'listing type'
        if t in self.src_l.ctors:
            n = self.tgt_l.cpre + t[len(self.src_l.cpre):]
            return n, 'listing constructor'
        if t.startswith(self.sp + '_') and t in self.src_l.names:
            return self.tp + t[len(self.sp):], 'listing name'
        # module names
        if u == 'frame' and t in self.frame_to_decode_mod:
            d = self.frame_to_decode_mod[t]
            return self.decode_to_transport_mod.get(d, d), 'kit module (frame -> decode -> transport)'
        if u == 'decode' and t in self.decode_to_transport_mod:
            return self.decode_to_transport_mod[t], ('kit module (kreloc)' if image == 'A' else
                                                     'kit module (kreloc rule on image B: DgnDecodeB* -> DgnTransportB*)')
        # image B's core-B names (rule table CORE_B): only a name the source unit's lib/B (outside lib/B/Prog) defines,
        # or the module of such a file
        if image == 'B' and t in CORE_B and (t in self.core_b_mods or any(
                p.startswith('B/') and not p.startswith('B/Prog/') for p in self.where.get(t, ()))):
            return CORE_B[t], 'core B name (rule table, step 3)'
        # own names (defined by a relocated file of this image)
        m = re.match(r'^(frame|decode)_(.*)$', t)
        if m and (t in self.own_src or 'transport_' + m.group(2) in self.own_tgt):
            return 'transport_' + m.group(2), 'own name'
        # the kit's names
        if t in self.kit:
            if u == 'frame':
                d = None
                mm = re.match(r'^(frame_|FRAME_)(.*)$', t)
                if mm:
                    c = ('decode_' if mm.group(1) == 'frame_' else 'DECODE_') + mm.group(2)
                    if c in self.dkit:
                        d = c
                if d is None and self.sp in t:
                    c = t.replace(self.sp, self.dp)
                    if c in self.dkit:
                        d = c
                if d is None and image == 'B' and t.startswith('dgn_leafb_'):
                    c = LEAFB_B.get(t, 'decode_leafb_' + t[len('dgn_leafb_'):])
                    if c in self.dkit:
                        return c, 'kit name (rule table, step 3: frame B dgn_leafb_ -> decode B decode_leafb_ / LEAFB_B)'
                if d is None:
                    if re.match(r'^(frame_|FRAME_)', t) and t in self.dkit:
                        return t, 'kit name kept (decode\'s kit defines the same name)'
                    if re.match(r'^(frame_|FRAME_)', t) and t in self.tgt_defs:
                        return t, 'kit name kept (the base defines it under the same name)'
                    if re.match(r'^(frame_|FRAME_)', t) and t in self.tgt_defs_all:
                        return t, 'kit name kept (image A\'s base defines it, image-free; image B\'s twin pending S10 B)'
                    if re.match(r'^(frame_|FRAME_)', t) or self.sp in t:
                        return t, 'kit name: no counterpart in decode kit'
                    return t, None
                t2 = d
            else:
                t2 = t
            if t2 in KRELOC_NAMES:
                return KRELOC_NAMES[t2], 'kit name (kreloc)' if u == 'decode' else 'kit name (frame -> decode -> kreloc)'
            if self.dp in t2:
                return t2.replace(self.dp, self.tp), 'kit listing-prefix name'
            if u == 'frame':
                return t2, 'kit name (frame -> decode, kept as decode names it)'
            return t2, None
        return t, None


# ------------------------------------------------------------------------------------------------------- relocation
class Reloc:
    def __init__(self, args):
        self.args = args
        self.repo = Repo(args.repo)
        self.stops = []
        self.rows = {'A': [], 'B': []}
        self.files = []
        self.summary = collections.OrderedDict()
        self._clo = {}                          # (unit, path) -> the files that path Requires, transitively

    def load_images(self):
        self.img, self.twins = {}, {}
        for unit in ('frame', 'decode', 'transport'):
            for image, b in BUILD.items():
                pair = {}
                for kind in ('pin', 'unstripped'):
                    p = os.path.join(self.args.img, '%s.%s.%s' % ('fuzz_' + unit, b, kind))
                    im = Img(p)
                    if im.sha != SHA[(unit, b, kind)]:
                        sys.exit('%s: sha256 %s, expected %s' % (p, im.sha, SHA[(unit, b, kind)]))
                    pair[kind] = im
                ok, why = twin_check(pair['pin'], pair['unstripped'])
                if not ok:
                    sys.exit('twin check fuzz_%s.%s: %s' % (unit, b, why))
                self.twins[(unit, image)] = (pair['pin'].sha, pair['unstripped'].sha, why)
                self.img[(unit, image)] = pair['unstripped']

    def load_trees(self):
        self.tree = {}
        for unit in ('frame', 'decode'):
            paths = [p for p in self.repo.ls(UNIT_REV[unit], UNIT_ROOT[unit]) if p.endswith('.v')]
            self.tree[unit] = self.repo.batch(UNIT_REV[unit], paths)
        bpaths = [p for p in self.repo.ls(BASE_REV, UNIT_ROOT['transport']) if p.endswith('.v')]
        self.base = self.repo.batch(BASE_REV, bpaths)
        # what a walk of image A / B can see: every base file outside the other image's directory (image B walks also
        # see the lib/A modules they Require, added per walk in analyse)
        self.base_file_defs = {p[len(UNIT_ROOT['transport']):]: defs(t) for p, t in self.base.items()}
        self.base_vis = {i: set().union(*(d for p, d in self.base_file_defs.items()
                                         if not p.startswith(('B/' if i == 'A' else 'A/'))))
                         for i in 'AB'}
        self.base_mods = set(p[len(UNIT_ROOT['transport']):-2].replace('/', '.') for p in bpaths)
        self.srcdef = {}
        for unit in ('frame', 'decode'):
            w = collections.defaultdict(set)
            for p, t in self.tree[unit].items():
                for d in defs(t, global_only=True):
                    w[d].add(p[len(UNIT_ROOT[unit]):])
            self.srcdef[unit] = w

    def walk_files(self, unit, image, f, pats):
        pre = UNIT_ROOT[unit] + image + '/Prog/'
        names = sorted(p[len(pre):] for p in self.tree[unit] if p.startswith(pre) and '/' not in p[len(pre):])
        out = []
        for pt in pats:
            if pt == 'DgnBc*':
                out += [n for n in names if n.startswith('DgnBc')]
            elif pt.endswith('*'):
                out += [n for n in names if n.startswith(f + pt[:-1])]
            elif f + pt + '.v' in names:
                out.append(f + pt + '.v')
        return out

    def run(self):
        a = self.args
        self.load_images()
        self.load_trees()
        L = {(u, i): Listing(self.repo, u, i) for u in ('frame', 'decode', 'transport') for i in 'AB'}
        self.L = L
        sets = collections.OrderedDict()
        for image, f, unit, pats in WALKS:
            sets[(image, f)] = (unit, self.walk_files(unit, image, f, pats))
        self.sets = sets
        relfiles = {i: set(x for (im, f), (u, l) in sets.items() if im == i for x in l) for i in 'AB'}
        # kit definitions: lib/<image>/Prog files outside every walk set (and the unit's walks of other functions)
        walkre = re.compile(r'^(LLVMFuzzerTestOneInput|check_|spec_|cefB|crefB|diginet_)')
        kit = {}
        for unit in ('frame', 'decode'):
            for image in 'AB':
                w = collections.defaultdict(set)
                for name, ps in self.srcdef[unit].items():
                    for p in ps:
                        base = p.rsplit('/', 1)[-1]
                        if p.startswith(image + '/Prog/') and base not in relfiles[image] and not walkre.match(base):
                            w[name].add(p)
                kit[(unit, image)] = w
        own_src, own_tgt, own_all = {}, {}, {}
        for image in 'AB':
            s = set()
            for (im, f), (u, l) in sets.items():
                if im == image:
                    for x in l:
                        s |= defs(self.src(u, image, x))
            own_src[image] = set(t for t in s if re.match(r'^(frame|decode)_', t))
            own_tgt[image] = set('transport_' + t.split('_', 1)[1] for t in own_src[image])
            own_all[image] = s | own_tgt[image]
        self.own_tgt, self.own_all = own_tgt, own_all
        names = {}
        for unit in ('frame', 'decode'):
            for image in 'AB':
                names[(unit, image)] = Names(unit, image, L[(unit, image)], L[('transport', image)], kit[(unit, image)],
                                             kit[('decode', image)], own_src[image], own_tgt[image],
                                             self.srcdef[unit])
                names[(unit, image)].tgt_defs = self.base_vis[image]
                names[(unit, image)].tgt_defs_all = self.base_vis['A'] | self.base_vis['B']
                pre = UNIT_ROOT[unit] + 'B/'
                names[(unit, image)].core_b_mods = set(
                    p[len(pre):-2] for p in self.tree[unit] if p.startswith(pre) and '/' not in p[len(pre):])
        self.names = names
        self.bycmp = {}
        if a.cmpkit:
            self.run_bycmp()
        for (image, f), (unit, files) in sets.items():
            key = '%s %s' % (image, f)
            rec = self.summary[key] = collections.OrderedDict(
                image=image, function=f, source=unit, files=files, numerals=0, stopped=None)
            try:
                outs, rows = [], []
                for x in files:
                    text, r = self.relocate(unit, image, f, x, names[(unit, image)])
                    outs.append((x, text))
                    rows += r
            except Stop as e:
                rec['stopped'] = str(e)
                self.stops.append('%s: %s' % (key, e))
                if not a.keep_going:
                    break
                continue
            rec['numerals'] = len(rows)
            self.rows[image] += rows
            for x, text in outs:
                p = os.path.join(a.out, image, UNIT_ROOT['transport'], image, 'Prog', x)
                os.makedirs(os.path.dirname(p), exist_ok=True)
                with open(p, 'w') as fh:
                    fh.write(text)
                self.files.append((image, f, unit, x, hashlib.sha256(self.src(unit, image, x).encode()).hexdigest(),
                                   hashlib.sha256(text.encode()).hexdigest()))
            self.analyse(rec, unit, image, f, outs, names[(unit, image)])
        self.consistency()
        self.write_tables()
        for s in self.stops:
            print('STOP', s)
        return 1 if self.stops else 0

    def src(self, unit, image, x):
        return self.tree[unit][UNIT_ROOT[unit] + image + '/Prog/' + x]

    def run_bycmp(self):
        kit = self.args.cmpkit
        with open(os.path.join(kit, 'SHA256SUMS'), 'rb') as fh:
            if hashlib.sha256(fh.read()).hexdigest()[:12] != CMPKIT_ID:
                sys.exit('cmpkit: SHA256SUMS is not kit %s' % CMPKIT_ID)
        with open(os.path.join(kit, 'strictcmp3.py'), 'rb') as fh:
            if hashlib.sha256(fh.read()).hexdigest() != STRICTCMP3_SHA:
                sys.exit('cmpkit: strictcmp3.py sha256 differs')
        r = subprocess.run(['sha256sum', '-c', 'SHA256SUMS'], cwd=kit, capture_output=True, text=True)
        if r.returncode:
            sys.exit('cmpkit: sha256sum -c failed\n' + r.stdout + r.stderr)
        cwd = os.path.dirname(os.path.abspath(self.args.img))
        rel = os.path.basename(os.path.abspath(self.args.img))
        kitp = os.path.relpath(os.path.abspath(kit), cwd)
        for image, f, unit, _ in WALKS:
            b = BUILD[image]
            cmd = ['python3', os.path.join(kitp, 'strictcmp3.py'), 'cmp', f,
                   'S=%s/fuzz_%s.%s.unstripped' % (rel, unit, b), 'T=%s/fuzz_transport.%s.unstripped' % (rel, b),
                   'S:T']
            r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
            out = '# ' + ' '.join(cmd) + '\n' + r.stdout + r.stderr
            name = 'bycmp_%s_%s.txt' % (f, image)
            with open(os.path.join(self.args.tables, name), 'w') as fh:
                fh.write(out)
            row = [l for l in r.stdout.splitlines() if l.startswith(f + '\t')]
            verdict = 'NO ROW'
            if len(row) == 1:
                c = row[0].split('\t')
                ncs = len([l for l in r.stdout.splitlines() if l.startswith('CSTR\t')])
                verdict = '%s pcrel/real/unmeasured %s/%s/%s target-differ %s C-string acceptances %d' % (
                    c[6], c[7], c[8], c[9], c[11], ncs)
            self.bycmp[(image, f)] = (name, verdict)

    def bycmp_ref(self, image, f):
        def ref(sym):
            if (image, sym) in self.bycmp:
                return '%s: %s' % self.bycmp[(image, sym)]
            if not self.bycmp:
                return 'bycmp not run'
            return 'no bycmp record: %s is not a relocated function' % sym
        return ref

    def relocate(self, unit, image, f, x, nm):
        text = self.src(unit, image, x)
        si, ti = self.img[(unit, image)], self.img[('transport', image)]
        am = AddrMap(si, ti, image)
        sl, tl = self.L[(unit, image)], self.L[('transport', image)]
        af_s = sl.af.get(f)
        fsz = [s[1] for s in si.named(f) if s[3] == 'STT_FUNC']
        lrange = (af_s, af_s + fsz[0]) if af_s is not None and len(fsz) == 1 else None
        rows = []
        ref = self.bycmp_ref(image, f)
        parts = split_code(text)
        out, line = [], 1
        for code, seg in parts:
            if not code:
                out.append(seg)
                line += seg.count('\n')
                continue
            seg2 = re.sub(r'libdiginet\.fuzz_(frame|decode)\b', 'libdiginet.fuzz_transport', seg)

            def sub(m, seg2=seg2, line0=line):
                ln = line0 + seg2.count('\n', 0, m.start())
                if m.group('obj') is not None or m.group('ewobj') is not None:
                    i = int(m.group('objn') if m.group('obj') is not None else m.group('ewn'))
                    k = sl.obj_key(si, i)
                    tj = [j for j in tl.obj if tl.obj_key(ti, j) == k] if k else []
                    if len(tj) != 1:
                        raise Stop('%s:%d: listing object %d (%s) has %d matches in the target listing'
                                   % (x, ln, i, k, len(tj)))
                    rows.append((x, ln, str(i), 'listing object %d = %s' % (i, k), str(tj[0]),
                                 'listing object index keyed by symbol (source object %d, target object %d)'
                                 % (i, tj[0])))
                    return (m.group('obj') or m.group('ewobj')) + str(tj[0])
                if m.group('bnd') is not None:
                    full = seg2[seg2.rfind('\n', 0, m.start()) + 1:m.start()]
                    if not re.search(r'Lemma \w+_ew_obj\b', full):
                        return m.group(0)
                    n = int(m.group('bndn'))
                    if n != sl.nobj:
                        raise Stop('%s:%d: object bound %d is not the listing object count %d' % (x, ln, n, sl.nobj))
                    rows.append((x, ln, str(n), 'listing object count', str(tl.nobj),
                                 'the object bound of the _ew_obj lemma = the listing object count'))
                    return m.group('bnd') + str(tl.nobj)
                if m.group('id') is not None:
                    t = m.group('id')
                    n, why = nm.ren(t)
                    if why:
                        nm.log[(t, n, why)] += 1
                    return n
                tok = m.group('num')
                v = int(tok, 16) if tok.lower().startswith('0x') else int(tok)
                if si.in_image(v):
                    try:
                        tv, sym, chk = am.map(v, ref)
                    except Stop as e:
                        raise Stop('%s:%d: numeral %s: %s' % (x, ln, tok, e))
                    rows.append((x, ln, tok, sym, ('%#x' % tv) if tok.lower().startswith('0x') else str(tv), chk))
                    return ('%#x' % tv) if tok.lower().startswith('0x') else str(tv)
                if not tok.lower().startswith('0x') and lrange and lrange[0] <= v < lrange[1] and v >= 4096:
                    if not re.search(r'BASE\s*\+\s*$', seg2[max(0, m.start() - 24):m.start()]):
                        raise Stop('%s:%d: decimal %s lies in AF_%s\'s listing range but is not a BASE + n position'
                                   % (x, ln, tok, f))
                    nv = tl.af[f] + (v - af_s)
                    rows.append((x, ln, tok, 'AF_%s+%#x' % (f, v - af_s), str(nv),
                                 'listing position re-based: source AF_%s = %#x, target AF_%s = %#x'
                                 % (f, af_s, f, tl.af[f])))
                    return str(nv)
                return tok
            new = COMB.sub(sub, seg2)
            if image == 'B':
                new = self.require_rules(new, x, nm)
            if new.count('\n') != seg.count('\n'):
                raise Stop('%s: a code change moved a line' % x)
            out.append(new)
            line += seg.count('\n')
        res = ''.join(out)
        # the invariants: same lines, comments and notice lines byte for byte
        a_l, b_l = text.split('\n'), res.split('\n')
        assert len(a_l) == len(b_l), x
        for la, lb in zip(a_l, b_l):
            if NOTICE.match(la):
                assert la == lb, (x, la)
        ca = [s for c, s in split_code(text) if not c]
        cb = [s for c, s in split_code(res) if not c]
        assert ca == cb, x
        return res, rows

    def require_rules(self, text, x, nm):
        """Image B's module homes (MOD_HOME_B: a Require statement whose modules all move takes the new directory) and
        the duplicate a rename makes on one Require line (CORE_B's DecodeTFIB -> YB1v beside YB1v: kept once)."""
        def fix(m):
            d, mods_s = m.group(2), m.group(4)
            mods = mods_s.split()
            homes = set(MOD_HOME_B.get((d, mm), d) for mm in mods)
            if len(homes) != 1:
                raise Stop('%s: a Require of lib.%s mixes module homes %s' % (x, d, sorted(homes)))
            nd = homes.pop()
            if nd != d:
                for mm in mods:
                    nm.log[('lib.%s.%s' % (d, mm), 'lib.%s.%s' % (nd, mm), 'module home (rule table, step 3)')] += 1
            if len(set(mods)) != len(mods):
                if '\n' in mods_s:
                    raise Stop('%s: a duplicate module on a Require that spans lines' % x)
                keep = []
                for mm in mods:
                    if mm not in keep:
                        keep.append(mm)
                    else:
                        nm.log[(mm, mm, 'duplicate module on one Require line kept once (rule table, step 3)')] += 1
                mods_s = mods_s[:len(mods_s) - len(mods_s.lstrip())] + ' '.join(keep)
            return m.group(1) + nd + m.group(3) + mods_s + m.group(5)
        return REQ_RE.sub(fix, text)

    def req_closure(self, unit, path):
        """The files (paths under the unit's lib/) that the file at path Requires, transitively, itself included."""
        memo = self._clo
        if (unit, path) in memo:
            return memo[(unit, path)]
        seen, stack = set(), [path]
        while stack:
            p = stack.pop()
            if p in seen:
                continue
            seen.add(p)
            t = self.tree[unit].get(UNIT_ROOT[unit] + p)
            if t is None:
                continue
            for r in requires(t):
                mm = re.match(r'OssFuzzTheorems\.Proofs\.libdiginet\.fuzz_%s\.lib\.(.*)$' % unit, r)
                if mm:
                    stack.append(mm.group(1).replace('.', '/') + '.v')
        memo[(unit, path)] = seen
        return seen

    def piece(self, image, p):
        """Which piece of the plan provides a source definition / module p (a path under the unit's lib/)."""
        base = p.rsplit('/', 1)[-1][:-2]
        if p.startswith(image + '/Prog/'):
            if re.match(r'^(DgnFrameCg|DgnDecodeCg|DgnDecodeBCg)$', base):
                return 'S10 (%s)' % p
            return ('S06 kit A (%s)' if image == 'A' else 'S07 kit B (%s)') % p
        if p in (image + '/AsanCells.v', image + '/Img0.v'):
            return ('S06 kit A (%s)' if image == 'A' else 'S07 kit B (%s)') % p
        if p.startswith(image + '/'):
            return ('core A, TCA (%s)' if image == 'A' else 'core B, TCB (%s)') % p
        if p in ('Lib/ExecF.v', 'Lib/StepF.v'):
            return 'S06 kit A (%s)' % p
        return 'not on the base (%s)' % p

    def analyse(self, rec, unit, image, f, outs, nm):
        """Modules and names of the relocated files that the base does not define yet, by the piece that brings them;
        kit names with no rule; unit-specific names nothing accounts for."""
        own_mods = set(x[:-2] for (im, g), (u, l) in self.sets.items() if im == image for x in l)
        own_all = self.own_all[image]
        vis = set(self.base_vis[image])
        for x, text in outs:
            for r in requires(text):
                mm = re.match(r'OssFuzzTheorems\.Proofs\.libdiginet\.fuzz_transport\.lib\.(A\..*)$', r)
                if mm and mm.group(1).replace('.', '/') + '.v' in self.base_file_defs:
                    vis |= self.base_file_defs[mm.group(1).replace('.', '/') + '.v']
        pend_mods, pend_names, unmapped, residual = (collections.Counter(), collections.Counter(),
                                                     collections.Counter(), collections.Counter())
        cmt_addr = 0
        marker = re.compile(r'fuzz_frame|fuzz_decode|DgnFrame|DgnDecode|FrameB|FrameFevt|DecodeFevt|dfsym|fbsym|ddsym|'
                            r'ddbsym|dgnframe|frameb|dgndec|^DF_|^DD_|^DDB_|^frame_|^decode_|TFIB|^T06_')
        for x, text in outs:
            for r in requires(text):
                mm = re.match(r'OssFuzzTheorems\.Proofs\.libdiginet\.fuzz_transport\.lib\.(.*)$', r)
                if mm and mm.group(1) not in self.base_mods and mm.group(1).rsplit('.', 1)[-1] not in own_mods:
                    srcmod = [m2 for m2 in requires(self.src(unit, image, x))
                              if m2.rsplit('.', 1)[-1] == r.rsplit('.', 1)[-1] or
                              nm.ren(m2.rsplit('.', 1)[-1])[0] == r.rsplit('.', 1)[-1]]
                    sp = srcmod[0].split('.lib.', 1)[1].replace('.', '/') + '.v' if srcmod else mm.group(1)
                    pend_mods['%s <- %s' % (mm.group(1), self.piece(image, sp))] += 1
            stoks = set()
            for c, s in split_code(self.src(unit, image, x)):
                if c:
                    stoks |= set(IDRE.findall(s))
            clo = self.req_closure(unit, image + '/Prog/' + x)
            for t in stoks:
                n, why = nm.ren(t)
                if n in own_all or n in vis or t not in self.srcdef[unit] or t in LTAC_WORDS:
                    continue
                # a reference only if a file the walk file Requires (transitively) defines the name; otherwise the
                # token is a local binder that shares a global's name (e.g. XL, CA)
                ps = [p for p in sorted(self.srcdef[unit][t]) if p in clo]
                ps = sorted(ps, key=lambda p: (0 if t in nm.kit and p in nm.kit[t] else 1, p))
                if not ps:
                    continue
                if why == 'kit name: no counterpart in decode kit':
                    unmapped[(t, self.piece(image, ps[0]))] += 1
                else:
                    pend_names[(t, n, self.piece(image, ps[0]))] += 1
            accounted = set(k[1] for k in pend_names) | set(k[0] for k in unmapped)
            for c, s in split_code(text):
                if c:
                    for t in set(IDRE.findall(s)):
                        if marker.search(t) and t not in own_all and t not in vis and t not in accounted:
                            residual[t] += 1
                elif s.startswith('(*'):
                    for m in re.finditer(r"(?<![\w.'])(0x[0-9a-fA-F]+|\d{5,})(?![\w'])", s):
                        v = int(m.group(1), 0) if m.group(1).startswith('0x') else int(m.group(1))
                        if self.img[(unit, image)].in_image(v):
                            cmt_addr += 1
        rec['comment_image_numerals_kept'] = cmt_addr
        rec['modules_pending'] = sorted(pend_mods)
        rec['names_pending'] = sorted('%s%s <- %s' % (t, '' if n == t else ' -> ' + n, p) for (t, n, p) in pend_names)
        rec['names_unmapped'] = sorted('%s <- %s' % k for k in unmapped)
        rec['residual_unit_names'] = sorted(residual)

    def consistency(self):
        """A cross-check only: frame's statement file of diginet_body_check (both images), relocated with frame's maps,
        compared (code) with decode's relocated file. Decode's file is the one of record on both images (the integration
        owner's decision of 2026-10-31 04:08Z: image B's core is decode's lineage); frame's text is never written to OUTDIR."""
        self.consist = []
        for image in 'AB':
            x = 'diginet_body_check_cg.v'
            nm = self.names[('frame', image)]
            saved = collections.Counter(nm.log)
            try:
                tf, _ = self.relocate('frame', image, 'diginet_body_check', x, nm)
            except Stop as e:
                self.consist.append((image, x, 'STOP %s' % e, []))
                continue
            finally:
                nm.log = saved
            p = os.path.join(self.args.out, image, UNIT_ROOT['transport'], image, 'Prog', x)
            if not os.path.exists(p):
                self.consist.append((image, x, 'decode file not written', []))
                continue
            td = open(p).read()

            def code(t):
                return [' '.join(l.split()) for l in strip_comments(t).split('\n') if l.strip()]
            a, b = code(tf), code(td)
            diff = [l for l in difflib.unified_diff(a, b, 'frame', 'decode', lineterm='', n=0)
                    if l[:1] in '+-' and not l.startswith(('+++', '---'))]
            self.consist.append((image, x, 'EQUAL (code)' if a == b else
                                 'DIFFERS (code): %d of %d code lines differ' % (len([l for l in diff if l[0] == '-']),
                                                                                len(a)), diff))

    def write_tables(self):
        t = self.args.tables
        os.makedirs(t, exist_ok=True)
        for image in 'AB':
            with open(os.path.join(t, 'reloc-numerals-%s.tsv' % image), 'w') as fh:
                fh.write('# file\tline\tsource value\tsymbol+offset\ttarget value\tcheck\n')
                for r in self.rows[image]:
                    fh.write('\t'.join(str(c) for c in r) + '\n')
            with open(os.path.join(t, 'namemap-%s.tsv' % image), 'w') as fh:
                fh.write('# every rename of image %s: source unit\tsource name\ttarget name\trule\tuses\n' % image)
                for unit in ('frame', 'decode'):
                    nm = self.names[(unit, image)]
                    for (a, b, why), c in sorted(nm.log.items()):
                        fh.write('%s\t%s\t%s\t%s\t%d\n' % (unit, a, b, why, c))
            pend = collections.defaultdict(set)
            for k, r in self.summary.items():
                if not k.startswith(image + ' '):
                    continue
                for m in r.get('modules_pending', []):
                    a, b = m.split(' <- ')
                    pend[('module', a, a, b)].add(r['function'])
                for m in r.get('names_pending', []):
                    a, b = m.split(' <- ')
                    src, _, tgt = a.partition(' -> ')
                    pend[('name', src, tgt or src, b)].add(r['function'])
                for m in r.get('names_unmapped', []):
                    a, b = m.split(' <- ')
                    pend[('name, no rule', a, '-', b)].add(r['function'])
            with open(os.path.join(t, 'names-%s.tsv' % image), 'w') as fh:
                fh.write('# what image %s\'s relocated walks name that base %s does not define yet: kind\tsource name\t'
                         'target name\tthe piece that brings it (the source file that defines it)\twalks\n'
                         % (image, BASE_REV[:12]))
                for (kind, a, b, p), ws in sorted(pend.items()):
                    fh.write('%s\t%s\t%s\t%s\t%s\n' % (kind, a, b, p, ' '.join(sorted(ws))))
        with open(os.path.join(t, 'files.tsv'), 'w') as fh:
            fh.write('# image\tfunction\tsource unit\tfile\tsource sha256\trelocated sha256\n')
            for r in self.files:
                fh.write('\t'.join(r) + '\n')
        summ = {'walks': self.summary, 'twins': {'%s %s' % k: v for k, v in self.twins.items()},
                'bycmp': {'%s %s' % k: v for k, v in self.bycmp.items()}, 'consistency': self.consist,
                'stops': self.stops}
        with open(os.path.join(t, 'summary.json'), 'w') as fh:
            json.dump(summ, fh, indent=1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--repo', required=True)
    ap.add_argument('--img', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--tables', required=True)
    ap.add_argument('--cmpkit')
    ap.add_argument('--keep-going', action='store_true')
    a = ap.parse_args()
    os.makedirs(a.tables, exist_ok=True)
    sys.exit(Reloc(a).run())


if __name__ == '__main__':
    main()
