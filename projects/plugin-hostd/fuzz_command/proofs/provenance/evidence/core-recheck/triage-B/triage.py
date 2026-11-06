#!/usr/bin/env python3
"""triage.py -- measured triage of the flagged rows of two port_addr_check 3d2eee813cce runs on lib/B of
plugin-hostd/fuzz_command (image B = fuzz_command.asan-ubsan):

  RB   donor cgif_file_fuzzer lib/Y*.v -> ours lib/B/Y*.v (the OPEN rows left by base_triage.py: RB.open.tsv)
  RAB  ours lib/A/A*.v -> ours lib/B/Y*.v (the relay view: every STALE-* / SAME-VALUE-DIFFERENT-OBJECT row, and
       the open DIFFERENT-SYMBOL / KIND-CHANGED / NON-ADDRESS-CHANGED rows; UNRESOLVED rows are keying artefacts
       of a run that keys both sides on B and are not taken)

Every row gets one rule. A rule finds the numeral's ROLE on the ported line (comments blanked, the gate's numeral
scan), computes the value that role must have from a MEASUREMENT (image B's symbol table, section and segment
headers, image bytes, GOT words, the asan_globals descriptors, the generated start-up certificate, or the text of
the definition the role restates) and compares. judge(v) is that comparison, so the controls re-judge each settled
row with v+4 and with the donor's value (cgif's for RB, the A twin's for RAB) and must see a refusal; a rule whose
claim holds for every value (a list that is sound for any content, an unread name) is marked value-independent.

Usage:
  triage.py --lib LIB --cgif-lib CGIF_LIB --img-b PIN TWIN --img-a PIN TWIN --img-cgif-b PIN TWIN \
            --rb-open RB.open.tsv --rab-full RAB.full.tsv --rab-open RAB.open.tsv --out DIR
Writes DIR/triage-rows.tsv (RB rows), DIR/rab-rows.tsv (RAB rows), DIR/controls.tsv (one control row per settled
row), DIR/code-findings.tsv (FINDING rows), DIR/relay-moved.tsv (round A values the relay changed, judged),
DIR/extra-findings.tsv (findings outside the triaged rows), DIR/kept-counts.tsv (counts a lib/B file says it took
from image A, re-measured on image B), and prints the counts.
"""
import argparse
import bisect
import collections
import csv
import hashlib
import io
import os
import re
import sys

from elftools.elf.elffile import ELFFile

csv.field_size_limit(10 ** 9)
NUM = r'(0x[0-9a-fA-F]+|\d+)'
NUMRX = re.compile(r"(?<![A-Za-z0-9_'.])(0x[0-9a-fA-F]+|\d+)(?![0-9A-Za-z_'])")


def ival(t):
    return int(t, 16) if t.lower().startswith('0x') else int(t)


# ---------------------------------------------------------------------------------------------------- images
class Img:
    """One image: loadable bytes from the PIN, symbols from the unstripped TWIN (same link)."""

    def __init__(self, role, pin, twin):
        self.role = role
        self.pin = open(pin, 'rb').read()
        tw = open(twin, 'rb').read()
        self.sha = hashlib.sha256(self.pin).hexdigest()[:12]
        self.tsha = hashlib.sha256(tw).hexdigest()[:12]
        e = ELFFile(io.BytesIO(self.pin))
        t = ELFFile(io.BytesIO(tw))
        self.ehdr = e.header
        self.loads = [(p['p_vaddr'], p['p_filesz'], p['p_memsz'], p['p_offset'], p['p_flags'])
                      for p in e.iter_segments() if p['p_type'] == 'PT_LOAD']
        self.secs = {s.name: (s['sh_addr'], s['sh_addr'] + s['sh_size']) for s in e.iter_sections() if s['sh_addr']}
        self.syms = []
        for s in t.get_section_by_name('.symtab').iter_symbols():
            if s.name and s['st_value'] and s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT', 'STT_NOTYPE'):
                if s.name.startswith('$'):
                    continue
                self.syms.append((s['st_value'], s['st_size'], s.name, s['st_info']['type']))
        self.syms.sort()
        self.addrs = [x[0] for x in self.syms]
        self.byname = collections.defaultdict(list)
        for x in self.syms:
            self.byname[x[2]].append(x)
        self.lo = min(v for v, *_ in self.loads)
        self.top = (max(v + m for v, f, m, o, fl in self.loads) + 0xfff) & ~0xfff
        self.file_end = max(v + f for v, f, m, o, fl in self.loads)
        self.globals = self._globals()

    def read(self, a, n):
        for va, fs, ms, off, fl in self.loads:
            if va <= a and a + n <= va + fs:
                return self.pin[off + a - va: off + a - va + n]
            if va <= a and a + n <= va + ms:
                return bytes(n)  # NOBITS part of a load: zero at load
        return None

    def word(self, a, n):
        b = self.read(a, n)
        return None if b is None else int.from_bytes(b, 'little')

    def at(self, a):
        """[(name, offset, size)] of sized symbols containing a, plus symbols starting at a."""
        i = bisect.bisect_right(self.addrs, a)
        out = []
        for j in range(i - 1, max(-1, i - 600), -1):
            v, sz, n, ty = self.syms[j]
            if v == a or v <= a < v + sz:
                out.append((n, a - v, sz))
        out.sort(key=lambda x: (x[1], -x[2]))
        return out

    def name(self, a):
        s = self.at(a)
        if not s:
            sec = self.sec(a)
            return f'{a:#x} ({sec or "no section"}, no symbol)'
        n, o, sz = s[0]
        return f'{n}+{o:#x} ({sz} bytes)'

    def sec(self, a):
        for n, (lo, hi) in self.secs.items():
            if lo <= a < hi:
                return n
        return None

    def cstr(self, a, n=96):
        b = self.read(a, n) or b''
        return b.split(b'\0')[0].decode('latin1')

    def _globals(self):
        """asan_globals descriptors (struct __asan_global: beg, size, size_with_redzone, name, module, dyn_init,
        location, odr_indicator: eight 8-byte words)."""
        if 'asan_globals' not in self.secs:
            return []
        lo, hi = self.secs['asan_globals']
        out = []
        for a in range(lo, hi, 64):
            w = [self.word(a + 8 * i, 8) for i in range(8)]
            out.append(dict(at=a, beg=w[0], size=w[1], szrz=w[2], name=self.cstr(w[3]), odr=w[7]))
        return out

    def first_poison(self, lo, hi):
        """first granule in [lo, hi) whose shadow byte is not 0 at start-up: the granule holding a global's end
        (beg + size not a multiple of 8) or the first granule of its redzone."""
        best = None
        for g in self.globals:
            p = (g['beg'] + g['size']) // 8 * 8
            e = g['beg'] + g['szrz']
            if p < hi and e > lo:
                q = max(p, lo // 8 * 8)
                best = q if best is None else min(best, q)
        return best

    def poison_end_below(self, a):
        """end of the last poisoned granule run that ends at or below a"""
        ends = [g['beg'] + g['szrz'] for g in self.globals if g['beg'] + g['szrz'] <= a]
        return max(ends) if ends else None


# ------------------------------------------------------------------------------------------- RISC-V (few forms)
def sext(v, b):
    return v - (1 << b) if v >> (b - 1) & 1 else v


def jal_imm(w):
    return sext(((w >> 31) & 1) << 20 | ((w >> 12) & 0xff) << 12 | ((w >> 20) & 1) << 11 | ((w >> 21) & 0x3ff) << 1, 21)


def is_call(img, pc):
    """the instruction before pc is jal ra / jalr ra / c.jalr (2-byte): pc is a return site"""
    w4 = img.word(pc - 4, 4)
    if w4 is not None and (w4 & 0x7f) in (0x6f, 0x67) and ((w4 >> 7) & 31) == 1:
        return 'jal ra' if (w4 & 0x7f) == 0x6f else 'jalr ra'
    w2 = img.word(pc - 2, 2)
    if w2 is not None and (w2 & 0xf07f) == 0x9002 and (w2 >> 7) & 31:
        return 'c.jalr'
    return None


# ------------------------------------------------------------------------------------------------ source text
def blank_comments(text):
    """text with every (nested) comment replaced by spaces, newlines kept; strings are kept as they are"""
    out, last, depth, start = [], 0, 0, 0
    tok = re.compile(r'\(\*|\*\)|"')
    i, n = 0, len(text)
    while True:
        m = tok.search(text, i)
        if not m:
            break
        t = m.group(0)
        if depth == 0 and t == '"':
            j = text.find('"', m.end())
            i = n if j < 0 else j + 1
            continue
        if t == '(*':
            if depth == 0:
                out.append(text[last:m.start()])
                start = m.start()
            depth += 1
        elif t == '*)' and depth:
            depth -= 1
            if depth == 0:
                out.append(re.sub(r'[^\n]', ' ', text[start:m.end()]))
                last = m.end()
        i = m.end()
    if depth:
        out.append(re.sub(r'[^\n]', ' ', text[start:]))
    else:
        out.append(text[last:])
    return ''.join(out)


class Tree:
    """a unit's lib/ folder; a bare file name of a gate row (dst_file Y<xx>.v) is lib/B/<name>"""

    def __init__(self, root, default_dir=None):
        self.root = root
        self.default_dir = default_dir
        self.cache = {}

    def path(self, rel):
        p = os.path.join(self.root, rel)
        if self.default_dir and '/' not in rel and not os.path.exists(p):
            p = os.path.join(self.root, self.default_dir, rel)
        return p

    def lines(self, rel):
        if rel not in self.cache:
            t = open(self.path(rel), encoding='utf-8', errors='replace').read()
            self.cache[rel] = (t.split('\n'), blank_comments(t).split('\n'), t)
        return self.cache[rel]

    def line(self, rel, ln, code=True):
        return self.lines(rel)[1 if code else 0][ln - 1]

    def text(self, rel):
        return self.lines(rel)[2]

    def find(self, rel, rx, flags=0):
        """(1-based line, match) of the first match of rx in rel's comment-blanked text"""
        code = '\n'.join(self.lines(rel)[1])
        m = re.search(rx, code, flags)
        if not m:
            raise LookupError(f'{rel}: no match for {rx}')
        return code.count('\n', 0, m.start()) + 1, m


def nums(line):
    return [(m.start(1), m.end(1), m.group(1), ival(m.group(1))) for m in NUMRX.finditer(line)]


def norm(s):
    return re.sub(r'\s+', ' ', s).strip()


# --------------------------------------------------------------------------------------------- measurements
class Facts:
    """Every value a rule compares with, read at run time from the unit's own text, the generated files and the
    images. Each entry: (value, 'what was read')."""

    def __init__(self, T, IB, IA, CB):
        self.T, self.IB, self.IA, self.CB = T, IB, IA, CB
        f = {}
        ln, m = T.find('Reusable/YG0d.v', r'Definition spZ \(regs : bvmap (\d+) word\) : Z := bv_unsigned \(getr regs (\d+)\)')
        f['regw'] = (int(m.group(1)), f'lib/Reusable/YG0d.v:{ln} spZ (regs : bvmap {m.group(1)} word): the register file is indexed by bv {m.group(1)}')
        f['sp'] = (int(m.group(2)), f'lib/Reusable/YG0d.v:{ln} spZ regs := bv_unsigned (getr regs {m.group(2)}): sp is register {m.group(2)}')
        ln, m = T.find('Reusable/YG0d.v', r'Definition argZ .*?\(Z_to_bv 5 \((\d+) \+ i\)\)')
        f['a0'] = (int(m.group(1)), f'lib/Reusable/YG0d.v:{ln} argZ regs i := getr regs ({m.group(1)} + i): a0 (argument 0, return value) is register {m.group(1)}')
        ln, m = T.find('Reusable/YG0d.v', r'Definition w64 \(z : Z\) : word := Z_to_bv (\d+) z')
        f['w64'] = (int(m.group(1)), f'lib/Reusable/YG0d.v:{ln} w64 z := Z_to_bv {m.group(1)} z: a machine word has {m.group(1)} bits')
        ln, m = T.find('Reusable/YI04.v', r'Definition sr_atoms : list sv := SLit 0 :: atom_regs 1 31')
        f['atoms'] = (None, f'lib/Reusable/YI04.v:{ln} sr_atoms := SLit 0 :: atom_regs 1 31 (atom i is register i)')
        # the contract the malloc chain restates (Qed): lib/B/Rt/RtDMallocI.v ipre_chain
        ln, m = T.find('B/Rt/RtDMallocI.v', r'Lemma ipre_chain :(.*?)\nProof\.', re.S)
        self.contract_ln = ln
        self.contract = norm(m.group(1))
        mm = re.search(r'let pT := bv_unsigned \(getr regs0 (\d+)\)', self.contract)
        f['pt'] = (int(mm.group(1)), f'lib/B/Rt/RtDMallocI.v:{ln} ipre_chain: let pT := bv_unsigned (getr regs0 {mm.group(1)}) (the trace pointer is a1 = register {mm.group(1)}); {f["atoms"][1]}')
        mm = re.search(r'\(1 <= length tr <= (\d+)\)%nat /\\ pT mod (\d+) = 0 /\\ pT \+ (\d+) \+ (\d+) \* (\d+) <= ly_stk_hi ly', self.contract)
        self.c_len, self.c_al, self.c_hdr, self.c_ent, self.c_max = map(int, mm.groups())
        f['tsize'] = (self.c_hdr + self.c_ent * self.c_max,
                      f'lib/B/Rt/RtDMallocI.v:{ln} ipre_chain: pT + {self.c_hdr} + {self.c_ent} * {self.c_max} <= ly_stk_hi ly (the trace object with its {self.c_max}-frame buffer spans {self.c_hdr + self.c_ent * self.c_max} bytes)')
        f['pal'] = (self.c_al.bit_length() - 1, f'lib/B/Rt/RtDMallocI.v:{ln} ipre_chain: pT mod {self.c_al} = 0 (alignment 2^{self.c_al.bit_length() - 1})')
        ln, m = T.find('B/Rt/RtDDefs.v', r'Definition astrace_at .*?:=\s*rdword \(aview segs \(w_H W\) mem\) p = Some \(p \+ (\d+)\) /\\\s*rd32 \(aview segs \(w_H W\) mem\) \(p \+ (\d+)\) \(Z.of_nat \(length tr\)\) /\\\s*rd32 \(aview segs \(w_H W\) mem\) \(p \+ (\d+)\) 0 /\\\s*\(forall i, \(i < length tr\)%nat -> rdword \(aview segs \(w_H W\) mem\) \(p \+ (\d+) \+ (\d+) \* Z.of_nat i\) = Some \(nth i tr (\d+)\)\)', re.S)
        self.astr = dict(ptr=int(m.group(1)), len=int(m.group(2)), tag=int(m.group(3)), buf=int(m.group(4)), ent=int(m.group(5)), dflt=int(m.group(6)))
        self.astr_where = f'lib/B/Rt/RtDDefs.v:{ln} astrace_at: [p] = p + {m.group(1)}, rd32 (p + {m.group(2)}) = length, rd32 (p + {m.group(3)}) = 0, frame i at p + {m.group(4)} + {m.group(5)} * i (nth i tr {m.group(6)})'
        ln, m = T.find('Reusable/YG0d.v', r'Definition rdword \(rd : reader\) \(a : Z\) : option Z :=\s*match rd a,((?: rd \(a\+\d\),?)+) with', re.S)
        f['rdw'] = (len(re.findall(r'rd \(a\+\d\)', m.group(1))) + 1, f'lib/Reusable/YG0d.v:{ln} rdword reads bytes a .. a+{len(re.findall(r"rd .a.[0-9].", m.group(1)))} (8 bytes)')
        f['rd32'] = (4, 'rd32 reads a 32-bit (4-byte) value (its name and lib/B/Rt/RtDDefs.v astrace_at, size and tag at p+8 and p+12)')
        f['byte'] = (256, 'a byte value v = bv_unsigned b of b : byte (bv 8) lies in [0, 2^8 = 256)')
        ln, m = T.find('Reusable/YG0f.v', r'Definition shadow_addr \(a : Z\) : Z := SHADOW_OFF \+ a / (\d+)')
        f['sscale'] = (int(m.group(1)), f'lib/Reusable/YG0f.v:{ln} shadow_addr a := SHADOW_OFF + a / {m.group(1)} (one shadow byte per {m.group(1)}-byte granule)')
        ln, m = T.find('Reusable/YG0n.v', r'Definition core_extents : list \(Z \* Z\) :=\s*\[(.*?)\]\.', re.S)
        ce = norm(m.group(1))
        self.core = {k: int(v) for k, v in re.findall(r'\(ly_(\w+) ly, (\d+)\)', ce)}
        self.core_where = f'lib/Reusable/YG0n.v:{ln} core_extents: ' + ', '.join(f'(ly_{k} ly, {v})' for k, v in self.core.items())
        ln2, m = T.find('Reusable/YG0n.v', r'in_zr a \(shadow_addr \(fst r\), \(snd r \+ (\d+)\) / (\d+)\)')
        f['owned_sh'] = ((int(m.group(1)), int(m.group(2))), f'lib/Reusable/YG0n.v:{ln2} owned_core: shadow of an owned range r is (shadow_addr (fst r), (snd r + {m.group(1)}) / {m.group(2)})')
        ln, m = T.find('Reusable/YG01.v', r'Definition DEPOT_CAP : Z := (\d+)\.')
        f['depot_cap'] = (int(m.group(1)), f'lib/Reusable/YG01.v:{ln} DEPOT_CAP := {m.group(1)} (shared by both builds; depot_cap_ok and depot_inv_cap are Qed)')
        ln, m = T.find('Reusable/YG01.v', r'Lemma depot_inv_frames : .*?<= (\d+) \* Z.of_nat \(length d\)', re.S)
        f['frames_per'] = (int(m.group(1)), f'lib/Reusable/YG01.v:{ln} depot_inv_frames: frames <= {m.group(1)} * length d')
        ln, m = T.find('Reusable/YG00.v', r'Definition kFreeArrayOffset : Z := (\d+)\.')
        f['kfao'] = (int(m.group(1)), f'lib/Reusable/YG00.v:{ln} kFreeArrayOffset := {m.group(1)}')
        ln, m = T.find('Reusable/YG00.v', r'Definition kRegionSizeLog : Z := (\d+)\.')
        f['kregion'] = (int(m.group(1)), f'lib/Reusable/YG00.v:{ln} kRegionSizeLog := {m.group(1)}')
        ln, m = T.find('Reusable/YG00.v', r'Definition kUnwindMax : nat := (\d+)%nat\.')
        f['kunwind'] = (int(m.group(1)), f'lib/Reusable/YG00.v:{ln} kUnwindMax := {m.group(1)}')
        ln, m = T.find('Reusable/YG0f.v', r'Definition SHADOW_OFF : Z := (0x[0-9a-f]+)\.')
        f['shoff'] = (ival(m.group(1)), f'lib/Reusable/YG0f.v:{ln} SHADOW_OFF := {m.group(1)}')
        ln, m = T.find('Reusable/YG0f.v', r'Definition kLowShadowBeg : Z := (0x[0-9a-f]+)\.')
        f['klsb'] = (ival(m.group(1)), f'lib/Reusable/YG0f.v:{ln} kLowShadowBeg := {m.group(1)}')
        ln, m = T.find('B/YF0x.v', r'Definition TFIB_IMG_END : Z := (0x[0-9a-f]+)\.')
        f['imgend'] = (ival(m.group(1)), f'lib/B/YF0x.v:{ln} TFIB_IMG_END := {m.group(1)}')
        ln, m = T.find('Reusable/YP08.v', r'Definition R_hdr \(two : bool\) : region :=\s*mkRegion \(Some (\d+)%nat\) 0 \(if two then (\d+) else (\d+)\)', re.S)
        f['rhdr'] = (int(m.group(2)), f'lib/Reusable/YP08.v:{ln} R_hdr true := mkRegion (Some {m.group(1)}%nat) 0 {m.group(2)} ..: the entry header region spans [usp, usp + {m.group(2)})')
        ln, m = T.find('Reusable/YP08.v', r'Definition E0 \(sp : word\).*?mkEnv \(fun n => match n with\s*\| (\d+) => sp', re.S)
        f['e0sp'] = (int(m.group(1)), f'lib/Reusable/YP08.v:{ln} E0 sp ..: atom {m.group(1)} => sp (ew E {m.group(1)} is the entry sp)')
        ln, m = T.find('Reusable/YCbq.v', r'Lemma not_inFP_token : forall a, a <> (\d+) ->')
        f['tok0'] = (int(m.group(1)), f'lib/Reusable/YCbq.v:{ln} not_inFP_token : forall a, a <> {m.group(1)} -> ~ inFP [sink_token] a')
        # CmdGlob (program globals of this harness)
        cg = 'B/Prog/CmdGlob.v'
        self.cg = {}
        for nm in ('A_G_REC', 'A_REC_SPILL', 'A_G_QUITTING'):
            ln, m = T.find(cg, r'Definition ' + nm + r' : Z := (0x[0-9a-f]+)\.')
            self.cg[nm] = (ival(m.group(1)), ln)
        ln, m = T.find(cg, r'Definition GI_cmdA \(j : nat\) \(rd : reader\) : Prop :=(.*?)\.\n', re.S)
        self.gi = []
        for base, off, n in re.findall(r'zero_atA rd \(?(A_\w+)(?: \+ (\d+))?\)? (\d+)', m.group(1)):
            self.gi.append((base, int(off or 0), int(n)))
        self.gi_where = f'lib/B/Prog/CmdGlob.v:{ln} GI_cmdA: ' + '; '.join(f'zero_atA ({b}{" + " + str(o) if o else ""}) {n}' for b, o, n in self.gi)
        ln, m = T.find(cg, r'Definition zero_atA \(rd : reader\) \(a n : Z\) : Prop := forall i, 0 <= i < n -> rd \(a \+ i\) = Some (\d+)\.')
        f['zero'] = (int(m.group(1)), f'lib/B/Prog/CmdGlob.v:{ln} zero_atA rd a n := forall i, .. rd (a + i) = Some {m.group(1)}')
        ln, m = T.find(cg, r'Definition cmd_PG : list \(Z \* Z\) :=\s*\[(.*?)\]\.', re.S)
        self.pg = [(b, int(n)) for b, n in re.findall(r'\((A_\w+), A_\w+ \+ (\d+)\)', m.group(1))]
        self.pg_where = f'lib/B/Prog/CmdGlob.v:{ln} cmd_PG := ' + norm(m.group(1))
        # start-up model (lib/B/YD1g.v) and its certificate (lib/B/YB01.v, generated from image B)
        g = 'B/YD1g.v'
        ln, m = T.find(g, r'Definition TFIB_HEAD4 : list amap := \[(.*?)\]\.', re.S)
        self.head4 = [x.strip() for x in m.group(1).split(';')]
        self.head4_ln = ln
        ln, m = T.find(g, r'Definition TFIB_TAIL12 : list amap :=\s*\[(.*?)\]\.', re.S)
        self.tail12 = [x.strip() for x in m.group(1).split(';')]
        self.tail12_ln = ln
        ln, m = T.find(g, r'Definition HEAD4 : list \(word \* word\) := \[(.*?)\]\.')
        self.HEAD4 = [x.strip() for x in m.group(1).split(';')]
        self.HEAD4_ln = ln
        ln, m = T.find(g, r'Definition TAIL12 : list \(word \* word\) := \[(.*?)\]\.')
        self.TAIL12 = [x.strip() for x in m.group(1).split(';')]
        self.TAIL12_ln = ln
        ln, m = T.find(g, r'Definition KNOWN : list \(word \* word\) := \[(.*?)\]\.')
        self.KNOWN = [x.strip() for x in m.group(1).split(';')]
        self.KNOWN_ln = ln
        ln, m = T.find(g, r'Definition epg \(v : nat\) : expr := EMd M_MUL \(ELit (\d+)\) \(EVar v\)\.')
        self.epg = (int(m.group(1)), ln)
        self.edefs = {}
        code = '\n'.join(T.lines(g)[1])
        for nm, v in re.findall(r'Definition (e\w+) : expr := epg (\d+)\.', code):
            self.edefs[nm] = int(v)
        ln, m = T.find(g, r'Lemma uTopRel : usp - (\d+) <= u eTop <= usp \+ (\d+)')
        self.utop = (int(m.group(1)), int(m.group(2)), ln)
        self.facts = f
        self.cert = Cert(T.text('B/YB01.v'))
        self.regions = parse_regions(T.text('B/YD2j.v'))
        self.yf0m = T.text('B/YF0m.v')

    def __getitem__(self, k):
        return self.facts[k]


class Cert:
    """lib/B/YB01.v, the start-up certificate the collector wrote from image B: per hand-off state its a_maps
    list, a_vis list, a_eager and a_abytes, and the KRange entries of its known facts."""

    def __init__(self, text):
        self.text = text
        self.states = []
        for m in re.finditer(r'a_maps := \[', text):
            i = m.end()
            depth, j = 1, i
            while depth:
                c = text[j]
                depth += c == '['
                depth -= c == ']'
                j += 1
            body = text[i:j - 1]
            ents = re.findall(r'\{\| am_base := (.*?); am_len := ELit (\d+); am_kind := (\w+) \|\}', body)
            tail = text[j:j + 200000]
            st = dict(maps=[(norm(b), int(n), k) for b, n, k in ents])
            for fld in ('a_eager', 'a_abytes'):
                mm = re.search(fld + r' := (\d+)', tail)
                st[fld] = int(mm.group(1)) if mm else None
            self.states.append(st)
        self.kranges = set((norm(e), int(lo), int(hi)) for e, lo, hi in
                           re.findall(r'KRange \((EVar \d+)\) (\d+) (\d+)', text))

    @staticmethod
    def epg_text(v, mul=4096):
        return f'EMd Instr.M_MUL (ELit {mul}) (EVar {v})'


def parse_regions(text):
    """generated region list (lib/B/YD2j.v): [(name, lo, hi)]"""
    return [(m.group(1), int(m.group(2)), int(m.group(3))) for m in
            re.finditer(r'Definition (R_\w+) : region :=\s*mkRegion None (\d+) (\d+) ', text)]


# ---------------------------------------------------------------------------------------------- verdicts
class V:
    """one settled row: reason id, measurement text, result, finding kind, new value, read_by, judge(v)"""

    def __init__(self, reason, meas, judge, result='OK', kind='-', new='-', read_by='-', control='value'):
        self.reason, self.meas, self.judge = reason, meas, judge
        self.result, self.kind, self.new, self.read_by = result, kind, new, read_by
        self.control = control  # 'value': judge compares the value; 'na:<why>': a value-independent rule


# ------------------------------------------------------------------------------------------------- rules
# A line rule: (id, file regex, line regex with named numeral groups, {group: callable(F, m, rel) -> (value, text)})
# The rule claims a numeral position when the line regex matches with that group exactly on it.
def mk_line_rules(F):
    f = F.facts
    R = []

    def const(key):
        return lambda F, m, rel: f[key]

    def lit(v, txt):
        return lambda F, m, rel: (v, txt)

    # ---- register file / registers (RISC-V integer ABI as the library names them)
    R.append(('REG-INDEX-WIDTH', r'.', r'(?:bvmap|[:(]\s*bv) (?P<a>' + NUM + r')\b(?! *%| *\)? *:)(?=\s*(?:word|,|\)|\]|$))',
              {'a': const('regw')}))
    sp_rx = [r'getr (?:regsI|regs0|regs\'|regs) (?P<a>' + NUM + r') = w64 \(sp0 - IFRAME\)',
             r'(?P<a>' + NUM + r')%bv \(SOff (?P<b>' + NUM + r') \(- IFRAME\)\)',
             r'sr_get \(ss_regs ss\) (?P<a>' + NUM + r')%bv = SOff (?P<b>' + NUM + r') \(- IFRAME\)',
             r'mkRegion \(Some (?P<a>' + NUM + r')%nat\) \(- (?:MALLOC_IN_STK|IFRAME)\)',
             r'r <> (?P<a>' + NUM + r')%bv']
    for rx in sp_rx:
        R.append(('REG-SP', r'.', rx, {'a': const('sp'), 'b': const('sp')}))
    R.append(('REG-A0', r'.', r'bv_unsigned k0 <> (?P<a>' + NUM + r')\b', {'a': const('a0')}))
    # atom 11 = the trace pointer pT (a1 at entry): R_bst region, the skeleton checks, the facts list
    R.append(('ATOM-PT', r'.', r'\((?P<a>' + NUM + r')%nat, mkAF kHighMemBeg kHighMemEnd (?P<al>' + NUM + r')\)',
              {'a': const('pt'), 'al': const('pal')}))
    R.append(('ATOM-PT', r'.', r'Nat\.eqb k (?P<a>' + NUM + r') && \((?P<z>' + NUM + r') <=\? (?:lo|YP09\.r_lo r)\) && \((?:hi|YP09\.r_hi r) <=\? (?P<sz>' + NUM + r')\)',
              {'a': const('pt'), 'z': lit(0, 'the trace object region starts at pT + 0 (lib/B/YFhy.v R_bst lo 0)'), 'sz': const('tsize')}))
    R.append(('ATOM-PT', r'.', r'b = Some (?P<a>' + NUM + r')%nat /\\ (?P<z>' + NUM + r') <= lo /\\ hi <= (?P<sz>' + NUM + r')\)',
              {'a': const('pt'), 'z': lit(0, 'the trace object region starts at pT + 0 (lib/B/YFhy.v R_bst lo 0)'), 'sz': const('tsize')}))
    A = F.astr
    R.append(('TRACE-LAYOUT', r'.', r'mkRegion \(Some (?P<a>' + NUM + r')%nat\) (?P<lo>' + NUM + r') (?P<hi>' + NUM + r') (?P<wl>' + NUM + r') (?P<wh>' + NUM + r') \[YP09\.mkChunk (?P<c0>' + NUM + r') \(CVal (?P<w0>' + NUM + r') \(SOff (?P<r>' + NUM + r') (?P<o>' + NUM + r')\)\); YP09\.mkChunk (?P<c1>' + NUM + r') \(CVal (?P<w1>' + NUM + r') \(SOff aLEN (?P<z>' + NUM + r')\)\)\]',
              {'a': const('pt'), 'r': const('pt'),
               'lo': lit(0, F.astr_where + ': the header starts at p'), 'hi': lit(A['buf'], F.astr_where + ': the header ends at the buffer p + %d' % A['buf']),
               'wl': lit(0, 'no write window (the chain only reads the caller\'s trace object)'), 'wh': lit(0, 'no write window (the chain only reads the caller\'s trace object)'),
               'c0': lit(0, F.astr_where + ': word at p'), 'w0': const('rdw'), 'o': lit(A['ptr'], F.astr_where),
               'c1': lit(A['len'], F.astr_where + ': size u32 at p + %d and tag u32 at p + %d read as one word' % (A['len'], A['tag'])),
               'w1': const('rdw'), 'z': lit(0, 'SOff aLEN 0: the word is atom aLEN itself')}))
    R.append(('TRACE-LAYOUT', r'.', r'pT (?P<w>' + NUM + r') \(pT \+ (?P<o>' + NUM + r')\)',
              {'w': const('rdw'), 'o': lit(A['ptr'], F.astr_where)}))
    R.append(('TRACE-LAYOUT', r'.', r'\(pT \+ (?P<o>' + NUM + r')\) (?P<w>' + NUM + r') \(Z\.of_nat \(length tr\)\)',
              {'w': const('rdw'), 'o': lit(A['len'], F.astr_where)}))
    R.append(('TRACE-LAYOUT', r'.', r'pT \+ (?P<b>' + NUM + r') \+ (?P<e>' + NUM + r') \* Z\.of_nat i\)? ?(?:(?P<w>' + NUM + r') \(nth i tr (?P<z>' + NUM + r')\))?',
              {'b': lit(A['buf'], F.astr_where), 'e': lit(A['ent'], F.astr_where), 'w': const('rdw'), 'z': lit(A['dflt'], F.astr_where)}))
    R.append(('TRACE-LAYOUT', r'.', r'\(k < (?P<w>' + NUM + r')\)%nat', {'w': const('rdw')}))
    R.append(('TRACE-LAYOUT', r'.', r'pT \+ (?P<sz>' + NUM + r') <= (?:T|ly_prim ly|ly_C ly|ly_stk_hi ly)\b', {'sz': const('tsize')}))
    R.append(('OWNED-CORE', r'.', r'ly_C ly \+ (?P<c>' + NUM + r') <=', {'c': lambda F, m, rel: (F.core['C'], F.core_where)}))
    # fcsr rounding mode
    R.append(('FCSR-FRM', r'.', r'Z\.land \(Z\.shiftr \(bv_unsigned \(@fp_csr \w+\'?\)\) (?P<a>' + NUM + r')\) (?P<b>' + NUM + r') = (?P<c>' + NUM + r')',
              {'a': lit(5, 'RISC-V fcsr: frm is bits 7..5 (shift 5); the line\'s own comment (lib/B/YCfn.v:49) says frm = fcsr bits 5..7'),
               'b': lit(7, 'RISC-V fcsr: frm is a 3-bit field (mask 7)'),
               'c': lit(0, 'frm 0 = round to nearest, ties to even (the start-up fcsr is 0)')}))
    # machine widths
    R.append(('WIDTH', r'.', r'rdword \(aview tfibsegs H mem\) a = Some v -> val_mem tfibsegs \(mrestrict H mem\) a (?P<w>' + NUM + r') v', {'w': const('rdw')}))
    R.append(('WIDTH', r'.', r'rd32 \(aview tfibsegs H mem\) a v -> val_mem tfibsegs \(mrestrict H mem\) a (?P<w>' + NUM + r') v', {'w': const('rd32')}))
    R.append(('WIDTH', r'.', r'v = bv_unsigned b /\\ (?P<z>' + NUM + r') <= v < (?P<w>' + NUM + r')', {'z': lit(0, 'bv_unsigned is >= 0'), 'w': const('byte')}))
    R.append(('WIDTH', r'.', r'(?:\ba|\+ \d+|Z\.of_nat k) <=? (?P<two>' + NUM + r') \^ (?P<w>' + NUM + r')\b(?!\s*-\s*\d)',
              {'two': lit(2, 'the word range is 2 ^ (word bits): base 2'), 'w': const('w64')}))
    R.append(('WIDTH', r'.', r'(?<![\w+*-] )(?P<z>' + NUM + r') <= pT \+', {'z': lit(0, 'an address (bv_unsigned of a word) is >= 0')}))
    R.append(('WIDTH', r'.', r'Z_to_bv (?P<w>' + NUM + r') ', {'w': const('w64')}))
    R.append(('ENTRY-STACK-LAYOUT', r'.', r'bv_unsigned \(ew E (?P<z>' + NUM + r')\) (?:=|<=) usp', {'z': const('e0sp')}))
    R.append(('ENTRY-STACK-LAYOUT', r'.', r'usp \+ (?P<h>' + NUM + r') <=', {'h': const('rhdr')}))
    R.append(('ENTRY-STACK-LAYOUT', r'.', r'usp <= a < usp \+ (?P<h>' + NUM + r') ->', {'h': const('rhdr')}))
    # shadow / owned-core text of lib/Reusable/YG0n.v
    R.append(('OWNED-CORE', r'YD2l\.v', r'\(snd r \+ (?P<s>' + NUM + r')\) / (?P<g>' + NUM + r')\)',
              {'s': lambda F, m, rel: (F['owned_sh'][0][0], F['owned_sh'][1]), 'g': lambda F, m, rel: (F['owned_sh'][0][1], F['owned_sh'][1])}))
    R.append(('OWNED-CORE', r'YD2l\.v', r'\| AC o => \((?P<z>' + NUM + r') <=\? o\) && \(o \+ w <=\? (?P<c>' + NUM + r')\)',
              {'z': lit(0, 'offsets inside an extent are >= 0'), 'c': lambda F, m, rel: (F.core['C'], F.core_where)}))
    R.append(('OWNED-CORE', r'YD2l\.v', r'\| AD o => \((?P<z>' + NUM + r') <=\? o\) && \(o \+ w <=\? (?P<c>' + NUM + r')\)',
              {'z': lit(0, 'offsets inside an extent are >= 0'), 'c': lambda F, m, rel: (F.core['D'], F.core_where)}))
    R.append(('OWNED-CORE', r'YD2l\.v', r'\| (?:YG0f\.AT|AQ|ANB|ASB) o => \((?P<z>' + NUM + r') <=\? o\)',
              {'z': lit(0, 'offsets inside an extent are >= 0 (the size is the named constant of lib/Reusable/YG0n.v core_extents)')}))
    R.append(('OWNED-CORE', r'YD2l\.v', r'let w := Z\.max (?P<one>' + NUM + r') \(Z\.of_nat \(c_w c\)\)',
              {'one': lit(1, 'a cell covers at least one byte (c_w is the cell width in bytes; a 0-width cell is checked as 1 byte)')}))
    # gi / footprint
    R.append(('ZERO-BYTES', r'YD1r\.v', r'rd a = Some (?P<z>' + NUM + r')\b', {'z': const('zero')}))
    R.append(('FP-TOKEN', r'YD1r\.v', r'a <> (?P<z>' + NUM + r') ->', {'z': const('tok0')}))
    return R


# --------------------------------------------------------------------------------------------- the engine
class Ctx:
    def __init__(self, args):
        self.T = Tree(args.lib, 'B')
        self.C = Tree(args.cgif_lib)
        self.IB = Img('B', *args.img_b)
        self.IA = Img('A', *args.img_a)
        self.CB = Img('cgif B', *args.img_cgif_b)
        self.F = Facts(self.T, self.IB, self.IA, self.CB)
        self.line_rules = mk_line_rules(self.F)
        self.rab = collections.defaultdict(list)
        for r in read_rows(args.rab_full):
            if r[5] and r[6]:
                self.rab[(r[5], r[6])].append(r)

    def rabmatch(self, r):
        c = [x for x in self.rab.get((r[5], r[6]), []) if x[7] == r[7] and x[11] == r[11]]
        return c or [x for x in self.rab.get((r[5], r[6]), []) if x[11] == r[11]]


def read_rows(path):
    rows = [l.rstrip('\n').split('\t') for l in open(path) if not l.startswith('#')]
    return rows[1:]


def proof_lines(T, rel):
    """1-based lines inside Proof .. Qed of rel (comment-blanked), and whether rel has Admitted/admit/Abort"""
    code = T.lines(rel)[1]
    inside, state = set(), False
    for i, line in enumerate(code, 1):
        ev = re.findall(r'\b(Proof|Qed|Defined|Admitted)\s*\.', line)
        if state or ev:
            inside.add(i)
        for e in ev:
            state = e == 'Proof'
    has = any(re.search(r'\b(Admitted|admit|Abort)\b', l) for l in code)
    return inside, has


# ------------------------------------------------------------------------------------- line-claim helpers
def claims_on_line(ctx, rel, ln):
    """{numeral start: (rule id, group, expected, text)} of every line rule on rel:ln (first rule wins)"""
    line = ctx.T.line(rel, ln)
    out = {}
    starts = {s for s, e, t, v in nums(line)}
    for rid, frx, lrx, groups in ctx.line_rules:
        if not re.search(frx, rel):
            continue
        for m in re.finditer(lrx, line):
            for g, fn in groups.items():
                if g not in m.groupdict() or m.group(g) is None:
                    continue
                s = m.start(g)
                if s in starts and s not in out:
                    exp, txt = fn(ctx.F, m, rel)
                    out[s] = (rid, g, exp, txt)
    return out


def contract_snippets(F):
    """conjuncts of the Qed contract lib/B/Rt/RtDMallocI.v ipre_chain that the chain's sections restate"""
    c = F.contract
    sn = []
    m = re.search(r'\((\(1 <= length tr <= \d+\)%nat /\\ .*? astrace_at tfibsegs W mem pT tr)\)', c)
    sn.append(m.group(1))
    m = re.search(r'\((forall r : bv \d+, r <> \d+%bv -> getr regsI r = getr regs0 r)\)', c)
    sn.append(m.group(1))
    m = re.search(r'(getr regsI \d+ = w64 \(sp0 - IFRAME\))', c)
    sn.append(m.group(1))
    m = re.search(r'let (pT) := (bv_unsigned \(getr regs0 \d+\))', c)
    sn.append(m.group(1) + ' := ' + m.group(2))
    return sn


def snippet_rx(s):
    """regex of a contract snippet: numerals are groups, tr/mem/W may be renamed (ch, mem0/memR, W')"""
    out, gi, vals = [], 0, []
    for tok in re.findall(r"0x[0-9a-fA-F]+|\d+|:=|[A-Za-z_][\w']*|\s+|.", s):
        if re.fullmatch(r'0x[0-9a-fA-F]+|\d+', tok):
            out.append(f'(?P<g{gi}>' + NUM + ')')
            vals.append(ival(tok))
            gi += 1
        elif tok == 'tr':
            out.append(r'(?:tr|ch)')
        elif tok == 'mem':
            out.append(r'(?:mem0|memR|mem)')
        elif tok == 'W':
            out.append(r"(?:W'|W)")
        elif tok == ':=':
            out.append(r'(?:\s*:\s*Z)?\s*:=')
        elif tok.isspace():
            out.append(r'\s*')
        else:
            out.append(re.escape(tok))
    return ''.join(out), vals


def rule_contract(ctx, r, used):
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    line = ctx.T.line(rel, ln)
    for sn in ctx.snippets:
        rx, vals = snippet_rx(sn)
        for m in re.finditer(rx, line):
            for gi, ev in enumerate(vals):
                g = f'g{gi}'
                s = m.start(g)
                if ival(m.group(g)) == v and (rel, ln, s) not in used:
                    used.add((rel, ln, s))
                    meas = (f'{rel}:{ln} col {s + 1} restates, token for token, the conjunct `{sn}` of the Qed contract '
                            f'lib/B/Rt/RtDMallocI.v:{ctx.F.contract_ln} ipre_chain (tr, mem, W may be renamed); the numeral is the '
                            f'contract\'s {ev} at the same place')
                    return V('CONTRACT-RESTATED', meas, eq_judge(ev))
    return None


def rule_line_claim(ctx, r, used):
    """settle r by a line rule claiming one numeral position of r's value not yet used by another row"""
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    key = (rel, ln)
    if key not in ctx.claim_cache:
        ctx.claim_cache[key] = claims_on_line(ctx, rel, ln)
    cl = ctx.claim_cache[key]
    line = ctx.T.line(rel, ln)
    for s, e, t, val in nums(line):
        if val != v or s not in cl or (rel, ln, s) in used:
            continue
        rid, g, exp, txt = cl[s]
        used.add((rel, ln, s))
        meas = f'{rel}:{ln} col {s + 1} `{line[max(0, s - 40):e + 10].strip()}`: {txt}'
        return V(rid, meas, eq_judge(exp))
    return None


# ------------------------------------------------------------------------------------------ row rules
def grp(line, rx, v):
    """the match of rx on line whose group 'n' holds the value v, or None"""
    for m in re.finditer(rx, line):
        if 'n' in m.groupdict() and m.group('n') is not None and ival(m.group('n')) == v:
            return m
    return None


def rule_cert(ctx, r):
    """start-up model values of lib/B/YD1g.v and YD1d.v that lib/B/CmdStartInstB.v's instances check by kernel
    computation over lib/B/YB01.v; re-measured here from YB01's own text"""
    F, rel, ln, v = ctx.F, r[5], int(r[6]), ival(r[11])
    line = ctx.T.line(rel, ln)
    C = F.cert
    nst = len(C.states)
    if rel == 'YD1g.v' and 'TFIB_HEAD4' in line:
        ents = re.findall(r'mk (e\w+) ' + NUM + r' (\w+)', line)
        for i, (nm, n, k) in enumerate(ents):
            if ival(n) == v:
                lens = {st['maps'][i][1] for st in C.states}
                bases = {st['maps'][i][0] for st in C.states}
                exp = lens.pop() if len(lens) == 1 else None
                meas = (f'{rel}:{ln} TFIB_HEAD4 entry {i} `mk {nm} {n} {k}`: a_maps entry {i} of all {nst} hand-off states of '
                        f'lib/B/YB01.v (the start-up certificate collected from image B) has am_len ELit {exp} and base '
                        f'{"/".join(sorted(bases))}; the instance cmd_holes_chk (lib/B/CmdStartInstB.v:25) checks hole_chk, '
                        f'which compares a_maps with TFIB_HEAD4 ++ musl_maps ++ TFIB_TAIL12, by kernel computation')
                return V('STARTUP-CERT', meas, eq_judge(exp))
    m = re.search(r'Definition (e\w+) : expr := epg (\d+)\.', line)
    if rel == 'YD1g.v' and m and int(m.group(2)) == v:
        nm = m.group(1)
        idx = [i for i, x in enumerate(F.head4) if x.startswith('mk ' + nm + ' ')]
        if idx:
            i = idx[0]
            bases = {st['maps'][i][0] for st in C.states}
            mm = re.fullmatch(r'EMd Instr\.M_MUL \(ELit 4096\) \(EVar (\d+)\)', bases.pop()) if len(bases) == 1 else None
            exp = int(mm.group(1)) if mm else None
            meas = (f'{rel}:{ln} {nm} = epg {v} is the base of TFIB_HEAD4 entry {i}; a_maps entry {i} of all {nst} states of '
                    f'lib/B/YB01.v has am_base 4096 * EVar {exp} (kernel-checked by cmd_holes_chk, lib/B/CmdStartInstB.v:25)')
            return V('STARTUP-CERT', meas, eq_judge(exp))
    m = re.search(r'Definition dDM := dm eDM (\d+) KRW', line) or re.search(r'wzp dDM = \(u eDM, (\d+)\)', line)
    if rel == 'YD1g.v' and m and int(m.group(1)) == v:
        lens = {st['maps'][0][1] for st in C.states}
        exp = lens.pop() if len(lens) == 1 else None
        meas = (f'{rel}:{ln} the length of dDM, the denotation of TFIB_HEAD4 entry 0 (mk eDM {exp} KRW): a_maps entry 0 of '
                f'all {nst} states of lib/B/YB01.v has am_len ELit {exp}; dDM_val is Qed')
        return V('STARTUP-CERT', meas, eq_judge(exp))
    if rel == 'YD1g.v' and 'KRange' in line:
        for m in re.finditer(r'KRange \((EVar (\d+))\) (\d+) (\d+)', line):
            var, lo, hi = int(m.group(2)), int(m.group(3)), int(m.group(4))
            for gname, gv in (('var', var), ('lo', lo), ('hi', hi)):
                if gv == v:
                    def j(x, gname=gname, var=var, lo=lo, hi=hi):
                        t = dict(var=var, lo=lo, hi=hi)
                        t[gname] = x
                        return (f'EVar {t["var"]}', t['lo'], t['hi']) in C.kranges
                    meas = (f'{rel}:{ln} TFIB_RANGES entry `KRange (EVar {var}) {lo} {hi}`: lib/B/YB01.v (written from '
                            f'image B) states KRange (EVar {var}) {lo} {hi} among its known facts '
                            f'({"present" if j(v) else "ABSENT"}); hole_chk requires kn_mem of every TFIB_RANGES entry '
                            f'(cmd_holes_chk, lib/B/CmdStartInstB.v:25, kernel computation)')
                    return V('STARTUP-CERT', meas, j)
    if rel == 'YD1g.v' and 'a_eager ch <=' in line:
        m = re.search(r'a_eager ch <= (\d+)', line)
        if m and int(m.group(1)) == v:
            mx = max(st['a_eager'] for st in C.states)
            meas = (f'{rel}:{ln} hole_facts bound on a_eager: the largest a_eager over the {nst} hand-off states of '
                    f'lib/B/YB01.v is {mx} ({mx:#x}); hole_facts is Qed (from hole_chk)')
            return V('STARTUP-CERT', meas, eq_judge(mx))
    if rel == 'YD1d.v' and 'epg' in line:
        maps = {}
        for nm, n in re.findall(r'mk (e\w+) (\d+) \w+', ' ; '.join(F.head4 + F.tail12)):
            if nm in F.edefs:
                maps.setdefault(F.edefs[nm], set()).add(int(n))
        for m in re.finditer(r'\(epg (\d+), ELit (\d+)\)', line):
            var, n = int(m.group(1)), int(m.group(2))
            for gname, gv in (('var', var), ('len', n)):
                if gv != v:
                    continue

                def j(x, gname=gname, var=var, n=n):
                    a, b = (x, n) if gname == 'var' else (var, x)
                    return b in maps.get(a, set())
                cnt = C.text.count(f'({Cert.epg_text(var)}, ELit {n})')
                meas = (f'{rel}:{ln} AVIS14 entry (epg {var}, ELit {n}): page variable {var} is the base of the start-up map '
                        f'of length {sorted(maps.get(var, []))} in lib/B/YD1g.v TFIB_HEAD4/TFIB_TAIL12 (both checked against '
                        f'lib/B/YB01.v by cmd_holes_chk); the pair occurs {cnt} times in YB01\'s a_vis lists; avis_chk is '
                        f'checked by cmd_holes_chkB (lib/B/CmdStartInstB.v:37, kernel computation)')
                return V('STARTUP-CERT', meas, j)
    return None


def rule_img_shadow(ctx, r):
    """kn_vis TFIB ch (ELit 0) SH LEN: the shadow of the whole image B"""
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    line = ctx.T.line(rel, ln)
    m = re.search(r'kn_vis TFIB ch \(ELit (?P<z>' + NUM + r')\) (?P<s>' + NUM + r') (?P<n>' + NUM + r')', line)
    if not m:
        m = re.search(r'\(ELit (?P<z>' + NUM + r')\) (?P<s>0x7fff[0-9a-f]+) (?P<n>' + NUM + r') IMGSH', line)
    if not m:
        return None
    IB, F = ctx.IB, ctx.F
    sh = F['shoff'][0] + IB.lo // 8
    ln_ = (IB.top - IB.lo) // 8
    exp = {'z': 0, 's': sh, 'n': ln_}
    for g in ('n', 's', 'z'):
        if ival(m.group(g)) == v:
            meas = (f'{rel}:{ln} `{m.group(0)}`: image B {IB.sha} program headers give the image [{IB.lo:#x}, {IB.top:#x}) '
                    f'(lowest PT_LOAD vaddr, highest PT_LOAD end rounded up to 4096); its shadow starts at SHADOW_OFF + '
                    f'{IB.lo:#x} / 8 = {sh:#x} and spans ({IB.top:#x} - {IB.lo:#x}) / 8 = {ln_:#x}; ELit 0: the zone is absolute; '
                    f'the class field is checked by cmd_holes_imgsh (lib/B/CmdStartInstB.v:39, kernel computation)')
            return V('IMAGE-SHADOW-GEOMETRY', meas, eq_judge(exp[g]))
    return None


def rule_zero_shadow(ctx, r):
    """zero_shadow .. SHADOW_OFF LO (HI - LO): measured from image B's asan_globals descriptors"""
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    line = ctx.T.line(rel, ln)
    m = re.search(r'zero_shadow \(aview tfibsegs \(w_H W\) mem\) SHADOW_OFF (?P<lo>' + NUM + r') \((?P<hi>' + NUM + r') - (?P<lo2>' + NUM + r')\)', line)
    if not m:
        return None
    IB = ctx.IB
    lo, hi = ival(m.group('lo')), ival(m.group('hi'))
    pe = IB.poison_end_below(IB.top)
    stop = IB.byname.get('__stop_asan_globals', [(None,)])[0][0]
    if lo == IB.lo:
        elo, why_lo = IB.lo, f'the image base {IB.lo:#x} (lowest PT_LOAD)'
    elif lo >= pe:
        elo, why_lo = pe, (f'the end of the last poisoned granule run of image B (largest beg + size_with_redzone over its '
                           f'{len(IB.globals)} asan_globals descriptors) {pe:#x}')
    else:
        elo, why_lo = stop, f'__stop_asan_globals {stop:#x} (end of the descriptor table; no global lies between it and the first program global)'
    first = IB.first_poison(elo, IB.top)
    if hi == IB.top:
        ehi, why_hi = IB.top, f'the image top {IB.top:#x}'
    else:
        ehi, why_hi = first, f'the first poisoned granule at or above {elo:#x}: {first:#x} ({IB.name(first)})'
    for g, exp, why in (('hi', ehi, why_hi), ('lo', elo, why_lo), ('lo2', elo, why_lo)):
        if ival(m.group(g)) == v:
            def j(x, g=g, exp=exp):
                lo_, hi_ = (x, ehi) if g in ('lo', 'lo2') else (elo, x)
                return x == exp and IB.first_poison(lo_, hi_) is None
            meas = (f'{rel}:{ln} zero_shadow range [{lo:#x}, {hi:#x}): {why}; no granule of [{elo:#x}, {ehi:#x}) is poisoned '
                    f'at start-up (image B {IB.sha} asan_globals: {len(IB.globals)} descriptors read from its bytes)')
            return V('ZERO-SHADOW-MEASURED', meas, j)
    return None


def rule_hull_margin(ctx, r):
    """rodata_hull_zero / rodata_shadow_facts / bss_shadow_facts: a bound at the A twin's distance from the
    zero-shadow edge, the edge measured in each image from its own descriptors"""
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    if rel not in ('YD1k.v', 'YD1o.v'):
        return None
    line = ctx.T.line(rel, ln)
    IB, IA = ctx.IB, ctx.IA
    kind = None
    if grp(line, r'p \+ n <= (?P<n>' + NUM + r') -> 0 < n', v) and rel == 'YD1k.v':
        kind = 'hi'
    if grp(line, r'(?P<n>' + NUM + r') <= p -> p \+ n <= 0x[0-9a-f]+ -> 0 < n', v) and rel == 'YD1o.v':
        kind = 'lo'
    if kind is None and rel == 'YD1k.v' and grp(line, r'\((?P<n>0x[0-9a-f]+) - 1\) / 8', v):
        kind = 'hi'
    if kind is None:
        return None
    rab = [x for x in ctx.rabmatch(r) if x[11] == r[11]]
    av = ival(rab[0][10]) if rab else None
    if av is None:
        return None
    if kind == 'hi':
        eb, ea = IB.first_poison(IB.lo, IB.top), IA.first_poison(IA.lo, IA.top)
        margin = ea - av
        exp = eb - margin
        meas = (f'{rel}:{ln} upper bound {v:#x} of the read-only strings with zero shadow: the first poisoned granule of image B '
                f'{IB.sha} is {eb:#x} ({IB.name(eb)}), of image A {IA.sha} {ea:#x}; the A twin ({rab[0][3]}:{rab[0][4]}) writes '
                f'{av:#x} = {ea:#x} - {margin:#x}, and B keeps the same margin: {eb:#x} - {margin:#x} = {exp:#x}; the lemmas are Qed '
                f'from rodata_zero_shadow (the same file, range [0x10000, {eb:#x}))')
    else:
        eb, ea = IB.poison_end_below(IB.top), IA.poison_end_below(IA.top)
        margin = av - ea
        exp = eb + margin
        meas = (f'{rel}:{ln} lower bound {v:#x} of the .bss tail with zero shadow: the last poisoned granule run of image B ends at '
                f'{eb:#x} ({IB.name(eb)}), of image A at {ea:#x}; the A twin writes {av:#x} = {ea:#x} + {margin:#x}, and B keeps the '
                f'same margin: {eb:#x} + {margin:#x} = {exp:#x}; the lemma is Qed from bss_zero_shadow')
    return V('ZERO-SHADOW-MARGIN', meas, eq_judge(exp))


def rule_img_region(ctx, r):
    """intervals that are exactly regions of the generated image region list (lib/B/YD2j.v IMG_REGIONS, from image B)"""
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    line = ctx.T.line(rel, ln)
    regs = {(lo, hi): nm for nm, lo, hi in ctx.F.regions}
    pairs = []  # (lo match, hi match) of every interval the line states
    for m in re.finditer(r'img_rd m (?P<a>' + NUM + r') (?P<b>' + NUM + r')', line):
        pairs.append(((m.start('a'), m.group('a')), (m.start('b'), m.group('b'))))
    m = re.search(r'(?P<a>' + NUM + r') <= p -> p \+ len <= (?P<b>' + NUM + r') -> \(p \+ len <= (?P<c>' + NUM + r') \\/ (?P<d>' + NUM + r') <= p\)', line)
    if m:
        pairs.append(((m.start('a'), m.group('a')), (m.start('c'), m.group('c'))))
        pairs.append(((m.start('d'), m.group('d')), (m.start('b'), m.group('b'))))
    for (ls, lt), (hs, ht) in pairs:
        lo, hi = ival(lt), ival(ht)
        for pos, val in (('hi', hi), ('lo', lo)):
            if val != v or (lo, hi) not in regs:
                continue

            def j(x, pos=pos, lo=lo, hi=hi):
                return ((x, hi) if pos == 'lo' else (lo, x)) in regs
            meas = (f'{rel}:{ln} [{lo:#x}, {hi:#x}) is exactly {regs[(lo, hi)]} of the generated region list lib/B/YD2j.v '
                    f'IMG_REGIONS (written from image B {ctx.IB.sha}); {v:#x} is its {pos} bound; img_facts is Qed from mem_ok over '
                    f'IMG_REGIONS; image B at {v:#x}: {ctx.IB.name(v)}')
            return V('GENERATED-REGION-BOUND', meas, j)
    return None


def rule_got(ctx, r):
    """CmdB's GOT and flag cells, and CmdB_lib_consts_chk's GOT words"""
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    if rel != 'YD2l.v':
        return None
    line = ctx.T.line(rel, ln)
    IB = ctx.IB
    got = IB.secs['.got']

    def got_of(target):
        return [a for a in range(got[0], got[1], 8) if IB.word(a, 8) == target]
    sym = {'as_shadow_cell': '__asan_shadow_memory_dynamic_address', 'as_uar_cell': '__asan_option_detect_stack_use_after_return'}
    m = re.search(r'(as_shadow_cell|as_uar_cell|as_got_shadow|as_got_uar) := (0x[0-9a-f]+);', line)
    if m and ival(m.group(2)) == v:
        f = m.group(1)
        s = sym.get(f) or sym['as_shadow_cell' if f == 'as_got_shadow' else 'as_uar_cell']
        sa = IB.byname[s][0][0]
        if f in sym:
            meas = f'{rel}:{ln} {f}: image B {IB.sha} symbol table: {s} at {sa:#x} ({IB.byname[s][0][1]} bytes, {IB.sec(sa)})'
            return V('GOT-CELL', meas, eq_judge(sa))
        g = got_of(sa)
        meas = (f'{rel}:{ln} {f}: the .got [{got[0]:#x}, {got[1]:#x}) word(s) of image B whose bytes hold {sa:#x} ({s}): '
                f'{", ".join(hex(x) for x in g)}')
        return V('GOT-CELL', meas, lambda x: x in g)
    m = re.search(r'\(fst r \+ snd r <=\? (0x[0-9a-f]+)\) \|\| \((0x[0-9a-f]+) <=\? fst r\)', line)
    if m and v in (ival(m.group(1)), ival(m.group(2))):
        F = ctx.F
        tgt = F.cg['A_G_REC'][0]
        g = got_of(tgt)
        lo = g[0] if len(g) == 1 else None
        words = [(lo + 8 * i, IB.word(lo + 8 * i, 8)) for i in range(4)] if lo else []
        hi = lo + 8 * 4 if lo else None
        meas = (f'{rel}:{ln} the program\'s GOT words: image B .got word {lo:#x} holds g_rec {tgt:#x} (lib/B/Prog/CmdGlob.v A_G_REC); '
                f'the four words {", ".join(f"{a:#x}->{w:#x} {IB.name(w).split(" ")[0]}" for a, w in words)} end at {hi:#x}')
        exp = lo if ival(m.group(1)) == v else hi
        return V('GOT-CELL', meas, eq_judge(exp))
    m = re.search(r'as_junk := fun _ => \[\(ANum (?P<a>0x[0-9a-f]+), (?P<n>\d+)\)\]', line)
    if m:
        rab = ctx.rabmatch(r)
        IA = ctx.IA
        a_b = ival(m.group('a'))
        nm, off, sz = IB.at(a_b)[0]
        a_sz = IA.byname[nm][0][1]
        aa = IA.byname[nm][0][0]
        if a_b == v:
            exp = IB.byname[nm][0][0] + off
            meas = (f'{rel}:{ln} as_junk cell: {v:#x} = {nm}+{off:#x} in image B ({sz} bytes); the A twin\'s value is {nm}+{off:#x} '
                    f'in image A ({a_sz} bytes, at {aa:#x}); the object has the same size in both images, so the offset is the same field')
            return V('SAME-SYMBOL-OFFSET', meas, eq_judge(exp))
        if ival(m.group('n')) == v:
            av = [ival(x[10]) for x in rab if x[11] == r[11]]
            av = av[0] if av else None
            meas = (f'{rel}:{ln} as_junk length {v}: the A twin\'s length is {av}; the cell lies in {nm} (image A {a_sz} bytes, image B {sz} '
                    f'bytes: the same layout), so the same field length holds')
            return V('SAME-LAYOUT-LENGTH', meas, lambda x: x == av and a_sz == sz)
    return None


def rule_dtor(ctx, r):
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    if rel != 'YE37.v':
        return None
    line = ctx.T.line(rel, ln)
    m = re.search(r'cell_lookup \(Tfib_const ly\) \(ANum (?P<a>0x[0-9a-f]+)\) = Some \(ACell \(ANum (?P<a2>0x[0-9a-f]+)\) (?P<w>\d+) \(AV \(ANum (?P<z>\d+)\)\)\)', line)
    if not m:
        return None
    IB, IA = ctx.IB, ctx.IA
    a = ival(m.group('a'))
    cell = re.search(r'z(\d) \(ANum ' + m.group('a') + r'\) (0x[0-9a-f]+|\d+)', ctx.F.yf0m)
    rab = [x for x in ctx.rabmatch(r) if x[11] == r[11]]
    if v == a:
        aa = ival(rab[0][10]) if rab else None
        anm = IA.at(aa)[0] if aa and IA.at(aa) else None
        exp = IB.byname[anm[0]][0][0] + anm[1] if anm else None
        meas = (f'{rel}:{ln} the DtorExit class (an open binder of the B top) names the cell {a:#x}: image B symbol table {IB.name(a)}; '
                f'the A twin\'s {aa:#x} is {IA.name(aa)}; generated lib/B/YF0m.v Tfib_const has `z{cell.group(1)} (ANum {m.group("a")}) {cell.group(2)}`')
        return V('SAME-SYMBOL-OFFSET', meas, eq_judge(exp))
    if ival(m.group('w')) == v and cell:
        meas = f'{rel}:{ln} cell width {v}: generated lib/B/YF0m.v Tfib_const writes the cell at {a:#x} as z{cell.group(1)} ({cell.group(1)} bytes)'
        return V('GENERATED-CELL', meas, eq_judge(int(cell.group(1))))
    if ival(m.group('z')) == v and cell:
        bw = IB.word(a, 8)
        meas = (f'{rel}:{ln} cell value {v}: generated lib/B/YF0m.v Tfib_const has value {cell.group(2)} at {a:#x}; image B bytes '
                f'there ({IB.sec(a)}, zero at load) read {bw}')
        return V('GENERATED-CELL', meas, lambda x: x == ival(cell.group(2)) == bw)
    return None


def rule_call_ret(ctx, r):
    """asan_malloc's return instructions (A_MALLOC_RET, at_S_ret): the word at the value is `ret` (jalr x0, 0(x1))"""
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    line = ctx.T.line(rel, ln)
    if not (re.search(r'A_MALLOC_RET : Z :=', line) or re.search(r'ss_pc ss = 0x[0-9a-f]+ \\/ ss_pc ss = 0x', line)):
        return None
    IB, IA = ctx.IB, ctx.IA
    s = IB.at(v)
    if not s:
        return None
    fn, off, sz = s[0]
    rets = [a for a in range(IB.byname[fn][0][0], IB.byname[fn][0][0] + sz, 2) if IB.word(a, 4) == 0x00008067]
    rab = [x for x in ctx.rabmatch(r) if x[11] == r[11]]
    av = ival(rab[0][10]) if rab else None
    meas = (f'{rel}:{ln} {v:#x} = {fn}+{off:#x} in image B {IB.sha}; the word there is {IB.word(v, 4):#010x} = ret (jalr x0, 0(x1)); '
            f'{fn} ({sz} bytes) has its ret instructions at {", ".join(hex(a) for a in rets)}; the A twin\'s {av:#x} is '
            f'{IA.name(av)}, word {IA.word(av, 4):#010x}')
    return V('RET-INSTRUCTION', meas, lambda x: x in rets)


def rule_same_symbol(ctx, r):
    """an address whose A twin names X+off in image A: B's value must be X+off in image B, and must not be
    cgif's address of some symbol our image B has elsewhere"""
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    IB, IA, CB = ctx.IB, ctx.IA, ctx.CB
    if not (IB.lo <= v <= IB.top):
        return None
    rab = [x for x in ctx.rabmatch(r) if x[0] == 'SAME-SYMBOL' and x[11] == r[11]]
    if not rab:
        return None
    av = ival(rab[0][10])
    sa = IA.at(av)
    if not sa:
        return None
    nm, off, sz = sa[0]
    if nm not in IB.byname or len(IB.byname[nm]) != 1 or len(IA.byname[nm]) != 1:
        return None
    exp = IB.byname[nm][0][0] + off
    stale = [n for n, o, s in CB.at(v) if o == 0 and n in IB.byname and IB.byname[n][0][0] != v]
    meas = (f'{rel}:{ln} {v:#x} = {nm}+{off:#x} in image B {IB.sha} symbols ({IB.byname[nm][0][1]} bytes); the A twin '
            f'{rab[0][3]}:{rab[0][4]} writes {av:#x} = {nm}+{off:#x} in image A {IA.sha} ({IA.byname[nm][0][1]} bytes)'
            + (f'; stale-donor check: cgif B starts {stale} there, which image B has elsewhere' if stale else
               '; stale-donor check: no cgif-B symbol that image B has elsewhere starts at the value'))
    return V('SAME-SYMBOL-OFFSET', meas, lambda x: x == exp and not stale)


def rule_gi(ctx, r):
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    if rel != 'YD1r.v':
        return None
    F, IB = ctx.F, ctx.IB
    line = ctx.T.line(rel, ln)
    if 'CmdGlob.A_G_REC +' in line or 'CmdGlob.A_REC_SPILL' in line:
        ivs = [(b, o, o + n) for b, o, n in F.gi]
        for m in re.finditer(r'\(CmdGlob\.(A_\w+)(?: \+ (\d+))?, CmdGlob\.(A_\w+) \+ (\d+)\)', line):
            b, o, e = m.group(1), int(m.group(2) or 0), int(m.group(4))
            for g, val in ((2, o), (4, e)):
                if m.group(g) is None or val != v:
                    continue
                cand = [x for x in ivs if x[0] == b and (x[1] == o or x[2] == e)]
                if not cand:
                    continue
                bb, eo, ee = cand[0]
                exp = eo if g == 2 else ee
                base = F.cg[b][0]
                onm, ooff, osz = IB.at(base)[0]
                gd = [x for x in IB.globals if x['beg'] == base]
                dsz = gd[0]['size'] if gd else None
                meas = (f'{rel}:{ln} GI_IVS entry ({b}{" + " + str(o) if o else ""}, {b} + {e}): {F.gi_where}; image B: {b} = '
                        f'{base:#x} = {onm} (symbol size {osz}, descriptor size {dsz}); the range [{base + eo:#x}, {base + ee:#x}) '
                        f'lies inside it, in {IB.sec(base)} (zero at load); bytes_of_GI / GI_of_bytes are Qed against GI_cmdA')
                return V('GI-RANGES', meas, lambda x, exp=exp, base=base, osz=osz: x == exp and exp <= osz)
    m = re.search(r'\(a < (0x[0-9a-f]+) \\/ (0x[0-9a-f]+) <= a\) -> a <> 0', line)
    if m and v in (ival(m.group(1)), ival(m.group(2))):
        lo = min(F.cg[b][0] for b, n in F.pg)
        hi_b, hi_n = max(F.pg, key=lambda x: F.cg[x[0]][0])
        hi = F.cg[hi_b][0] + hi_n
        gq = [x for x in IB.globals if x['beg'] == F.cg[hi_b][0]]
        exp = lo if v == ival(m.group(1)) else hi
        meas = (f'{rel}:{ln} not_inFPC excludes the program footprint [{lo:#x}, {hi:#x}): {F.pg_where}; image B symbols: '
                f'{IB.name(lo)} at the low end, {IB.name(F.cg[hi_b][0])} with descriptor size {gq[0]["size"] if gq else "?"} at the high end')
        return V('GI-RANGES', meas, eq_judge(exp))
    m = re.search(r'gi_byte a -> (0x[0-9a-f]+) <= a < (0x[0-9a-f]+)', line)
    if m and v in (ival(m.group(1)), ival(m.group(2))):
        stop = IB.byname['__stop_asan_globals'][0][0]
        lo_gi = min(F.cg[b][0] + o for b, o, n in F.gi)
        exp = stop if v == ival(m.group(1)) else IB.top
        meas = (f'{rel}:{ln} gi_byte_range: the lowest GI byte is {lo_gi:#x}; the bounds are __stop_asan_globals {stop:#x} (image B '
                f'symbols: the end of the descriptor table, below .bss) and the image top {IB.top:#x} (program headers); the lemma is Qed')
        return V('GI-RANGES', meas, lambda x, exp=exp: x == exp)
    return None


def rule_stack_malloc(ctx, r):
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    if rel != 'YF0l.v':
        return None
    line = ctx.T.line(rel, ln)
    IB = ctx.IB
    have = sorted(int(n.split('_')[-1]) for n in IB.byname if re.fullmatch(r'__asan_stack_malloc_\d+', n))
    for m in re.finditer(r'cid =\? (\d+) then (0x[0-9a-f]+)', line):
        cid, pc = int(m.group(1)), ival(m.group(2))
        if cid != v:
            continue
        meas = (f'{rel}:{ln} pc_stack_malloc: image B {IB.sha} has __asan_stack_malloc_N for N in {have}; '
                f'__asan_stack_malloc_{cid} is at {pc:#x}, the pc the line pairs with class {cid}')
        return V('STACK-MALLOC-CLASSES', meas, lambda x, pc=pc: [y[0] for y in IB.byname.get(f'__asan_stack_malloc_{x}', [])] == [pc])
    return None


def rule_counts(ctx, r):
    """small counts read from the file's own lists"""
    F, rel, ln, v = ctx.F, r[5], int(r[6]), ival(r[11])
    line = ctx.T.line(rel, ln)
    h4, t12 = len(F.head4), len(F.tail12)
    where = f'lib/B/YD1g.v:{F.head4_ln} TFIB_HEAD4 has {h4} entries, :{F.tail12_ln} TFIB_TAIL12 has {t12}'
    m = re.search(r'firstn \(length \(a_maps ch\) - (\d+)\) \(skipn (\d+) \(a_maps ch\)\)', line)
    if m:
        if int(m.group(1)) == v:
            return V('LIST-COUNT', f'{rel}:{ln} musl_maps drops the head and tail maps: {where}; {h4} + {t12} = {h4 + t12}', eq_judge(h4 + t12))
        if int(m.group(2)) == v:
            return V('LIST-COUNT', f'{rel}:{ln} musl_maps skips the head maps: {where}', eq_judge(h4))
    if re.search(r'(?:i <> |ALLMAPS )\(?' + str(v) + r' \+ length \(musl_maps ch\)', line):
        return V('LIST-COUNT', f'{rel}:{ln} {v} + length (musl_maps ch) + t is position t of TFIB_TAIL12 in ALLMAPS = TFIB_HEAD4 ++ musl ++ TFIB_TAIL12: {where}', eq_judge(h4))
    m = re.search(r'\(i <> (\d+)\)%nat -> \(i <> (\d+)\)%nat ->', line)
    if m and v in (int(m.group(1)), int(m.group(2))):
        known = [i for i, x in enumerate(F.HEAD4) if x in F.KNOWN]
        k = 0 if int(m.group(1)) == v else 1
        meas = (f'{rel}:{ln} unknown_at excludes the HEAD4 positions whose map is KNOWN: lib/B/YD1g.v:{F.HEAD4_ln} HEAD4 = '
                f'[{"; ".join(F.HEAD4)}], :{F.KNOWN_ln} KNOWN = [{"; ".join(F.KNOWN)}]: positions {known}; this is exclusion {k + 1}')
        return V('LIST-COUNT', meas, eq_judge(known[k] if len(known) > k else None))
    m = re.search(r'skipn (\d+) \(?(REG0K|REG0|MREG0|MKREG0|SREG0)\b', line)
    if m and int(m.group(1)) == v:
        reg0 = ctx.reg0
        head = 0
        for e in reg0:
            if re.match(r'R_\w+$', e):
                head += 1
            else:
                break
        meas = (f'{rel}:{ln} skipn {v} {m.group(2)} drops the register-based head regions: lib/B/YFhy.v REG0 starts with '
                f'[{"; ".join(reg0[:head])}] ({head} regions based at atoms 11 and 2), then absolute cells ({reg0[head][:24]} ..); '
                f'REG0K, MREG0, MKREG0 and SREG0 keep that head (firstn n REG0 / REG0K with n > {head})')
        return V('LIST-COUNT', meas, eq_judge(head))
    m = re.search(r'firstn (\d+) REG0 \+\+', line)
    if m and int(m.group(1)) == v:
        reg0 = ctx.reg0
        idx = [i for i, e in enumerate(reg0) if e.startswith('YP09.mkRegion (Some aSSLOT)')]
        meas = (f'{rel}:{ln} SREG0 keeps REG0 up to the per-chunk regions it replaces: lib/B/YFhy.v REG0 has {len(reg0)} entries and '
                f'its first per-chunk region (Some aSSLOT) is entry {idx[0] if idx else None}; cgif\'s REG0 has it at entry {ctx.creg0_sslot} '
                f'(the donor value)')
        return V('LIST-COUNT', meas, eq_judge(idx[0] if idx else None))
    return None


def rule_consts(ctx, r):
    """values computed from named constants of lib/Reusable that both builds share"""
    F, rel, ln, v = ctx.F, r[5], int(r[6]), ival(r[11])
    line = ctx.T.line(rel, ln)
    cap, cw = F['depot_cap']
    fp, fw = F['frames_per']
    rab = [x for x in ctx.rabmatch(r) if x[11] == r[11]]
    av = ival(rab[0][10]) if rab else None
    for rx in (r"depot_ids S'? <= (?P<n>\d+)", r'mkAF (?:0|1) (?P<n>\d+) 0\)', r'1 <= nD <= (?P<n>\d+)', r'0 <= cur <= (?P<n>\d+)'):
        if grp(line, rx, v) and v in (cap + 1, cap + 2):
            k = v - cap
            meas = (f'{rel}:{ln} depot id bound {v} = DEPOT_CAP + {k}: {cw}; '
                    + ('ids after one insertion (depot_after) are at most DEPOT_CAP + 2' if k == 2 else
                       'nD_range / depot_ids_bound* (Qed) derive it from depot_inv_cap')
                    + f'; cgif\'s DEPOT_CAP is {ctx.cgif_cap} (the donor value {ctx.cgif_cap + k})')
            return V('REUSABLE-CONSTANT', meas, eq_judge(cap + k))
    if grp(line, r'(?:2 <= TOT <= |mkAF 2 )(?P<n>\d+)', v):
        need = fp * (cap + 2)
        meas = (f'{rel}:{ln} TOT bound {v}: TOT (the depot\'s frames) <= {fp} * depot ids ({fw}) and depot ids <= DEPOT_CAP + 2 = '
                f'{cap + 2} ({cw}), so any bound >= {need} holds; {v} = {fp} * ({cap} + 3) + 1 is the A twin\'s value ({av}), '
                f'kept by the relay; TOT_range is Qed')
        return V('REUSABLE-CONSTANT', meas, lambda x: x == av and x >= need)
    if grp(line, r'SB \+ 24 \* 2 \^ 32 \+ (?P<n>\d+)', v):
        k, kw = F['kfao']
        return V('REUSABLE-CONSTANT', f'{rel}:{ln} the end of the usable part of a primary region: {kw} (the free array starts there)', eq_judge(k))
    if grp(line, r'(?:\(41%nat, mkAF 0 \(2 \^ |0 <= CPv < 2 \^ )(?P<n>\d+)', v):
        k, kw = F['kfao']
        e = (k // 16 - 1).bit_length()
        meas = (f'{rel}:{ln} CPv = coff / 16 (lib/B/YFgq.v CPv; atom 41 is CPv: EqCP) with coff < kFreeArrayOffset ({kw}): '
                f'CPv < {k // 16:#x} <= 2 ^ {e}')
        return V('REUSABLE-CONSTANT', meas, eq_judge(e))
    m = re.search(r'Definition EV_LIB : Z := (\d+)\.', line)
    if m and int(m.group(1)) == v:
        meas = (f'{rel}:{ln} EV_LIB {v}: lib/B/Prog/HarnessArgsEv.v:146 ev_ltoi_lib (Qed) proves EV_LTOI pl <= EV_LIB for every '
                f'payload (its header: at most 2 + 32 * 78 + 7 = 2,505 events); the A twin\'s value is {av} (the same C program and '
                f'allocator calls); EV_MAX = 11776 (lib/Reusable/YG00.v)')
        return V('EVENT-BUDGET', meas, lambda x: x == av and 2505 <= x <= 11776)
    return None


def rule_topf(ctx, r):
    F, rel, ln, v = ctx.F, r[5], int(r[6]), ival(r[11])
    if rel != 'YD1v.v':
        return None
    line = ctx.T.line(rel, ln)
    if not re.search(r'TOPF|usp - \d+ <=', line):
        return None
    low, up, uln = F.utop
    pg = F.epg[0]
    for s, e, t, val in nums(line):
        if val != v:
            continue
        pre = line[max(0, s - 16):s]
        if re.search(r'usp - $', pre):
            role, why = low, f'lib/B/YD1g.v:{uln} uTopRel (Qed, from the start-up certificate): usp - {low} <= u eTop <= usp + {up}'
        elif re.search(r'usp \+ $', pre) and 'TOPF usp <=' in line[:s]:
            role, why = up, f'{up} = {pg - 1} - {low}: TOPF usp <= usp - {low} + {pg - 1}; uTopRel states the same {up}'
        elif re.search(r'usp \+ $', pre):
            role, why = up - 15, f'{up - 15} = {up} - 15: usp is 16-aligned and t page-aligned, so t <= usp + {up} gives t <= usp + {up - 15}'
        elif re.search(r'\+ $', pre) and val == pg - 1:
            role, why = pg - 1, f'page size - 1 = {pg - 1} (rounds up to a page)'
        elif val == pg:
            role, why = pg, f'the page size {pg} (lib/B/YD1g.v epg v := 4096 * EVar v)'
        elif re.search(r'mod 4096 = $', pre):
            role, why = 0, 't mod 4096 = 0: t is page-aligned'
        else:
            continue
        return V('TOPF-ARITH', f'{rel}:{ln} col {s + 1} `{line[max(0, s - 14):e + 4].strip()}`: {why}', eq_judge(role))
    return None


def rule_misc_text(ctx, r):
    """remaining text anchors: H1_8 (YCmdWorldH8.H1_H8), the map header window (the file's own run_ok)"""
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    line = ctx.T.line(rel, ln)
    T = ctx.T
    if rel == 'YD2i.v' and grp(line, r'a - a mod (?P<n>\d+)', v):
        l2, mm = T.find('B/YCmdWorldH8.v', r'Theorem H1_H8 : .*?\(Z_to_bv 64 \(a - a mod (\d+)\)\)', re.S)
        return V('CONTRACT-RESTATED', f'{rel}:{ln} H1_8 is discharged by lib/B/YCmdWorldH8.v:{l2} Theorem H1_H8 (Qed), whose statement '
                 f'has (a - a mod {mm.group(1)})', eq_judge(int(mm.group(1))))
    if rel == 'YFjo.v':
        if grp(line, r'mb \+ (?P<n>\d+) <= a < mb \+ MSv', v):
            l2, mm = T.find('B/YFjo.v', r'Definition run_ok \(r : Z \* Z \* Z\) : Prop :=\s*\(mb \+ (\d+) <= fst')
            return V('FILE-ANCHOR', f'{rel}:{ln} the map\'s header window [mb, mb + {mm.group(1)}) is the same in the file\'s run_ok '
                     f'({rel}:{l2}), WIN1S and skel_okb (Some aMAP, 0, {mm.group(1)}); the walk\'s Qed lemmas use them together',
                     eq_judge(int(mm.group(1))))
        if grp(line, r'MSv / (?P<n>\d+)\)', v):
            return V('WIDTH', f'{rel}:{ln} the map\'s shadow is MSv / {v} bytes: {ctx.F["sscale"][1]}', eq_judge(ctx.F['sscale'][0]))
    return None


def rule_geometry(ctx, r):
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    if rel != 'YB12.v':
        return None
    line = ctx.T.line(rel, ln)
    IB = ctx.IB
    m = re.search(r'TFIB_TEXT_N : nat := (\d+)', line)
    if m and int(m.group(1)) == v:
        lo, hi = IB.secs['.text']
        return V('IMAGE-GEOMETRY', f'{rel}:{ln} image B .text [{lo:#x}, {hi:#x}) section header: ({hi:#x} - {lo:#x}) / 4 = {(hi - lo) // 4}',
                 eq_judge((hi - lo) // 4))
    m = re.search(r'ph_addr_z := (0x[0-9a-f]+)', line)
    if m and ival(m.group(1)) == v:
        e = IB.ehdr['e_phoff']
        return V('IMAGE-GEOMETRY', f'{rel}:{ln} ph_addr_z: image B ELF header e_phoff = {e:#x} and the first PT_LOAD maps file offset 0 '
                 f'at {IB.lo:#x}, so the program headers are at {IB.lo + e:#x}', eq_judge(IB.lo + e))
    return None


def rule_decode(ctx, r):
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    if rel != 'YE3e.v':
        return None
    line = ctx.T.line(rel, ln)
    m = re.search(r'decode_any \((0x[0-9a-f]+)%bv : bv 32\) = Some \(Jal (\d+) (\d+), 4%Z\)', line)
    if not m or int(m.group(3)) != v:
        return None
    w = ival(m.group(1))
    prev = ctx.T.line(rel, ln - 2)
    pm = re.search(r'fetch_word tfibsegs \((0x[0-9a-f]+)%bv : word\) = Some \((0x[0-9a-f]+)%bv', prev)
    pc = ival(pm.group(1))
    wb = ctx.IB.word(pc, 4)
    imm = jal_imm(w)
    enc = imm & ((1 << 21) - 1)
    tgt = pc + imm
    meas = (f'{rel}:{ln} J-type immediate of {w:#010x} = {imm} (the 21-bit field {enc}); the word is image B\'s bytes at {pc:#x} '
            f'(read {wb:#010x}; {rel}:{ln - 2} F_ lemma by ftac); the jump target {tgt:#x} is {ctx.IB.name(tgt)}; both lemmas are Qed '
            f'by kernel computation')
    return V('DECODED-IMMEDIATE', meas, lambda x: x == enc and wb == w)


def rule_itab(ctx, r):
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    if rel != 'YB05.v' or 'startup_plan_tfib_ranges' not in ctx.T.line(rel, ln):
        return None
    line = ctx.T.line(rel, ln)
    lo_t, hi_t = ctx.IB.secs['.text']
    rs = [(ival(a), int(n)) for a, n in re.findall(r'\((0x[0-9a-f]+), (\d+)%nat\)', line)]
    ok = all(lo_t <= a and a + 4 * n <= hi_t for a, n in rs)
    uses = ctx.uses_in_b('startup_plan_tfib_ranges', rel)
    meas = (f'{rel}:{ln} instruction counts of the start-up plan\'s code table: a by-use grep finds startup_plan_tfib_ranges only '
            f'at {", ".join(uses)} (IT0 := mk_itab_ranges TSEGS startup_plan_tfib_ranges), whose IT0_ok (Qed) is mk_itab_ranges_sound '
            f'for every list, so no value of the list can make a claim false (a missing instruction only makes the start-up '
            f'computation fail, and the build is green); all {len(rs)} ranges [lo, lo + 4n) lie inside image B .text '
            f'[{lo_t:#x}, {hi_t:#x}): {ok}')
    return V('SOUND-FOR-ANY-VALUE', meas, lambda x: ok, control='na:the list is sound for every value (mk_itab_ranges_sound)')


def rule_kept_bound(ctx, r):
    """true bounds that are not this image's bound"""
    F, IB, rel, ln, v = ctx.F, ctx.IB, r[5], int(r[6]), ival(r[11])
    line = ctx.T.line(rel, ln)
    if rel == 'YE7d.v' and re.search(r'in_rom tfibsegs a -> 0 <= a < (0x[0-9a-f]+)', line):
        rom = max(va + fs for va, fs, ms, off, fl in IB.loads if not fl & 2)
        meas = (f'{rel}:{ln} snl_rom_low: every non-writable PT_LOAD of image B {IB.sha} ends at or below {rom:#x}, so the bound {v:#x} '
                f'(the A twin writes the same literal, {r[10]}) holds; the lemma is Qed over the segment table')
        return V('TRUE-WEAKER-BOUND', meas, lambda x: x >= rom, control='na:a bound; every value >= the measured rom end is true')
    if rel in ('YFjm.v', 'YFk1.v') and grp(line, r'(?P<n>\d+) <= SMv', v):
        klsb, kw = F['klsb']
        iend, iw = F['imgend']
        tight = klsb + iend // 8
        l0, m0 = ctx.T.find('B/YFjm.v', r'kLowShadowBeg \+ TFIB_IMG_END / 8 <= SMv')
        moved = (v - F['shoff'][0]) * 8
        cg = ctx.cgif_smv
        meas = (f'{rel}:{ln} lower bound of SMv in the low shadow band: lib/B/YFjm.v:{l0} states the case as `kLowShadowBeg + '
                f'TFIB_IMG_END / 8 <= SMv`; {kw}, {iw} (= the image B top from its program headers {IB.top:#x}), so the bound is '
                f'{tight} ({tight:#x}); the file writes {v} ({v:#x}) = SHADOW_OFF + {moved:#x} / 8, the shadow of {moved:#x} '
                f'({IB.name(moved)}), i.e. cgif\'s {cg} (SHADOW_OFF + {(cg - F["shoff"][0]) * 8:#x} / 8, the shadow of a cgif .bss '
                f'address) moved by port_core as if it were an address (class B); the statement stays true (weaker) and is Qed, so no '
                f'claim changes; the same line\'s other numerals are TFIB_IMG_END, kLowShadowBeg and kLowShadowEnd exactly')
        return V('MOVED-MODEL-BOUND', meas, eq_judge(tight), result='FINDING', kind='code', new=str(tight),
                 read_by=ctx.read_by(rel, ln))
    return None


def rule_stop_pc(ctx, r):
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    line = ctx.T.line(rel, ln)
    m = re.search(r'runto (0x[0-9a-f]+) MK_N0', line)
    if not m or ival(m.group(1)) != v:
        return None
    IB = ctx.IB
    xs = [(va, va + ms) for va, fs, ms, off, fl in IB.loads if fl & 1]
    out = all(not (a <= v < b) for a, b in xs)
    uses = ctx.uses_in_b('MK_NR', rel)
    meas = (f'{rel}:{ln} runto {v:#x}: a stop pc outside every executable PT_LOAD of image B ({", ".join(f"[{a:#x}, {b:#x})" for a, b in xs)}): '
            f'{out}, so the walk runs to its own end (cgif stopped at a pc of ___interceptor_malloc); a by-use grep finds MK_NR '
            f'{"at " + ", ".join(uses) if uses else "nowhere but its definition"}, so no statement reads the result')
    return V('STOP-PC-SENTINEL', meas, lambda x: all(not (a <= x < b) for a, b in xs),
             control='na:any pc outside the code is the same sentinel')


def rule_unused(ctx, r):
    """a definition whose only use stores it in a record field that nothing lib/B reaches reads"""
    rel, ln, v = r[5], int(r[6]), ival(r[11])
    line = ctx.T.line(rel, ln)
    m = re.search(r'Definition (A_\w+) : Z := (\d+)\.', line)
    if not m or rel != 'YE2k.v' or int(m.group(2)) != v:
        return None
    name = m.group(1)
    T = ctx.T
    code = T.lines(rel)[1]
    uses = [(i, l) for i, l in enumerate(code, 1) if i != ln and re.search(r'\b' + name + r'\b', l)]
    if len(uses) != 1 or 'mkASink' not in uses[0][1]:
        return None
    args_ = uses[0][1].split('mkASink', 1)[1].split()
    l0, mr = T.find('Reusable/YE00.v', r'Record asink_syms : Type := mkASink \{(.*?)\}\.', re.S)
    fields = re.findall(r'(ak_\w+) :', mr.group(1))
    field = fields[args_.index(name)]
    readers = closure_readers(ctx, field)
    hits = [f for f in readers if ctx.used_in_b(f)]
    if hits:
        print(f'{rel}:{ln} {name}: readers used in lib/B: {hits[:5]}', file=sys.stderr)
        return None
    meas = (f'{rel}:{ln} {name} := {v} (cgif\'s sink-file string; the file\'s comment: fuzz_command\'s harness opens no file): its '
            f'only use is {rel}:{uses[0][0]} tfib_K := mkASink .., which stores it in field {field} of asink_syms '
            f'(lib/Reusable/YE00.v:{l0}); the definitions of lib/Reusable that read {field}, and those that use them '
            f'({", ".join(sorted(readers)[:8])}{" .." if len(readers) > 8 else ""}; {len(readers)} names), occur nowhere in lib/B '
            f'(by-use grep); so no statement lib/B proves or assumes reads the value')
    return V('UNREAD-FIELD', meas, lambda x: True, control='na:no statement or definition lib/B reaches reads the value')


def closure_readers(ctx, field):
    """names of lib/Reusable sentences that mention field, closed under use inside lib/Reusable"""
    T = ctx.T
    files = [f for f in ctx.all_files() if f.startswith('Reusable/')]
    names, todo = set(), [field]
    while todo:
        nm = todo.pop()
        rx = re.compile(r"(?<![\w'])" + re.escape(nm) + r"(?![\w'])")
        for f in files:
            if nm not in ctx.raw_text(f):
                continue
            code = T.lines(f)[1]
            for i, l in enumerate(code, 1):
                if rx.search(l):
                    s, _ = sentence_name(T, f, i)
                    if s and s not in names and s not in (field, 'asink_syms', 'mkASink'):
                        names.add(s)
                        todo.append(s)
    return names


def rule_generated(ctx, r):
    """RAB rows in generated files and the remaining RAB rows: re-measured from image B"""
    F, IB, rel, ln, v = ctx.F, ctx.IB, r[5], int(r[6]), ival(r[11])
    line = ctx.T.line(rel, ln)
    m = re.search(r'z([1248]) \(ANum (0x[0-9a-f]+)\) (0x[0-9a-f]+|\d+)', line)
    if m and rel == 'YF0m.v':
        n, a, val = int(m.group(1)), ival(m.group(2)), ival(m.group(3))
        wb = IB.word(a, n)
        g = [x for x in IB.globals if x['at'] <= a < x['at'] + 64]
        fld = ''
        if g:
            fld = (f'; {a:#x} is word {(a - g[0]["at"]) // 8} of the asan_globals descriptor at {g[0]["at"]:#x} '
                   f'(global {g[0]["name"]} at {g[0]["beg"]:#x})')
        if v == a:
            prev = None
            for k in range(ln - 1, max(0, ln - 50), -1):
                pm = re.search(r'z([1248]) \(ANum (0x[0-9a-f]+)\)', ctx.T.line(rel, k))
                if pm:
                    prev = (ival(pm.group(2)), int(pm.group(1)))
                    break
            nxt = prev[0] + prev[1] if prev else None
            meas = f'{rel}:{ln} generated cell `z{n} (ANum {a:#x}) {m.group(3)}`: image B bytes at {a:#x} ({n} bytes) read {wb:#x}{fld}'
            if prev:
                meas += f'; the cell follows the previous cell of the list ({prev[0]:#x}, {prev[1]} bytes) without a gap'
            return V('GENERATED-CELL', meas, lambda x: IB.word(x, n) == val and (nxt is None or x == nxt))
        if v == val:
            meas = (f'{rel}:{ln} generated cell value {val:#x} at {a:#x}: image B bytes there read {wb:#x}{fld}; {val:#x} is '
                    f'{IB.name(val)} (string {IB.cstr(val)!r})')
            return V('GENERATED-CELL', meas, lambda x: x == wb)
    m = re.search(r'\((0x[0-9a-f]+), (0x[0-9a-f]+)\);', line)
    if m and rel == 'YF0m.v' and ival(m.group(2)) == v:
        a = ival(m.group(1))
        rs = IB.byname['read_stage'][0][0]
        al_ = ctx.twin_line(r)
        am = re.search(r'\((0x[0-9a-f]+), (0x[0-9a-f]+)\);', al_ or '')
        a_end = ival(am.group(1)) + ival(am.group(2)) if am else None
        meas = (f'{rel}:{ln} Tfib_owned_static range ({a:#x}, {v:#x}): from {IB.name(a)} to {a + v:#x} = {IB.name(a + v)} '
                f'(image B symbols); the A twin line `{(am.group(0) if am else "?")}` ends at {a_end:#x} = {ctx.IA.name(a_end)} in image A')
        return V('GENERATED-RANGE', meas, eq_judge(rs - a))
    if rel in ('YB01.v', 'YB03.v'):
        for mm in re.finditer(r'\(EVar (\d+)\); a_off := (\d+) \|\} \(ELit (\d+)\)', line):
            var, off, n = int(mm.group(1)), int(mm.group(2)), int(mm.group(3))
            if n != v:
                continue
            lens = set()
            for st in F.cert.states:
                for b, l, k in st['maps']:
                    if b == Cert.epg_text(var):
                        lens.add(l)
            if len(lens) == 1:
                L_ = lens.pop()
                meas = (f'{rel}:{ln} KDisj shadow zone of the map at page variable {var}: base 512 * EVar {var} + {off} '
                        f'(SHADOW_OFF = {F["shoff"][0]}), length {v} = {L_} / 8, where {L_} is that map\'s a_maps length in every '
                        f'hand-off state of lib/B/YB01.v (and lib/B/YD1g.v TFIB_TAIL12); a length, not an address')
                return V('SHADOW-LENGTH', meas, lambda x, L_=L_, off=off: x == L_ // 8 and off == F['shoff'][0])
    if rel == 'YFk5.v' and grp(line, r'exists \((?P<n>\d+) \+ 2 \* q\)', v):
        inside, _ = proof_lines(ctx.T, 'B/' + rel)
        meas = (f'{rel}:{ln} proof-step witness {v} = SHADOW_OFF / 4096 = {F["shoff"][0]} / 4096 ({F["shoff"][1]}); the line is '
                f'{"inside Proof .. Qed" if ln in inside else "OUTSIDE a proof"} (checked by the kernel); not an address')
        return V('DERIVED-QUOTIENT', meas, eq_judge(F['shoff'][0] // 4096))
    regs = {lo: (nm, hi) for nm, lo, hi in F.regions}
    if v in regs and (rel in ('YD2j.v', 'YE3i.v', 'YD1k.v')):
        xr = ctx.xrefs.get(v, [])
        nm, hi = regs[v]
        meas = (f'{rel}:{ln} {v:#x} is the start of {nm} [{v:#x}, {hi:#x}) of the generated lib/B/YD2j.v IMG_REGIONS; image B code '
                f'forms that address with auipc + addi/load at {", ".join(xr[:4]) or "no site"}; image A\'s code forms the same address '
                f'({len(ctx.xrefs_a.get(v, []))} sites): both images place this constant at {v:#x}')
        return V('GENERATED-REGION-BOUND', meas, lambda x: x in regs and bool(ctx.xrefs.get(x)))
    return None


# ------------------------------------------------------------------------------------------------ engine
def xref_scan(img, targets):
    """{target: ['fn+off', ...]}: a register set by auipc and then used as the base of addi or a load, before the
    register is written again (a linear sweep over every sized function of the image)"""
    out = collections.defaultdict(list)
    for v, sz, n, ty in img.syms:
        if ty != 'STT_FUNC' or not sz:
            continue
        pc, end, regs = v, v + sz, {}
        while pc < end:
            w2 = img.word(pc, 2)
            if w2 is None:
                break
            if w2 & 3 != 3:
                pc += 2
                continue
            w = img.word(pc, 4)
            op, rd, rs1, f3 = w & 0x7f, (w >> 7) & 31, (w >> 15) & 31, (w >> 12) & 7
            if rs1 in regs and (op == 0x13 and f3 == 0 or op == 0x03):
                t = regs[rs1] + sext(w >> 20, 12)
                if t in targets:
                    out[t].append(f'{n}+{pc - v:#x}')
            if op == 0x17:
                regs[rd] = pc + sext(w & 0xfffff000, 32)
            elif op not in (0x23, 0x63, 0x27, 0x0f, 0x73) and rd in regs:
                del regs[rd]
            pc += 4
    return out


def prepare(ctx):
    T, F = ctx.T, ctx.F
    ctx.claim_cache = {}
    ctx.snippets = contract_snippets(F)
    ctx.reg0 = list_entries(T.text('B/YFhy.v'), 'REG0')
    creg0 = list_entries(ctx.C.text('YFhy.v'), 'REG0')
    idx = [i for i, e in enumerate(creg0) if e.startswith('YP09.mkRegion (Some aSSLOT)')]
    ctx.creg0_sslot = idx[0] if idx else None
    l2, m = ctx.C.find('YG01.v', r'Definition DEPOT_MAX : Z := (\d+)\.')
    ctx.cgif_cap = int(m.group(1))
    ctx.cgif_cap_where = f'cgif lib/YG01.v:{l2} DEPOT_MAX := {m.group(1)}'
    ctx.cgif_smv = None
    targets = {0x10330}
    ctx.xrefs = xref_scan(ctx.IB, targets)
    ctx.xrefs_a = xref_scan(ctx.IA, targets)
    ctx.lib_files = None
    ctx.raw = {}

    def all_files():
        if ctx.lib_files is None:
            ctx.lib_files = tree_files(T.root)
        return ctx.lib_files

    def raw_text(f):
        if f not in ctx.raw:
            ctx.raw[f] = open(os.path.join(T.root, f), encoding='utf-8', errors='replace').read()
        return ctx.raw[f]

    def used_in_b(name):
        rx = re.compile(r"(?<![\w'])(?:\w+\.)?" + re.escape(name) + r"(?![\w'])")
        return any(name in raw_text(f) and rx.search('\n'.join(T.lines(f)[1]))
                   for f in all_files() if f.startswith('B/'))
    ctx.all_files, ctx.raw_text, ctx.used_in_b = all_files, raw_text, used_in_b

    def uses_in_b(name, rel):
        """lib/B places that use name, outside the sentence that defines it"""
        rx = re.compile(r"(?<![\w'])(?:\w+\.)?" + re.escape(name) + r"(?![\w'])")
        out = []
        for f in all_files():
            if not f.startswith('B/') or name not in raw_text(f):
                continue
            for i, l in enumerate(T.lines(f)[1], 1):
                if rx.search(l) and not re.search(r'\b(?:Definition|Lemma|Let)\s+' + re.escape(name) + r'\b', l):
                    out.append(f'lib/{f}:{i}')
        return out

    def twin_line(r):
        try:
            return T.line('A/' + r[3], int(r[4]))
        except (OSError, ValueError, IndexError):
            return None
    ctx.uses_in_b, ctx.twin_line = uses_in_b, twin_line


def list_entries(text, name):
    m = re.search(r'Definition ' + name + r' : smem :=\s*\[', text)
    i = m.end()
    depth, j = 1, i
    while depth:
        c = text[j]
        depth += c == '['
        depth -= c == ']'
        j += 1
    out, depth, cur = [], 0, ''
    for ch in text[i:j - 1]:
        depth += ch in '([{'
        depth -= ch in ')]}'
        if ch == ';' and depth == 0:
            out.append(norm(cur))
            cur = ''
        else:
            cur += ch
    if cur.strip():
        out.append(norm(cur))
    return out


def tree_files(root):
    out = []
    for dp, dn, fs in os.walk(root):
        dn.sort()
        for f in sorted(fs):
            if f.endswith('.v'):
                out.append(os.path.relpath(os.path.join(dp, f), root))
    return out


def sentence_name(T, rel, ln):
    code = T.lines(rel)[1]
    for i in range(ln - 1, -1, -1):
        m = re.search(r"\b(?:Lemma|Theorem|Definition|Hypothesis|Hypotheses|Let|Class|Record|Fact|Corollary)\s+\(?([A-Za-z_][\w']*)", code[i])
        if m:
            return m.group(1), i + 1
    return None, None


def read_by(ctx, rel, ln, name=None):
    """first use of the name the numeral sits in (or of `name`), outside its own sentence, by a by-use grep over lib/"""
    T = ctx.T
    if name is None:
        name, dl = sentence_name(T, 'B/' + rel, ln)
    else:
        dl = ln
    if not name:
        return '-'
    stem = rel[:-2]
    rx = re.compile(r"(?<![\w'.])(?:\w+\.)?" + re.escape(name) + r"(?![\w'])")
    for f in ctx.all_files():
        t = ctx.raw_text(f)
        if name not in t or (f != 'B/' + rel and stem not in t):
            continue
        code = T.lines(f)[1]
        for i, l in enumerate(code, 1):
            if f == 'B/' + rel and i <= dl:
                continue
            if rx.search(l):
                return f'lib/{f}:{i} ({name})'
    return '-'


def settle(ctx, r, used):
    v = rule_contract(ctx, r, used)
    if v:
        return v
    for fn in (rule_cert, rule_img_shadow, rule_zero_shadow, rule_hull_margin, rule_img_region, rule_got, rule_dtor,
               rule_call_ret, rule_gi, rule_stack_malloc, rule_counts, rule_consts, rule_topf, rule_misc_text, rule_geometry,
               rule_decode, rule_itab, rule_kept_bound, rule_stop_pc, rule_unused, rule_generated):
        v = fn(ctx, r)
        if v:
            return v
    v = rule_line_claim(ctx, r, used)
    if v:
        return v
    return rule_same_symbol(ctx, r)


def clean(s):
    s = re.sub(r'[\t\n]+', ' ', str(s))
    if re.search(r'/(?:tmp|home|mnt)/', s):
        raise ValueError('host path in evidence text: ' + s)
    return s


def run_set(ctx, rows, name):
    used, out, ctl = set(), [], []
    order = sorted(range(len(rows)), key=lambda i: (rows[i][5], int(rows[i][6] or 0), int(rows[i][8] or 0) if rows[i][8].isdigit() else 0))
    res = [None] * len(rows)
    for i in order:
        r = rows[i]
        try:
            v = settle(ctx, r, used)
        except Exception as e:  # a rule that cannot read its measurement leaves the row open, loudly
            import traceback
            print(f'{name} {r[5]}:{r[6]} {r[11]}: rule error {type(e).__name__}: {e}', file=sys.stderr)
            traceback.print_exc(limit=2, file=sys.stderr)
            v = None
        res[i] = v
    for r, v in zip(rows, res):
        val = ival(r[11])
        if v is None:
            out.append(r + ['NO-RULE', '-', '-', '-', '-', '-'])
            continue
        ok = bool(v.judge(val))
        result, kind, new = v.result, v.kind, v.new
        if not ok and result == 'OK':
            result, kind = 'FINDING', 'code'
            new = str(getattr(v.judge, 'exp', '?'))
            v.read_by = ctx.read_by(r[5], int(r[6]))
        out.append(r + [v.reason, clean(v.meas), result, kind, clean(new), clean(v.read_by)])
        donor = ival(r[10]) if r[10] else None
        if v.control.startswith('na:'):
            ctl.append([name, r[5], r[6], r[7], r[11], v.reason, str(ok), '-', '-', r[10] or '-', '-', v.control])
            continue
        j4 = bool(v.judge(val + 4))
        jd = bool(v.judge(donor)) if donor is not None and donor != val else None
        ctl.append([name, r[5], r[6], r[7], r[11], v.reason, str(ok), hex(val + 4), 'REFUSED' if not j4 else 'ACCEPTED',
                    r[10] or '-', '-' if jd is None else ('REFUSED' if not jd else 'ACCEPTED'), 'value'])
    return out, ctl


def eq_judge(expected):
    """judge(v): v equals the measured value; keeps that value for the new_value column"""
    def j(v):
        return v == expected
    j.exp = expected
    return j


def relay_moved_scan(ctx, args):
    """every RAB numeral of a non-generated lib/B file whose A value is round (a multiple of 4096 or a power of two)
    and whose B value differs, unless the gate pairs it as geometry: the relay (a2b) moved it. Judged: a code or data
    address at the same symbol and offset in both images, or a model constant moved as an address (a power of two
    that lands inside an object)."""
    IB, IA, T = ctx.IB, ctx.IA, ctx.T
    gen = {'YB01.v', 'YB03.v', 'YF0m.v', 'YD2j.v', 'YE3i.v', 'YCej.v', 'YB1w.v'}
    out, extra = [], []
    for r in read_rows(args.rab_full):
        if not r[10] or not r[11] or r[5] in gen or r[0] == 'SAME-GEOMETRY':
            continue
        a, b = int(r[10], 16), int(r[11], 16)
        if a == b or not (a % 0x1000 == 0 or a & (a - 1) == 0) or a == 0:
            continue
        sa, sb = IA.at(a), IB.at(b)
        same = bool(sa and sb and sa[0][0] == sb[0][0] and sa[0][1] == sb[0][1])
        code = IA.sec(a) == '.text' and IB.sec(b) == '.text'
        if a & (a - 1) == 0 and a >= 0x10000 and sa and sa[0][1] > 0x1000 and not code:
            inside, _ = proof_lines(T, 'B/' + r[5])
            ent = [(ival(x), int(n)) for x, n in re.findall(r'\((0x[0-9a-f]+), (\d+), \[', T.text('B/YE2y.v'))]
            mx = max(x + n for x, n in ent) if ent else None
            meas = (f'lib/B/{r[5]}:{r[6]} the A twin {r[3]}:{r[4]} writes {a:#x} = 2^{a.bit_length() - 1}, a round bound; the relay '
                    f'moved it as if it were the address {IA.name(a)} (image A) to {IB.name(b)} (image B); the numeral is a bound of a '
                    f'{"proof-local assert (inside Proof .. Qed)" if int(r[6]) in inside else "statement"}; the largest end '
                    f'fst + snd of lib/B/YE2y.v icpt_rodata is {mx:#x}, below both values, so the proof still holds')
            judge = 'MOVED-MODEL-CONSTANT'
            extra.append(['plugin-hostd/fuzz_command', f'lib/B/{r[5]}', r[6], hex(b), hex(a), 'code', meas])
        elif same:
            judge = 'CODE-ADDRESS' if code else 'DATA-ADDRESS'
            meas = (f'A {a:#x} = {IA.name(a)} in image A, B {b:#x} = {IB.name(b)} in image B: the same symbol and offset'
                    + (f'; instruction words {IA.word(a, 4):#010x} / {IB.word(b, 4):#010x}' if code else ''))
        else:
            judge = 'UNJUDGED'
            meas = f'A {a:#x} = {IA.name(a)}; B {b:#x} = {IB.name(b)}'
        out.append([f'lib/B/{r[5]}', r[6], r[7], r[0], hex(a), hex(b), judge, clean(meas)])
    with open(os.path.join(args.out, 'relay-moved.tsv'), 'w') as fh:
        fh.write('\t'.join(['dst_file', 'dst_line', 'sentence', 'rab_verdict', 'a_value', 'b_value', 'judgement', 'measurement']) + '\n')
        for x in out:
            fh.write('\t'.join(x) + '\n')
    with open(os.path.join(args.out, 'extra-findings.tsv'), 'w') as fh:
        fh.write('\t'.join(['unit', 'file', 'line', 'old', 'new', 'finding_kind', 'evidence']) + '\n')
        for x in extra:
            fh.write('\t'.join(clean(y) for y in x) + '\n')
    c = collections.Counter(x[6] for x in out)
    print('== relay-moved round values (non-generated lib/B files):', dict(c))
    for x in extra:
        print('EXTRA FINDING\t' + '\t'.join(x[1:5]))


def kept_counts(ctx, args):
    """image-derived counts that a lib/B file's own text says were measured on image A (YB05.v's header): re-measured on B"""
    IB = ctx.IB
    head = ctx.T.lines('B/YB05.v')[0][3]
    m = re.search(r'\((\d+) XMemset steps for its (\d+) asan_globals descriptors and the descriptor table, and one PMmap before '
                  r'descriptor (\d+), the first one with an ODR indicator', head)
    rows = []
    if m:
        steps, n, k = map(int, m.groups())
        lo, hi = IB.secs['asan_globals']
        nb = (hi - lo) // 64
        kb = next((i for i, g in enumerate(IB.globals) if g['odr'] not in (0, (1 << 64) - 1)), None)
        rows.append(['lib/B/YB05.v', '4', 'asan_globals descriptors', str(n), str(nb),
                     f'image B asan_globals section [{lo:#x}, {hi:#x}) / 64-byte descriptor = {nb}', 'OK' if nb == n else 'FINDING'])
        rows.append(['lib/B/YB05.v', '4', 'XMemset steps (descriptors + the table)', str(steps), str(nb + 1),
                     f'{nb} descriptors + 1', 'OK' if nb + 1 == steps else 'FINDING'])
        rows.append(['lib/B/YB05.v', '4', 'first descriptor with an ODR indicator', str(k), str(kb),
                     f'image B descriptor {kb} is the first whose odr_indicator word is neither 0 nor -1 '
                     f'({IB.globals[kb]["name"]}, indicator {IB.globals[kb]["odr"]:#x})', 'OK' if kb == k else 'FINDING'])
    with open(os.path.join(args.out, 'kept-counts.tsv'), 'w') as fh:
        fh.write('\t'.join(['file', 'line', 'count', 'text_value', 'image_B_value', 'measurement', 'result']) + '\n')
        for x in rows:
            fh.write('\t'.join(clean(y) for y in x) + '\n')
    for x in rows:
        print('KEPT-COUNT\t' + '\t'.join(x[:5] + x[6:]))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--lib', required=True)
    ap.add_argument('--cgif-lib', required=True)
    ap.add_argument('--img-b', nargs=2, required=True, metavar=('PIN', 'TWIN'))
    ap.add_argument('--img-a', nargs=2, required=True, metavar=('PIN', 'TWIN'))
    ap.add_argument('--img-cgif-b', nargs=2, required=True, metavar=('PIN', 'TWIN'))
    ap.add_argument('--rb-open', required=True)
    ap.add_argument('--rab-full', required=True)
    ap.add_argument('--rab-open', required=True)
    ap.add_argument('--out', required=True)
    args = ap.parse_args()
    ctx = Ctx(args)
    ctx.cgif_files = lambda pat: [f for f in tree_files(ctx.C.root) if f.count('/') == 0 and pat in ctx.C.text(f)][:3]
    ctx.read_by = lambda rel, ln, name=None: read_by(ctx, rel, ln, name)
    prepare(ctx)
    hdr = ['verdict', 'kernel_checked', 'image', 'src_file', 'src_line', 'dst_file', 'dst_line', 'sentence', 'idx', 'kind',
           'src_value', 'dst_value', 'src_class', 'src_res', 'dst_res', 'note']
    H = hdr + ['reason', 'measurement', 'result', 'finding_kind', 'new_value', 'read_by']
    rb = read_rows(args.rb_open)
    ctx.cgif_smv = next((ival(r[10]) for r in rb if r[5] == 'YFjm.v' and r[11] == '0x800b4a71' and r[10]), None)
    STALE = {'STALE-DONOR-CODE-POINTER', 'STALE-DONOR-DATA-POINTER', 'SAME-VALUE-DIFFERENT-OBJECT', 'STALE-DERIVED-QUOTIENT'}
    rab = [r for r in read_rows(args.rab_full) if r[0] in STALE]
    seen = {tuple(r) for r in rab}
    for r in read_rows(args.rab_open):
        if r[0] != 'UNRESOLVED' and tuple(r) not in seen:
            rab.append(r)
            seen.add(tuple(r))
    ctl_all, finds = [], {}
    for name, rows, fn in (('RB', rb, 'triage-rows.tsv'), ('RAB', rab, 'rab-rows.tsv')):
        out, ctl = run_set(ctx, rows, name)
        ctl_all += ctl
        with open(os.path.join(args.out, fn), 'w') as fh:
            fh.write('\t'.join(H) + '\n')
            for r in out:
                fh.write('\t'.join(r) + '\n')
        c = collections.Counter((r[16], r[18]) for r in out)
        print(f'== {name}: {len(out)} rows')
        for k in sorted(c):
            print(f'{name}\t{k[0]}\t{k[1]}\t{c[k]}')
        for r in out:
            if r[18] != 'OK':
                print(f'{name}\t{r[18]}\tlib/B/{r[5]}:{r[6]}\t{r[11]}\t-> {r[20]}\t{r[16]}\tread_by {r[21]}')
                k = (r[5], r[6], r[11])
                if k not in finds and r[18] == 'FINDING':
                    old = str(ival(r[11])) if not r[9] == 'hex' else r[11]
                    finds[k] = ['plugin-hostd/fuzz_command', f'lib/B/{r[5]}', r[6], old, r[20], r[19], r[21], r[17]]
    with open(os.path.join(args.out, 'code-findings.tsv'), 'w') as fh:
        fh.write('\t'.join(['unit', 'file', 'line', 'old', 'new', 'finding_kind', 'read_by', 'evidence']) + '\n')
        for x in finds.values():
            fh.write('\t'.join(x) + '\n')
    relay_moved_scan(ctx, args)
    kept_counts(ctx, args)
    with open(os.path.join(args.out, 'controls.tsv'), 'w') as fh:
        fh.write('\t'.join(['set', 'dst_file', 'dst_line', 'sentence', 'value', 'reason', 'judge(value)', 'value+4',
                            'judge(value+4)', 'donor_value', 'judge(donor_value)', 'control']) + '\n')
        for r in ctl_all:
            fh.write('\t'.join(clean(x) for x in r) + '\n')
    s = collections.defaultdict(collections.Counter)
    for r in ctl_all:
        s[(r[0], r[5])]['rows'] += 1
        if r[11] != 'value':
            s[(r[0], r[5])]['na'] += 1
            continue
        s[(r[0], r[5])]['v+4 refused'] += r[8] == 'REFUSED'
        s[(r[0], r[5])]['donor tried'] += r[10] != '-'
        s[(r[0], r[5])]['donor refused'] += r[10] == 'REFUSED'
    print('== controls (set, reason: rows, v+4 refused, donor tried, donor refused, value-independent)')
    for k in sorted(s):
        d = s[k]
        print(f'{k[0]}\t{k[1]}\t{d["rows"]}\t{d["v+4 refused"]}\t{d["donor tried"]}\t{d["donor refused"]}\t{d["na"]}')
    print(f'images: B {ctx.IB.sha} (symbols {ctx.IB.tsha}), A {ctx.IA.sha} (symbols {ctx.IA.tsha}), cgif B {ctx.CB.sha} (symbols {ctx.CB.tsha})')


if __name__ == '__main__':
    main()
