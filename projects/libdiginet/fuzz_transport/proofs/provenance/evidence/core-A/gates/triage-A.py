#!/usr/bin/env python3
"""triage-A.py: one measured reason per flagged row of port_addr_check (205a90fd19b8, the version of record after 08:00Z;
written for 0d24592683b6, whose changes (2) and (3) the rules below name; --fail-on-flags) over the
libdiginet/fuzz_transport image-A core relocation (row TCA: fuzz_grant's released ASan core moved onto
fuzz_transport.asan e89be137db17 by port_core 83f5203d2a2f). libdiginet/fuzz_decode's gates/triage-A.py
(sha256 77f73f67f443; internal record) with the images, the names and the rules of this unit; D9's reason ids where
they fit, new ids where this unit needs them.

For every row of the gate's raw tsv whose verdict is in the checker's flag set (read from the gate log, where pac-A.sh
appends `--list-flag-classes`), is GENERATOR-FILL (reported, not counted) or is UNMEASURED-NAME (reported, measured by
nothing), it writes one row
    raw_line verdict src_file src_line dst_line sentence idx kind src_value dst_value reason class known detail
The reason id names a rule below; the detail is what the rule MEASURED for that row (image bytes, symtab, program and
section headers, the text of stage/ and stage-out/, the start-up layer of LIB, the patches, the overrides). The class is
  OK-explained  the checker flags, by its own stated rule, a pair it does not decide (a changed non-address, an
                unpaired numeral, a shadow address where no object starts, an extent), and the measurement shows the
                dst value right;
  TOOL-LIMIT    the checker's note states an expected value or a role that the images contradict (a size read as a
                code pointer, a row label read as a symbol name, an mmap offset read as a header distance, a flags word
                read as an address); the dst value is right; the row goes to the address checker's owner;
  REAL          a wrong value in stage-out (none of the rules below accepts a wrong value: such a row is UNEXPLAINED).
A row that no rule accepts is written with reason UNEXPLAINED, and the script exits 1. Every rule checks that the dst
value is fuzz_transport's value of the quantity the src value is in fuzz_grant's image, so a wrong dst value is never
accepted. The `known` column cites the owner's decision for the five known items of the gate brief.

Usage (every input is a parameter):
  triage-A.py --raw RAW.tsv --log RAW.log --run WORK --lib LIB --overrides OVERRIDES.tsv --evidence EV \
      --src-image STRIPPED:TWIN --dst-image STRIPPED:TWIN --donor-lib DONOR_LIB \
      [--stage DIR] [--stage-out DIR] --out ROWS.tsv [--md TRIAGE.md [--controls flag-gate.txt]]
  WORK       port_core run dir (stage/, stage-out/, check.tsv, review.tsv, decimals.tsv, fixed.tsv, patches.log)
  LIB        the target lib the run used; its A/ holds the unit's start-up layer (AB13.v, AF0m.v, AD2j.v)
  EV         the run's evidence dir: zero-shadow-forallb.patch, cell-lookup.patch, dead-arm-ad1g.patch,
             bss-zero-range.patch (rule P-BSSZR; WORK/overrides.tsv gives port_core's status of each override row)
  DONOR_LIB  fuzz_grant's released lib, normalised (A/AB13.v, A/AF0m.v, A/AD2j.v of the donor)
  --stage / --stage-out override WORK/stage and WORK/stage-out (a planted copy of stage-out, for a control)
"""
import argparse
import collections
import difflib
import glob
import hashlib
import os
import re
import struct
import sys

from elftools.elf.elffile import ELFFile

SHADOW_OFF = 0x7fff8000
FILL = 'GENERATOR-FILL'
UMN = 'UNMEASURED-NAME'
OK, TOOL, REAL = 'OK-explained', 'TOOL-LIMIT', 'REAL'
KNOWN = "known, decided by the image-A core's writer (gate (a) brief, item 5)"
# Linux mmap flag bits (include/uapi/asm-generic/mman-common.h, mman.h; riscv64 uses the generic values)
MAP_BITS = [(0x2, 'MAP_PRIVATE'), (0x10, 'MAP_FIXED'), (0x20, 'MAP_ANONYMOUS'), (0x4000, 'MAP_NORESERVE'),
            (0x100000, 'MAP_FIXED_NOREPLACE')]
TFIB_RE = re.compile(r'\btfib_\w+')
NUM_RE = r'(0x[0-9a-fA-F]+|\d+)'


def ival(s):
    if isinstance(s, int):
        return s
    try:
        return int(s, 0) if s else None
    except ValueError:
        return None


def hx(v):
    return hex(v) if isinstance(v, int) else str(v)


def fl8(x):
    return x // 8 * 8


def shadow(a):
    return SHADOW_OFF + a // 8


def pageup(x, p=0x1000):
    return (x + p - 1) // p * p


def sha12(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()[:12] if path and os.path.exists(path) else 'absent'


# ---------------------------------------------------------------- images

class Image:
    """bytes, program and section headers from the stripped image; symbols from its unstripped twin's .symtab."""

    def __init__(self, spec):
        self.path, self.twin = spec.split(':', 1)
        self.data = open(self.path, 'rb').read()
        self.sha = hashlib.sha256(self.data).hexdigest()[:12]
        tdata = open(self.twin, 'rb').read()
        self.twinsha = hashlib.sha256(tdata).hexdigest()[:12]
        e = ELFFile(open(self.path, 'rb'))
        self.entry, self.phentsize, self.phnum = e['e_entry'], e['e_phentsize'], e['e_phnum']
        self.secs = {s.name: (s['sh_addr'], s['sh_size'], s['sh_type'], s['sh_flags']) for s in e.iter_sections()}
        self.secdata = {s.name: s.data() for s in e.iter_sections() if s.name == 'asan_globals'}
        self.phdrs = [(p['p_type'], p['p_vaddr'], p['p_memsz'], p['p_filesz'], p['p_offset']) for p in e.iter_segments()]
        self.loads = [p for p in self.phdrs if p[0] == 'PT_LOAD']
        t = ELFFile(open(self.twin, 'rb'))
        # twin check: every allocated PROGBITS section equal to the stripped image's, except the build id
        self.twin_diff = []
        for s in e.iter_sections():
            if not (s['sh_flags'] & 2) or s['sh_type'] == 'SHT_NOBITS' or s.name == '.note.gnu.build-id':
                continue
            ts = t.get_section_by_name(s.name)
            if ts is None or ts['sh_addr'] != s['sh_addr'] or ts.data() != s.data():
                self.twin_diff.append(s.name)
        self.syms = []
        for x in t.get_section_by_name('.symtab').iter_symbols():
            if x['st_shndx'] != 'SHN_UNDEF' and x.name and not x.name.startswith('$'):
                self.syms.append((x.name, x['st_value'], x['st_size'], x['st_info']['type']))
        self.byname = collections.defaultdict(list)
        for n, v, sz, ty in self.syms:
            self.byname[n].append((v, sz, ty))
        self.label = '/'.join(self.path.split('/')[-3:])
        self.twinlabel = '/'.join(self.twin.split('/')[-3:])
        self._lui = {}

    def sym(self, name):
        c = [x for x in self.byname.get(name, []) if x[2] in ('STT_FUNC', 'STT_OBJECT')] or self.byname.get(name, [])
        return (c[0][0], c[0][1]) if c else None

    def sym_sub(self, sub):
        """the one symbol whose (mangled) name contains sub."""
        c = sorted({(n, v, sz) for n, v, sz, ty in self.syms if sub in n and ty in ('STT_OBJECT', 'STT_FUNC')})
        return c[0] if len(c) == 1 else None

    def at(self, a):
        """objects / functions covering a (start <= a < end), else those starting at a."""
        c = [(n, v, sz) for n, v, sz, ty in self.syms if ty in ('STT_OBJECT', 'STT_FUNC') and v <= a < v + sz]
        return c or [(n, v, sz) for n, v, sz, ty in self.syms if v == a and ty != 'STT_FILE']

    def labels(self, a):
        """symbol labels of a: ('at', NAME, OFF) for every sized function / object covering a and every symbol
        starting at a; ('end', NAME) for every sized function / object ending at a."""
        out = set()
        for n, v, sz, ty in self.syms:
            if ty in ('STT_FILE', 'STT_SECTION'):
                continue
            if ty in ('STT_FUNC', 'STT_OBJECT') and v <= a < v + sz:
                out.add(('at', n, a - v))
            elif v == a:
                out.add(('at', n, 0))
            if sz and v + sz == a and ty in ('STT_FUNC', 'STT_OBJECT'):
                out.add(('end', n))
        return out

    def func_at(self, a):
        c = [(n, v, sz) for n, v, sz, ty in self.syms if ty == 'STT_FUNC' and v <= a < v + sz]
        return c[0] if c else None

    def funcs(self, lo, hi):
        return sorted({(v, n, sz) for n, v, sz, ty in self.syms if ty == 'STT_FUNC' and lo <= v < hi})

    def lui_sites(self, imm20):
        """every `lui rd, imm20` word of .text: (address, rd, containing function (name, start, size))."""
        if imm20 not in self._lui:
            lo, n = self.secs['.text'][0], self.secs['.text'][1]
            b = self.read(lo, n)
            out = []
            for i in range(0, len(b) - 3, 4):
                w = int.from_bytes(b[i:i + 4], 'little')
                if w & 0x7f == 0x37 and (w >> 12) == imm20:
                    out.append((lo + i, (w >> 7) & 31, self.func_at(lo + i)))
            self._lui[imm20] = out
        return self._lui[imm20]

    def sec(self, name):
        s = self.secs.get(name)
        return (s[0], s[0] + s[1]) if s else None

    def pt(self, typ):
        return next((p for p in self.phdrs if p[0] == typ), None)

    def top(self):
        return pageup(max(p[1] + p[2] for p in self.loads))

    def read(self, a, n):
        for p in self.loads:
            if p[1] <= a and a + n <= p[1] + p[3]:
                o = p[4] + a - p[1]
                return self.data[o:o + n]
        return None

    def globals_shadow_end(self):
        """(descriptor count, highest shadow end of a registered global): asan_globals holds one 64-byte descriptor
        per global (beg, size, size_with_redzone, ...); shadow end = 0x7fff8000 + ceil((beg + size_with_rz) / 8)."""
        d = self.secdata.get('asan_globals')
        if not d:
            return None
        hi = 0
        for i in range(0, len(d) - 63, 64):
            beg, size, szr = struct.unpack_from('<QQQ', d, i)
            hi = max(hi, SHADOW_OFF + ((beg + szr + 7) >> 3))
        return len(d) // 64, hi

    def cstr(self, a):
        """(start, bytes) of the printable NUL-terminated string that holds a, read from the image bytes."""
        if self.read(a, 1) is None:
            return None
        s = a
        while s > a - 4096:
            b = self.read(s - 1, 1)
            if b is None or b == b'\0':
                break
            s -= 1
        e = a
        while e < a + 4096:
            b = self.read(e, 1)
            if b is None:
                return None
            if b == b'\0':
                break
            e += 1
        if e == s or self.read(s - 1, 1) != b'\0':
            return None
        bs = self.read(s, e - s)
        if not all(0x20 <= c < 0x7f or c in (9, 10, 13) for c in bs):
            return None
        return s, bs


def qs(bs):
    return '"' + bs.decode('latin-1').replace('\\', '\\\\').replace('\n', '\\n').replace('\t', '\\t') + '"'


def lab(ls):
    return ', '.join(f'{x[1]}+{hx(x[2])}' if x[0] == 'at' else f'end of {x[1]}' for x in sorted(ls))


# ---------------------------------------------------------------- text

class Tree:
    def __init__(self, root, label):
        self.root, self.label, self.cache = root, label, {}

    def lines(self, f):
        if f not in self.cache:
            p = os.path.join(self.root, f)
            self.cache[f] = open(p, errors='replace').read().split('\n') if f and os.path.exists(p) else None
        return self.cache[f]

    def line(self, f, n):
        ls, n = self.lines(f), ival(n)
        return ls[n - 1] if ls and n and 0 < n <= len(ls) else None

    def text(self, f):
        ls = self.lines(f)
        return '\n'.join(ls) if ls is not None else None


def defval(text, name):
    m = re.search(r'Definition\s+' + re.escape(name) + r'\s*:\s*Z\s*:=\s*' + NUM_RE + r'\s*\.', text or '')
    return ival(m.group(1)) if m else None


def defpair(text, name):
    m = re.search(r'Definition\s+' + re.escape(name) + r'\s*:\s*Z\s*\*\s*Z\s*:=\s*\(\s*' + NUM_RE + r'\s*,\s*' + NUM_RE
                  + r'\s*\)', text or '')
    return (ival(m.group(1)), ival(m.group(2))) if m else None


def region(text, name):
    m = re.search(r'Definition\s+' + re.escape(name) + r'\s*:\s*region\s*:=\s*mkRegion\s+\S+\s+(\d+)\s+(\d+)[^\[]*\[\s*'
                  r'mkChunk\s+(\d+)\s+\(CImg\s+(\d+)\)', text or '')
    return tuple(int(x) for x in m.groups()) if m else None


def img_regions(text):
    m = re.search(r'Definition\s+IMG_REGIONS\b[^:]*:[^=]*:=\s*\[(.*?)\]\s*\.', text or '', re.S)
    return [x.strip() for x in m.group(1).split(';') if x.strip()] if m else None


def readf(d, rel):
    p = os.path.join(d, rel) if d else None
    return open(p, errors='replace').read() if p and os.path.exists(p) else None


def adir(d):
    """a lib dir holding A/, or the A/ dir itself -> the dir that holds the A files."""
    if d and os.path.isdir(os.path.join(d, 'A')):
        return os.path.join(d, 'A')
    return d


def parse_patch(path):
    """file -> (set of deleted lines, set of added lines) of a unified diff."""
    out, cur = {}, None
    if not path or not os.path.exists(path):
        return out
    for ln in open(path, errors='replace').read().split('\n'):
        if ln.startswith('+++ '):
            cur = ln[4:].split('\t')[0].strip()
            out.setdefault(cur, (set(), set()))
        elif ln.startswith('--- ') or ln.startswith('@@'):
            continue
        elif cur and ln.startswith('-'):
            out[cur][0].add(ln[1:].rstrip())
        elif cur and ln.startswith('+'):
            out[cur][1].add(ln[1:].rstrip())
    return out


def load_tsv(path):
    if not path or not os.path.exists(path):
        return []
    rows, hdr = [], None
    for ln in open(path, errors='replace'):
        if ln.startswith('#') or not ln.strip():
            continue
        r = ln.rstrip('\n').split('\t')
        if hdr is None:
            hdr = r
            continue
        rows.append(dict(zip(hdr, r)))
    return rows


# ---------------------------------------------------------------- context

PATCHES = ('zero-shadow-forallb.patch', 'cell-lookup.patch', 'ad1q-shape.patch', 'imgtop-alias.patch', 'dead-arm-ad1g.patch',
           'bss-zero-range.patch', 'g-ACfn.patch', 'g-AD1w.patch', 'g-AD1m.patch', 'g-AD1p.patch', 'g-AD1q.patch',
           'g-AD1r.patch', 'g-AD2f.patch', 'afet-cost.patch')
STARTUP_FILES = ('AB13.v', 'AF0m.v', 'AD2j.v')


class Ctx:
    def __init__(self, a):
        self.a = a
        self.G, self.F = Image(a.src_image), Image(a.dst_image)
        self.st = Tree(a.stage or os.path.join(a.run, 'stage'), 'stage')
        self.so = Tree(a.stage_out or os.path.join(a.run, 'stage-out'), 'stage-out')
        self.startup = adir(a.lib)
        self.donor_a = adir(a.donor_lib)
        self.su = {f: readf(self.startup, f) for f in STARTUP_FILES}
        self.dn = {f: readf(self.donor_a, f) for f in STARTUP_FILES}
        self.zs = parse_patch(os.path.join(a.evidence, 'zero-shadow-forallb.patch'))
        self.cl = parse_patch(os.path.join(a.evidence, 'cell-lookup.patch'))
        self.da = parse_patch(os.path.join(a.evidence, 'dead-arm-ad1g.patch'))
        bz = os.path.join(a.evidence, 'bss-zero-range.patch')
        self.bz = parse_patch(bz) if os.path.exists(bz) else {}
        # the G patches (rule P-GHUNK): patch name -> file -> (deleted lines, added lines)
        self.gp = {p: parse_patch(os.path.join(a.evidence, p)) for p in G_PATCHES
                   if os.path.exists(os.path.join(a.evidence, p))}
        # every patch of the run (rule P-LINEPAIR: a line a patch changed is not paired by line)
        self.allp = {p: parse_patch(os.path.join(a.evidence, p)) for p in PATCHES}
        # port_core's status of each --override row in this run (WORK/overrides.tsv): (file, donor line, old, new) -> status
        self.ovst = {}
        for r in load_tsv(os.path.join(a.run, 'overrides.tsv')):
            if r.get('line', '').isdigit():
                self.ovst[(r['file'], int(r['line']), ival(r.get('old')), ival(r.get('new')))] = r.get('status', '')
        plog = readf(a.run, 'patches.log') or ''
        self.patched = collections.defaultdict(set)
        cur = None
        for ln in plog.split('\n'):
            if ln.startswith('== '):
                cur = os.path.basename(ln[3:].strip())
            m = re.match(r'patching file (\S+)', ln)
            if m and cur:
                self.patched[cur].add(m.group(1))
        # overrides: (file, donor line) -> [(old, new, text line no)]
        self.ovr = collections.defaultdict(list)
        for i, ln in enumerate(open(a.overrides, errors='replace').read().split('\n'), 1):
            if not ln.strip() or ln.startswith('#'):
                continue
            c = ln.split('\t')
            if len(c) >= 4 and ival(c[2]) is not None and ival(c[3]) is not None and c[1].isdigit():
                self.ovr[(c[0], int(c[1]))].append((ival(c[2]), ival(c[3]), i))
        self.ovr_name = os.path.basename(a.overrides)
        # port_core's own decision tables, keyed by (file, donor line)
        self.dec = collections.defaultdict(list)
        for t in ('check.tsv', 'review.tsv', 'fixed.tsv'):
            for r in load_tsv(os.path.join(a.run, t)):
                if r.get('line', '').isdigit():
                    self.dec[(r['file'], int(r['line']))].append((t, ival(r.get('old')), ival(r.get('new')),
                                                                  r.get('status') or r.get('new_sym') or ''))
        for r in load_tsv(os.path.join(a.run, 'decimals.tsv')):
            if r.get('line', '').isdigit():
                self.dec[(r['file'], int(r['line']))].append(('decimals.tsv', ival(r.get('old')), ival(r.get('new')),
                                                              r.get('action', '') + ' ' + r.get('why', '')))
        self._uses = None
        self.facts = {}

    # names used anywhere: stage-out, the unit lib
    def uses(self, name, skip=()):
        if self._uses is None:
            self._uses = collections.defaultdict(set)
            for root, lb in ((self.so.root, 'stage-out'), (self.a.lib, 'lib')):
                for p in glob.glob(os.path.join(root, '**', '*.v'), recursive=True):
                    rel = lb + '/' + os.path.relpath(p, root)
                    for tok in set(TFIB_RE.findall(open(p, errors='replace').read())):
                        self._uses[tok].add(rel)
        return sorted(f for f in self._uses.get(name, ()) if f not in skip)

    def decision(self, f, line, old):
        out = []
        for t, o, n, why in self.dec.get((f, ival(line) or -1), []):
            if o == old:
                out.append(f'{t} `{why.strip()[:110]}`')
        return '; '.join(dict.fromkeys(out))


# ---------------------------------------------------------------- measured facts (computed once)

def program_range(I):
    lo, hi = I.sym('LLVMFuzzerTestOneInput'), I.sym('__wrap_getenv')
    return (lo[0], hi[0]) if lo and hi else None


def tfib_sym(I, x):
    for n in (x, '__' + x, '_' + x, x.replace('asan_module_', 'asan.module_')):
        s = I.sym(n)
        if s:
            return n, s
    return None


def stack_classes(I):
    out = {}
    for n, v, sz, ty in I.syms:
        m = re.fullmatch(r'__asan_stack_malloc_(\d+)', n)
        if m and ty == 'STT_FUNC':
            out[int(m.group(1))] = v
    return out


def arms(line):
    return {int(k): int(v, 16) for k, v in re.findall(r'cid\s*=\?\s*(\d+)\s+then\s+(0x[0-9a-f]+)', line or '')}


def jt_table(I, fname, sec='.rodata'):
    f, r = I.sym(fname), I.sec(sec)
    if not f or not r:
        return None
    fv, fs = f
    a, best = r[0], None
    while a < r[1]:
        n = 0
        while a + 4 * n + 4 <= r[1]:
            e = struct.unpack('<i', I.read(a + 4 * n, 4))[0]
            if fv <= a + e < fv + fs:
                n += 1
            else:
                break
        if n >= 8:
            if best is None or n > best[1]:
                best = (a, n)
            a += 4 * n
        else:
            a += 4
    if not best:
        return None
    b, n = best
    offs = [b + struct.unpack('<i', I.read(b + 4 * i, 4))[0] - fv for i in range(n)]
    return b, n, offs


def r_a3(I):
    lo, hi, se = I.sym('oft_arg0'), I.sym('__start_asan_globals'), I.sym('__stderr_FILE')
    if not (lo and hi and se):
        return None
    return lo[0], hi[0], hi[0] - lo[0], se[0] - lo[0]


def compute_facts(c):
    G, F, fx = c.G, c.F, c.facts
    for k, I in (('G', G), ('F', F)):
        fx[k + 'top'] = I.top()
        fx[k + 'lo'] = I.loads[0][1] // 0x1000 * 0x1000
        fx[k + 'lastload'] = max(p[1] + p[2] for p in I.loads)
        fx[k + 'stop'] = (I.sym('__stop_asan_globals') or (None,))[0]
        fx[k + 'bss'] = (I.sec('.bss') or (None,))[0]
        fx[k + 'tls'] = (I.pt('PT_TLS') or (None, None))[1]
        fx[k + 'phdr'] = (I.pt('PT_PHDR') or (None, None))[1]
        fx[k + 'text'] = I.sec('.text')
        fx[k + 'rodata'] = I.sec('.rodata')
        fx[k + 'load1hi'] = I.loads[1][1] + I.loads[1][2]
        fx[k + 'load2hi'] = I.loads[2][1] + I.loads[2][2]
        fx[k + 'got'] = (I.sec('.got') or (None,))[0]
        fx[k + 'depot'] = I.sym_sub('theDepot')
        fx[k + 'ial'] = I.sym_sub('internal_alloc_placeholder')
        fx[k + 'inst'] = I.sym_sub('_ZN6__asanL8instanceE')
        fx[k + 'tlsbuf'] = I.sym('builtin_tls')
        fx[k + 'ra3'] = r_a3(I)
        fx[k + 'prog'] = program_range(I)
        fx[k + 'sm'] = stack_classes(I)
        fx[k + 'jt'] = jt_table(I, '__strftime_fmt_1')
        fx[k + 'glob'] = I.globals_shadow_end()
    yg = c.st.text('Reusable/YG00.v')
    fx['kPage'], fx['kSecRz'], fx['kChunkHeaderSize'] = (defval(yg, 'kPage'), defval(yg, 'kSecRz'),
                                                         defval(yg, 'kChunkHeaderSize'))
    fx['DEPOT_MAX'] = defval(c.so.text('Reusable/YG01.v'), 'DEPOT_MAX')
    m = re.search(r'lo_tr0\s*:\s*\(1 <= length \(ly_tr0 ly\) <= (\d+)\)%nat', c.so.text('Reusable/YG0f.v') or '')
    fx['TR0_MAX'] = int(m.group(1)) if m else None
    # CZONE: kLowShadowBeg (the kernel's Reusable/YG0f.v) and map_facts SM1 of A/AFjm.v, the goal the bound must meet
    fx['kLowShadowBeg'] = defval(c.so.text('Reusable/YG0f.v'), 'kLowShadowBeg')
    fx['SM1'] = 'kLowShadowBeg + TFIB_IMG_END / 8 <= SMv' in (c.so.text('A/AFjm.v') or '')
    # the zero-shadow pieces of the start-up layer (LIB/A/AF0m.v Tfib_zero_shadow: (lo, hi - lo) entries)
    m = re.search(r'Definition Tfib_zero_shadow : list \(Z \* Z\) :=\s*\[(.*?)\]\s*\.', c.su['AF0m.v'] or '', re.S)
    fx['su_zsh'] = [(int(x, 16), int(y, 16)) for x, y, x2 in
                    re.findall(r'\((0x[0-9a-f]+), (0x[0-9a-f]+) - (0x[0-9a-f]+)\)', m.group(1)) if x == x2] if m else []
    fx['su_bss'] = defpair(c.su['AB13.v'], 'TFIB_BSS')
    fx['dn_bss'] = defpair(c.dn['AB13.v'], 'TFIB_BSS')
    for nm in ('TFIB_DEPOT', 'TFIB_IAL_LO', 'TFIB_INST'):
        fx['su_' + nm] = defval(c.su['AF0m.v'], nm)
        fx['dn_' + nm] = defval(c.dn['AF0m.v'], nm)
    fx['su_ra3'] = region(c.su['AD2j.v'], 'R_A3')
    fx['dn_ra3'] = region(c.dn['AD2j.v'], 'R_A3')
    fx['su_regions'] = img_regions(c.su['AD2j.v'])
    fx['dn_regions'] = img_regions(c.dn['AD2j.v'])
    # the dst AB1w function table: tfib_A_<x> -> value
    t = c.so.text('A/AB1w.v') or ''
    fx['dst_ab1w'] = {m.group(1): int(m.group(2), 16)
                      for m in re.finditer(r'Definition tfib_A_(\w+)\s*:\s*Z\s*:=\s*(0x[0-9a-f]+)', t)}


# ---------------------------------------------------------------- rules
# each rule: (reason id, class, verdicts it may accept, function(d, c) -> detail | (detail, known) | None)

RULES = []
RCLASS = {}


def rule(rid, cls, verdicts):
    def deco(fn):
        RULES.append((rid, set(verdicts), fn))
        RCLASS[rid] = cls
        return fn
    return deco


def tname(d):
    m = re.match(r'Definition tfib_([AE])_(\w+)$', d['sentence'])
    return (m.group(1), m.group(2)) if m else (None, None)


def note_expected(d):
    m = re.search(r'expected (0x[0-9a-f]+)', d.get('note') or '')
    return m.group(1) if m else None


@rule('G-6128', TOOL, ['GEOMETRY-CHANGED'])
def r_g6128(d, c):
    fx, sv, dv = c.facts, ival(d['src_value']), ival(d['dst_value'])
    k = (fx['kPage'] or 0) + (fx['kSecRz'] or 0) - (fx['kChunkHeaderSize'] or 0)
    s, t = d['_sl'] or '', d['_dl'] or ''
    pat = re.compile(r'(SOff aMAP|MAP \+) 6128\b')
    if not (sv == dv == k == 6128 and pat.search(s) and pat.search(t)):
        return None
    m = pat.search(s).group(0)
    return (f'6128 = kPage {fx["kPage"]} + kSecRz {fx["kSecRz"]} - kChunkHeaderSize {fx["kChunkHeaderSize"]} '
            f'(stage/Reusable/YG00.v); src and dst lines both read `{m}`: an offset from the runtime mmap base, not an '
            f'image quantity; value unchanged. The checker reads it as the donor distance load2.memhi - .got.lo = '
            f'{hx(fx["Gload2hi"])} - {hx(fx["Ggot"])} = {hx(fx["Gload2hi"] - fx["Ggot"])} (a coincidence) and expects '
            f'{note_expected(d)} = the same distance in fuzz_transport ({hx(fx["Fload2hi"])} - {hx(fx["Fgot"])}), which '
            f'has no role here')


@rule('K-TLS', OK, ['KIND-CHANGED'])
def r_ktls(d, c):
    fx, sv, dv = c.facts, ival(d['src_value']), ival(d['dst_value'])
    if not (re.search(r'tfib_(text_hi|tbss_lo)\b', d['sentence']) and sv == fx['Gtls'] and dv == fx['Ftls']):
        return None
    return (f'tls.lo = PT_TLS p_vaddr: src {hx(sv)} (.text.hi {hx(fx["Gtext"][1])}, load1.memhi {hx(fx["Gload1hi"])}), '
            f'dst {hx(dv)} (.text.hi {hx(fx["Ftext"][1])}, load1.memhi {hx(fx["Fload1hi"])}); in dst .text.hi = tls.lo = '
            f'load1.memhi, so the checker reads it as an image extent')


def fmt_of(tree, f, name='FMT'):
    return defval(tree.text(f), name)


def window(fmt, n):
    return fl8(shadow(fmt)), fl8(shadow(fmt + n)) + 8


@rule('FMTWIN', OK, ['KIND-CHANGED', 'NON-ADDRESS-CHANGED', 'UNRESOLVED', 'DIFFERENT-SYMBOL'])
def r_fmtwin(d, c):
    m = re.match(r'Definition SH_(LO|HI)$', d['sentence'])
    f = d['_f']
    if not m:
        return None
    fs, fd = fmt_of(c.st, f), fmt_of(c.so, f)
    if fs is None or fd is None:
        return None
    a, b = c.G.cstr(fs), c.F.cstr(fd)
    if not (a and b and a[0] == fs and b[0] == fd and a[1] == b[1]):
        return None
    n = len(a[1])
    ws, wd = window(fs, n), window(fd, n)
    i = 0 if m.group(1) == 'LO' else 1
    sv, dv = ival(d['src_value']), ival(d['dst_value'])
    if not (sv == ws[i] and dv == wd[i]):
        return None
    form = 'floor8(0x7fff8000 + fmt/8)' if i == 0 else 'floor8(0x7fff8000 + (fmt+len)/8) + 8'
    hull = ' (hull_zero in the file: [floor8(shadow x), floor8(shadow(x+n-1)) + 8) with n = len + 1)' if re.search(
        r'Definition hull_zero', c.so.text(f) or '') else ''
    return (f'format {qs(a[1])} (len {n}) src @{hx(fs)}, dst @{hx(fd)} (`Definition FMT` of stage/{f} and stage-out/{f}; '
            f'bytes read from both images, NUL before and after): SH_{m.group(1)} = {form} = src {hx(ws[i])}, dst '
            f'{hx(wd[i])}{hull}')


def strptr(d, c):
    sv, dv = ival(d['src_value']), ival(d['dst_value'])
    a, b = c.G.cstr(sv) if sv is not None else None, c.F.cstr(dv) if dv is not None else None
    if not (a and b and a[1] == b[1] and sv - a[0] == dv - b[0]):
        return None
    f = d['_f']
    fn = ''
    for tree, side, base in ((c.st, 'src', a[0]), (c.so, 'dst', b[0])):
        t = tree.text(f) or ''
        nm = [mm.group(1) for mm in re.finditer(r'Definition (FMT\w*)\s*:\s*Z\s*:=\s*' + NUM_RE + r'\s*\.', t)
              if ival(mm.group(2)) == base]
        if nm:
            fn += f'; {side} {nm[0]} = {hx(base)}'
    return (f'string {qs(a[1])} src @{hx(a[0])}, dst @{hx(b[0])} (bytes equal, NUL before, read from both images); '
            f'offset +{sv - a[0]} on both sides: src {hx(sv)} = {sv}, dst {hx(dv)} = {dv}{fn}')


@rule('N-FMTPTR', OK, ['NON-ADDRESS-CHANGED'])
def r_fmtptr(d, c):
    return strptr(d, c)


@rule('GF-FMTPTR', OK, [FILL])
def r_gffmtptr(d, c):
    r = strptr(d, c)
    if not r:
        return None
    sv, dv = ival(d['src_value']), ival(d['dst_value'])
    ns = len(re.findall(r'(?<![\w.])' + str(sv) + r'(?![\w.])', d['_sl'] or ''))
    nd = len(re.findall(r'(?<![\w.])' + str(dv) + r'(?![\w.])', d['_dl'] or ''))
    if not (ns >= 2 and ns == nd):
        return None
    return r + f'; the donor line holds {sv} {ns} times and the dst line {dv} {nd} times (the same duplicate)'


@rule('N-AD1o-BSS20', OK, ['NON-ADDRESS-CHANGED'])
def r_bss20(d, c):
    fx, sv, dv = c.facts, ival(d['src_value']), ival(d['dst_value'])
    gs, fs = fx['Gbss'] + 0x20, fx['Fbss'] + 0x20
    if not (gs % 8 == 0 and fs % 8 == 0 and sv == gs // 8 and dv == fs // 8 and f'{hx(fs)} / 8' in (d['_dl'] or '')):
        return None
    nm = ', '.join(f'{n}+{hx(fs - v)}' for n, v, sz in c.F.at(fs)) or 'no symbol'
    return (f'(.bss.lo + 0x20) / 8: src ({hx(fx["Gbss"])} + 0x20) / 8 = {sv}, dst ({hx(fx["Fbss"])} + 0x20) / 8 = {dv} '
            f'(dst {hx(fs)} = {nm}); the dst line reads `{hx(fs)} / 8`')


def bss_check(c):
    fx = c.facts
    out = []
    if fx['su_bss'] is None or fx['su_bss'] != (fx['Fstop'], fx['Ftop']):
        return None
    out.append(f'start-up LIB/A/AB13.v TFIB_BSS = ({hx(fx["su_bss"][0])}, {hx(fx["su_bss"][1])})')
    if fx['dn_bss'] and fx['dn_bss'] != (fx['Gstop'], fx['Gtop']):
        return None
    if fx['dn_bss']:
        out.append(f'donor A/AB13.v TFIB_BSS = ({hx(fx["dn_bss"][0])}, {hx(fx["dn_bss"][1])})')
    return '; '.join(out)


@rule('N-AD1o-TOP', OK, ['NON-ADDRESS-CHANGED'])
def r_top(d, c):
    fx, sv, dv = c.facts, ival(d['src_value']), ival(d['dst_value'])
    if not (sv == (fx['Gtop'] - 1) // 8 and dv == (fx['Ftop'] - 1) // 8):
        return None
    x = bss_check(c)
    if x is None:
        return None
    return (f'(IMG_TOP - 1) / 8: src ({hx(fx["Gtop"])} - 1) / 8 = {sv}, dst ({hx(fx["Ftop"])} - 1) / 8 = {dv}; IMG_TOP = '
            f'page-up of the last PT_LOAD end (src {hx(fx["Glastload"])}, dst {hx(fx["Flastload"])}); {x}')


@rule('N-AD1o-ZLEN', OK, ['NON-ADDRESS-CHANGED'])
def r_zlen(d, c):
    fx, sv, dv = c.facts, ival(d['src_value']), ival(d['dst_value'])
    gl, fl = fx['Gtop'] - fx['Gstop'], fx['Ftop'] - fx['Fstop']
    if not (gl % 8 == 0 and fl % 8 == 0 and sv == gl // 8 and dv == fl // 8):
        return None
    x = bss_check(c)
    if x is None:
        return None
    return (f'(IMG_TOP - TFIB_BSS.lo) / 8 with TFIB_BSS.lo = __stop_asan_globals: src ({hx(fx["Gtop"])} - '
            f'{hx(fx["Gstop"])}) / 8 = {sv}, dst ({hx(fx["Ftop"])} - {hx(fx["Fstop"])}) / 8 = {dv}; {x}')


@rule('N-RA3', OK, ['NON-ADDRESS-CHANGED'])
def r_ra3(d, c):
    fx, sv, dv = c.facts, ival(d['src_value']), ival(d['dst_value'])
    g, f = fx['Gra3'], fx['Fra3']
    if not (g and f and sv == g[2] and dv == f[2] and re.search(r'\b%d\b' % g[0], d['_sl'] or '')
            and re.search(r'\b%d\b' % f[0], d['_dl'] or '')):
        return None
    if not fx['su_ra3'] or fx['su_ra3'][0] != f[0] or fx['su_ra3'][3] != f[2]:
        return None
    return (f'R_A3 = [oft_arg0, __start_asan_globals): src [{hx(g[0])}, {hx(g[1])}) {g[2]} bytes, dst [{hx(f[0])}, '
            f'{hx(f[1])}) {f[2]} bytes; start-up LIB/A/AD2j.v R_A3 mkRegion {fx["su_ra3"][0]} CImg {fx["su_ra3"][3]}')


def af0m(c, nm, gv, fv):
    """cross-check against AF0m.v of the donor and of the unit's start-up layer."""
    fx, out = c.facts, []
    if fx['dn_' + nm] is not None:
        if fx['dn_' + nm] != gv:
            return None
        out.append(f'donor A/AF0m.v {nm} = {hx(gv)}')
    if fx['su_' + nm] != fv:
        return None
    out.append(f'start-up LIB/A/AF0m.v {nm} = {hx(fv)}')
    return '; '.join(out)


@rule('N-DEPOT', OK, ['NON-ADDRESS-CHANGED'])
def r_depot(d, c):
    fx, sv, dv = c.facts, ival(d['src_value']), ival(d['dst_value'])
    g, f = fx['Gdepot'], fx['Fdepot']
    if not (g and f and g[1] % 4 == 0 and f[1] % 4 == 0 and sv == g[1] // 4 and dv == f[1] // 4):
        return None
    x = af0m(c, 'TFIB_DEPOT', g[1], f[1])
    if x is None:
        return None
    return f'TFIB_DEPOT / 4 with TFIB_DEPOT = {g[0]}+0: src {hx(g[1])} / 4 = {sv}, dst {hx(f[1])} / 4 = {dv}; {x}'


@rule('N-IAL', OK, ['NON-ADDRESS-CHANGED'])
def r_ial(d, c):
    fx, sv, dv = c.facts, ival(d['src_value']), ival(d['dst_value'])
    g, f = fx['Gial'], fx['Fial']
    if not (g and f and sv == g[1] // 8 and dv == f[1] // 8 and g[1] % 8 == 0 and f[1] % 8 == 0
            and re.search(r'\b%d\b' % f[1], d['_dl'] or '')):
        return None
    x = af0m(c, 'TFIB_IAL_LO', g[1], f[1])
    if x is None:
        return None
    return (f'witness of (P + 8k) mod 8 = 0 with P = TFIB_IAL_LO = {g[0]}: src {hx(g[1])} / 8 = {sv}, dst {hx(f[1])} / 8 '
            f'= {dv}; the dst line states P as {f[1]}; {x}')


@rule('N-INST', OK, ['NON-ADDRESS-CHANGED'])
def r_inst(d, c):
    fx, sv, dv = c.facts, ival(d['src_value']), ival(d['dst_value'])
    g, f = fx['Ginst'], fx['Finst']
    if not (g and f and sv * 8 == g[1] + 168 and dv * 8 == f[1] + 168
            and re.search(r'\b%d \+ 168\b' % f[1], d['_dl'] or '')):
        return None
    x = af0m(c, 'TFIB_INST', g[1], f[1])
    if x is None:
        return None
    return (f'(TFIB_INST + 168) / 8 with TFIB_INST = {g[0]}: src ({hx(g[1])} + 168) / 8 = {sv}, dst ({hx(f[1])} + 168) / 8 '
            f'= {dv}; the dst sentence reads `{f[1]} + 168 + 8 * LGv = ({dv} + LGv) * 8`, exact; {x}')


@rule('N-CELLPATCH', OK, ['NON-ADDRESS-CHANGED'])
def r_cell(d, c):
    sv, dv, f = ival(d['src_value']), ival(d['dst_value']), d['_f']
    old, new = 'nth_error_In _ 60', 'cell_lookup_In _ (ANum (TFIB_OOM + 1))'
    dl, al = c.cl.get(f, (set(), set()))
    if not (sv == 60 and dv == 1 and old in (d['_sl'] or '') and new in (d['_dl'] or '')
            and (d['_sl'] or '').rstrip() in dl and (d['_dl'] or '').rstrip() in al
            and f in c.patched.get('cell-lookup.patch', ())):
        return None
    return (f'cell-lookup.patch (applied to {f}, patches.log): the src line `apply ({old})` (60 = a list index) is the '
            f'patch\'s deleted line, the dst line `apply (AF0x.{new})` its added line; the checker pairs the index 60 '
            f'with the byte offset 1. Neither is an address')


@rule('N-TOT', OK, ['NON-ADDRESS-CHANGED'])
def r_tot(d, c):
    fx, sv, dv = c.facts, ival(d['src_value']), ival(d['dst_value'])
    if d['_f'] != 'A/AFem.v' or not (fx['TR0_MAX'] and fx['DEPOT_MAX']):
        return None
    want = fx['TR0_MAX'] + 1 + 31 * fx['DEPOT_MAX']
    tot = re.search(r'Definition TOT : Z := Z\.of_nat \(length \(ly_tr0 ly\)\) \+ 1 \+ depot_frames S\.',
                    c.so.text('A/AFem.v') or '')
    fb = re.search(r'Lemma depot_frames_bound\b.{0,400}?<= 31 \* Z\.of_nat \(length d\)', c.so.text('A/AFem.v') or '',
                   re.S)
    if not (dv == want and sv != dv and tot and fb and re.search(r'TOT <= %d\b' % dv, d['_dl'] or '')
            and re.search(r'TOT <= %d\b' % sv, d['_sl'] or '')):
        return None
    return ((f'a COUNT, not an address: TOT := length (ly_tr0 ly) + 1 + depot_frames S (stage-out/A/AFem.v), length '
             f'(ly_tr0 ly) <= {fx["TR0_MAX"]} (stage-out/Reusable/YG0f.v lo_tr0), depot_frames <= 31 * length d '
             f'(A/AFem.v depot_frames_bound) with length d <= DEPOT_MAX = {fx["DEPOT_MAX"]} (stage-out/Reusable/YG01.v): '
             f'TOT <= {fx["TR0_MAX"]} + 1 + 31 * {fx["DEPOT_MAX"]} = {want} = dst; the donor\'s {sv} is a weaker true '
             f'bound (that count moved by an earlier relocation)'), KNOWN + ': A/AFem.v TOT_range 127008 is a count')


@rule('SV-MMAP', TOOL, ['SAME-VALUE-DIFFERENT-OBJECT'])
def r_mmap(d, c):
    sv, dv = ival(d['src_value']), ival(d['dst_value'])
    ctx = (d['sentence'] + ' ' + (d['_sl'] or '')).lower()
    if not (sv is not None and sv == dv and re.search(r'mmap|noreplace|ff_class', ctx)):
        return None
    rem, names = sv, []
    for b, n in MAP_BITS:
        if rem & b:
            names.append(n)
            rem &= ~b
    if rem or 'MAP_PRIVATE' not in names or 'MAP_ANONYMOUS' not in names:
        return None
    return (f'mmap flags word {hx(sv)} = ' + ' | '.join(names) + ' (Linux uapi values), remainder 0; context '
            f'`{d["sentence"]}` (mmap flag argument); an ABI constant, never relocated; src and dst text equal. The '
            f'checker reads it as an address inside internal_alloc_placeholder and expects {note_expected(d)}')


@rule('SV-HWCAP', TOOL, ['SAME-VALUE-DIFFERENT-OBJECT'])
def r_hwcap(d, c):
    sv, dv = ival(d['src_value']), ival(d['dst_value'])
    if not (sv is not None and sv == dv and 'KRange (EVar V_HW)' in (d['_sl'] or '') and 'KRange (EVar V_HW)' in
            (d['_dl'] or '')):
        return None
    letters = ''.join(chr(ord('a') + i) for i in range(26) if sv >> i & 1)
    if sv >> 26:
        return None
    return (f'KRange (EVar V_HW) bound {hx(sv)}: AT_HWCAP ISA letter bits {letters} (bit i = letter a+i); not an '
            f'address; src and dst text equal. The checker reads it as an address inside theDepot and expects '
            f'{note_expected(d)}')


def rodata_list(tree):
    t = tree.text('A/AE2y.v') or ''
    m = re.search(r'Definition icpt_rodata\s*:[^=]*:=\s*\[(.*?)\]\s*\.', t, re.S)
    if not m:
        return None
    return [(ival(a), ival(n)) for a, n in re.findall(r'\(\s*' + NUM_RE + r'\s*,\s*' + NUM_RE + r'\s*,\s*\[', m.group(1))]


@rule('SV-RODATA-BOUND', TOOL, ['SAME-VALUE-DIFFERENT-OBJECT'])
def r_rodata_bound(d, c):
    sv, dv = ival(d['src_value']), ival(d['dst_value'])
    pat = r'fst \(fst e\) \+ snd \(fst e\) <= ' + re.escape(d['src_value'] if d['src_value'].startswith('0x') else hx(sv))
    if not (sv is not None and sv == dv and re.search(pat, d['_sl'] or '') and re.search(pat, d['_dl'] or '')
            and 'icpt_rodata' in (c.st.text(d['_f']) or '') and 'icpt_rodata' in (c.so.text(d['_f']) or '')):
        return None
    gl, fl = rodata_list(c.st), rodata_list(c.so)
    if not gl or not fl:
        return None
    ge, fe = max(a + n for a, n in gl), max(a + n for a, n in fl)
    if not (ge <= sv and fe <= dv and min(a for a, n in gl) >= 0 and min(a for a, n in fl) >= 0):
        return None
    return (f'a loose upper bound, not an object: `Hrange : 0 <= fst (fst e) /\\ fst (fst e) + snd (fst e) <= {hx(sv)}` '
            f'over every entry e of icpt_rodata (A/AE2y.v), proved per entry by `cbn; lia`. Measured: the {len(gl)} '
            f'donor entries end at most at {hx(ge)}, the {len(fl)} dst entries at most at {hx(fe)} (stage-out/A/AE2y.v), '
            f'both <= {hx(sv)}. The checker reads it as theDepot+offset and expects {note_expected(d)}')


@rule('U-RODATA-HI', OK, ['UNRESOLVED'])
def r_rodata_hi(d, c):
    fx, sv, dv = c.facts, ival(d['src_value']), ival(d['dst_value'])
    g = fx['Gjt']
    if not ('tfib_rodata_hi' in d['sentence'] and g and dv == fx['Frodata'][1]):
        return None
    k = sv - g[0]
    if not (0 <= k < 4 * g[1] and k % 4 == 0):
        return None
    use = c.uses('tfib_rodata_hi', skip=('stage-out/A/AB1w.v',))
    lo = defval(c.so.text('A/AB1w.v'), 'tfib_rodata_lo')
    return ((f'src {hx(sv)} = cell +{hx(k)} (entry {k // 4}) of the {g[1]}-entry jump table of __strftime_fmt_1 at '
             f'{hx(g[0])}..{hx(g[0] + 4 * g[1])}, = fuzz_grant .rodata.hi {hx(fx["Grodata"][1])} - '
             f'{hx(fx["Grodata"][1] - sv)} (the donor\'s cut point); dst {hx(dv)} = fuzz_transport .rodata.hi '
             f'(section header: .rodata [{hx(fx["Frodata"][0])}, {hx(fx["Frodata"][1])})), so the dst range '
             f'[tfib_rodata_lo {hx(lo)}, tfib_rodata_hi) is the whole .rodata section; written by port_core 83f5203d2a2f '
             f'(item 97); uses of tfib_rodata_hi outside AB1w: {len(use)}'),
            KNOWN + ': tfib_rodata_hi 0x22b4c = .rodata end')


@rule('U-PHDR', OK, ['UNRESOLVED'])
def r_phdr(d, c):
    fx, sv, dv = c.facts, ival(d['src_value']), ival(d['dst_value'])
    if not ('tfib_at_ph_addr' in d['sentence'] and sv == fx['Gphdr'] and dv == fx['Fphdr']):
        return None
    return f'AT_PHDR value: PT_PHDR p_vaddr = src {hx(sv)}, dst {hx(dv)}'


@rule('U-TLSSH', OK, ['UNRESOLVED'])
def r_tlssh(d, c):
    fx, sv, dv = c.facts, ival(d['src_value']), ival(d['dst_value'])
    g, f = fx['Gtlsbuf'], fx['Ftlsbuf']
    if not (g and f and sv and dv and sv >= SHADOW_OFF and dv >= SHADOW_OFF):
        return None
    ks, kd = (sv - SHADOW_OFF) * 8 - g[0], (dv - SHADOW_OFF) * 8 - f[0]
    if not (ks == kd and 0 <= ks < g[1] and g[1] == f[1]):
        return None
    ms, md = shadow(fx['Gtop']) - sv, shadow(fx['Ftop']) - dv
    return (f'0x7fff8000 + a/8 with a = builtin_tls+{hx(ks)} in both (src {hx(g[0] + ks)}, dst {hx(f[0] + kd)}; '
            f'builtin_tls size {hx(g[1])} both); below shadow(IMG_TOP) by {hx(ms)} in src, {hx(md)} in dst')


@rule('K-CZONE', OK, ['KIND-CHANGED', 'UNRESOLVED'])
def r_czone(d, c):
    fx, sv, dv = c.facts, ival(d['src_value']), ival(d['dst_value'])
    gg, fg, kl = fx['Gglob'], fx['Fglob'], fx['kLowShadowBeg']
    if not (sv == 0x80050000 and kl is not None and fx['SM1'] and dv == kl + fx['Ftop'] // 8 and gg and fg
            and fg[1] <= dv and gg[1] <= sv
            and re.search(r'\b%s\b' % re.escape(d['src_value']), d['_sl'] or '')
            and re.search(r'\b%s\b' % re.escape(d['dst_value']), d['_dl'] or '')):
        return None
    return ((f'CZONE, the upper bound of the constant cells\' shadow window [0x7fff8000, CZONE): dst {hx(dv)} = '
             f'kLowShadowBeg {hx(kl)} (stage-out Reusable/YG0f.v) + IMG_TOP {hx(fx["Ftop"])} / 8 (page-up of the last '
             f'PT_LOAD end {hx(fx["Flastload"])}), the least value map_facts SM1 of A/AFjm.v (`kLowShadowBeg + '
             f'TFIB_IMG_END / 8 <= SMv`) allows for the secondary map\'s shadow start SMv, so the window stays below it '
             f'(the goal of A/AFju.v CZ_untouched); the highest shadow end of fuzz_transport\'s {fg[0]} registered '
             f'globals (asan_globals descriptors read from the image) is {hx(fg[1])} <= {hx(dv)}, while the donor\'s '
             f'{hx(sv)} lies below it (fuzz_grant: {gg[0]} globals, highest shadow end {hx(gg[1])} <= {hx(sv)})'),
            KNOWN + ': CZONE 0x800b9c00 = kLowShadowBeg + IMG_TOP / 8 (overrides.tsv reason)')

G_PATCHES = ('g-ACfn.patch', 'g-AD1w.patch', 'g-AD1m.patch', 'g-AD1p.patch', 'g-AD1q.patch', 'g-AD1r.patch',
             'g-AD2f.patch')


def num_tokens(line):
    """the numerals of a line (decimal and hex), as values"""
    return {int(t, 0) for t in re.findall(r'(?<![\w.])(0x[0-9a-fA-F]+|\d+)(?![\w.])', line or '')}


@rule('P-GHUNK', OK, ['UNPAIRED-PORTED', 'UNPAIRED-SOURCE'])
def r_ghunk(d, c):
    """a numeral on a line a G patch added (UNPAIRED-PORTED) or deleted (UNPAIRED-SOURCE), below the image base
    0x10000 (no address of either image), and, for a deleted line, kept with the same value in the line the patch
    wrote in its place (the same sentence with the G names added)"""
    f = d['_f']
    for p in G_PATCHES:
        if f not in c.patched.get(p, ()) or f not in c.gp.get(p, {}):
            continue
        dele, add = c.gp[p][f]
        if d['dst_value'] and not d['src_value']:
            v, line = ival(d['dst_value']), (d['_dl'] or '').rstrip()
            if v is not None and v < 0x10000 and line in add and line not in dele and v in num_tokens(line):
                return ((f'{p} (applied to {f}, patches.log): the dst line is a line the patch added (the G form, '
                         f'records/ghunks/GHUNKS-A-rec3.md), and {d["dst_value"]} = {v} is below the image base '
                         f'0x10000, no address of either image: `{line.strip()[:120]}`'),
                        KNOWN + ': the G patches (harness globals)')
        if d['src_value'] and not d['dst_value']:
            v, line = ival(d['src_value']), (d['_sl'] or '').rstrip()
            if v is None or v >= 0x10000 or line not in dele or v not in num_tokens(line):
                continue
            best = max(add, key=lambda x: difflib.SequenceMatcher(None, line, x).ratio(), default=None)
            if best is not None and v in num_tokens(best) and difflib.SequenceMatcher(None, line, best).ratio() >= 0.8:
                return ((f'{p} (applied to {f}, patches.log): the src line is a line the patch deleted, and the line it '
                         f'wrote in its place keeps {d["src_value"]} = {v} (below the image base 0x10000, no address): '
                         f'`{best.strip()[:120]}`'),
                        KNOWN + ': the G patches (harness globals)')
    return None


NUMTOK = re.compile(r'(?<![\w.])(0x[0-9a-fA-F]+|\d+)(?![\w.])')


@rule('N-IMGSPAN', OK, ['NON-ADDRESS-CHANGED', 'GEOMETRY-CHANGED', 'KIND-CHANGED'])
def r_imgspan(d, c):
    """(added for port_addr_check 205a90fd19b8, whose size-name slot rule flags it) the image span IMG_TOP - IMG_LO of
    each image: src = fuzz_grant's page-up last PT_LOAD end - its first PT_LOAD vaddr, dst = the same of
    fuzz_transport.asan, on a line that adds it to IMG_LO 0x10000 (`0x10000 + SPAN`, the image top)"""
    fx, sv, dv = c.facts, ival(d['src_value']), ival(d['dst_value'])
    sg, sf = fx['Gtop'] - fx['Glo'], fx['Ftop'] - fx['Flo']
    if sv != sg or dv != sf:
        return None
    if not re.search(r'\b%s\s*\+\s*%s\b' % (re.escape(hx(fx['Flo'])), re.escape(d['dst_value'])), d['_dl'] or ''):
        return None
    return ((f'the image span: dst {hx(dv)} = IMG_TOP {hx(fx["Ftop"])} - IMG_LO {hx(fx["Flo"])} (fuzz_transport.asan: '
             f'page-up of its last PT_LOAD end {hx(fx["Flastload"])}, first PT_LOAD vaddr); src {hx(sv)} = '
             f'{hx(fx["Gtop"])} - {hx(fx["Glo"])} (fuzz_grant.asan); the line adds it to IMG_LO: '
             f'`{hx(fx["Flo"])} + {d["dst_value"]}` = the image top, an image size that moves with the image'),
            KNOWN + ': the image span (205a90fd19b8 size-name slot)')


@rule('P-LINEPAIR', OK, ['UNPAIRED-PORTED', 'UNPAIRED-SOURCE'])
def r_linepair(d, c):
    """(added for the run of record) a numeral on a line no patch changed, in a file a patch of the run changed, that
    the checker leaves unpaired because the patch changed the sentence before it (its sentence alignment then misses
    the line). Paired by line instead: port_core's provenance line under the notice block puts donor line L at
    stage-out line L + 1; the two lines must be the same text with every numeral masked, the numeral is taken at the
    same position, and the two values must name the same symbol + offset in their own images (twin symtabs)."""
    f = d['_f']
    pats = [p for p in PATCHES if f in c.patched.get(p, ())]
    if not pats:
        return None
    if d['src_value'] and not d['dst_value']:
        sl, dl, v = (d['_sl'] or ''), (c.so.line(f, ival(d['src_line']) + 1) or ''), ival(d['src_value'])
        side = 'src'
    elif d['dst_value'] and not d['src_value']:
        sl, dl, v = (c.st.line(f, ival(d['dst_line']) - 1) or ''), (d['_dl'] or ''), ival(d['dst_value'])
        side = 'dst'
    else:
        return None
    for p in pats:
        dele, add = c.allp.get(p, {}).get(f, (set(), set()))
        if sl.rstrip() in dele or dl.rstrip() in add:
            return None
    if not sl or not dl or NUMTOK.sub('#', sl) != NUMTOK.sub('#', dl):
        return None
    st, dt = [int(x, 0) for x in NUMTOK.findall(sl)], [int(x, 0) for x in NUMTOK.findall(dl)]
    mine = st if side == 'src' else dt
    if v not in mine:
        return None
    k = mine.index(v)
    sv, dv = st[k], dt[k]
    shared = {(x[1], x[2]) for x in c.G.labels(sv) if x[0] == 'at'} & {(x[1], x[2]) for x in c.F.labels(dv) if x[0] == 'at'}
    if not shared:
        return None
    n, off = sorted(shared)[0]
    return ((f'the line pairs by line ({", ".join(pats)} changed {f}, not this line): donor line {d["src_line"] or ival(d["dst_line"]) - 1} '
             f'and stage-out line {ival(d["src_line"]) + 1 if d["src_line"] else d["dst_line"]} are the same text with the '
             f'numerals masked; at the same position the donor holds {hx(sv)} and the port {hx(dv)}, each {n}+{hx(off)} in its '
             f'own image; the checker leaves the pair unpaired because the patch changed the sentence before it'),
            KNOWN + ': lines next to a patch, paired by line')



def zsh_values(lo, hi):
    """the quantities a lemma over the zero-shadow piece [lo, hi) states: its ends, lo + 0x20, and their quotients by 8"""
    return {lo: 'the piece\'s start', hi: 'the piece\'s end', lo + 0x20: 'the piece\'s start + 0x20',
            lo // 8: 'start / 8', (lo + 0x20) // 8: '(start + 0x20) / 8', (hi - lo) // 8: '(end - start) / 8'}


@rule('P-BSSZR', OK, ['DIFFERENT-SYMBOL', 'NON-ADDRESS-CHANGED', 'GEOMETRY-CHANGED', 'KIND-CHANGED'])
def r_bsszr(d, c):
    fx, f, dv = c.facts, d['_f'], ival(d['dst_value'])
    if f not in c.bz or f not in c.patched.get('bss-zero-range.patch', ()):
        return None
    dl = (d['_dl'] or '').rstrip()
    if dl not in c.bz[f][1]:
        return None
    # the pieces the patch names in this file (an end of the piece written in an added line, `(lo, hi - lo)` form)
    added = '\n'.join(c.bz[f][1])
    named = [(lo, hi) for lo, hi in fx['su_zsh'] if f'({hx(lo)}, {hx(hi)} - {hx(lo)})' in added]
    hits = [(lo, hi) for lo, hi in named if dv in zsh_values(lo, hi)]
    if len(hits) != 1:
        return None
    lo, hi = hits[0]
    return ((f'bss-zero-range.patch (applied to {f}, patches.log): the dst line is a line the patch added; dst '
             f'{hx(dv)} = {dv} is {zsh_values(lo, hi)[dv]} of the zero-shadow piece [{hx(lo)}, {hx(hi)}) that the patch '
             f'writes in {f} as `({hx(lo)}, {hx(hi)} - {hx(lo)})`, an entry of LIB/A/AF0m.v Tfib_zero_shadow '
             f'({len(fx["su_zsh"])} pieces). The donor\'s lemma takes one range over the whole .bss after asan_globals, '
             f'which this image\'s list does not hold (its instrumented harness globals cut it); the lemma takes the '
             f'piece its consumer needs'),
            KNOWN + ': A/AD1o.v / A/AD25.v zero-shadow pieces (bss-zero-range.patch)')


def mapflags(v):
    rem, names = v, []
    for b, n in MAP_BITS:
        if rem & b:
            names.append(n)
            rem &= ~b
    return names, rem


@rule('SDCP-SIZE', TOOL, ['STALE-DONOR-CODE-POINTER'])
def r_sizelui(d, c):
    sv, dv = ival(d['src_value']), ival(d['dst_value'])
    if not (sv is not None and sv == dv and sv % 0x1000 == 0 and sv < 1 << 31):
        return None
    reg = re.compile(r'(?:(\d+)%bv = SLit ' + str(sv) + r'\b|(\d+)%bv \(SLit ' + str(sv) + r'\))')
    ms, md = reg.search(d['_sl'] or ''), reg.search(d['_dl'] or '')
    if not (ms and md):
        return None
    r_s = int(ms.group(1) or ms.group(2))
    # the proof's own names of the value: the size constants of Reusable/YG00.v, equal in stage and stage-out
    names = [n for n, v in re.findall(r'Definition (\w+) : Z := (\d+)\.', c.so.text('Reusable/YG00.v') or '')
             if int(v) == sv and defval(c.st.text('Reusable/YG00.v'), n) == sv]
    if not names:
        return None
    imm = sv >> 12
    gs = {(f[0], a - f[1], rd) for a, rd, f in c.G.lui_sites(imm) if f}
    fs = {(f[0], a - f[1], rd) for a, rd, f in c.F.lui_sites(imm) if f}
    both = sorted(gs & fs)
    if not both:
        return None
    pm = re.search(r'pin \(runto (0x[0-9a-f]+) \w+\) (\d+)%bv \(SLit ' + str(sv) + r'\)', d['_sl'] or '')
    pd = re.search(r'pin \(runto (0x[0-9a-f]+) \w+\) (\d+)%bv \(SLit ' + str(dv) + r'\)', d['_dl'] or '')
    if pm or pd:
        if not (pm and pd and pm.group(2) == pd.group(2)):
            return None
        gpc, fpc, rp = int(pm.group(1), 16), int(pd.group(1), 16), int(pm.group(2))
        gf, ff = c.G.func_at(gpc), c.F.func_at(fpc)
        if not (gf and ff and gf[0] == ff[0] and gf[2] == ff[2] and gpc - gf[1] == fpc - ff[1]):
            return None
        off = gpc - gf[1]
        hit = [(n, o, rd) for n, o, rd in both if n == gf[0] and o < off]
        if not hit:
            return None
        # the function's instruction words from its start to the pc: equal in both images except the immediates of
        # auipc / jal (pc-relative: they differ by the code shift)
        ws = [int.from_bytes(c.G.read(gf[1] + i, 4), 'little') for i in range(0, off, 4)]
        wd = [int.from_bytes(c.F.read(ff[1] + i, 4), 'little') for i in range(0, off, 4)]
        diff = [i * 4 for i, (x, y) in enumerate(zip(ws, wd)) if x != y and not (x & 0x7f == y & 0x7f and x & 0x7f in
                                                                                (0x17, 0x6f) and (x ^ y) & 0xfff == 0)]
        if diff:
            return None
        direct = [h for h in hit if h[2] == rp]
        how = (f'written by `lui x{rp}, {hx(imm)}` at +{hx(direct[0][1])}' if direct else
               f'a length the function computes from the constant it forms with `lui x{hit[0][2]}, {hx(imm)}` at '
               f'+{hx(hit[0][1])}')
        role = (f'the pinned register x{rp} at runto {pm.group(1)} (src) / {pd.group(1)} (dst) = {gf[0]}+{hx(off)} in '
                f'both (same size {gf[2]}; its {off // 4} instruction words before the pc are equal in both images '
                f'except auipc / jal immediates): {how}')
    elif r_s == 11:
        # the sentence states an ecall state: a7 = 222 (__NR_mmap, riscv64 generic table), a1 = the length
        regs = []
        for tree, f, n in ((c.st, d['src_file'], d['src_line']), (c.so, d['dst_file'], d['dst_line'])):
            L, n = tree.lines(f) or [], ival(n)
            st = re.search(r'ss_regs (\w+)\) 11%bv = SLit ' + str(sv) + r'\b', L[n - 1] if 0 < n <= len(L) else '')
            if not st:
                return None
            win = '\n'.join(L[max(0, n - 5): n + 4])
            rv = {}
            for k in (10, 12, 13, 14, 15, 17):
                m = re.search(r'ss_regs ' + st.group(1) + r'\) ' + str(k) + r'%bv = (SLit (0x[0-9a-f]+|\d+)|SOff \w+ 0|\w+)',
                              win)
                rv[k] = (ival(m.group(2)) if m.group(2) else m.group(1)) if m else None
            regs.append(rv)
        if regs[0] != regs[1]:
            return None
        rv = regs[1]
        fn, frem = mapflags(rv[13]) if isinstance(rv[13], int) else ([], 1)
        if not (rv[17] == 222 and rv[12] in (0, 1, 3) and not frem and 'MAP_PRIVATE' in fn and 'MAP_ANONYMOUS' in fn):
            return None
        role = (f'the sentence states an ecall state with x17 (a7) = 222 = __NR_mmap (riscv64 generic syscall table), '
                f'x10 (a0) = {rv[10]} (addr), x11 (a1) = {sv} (the LENGTH), x12 (a2) = {rv[12]} (prot), x13 (a3) = '
                f'{hx(rv[13])} = {" | ".join(fn)} (flags), x14 = {rv[14]} (fd), x15 = {rv[15]} (offset); the same in '
                f'stage and stage-out')
    else:
        return None
    sites = '; '.join(f'{n}+{hx(o)} `lui x{rd}, {hx(imm)}`' for n, o, rd in both if 'SizeClassAllocator64' in n) or \
        '; '.join(f'{n}+{hx(o)} `lui x{rd}, {hx(imm)}`' for n, o, rd in both[:3])
    gsrc = ', '.join(f'{n}+{hx(sv - v)}' for n, v, sz in c.G.at(sv))
    return (f'a SIZE, not a code address: {sv} = {hx(sv)} = {" = ".join(names)} (Reusable/YG00.v, stage and '
            f'stage-out), in a register value (`{ms.group(0)}`): {role}. Both images form {hx(sv)} with `lui` at the '
            f'same function offsets ({len(both)} shared sites; the allocator\'s: {sites}). That {hx(sv)} also lies '
            f'inside fuzz_grant\'s {gsrc} is a coincidence; the checker reads it as that code pointer and expects '
            f'{note_expected(d)} (0d24592683b6 change (2): a value inside a named symbol is no round constant)')


def ab1w_label(d, c):
    """the AB1w row tfib_[AE]_<label>: src and dst name the same symbol + offset (A) or the same end (E) in their own
    images; returns (detail) or None."""
    if d['_f'] != 'A/AB1w.v':
        return None
    ae, x = tname(d)
    if not ae:
        return None
    sv, dv = ival(d['src_value']), ival(d['dst_value'])
    ls, ld = c.G.labels(sv), c.F.labels(dv)
    common = {l for l in ls & ld if l[0] == 'at'} if ae == 'A' else (ls & ld)
    if ae == 'A':
        common = {l for l in common if c.G.sym(l[1]) and c.F.sym(l[1])}
    if not common:
        return None
    own = []
    for side, I, v in (('fuzz_grant', c.G, sv), ('fuzz_transport', c.F, dv)):
        s = tfib_sym(I, x)
        if s:
            val = s[1][0] if ae == 'A' else s[1][0] + s[1][1]
            if val == v:
                return None   # the label IS the symbol on one side: not a label row
            own.append(f'{side}\'s own `{s[0]}` {"starts" if ae == "A" else "ends"} at {hx(val)}')
        else:
            own.append(f'{side} has no symbol `{x}` / `_{x}` / `__{x}`')
    carried = 'copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v' in (c.st.text('A/AB1w.v') or '')
    return (f'src {hx(sv)} = {lab(ls & ld)} in fuzz_grant, dst {hx(dv)} = the same in fuzz_transport (both unstripped '
            f'symtabs; all labels src: {lab(ls)}; dst: {lab(ld)}). The row name `{x}` is a label the released donor '
            f'carries' + (' from cgif_file_fuzzer\'s AB1w (stage/A/AB1w.v notice: `copied from '
                          'proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v`)' if carried else '') + ': '
            + '; '.join(own) + ', so the donor row names the same object the port row names')


@rule('DS-AB1W-LABEL', TOOL, ['DIFFERENT-SYMBOL'])
def r_ab1w_ds(d, c):
    r = ab1w_label(d, c)
    if not r:
        return None
    return r + (f'. The named-symbol rule (0d24592683b6 change (3), absolute on an own symtab) reads the label as a '
                f'symbol name and expects {note_expected(d)}, the label-named symbol of fuzz_transport, which is not the '
                f'object the donor row names')


@rule('UM-AB1W-LABEL', OK, [UMN])
def r_ab1w_um(d, c):
    return ab1w_label(d, c)


def dropped_row(d, c):
    """common part of the AB1w dropped-row rules: the name, its src value by role, its absence in dst."""
    ae, x = tname(d)
    if not ae:
        return None
    gs = tfib_sym(c.G, x)
    if not gs:
        return None
    n, (v, sz) = gs
    sv = ival(d['src_value'])
    if sv != (v if ae == 'A' else v + sz):
        return None
    if tfib_sym(c.F, x):
        return None
    dl = c.so.line(d['_f'], ival(d['src_line']) + 1) or ''
    if re.search(r'\btfib_[AE]_' + re.escape(x) + r'\b', dl):
        return None
    use = c.uses('tfib_A_' + x) + c.uses('tfib_E_' + x)
    if use:
        return None
    role = f'{n}+0x0 (size {hx(sz)})' if ae == 'A' else f'end of {n} ({hx(v)} + {hx(sz)})'
    return n, role, dl


@rule('S-GRANTPROG', OK, ['UNPAIRED-SOURCE'])
def r_grantprog(d, c):
    fx = c.facts
    if d['_f'] != 'A/AB1w.v' or not fx['Gprog']:
        return None
    r = dropped_row(d, c)
    if not r:
        return None
    n, role, dl = r
    v = c.G.sym(n)[0]
    if not (fx['Gprog'][0] <= v < fx['Gprog'][1]):
        return None
    return (f'src {role}, a function of fuzz_grant\'s program range [{hx(fx["Gprog"][0])}, {hx(fx["Gprog"][1])}) '
            f'(LLVMFuzzerTestOneInput .. __wrap_getenv); the dst symtab has no {n}; dst line {ival(d["src_line"]) + 1} '
            f'{"is blank" if not dl.strip() else "holds no row of it"}; no file of stage-out or of LIB uses '
            f'tfib_A_/tfib_E_ of it')


@rule('P-TRANSPROG', OK, ['UNPAIRED-PORTED'])
def r_transprog(d, c):
    fx = c.facts
    if d['_f'] != 'A/AB1w.v' or not fx['Fprog']:
        return None
    ae, x = tname(d)
    if not ae:
        return None
    fs = tfib_sym(c.F, x)
    if not fs or tfib_sym(c.G, x):
        return None
    n, (v, sz) = fs
    dv = ival(d['dst_value'])
    if not (fx['Fprog'][0] <= v < fx['Fprog'][1] and dv == (v if ae == 'A' else v + sz)):
        return None
    fns = c.F.funcs(*fx['Fprog'])
    cov = [nm for (vv, nm, s) in fns if fx['dst_ab1w'].get(nm.replace('.', '_')) == vv]
    miss = [nm for (vv, nm, s) in fns if nm not in cov]
    role = f'{n}+0x0 (size {hx(sz)})' if ae == 'A' else f'end of {n} ({hx(v)} + {hx(sz)})'
    return (f'dst {role}, one of fuzz_transport\'s own program functions (range [{hx(fx["Fprog"][0])}, '
            f'{hx(fx["Fprog"][1])}) = LLVMFuzzerTestOneInput .. __wrap_getenv); fuzz_grant has no {n}; written on dst '
            f'line {d["dst_line"]}. The dst AB1w table holds a tfib_A_ row with the symtab start for {len(cov)} of the '
            f'{len(fns)} functions of that range{"; missing: " + ", ".join(miss) if miss else ""}')


@rule('P-SMCLASS', OK, ['UNPAIRED-PORTED'])
def r_smclass(d, c):
    fx = c.facts
    m = re.match(r'Definition tfib_([AE])_asan_stack_malloc_(\d+)$', d['sentence'])
    if d['_f'] != 'A/AB1w.v' or not m:
        return None
    k = int(m.group(2))
    if k in fx['Gsm'] or k not in fx['Fsm']:
        return None
    v, sz = c.F.sym('__asan_stack_malloc_%d' % k)
    dv = ival(d['dst_value'])
    if dv != (v if m.group(1) == 'A' else v + sz):
        return None
    return (f'dst {"start" if m.group(1) == "A" else "end"} of __asan_stack_malloc_{k} ({hx(v)} + {hx(sz)}): '
            f'fuzz_transport.asan links classes {"/".join(map(str, sorted(fx["Fsm"])))}, fuzz_grant '
            f'{"/".join(map(str, sorted(fx["Gsm"])))}; the port added the row of the class the donor lacks')


@rule('P-AF0L', OK, ['UNPAIRED-PORTED'])
def r_af0l(d, c):
    fx = c.facts
    if d['_f'] != 'A/AF0l.v' or 'pc_stack_malloc' not in (d['_dl'] or ''):
        return None
    da, sa = arms(d['_dl']), arms(c.st.line(d['_f'], ival(d['dst_line']) - 1))
    if da != fx['Fsm'] or sa != fx['Gsm']:
        return None
    new = set(da) - set(sa)
    dv = ival(d['dst_value'])
    hit = [k for k in new if dv in (k, da[k])]
    if not hit:
        return None
    k = hit[0]
    return (f'Tfib_code pc_stack_malloc: the dst arms {{{", ".join(f"{i}: {hx(v)}" for i, v in sorted(da.items()))}}} '
            f'are fuzz_transport\'s __asan_stack_malloc_N starts (its symtab), the src arms (stage line '
            f'{ival(d["dst_line"]) - 1}) {{{", ".join(f"{i}: {hx(v)}" for i, v in sorted(sa.items()))}}} fuzz_grant\'s; '
            f'this row is the {"key" if dv == k else "value"} of the class-{k} arm, which fuzz_grant has no symbol for')


@rule('PATCH-ZS', OK, ['UNPAIRED-SOURCE', 'UNPAIRED-PORTED'])
def r_zs(d, c):
    f, v = d['_f'], ival(d['src_value'] or d['dst_value'])
    if f not in c.zs or f not in c.patched.get('zero-shadow-forallb.patch', ()) or v not in (0, 8) or d['kind'] != 'dec':
        return None
    dl, al = c.zs[f]
    if d['verdict'] == 'UNPAIRED-SOURCE':
        t, side = (d['_sl'] or '').rstrip(), 'deleted'
        ok = t in dl
    else:
        t, side = (d['_dl'] or '').rstrip(), 'added'
        ok = t in al
    if not ok or not re.search(r'(?<![\w.])%d(?![\w.])' % v, t):
        return None
    return (f'zero-shadow-forallb.patch (applied to {f}, patches.log): the {"src" if side == "deleted" else "dst"} line '
            f'is a line the patch {side}; the value {v} is a literal {"8 (shadow granule)" if v == 8 else "0 (remainder)"} '
            f'of that line, not an address. The patch replaces the Tfib_zero_shadow case split by a forallb check')


@rule('PATCH-DEADARM', OK, ['UNPAIRED-SOURCE'])
def r_deadarm(d, c):
    fx, f, sv = c.facts, d['_f'], ival(d['src_value'])
    if f not in c.da or f not in c.patched.get('dead-arm-ad1g.patch', ()):
        return None
    dl, al = c.da[f]
    sl = (d['_sl'] or '').rstrip()
    m = re.search(r'apply Z_mod_mult \|\| \(change (\d+) with \((\d+) \* (\d+)\); apply Z_mod_mult\)', sl)
    if not m:
        return None
    gv, q, p = (int(x) for x in m.groups())
    span_g, span_f = fx['Gtop'] - fx['Glo'], fx['Ftop'] - fx['Flo']
    dele = [x for x in dl if x.replace(str(span_f), str(span_g)) == sl]
    dstl = (c.so.line(f, ival(d['src_line']) + 1) or '').rstrip()
    if not (gv == span_g and sv in (gv, q, p) and dele and dstl in al and q * p != gv):
        return None
    return ((f'dead-arm-ad1g.patch (applied to {f}, patches.log): the src line is the patch\'s deleted line with the '
             f'image span written for fuzz_grant ({gv} = {hx(gv)} = IMG_TOP {hx(fx["Gtop"])} - IMG_LO {hx(fx["Glo"])}; '
             f'the deleted line holds {span_f} = {hx(span_f)} = {hx(fx["Ftop"])} - {hx(fx["Flo"])}), and the dst line '
             f'(src line + 1) is its added line. The arm `|| (change {gv} with ({q} * {p}); apply Z_mod_mult)` is dead: '
             f'{q} * {p} = {q * p} != {gv}, so the change fails and only the first `apply Z_mod_mult` closes the goal, '
             f'in the donor as in the port; this row is the {"span" if sv == gv else "factor"} {sv} of that arm'),
            KNOWN + ': the dead arm removed from A/AD1g.v')


@rule('N-REGCNT', OK, ['NON-ADDRESS-CHANGED', FILL])
def r_regcnt(d, c):
    fx, sv, dv = c.facts, ival(d['src_value']), ival(d['dst_value'])
    dn, un = fx['dn_regions'], fx['su_regions']
    if not dn or not un or sv is None or dv is None or sv >= 0x40:
        return None

    def fb(rs):
        return (next((i for i, r in enumerate(rs) if r.startswith('R_A5a')), None),
                rs.index('R_A7b') if 'R_A7b' in rs else None)
    (fd, bd), (fu, bu), Nd, Nu = fb(dn), fb(un), len(dn), len(un)
    cand = {}
    if sv - Nd in range(7):
        cand['count N + %d' % (sv - Nd)] = Nu + sv - Nd
    if None not in (fd, bd, fu, bu):
        for k, w in ((fd, fu), (fd + 1, fu + 1), (bd + 1, bu + 1), (bd - fd - 1, bu - fu - 1)):
            if sv == k:
                cand['index %d' % k] = w
    hit = [k for k, w in cand.items() if w == dv]
    if not hit:
        return None
    return ((f'region {hit[0]} of IMG_REGIONS: donor A/AD2j.v N {Nd} (R_A5a at {fd}, R_A7b at {bd}), start-up '
             f'LIB/A/AD2j.v N {Nu} (R_A5a_1 at {fu}, R_A7b at {bu}): {sv} -> {dv}'),
            KNOWN + ': IMG_E / IMG_B / PM_tailL and the other region counts depend on the stand-in AD2j region count')


# ---------------------------------------------------------------- the extra check: AB1w auxv/geometry rows

def geometry_check(c):
    """the AB1w tfib_at_* rows that restate image geometry, against both images (rows the flag set may not flag)."""
    out = []
    want = {}
    for k, I in (('F', c.F), ('G', c.G)):
        rw_lo = I.loads[-1][1] // 0x1000 * 0x1000
        want[k] = {'tfib_at_img_lo': I.loads[0][1] // 0x1000 * 0x1000, 'tfib_at_img_hi': I.top(),
                   'tfib_at_a_entry': I.entry, 'tfib_at_rw_lo': rw_lo, 'tfib_at_rw_len': I.top() - rw_lo,
                   'tfib_at_ph_addr_z': (I.pt('PT_PHDR') or (0, None))[1], 'tfib_at_ph_ent_z': I.phentsize,
                   'tfib_at_ph_num_z': I.phnum}
    td, ts = c.so.text('A/AB1w.v') or '', c.st.text('A/AB1w.v') or ''
    for nm in want['F']:
        rx = r'Definition ' + nm + r'\s*:\s*Z\s*:=\s*' + NUM_RE + r'\s*\.'
        m, ms = re.search(rx, td), re.search(rx, ts)
        ln = td[:m.start()].count('\n') + 1 if m else None
        out.append(dict(name=nm, line=ln, v=ival(m.group(1)) if m else None, want=want['F'][nm],
                        sline=ts[:ms.start()].count('\n') + 1 if ms else None, sv=ival(ms.group(1)) if ms else None,
                        swant=want['G'][nm], verdict=c.gate_ab1w.get(ln, 'no gate row')))
    for g in out:
        g['ok'] = g['v'] == g['want']
    return out


def region_layout(c, rows):
    """the IMG_REGIONS layout (N, R_A5a index, R_A7b index) that the region counts of stage-out follow."""
    def nfb(rs):
        if not rs:
            return None
        return (len(rs), next((i for i, r in enumerate(rs) if r.startswith('R_A5a')), None),
                rs.index('R_A7b') if 'R_A7b' in rs else None)
    fx = c.facts
    d, u = nfb(fx['dn_regions']), nfb(fx['su_regions'])
    nreg = sum(1 for r in rows if r['reason'] == 'N-REGCNT')
    if d is None:
        st = 'no donor list'
    elif u is None:
        st = 'needs LIB/A/AD2j.v'
    elif u == d:
        st = 'same layout'
    elif nreg:
        st = 'recomputed'
    else:
        st = 'DEFECT'
    return dict(status=st, donor=d, unit=u, nreg=nreg)


# ---------------------------------------------------------------- main

def read_log(path):
    txt = open(path, errors='replace').read().split('\n')
    flagged = next((l for l in txt if l.startswith('FLAGGED ')), None)
    fc = next((l for l in txt if l.startswith('FLAG-CLASSES ')), None)
    um = next((l for l in txt if l.startswith('UNMEASURED ') and ' rows in ' in l), None)
    i = next((k for k, l in enumerate(txt) if re.match(r'checker \S+ rc=\d+', l)), None)
    rc = txt[i] if i is not None else None
    classes = {l.strip() for l in txt[i + 1:] if re.fullmatch(r'[A-Z][A-Z-]+', l.strip())} if i is not None else set()
    counts = dict(re.findall(r'([A-Z][A-Z-]+)=(\d+)', flagged.split(':', 1)[1])) if flagged and ':' in flagged else {}
    return classes, flagged, fc, rc, um, {k: int(v) for k, v in counts.items()}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    for o in ('raw', 'log', 'run', 'lib', 'overrides', 'evidence', 'src-image', 'dst-image', 'donor-lib', 'out'):
        ap.add_argument('--' + o, required=True)
    ap.add_argument('--stage')
    ap.add_argument('--stage-out')
    ap.add_argument('--md')
    ap.add_argument('--controls', help='flag-gate.txt of flag-gate-A.sh, embedded in the --md record')
    a = ap.parse_args()
    classes, flagged_line, fc_line, rc_line, um_line, counts = read_log(a.log)
    if not classes:
        sys.exit(f'no flag classes in {a.log} (pac-A.sh appends --list-flag-classes)')
    c = Ctx(a)
    compute_facts(c)
    rows, hdr = [], None
    c.gate_ab1w = {}
    for i, ln in enumerate(open(a.raw, errors='replace'), 1):
        if ln.startswith('#'):
            continue
        r = ln.rstrip('\n').split('\t')
        if hdr is None:
            hdr = r
            continue
        d = dict(zip(hdr, r))
        if d['dst_file'] == 'A/AB1w.v' and d['dst_line'].isdigit():
            c.gate_ab1w.setdefault(int(d['dst_line']), d['verdict'])
        if d['verdict'] in classes or d['verdict'] in (FILL, UMN):
            d['raw_line'] = i
            d['_f'] = d['src_file'] or d['dst_file']
            d['_sl'] = c.st.line(d['src_file'], d['src_line']) if d['src_file'] else None
            d['_dl'] = c.so.line(d['dst_file'], d['dst_line']) if d['dst_file'] else None
            rows.append(d)
    for d in rows:
        d['reason'], d['detail'], d['known'], d['class'] = 'UNEXPLAINED', '', '', ''
        for rid, vs, fn in RULES:
            if d['verdict'] not in vs:
                continue
            try:
                r = fn(d, c)
            except (TypeError, KeyError, IndexError, ValueError, AttributeError) as e:
                r = None
                d['_err'] = f'{rid}: {type(e).__name__} {e}'
            if r:
                det, known = r if isinstance(r, tuple) else (r, '')
                d['reason'], d['detail'], d['known'], d['class'] = rid, det, known, RCLASS[rid]
                break
        sv = ival(d['src_value'])
        # override cross-check: an override row on this donor line and value must have written exactly this dst value,
        # unless port_core reports the row `removed by --patch` (WORK/overrides.tsv) and bss-zero-range.patch explains the
        # line the patch wrote (rule P-BSSZR; no other rule may then explain the row)
        for old, new, ln in c.ovr.get((d['src_file'], ival(d['src_line']) or -1), []):
            if old == sv:
                if ival(d['dst_value']) == new:
                    d['detail'] += f'; {c.ovr_name} line {ln}: {hx(old)} -> {hx(new)} (dst = the override value)'
                else:
                    st = c.ovst.get((d['src_file'], ival(d['src_line']), old, new), '')
                    try:
                        r = r_bsszr(d, c) if st.startswith('removed by --patch') else None
                    except (TypeError, KeyError, IndexError, ValueError, AttributeError):
                        r = None
                    if r:
                        d['reason'], d['known'], d['class'] = 'P-BSSZR', r[1], RCLASS['P-BSSZR']
                        d['detail'] = (r[0] + f'; {c.ovr_name} line {ln} ({hx(old)} -> {hx(new)}) is `{st}` in '
                                       f'WORK/overrides.tsv: the patch rewrote the line the override wrote')
                    else:
                        d['reason'], d['class'] = 'UNEXPLAINED', ''
                        d['detail'] = f'{c.ovr_name} line {ln} writes {hx(new)}, dst holds {d["dst_value"]}'
                break
        if d['reason'] != 'UNEXPLAINED' and d['src_file']:
            dec = c.decision(d['src_file'], d['src_line'], sv)
            if dec:
                d['detail'] += f'; port_core: {dec}'
        if d['reason'] == 'UNEXPLAINED':
            d['detail'] = (d['detail'] or 'no rule accepts this row') + f' | checker note: {d["note"][:200]}' + (
                f' | {d["_err"]}' if d.get('_err') else '')
    cols = ['raw_line', 'verdict', 'src_file', 'src_line', 'dst_line', 'sentence', 'idx', 'kind', 'src_value',
            'dst_value', 'reason', 'class', 'known', 'detail']
    with open(a.out, 'w') as fh:
        fh.write('\t'.join(cols) + '\n')
        for d in rows:
            dd = dict(d, src_file=d['_f'])
            fh.write('\t'.join(str(dd[k]).replace('\t', ' ') for k in cols) + '\n')
    fl = [d for d in rows if d['verdict'] not in (FILL, UMN)]
    fill = [d for d in rows if d['verdict'] == FILL]
    um = [d for d in rows if d['verdict'] == UMN]
    got = collections.Counter(d['verdict'] for d in fl)
    bad = [d for d in rows if d['reason'] == 'UNEXPLAINED']
    badf = [d for d in fl + fill if d['reason'] == 'UNEXPLAINED']
    badu = [d for d in um if d['reason'] == 'UNEXPLAINED']
    match = dict(got) == counts
    geo = geometry_check(c)
    reg = region_layout(c, rows)
    cls = collections.Counter(d['class'] or 'UNEXPLAINED' for d in fl + fill)
    print(f'{len(fl)} flagged rows + {len(fill)} {FILL}: {len(fl) + len(fill) - len(badf)} explained, {len(badf)} '
          f'UNEXPLAINED -> {a.out}')
    print(f'{len(um)} {UMN} rows (reported, measured by nothing): {len(um) - len(badu)} explained, {len(badu)} UNEXPLAINED')
    print(f'per class {dict(sorted(got.items()))}; FLAGGED line {"matches" if match else "DIFFERS: " + str(counts)}')
    print(f'classification of the flagged + {FILL} rows: {OK} {cls.get(OK, 0)}, {TOOL} {cls.get(TOOL, 0)}, '
          f'{REAL} {cls.get(REAL, 0)}, UNEXPLAINED {cls.get("UNEXPLAINED", 0)}')
    print('reasons', dict(sorted(collections.Counter(d['reason'] for d in rows).items())))
    for d in bad:
        print(f'UNEXPLAINED raw {d["raw_line"]} {d["verdict"]} {d["_f"]}:{d["src_line"] or "-"}->{d["dst_line"] or "-"} '
              f'{d["src_value"]} -> {d["dst_value"]}: {d["detail"][:240]}')
    for g in geo:
        if not g['ok']:
            print(f'UNFLAGGED-DEFECT stage-out/A/AB1w.v:{g["line"]} {g["name"]} = {hx(g["v"])}, the dst image gives '
                  f'{hx(g["want"])} (checker verdict {g["verdict"]})')
    print(f'region layout (N, R_A5a, R_A7b): donor {reg["donor"]}, unit {reg["unit"]} (LIB/A/AD2j.v), N-REGCNT rows '
          f'{reg["nreg"]}: {reg["status"]}')
    if a.md:
        write_md(a, c, rows, flagged_line, fc_line, rc_line, um_line, counts, match, geo, reg)
    sys.exit(1 if bad or not match else 0)


# ---------------------------------------------------------------- the record

DESC = {
    'G-6128': lambda fx: (f'6128 = kPage {fx["kPage"]} + kSecRz {fx["kSecRz"]} - kChunkHeaderSize {fx["kChunkHeaderSize"]} '
                          f'(stage/Reusable/YG00.v): the chunk header offset from the runtime mmap base aMAP (`SOff aMAP '
                          f'6128`, `hdr = MAP + 6128`), not an image quantity. The checker reads it as the donor distance '
                          f'load2.memhi - .got.lo ({hx(fx["Gload2hi"])} - {hx(fx["Ggot"])} = 0x17f0, a coincidence) and '
                          f'expects fuzz_transport\'s {hx(fx["Fload2hi"] - fx["Fgot"])}, which has no role here.'),
    'K-TLS': lambda fx: (f'tls.lo = PT_TLS p_vaddr: src {hx(fx["Gtls"])} (.text.hi {hx(fx["Gtext"][1])} + pad), dst '
                         f'{hx(fx["Ftls"])}. In dst .text.hi = tls.lo = load1.memhi = {hx(fx["Ftls"])}, so the checker '
                         f'reads the value as an image extent.'),
    'FMTWIN': lambda fx: ('driver format-string shadow window [SH_LO, SH_HI): SH_LO = floor8(0x7fff8000 + fmt/8), SH_HI = '
                          'floor8(0x7fff8000 + (fmt+len)/8) + 8, each side from its own image\'s string at `Definition FMT` '
                          'of the file (bytes read from the image, equal on both sides). The checker names a shadow '
                          'address only where an object starts in the 8 bytes it covers.'),
    'N-FMTPTR': lambda fx: ('decimal pointer into a driver format string (a position of the vfprintf walk). Same string, '
                            'same offset in both images; the string start is checked in the image bytes (NUL before it, '
                            'bytes equal). The checker classes a decimal that is not a symbol start as non-address, so '
                            'every moved one is flagged.'),
    'GF-FMTPTR': lambda fx: ('GENERATOR-FILL row: the same string + offset in both images (as N-FMTPTR), and the donor '
                             'line holds the same value as often as the dst line, so the duplicate is the donor\'s.'),
    'N-AD1o-BSS20': lambda fx: (f'(.bss.lo + 0x20) / 8: dst ({hx(fx["Fbss"])} + 0x20) / 8 = {(fx["Fbss"] + 0x20) // 8} '
                                f'(src ({hx(fx["Gbss"])} + 0x20) / 8 = {(fx["Gbss"] + 0x20) // 8}).'),
    'N-AD1o-TOP': lambda fx: (f'(IMG_TOP - 1) / 8: dst ({hx(fx["Ftop"])} - 1) / 8 = {(fx["Ftop"] - 1) // 8} (src '
                              f'({hx(fx["Gtop"])} - 1) / 8 = {(fx["Gtop"] - 1) // 8}); the start-up LIB/A/AB13.v TFIB_BSS '
                              f'gives the same top.'),
    'N-AD1o-ZLEN': lambda fx: (f'(IMG_TOP - TFIB_BSS.lo) / 8 with TFIB_BSS.lo = __stop_asan_globals: dst ({hx(fx["Ftop"])} '
                               f'- {hx(fx["Fstop"])}) / 8 = {(fx["Ftop"] - fx["Fstop"]) // 8} (src '
                               f'{(fx["Gtop"] - fx["Gstop"]) // 8}); start-up LIB/A/AB13.v TFIB_BSS checked.'),
    'N-RA3': lambda fx: 'R_A3 length: [oft_arg0, __start_asan_globals) of each image, checked against LIB/A/AD2j.v.',
    'N-DEPOT': lambda fx: (f'witness TFIB_DEPOT / 4: dst {fx["Fdepot"][0]} = {hx(fx["Fdepot"][1])}, / 4 = '
                           f'{fx["Fdepot"][1] // 4}; src {hx(fx["Gdepot"][1])} / 4 = {fx["Gdepot"][1] // 4}. TFIB_DEPOT is '
                           f'the start-up LIB/A/AF0m.v\'s.'),
    'N-IAL': lambda fx: (f'witness of (P + 8k) mod 8 = 0 with P = TFIB_IAL_LO = internal_alloc_placeholder: dst '
                         f'{hx(fx["Fial"][1])} / 8 = {fx["Fial"][1] // 8}; src {hx(fx["Gial"][1])} / 8 = '
                         f'{fx["Gial"][1] // 8}. TFIB_IAL_LO is the start-up LIB/A/AF0m.v\'s.'),
    'N-INST': lambda fx: (f'(TFIB_INST + 168) / 8 with TFIB_INST = __asan::instance: dst ({hx(fx["Finst"][1])} + 168) / 8 '
                          f'= {(fx["Finst"][1] + 168) // 8}; src ({hx(fx["Ginst"][1])} + 168) / 8 = '
                          f'{(fx["Ginst"][1] + 168) // 8}. TFIB_INST is the start-up LIB/A/AF0m.v\'s.'),
    'N-CELLPATCH': lambda fx: ('cell-lookup.patch: `apply (nth_error_In _ 60)` (60 = list index) is replaced by `apply '
                               '(AF0x.cell_lookup_In _ (ANum (TFIB_OOM + 1)))`; the checker pairs the index 60 with the '
                               'byte offset 1. Neither is an address.'),
    'N-TOT': lambda fx: (f'A/AFem.v TOT bound: TOT = length (ly_tr0 ly) + 1 + depot_frames S <= {fx["TR0_MAX"]} + 1 + 31 * '
                         f'DEPOT_MAX {fx["DEPOT_MAX"]} = {fx["TR0_MAX"] + 1 + 31 * fx["DEPOT_MAX"]}, a count (override rows '
                         f'of overrides.tsv; the owner\'s decision).'),
    'SV-MMAP': lambda fx: ('mmap flags word (YA01 node_mmap2g, YA09 mmap_noreserve_b / ff_class / noreplace_core): each '
                           'value decomposes into MAP_PRIVATE 0x2, MAP_ANONYMOUS 0x20 [, MAP_FIXED 0x10] [, MAP_NORESERVE '
                           '0x4000], MAP_FIXED_NOREPLACE 0x100000 with remainder 0. ABI constants; never relocated. The '
                           'checker reads each as an address inside internal_alloc_placeholder and gives a moved '
                           'expected value (its FLAGS-NOT-DECOMPOSABLE reading does not reach these positions).'),
    'SV-HWCAP': lambda fx: ('KRange (EVar V_HW) 0x112D 0x20112D: the range of the AT_HWCAP value; 0x112D = ISA bits a, c, '
                            'd, f, i, m; 0x20112D adds bit 21 (v). Not an address; the checker reads it as theDepot+off.'),
    'SV-RODATA-BOUND': lambda fx: ('0x200000 in `fst (fst e) + snd (fst e) <= 0x200000` over icpt_rodata (A/AE30.v, '
                                   'A/AE6k.v entD_ro): a loose upper bound on the ends of the rodata entries the file '
                                   'lists (A/AE2y.v), proved per entry by lia; every entry of both lists ends below it. '
                                   'The checker reads it as theDepot+offset.'),
    'U-RODATA-HI': lambda fx: (f'A/AB1w.v tfib_rodata_hi: the donor\'s value is a jump-table cell 0x40 below fuzz_grant\'s '
                               f'.rodata end; port_core 83f5203d2a2f writes fuzz_transport\'s .rodata end '
                               f'{hx(fx["Frodata"][1])} (section header), the owner\'s decision.'),
    'U-PHDR': lambda fx: f'AT_PHDR value: PT_PHDR p_vaddr = {hx(fx["Fphdr"])} in both images.',
    'U-TLSSH': lambda fx: (f'0x7fff8000 + a/8 with a = builtin_tls+0xeb8 in both (builtin_tls src {hx(fx["Gtlsbuf"][0])}, '
                           f'dst {hx(fx["Ftlsbuf"][0])}, size {hx(fx["Ftlsbuf"][1])} both); a lower bound on SMv that stays '
                           f'below shadow(IMG_TOP) in both trees.'),
    'K-CZONE': lambda fx: (f'CZONE bound {hx((fx["kLowShadowBeg"] or 0) + fx["Ftop"] // 8)} = kLowShadowBeg '
                           f'{hx(fx["kLowShadowBeg"])} + IMG_TOP {hx(fx["Ftop"])} / 8, the least shadow start of the '
                           f'secondary map that map_facts SM1 (A/AFjm.v) allows, so the CZONE window stays below it (the '
                           f'goal of A/AFju.v CZ_untouched); above the highest shadow end of fuzz_transport\'s registered '
                           f'globals {hx(fx["Fglob"][1])}; the donor\'s 0x80050000 is below it. The owner\'s decision '
                           f'(override rows).'),
    'P-BSSZR': lambda fx: ('bss-zero-range.patch: A/AD1o.v bss_zero_shadow / bss_shadow_facts and A/AD25.v rs_zero_shadow '
                           'take one piece of LIB/A/AF0m.v Tfib_zero_shadow each (the donor\'s one range over the whole '
                           '.bss after asan_globals is not in this image\'s list); each value is an end of that piece, the '
                           'start + 0x20, or a quotient by 8 of them, on a line the patch added. Where an override row '
                           'wrote the line first, port_core reports it `removed by --patch`.'),
    'P-GHUNK': lambda fx: ('the G patches (g-ACfn, g-AD1w, g-AD1m, g-AD1p, g-AD1q, g-AD1r, g-AD2f; records/ghunks/'
                           'GHUNKS-A-rec3.md): a numeral below the image base 0x10000 (no address of either image) on a '
                           'line a G patch added (the out-window count 0 of `ajournal_gx ... G 0 []`, the bounds of '
                           '`0 <= a < 2 ^ 64` in the memory-agreement hypothesis), or on a line it deleted whose '
                           'replacement keeps the value (the same sentence with the G names added).'),
    'P-LINEPAIR': lambda fx: ('a numeral on a line no patch changed, in a file a patch changed (afet-cost.patch, A/AFet.v), '
                              'which the checker leaves unpaired because the patch changed the sentence before it. Paired '
                              'by line (donor line L = stage-out line L + 1, the provenance line): the two lines are the '
                              'same text with the numerals masked, and the two values at the same position name the same '
                              'symbol + offset, each in its own image (twin symtabs).'),
    'N-IMGSPAN': lambda fx: (f'the image span IMG_TOP - IMG_LO: dst {hx(fx["Ftop"] - fx["Flo"])} = {hx(fx["Ftop"])} - '
                             f'{hx(fx["Flo"])}, src {hx(fx["Gtop"] - fx["Glo"])} = {hx(fx["Gtop"])} - {hx(fx["Glo"])}, on a '
                             f'line that adds it to IMG_LO (`0x10000 + SPAN`, the image top; A/AD1g.v static_img_chk). '
                             f'205a90fd19b8 flags it in its size-name slot rule; it is an image size that moves with the image.'),
    'SDCP-SIZE': lambda fx: ('262144 = 0x40000 in a register value of the allocator\'s free-array mapping walk: the mmap '
                             'length (x11) and the register the code fills with `lui xN, 0x40` (PopulateFreeArray, '
                             'EnsureFreeArraySpace), at the same function offsets in both images. A size; 0d24592683b6\'s '
                             'change (2) reads it as a code pointer because 0x40000 lies inside a function of fuzz_grant.'),
    'DS-AB1W-LABEL': lambda fx: ('AB1w rows whose name is a label carried from cgif_file_fuzzer\'s AB1w by the released '
                                 'donor, not the symbol: tfib_A_strlen .. tfib_A_wctomb hold the 4-byte wrappers '
                                 '__wrap_<f> = __interceptor_trampoline_<f> the program calls, tfib_A_asan_register_globals '
                                 'holds __asan_register_elf_globals, and so on. The dst value is the same symbol + offset '
                                 '(A) or the same end (E) in fuzz_transport as the src value in fuzz_grant. The named-symbol '
                                 'rule reads the label as a symbol name and expects the label-named symbol.'),
    'UM-AB1W-LABEL': lambda fx: ('UNMEASURED-NAME (reported, measured by nothing): as DS-AB1W-LABEL, rows whose label '
                                 'names a symbol of another spelling (gmtime_r / __gmtime_r ...); the dst value is the same '
                                 'symbol + offset as the src value.'),
    'S-GRANTPROG': lambda fx: ('fuzz_grant\'s own program functions (AB1w program table): fuzz_transport.asan has none of '
                               'them (both symtabs read); the port blanked these rows and wrote fuzz_transport\'s own '
                               'program functions on the LLVMFuzzerTestOneInput line (P-TRANSPROG). No file of stage-out or '
                               'LIB uses these names.'),
    'P-TRANSPROG': lambda fx: (f'fuzz_transport\'s own program functions, written on the dst LLVMFuzzerTestOneInput line of '
                               f'AB1w (A and E rows): each A value is the symtab start, each E value start + size; with the '
                               f'kept rows they cover every function of fuzz_transport\'s program range '
                               f'[{hx(fx["Fprog"][0])}, {hx(fx["Fprog"][1])}).'),
    'P-SMCLASS': lambda fx: (f'AB1w rows of __asan_stack_malloc_'
                             f'{"/".join(map(str, sorted(set(fx["Fsm"]) - set(fx["Gsm"]))))}: fuzz_transport links classes '
                             f'{"/".join(map(str, sorted(fx["Fsm"])))}, fuzz_grant {"/".join(map(str, sorted(fx["Gsm"])))}.'),
    'P-AF0L': lambda fx: (f'AF0l Tfib_code pc_stack_malloc: fuzz_transport has classes '
                          f'{"/".join(map(str, sorted(fx["Fsm"])))}, fuzz_grant {"/".join(map(str, sorted(fx["Gsm"])))}; '
                          f'the port wrote fuzz_transport\'s own class map, so the added arm has no partner.'),
    'PATCH-ZS': lambda fx: ('zero-shadow-forallb.patch: the Tfib_zero_shadow case split becomes a forallb check. Lines the '
                            'patch deletes (src) or adds (dst) carry literal 8s (shadow granule) and 0s (remainder); each '
                            'row\'s line is a deleted / added line of the patch for its file.'),
    'PATCH-DEADARM': lambda fx: ('dead-arm-ad1g.patch: the arm `|| (change SPAN with (1482 * 4096); apply Z_mod_mult)` '
                                 'of A/AD1g.v is dead in the donor (1482 * 4096 != SPAN) and removed in the port; the '
                                 'deleted arm\'s numerals have no partner. The owner\'s decision.'),
    'N-REGCNT': lambda fx: ('count or index in the IMG_REGIONS region list, mapped from the donor\'s list to the unit\'s '
                            '(LIB/A/AD2j.v, the stand-in start-up layer); the run of record recomputes them from the new '
                            'start-up layer.'),
}


def write_md(a, c, rows, flagged_line, fc_line, rc_line, um_line, counts, match, geo, reg):
    fx = c.facts
    fl = [d for d in rows if d['verdict'] not in (FILL, UMN)]
    fill = [d for d in rows if d['verdict'] == FILL]
    um = [d for d in rows if d['verdict'] == UMN]
    bad = [d for d in rows if d['reason'] == 'UNEXPLAINED']
    geobad = [g for g in geo if not g['ok']]
    tool = [d for d in fl + fill if d['class'] == TOOL]
    real = [d for d in fl + fill if d['class'] == REAL]

    def nrows(n):
        return f'{n} row' + ('' if n == 1 else 's')
    bycls = collections.defaultdict(list)
    for d in fl:
        bycls[d['verdict']].append(d)
    W = []
    w = W.append
    rcm = re.search(r'rc=(\d+) \(sha256 (\w+)\)', rc_line or '')
    ck = rcm.group(2) if rcm else '?'
    w(f'# Triage of the {ck} flag-gate rows: libdiginet/fuzz_transport image-A core relocation (row TCA)')
    w('')
    w('proves no function (kind: measurement). Read-only triage of gate (a); made by `gates/triage-A.py` (every value in '
      'this file is computed by it from the images and the text).')
    w('')
    w('## Result')
    w('')
    w(f'- Gate run: `{os.path.basename(a.raw)}` / `{os.path.basename(a.log)}` (port_addr_check {ck} '
      f'`--fail-on-flags`, one default pass, made by `gates/pac-A.sh`). '
      f'{"checker rc=" + rcm.group(1) + " (sha256 " + rcm.group(2) + ")" if rcm else ""}. '
      f'Last line: `{flagged_line}`. `{(fc_line or "").split(chr(9))[0]}`. `{um_line}`.')
    w(f'- {len(fl)} flagged rows (FLAGGED line {"matches, class by class" if match else "DIFFERS"}) and {len(fill)} '
      f'GENERATOR-FILL rows (reported, not counted): {len(fl) + len(fill) - sum(1 for d in fl + fill if d["reason"] == "UNEXPLAINED")} '
      f'explained, {sum(1 for d in fl + fill if d["reason"] == "UNEXPLAINED")} UNEXPLAINED. Also triaged: {len(um)} '
      f'UNMEASURED-NAME rows (reported, measured by nothing by the checker): '
      f'{len(um) - sum(1 for d in um if d["reason"] == "UNEXPLAINED")} explained.')
    cls = collections.Counter(d['class'] or 'UNEXPLAINED' for d in fl + fill)
    w(f'- Classification (flagged + GENERATOR-FILL): **{OK} {cls.get(OK, 0)}, {TOOL} {cls.get(TOOL, 0)}, {REAL} '
      f'{cls.get(REAL, 0)}**{", UNEXPLAINED " + str(cls["UNEXPLAINED"]) if cls.get("UNEXPLAINED") else ""}.')
    if bad:
        w(f'- **{len(bad)} rows no rule explains** (listed under REAL / UNEXPLAINED).')
    else:
        w('- **REAL among the triaged rows: none.** Every dst value is fuzz_transport\'s own value of the quantity that '
          'the src value names in fuzz_grant\'s image, or a value with no address role that is correct for '
          'fuzz_transport.')
    if geobad:
        w('- **Outside the flag set: ' + '; '.join(
            f'stage-out/A/AB1w.v:{g["line"]} `{g["name"]} := {hx(g["v"])}`, fuzz_transport gives {hx(g["want"])}'
            for g in geobad) + '.**')
    w(f'- One row per line, with reason id, class and measurement: `{os.path.basename(a.out)}` (column `raw_line` = the '
      f'row\'s line number in `{os.path.basename(a.raw)}`).')
    w('')
    w('| class | FLAGGED | triaged | reasons (rows) |')
    w('|---|---:|---:|---|')
    for k in sorted(bycls):
        rc = collections.Counter(d['reason'] for d in bycls[k])
        w(f'| {k} | {counts.get(k, 0)} | {len(bycls[k]) - sum(1 for d in bycls[k] if d["reason"] == "UNEXPLAINED")} | '
          + ', '.join(f'{r} ({n}, {RCLASS.get(r, "-")})' for r, n in rc.most_common()) + ' |')
    w(f'| total | {sum(counts.values())} | {len(fl) - sum(1 for d in fl if d["reason"] == "UNEXPLAINED")} | |')
    for lab_, grp in (('GENERATOR-FILL (reported)', fill), ('UNMEASURED-NAME (reported)', um)):
        if grp:
            rc = collections.Counter(d['reason'] for d in grp)
            w(f'| {lab_} | - | {len(grp) - sum(1 for d in grp if d["reason"] == "UNEXPLAINED")} | '
              + ', '.join(f'{r} ({n}, {RCLASS.get(r, "-")})' for r, n in rc.most_common()) + ' |')
    w('')
    w('Classes: **OK-explained** = the checker flags, by its own stated rule, a pair it does not decide, and the '
      'measurement shows the dst value right. **TOOL-LIMIT** = the checker\'s note states an expected value or a role '
      'that the images contradict; the dst value is right; for the address checker\'s owner. **REAL** = a wrong value '
      'in stage-out.')
    w('')
    if a.controls and os.path.exists(a.controls):
        w('## Record run and planted controls')
        w('')
        w(f'`{os.path.basename(a.controls)}` (made by `flag-gate-A.sh`, the form of D9\'s records/flag-gate.txt): the '
          'checker run exactly as `gates/pac-A.sh` runs it, on stage/ against a copy of stage-out/ restricted to A/AF0l.v '
          '(`--include A/AF0l.v`), with `pc_wrap_memcpy` planted wrong, and on the same file unplanted.')
        w('')
        w('```')
        W.extend(open(a.controls).read().rstrip('\n').split('\n'))
        w('```')
        w('')
    w('## REAL rows (a wrong value in stage-out)')
    w('')
    if real or bad:
        for d in real + bad:
            w(f'- raw {d["raw_line"]} {d["verdict"]} {d["_f"]}:{d["src_line"] or "-"} -> dst line {d["dst_line"] or "-"}: '
              f'written {d["dst_value"]}; {d["detail"]}')
    else:
        w('None. No triaged row has a dst value that is wrong for fuzz_transport.asan.')
    w('')
    w(f'## TOOL-LIMIT rows ({len(tool)}; for the address checker\'s owner)')
    w('')
    w('Each row: the dst value is right (measured); the checker\'s verdict rests on a reading the images contradict.')
    w('')
    tr = collections.defaultdict(list)
    for d in tool:
        tr[d['reason']].append(d)
    for r, ds in sorted(tr.items(), key=lambda kv: -len(kv[1])):
        w(f'- **{r}** ({nrows(len(ds))}): {DESC[r](fx)}')
        for d in ds:
            w(f'  - raw {d["raw_line"]} {d["verdict"]} {d["_f"]}:{d["src_line"] or "-"} -> {d["dst_line"] or "-"} '
              f'`{d["sentence"]}` {d["src_value"]} -> {d["dst_value"]}; checker expected {note_expected(d) or "-"}')
    w('')
    w("## Known items (decided by the image-A core's writer; triaged here all the same)")
    w('')
    kn = collections.defaultdict(list)
    for d in rows:
        if d['known']:
            kn[d['known']].append(d)
    for k, ds in kn.items():
        w(f'- {k}: {nrows(len(ds))} (' + ', '.join(f'{d["_f"].split("/")[-1][:-2]}:{d["src_line"] or d["dst_line"]}'
                                                    for d in ds) + ')')
    w('')
    w('## What was measured, and how')
    w('')
    for side, I in (('src', c.G), ('dst', c.F)):
        w(f'- Image {side}: `{I.label}` sha256 {I.sha}; symbols from its unstripped twin `{I.twinlabel}` sha256 '
          f'{I.twinsha} (`.symtab`). Allocated sections of the twin equal to the stripped image except '
          f'`.note.gnu.build-id`: {"yes (checked)" if not I.twin_diff else "NO: " + ", ".join(I.twin_diff)}.')
    w('- Image bytes, PT_LOAD / PT_TLS / PT_PHDR, section bounds and the asan_globals descriptors: read from the stripped '
      f'images with pyelftools. IMG_TOP (page-up of the last PT_LOAD end): src {hx(fx["Gtop"])}, dst {hx(fx["Ftop"])}; '
      f'__stop_asan_globals: src {hx(fx["Gstop"])}, dst {hx(fx["Fstop"])}; .bss: src {hx(fx["Gbss"])}, dst '
      f'{hx(fx["Fbss"])}; .rodata: src [{hx(fx["Grodata"][0])}, {hx(fx["Grodata"][1])}), dst [{hx(fx["Frodata"][0])}, '
      f'{hx(fx["Frodata"][1])}); program range (LLVMFuzzerTestOneInput .. __wrap_getenv): src '
      f'[{hx(fx["Gprog"][0])}, {hx(fx["Gprog"][1])}), dst [{hx(fx["Fprog"][0])}, {hx(fx["Fprog"][1])}); '
      f'registered globals: src {fx["Gglob"][0]} (highest shadow end {hx(fx["Gglob"][1])}), dst {fx["Fglob"][0]} '
      f'({hx(fx["Fglob"][1])}).')
    w('- Instruction words (SDCP-SIZE only): every `lui` word of .text whose 20-bit immediate is the value / 4096, '
      'located by function + offset in both images; only what the word writes to its register is used.')
    w('- Text: src = `stage/`, dst = `stage-out/` of the port_core run. Each row\'s src line and dst line were read; a '
      'dst line is the src line + 1 (the added provenance line), unless a patch or a removed row moves it.')
    w(f'- Start-up layer (not relocated; the stand-in of LIB `{a.lib}`, A/): '
      + ', '.join(f'A/{f} sha256 {sha12(os.path.join(c.startup, f))}' for f in STARTUP_FILES)
      + '. Donor start-up values from fuzz_grant\'s released lib (`A/AB13.v`, `A/AF0m.v`, `A/AD2j.v`). The run of record '
        'changes only the start-up dependent values; re-run this script with its LIB.')
    w(f'- The run\'s decisions: `check.tsv`, `review.tsv`, `fixed.tsv`, `decimals.tsv`, `patches.log` of the run dir '
      f'(each row\'s matching decision is quoted in its detail), the overrides `{c.ovr_name}` (sha256 '
      f'{sha12(a.overrides)}), and ' + ', '.join(f'`{p}` ({sha12(os.path.join(a.evidence, p))})' for p in PATCHES)
      + f' of `{a.evidence}`.')
    ov = [d for d in rows if c.ovr_name + ' line' in d['detail']]
    w(f'- Override cross-check: {len(ov)} triaged rows carry an override row (same file, donor line, old value); for '
      f'{"all" if all("(dst = the override value)" in d["detail"] for d in ov) else "NOT all"} of them the dst value '
      f'equals the override\'s new value: ' + ', '.join(f'{d["_f"].split("/")[-1][:-2]}:{d["src_line"]}' for d in ov) + '.')
    w('')
    w('## Reasons')
    w('')
    rc = collections.Counter(d['reason'] for d in rows)
    for r, n in rc.most_common():
        if r == 'UNEXPLAINED':
            continue
        vs = sorted({d['verdict'] for d in rows if d['reason'] == r})
        try:
            desc = DESC[r](fx)
        except (TypeError, KeyError, IndexError):
            desc = '(description needs a fact this run lacks; see the rows)'
        no = sum(1 for d in rows if d['reason'] == r and '(dst = the override value)' in d['detail'])
        ovn = f' {no} of the {n} dst values are override rows of `{c.ovr_name}` (each equal to its new value).' if no else ''
        w(f'- **{r}** ({nrows(n)}; {", ".join(vs)}; {RCLASS[r]}): {desc}{ovn}')
    w('')
    w('## Rows per class')
    hdrrow = ('| raw line | src file:line | dst line | sentence (idx) | kind | src value | dst value | reason | class | '
              'measurement |')
    groups = [(k, bycls[k], counts.get(k, 0)) for k in sorted(bycls)] + [(FILL, fill, None), (UMN, um, None)]
    for k, grp, nflag in groups:
        if not grp:
            continue
        rcc = collections.Counter(d['reason'] for d in grp)
        w('')
        w(f'### {k} ({nrows(len(grp))}' + (f'; FLAGGED says {nflag})' if nflag is not None else '; reported, not counted)'))
        w('')
        w('Reasons: ' + ', '.join(f'{r} ({n})' for r, n in rcc.most_common()) + '.')
        w('')
        w(hdrrow)
        w('|---:|---|---:|---|---|---|---|---|---|---|')
        for d in sorted(grp, key=lambda x: (x['reason'], x['_f'], ival(x['src_line'] or x['dst_line']) or 0)):
            w(f'| {d["raw_line"]} | {d["_f"]}:{d["src_line"] or "-"} | {d["dst_line"] or "-"} | {d["sentence"]} '
              f'({d["idx"] or "-"}) | {d["kind"]} | {d["src_value"] or "-"} | {d["dst_value"] or "-"} | {d["reason"]} | '
              f'{d["class"] or "-"} | {(d["detail"] + ("; " + d["known"] if d["known"] else "")).replace("|", "/")} |')
    w('')
    w('## Rows outside the flag set')
    w('')
    w('The AB1w rows that restate image geometry for the auxiliary vector, checked against both images:')
    w('')
    w('| stage-out line | name | written | fuzz_transport | donor line value | fuzz_grant | checker verdict | |')
    w('|---:|---|---|---|---|---|---|---|')
    for g in geo:
        w(f'| A/AB1w.v:{g["line"]} | {g["name"]} | {hx(g["v"])} | {hx(g["want"])} | {hx(g["sv"])} | {hx(g["swant"])} | '
          f'{g["verdict"]} | {"ok" if g["ok"] else "**WRONG**"} |')
    w('')
    w(f'Region counts: donor layout (N, R_A5a, R_A7b) {reg["donor"]}, unit layout {reg["unit"]} (LIB/A/AD2j.v, the '
      f'stand-in): {reg["status"]} (N-REGCNT rows {reg["nreg"]}).')
    w('')
    w(f'{"No REAL row among the triaged rows" if not bad else str(len(bad)) + " UNEXPLAINED rows"}. {flagged_line} '
      f'({(fc_line or "").split(chr(9))[0]}); GENERATOR-FILL {len(fill)}, UNMEASURED-NAME {len(um)} (all triaged above).')
    open(a.md, 'w').write('\n'.join(W) + '\n')


if __name__ == '__main__':
    main()
