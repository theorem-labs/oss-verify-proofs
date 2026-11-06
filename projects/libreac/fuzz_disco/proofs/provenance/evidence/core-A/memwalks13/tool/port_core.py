#!/usr/bin/env python3
"""port_core.py -- copy a set of released cgif_file_fuzzer ASan-side proof files to another target and move their
addresses from cgif_file_fuzzer.asan to TARGET.asan. README.md beside this file states every rule and every table.

    port_core.py --target-lib DIR --target-mod MOD --target-images MOD --target-elf ELF --files LIST [options]

Steps (each one writes into --work):
  1. map    elf_symbols.py OLD_ELF TARGET_ELF -> map.json (+ map.txt summary).           (the slice's kit/elf_symbols.py)
  2. stage  copy each file of LIST from --src-lib to stage/, renaming module paths. A non-A file the target already
            has is kept (kept.txt) and never copied.
  3. remap  numeral_map.py --rewrite over the staged A/ files (and image-importing non-A files with --remap-images).
  4. reloc  every numeral of stage-out/ is decided again, position by position against stage/ (the released text),
            by the rules in README.md: section/segment/image bounds from the target's headers, code by function
            pairing (resolve_code.py) with the end rule, GOT words by the code that loads them, values held by a GOT
            word by the twin word's value, cells by the target's bytes, geometry-derived decimals from the headers.
            A value no rule can give becomes `port_core_refused_<old>` (the file stops there).
  5. checks image ends left behind, non-A files that state image constants, names, names used from kept target
            files, per-image values still missing, then the symbol gate (port_addr_check.py) over stage/ vs
            stage-out/.
  6. header one licence line per file; with --apply (only when every gate passes) copy stage-out/ into TARGET_LIB.
Exit status: 0 all gates pass; 3 the symbol gate failed; 4 values that need an --override row are missing.
"""
import argparse, bisect, collections, hashlib, json, os, re, shutil, struct, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
KIT = os.path.join(HERE, os.pardir, os.pardir, 'kit')  # the slice's kit: rvelf.py, elf_symbols.py, numeral_map.py
sys.path.insert(0, KIT)
sys.path.insert(0, HERE)
# the check tools and caches below are arguments (--cell-gates, --cellcheck, --decode-check, --syms-cache); None skips
CELL_GATES = None  # dir of shadowcheck.py, ownedcheck.py
CELLCHECK = None
DECODE_CHECK = None  # independent decoder (a gate)
OLD_SYMS_TXT = {}  # image sha256[:16] -> its recovered-symbols text (none known here: give --old-syms)
SYMS_CACHE = None  # <image sha16>.<donors sha16>.v4.json
SYMS_DONORS = '978e0a064c5a4c6e'  # the donor set port_addr_check recovers cgif's names from (the README's caches)
SHADOW = 0x7fff8000
REFUSED = 'port_core_refused_'
PAGE = 0x1000


def run(cmd, **kw):
    print('+', ' '.join(cmd), file=sys.stderr)
    r = subprocess.run(cmd, **kw)
    if r.returncode != 0:
        sys.exit(f'port_core: command failed ({r.returncode}): {" ".join(cmd)}')
    return r


DIRMAP = {}  # non-A source path -> the target directory it goes to (--kernel-dir split); default --reusable-dir
DONOR_DIRS = set()  # a non-cgif donor's own dir of non-A files (e.g. Reusable): stripped, never doubled
AS_TWIN = set()  # --as-twin: the donor's A/ module names (A<x>) staged as <reusable-dir>/Y<x>.v
DONOR_DESC = 'proofs/cgif/cgif_file_fuzzer/lib'  # provenance text: the donor tree (and its image sha), set in main


def rename_text(t, a):
    """module paths: <src>.A.X -> <target>.A.X; <src>.X -> <target>.<dir of X>.X, where the dir is --reusable-dir,
    or with --kernel-dir the kernel dir for a file whose Require closure reaches no image-specific module (a
    `From <src> Require Import X Y.` whose modules go to two dirs becomes two sentences on the same line)."""
    # the target module is written as a placeholder until the end: a target path that contains the source path (a
    # donor control, cgif -> cgif, or --as-twin grant A -> grant A) must not be renamed a second time
    sm, tm = a.src_mod, '\x01'
    if AS_TWIN:
        # --as-twin: the donor's A/A<x>.v are a unit's own image-A text, staged as <reusable-dir>/Y<x>.v: module
        # paths lib.A.A<x> -> lib.<dir>.Y<x> and module-qualified names A<x>.n -> Y<x>.n (the kernel dir where the
        # target lib holds Y<x> shared)
        def ydir(x):
            y = 'Y' + x[1:] + '.v'
            if getattr(a, 'kernel_dir', None) and os.path.exists(os.path.join(a.target_lib, a.kernel_dir, y)) and \
                    not os.path.exists(os.path.join(a.target_lib, a.reusable_dir, y)):
                return a.kernel_dir.replace('/', '.')
            return a.reusable_dir.replace('/', '.')

        def afrom(m):
            groups = collections.OrderedDict()
            for n in m.group(2).split():
                groups.setdefault(ydir(n), []).append('Y' + n[1:] if n in AS_TWIN else n)
            return ' '.join(f'From {tm}.{d} Require{m.group(1)} {" ".join(ns)}.' for d, ns in groups.items()) + \
                '\n' * m.group(0).count('\n')
        t = re.sub(r'From\s+' + re.escape(sm) + r'\.A\s+Require((?:\s+(?:Import|Export))?)\s+([\w.\'\s]+?)\.(?=\s|$)',
                   afrom, t)
        t = re.sub(re.escape(sm) + r'\.A\.(A\w+)', lambda m: f'{tm}.{ydir(m.group(1))}.Y{m.group(1)[1:]}'
                   if m.group(1) in AS_TWIN else m.group(0), t)
        t = re.sub(r"(?<![\w.'])(A[A-Za-z0-9]{3})(?=\.[A-Za-z_])", lambda m: 'Y' + m.group(1)[1:]
                   if m.group(1) in AS_TWIN else m.group(1), t)
    t = t.replace(sm + '.A.', '\0A.').replace(sm + '.A ', '\0A ').replace(sm + '.A\n', '\0A\n')

    def mdir(mod):
        f = mod.replace('.', '/') + '.v'
        if f in DIRMAP:
            return DIRMAP[f].replace('/', '.')
        # a module the run does not stage (a kit file such as YK18 / YK0j the trunk lib holds): named by where the
        # target lib has it. Their Require closures reach no images module and no image value (grant: YK18 28
        # modules, YK0j 5), so they are the shared dir's, never the per-image one's (the hand-written twins)
        if getattr(a, 'kernel_dir', None) and not os.path.exists(os.path.join(a.target_lib, a.reusable_dir, f)) \
                and os.path.exists(os.path.join(a.target_lib, a.kernel_dir, f)):
            return a.kernel_dir.replace('/', '.')
        return a.reusable_dir.replace('/', '.')

    def from_line(m):
        groups = collections.OrderedDict()
        for n in m.group(2).split():
            groups.setdefault(mdir(n), []).append(n)
        if len(groups) == 1:  # one directory: the sentence keeps its own layout
            return m.group(0).replace(sm, f'{tm}.{next(iter(groups))}', 1)
        return ' '.join(f'From {tm}.{d} Require{m.group(1)} {" ".join(ns)}.' for d, ns in groups.items()) + \
            '\n' * m.group(0).count('\n')  # the same number of lines, so line numbers stay the donor's
    t = re.sub(r'From\s+' + re.escape(sm) + r'\s+Require((?:\s+(?:Import|Export))?)\s+([\w.\'\s]+?)\.(?=\s|$)',
               from_line, t)

    def qual(m):
        parts = m.group(1).split('.')
        if parts[0] in DONOR_DIRS:  # <donor>.Reusable.X: the donor's own dir is not part of the target path
            parts = parts[1:]
            if not parts:
                return f'{tm}.{a.reusable_dir.replace("/", ".")}'
        mod = '.'.join(parts[:2]) if parts[0] in ('R', 'Z') and len(parts) > 1 else parts[0]
        return f'{tm}.{mdir(mod)}.{".".join(parts)}'
    t = re.sub(re.escape(sm) + r'\.((?!A\b)[A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)*)', qual, t)
    t = re.sub(re.escape(sm) + r'(?=[ .\n])', tm + '.' + a.reusable_dir.replace('/', '.'), t)
    t = t.replace('\0A', tm + '.A').replace('\x01', a.target_mod)
    t = t.replace(a.src_images, a.target_images)
    for r in a.rename:
        o, n = r.split('=', 1)
        t = re.sub(r'(?<![A-Za-z0-9_\'])' + re.escape(o) + r'(?![A-Za-z0-9_\'])', n, t)
    return t


def dst_path(rel, reusable='Reusable'):
    if rel.startswith('A/'):
        b = os.path.basename(rel)
        return os.path.join(reusable, 'Y' + b[1:]) if AS_TWIN and b[:-2] in AS_TWIN else rel
    base = rel.split('/', 1)[1] if rel.split('/', 1)[0] in DONOR_DIRS else rel
    return os.path.join(DIRMAP.get(rel, DIRMAP.get(base, reusable)), base)

def y_twin(name, src_lib):
    """cgif's release layout: a root `Y<x>.v` whose `A/A<x>.v` exists is that A/ file's asan-ubsan twin (it states
    the same image facts for the other image, often without importing the images module, e.g. YB1w's function
    table)."""
    return bool(re.fullmatch(r'Y\w+\.v', name)) and os.path.exists(os.path.join(src_lib, 'A', 'A' + name[1:]))



# ---------------------------------------------------------------- ELF access
class Elf:
    def __init__(self, path):
        self.b = open(path, 'rb').read()
        b = self.b
        assert b[:4] == b'\x7fELF' and b[4] == 2
        shoff, = struct.unpack_from('<Q', b, 0x28)
        shentsize, shnum, shstrndx = struct.unpack_from('<HHH', b, 0x3a)
        secs = []
        for i in range(shnum):
            o = shoff + i * shentsize
            name, typ, flags, addr, off, size = struct.unpack_from('<IIQQQQ', b, o)
            secs.append([name, typ, flags, addr, off, size])
        so = secs[shstrndx][4]
        self.secs = []
        for name, typ, flags, addr, off, size in secs:
            n = b[so + name: b.index(b'\0', so + name)].decode()
            if flags & 2 and size:  # SHF_ALLOC
                self.secs.append((n, typ, flags, addr, off, size))

    def sec(self, a):
        for s in self.secs:
            if s[3] <= a < s[3] + s[5]:
                return s
        return None

    def read(self, a, n):
        s = self.sec(a)
        if s is None or s[1] == 8:  # NOBITS
            return None
        n = min(n, s[3] + s[5] - a)
        return self.b[s[4] + a - s[3]: s[4] + a - s[3] + n]

    def q(self, a, n=8):
        """little-endian n-byte value at a, or None when a..a+n is not file-backed in one section."""
        b = self.read(a, n)
        return int.from_bytes(b, 'little') if b is not None and len(b) == n else None


class Geo:
    """Every bound a proof can state, from an ELF's own headers. Roles are strings so that reports read plainly:
    `sec:.got.hi`, `load3.filehi`, `seg2.base`, `hull.hi`, `relro.lo`, `tls.lo`; derived (decimal) roles:
    `seg0.size`, `seg3.zoff` (file end - segment base: where the zero fill starts), `seg3.zlen` (segment end - file
    end), `hull.size`, `hull.page` (hull.hi / 4096), `segN.basepage`/`segN.endpage`."""

    def __init__(self, path):
        b = open(path, 'rb').read()
        phoff, = struct.unpack_from('<Q', b, 0x20)
        phentsize, phnum = struct.unpack_from('<HH', b, 0x36)
        loads, self.relro, self.tls = [], None, None
        for i in range(phnum):
            t, _, _, va, _, fs, ms, _ = struct.unpack_from('<IIQQQQQQ', b, phoff + i * phentsize)
            if t == 1:
                loads.append((va, va + fs, va + ms))
            elif t == 0x6474e552:
                self.relro = (va, va + ms)
            elif t == 7:
                self.tls = (va, va + ms)
        self.loads = loads
        self.segs = [(lo & ~(PAGE - 1), (mh + PAGE - 1) & ~(PAGE - 1)) for lo, _, mh in loads]
        self.hull = (min(s[0] for s in self.segs), max(s[1] for s in self.segs))
        e = Elf(path)
        self.sec = {s[0]: (s[3], s[3] + s[5]) for s in e.secs}
        r = {}
        for n, (lo, hi) in self.sec.items():
            r[f'sec:{n}.lo'], r[f'sec:{n}.hi'] = lo, hi
        for i, (lo, fh, mh) in enumerate(loads):
            r[f'load{i}.lo'], r[f'load{i}.filehi'], r[f'load{i}.memhi'] = lo, fh, mh
        for i, (bs, en) in enumerate(self.segs):
            r[f'seg{i}.base'], r[f'seg{i}.end'] = bs, en
        r['hull.lo'], r['hull.hi'] = self.hull
        if self.relro:
            r['relro.lo'], r['relro.hi'] = self.relro
        if self.tls:
            r['tls.lo'], r['tls.hi'] = self.tls
        self.role = r
        d = {}
        for i, (bs, en) in enumerate(self.segs):
            d[f'seg{i}.size'] = en - bs
            d[f'seg{i}.base'], d[f'seg{i}.end'] = bs, en
            d[f'seg{i}.basepage'], d[f'seg{i}.endpage'] = bs // PAGE, en // PAGE
            lo, fh, mh = loads[i]
            if mh > fh:
                d[f'seg{i}.zoff'], d[f'seg{i}.zlen'] = fh - bs, en - fh
        d['hull.size'] = self.hull[1] - self.hull[0]
        d['hull.page'] = self.hull[1] // PAGE
        d['hull.hi'] = self.hull[1]
        d['hull.hi/8'] = self.hull[1] >> 3  # the shadow bound of the image top
        d['hull.size/8'] = (self.hull[1] - self.hull[0]) >> 3
        d['shadow(hull.hi)'] = SHADOW + (self.hull[1] >> 3)  # the shadow byte of the image top (a8 2148234752)
        if '.bss' in self.sec:  # .bss offset inside its own PT_LOAD, image top minus .bss (grant A 12056, 5606272)
            b = self.sec['.bss'][0]
            for lo, fh, mh in loads:
                if lo <= b < mh:
                    d['bss.segoff'] = b - lo
            d['hull.hi-bss'] = self.hull[1] - b
        self.dec = d
        self.by = collections.defaultdict(list)
        for k, v in r.items():
            self.by[v].append(k)
        self.dby = collections.defaultdict(list)
        for k, v in d.items():
            self.dby[v].append(k)


def mask_insn(w, size):
    """Masked encoding: drop every immediate an address move can change."""
    if size == 2:
        op = w & 3; f3 = (w >> 13) & 7
        if op == 1 and f3 in (1, 5):   # c.jal / c.j
            return w & 0xe003
        if op == 1 and f3 in (6, 7):   # c.beqz / c.bnez
            return w & 0xe383
        return w
    opc = w & 0x7f
    if opc in (0x17, 0x37):             # auipc / lui
        return w & 0xfff
    if opc == 0x6f:                     # jal
        return w & 0xfff
    if opc == 0x63:                     # branch
        return w & 0x01fff07f
    if opc in (0x13, 0x03, 0x67, 0x1b, 0x07):  # addi/load/jalr/addiw/fp-load: lo12 partner of an auipc
        return w & 0xfffff
    if opc in (0x23, 0x27):             # store: lo12 partner
        return w & 0x01fff07f
    return w


def insn_at(elf, a):
    b = elf.read(a, 4)
    if b is None or len(b) < 2:
        return None
    lo = b[0] | b[1] << 8
    if lo & 3 != 3:
        return (lo, 2)
    if len(b) < 4:
        return None
    return (struct.unpack('<I', b)[0], 4)


NUM = re.compile(r"(?<![A-Za-z0-9_'.])(0x[0-9a-fA-F]+|\d+)(?![0-9A-Za-z_])")
OPCODE_CTX = re.compile(r'\s*(?:%bv)?\s*\)?\s*:\s*bv\s+32\b')  # `0x...%bv : bv 32` (a `%bv : word` is an address)
WORD32 = re.compile(r'0x0[0-9a-fA-F]{7}')  # zero-padded to 8 digits: a 32-bit word, never an address here
OPCODE_PRE = re.compile(r'(?:Z_to_bv\s+32|bv\s+32\s*:=|W_[0-9a-f]+\s*:=|\bPW)\s*\(?\s*$')  # PW: a listing's word
DEF = re.compile(r"\b(?:Local\s+)?(?:Definition|Let|Notation)\s+([A-Za-z_][\w']*)")
FIELD = re.compile(r"(?:^|[{;(]|\|\s)\s*([A-Za-z_][\w']*)\s*:=")  # a record field `name := value`
END_HINT = re.compile(r'(?:^|_)(?:E|END|end|hi|HI|lim|stop|top)(?:_|$)')
START_HINT = re.compile(r'(?:^|_)(?:A|pc|PC|start|START|lo|LO|beg|BEG|entry|ENTRY)(?:_|$)')
BOUND_NAME = re.compile(r'(?:^|_)([a-z0-9_]+)_(lo|hi)$')
_V = r'(0x[0-9a-fA-F]+|\d+)'
CELLS = [  # (regex, group of address, group of size, group of value): the cell forms of the released text
    (re.compile(r'\bz([1248])\s+\(ANum\s+' + _V + r'\)\s+' + _V + r'(?![\w])'), 2, 1, 3),
    (re.compile(r'\blit([1248])\s+' + _V + r'\s+' + _V + r'(?![\w])'), 2, 1, 3),
    (re.compile(r'\bval_mem\s+\w+\s+(?:\w+|\((?:[^()]|\([^()]*\))*\))\s+' + _V + r'\s+([1248])\s+' + _V + r'(?![\w])'), 1, 2, 3),
    (re.compile(r'mkChunk\s+' + _V + r'\s+\(CVal\s+([1248])\s+\(SLit\s+' + _V + r'\)\)'), 1, 2, 3),
    (re.compile(r'\(\s*' + _V + r'\s*,\s*([1248])%N\s*,\s*' + _V + r'\s*\)'), 1, 2, 3),
    (re.compile(r'a_base\s*:=\s*ELit\s+0\s*;\s*a_off\s*:=\s*' + _V + r'\s*\|\}\s*([1248])\s+\(ELit\s+' + _V + r'\)'), 1, 2, 3),
    # a fetched instruction word is a 4-byte cell of the image: `fetch_word S (A%bv : word) = Some (W%bv : bv 32)`
    # (a negative size field is the size itself)
    (re.compile(r'fetch_word\s+\w+\s+\(\s*' + _V + r'%bv\s*:\s*word\s*\)\s*=\s*Some\s+\(\s*' + _V +
                r'%bv\s*:\s*bv\s+32\s*\)'), 1, -4, 2),
    (re.compile(r'fetch_word\s+\w+\s+\(\s*Z_to_bv\s+64\s+' + _V + r'\s*\)\s*=\s*Some\s+\(\s*' + _V +
                r'%bv\s*:\s*bv\s+32\s*\)'), 1, -4, 2),
    (re.compile(r'\w+_tbl_ok\s+' + _V + r'\s+(0x[0-9a-fA-F]+)(?![\w])'), 1, -4, 2),
]
LABEL_ARG = re.compile(r'\b(spin|ISpin|mcheck|FCheck|stag)\s+\(?\s*(0x[0-9a-fA-F]+|\d+)(?![\w])')  # opaque pc labels


def left_operand(t):
    """the left operand ending at the end of t: scanned back over balanced parentheses to an unmatched `(` or a
    separator (`/\\`, `\\/`, `&&`, `||`, `:`, `;`, `,`, `with`) at depth 0."""
    depth, i = 0, len(t)
    while i > 0:
        ch = t[i - 1]
        if ch == ')':
            depth += 1
        elif ch == '(':
            if depth == 0:
                break
            depth -= 1
        elif depth == 0 and (ch in ':;,' or t[max(0, i - 2):i] in ('/\\', '\\/', '&&', '||') or
                             (t[max(0, i - 4):i] == 'with' and (i < 5 or not (t[i - 5].isalnum() or t[i - 5] == '_')))):
            break
        i -= 1
    return t[i:]


MAP_FLAG_BITS = (0x1 | 0x2 | 0x10 | 0x20 | 0x100 | 0x800 | 0x1000 | 0x2000 | 0x4000 | 0x8000 | 0x10000 | 0x20000 |
                 0x40000 | 0x80000 | 0x100000)  # Linux MAP_* (SHARED .. FIXED_NOREPLACE)


def is_map_flags(v):
    """v is a sum of Linux MAP_* flags with a sharing type (MAP_SHARED / MAP_PRIVATE) and MAP_FIXED_NOREPLACE (so it is
    >= 0x100000: below that a flags value is never confused with an image address); not 4-aligned, so never an
    8-aligned .bss object."""
    return bool(v & 0x100000) and not v & ~MAP_FLAG_BITS and v & 3 in (1, 2, 3)


def label_starts(line):
    """{start offset of a numeral: the label function} for every opaque pc label of a line: the argument of spin /
    ISpin / FCheck, and the pc of `mcheck B PC` whatever B is (a parenthesised condition, a `match ... end`, a name:
    AFk0.v:759 `mcheck (... <? kMaxNumChunks) 221048`, AFg2.v:292 `mcheck match ck_state k0 with ... end 201364`)."""
    out = {m.start(2): m.group(1) for m in LABEL_ARG.finditer(line)}
    for m in re.finditer(r'\bmcheck\s+', line):
        j = m.end()
        if line.startswith('(', j):
            depth = 0
            while j < len(line):
                depth += {'(': 1, ')': -1}.get(line[j], 0)
                j += 1
                if depth == 0:
                    break
        elif re.match(r'match\b', line[j:]):
            depth, k = 0, j
            for t in re.finditer(r'\b(match|end)\b', line[j:]):
                depth += 1 if t.group(1) == 'match' else -1
                if depth == 0:
                    k = j + t.end()
                    break
            j = k
        else:
            t = re.match(r"[\w.']+", line[j:])
            j += t.end() if t else 0
        n = re.match(r'\s*\(?\s*(0x[0-9a-fA-F]+|\d+)(?![\w])', line[j:])
        if n:
            out[j + n.start(1)] = 'mcheck'
    return out


PER_UNIT_DEFS = {  # definitions stated from the target program, never relocated (refused: a hand value per unit)
    'lib_const_addr': "state it from the target program's own measured constant reads (grant: False); a moved GOT "
                      "range names cells of other objects",
}
FROZEN = ['YK09.v']  # non-A files whose numerals belong to another image: staged, never relocated
GENERATED_DEFS = {'Tfib_const_shadow', 'Tfib_zero_shadow', 'Tfib_owned_static'}  # A/AF0m.v, YF0m.v start-up classes
ENTRY_FNS = ('LLVMFuzzerTestOneInput',)  # AB1w always emits these from the target's own symbol
ABI_ENTRY = ('main', 'LLVMFuzzerTestOneInput', 'LLVMFuzzerInitialize')  # starts paired by symbol name (ABI role)
ADDR_POS = [  # numerals that stand where an address stands: (regex, ((group, 'addr'|'lo'|'hi'), ...))
    (re.compile(r'\bANum\s+' + _V), ((1, 'addr'),)),
    (re.compile(r'\ba_off\s*:=\s*' + _V), ((1, 'addr'),)),
    (re.compile(r'\bZ_to_bv\s+64\s+\(?\s*' + _V + r'(?=\s*\)?\s*(?:%bv)?\s*:\s*word)'), ((1, 'addr'),)),
    (re.compile(r'\bmkRegion\s+\w+\s+' + _V + r'\s+' + _V), ((1, 'lo'), (2, 'hi'))),
    (re.compile(r'\bimg_rd\s+\w+\s+' + _V + r'\s+' + _V), ((1, 'lo'), (2, 'hi'))),
    # a hex interval `LO <= a < HI` (YE23.v:37's shadow disjuncts) and a chunk written `mkChunk A (CImg (E - A))`
    (re.compile(r"(0x[0-9a-fA-F]+)\s*<=\s*[\w']+\s*<\s*(0x[0-9a-fA-F]+)(?![\w]|\s*[-+*])"), ((1, 'lo'), (2, 'hi'))),
    (re.compile(r'\bCImg\s*\(\s*' + _V + r'\s*-\s*' + _V + r'\s*\)'), ((1, 'hi'), (2, 'lo'))),
    (re.compile(r'\bv_addi\s*\(\s*Z_to_bv\s+64\s+' + _V), ((1, 'addr'),)),
    # a span `LO <= v /\ v + n <= HI` (YE37.v:183 `0x7fffc1d0 <= lo /\ lo + n <= 0x8000c28c`)
    (re.compile(r"(0x[0-9a-fA-F]+)\s*<=\s*([\w']+)\s*/\\\s*\2\s*\+\s*[\w']+\s*<=\s*(0x[0-9a-fA-F]+)(?![\w]|\s*[-+*])"),
     ((1, 'lo'), (3, 'hi'))),
]
DECL = re.compile(r"^\s*(?:#\[[^\]]*\]\s*)?(?:Local\s+|Global\s+|Program\s+)?(?:Definition|Lemma|Theorem|Fixpoint|Record|"
                  r"Structure|Class|Instance|Inductive|Corollary|Fact|Remark|Let|Ltac|Example|Notation|Hypothesis|"
                  r"Variable|Parameter|Axiom|Function)\s+([A-Za-z_][\w']*)", re.M)
HEADER_CLASSES = ('bound', 'image-end', 'geometry', 'cell-bytes', 'got-word', 'got-value', 'override', 'code-end')


def ival(t):
    return int(t, 16) if t.lower().startswith('0x') else int(t)


def fmt_like(tok, v):
    """v in the radix of the token it replaces."""
    return hex(v) if tok.lower().startswith('0x') else str(v)


# the trace store's hash, Reusable/YF0p.v tfib_dhash (grant's hand values A/AF0m.v:529-530 are exactly this of its
# TFIB_TR0): a numeral equal to the hash of a pc list of its own file is a HASH by role, recomputed from the list
DH_M, DH_M8, DH_SEED = 14313749767032793493, 3829533694005038248, 10900877739976798860
PCLIST = re.compile(r'\[\s*((?:0x[0-9a-fA-F]+|port_core_refused_[0-9a-f]+)(?:\s*;\s*(?:0x[0-9a-fA-F]+|'
                    r'port_core_refused_[0-9a-f]+))*)\s*\]')


def dhash(tr):
    m64 = 2 ** 64
    mul = lambda x: (x * DH_M) % m64

    def step(h, w):
        k = mul(w)
        k = mul((k >> 47) ^ k)
        return mul(k ^ h)
    h = ((len(tr) * DH_M8) % m64) ^ DH_SEED
    for w in tr:
        h = step(h, w)
    h = mul((lambda x: (x >> 47) ^ x)(step(h, 0)))
    return (h >> 47) ^ h


def decode_result_spans(line):
    """[start, end) of each `decode_any <word> = Some ( ... )` result on a line (the parenthesised result)."""
    out = []
    for m in re.finditer(r'decode_any\b[^=;]*?=\s*Some\s*\(', line):
        depth, j = 1, m.end()
        while j < len(line) and depth:
            depth += {'(': 1, ')': -1}.get(line[j], 0)
            j += 1
        out.append((m.end(), j))
    return out


def decode_text(w):
    """`Ctor args` of a 32-bit rv64 word in the form cgif's inline decode lemmas state it (checked against every inline
    `decode_any (W%bv : bv 32) = Some (C args, 4%Z)` of cgif's lib: Lui, Auipc, Jal, Jalr, Branch, Load, Store,
    OpImm, ShiftImm, OpImm32), or None for a form it does not produce (Op, Op32, Mul, ShiftImm32, ...)."""
    op, rd, f3, rs1, rs2 = w & 0x7f, (w >> 7) & 31, (w >> 12) & 7, (w >> 15) & 31, (w >> 20) & 31
    if op == 0x37:
        return f'Lui {rd} {w >> 12}'
    if op == 0x17:
        return f'Auipc {rd} {w >> 12}'
    if op == 0x6f:
        return f'Jal {rd} {((w >> 31) & 1) << 20 | ((w >> 12) & 0xff) << 12 | ((w >> 20) & 1) << 11 | ((w >> 21) & 0x3ff) << 1}'
    if op == 0x67 and f3 == 0:
        return f'Jalr {rd} {rs1} {w >> 20}'
    if op == 0x63 and f3 in (0, 1, 4, 5, 6, 7):
        imm = ((w >> 31) & 1) << 12 | ((w >> 7) & 1) << 11 | ((w >> 25) & 0x3f) << 5 | ((w >> 8) & 0xf) << 1
        return f'Branch {("BC_EQ", "BC_NE", "", "", "BC_LT", "BC_GE", "BC_LTU", "BC_GEU")[f3]} {rs1} {rs2} {imm}'
    if op == 0x03 and f3 != 7:
        return f'Load SZ{1 << (f3 & 3)} {"false" if f3 & 4 else "true"} {rd} {rs1} {w >> 20}'
    if op == 0x23 and f3 < 4:
        return f'Store SZ{1 << f3} {rs1} {rs2} {((w >> 25) << 5) | ((w >> 7) & 31)}'
    if op == 0x13 and f3 in (1, 5):
        return f'ShiftImm {"ALU_SLL" if f3 == 1 else ("ALU_SRA" if (w >> 30) & 1 else "ALU_SRL")} {rd} {rs1} {(w >> 20) & 63}'
    if op == 0x13:
        return f'OpImm {("ALU_ADD", "", "ALU_SLT", "ALU_SLTU", "ALU_XOR", "", "ALU_OR", "ALU_AND")[f3]} {rd} {rs1} {w >> 20}'
    if op == 0x1b and f3 == 0:
        return f'OpImm32 {rd} {rs1} {w >> 20}'
    return None


def lib_const(a, name):
    """`Definition NAME : Z := N.` (N a numeral or `B ^ E`) of the target lib's or the donor's Reusable/YG0f.v."""
    for d in (a.target_lib, a.src_lib):
        for sub in ('Reusable', ''):
            p = os.path.join(d, sub, 'YG0f.v')
            if not os.path.exists(p):
                continue
            m = re.search(r'Definition\s+' + re.escape(name) + r'\s*:\s*Z\s*:=\s*(\d+)(?:\s*\^\s*(\d+))?\s*\.',
                          open(p).read())
            if m:
                return int(m.group(1)) ** int(m.group(2)) if m.group(2) else int(m.group(1))
    return None


def hash_role_values(text, dtab):
    """{numeral: (kind, pc list)} of a donor text: a 64-bit numeral equal to dhash of a hex pc list the same text
    states is a HASH; with one found, a numeral equal to that hash mod d_tab_words is its BUCKET."""
    lists = {tuple(int(x, 16) for x in re.split(r'\s*;\s*', m.group(1).strip()))
             for m in PCLIST.finditer(text) if REFUSED not in m.group(1)}
    hs = {dhash(list(t)): t for t in lists}
    nums = {ival(m.group(1)) for m in NUM.finditer(text)}
    out = {h: ('hash', t) for h, t in hs.items() if h in nums}
    if dtab:
        for h, (_, t) in list(out.items()):
            if h % dtab in nums:
                out.setdefault(h % dtab, ('bucket', t))
    return out


# ---------------------------------------------------------------- relocation
class Reloc:
    def __init__(self, a, old, new, R, look, OG, NG):
        self.a, self.old, self.new, self.R, self.look, self.OG, self.NG = a, old, new, R, look, OG, NG
        self.prog = [tuple(int(x, 16) for x in r.split(':')) for r in a.old_prog]
        self.chk, self.rev, self.fixed = [], [], []
        self.tab = collections.defaultdict(list)  # extra tables: name -> rows
        self.explained = {}   # (file, line, old value) -> status, for the symbol gate
        self.written = collections.defaultdict(set)  # (file, line, old value) -> values written there
        self.fetches = collections.defaultdict(list)  # file -> [(line, released word, the target's word)] of fetches
        self.generated = set()
        self.imgtop_users = set()  # staged non-A files whose image bounds now cite Reusable/YImgTop.v
        self.gen_defs = set()  # (file, definition) of generated start-up classes kept as slots
        self.remapped = set()
        self.refusals = []    # (file, line, old, status)
        self.stems = sorted({n[1:].replace('.', '_') if n.startswith('.') else n.replace('.', '_'): n
                             for n in OG.sec}.items(), key=lambda x: -len(x[0]))
        self.rcls = {}
        for l in open(os.path.join(a.work, 'remap.tsv')).read().split('\n')[1:]:
            r = l.split('\t')
            if len(r) >= 10:
                try:
                    self.rcls[(r[0], int(r[1]), ival(r[4]))] = (r[6], r[7], r[8], r[9])
                except ValueError:
                    pass
        self.fde_end = set(R.ohi.values())
        self.nobj = {}
        if a.target_syms:
            from resolve_code import all_syms
            for lo, hi, _ in all_syms(a.target_syms):
                self.nobj[lo] = max(hi, self.nobj.get(lo, hi))
        self.fde_lo = {hi: lo for lo, hi in R.ofn}
        self._nsl = sorted(self.nobj)
        from resolve_code import old_syms_list
        self._osl = sorted(lo for lo, _, _ in old_syms_list(a.old_syms)) if a.old_syms else []
        self._oszl = sorted({(lo, lo + n) for lo, n, _ in old_syms_list(a.old_syms) if n > 0}) if a.old_syms else []
        self.names = None
        if a.old_syms and a.target_syms:
            from resolve_code import NameMap
            self.names = NameMap(a.old_syms, a.target_syms)
        self._got_tables()
        self.ogp, self.ngp = self._gp(R.co, old), self._gp(R.cn, new)
        self.hash_role, self.file_geo_ok = {}, set()
        self.dtab = lib_const(a, 'd_tab_words')  # the trace store's bucket count (Reusable/YG0f.v: 2 ^ 20)
        self.required_extra = []  # (file, why) rows of the gates added in this release (globals counts, ...)
        self.override_lines = set()  # (file, line) an --override row changed: later passes leave the line alone
        self.twin = Elf(a.twin_image) if getattr(a, 'twin_image', None) else None  # the donor's other image
        self.twin_vals = set()

    @staticmethod
    def _gp(code, elf):
        """the global pointer the entry code sets (`auipc gp; addi gp, gp, lo`), or None."""
        e = struct.unpack_from('<Q', elf.b, 0x18)[0]
        k = code.index_of(e)
        for j in range(k or 0, (k or 0) + 6 if k is not None else 0):
            sv = code.sens[j]
            if sv and sv[0] == 'lo12' and (code.raws[j] >> 7) & 31 == 3:
                return sv[1]
        return None

    # ---- helpers
    def in_prog(self, v):
        return any(lo <= v < hi for lo, hi in self.prog)

    def is_exec(self, v):
        s = self.old.sec(v)
        return bool(s and s[2] & 4)

    TABLES = ('asan_globals', '.init_array', '.fini_array', '.preinit_array')  # per-image tables: index by offset

    def ptr_map(self, v):
        """NEW value of a pointer OLD stores (GOT content, a stored address), or None when unknown."""
        if v == 0:
            return 0
        if self.is_exec(v):
            return self.R.map_code(v)
        if self.OG.hull[0] <= v < self.OG.hull[1]:
            m = self.data_value(v)[0]
            if m is None and self.OG.by.get(v):
                vs = {self.NG.role.get(r) for r in self.OG.by[v]} - {None}
                m = vs.pop() if len(vs) == 1 else None
            return m
        return v

    def data_value(self, a):
        """(NEW address, how) of an OLD data address, from code and symbols only (never elf_symbols): the GOT word's twin,
        the value a GOT word holds, a per-image table by offset, the address paired code forms (coderef), an offset
        inside the object such an address starts (the target's symbol gives its size), the symbol of the same name
        (--old-syms), a content-checked shift of the nearest coderef. (None, None) when none applies."""
        s = self.old.sec(a)
        if s is None:
            return None, None
        gw = getattr(self, 'gotw', {})
        if s[0] == '.got' and gw.get(a & ~7) is not None:
            return gw[a & ~7] + (a & 7), 'got-word'
        gv = getattr(self, 'gotval', {})
        if a in gv and len(gv[a]) == 1:
            return next(iter(gv[a])), 'got-value'
        if s[0] == '.eh_frame':
            # inside an FDE record: the paired function's FDE record + the same offset (AE3i IMG_RO_HI 0x2f1ac ->
            # grant 0x2f6ac)
            if not hasattr(self, '_ofde'):
                from resolve_code import fde_records
                self._ofde = sorted((ra, rl, lo) for lo, (ra, rl) in fde_records(self.a.old_elf).items())
                self._nfde = fde_records(self.a.target_elf)
                self._ofa = [x[0] for x in self._ofde]
            j = bisect.bisect_right(self._ofa, a) - 1
            if j >= 0 and a <= self._ofde[j][0] + self._ofde[j][1]:
                ra, rl, lo = self._ofde[j]
                n = self.R.map_code(lo)
                if n is not None and n in self._nfde and self._nfde[n][1] == rl:
                    return self._nfde[n][0] + (a - ra), f'FDE of {lo:#x} + {a - ra:#x}'
        if s[0] in self.TABLES:
            # a per-image table is paired by CONTENT, never by index: an asan_globals descriptor (64 bytes, field 0 =
            # the global) pairs with the NEW descriptor of the global's twin; an init/fini entry with the NEW entry
            # holding the twin function. No twin: no value (refused), never the entry at the same index
            esz = 64 if s[0] == 'asan_globals' else 8
            base = s[3] + (a - s[3]) // esz * esz
            key = self.old.q(base)
            if key is None or s[0] not in self.NG.sec:
                return None, None
            tw = self.R.map_code(key) if self.is_exec(key) else (self.data_value(key)[0] if self.old.sec(key) and
                                                                   self.old.sec(key)[0] not in self.TABLES else None)
            if tw is None:
                return None, None
            nlo, nhi = self.NG.sec[s[0]]
            hits = [b for b in range(nlo, nhi, esz) if self.new.q(b) == tw]
            if len(hits) == 1:
                return hits[0] + (a - base), f'{s[0]} entry of {key:#x} (paired by content: NEW entry holds {tw:#x})'
            return None, None
        cr = self.R.cref
        if a in cr:
            return cr[a], 'coderef'
        if self.names:
            m = self.names.map(a)
            o = self.names.name_of(a) if m is not None else None
            if m is not None and not o[2].startswith('.'):
                ro = not (s[2] & 1) and s[1] != 8  # read-only and file-backed: the object's bytes must agree
                n0 = m - (a - o[0])
                sz = min(o[1] - o[0], 64)
                if not ro or self.old.read(o[0], sz) == self.new.read(n0, sz):
                    return m, 'symbol ' + o[2][:40]
        if a in self.R.jtab:
            return self.R.jtab[a][0], f'switch table {self.R.jtab[a][1]:#x} entry {self.R.jtab[a][2]}'
        ks = self.__dict__.setdefault('_crk', sorted(cr))
        i = bisect.bisect_right(ks, a) - 1
        if i >= 0 and s[3] <= ks[i] < a and s[1] != 8:
            # inside a string the code forms at k (or at its NUL): the target string at cr[k] holds the same bytes,
            # so the same offset k + j moves to cr[k] + j (AE3l 104143 = FMT_refused + 16)
            k = ks[i]
            ob = self.old.read(k, 4096) or b''
            z = ob.find(b'\0')
            if 0 < z and a - k <= z and all(32 <= x < 127 or x in (9, 10, 13) for x in ob[:z]) and \
                    self.new.read(cr[k], z + 1) == ob[:z + 1]:
                return cr[k] + (a - k), f'string {k:#x} + {a - k} (the target string holds the same bytes)'
        if i >= 0 and s[3] <= ks[i] < a:
            # inside (or one past) the OLD object holding the coderef k, when the NEW object holding cr[k] has the
            # same size and the same offset of k (BUFEND = stdout buffer + 1024)
            k = ks[i]
            n = cr[k]
            j = bisect.bisect_right(self._oszl, (k, float('inf'))) - 1
            q = bisect.bisect_right(self._nsl, n) - 1
            if j >= 0 and q >= 0:
                olo, ohi = self._oszl[j]
                nlo = self._nsl[q]
                nhi = self.nobj[nlo]
                if olo <= k < ohi and nlo <= n < nhi and a <= ohi and ohi - olo == nhi - nlo and k - olo == n - nlo:
                    return n + (a - k), (f'object {olo:#x}+{a - olo:#x} ' + ('(one past it)' if a == ohi else
                                                                             '(same size in the target)'))
        if i >= 0 and s[3] <= ks[i] < a:
            # inside (or in the trailing redzone/padding of) the object the code forms at k: the next OLD object
            # (next coderef, next recovered symbol) is past a, and the next NEW symbol is past n + (a - k)
            k = ks[i]
            n = cr[k]
            onext = min([ks[i + 1]] if i + 1 < len(ks) else [s[3] + s[5]])
            j = bisect.bisect_right(self._osl, k)
            if j < len(self._osl):
                onext = min(onext, self._osl[j])
            j = bisect.bisect_right(self._nsl, n)
            nnext = self._nsl[j] if j < len(self._nsl) else n + (a - k) + 1
            if n in self.nobj and a < onext and n + (a - k) < nnext:
                inside = a - k < self.nobj[n] - n
                return n + (a - k), f'coderef {k:#x} + {a - k:#x} ({"inside the object" if inside else "its padding"})'
        j = bisect.bisect_right(self._oszl, (a, float('inf'))) - 1
        if j >= 0 and self._oszl[j][0] <= a < self._oszl[j][1]:
            # a point of a donor object (its recovered symbol) that code forms only further in (musl's stdout buffer
            # STDOUT_BUFA, formed as buf + UNGET): the first coderef inside the object moves it, when the NEW object
            # holding that coderef's twin has the same size and the same offset (AE3m.v:32 -> grant 0x5f81e0)
            olo, ohi = self._oszl[j]
            q = bisect.bisect_left(ks, olo)
            if q < len(ks) and ks[q] < ohi:
                k = ks[q]
                n = cr[k]
                p = bisect.bisect_right(self._nsl, n) - 1
                if p >= 0:
                    nlo = self._nsl[p]
                    nhi = self.nobj[nlo]
                    if nlo <= n < nhi and nhi - nlo == ohi - olo and k - olo == n - nlo:
                        return nlo + (a - olo), f'object {olo:#x}+{a - olo:#x} (its coderef {k:#x} -> {n:#x})'
        if s[1] != 8:
            v = self.interp(a, s)
            if v is not None:
                return v, 'shift of the nearest coderef (same bytes)'
        return None, None

    def _got_tables(self):
        """GOT words: OLD word -> NEW word (by the code that loads it, else the one NEW word holding the twin of the
        OLD word's content); and the values GOT words hold: OLD held data address -> NEW held value."""
        self.gotw, held = {}, collections.defaultdict(set)
        if '.got' not in self.OG.sec or '.got' not in self.NG.sec:
            self.gotval = {}
            return
        glo, ghi = self.OG.sec['.got']
        nlo, nhi = self.NG.sec['.got']
        ncontent = collections.defaultdict(list)
        for w in range(nlo, nhi, 8):
            ncontent[self.new.q(w)].append(w)
        for g in range(glo, ghi, 8):
            co = self.old.q(g)
            exp = self.ptr_map(co) if co is not None else None
            if g in self.R.cref:
                t, how = self.R.cref[g], 'coderef'
            else:
                alts = ncontent.get(exp, []) if exp else []
                t, how = (alts[0], 'content') if len(alts) == 1 else (None, 'unresolved')
            cn = self.new.q(t) if t is not None else None
            self.gotw[g] = t
            ok = '-' if exp is None else ('same' if cn == exp else 'DIFFERS')
            lm = self.look(g)
            self.tab['got.tsv'].append(('word', hex(g), hex(co) if co is not None else '-', hex(t) if t else '-',
                                        hex(cn) if cn is not None else '-', how, ok,
                                        self.R.name_new(cn) if cn and self.new.sec(cn) else '-',
                                        '-' if lm is None else hex(lm) + ('' if lm == t else ' (differs)')))
            if co and t is not None and cn is not None and not self.is_exec(co) and \
                    self.OG.hull[0] <= co < self.OG.hull[1]:
                held[co].add(cn)
        self.gotval = held

    def def_hint(self, dn):
        """(kind, role) from a definition name: ('bound', 'sec:.got.hi'), ('end', None), ('start', None), or None."""
        if not dn:
            return None
        m = BOUND_NAME.search(dn)
        if m:
            side = m.group(2)
            for st, sec in self.stems:
                if dn == f'{st}_{side}' or dn.endswith(f'_{st}_{side}'):
                    return ('bound', f'sec:{sec}.{side}')
            for st, role in (('img', 'hull'), ('relro', 'relro'), ('tls', 'tls')):
                if dn == f'{st}_{side}' or dn.endswith(f'_{st}_{side}'):
                    return ('bound', f'{role}.{side}')
        if END_HINT.search(dn):
            return ('end', None)
        if START_HINT.search(dn):
            return ('start', None)
        return None

    def row(self, table, rel, ln, ov, nv, status):
        o = hex(ov) if isinstance(ov, int) else ov
        n = hex(nv) if isinstance(nv, int) else nv
        (self.chk if table == 'ok' else self.rev).append((rel, ln, o, n, status))
        if table == 'ok' and isinstance(ov, int) and status.split(' ')[0] in HEADER_CLASSES:
            self.explained[(rel, ln, ov)] = status

    def refuse(self, rel, ln, ov, nv, status):
        self.rev.append((rel, ln, hex(ov), hex(nv) if isinstance(nv, int) else nv, status))
        self.refusals.append((rel, ln, hex(ov), status.split(' ')[0]))
        kind = status.split(' ')[0]
        if kind in ('code-no-counterpart', 'code-end-no-twin', 'old-program-block'):
            f = self.R._fn_of(ov - 1 if kind == 'code-end-no-twin' else ov)
            nm = self.R.oname.get(f[0], '-') if f else '-'
            self.tab['no-twin.tsv'].append((rel, ln, hex(ov), kind, f'{f[0]:#x}' if f else '-', nm))
        return f'{REFUSED}{ov:x}'

    # ---- per literal
    def decide(self, c):
        """c: dict(rel, ln, line, ov, nv, tok, ntok, dn, olds, hex). Returns the new token text, or None to keep."""
        if not c['remapped']:
            return self.decide_hex(c) if c['hex'] else None  # only the image end moves (decide_hex's first branch)
        if c.get('label'):
            # the allocator model's pcs are opaque labels (YG0d's amreal ignores ISpin's pc; FCheck is a failure tag);
            # a decode_any result is a function of its instruction word (a field of it), never an address: when the
            # word changes, regen_decode recomputes the result by decoding the new word
            dec = c['label'] == 'decode_any result'
            self.tab['decimals.tsv'].append(('excluded', c['rel'], c['ln'], c['ov'], '-', hex(c['ov']), '-',
                                             'a decode_any result (a field of the word)' if dec else
                                             f'opaque label: argument of {c["label"]}', '-'))
            self.explained[(c['rel'], c['ln'], c['ov'])] = 'insn-word' if dec else 'opaque label'
            return c['tok'] if c['ntok'] != c['tok'] else None  # the donor's label / word, whatever remap wrote
        if c['dn'] in GENERATED_DEFS and c['remapped']:
            # a generated start-up class inside a relocated file: the released numerals stay (a named slot), the
            # definition is regenerated from the unit's start-up collector
            self.gen_defs.add((c['rel'], c['dn']))
            self.explained[(c['rel'], c['ln'], c['ov'])] = 'generated slot'
            return c['tok'] if c['ntok'] != c['tok'] else None
        if c['remapped'] and c['ov'] >= 0x1000 and self.model_const(c['dn'], c['ov']):
            return self.refuse(c['rel'], c['ln'], c['ov'], c['nv'], f'ambiguous-model-constant (the name or the value '
                               f'is a model constant of {self.model_const(c["dn"], c["ov"])}: state it per unit)')
        if c['dn'] in PER_UNIT_DEFS and c['ov'] >= 0x10000 and c['remapped']:
            return self.refuse(c['rel'], c['ln'], c['ov'], c['nv'], f'per-unit-definition ({c["dn"]}: '
                               f'{PER_UNIT_DEFS[c["dn"]]})')
        if c['ov'] in self.hash_role:
            # a HASH by role (the trace store's hash of a pc list of this file, or its bucket): never an address;
            # hash_roles() recomputes it from the relocated list after the pass. A definition NAME never decides it
            # (AB1w's StackDepotNode_store_hash_helper is a code address and pairs as one)
            self.explained[(c['rel'], c['ln'], c['ov'])] = 'per-image hash'
            return c['tok'] if c['ntok'] != c['tok'] else None
        p = c.get('prev')
        if p is not None and c['remapped'] and not c.get('label'):
            # a size right after its start: (BASE, SIZE) of a section, a page-rounded segment or a PT_LOAD
            sizes = {}
            for r in self.OG.by.get(p, []):
                m = re.fullmatch(r'sec:(.+)\.lo', r)
                if m and m.group(1) in self.NG.sec:
                    nm = m.group(1)
                    sizes[f'size of {nm}'] = (self.OG.sec[nm][1] - self.OG.sec[nm][0], self.NG.sec[nm][1] - self.NG.sec[nm][0])
                m = re.fullmatch(r'seg(\d+)\.base', r)
                if m and f'seg{m.group(1)}.size' in self.NG.dec:
                    k = f'seg{m.group(1)}.size'
                    sizes[k] = (self.OG.dec[k], self.NG.dec[k])
                m = re.fullmatch(r'load(\d+)\.lo', r)
                if m and int(m.group(1)) < len(self.NG.loads):
                    i = int(m.group(1))
                    (lo, fh, mh), (nlo, nfh, nmh) = self.OG.loads[i], self.NG.loads[i]
                    sizes[f'load{i}.filesz'] = (fh - lo, nfh - nlo)
                    sizes[f'load{i}.memsz'] = (mh - lo, nmh - nlo)
            if SHADOW <= p < SHADOW + (self.OG.hull[1] >> 3):
                # a shadow window (SH(lo), n) of a section: n = the section's size / 8 (YE37.v:54 `(0x8000c55c, 24)`
                # of asan_globals 0xc0 -> fm's 0x400 / 8 = 128)
                for r in self.OG.by.get((p - SHADOW) << 3, []):
                    m = re.fullmatch(r'sec:(.+)\.lo', r)
                    if m and m.group(1) in self.NG.sec:
                        nm = m.group(1)
                        sizes[f'shadow size of {nm}'] = ((self.OG.sec[nm][1] - self.OG.sec[nm][0]) >> 3,
                                                         (self.NG.sec[nm][1] - self.NG.sec[nm][0]) >> 3)
            hit = {(k, nw) for k, (ol, nw) in sizes.items() if ol == c['ov']}
            if len({nw for _, nw in hit}) == 1:
                k, n = sorted(hit)[0]
                self.tab['geometry.tsv'].append((c['rel'], c['ln'], c['tok'], fmt_like(c['tok'], n), f'{k} (after its start)'))
                self.explained[(c['rel'], c['ln'], c['ov'])] = 'geometry'
                if n != c['nv']:
                    self.row('ok', c['rel'], c['ln'], c['ov'], n, f'geometry {k} (after its start)')
                    return fmt_like(c['tok'], n)
                return None
        if c['hex']:
            return self.decide_hex(c)
        cls, st, _, note = self.rcls.get((c['rel'], c['ln'], c['ov']), ('', '', '', ''))
        if c['ov'] >= 0x10000 and 'as geometry' not in note and (
                c.get('addr_pos') or 'in an address field' in note or cls == 'auipc-result?'
                or (c['nv'] != c['ov'] and cls not in ('geometry', 'derived', 'section-end', 'page-index', 'size',
                                                       'constant'))
                or (c.get('cell_value_pos') and self.exact(c['ov']))):
            # a decimal where an address stands, or a stored value that IS an OLD address, or one remap moved: the
            # address rules decide it, unless its CONTEXT says it is no address (a nat, the bound of a length /
            # count comparison, an interval bound whose partner is no address, an argument the callee names a length
            # or fuel): grant's drain set (fuel 100000, bound 127070, length 262728 moved as string / code interiors)
            why = '' if c.get('addr_pos') or self.exact(c['ov']) else self.const_context(c)
            if why:
                return self.keep_decimal(c, why)
            return self.decide_hex(c)
        return self.decide_dec(c)

    def keep_decimal(self, c, why):
        rel, ln, D = c['rel'], c['ln'], c['ov']
        self.tab['decimals.tsv'].append(('excluded', rel, ln, D, '-', hex(D), '-', why, '-'))
        self.explained[(rel, ln, D)] = 'excluded decimal'
        if c['ntok'] != c['tok']:
            self.row('ok', rel, ln, D, D, f'decimal-kept ({why}; remap had written {c["ntok"]})')
            return c['tok']
        return None

    LEN_WORD = re.compile(r"\b(?:z?len\w*|length|size\w*|count\w*|cnt|nbytes)\b", re.I)
    LEN_PARAM = re.compile(r"^(?:len|length|n|fuel|size|sz|cnt|count|nbytes|bytes)$", re.I)
    LABEL_PARAM = re.compile(r"^(?:stag|tag|label|lbl)$", re.I)  # a callee's opaque-label parameter

    def const_context(self, c):
        """why the CONTEXT of a decimal says it is no address, or '': a nat; the upper bound of a comparison whose
        other side is a length / count (`zlen t < 100000`, `length (...) < 100000`); an interval bound whose partner is
        no address (`2 <= TOT <= 127070`); an argument the callee's own parameter names a length or fuel (A/AFfg.v
        `do_stretch HS 42%nat 0xe7fc0 262728 ...` -> Ltac do_stretch HS k d len ...; YG00.v pop_batches (fuel : nat))."""
        line, s, e = c['line'], c['start'], c['end']
        if re.search(r':\s*nat\s*:=\s*$', line[:s]) or line[e:].startswith('%nat'):
            return 'a nat (fuel, a count)'
        pre = line[:s]
        m = re.search(r'(<=?\??)\s*$', pre)
        if m:
            left = left_operand(pre[:m.start()])
            if self.LEN_WORD.search(left):
                return f'the bound of a length / count comparison ({left.strip()[-40:]} {m.group(1)} N)'
            mm = re.search(r"(0x[0-9a-fA-F]+|\d+)\s*<=?\s*[\w']+\s*$", left)
            if mm and ival(mm.group(1)) < 0x10000:
                return f'an interval bound whose partner {mm.group(1)} is no address'
        arg = self.callee_param(line, s)
        if arg:
            return arg
        return ''

    def callee_param(self, line, s):
        """'argument P of F' when the numeral at s is the k-th explicit argument of F, a lib Ltac / Definition /
        Fixpoint / Lemma whose k-th parameter is named like a length or fuel or is typed nat; else ''."""
        sig = self.signatures()
        n = len(line)
        for m in re.finditer(r"(?<![\w'.])([A-Za-z_][\w']*)\s+", line[:s]):
            f = m.group(1)
            if f not in sig:
                continue
            k, j = 0, m.end()
            while j < n:
                while j < n and line[j] == ' ':
                    j += 1
                if j >= n or line[j] in ';),]}.' and not (line[j] == '.' and j + 1 < n and line[j + 1].isdigit()):
                    break  # the application ends
                st0 = j
                if line[j] in '([':
                    depth = 0
                    while j < n:
                        depth += {'(': 1, '[': 1, ')': -1, ']': -1}.get(line[j], 0)
                        j += 1
                        if depth == 0:
                            break
                else:
                    while j < n and line[j] not in ' ()[];,':
                        j += 1
                if re.fullmatch(r"<=?\??|>=?|=|<>|->|<->|/\\|\\/|\+|-|\*|/|&&|\|\||:=|with|in|by|=>|\|", line[st0:j]):
                    break  # an infix operator ends the application
                if st0 == s:
                    if k < len(sig[f]):
                        nm, ty = sig[f][k]
                        if self.LEN_PARAM.match(nm) or re.fullmatch(r'\s*nat\s*', ty or ''):
                            return f'argument {nm} of {f}'
                        if self.LABEL_PARAM.match(nm):
                            return f'opaque label: argument {nm} of {f}'
                    break
                if st0 > s:
                    break
                k += 1
        return ''

    def signatures(self):
        """{name: [(param, type)]} of the donor lib's Ltac, Definition, Fixpoint and Lemma heads (explicit binders)."""
        if hasattr(self, '_sig'):
            return self._sig
        sig = {}
        lt = re.compile(r"(?:Local\s+)?Ltac\s+([A-Za-z_][\w']*)\s+([A-Za-z_][\w'\s]*?)\s*:=")
        df = re.compile(r"(?:Definition|Fixpoint|Lemma|Theorem)\s+([A-Za-z_][\w']*)\s*((?:\([^()]*\)\s*)+)[:{]")
        for root, _, fs in os.walk(self.a.src_lib):
            for f in fs:
                p = os.path.join(root, f)
                if not f.endswith('.v') or os.path.getsize(p) > 1 << 21:
                    continue  # (a data blob of megabytes declares no Ltac / lemma heads worth reading)
                t = open(p, errors='replace').read()
                if 'Ltac' not in t and '(' not in t:
                    continue
                for m in lt.finditer(t):
                    sig.setdefault(m.group(1), [(p, None) for p in m.group(2).split()])
                for m in df.finditer(t):
                    ps = []
                    for b in re.finditer(r'\(([^()]*)\)|\{[^{}]*\}', m.group(2)):
                        if b.group(1) is None:
                            continue
                        names, _, ty = b.group(1).partition(':')
                        ps += [(p, ty) for p in names.split()]
                    if ps:
                        sig.setdefault(m.group(1), ps)
        self._sig = sig
        return sig

    def model_const(self, dn, v):
        """the file of a model constant (`Definition N : Z := V.` of Reusable/YG0f.v or an AsanCtrl module) whose
        NAME this literal defines, or whose VALUE it is where no bound or geometry role explains it: such a value is
        the model's, not the image's, and is refused rather than relocated (pcap's FS_FROFF 0x109000). A value that
        is also a bound of the image, the shadow offset, or below 0x10000 is the image's and the rules decide it."""
        if not hasattr(self, '_mc'):
            self._mc, self._mcv = {}, {}
            for d in (self.a.src_lib, self.a.target_lib):
                for sub in ('', 'Reusable'):
                    for nm in ('YG0f.v', 'AsanCtrl.v'):
                        p = os.path.join(d, sub, nm)
                        if not os.path.exists(p):
                            continue
                        for m in re.finditer(r"Definition\s+([A-Za-z_][\w']*)\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+|\d+)\s*\.",
                                             open(p).read()):
                            self._mc[m.group(1)] = nm
                            self._mcv[ival(m.group(2))] = nm
        return self._mc.get(dn)  # by NAME only: on grant a value-only match refuses 100 of the image's own sizes
        # and bounds (0x800000, 0x7fff7000, 0x100000, 0xb09000), so a value match is left to the other rules

    def exact(self, v):
        """v is exactly an OLD identity: a bound, a function start, a trampoline, a coderef target, a value a GOT
        word holds, or the start of a named object."""
        if self.OG.by.get(v) or v in self.R.ohi or v in self.R.tramp or v in self.R.entries or v in self.R.cref \
                or v in self.gotval:
            return True
        o = self.names.name_of(v) if self.names else None
        return bool(o and o[0] == v)

    def twin_differs(self, v):
        """the donor's two images differ at the place v would denote (v, or for a shadow address the granule it
        shadows): a different section or section start there, or different file bytes."""
        if self.twin is None:
            return False
        hl, hh = self.OG.hull
        p = v if hl <= v < hh else ((v - SHADOW) << 3 if SHADOW + (hl >> 3) <= v < SHADOW + (hh >> 3) else None)
        if p is None:
            return False
        so, st = self.old.sec(p), self.twin.sec(p)
        if so is None or st is None:
            return (so is None) != (st is None)
        if so[0] != st[0] or so[3] != st[3]:
            return True
        bo, bt = self.old.read(p, 8), self.twin.read(p, 8)
        return bo is not None and bt is not None and bo != bt

    def twin_file_values(self, rel):
        """the numerals of this file's other-image twin in the donor (A/A<x>.v <-> Y<x>.v), or an empty set."""
        if self.twin is None or AS_TWIN:
            return set()  # (under --as-twin the twin of a staged Y file is its own source)
        b = os.path.basename(rel)
        if rel.startswith('A/') and b.startswith('A'):
            p = os.path.join(self.a.src_lib, 'Y' + b[1:])
        elif b.startswith('Y'):
            p = os.path.join(self.a.src_lib, 'A', 'A' + b[1:])
        else:
            return set()
        if not os.path.exists(p):
            return set()
        return {ival(m.group(1)) for m in NUM.finditer(strip_comments(open(p).read())) if m.group(1).startswith('0x')}

    def object_value(self, ov):
        """the code/data reading of an OLD address inside a section (without writing anything)."""
        if self.is_exec(ov):
            return self.R.map_code(ov)
        return self.data_value(ov)[0]

    def decide_hex(self, c):
        rel, ln, ov, nv, line = c['rel'], c['ln'], c['ov'], c['nv'], c['line']
        if ov < 0x10000:
            return None
        if OPCODE_CTX.match(line, c['end']) or OPCODE_PRE.search(line, 0, c['start']) or WORD32.fullmatch(c['tok']) \
                or (not c.get('addr_pos') and ov & 3 == 3 and ov < 2 ** 32 and (self.is_exec(ov) or self.in_prog(ov))):
            # an instruction word (`0x...%bv : bv 32`, `Z_to_bv 32 0x...`, `0x0...` padded to 8 digits): not an
            # address. remap sometimes rewrites one as if it were: write the released word back.
            self.explained[(rel, ln, ov)] = 'insn-word'
            if nv != ov:
                self.fixed.append((rel, ln, hex(ov), hex(nv), hex(ov), 'instruction word'))
                self.row('ok', rel, ln, ov, ov, f'insn-word-restored (remap had written {nv:#x})')
                return c['tok']
            return None
        nona = not rel.startswith('A/') and not y_twin(os.path.basename(rel), self.a.src_lib)
        if not c['remapped'] or (nona and c['hex'] and rel not in self.generated):
            if rel in self.generated:
                return None  # a per-image generated file: a slot, regenerated from the start-up collector
            # a non-A file (shared, or per-image under --kernel-dir: YCbq / YCe5 on the asan-ubsan side): its image
            # bounds cite the unit's own YImgTop.v of the file's own dir (IMG_LO, IMG_TOP: parsing-only notations),
            # so the text carries no image constant (the asan-ubsan side as the asan side does: the hand-written twins
            # 7a4e49d47fb lib/B/Reusable/YCbq.v:794, YCe5.v:673); every other image constant it holds is listed in
            # nonA.tsv
            if ov == self.OG.hull[1] or (ov == self.OG.hull[0] and self.OG.hull[1] in c['olds']):
                name = 'IMG_TOP' if ov == self.OG.hull[1] else 'IMG_LO'
                self.row('ok', rel, ln, ov, self.NG.hull[1] if name == 'IMG_TOP' else self.NG.hull[0],
                         f'image-end (non-A file: {name} of its own dir\'s YImgTop.v)')
                self.explained[(rel, ln, ov)] = 'image-end'
                self.imgtop_users.add(rel)
                return name
            if not c['remapped']:
                return None
        cls, st, rnew, note = self.rcls.get((rel, ln, ov), ('', '', '', ''))
        olds_h = [v for v in c['olds'] if v != ov]
        droles = [r for r in self.OG.dby.get(ov, []) if r in self.NG.dec]
        if cls in ('derived', 'section-end') and nv != ov:
            if not droles or any(self.geo_used(r, line, olds_h) for r in droles) or self.OG.by.get(ov):
                self.row('ok', rel, ln, ov, nv, f'geometry (remap {cls}, from the headers: {note[:80]})')
                return None
            self.row('rev', rel, ln, ov, ov, f'geometry-ungated (remap read {ov:#x} as {",".join(droles)}; the line '
                     f'states no such geometry: the donor value is kept)')
            return c['tok']
        for role in ('hull.hi/8', 'hull.size/8', 'hull.size'):  # image geometry before any symbol reading
            if ov == self.OG.dec[role] and not self.OG.by.get(ov) and self.geo_used(role, line, olds_h):
                self.tab['geometry.tsv'].append((rel, ln, hex(ov), hex(self.NG.dec[role]), role, ''))
                return self.put(c, self.NG.dec[role], f'geometry {role}')
        so = self.old.sec(ov)
        roles = self.OG.by.get(ov, [])
        hint = self.def_hint(c['dn'])
        if ov == self.ogp and self.ngp is not None and (re.search(r'(?:^|_)gp(?:_|$)', c['dn'] or '', re.I)
                                                        or not c.get('addr_pos')):
            # the source's global pointer (the value its entry code sets) is the gp ROLE wherever it stands outside an
            # address position (AD23 / AD2f vm_compute lemmas: grant 0x10800, not a string end 0x107f8)
            return self.put(c, self.ngp, 'bound gp (the global pointer the target\'s entry code sets)')
        if is_map_flags(ov) and not c.get('addr_pos') and not self.exact(ov) and not roles:
            # a sum of MAP_* constants (0x104022 = MAP_FIXED_NOREPLACE | MAP_NORESERVE | MAP_ANONYMOUS | MAP_PRIVATE,
            # `lui a0,0x104; addiw a3,a0,0x22` before internal_mmap): NOT an address, kept (scene moved it to
            # 0x101822 / 0x1018a2 at six sites per image: AFkn 922 / 1213 / 1222 / 1231, AFk8 101, AFk9 114 x2)
            self.row('ok', rel, ln, ov, ov, 'not-an-address (mmap flags: a sum of MAP_* constants)')
            self.explained[(rel, ln, ov)] = 'constant'
            return c['tok'] if nv != ov else None
        if cls in ('constant', 'size') and not c.get('addr_pos') and not self.exact(ov) and not roles:
            # remap reads a constant here (mmap flags 0x104022) and no address role says otherwise: a value inside
            # an object is not moved because it lands there (grant AFk8 / AFk9 / AFkn: 0x104022 -> 0x102b62)
            self.row('ok', rel, ln, ov, ov, f'constant-kept (remap class {cls}; no address role)')
            self.explained[(rel, ln, ov)] = 'constant'
            return c['tok'] if nv != ov else None
        hl_, hh_ = self.OG.hull
        if ov in self.twin_vals and not self.exact(ov) and not roles and not (hint and hint[0] == 'bound') and \
                ov % PAGE == 0 and SHADOW + (hl_ >> 3) <= ov < SHADOW + (hh_ >> 3) and self.twin_differs(ov):
            # KEPT-TWIN-EQUAL: a page-aligned SHADOW bound the donor states identically in this file and in its
            # other-image twin (A/A<x>.v and Y<x>.v), while the two donor images differ at the granule it would
            # denote, and no name or bound role claims it: it is image-independent (cgif's CZONE shadow bound
            # 0x80050000 in AFhn / AFix / AFjb / AFju / AFkm / AFkz; ctrl moved it to 0x80050510). Narrower than
            # "any twin-equal numeral": A/AB1w.v tfib_rodata_hi 0x2278c (cgif asan .rodata end - 0x40 = cgif
            # asan-ubsan .rodata end; grant 0x22c0c), A/AE23.v:35's 0x7fffc1c4 / 0x7fffc1cc (the shadow of cgif's
            # .rodata globals, at the same place in both donor images) and YB1k's fetch pcs are twin-equal too, and
            # per image
            self.row('ok', rel, ln, ov, ov, 'KEPT-TWIN-EQUAL (the same shadow address in both donor twins; the two '
                     'donor images differ at the granule it would denote)')
            self.explained[(rel, ln, ov)] = 'kept twin-equal'
            return c['tok'] if nv != ov else None
        # 1. bounds, from the target's headers
        if hint and hint[0] == 'bound' and not roles and hint[1] in self.NG.role:
            ob = self.OG.role.get(hint[1])
            # the donor's own convention: its released bound sits a fixed distance from the section bound (cgif's
            # rodata_hi 0x2278c = .rodata end - 0x40, text_hi 0x9ca00 = .text end + 4); the target keeps that offset
            d = ov - ob if ob is not None and abs(ov - ob) < 0x1000 else 0
            b = self.NG.role[hint[1]] + d
            self.row('rev', rel, ln, ov, b, f'bound-released-elsewhere ({c["dn"]} names {hint[1]} = OLD {ob or 0:#x}, '
                     f'the released value {ov:#x} is {d:+#x} from it; wrote NEW {hint[1]} {d:+#x})')
            self.explained[(rel, ln, ov)] = 'bound-released-elsewhere'
            return self.put(c, b, 'bound')
        if roles:
            cands = {r: self.NG.role.get(r) for r in roles}
            vals = {v for v in cands.values() if v is not None}
            pick = hint[1] if hint and hint[0] == 'bound' and hint[1] in roles else None
            b = cands[pick] if pick else (next(iter(vals)) if len(vals) == 1 else None)
            m = self.object_value(ov) if (so is not None and pick is None) else None
            if m is not None and not self.NG.hull[0] <= m <= self.NG.hull[1]:
                m = None  # an object reading outside the target image (knock AD1l.v:128: 0x0 for .data's end) is none
            if b is not None and (m is None or m == b):
                tag = f'bound {pick or ",".join(roles)}'
                if hint and hint[0] == 'bound' and not pick:
                    self.row('rev', rel, ln, ov, b, f'bound-name-mismatch ({c["dn"]} names {hint[1]}, the value is '
                             f'OLD {",".join(roles)}; wrote NEW {",".join(roles)})')
                    self.explained[(rel, ln, ov)] = 'bound'
                return self.put(c, b, tag)
            if b is not None:
                self.row('rev', rel, ln, ov, m, f'bound-or-object (OLD {",".join(roles)} -> {b:#x}; the object '
                         f'reading gives {m:#x}; wrote the object reading)')
                return self.put(c, m, None)
            if m is not None:
                self.row('rev', rel, ln, ov, m, 'bound-ambiguous (' + ', '.join(f'{r} -> {v:#x}' if v is not None
                         else f'{r} -> none' for r, v in cands.items()) + '; wrote the object reading)')
                return self.put(c, m, None)
            return self.refuse(rel, ln, ov, nv, 'bound-ambiguous (' + ', '.join(
                f'{r} -> {v:#x}' if v is not None else f'{r} -> none' for r, v in cands.items()) + ')')
        # 2. outside every OLD section
        if so is None:
            in_sh = SHADOW + (self.OG.hull[0] >> 3) <= ov <= SHADOW + (self.OG.hull[1] >> 3)
            if cls in ('shadow', 'tls-shadow') or (in_sh and c.get('addr_pos') in ('lo', 'hi')):
                # a shadow byte address (0x7fff8000 + a/8) of image a: remap's class, or an interval bound in the
                # image's shadow that remap left unclassified (YE23.v:37's end 0x8000c574)
                end = c.get('addr_pos') == 'hi' or 'end of a half-open interval' in note or 'interval end' in note
                if end:
                    # an END of a shadow window: the shadow of a BOUND's end goes by that bound's role (fmb2 YE23.v:37
                    # 0x8000c574 = SH(asan_globals end) -> fm's 0x8000bd34), never by the last descriptor's twin
                    ge = (ov - SHADOW) << 3
                    vs = {self.NG.role.get(r) for r in self.OG.by.get(ge, [])} - {None}
                    if len(vs) == 1:
                        b = vs.pop()
                        return self.put(c, SHADOW + ((b + 7) >> 3), f'shadow end (SH of OLD bound {ge:#x} '
                                        f'{",".join(self.OG.by[ge])} -> NEW {b:#x})')
                g = ((ov - 1 if end else ov) - SHADOW) << 3
                m = None
                for k in range(8):  # the granule's first byte that maps, moved by a multiple of 8
                    rs = self.OG.by.get(g + k, [])
                    vs = {self.NG.role.get(r) for r in rs} - {None}
                    x = vs.pop() if len(vs) == 1 else self.object_value(g + k)
                    if x is not None:
                        m = x - k if (x - (g + k)) % 8 == 0 else None
                        break
                ob16 = self.old.read(g, 16) if m is None else None
                if ob16 and len(set(ob16)) >= 3 and ob16 == self.new.read(g, 16) and self.old.sec(g)[0] == \
                        (self.new.sec(g) or ('',))[0]:
                    m = g  # no rule moves the granule and the target holds the same 16 bytes there: it stays
                if m is not None:
                    v = SHADOW + (m >> 3) + (1 if end else 0)
                    return self.put(c, v, f'shadow (granule of OLD {g:#x} -> NEW {m:#x})')
                if st == 'review' and ov == nv:
                    self.row('rev', rel, ln, ov, nv, f'shadow-unmoved (remap: {note[:100]})')
                    return None
                return self.refuse(rel, ln, ov, nv, f'shadow-unmapped (granule of OLD {g:#x}: no code-derived map '
                                   f'moves it by a multiple of 8; remap: {st})')
            if ov != nv:
                self.row('rev', rel, ln, ov, nv, 'outside-image-moved')
            return None
        # 3. code
        if so[2] & 4 or self.in_prog(ov):
            if cls in ('geometry', 'size', 'constant', 'derived', 'page-index', 'section-end', 'image-pad'):
                if ov == nv:
                    self.row('rev', rel, ln, ov, nv, f'code-unmoved (remap: {cls})')
                elif droles and not self.OG.by.get(ov) and not any(self.geo_used(r, line, olds_h) for r in droles):
                    self.row('rev', rel, ln, ov, ov, f'geometry-ungated (remap read {ov:#x} as {",".join(droles)}; the '
                             f'line states no such geometry: the donor value is kept)')
                    return c['tok']
                else:
                    self.row('ok', rel, ln, ov, nv, f'geometry (remap {cls}: {note[:80]})' if cls in
                             ('geometry', 'derived', 'section-end', 'page-index') else f'code-kept-remap ({cls})')
                return None
            return self.decide_code(c, cls, st, note)
        # 4. data
        return self.decide_data(c, so, cls, st, note)

    def put(self, c, v, tag):
        """write v at this literal (fixed.tsv when it differs from remap's), record an ok row with tag."""
        rel, ln, ov, nv = c['rel'], c['ln'], c['ov'], c['nv']
        if tag:
            self.row('ok', rel, ln, ov, v, tag)
        if v != nv:
            self.fixed.append((rel, ln, hex(ov), hex(nv), hex(v), self.R.name_new(v) if self.new.sec(v) else '-'))
            return fmt_like(c['tok'], v)
        return None

    def end_context(self, c, cls, note):
        """'end', 'start' or None for a code literal. A range START is a function start (it pairs by the start of
        the same function); only a range END takes the end rule."""
        ov = c['ov']
        if c.get('addr_pos') == 'lo' or 'start of a half-open interval' in note:
            return 'start'
        if c.get('addr_pos') == 'hi' or 'end of a half-open interval' in note or 'interval end' in note \
                or 'one past' in note:
            return 'end'
        h = self.def_hint(c['dn'])
        if h and h[0] in ('end', 'start'):
            return h[0]
        st, en = ov in self.R.ohi, ov in self.fde_end
        if en and not st:
            return 'end'
        if st and not en:
            return 'start'
        return None

    def decide_code(self, c, cls, st, note):
        rel, ln, ov, nv = c['rel'], c['ln'], c['ov'], c['nv']
        R = self.R
        r = R.map_code(ov)
        abi = None
        if r is None and ov in R.ohi and R.oname.get(ov) in ABI_ENTRY:
            # the C runtime's / the fuzzer driver's entry (main, LLVMFuzzerTestOneInput): its ROLE is fixed by the ABI,
            # so the donor's start names the target's function of the same symbol (AD28.v:23 `SLit 524272` = cgif's
            # main -> grant's main 524816), never a stream twin
            hits = [lo for lo, ns in R.nnames.items() if R.oname[ov] in ns and lo in R.nhi]
            if len(hits) == 1:
                r = abi = hits[0]
        e0 = R.map_code(ov - 1)
        e = e0 + 1 if e0 is not None else None
        ctx = self.end_context(c, cls, note)
        if e is None and ctx == 'end':
            # the function that ends here, by its FDE or by the start the same line states: its start's twin (a
            # call-paired start, or the code right after the previous twin) + its length, when that NEW code is
            # this OLD function moved
            los = [self.fde_lo[ov]] if ov in self.fde_lo else []
            los += [s for s in c['olds'] if s < ov <= s + 0x100000 and self.is_exec(s) and s not in los]
            for lo in los:
                s = R.map_code(lo)
                if s is None:
                    p = R.map_code(lo - 1)
                    s = p + 1 if p is not None else None
                if s is not None and R.same_fn_at(lo, ov, s, lo12_tolerant=True):
                    e = s + (ov - lo)
                    break
        prog = self.in_prog(ov)
        if ctx == 'end':
            if e is None:
                return self.refuse(rel, ln, ov, nv, f'code-end-no-twin (the function that ends here has no twin'
                                   f'{"; next function start " + hex(r) if r is not None else ""})')
            v, tag = e, 'code-end'
        elif ctx == 'start':
            if r is None and ov in R.ohi and e is not None and R.same_fn_at(ov, R.ohi[ov], e):
                r = e  # unpaired only because nothing else names it: the code right after the previous twin is it
            if r is None:
                return self.refuse(rel, ln, ov, nv, 'old-program-block' if prog else
                                   'code-no-counterpart (this function has no twin in the target)')
            v, tag = r, 'code-entry' if ov in R.entries and R._fn_map(ov) is None else 'code'
        else:
            if r is not None and (e is None or e == r):
                v, tag = r, 'code-entry' if ov in R.entries and R._fn_map(ov) is None else 'code'
            elif r is None and e is not None and ov in self.fde_end:
                if ov in R.ohi and not R.same_fn_at(ov, R.ohi[ov], e):
                    return self.refuse(rel, ln, ov, nv, f'code-no-counterpart (starts a function with no twin; the '
                                       f'end of the function before it would be {e:#x})')
                v, tag = e, 'code-end'
            elif r is None and e is None:
                if prog:
                    return self.refuse(rel, ln, ov, nv, 'old-program-block')
                if ov == nv and st == 'unmappable':
                    return self.refuse(rel, ln, ov, nv, f'code-no-counterpart (remap: {note[:80]})')
                partner = [x for x in c['olds'] if x != ov and self.is_exec(x) and R.map_code(x) not in (None, x)]
                if ov in R.ohi and partner:
                    # a donor function start with no twin beside a code partner that moves (AD28.v:23 `SLit 524272`
                    # beside `SLit 577284` -> 567036): never left at the donor's value
                    return self.refuse(rel, ln, ov, nv, f'code-no-counterpart (a donor function start with no twin; '
                                       f'its line partner {partner[0]:#x} moves)')
                self.row('rev', rel, ln, ov, nv, 'code-unpaired' if ov != nv else 'code-unmoved')
                return None
            else:
                return self.refuse(rel, ln, ov, nv, f'code-end-or-start (end rule {"-" if e is None else hex(e)}, '
                                   f'next function start {"-" if r is None else hex(r)})')
        # symbol identity: the donor function's recovered name must name the target function the value lands in
        f = R._fn_of(ov - 1 if tag.endswith('code-end') else ov)
        on = R.oname.get(f[0]) if f else None
        if on and not prog:
            nlo = R.map_code(f[0])
            nn = R.nnames.get(nlo) if nlo is not None else None
            from resolve_code import stem
            if nn and stem(on) not in {stem(x) for x in nn}:
                return self.refuse(rel, ln, ov, nv, f'symbol-identity (donor {on} would land in target '
                                   f'{"/".join(sorted(nn))})')
        if prog:
            tag = 'program-block-paired ' + tag
        if abi is not None and v == abi:
            tag = f'code-abi-entry (the target\'s own {R.oname[ov]} by its symbol)'
        out = self.put(c, v, None)
        if tag.endswith('code-end') or abi is not None and v == abi:
            self.row('ok', rel, ln, ov, v, tag)
        else:
            io, inw = insn_at(self.old, ov), insn_at(self.new, v)
            ok = (io and inw and io[1] == inw[1] and mask_insn(*io) == mask_insn(*inw)) if ov % 2 == 0 else \
                R.map_code(ov & ~1) == v - 1  # a byte inside an instruction: the instruction moves with it
            self.row('ok' if ok else 'rev', rel, ln, ov, v, (tag + ' same' if ok else 'code-DIFFERS ' + tag)
                     if tag != 'code' else ('code-same' if ok else 'code-DIFFERS'))
        return out

    def word_ok(self, ov, nv):
        """the target holds the same bytes, or the same pointers (8- or 4-byte words, moved by the maps)."""
        bo, bn = self.old.read(ov, 8), self.new.read(nv, 8)
        if bo is None or bn is None:
            return False
        if bo == bn:
            return True
        if len(bo) == 8 and len(bn) == 8:
            m = self.ptr_map(struct.unpack('<Q', bo)[0])
            if m is not None and m == struct.unpack('<Q', bn)[0]:
                return True
            hs = [(struct.unpack_from('<I', bo, i)[0], struct.unpack_from('<I', bn, i)[0]) for i in (0, 4)]
            return all(x == y or self.ptr_map(x) == y for x, y in hs)
        return False

    def interp(self, ov, so):
        """a file-backed OLD datum no map names: the shift of the nearest coderef'd address of the same section,
        accepted only when the 8 bytes (or up to the section end) agree there."""
        lo, hi = so[3], so[3] + so[5]
        ks = self.__dict__.setdefault('_crk', sorted(self.R.cref))
        i = bisect.bisect_left(ks, ov)
        bo = self.old.read(ov, 8)
        if not bo or len(set(bo)) < 3:
            return None  # padding or a run of one byte matches anywhere: no evidence
        for j in (i - 1, i, i - 2, i + 1):
            if 0 <= j < len(ks) and lo <= ks[j] < hi and abs(ks[j] - ov) <= 0x400:
                v = ov + self.R.cref[ks[j]] - ks[j]
                if self.new.read(v, len(bo)) == bo:
                    return v
        return None

    def decide_data(self, c, so, cls, st, note):
        rel, ln, ov, nv = c['rel'], c['ln'], c['ov'], c['nv']
        if so[0] == '.got':
            gend = c.get('addr_pos') == 'hi' or 'end of a half-open interval' in note or 'interval end' in note
            b = (ov - 1) if gend else ov  # an interval end closes the word before it
            t = self.gotw.get(b & ~7)
            if t is None:
                return self.refuse(rel, ln, ov, nv, 'got-word-unresolved (no code loads it and its content names no '
                                   'unique NEW word)')
            v = t + (b & 7) + (1 if gend else 0)
            co, cn = self.old.q(b & ~7), self.new.q(t)
            exp = self.ptr_map(co) if co is not None else None
            out = self.put(c, v, None)
            if exp is None or exp == cn:
                self.row('ok', rel, ln, ov, v, f'got-word (holds {cn:#x})' if cn is not None else 'got-word')
            else:
                self.row('rev', rel, ln, ov, v, f'got-word-content-DIFFERS (OLD holds {co:#x} -> expected {exp:#x}, '
                         f'NEW holds {cn:#x})')
            return out
        w = self.old.q(ov) if so[1] != 8 and ov % 8 == 0 else None
        if w and self.is_exec(w) and self.R.map_code(w) is None:
            # the cell holds a pointer to a function the target does not link (REAL(fopen) on a unit with no fopen):
            # the cell has no counterpart; never the slot of another function (ctrl put FF_got_fopen on real_fflush's)
            return self.refuse(rel, ln, ov, nv, f'data-holds-unpaired-function (OLD {ov:#x} holds {w:#x}, which '
                               f'has no twin in the target)')
        if ov in self.gotval:
            vs = self.gotval[ov]
            if len(vs) == 1:
                v = next(iter(vs))
                words = [hex(g) for g, t in self.gotw.items() if self.old.q(g) == ov]
                self.tab['got.tsv'].append(('value', c['rel'], c['ln'], hex(ov), hex(v), ' '.join(words)))
                return self.put(c, v, f'got-value (held by GOT {" ".join(words)})')
            return self.refuse(rel, ln, ov, nv, 'got-value-ambiguous (' + ' '.join(hex(x) for x in sorted(vs)) + ')')
        if cls in ('geometry', 'derived', 'section-end', 'page-index') and (nv != ov or st == 'mapped'):
            droles = [r for r in self.OG.dby.get(ov, []) if r in self.NG.dec]
            olds_h = [v for v in c['olds'] if v != ov]
            if droles and not self.OG.by.get(ov) and not any(self.geo_used(r, c['line'], olds_h) for r in droles):
                self.row('rev', rel, ln, ov, ov, f'geometry-ungated (remap read {ov:#x} as {",".join(droles)}; the '
                         f'line states no such geometry: the donor value is kept)')
                return c['tok']
            self.row('ok', rel, ln, ov, nv, f'geometry (remap {cls}, from the headers: {note[:80]})')
            return None
        gm = re.search(r'as geometry \(mapped -> (0x[0-9a-f]+|\d+)\)', note) if cls == 'auipc-result?' else None
        if gm:
            droles = [r for r in self.OG.dby.get(ov, []) if r in self.NG.dec]
            olds_h = [x for x in c['olds'] if x != ov]
            if droles and not any(self.geo_used(r, c['line'], olds_h) for r in droles):
                self.row('rev', rel, ln, ov, ov, f'geometry-ungated (remap read the auipc-result? value {ov:#x} as '
                         f'{",".join(droles)}; the line states no such geometry: the donor value is kept)')
                return c['tok']
            v = ival(gm.group(1))
            self.tab['geometry.tsv'].append((rel, ln, hex(ov), hex(v), 'remap geometry reading', note[:80]))
            return self.put(c, v, 'geometry (remap: the auipc-result? value read as geometry)')
        if ov in self.R.cref_conflict:
            return self.refuse(rel, ln, ov, nv, 'coderef-conflict (' + ' '.join(
                f'{k:#x}x{n}' for k, n in self.R.cref_conflict[ov].items()) + ')')
        end = c.get('addr_pos') == 'hi' or 'end of a half-open interval' in note or 'interval end' in note
        if end and ov not in self.R.cref:
            e, how = self.data_value(ov - 1)
            if e is not None:  # one past an object: the end moves with the object it closes
                ob, nb = self.old.read(ov - 4, 4), self.new.read(e + 1 - 4, 4)
                if so[1] != 8 and ob and nb and ob != nb:
                    # the bytes the end closes differ: the end would cross into a neighbour (its redzone)
                    return self.refuse(rel, ln, ov, nv, f'chunk-end-crosses (the end reading {e + 1:#x} by {how} '
                                       f'does not close the same bytes in the target)')
                out = self.put(c, e + 1, None)
                self.row('ok', rel, ln, ov, e + 1, f'data-end ({how} of {ov - 1:#x}, + 1)')
                return out
        v, how = self.data_value(ov)
        if v is None:
            length = bool(re.search(r'\bCImg\s*\(?\s*$', c['line'][:c['start']]))
            if so[1] != 8 and end and not length:
                pb = self.old.read(ov - 16, 16)
                if pb and len(pb) == 16 and len(set(pb)) >= 3 and pb == self.new.read(ov - 16, 16):
                    # an END closes the bytes BEFORE it: the target holds the same 16 bytes there (cgif -> cgif keeps
                    # AE3i's chunk ends; a8's 0x20dcd closes another global's tail in scene: refused)
                    return self.put(c, ov, 'data-end-same-place (the target holds the same bytes the end closes)')
            same16 = self.old.read(ov, 16)
            if so[1] != 8 and not end and not length and same16 and len(set(same16)) >= 3 and \
                    same16 == self.new.read(ov, 16):
                # the same bytes at the same place: a START or a plain address only, and only over bytes that say
                # something (16 bytes of at least 3 distinct values: zero fill or a redzone is the same everywhere;
                # grant A -> B: YF0m.v:234 cell 0xa1248 over zeros, right 0xa20a8). An interval END or a
                # length field says nothing about the bytes at it (a8 AU/YE3i.v:33's chunk end 0x20dcd)
                return self.put(c, ov, 'data-same-place (the target holds the same bytes there)')
            lm = self.look(ov)
            if c.get('soft'):
                self.row('rev', rel, ln, ov, nv, f'decimal-unmapped (in OLD {so[0]}: no rule; kept)')
                return None
            return self.refuse(rel, ln, ov, nv, f'data-no-rule (in OLD {so[0]}: no code forms it, no symbol names '
                               f'it{"; elf_symbols would give " + hex(lm) if lm is not None else ""})')
        if ov % PAGE == 0 and v % PAGE and not c.get('addr_pos') and how != 'coderef' \
                and not how.startswith(('got-', 'table', 'switch')) and not (how.startswith('symbol') and self.exact(ov)):
            d = self.OG.dby.get(ov, [])
            vs = {self.NG.dec.get(k) for k in d} - {None}
            if len(vs) == 1:
                g = vs.pop()
                self.tab['geometry.tsv'].append((rel, ln, hex(ov), hex(g), ','.join(d)))
                return self.put(c, g, f'geometry {",".join(d)}')
            self.row('rev', rel, ln, ov, nv, f'data-unmoved (page-aligned; {how} gives {v:#x}: a size or a page '
                     f'bound, not decided)')
            return None
        out = self.put(c, v, None)
        self.check_data(c, ov, v, so, how)
        return out

    def check_data(self, c, ov, v, so, how):
        rel, ln = c['rel'], c['ln']
        pre = f'{how} ' if how else ''
        if so[1] == 8 or so[0] == '.tbss':
            self.row('ok', rel, ln, ov, v, pre + 'nobits')
        elif ov in self.R.jtab and self.R.jtab[ov][0] == v:
            self.row('ok', rel, ln, ov, v, pre + 'data-same (switch table entry)')
        elif self.word_ok(ov, v):
            self.row('ok', rel, ln, ov, v, pre + 'data-same')
        else:
            self.row('rev', rel, ln, ov, v, pre + 'data-DIFFERS')

    # ---- decimals
    def seg_context(self, line, olds, i):
        lo, fh, _ = self.OG.loads[i]
        bs, en = self.OG.segs[i]
        if any(v in (lo, fh, bs, en) for v in olds):
            return True
        return re.search(r'seg(?:ment)?(?:_bytes)?_?0*%d(?![0-9])|tfib_len%d(?![0-9])|segments_reserved|_segs\b'
                         % (i, i), line, re.I) is not None

    def geo_used(self, role, line, olds, local=False):
        """the USE GATE: a value equal to a geometry role is that role only when the same line states the geometry it
        belongs to (a segment's base / end / file-high bound, its size or zero-fill offset / length, a segment list,
        `seg_bytes_00N`, `tfib_lenN` for a segment size; an image name, a hull bound or the shadow of one for the hull
        roles; `.bss` for the .bss offsets). A bare 131072 is a 2^17 size far more often than segment 0's length
        (scene: 62 of 74 such moves were wrong). The hull roles (the image top, its size, their /8, the shadow of the
        top) are distinctive values: one also passes when ANOTHER line of the same file states it with the geometry
        (a8 A/AF0s.v:83 `HF1 : 6270976 <= ly_F ly` follows :80's ZONE; the proof needs both moved)."""
        s = strip_comments(line)
        m = re.match(r'seg(\d+)\.(\w+)', role)
        if m:
            i = int(m.group(1))
            if i >= len(self.NG.segs):
                return False
            if re.search(r'seg(?:ment)?_bytes_?0*%d(?![0-9])|tfib_(?:len|hex|rom)%d(?![0-9])|segments_reserved'
                         % (i, i), s, re.I):
                return True
            lo, fh, _ = self.OG.loads[i]
            bs, en = self.OG.segs[i]
            if m.group(2) in ('basepage', 'endpage'):
                # a PAGE INDEX (16, 48: tiny values) only beside page arithmetic or its partner page index (knock
                # A/AFfd.v:207 `t_stats + 48` is a struct offset on a line that also holds seg0's base 65536)
                pp = {self.OG.dec.get(f'seg{i}.basepage'), self.OG.dec.get(f'seg{i}.endpage')} - {None}
                return bool(re.search(r'4096|\bPAGE|[Pp]age|>>\s*12|<<\s*12', s)) or any(v in pp for v in olds)
            if m.group(2) != 'size':
                # a bound of segment i: another bound of it, or its size / zero-fill offset / length beside it
                # (AB13.v:83 `(643072 <=? x) && (x + 1 <=? 643072 + 8192)`: seg2's base and size)
                own = {lo, fh, bs, en} | {self.OG.dec[f'seg{i}.{k}'] for k in ('size', 'zoff', 'zlen')
                                          if f'seg{i}.{k}' in self.OG.dec}
                return any(v in own for v in olds)
            # a SIZE: its base written beside it (`base + size`, `(base, size)`) or the segment's end / file-high
            # bound on the line; a bare base that is also a power of two (65536 = 2^16 beside 2^17) is not enough
            v = self.OG.dec[role]
            forms = lambda x: r'(?:%s|%s)' % (x, hex(x))
            if re.search(forms(bs) + r'\s*[+,]\s*\(?\s*' + forms(v) + r'(?![\w])', s):
                return True
            return any(x in (fh, en) for x in olds if x != bs)
        if role.startswith('hull.') or role in ('shadow(hull.hi)',):
            hl, hh = self.OG.hull
            near = {hl, hh, SHADOW, 0x7fff7000, 0x8fff7000, SHADOW + (hl >> 3), SHADOW + (hh >> 3)} | \
                {self.OG.dec[r] for r in ('hull.hi', 'hull.hi/8', 'hull.size', 'hull.size/8')}
            if re.search(r'(?i)img|image|IMG_TOP|kImg|off_img|shadow', s) or any(x in near for x in olds):
                return True
            return not local and role in self.file_geo_ok
        if role == 'bss.segoff':
            return bool(re.search(r'(?i)bss', s)) or self.OG.sec.get('.bss', (0,))[0] in olds
        return True

    HULL_ROLES = ('hull.hi', 'hull.hi/8', 'hull.size', 'hull.size/8', 'hull.hi-bss', 'shadow(hull.hi)')

    def file_geo_roles(self, lines):
        """the hull roles some line of this (donor) file states with its geometry (the file-level use gate)."""
        ok = set()
        want = {self.OG.dec[r]: r for r in self.HULL_ROLES if r in self.OG.dec}
        for l in lines:
            vs = [ival(m.group(1)) for m in NUM.finditer(l)]
            for v in set(vs) & want.keys():
                if want[v] not in ok and self.geo_used(want[v], l, [x for x in vs if x != v], local=True):
                    ok.add(want[v])
        return ok

    def decide_dec(self, c):
        rel, ln, D, nv, line = c['rel'], c['ln'], c['ov'], c['nv'], c['line']
        if not c['remapped'] or D < 2:
            return None
        olds = [v for v in c['olds'] if v != D]
        cls, st, rnew, note = self.rcls.get((rel, ln, D), ('', '', '', ''))
        roles = [r for r in self.OG.dby.get(D, []) if r in self.NG.dec]
        if cls in ('geometry', 'derived', 'section-end') and nv != D:
            # remap's header-derived value: kept only when the line USES that geometry (the use gate)
            if not roles or any(self.geo_used(r, line, olds) for r in roles):
                self.explained[(rel, ln, D)] = 'geometry'
                self.tab['geometry.tsv'].append((rel, ln, str(D), str(nv), f'remap {cls}', note[:80]))
                return None
            self.row('rev', rel, ln, D, D, f'geometry-ungated (remap read {D} as {",".join(roles)} -> {nv}; the line '
                     f'states no such geometry: the donor value is kept)')
            self.explained[(rel, ln, D)] = 'ungated geometry kept'
            return c['tok']
        for role in ('hull.hi/8', 'hull.size/8', 'hull.size', 'hull.hi', 'hull.hi-bss', 'bss.segoff'):
            if role in self.OG.dec and role in self.NG.dec and D == self.OG.dec[role] and \
                    self.NG.dec[role] != nv and self.geo_used(role, line, olds):
                self.explained[(rel, ln, D)] = 'geometry'
                self.tab['geometry.tsv'].append((rel, ln, str(D), str(self.NG.dec[role]), role, ''))
                self.row('ok', rel, ln, D, self.NG.dec[role], f'geometry-decimal {role}')
                return str(self.NG.dec[role])
        g, why = None, None
        m = re.search(r'as geometry \((?:mapped|review) -> (0x[0-9a-f]+|\d+)\)', note) if cls == 'auipc-result?' else None
        if m and (not roles or any(self.geo_used(r, line, olds) for r in roles)):
            g, why = ival(m.group(1)), 'remap geometry reading of an auipc-result? value'
        if g is None and D == self.OG.dec['hull.page']:
            g, why = self.NG.dec['hull.page'], 'hull.page (image-end page index)'
        if g is None and D in self.OG.dby:
            for role in self.OG.dby[D]:
                if role in self.NG.dec and role != 'hull.page' and self.geo_used(role, line, olds):
                    g, why = self.NG.dec[role], role
                    break
        if g is None:
            sm = re.match(r'(.+)_count$', c['dn'] or '')
            if sm and sm.group(1) in c['starts']:
                S = c['starts'][sm.group(1)]
                g, why = self.fn_count(S, D, c)
                if g is None:
                    g, why = self.word_count(S, D)
        if g is not None:
            if g != nv:
                self.tab['geometry.tsv'].append((rel, ln, str(D), str(g), why, f'remap wrote {nv}'))
                self.row('ok', rel, ln, D, g, f'geometry-decimal {why}')
                self.explained[(rel, ln, D)] = 'geometry'
                return str(g)
            if g != D:
                self.explained[(rel, ln, D)] = 'geometry'
            return None
        if roles and nv != D:
            # a geometry value the gate did not accept, moved by remap anyway: the donor value stays
            self.row('rev', rel, ln, D, D, f'geometry-ungated ({",".join(roles)}; the line states no such geometry: '
                     f'the donor value is kept)')
            self.explained[(rel, ln, D)] = 'ungated geometry kept'
            return c['tok']
        # class 10: a decimal inside the source image is an address unless it is excluded by name; it is mapped by the
        # same rules as a hex literal (soft: a data value with no rule is a review row, not a refusal) and reported
        if D < self.OG.hull[0] or D >= self.OG.hull[1] or not self.old.sec(D):
            return None
        for k in (8, 4):  # a value DERIVED from an address (TFIB_DEPOT / 4, a witness / 8): recomputed from the base
            if self.exact(D * k):
                m = self.object_value(D * k)
                if m is not None and m % k == 0:
                    self.tab['decimals.tsv'].append(('derived', rel, ln, D, m // k, hex(D), hex(m // k),
                                                     f'{D * k:#x} / {k}', '-'))
                    return self.put(c, m // k, f'derived address/{k} ({D * k:#x} -> {m:#x})')
        role = self.dec_role(D, c)
        # the context first (a nat, a length / count bound, an argument the callee names a length or fuel), then the
        # value rules; a STRONG role (an identity, an address position, the same value in hex in the file) overrides
        # the weak value rules (an offset operand, a difference, a power of two, a page multiple: AD24.v:45
        # `0 + 683224 + i` is the .bss object 0xa6cd8 the file also writes in hex)
        excl = self.const_context(c) or self.dec_excluded(D, cls, c, strong=role and not role.startswith('within'))
        if excl:
            return self.keep_decimal(c, excl)
        c['soft'] = True
        t = self.decide_hex(c)
        mv = ival(t) if t and not t.startswith(REFUSED) else (None if t else nv)
        why = role
        self.tab['decimals.tsv'].append(('mapped' if t and not t.startswith(REFUSED) else
                                         ('refused' if t else 'kept'), rel, ln, D,
                                         '-' if mv is None else mv, hex(D), '-' if mv is None else hex(mv),
                                         why or '-', self.R.name_new(mv) if mv and self.new.sec(mv) else '-'))
        return t

    def dec_excluded(self, D, cls, c, strong=False):
        """why a decimal inside the image is NOT an address, by rule (not by value), or ''. With a STRONG role the
        weak value rules (an offset operand, a difference, a power of two, a page multiple) do not apply."""
        if self.OG.by.get(D):
            return ''  # a bound: the bound rule maps it
        line, s = c['line'], c['start']
        if D & 3 == 3 and D < 2 ** 32 and (self.is_exec(D) or self.in_prog(D)):
            return 'instruction word (low bits 11 in code: an rv64g encoding, never an instruction address)'
        if cls in ('size', 'constant'):
            return f'remap class {cls}'
        if re.search(r':\s*nat\s*:=\s*$', line[:s]) or line[c['end']:].startswith('%nat'):
            return 'a nat (fuel, a count)'
        if strong:
            return ''
        if re.search(r'\bSOff\s+\S+\s+$', line[:s]):
            return 'an offset operand (SOff r N)'
        if re.search(r'[\w)\']\s*\+\s*$', line[:s]):
            return 'an offset operand (X + N)'
        lo = self.OG.hull[0]
        if any(o - p == D or p - o == D for o in c['olds'] for p in c['olds'] if o != D and p != D and o >= lo and p >= lo):
            return 'the difference of two addresses on the line (a size)'
        pcs = D in self.R.ohi and any(x != D and self.is_exec(x) and x >= 0x10000 for x in c['olds'])
        if pcs:
            return ''  # a donor function start beside another code address: a stored pc (AD28.v:23), not a size
        if any(abs(D - (1 << k)) <= 64 for k in range(16, 33)):
            return 'a power of two or next to one (a size)'
        if D % PAGE == 0:
            return 'a page multiple that is no bound (a size)'
        return ''

    def dec_role(self, D, c, depth=0):
        """the ADDRESS ROLE of a decimal in the image, or '': an identity (a bound, a function start, a trampoline, a
        call-paired entry, a coderef target, a value a GOT word holds, the start of a named object), an address
        position (ANum, a_off, `Z_to_bv 64 D : word`, a region bound, a cell address, `v_addi (Z_to_bv 64 D)`), the same
        value written in hex in the file, or within 8 of a numeral on the line that has one of those (a pc beside its
        partner: `v_addi (Z_to_bv 64 410032) 4` with 410036)."""
        if self.exact(D):
            return 'an identity (bound, function start, coderef target, named object)'
        if depth == 0 and c.get('addr_pos'):
            return f'an address position ({c["addr_pos"]})'
        if hex(D) in c['filehex']:
            return 'the file writes it in hex'
        if depth == 0:
            for x in c['olds']:
                if x != D and abs(x - D) <= 8 and self.old.sec(x) and self.dec_role(x, c, 1):
                    return f'within {abs(x - D)} of {x}, which has an address role'
        return ''

    def fn_count(self, S, D, c):
        """a (start, COUNT) pair over a WHOLE function (A/AB1v.v tfibguard_start / _count: D = the number of
        instructions of the donor function starting at S): the count is emitted from the TARGET's function at the
        start's twin (identity's oft_exit_guard 0x80694: 12 instructions, cgif's 4). A changed count is a review row
        (a unit's walks may fetch fewer; grant's 4 is sound over its own bytes). (None, None) when D does not count
        the whole donor function or the start has no twin."""
        R = self.R

        def n_insns(code, lo, hi):
            i, j = code.index_of(lo), code.index_of(hi)
            return None if i is None else (j if j is not None else len(code.pcs)) - i
        if S not in R.ohi or n_insns(R.co, S, R.ohi[S]) != D:
            return None, None
        Sn = R.map_code(S)
        if Sn is None or Sn not in R.nhi:
            return None, None
        n = n_insns(R.cn, Sn, R.nhi[Sn])
        if n is None:
            return None, None
        if n != D:
            self.row('rev', c['rel'], c['ln'], D, n, f'count-changed (the whole function at {S:#x} has {D} '
                     f'instructions in the donor, its twin at {Sn:#x} has {n}: emitted from the target; check that the '
                     f'unit\'s walks fetch no more than this)')
        return n, f'whole-function count ({S:#x}: {D} -> twin {Sn:#x}: {n} instructions)'

    def word_count(self, S, D):
        """`X_count` words from `X_start` S: Y = S + 4D; NEW count = (Y' - S') / 4, with Y' by the pairing or, past
        the end of S's section, NEW section end + the same distance."""
        Sn = self.R.map_code(S)
        if Sn is None:
            return None, None
        Y = S + 4 * D
        Yn = self.R.map_code(Y) if self.is_exec(Y) else None
        how = 'pairing'
        if Yn is None:
            for n, (lo, hi) in self.OG.sec.items():
                if lo <= S < hi and hi <= Y < hi + 64 and n in self.NG.sec:
                    Yn, how = self.NG.sec[n][1] + (Y - hi), f'NEW {n} end + {Y - hi}'
                    break
        if Yn is None or (Yn - Sn) % 4:
            return None, None
        return (Yn - Sn) // 4, f'word count ({S:#x} + 4*{D} = {Y:#x}; NEW end by {how})'

    # ---- cells
    def cell_value(self, c, addr_new, n):
        """A cell `(A, n, V)` whose V is OLD's file bytes at A: V becomes the target's bytes at A'. Returns
        (handled, new token)."""
        rel, ln, V, Vcur = c['rel'], c['ln'], c['ov'], c['nv']
        A = c['cell_addr']
        ob = self.old.q(A, n)
        if ob is None or ob != V or addr_new is None:
            return False, None  # not file-backed, or a runtime value: the ordinary rules decide
        nb = self.new.q(addr_new, n)
        if nb is not None and (OPCODE_CTX.match(c['line'], c['end']) or WORD32.fullmatch(c['tok'])):
            self.fetches[rel].append((ln, V, nb))  # a decode lemma pairs with the nearest fetch of its word before it
        jt = A in self.R.jtab
        if nb is None:
            return True, self.refuse(rel, ln, V, Vcur, f'cell-not-file-backed (OLD {A:#x} -> NEW {addr_new:#x})')
        tag = 'cell-bytes' + (' (switch table entry)' if jt else '')
        self.tab['cells.tsv'].append((rel, ln, hex(A), hex(addr_new), n, hex(V), hex(nb), 'written' if nb != Vcur
                                      else 'same', 'switch-table' if jt else ''))
        if nb != Vcur:
            self.fixed.append((rel, ln, hex(V), hex(Vcur), hex(nb), f'bytes at {addr_new:#x}'))
            self.row('ok', rel, ln, V, nb, tag)
            if nb != V and (OPCODE_CTX.match(c['line'], c['end']) or WORD32.fullmatch(c['tok'])):
                self.row('rev', rel, ln, V, nb, f'insn-word-changed (the target\'s word at {addr_new:#x}; decode '
                         f'lemmas over it are regenerated from this word)')
            return True, fmt_like(c['tok'], nb) if not WORD32.fullmatch(c['tok']) else f'0x{nb:08x}'
        if V >= 0x10000 or nb != V:
            self.row('ok', rel, ln, V, nb, tag)
        return True, None

    def regen_decode(self, outdir):
        """a fetched word the cell rule changed (a pc-relative jal / branch / auipc whose distance differs in the target,
        a lo12 that moved) and its decode lemma `decode_any (W%bv : bv 32) = Some (C args, 4%Z)` are regenerated
        TOGETHER: the result is a function of the word, so the lemma takes the target's word and the result DECODED
        from it (decode_text). Regenerated only when decode_text reproduces the released result from the released
        word and decodes the new word to the same constructor; otherwise the lemma is refused (its word becomes a
        refusal name)."""
        rx = re.compile(r'decode_any\s*\(\s*(0x[0-9a-fA-F]+)%bv\s*:\s*bv\s+32\s*\)\s*=\s*Some\s*\(\s*(\w+)\s+([^,]*?)\s*,'
                        r'\s*4%Z\s*\)')
        for rel, fl in self.fetches.items():
            if all(v == nb for _, v, nb in fl):
                continue
            p = os.path.join(outdir, rel)
            t = open(p).read().split('\n')
            for i, l in enumerate(t):
                for m in reversed(list(rx.finditer(l))):
                    w0 = int(m.group(1), 16)
                    # the decode lemma's own fetch: the nearest fetch of the same released word at or before it (the
                    # same word fetched elsewhere may hold another word in the target: scene AB1k D_02c)
                    near = [nb for ln, v, nb in fl if v == w0 and ln <= i + 1]
                    if not near or near[-1] == w0:
                        continue
                    w1 = near[-1]
                    d0, d1 = decode_text(w0), decode_text(w1)
                    said = f'{m.group(2)} {" ".join(m.group(3).split())}'
                    if d0 == said and d1 and d1.split()[0] == m.group(2):
                        new = f'decode_any (0x{w1:08x}%bv : bv 32) = Some ({d1}, 4%Z)'
                        self.row('ok', rel, i + 1, w0, w1, f'decode-regenerated ({d1} decoded from the target\'s '
                                 f'word)')
                        self.explained[(rel, i + 1, w0)] = 'insn-word'
                    else:
                        new = l[m.start():m.start(1)] + f'{REFUSED}{w0:x}' + l[m.end(1):m.end()]
                        self.refuse(rel, i + 1, w0, w1, f'decode-lemma-to-restate ({said} over a word the target '
                                    f'changed to {w1:#x}, which decodes to {d1 or "a form this tool does not state"})')
                    l = l[:m.start()] + new + l[m.end():]
                t[i] = l
            open(p, 'w').write('\n'.join(t))

    # ---- the pass
    def run(self, stage, outdir, remapped):
        self.remapped = remapped
        for root, _, fs in os.walk(stage):
            for f in sorted(fs):
                if f.endswith('.v'):
                    self.file(os.path.relpath(os.path.join(root, f), stage), stage, outdir, remapped)

    def file(self, rel, stage, outdir, remapped):
        ot = open(os.path.join(stage, rel)).read().split('\n')
        nt = open(os.path.join(outdir, rel)).read().split('\n')
        if len(ot) != len(nt):
            self.rev.append((rel, 0, '-', '-', 'line-count-changed'))
            return
        text = '\n'.join(ot)
        starts = {m.group(1): ival(m.group(2)) for m in
                  re.finditer(r'Definition\s+(\w+)_start\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+)', text)}
        filehex = {t.lower() for t in re.findall(r'0x[0-9a-fA-F]+', text)}
        linehex = [[int(t, 16) for t in re.findall(r'0x[0-9a-fA-F]+', l)] for l in ot]
        rm = rel in remapped
        self.hash_role = hash_role_values(text, self.dtab) if rm else {}
        self.file_geo_ok = self.file_geo_roles(ot) if rm else set()
        self.twin_vals = self.twin_file_values(rel) if rm else set()
        cruns = comment_runs(text)  # numerals inside comments are never decided (restore_comments puts them back)
        dn_carry, changed = None, False
        for ln, (ol, nl) in enumerate(zip(ot, nt), 1):
            om, nm = list(NUM.finditer(ol)), list(NUM.finditer(nl))
            defs = sorted([(m.start(), m.group(1)) for m in DEF.finditer(ol)] +
                          [(m.start(1), m.group(1)) for m in FIELD.finditer(ol)])
            if len(om) != len(nm):
                self.rev.append((rel, ln, '-', '-', 'literal-count-changed'))
                dn_carry = defs[-1][1] if defs else dn_carry
                continue
            if not om:
                dn_carry = defs[-1][1] if defs else dn_carry
                continue
            pos = {m.start(): i for i, m in enumerate(om)}
            cells = {}  # value token index -> (address token index, size)
            apos = {}   # token index -> 'addr' | 'lo' | 'hi'
            labels = {pos[s]: f for s, f in label_starts(ol).items() if s in pos}
            dres = decode_result_spans(ol)
            for k, m in enumerate(om):  # a decode_any result: fields of the instruction word, never an address
                if any(a <= m.start() < b for a, b in dres):
                    labels[k] = 'decode_any result'
            for rx, gs in ADDR_POS:
                for m in rx.finditer(ol):
                    for g, kind in gs:
                        if pos.get(m.start(g)) is not None:
                            apos[pos[m.start(g)]] = kind
            for rx, ga, gn, gv in CELLS:
                for m in rx.finditer(ol):
                    ia, iv = pos.get(m.start(ga)), pos.get(m.start(gv))
                    if ia is not None and iv is not None:
                        cells[iv] = (ia, int(m.group(gn)) if gn > 0 else -gn)
            olds = [ival(m.group(1)) for m in om]
            final, subs = {}, {}
            order = [i for i in range(len(om)) if i not in cells] + sorted(cells)
            incom = {i for i, m in enumerate(om) if any(x <= m.start() < y for x, y in cruns[ln - 1])}
            for i in order:
                if i in incom:
                    if nm[i].group(1) != om[i].group(1):
                        subs[i] = om[i].group(1)
                    final[i] = ival(om[i].group(1))
                    continue
                mo, mn = om[i], nm[i]
                dn = dn_carry
                for p, n in defs:
                    if p < mo.start():
                        dn = n
                c = dict(rel=rel, ln=ln, line=ol, ov=olds[i], nv=ival(mn.group(1)), tok=mo.group(1), ntok=mn.group(1),
                         start=mo.start(), end=mo.end(), dn=dn, olds=olds, hex=mo.group(1).lower().startswith('0x'),
                         remapped=rm, starts=starts, filehex=filehex,
                         near_hex=[v for k in range(max(0, ln - 4), min(len(ot), ln + 3)) for v in linehex[k]],
                         cell_addr_pos=any(ia == i for ia, _ in cells.values()),
                         addr_pos=apos.get(i, 'addr' if any(ia == i for ia, _ in cells.values()) else None),
                         cell_value_pos=i in cells, label=labels.get(i) if rm else None,
                         prev=olds[i - 1] if i > 0 else None)
                t = None
                if i in cells and rm:
                    ia, n = cells[i]
                    c['cell_addr'] = olds[ia]
                    an = final.get(ia)
                    handled, t = self.cell_value(c, an, n)
                    if not handled:
                        t = self.decide(c)
                else:
                    t = self.decide(c)
                if t is not None:
                    subs[i] = t
                v = t if t is not None else mn.group(1)
                final[i] = ival(v) if re.fullmatch(r'0x[0-9a-fA-F]+|\d+', v) else None
                self.written[(rel, ln, olds[i])].add(final[i] if final[i] is not None else
                                                     ('REFUSED' if v.startswith(REFUSED) else v))
            if subs:
                for i in sorted(subs, reverse=True):
                    nl = nl[:nm[i].start()] + subs[i] + nl[nm[i].end():]
                nt[ln - 1] = nl
                changed = True
            dn_carry = defs[-1][1] if defs else dn_carry
        if changed:
            open(os.path.join(outdir, rel), 'w').write('\n'.join(nt))


# ---------------------------------------------------------------- after the pass
def apply_overrides(a, stage, out, X):
    """--override FILE: lines `file<TAB>line<TAB>old<TAB>new[<TAB>occurrence]` (hex or decimal), applied to stage-out
    after the relocation pass. `old` is the RELEASED value at that line (the numeral is replaced at the position the
    released text holds it, whatever the pass wrote there, a refusal name included), else a literal text of
    stage-out's line. OCCURRENCE (1-based, counted along the line among the numerals equal to `old`, or among the
    places the literal text occurs; a comma list `1,2` names several) picks which copies change: a row whose `old`
    occurs more than once on its line and gives no OCCURRENCE is REFUSED (a FAIL row `override-ambiguous`), never
    applied to every copy. Each line is reported in overrides.tsv as applied, NOT-FOUND, AMBIGUOUS or BAD-OCCURRENCE.
    Returns (applied, covered, fails)."""
    covered = set()
    if not a.override:
        return 0, covered, 0
    rows = []
    for p in a.override:
        for l in open(p):
            f = l.split('#')[0].rstrip('\n').split('\t')
            if len(f) >= 4:
                # a 5th column is OCCURRENCE only when it is a 1-based number or a comma list of them (other tables
                # carry a free-text note there: pcap's overrides.in)
                occ = [int(x) for x in f[4].split(',')] if len(f) >= 5 and re.fullmatch(r'\s*\d+(?:\s*,\s*\d+)*\s*',
                                                                                         f[4]) else None
                rows.append((f[0].strip(), int(f[1]), f[2].strip(), f[3].strip(), occ))
    tok = re.compile(r"port_core_refused_[0-9a-f]+|(?<![A-Za-z0-9_'.])(?:0x[0-9a-fA-F]+|\d+)(?![0-9A-Za-z_])")
    n = nbad = 0
    with open(os.path.join(a.work, 'overrides.tsv'), 'w') as log:
        log.write('file\tline\told\tnew\toccurrence\tstatus\n')
        for rel, ln, old, newv, occ in rows:
            o_s = '' if occ is None else ','.join(map(str, occ))
            p = os.path.join(out, rel)
            if not os.path.exists(p):
                log.write(f'{rel}\t{ln}\t{old}\t{newv}\t{o_s}\tNO-FILE\n'); continue
            lines = open(p).read().split('\n')
            sl = open(os.path.join(stage, rel)).read().split('\n')
            l = lines[ln - 1] if ln - 1 < len(lines) else ''
            spans = None  # the places `old` stands on the stage-out line, in line order
            if re.fullmatch(r'0x[0-9a-fA-F]+|\d+', old) and ln - 1 < len(sl):
                so, no = list(tok.finditer(sl[ln - 1])), list(tok.finditer(l))
                if len(so) == len(no):
                    hit = [(no[i].start(), no[i].end()) for i, m in enumerate(so) if ival(m.group(0)) == ival(old)]
                    spans = hit or None
            if spans is None and old:
                spans = [(m.start(), m.end()) for m in re.finditer(r'(?<![A-Za-z0-9_\'.])' + re.escape(old) +
                                                                    r'(?![0-9A-Za-z_])', l)] or None
            if spans is None:
                log.write(f'{rel}\t{ln}\t{old}\t{newv}\t{o_s}\tNOT-FOUND\n'); continue
            if occ is None and len(spans) > 1:
                log.write(f'{rel}\t{ln}\t{old}\t{newv}\t{o_s}\tAMBIGUOUS ({len(spans)} occurrences: give the '
                          f'OCCURRENCE column)\n')
                row = (rel, ln, old, newv, f'FAIL override-ambiguous ({old} occurs {len(spans)} times on the line; '
                                           f'the row needs a 5th column OCCURRENCE, 1-based)')
                X.rev.append(row); X.chk.append(row); nbad += 1
                continue
            if occ is not None and not all(1 <= k <= len(spans) for k in occ):
                log.write(f'{rel}\t{ln}\t{old}\t{newv}\t{o_s}\tBAD-OCCURRENCE (the line holds {len(spans)})\n')
                row = (rel, ln, old, newv, f'FAIL override-ambiguous (OCCURRENCE {o_s}: the line holds {old} '
                                           f'{len(spans)} times)')
                X.rev.append(row); X.chk.append(row); nbad += 1
                continue
            for k in sorted(set(occ or [1]), reverse=True):
                st, en = spans[k - 1]
                l = l[:st] + newv + l[en:]
            lines[ln - 1] = l
            open(p, 'w').write('\n'.join(lines))
            log.write(f'{rel}\t{ln}\t{old}\t{newv}\t{o_s}\tapplied\n'); n += 1
            X.override_lines.add((rel, ln))
            try:
                covered.add((rel, ln, ival(old)))
                X.explained[(rel, ln, ival(old))] = 'override'
            except ValueError:
                pass
    return n, covered, nbad


def kernel_split(a, files):
    """{non-A file: why} for the files that are per-image: a file that imports the source images module, is the
    asan-ubsan twin of an A/ file, or holds an image value of ANY of the unit's source images (--old-elf and each
    --kernel-image) outside the opaque label positions (mcheck/FCheck/spin/ISpin arguments): the image end (hex, or
    the decimal end / 8), a hex code pc that is not an instruction word, a hex data address (page multiples
    excepted: sizes); and every file that Requires one of those, transitively. The rest is kernel."""
    imgs = [(Elf(p), Geo(p)) for p in [a.old_elf] + list(a.kernel_image or [])]
    from resolve_code import old_syms_list
    ostarts = {lo for lo, _, _ in old_syms_list(a.old_syms)} if getattr(a, 'old_syms', None) else set()
    nona = [f for f in files if not f.startswith('A/')]
    mods = {f[:-2].replace('/', '.'): f for f in nona}
    texts = {f: open(os.path.join(a.src_lib, f)).read() for f in nona}
    req = re.compile(r'From\s+' + re.escape(a.src_mod) + r'\s+Require(?:\s+(?:Import|Export))?\s+([\w.\'\s]+?)\.(?=\s|$)')
    deps = {}
    for f, t in texts.items():
        ds = {mods[n] for m in req.finditer(t) for n in m.group(1).split() if n in mods}
        ds |= {mods[m.group(1)] for m in re.finditer(re.escape(a.src_mod) + r'\.((?!A\b)[A-Za-z_]\w*)', t)
               if m.group(1) in mods}
        deps[f] = ds - {f}

    def seed(f, t):
        if a.src_images in t:
            return 'imports the images module'
        if y_twin(os.path.basename(f), a.src_lib):
            return 'asan-ubsan twin of an A/ file'
        for ln, l in enumerate(t.split('\n'), 1):
            labels = set(label_starts(l))
            for m in NUM.finditer(l):
                if m.start(1) in labels or OPCODE_CTX.match(l, m.end()) or OPCODE_PRE.search(l, 0, m.start()):
                    continue
                tok = m.group(1)
                v = ival(tok)
                for old, og in imgs:
                    if v in (og.hull[1], og.hull[1] >> 3) and (tok.lower().startswith('0x') or v >= 0x10000):
                        return f'line {ln}: image end {tok}'
                    if not tok.lower().startswith('0x') or v < 0x10000 or WORD32.fullmatch(tok):
                        continue
                    s = old.sec(v)
                    if s and s[2] & 4 and v & 3 != 3:
                        return f'line {ln}: code pc {tok}'
                    if s and not s[2] & 4 and v % PAGE and (s[1] != 8 or v in ostarts):
                        return f'line {ln}: data address {tok} ({s[0]})'  # in .bss only an object start counts
        return None
    out = {}
    for f, t in texts.items():
        w = seed(f, t)
        if w:
            out[f] = w
    changed = True
    while changed:
        changed = False
        for f, ds in deps.items():
            if f not in out and ds & out.keys():
                out[f] = 'Requires ' + ' '.join(sorted(os.path.basename(d)[:-2] for d in ds & out.keys()))
                changed = True
    return out


def differing_kept(a, stage, kept):
    """Which target files that the staged A/ files Require are NOT a plain copy of the source's file (the target
    changed them). Those are where a ported A/ file breaks. Writes differs.tsv: module, how many A/ files name it,
    those files."""
    def norm(t):
        return [l for l in t.split('\n') if not l.startswith('(*')]
    diff = {}
    for rel in kept:
        s = os.path.join(a.src_lib, rel)
        d = os.path.join(a.target_lib, dst_path(rel, a.reusable_dir))
        # the donor's text renamed exactly as staging would rename it, against the target's copy
        if os.path.exists(d) and norm(rename_text(open(s).read(), a)) != norm(open(d).read()):
            diff[rel] = []
    for root, _, fs in os.walk(stage):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            txt = open(os.path.join(root, f)).read()
            for m in diff:
                if re.search(r'(?<![A-Za-z0-9_.])' + re.escape(os.path.basename(m)[:-2]) + r'(?![A-Za-z0-9_])', txt):
                    diff[m].append(os.path.relpath(os.path.join(root, f), stage))
    with open(os.path.join(a.work, 'differs.tsv'), 'w') as fh:
        for m, us in sorted(diff.items(), key=lambda x: -len(x[1])):
            fh.write(f'{m[:-2]}\t{len(us)}\t{" ".join(us)}\n')
    return diff


def decl_names(t):
    """names a file declares: Definition/Lemma/... names, Inductive constructors, Record fields."""
    names = set(DECL.findall(t))
    for blk in re.finditer(r'\bInductive\b(.*?)\.\s*(?:\n|$)', t, re.S):
        names.update(re.findall(r"\|\s*([A-Za-z_][\w']*)", blk.group(1)))
    for blk in re.finditer(r'\b(?:Record|Structure)\s+\w+[^{]*\{(.*?)\}', t, re.S):
        names.update(re.findall(r"(?:^|;|\{)\s*([A-Za-z_][\w']*)\s*:", blk.group(1)))
        m = re.search(r"\b(?:Record|Structure)\s+\w+[^{]*:=\s*([A-Za-z_][\w']*)\s*\{", blk.group(0))
        if m:
            names.add(m.group(1))
    return names


def kept_names(a, out, diff, X):
    """For every kept target file that is not a plain copy of the donor's: the names the donor's copy declares that
    the target's copy does not, and every staged line that uses one (review rows `kept-name-missing`)."""
    missing = {}
    for rel in diff:
        s = open(os.path.join(a.src_lib, rel)).read()
        d = open(os.path.join(a.target_lib, dst_path(rel, a.reusable_dir))).read()
        gone = decl_names(s) - decl_names(d)
        if gone:
            missing[rel] = gone
    if not missing:
        return 0
    rx = {n: re.compile(r"(?<![A-Za-z0-9_'.])" + re.escape(n) + r"(?![A-Za-z0-9_'])") for g in missing.values() for n in g}
    owner = {n: rel for rel, g in missing.items() for n in g}
    k = 0
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            for ln, l in enumerate(open(p).read().split('\n'), 1):
                for n, r in rx.items():
                    if r.search(l):
                        X.rev.append((rel, ln, '-', '-', f'kept-name-missing {n} (declared by the donor\'s '
                                      f'{owner[n]}, not by the target\'s copy)'))
                        k += 1
    return k


def apply_patches(a, stage, out, X):
    """--patch FILE: unified diffs against stage-out, applied with `patch --fuzz=0` after the overrides and before every
    check (a structural fix: a rename, an added definition or branch). A hunk that does not apply is a FAIL row: on a
    re-run the fix is never lost silently. Returns (applied, failed, the stage dir the symbol gate pairs with): lines a
    patch adds get an empty line in a copy of stage/, lines it removes leave it, so the gate keeps pairing lines."""
    if not a.patch:
        return 0, 0, stage
    before = {}
    for root, _, fs in os.walk(out):
        for f in fs:
            if f.endswith('.v'):
                p = os.path.join(root, f)
                before[os.path.relpath(p, out)] = open(p).read().split('\n')
    ok = bad = 0
    for pf in a.patch:
        r = subprocess.run(['patch', '--fuzz=0', '--forward', '--batch', '-p0', '-d', out, '-i', os.path.abspath(pf)],
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        open(os.path.join(a.work, 'patches.log'), 'a').write(f'== {pf}\n{r.stdout}\n')
        if r.returncode:
            row = (pf, 0, '-', '-', 'FAIL patch-did-not-apply (zero fuzz; see patches.log)')
            X.rev.append(row); X.chk.append(row); bad += 1
        else:
            ok += 1
    import difflib
    gst = os.path.join(a.work, 'gate-stage')
    shutil.rmtree(gst, ignore_errors=True)
    shutil.copytree(stage, gst)
    for rel, b in before.items():
        now = open(os.path.join(out, rel)).read().split('\n')
        if now == b:
            continue
        s = open(os.path.join(stage, rel)).read().split('\n')
        g = []
        for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, b, now, autojunk=False).get_opcodes():
            if tag == 'equal':
                g += s[i1:i2]
            elif tag == 'replace':
                g += s[i1:i1 + min(i2 - i1, j2 - j1)] + [''] * max(0, (j2 - j1) - (i2 - i1))
            elif tag == 'insert':
                g += [''] * (j2 - j1)
        open(os.path.join(gst, rel), 'w').write('\n'.join(g))
        X.chk.append((rel, 0, '-', '-', 'patched (--patch)'))
    return ok, bad, gst


def quotients(stage, out, X):
    """a numeral that is another numeral of the same line / 8 (or the sum of an address and an offset on the line / 8)
    in the released text (region length / 8, image size / 8: AD1d.v:39/281 1446400 = 11571200 / 8, AFfu.v:406
    85568 = 684544 / 8; AFjr.v:625 83272 = (666008 + 168) / 8) is DERIVED: after the run it is recomputed from its
    partner (partner' / 8), never moved as an address; when the partner' does not divide, a FAIL row. A partner the
    run left (an ungated geometry value keeps the donor's) leaves its quotient as it is."""
    n = fails = 0
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            if rel in X.generated or not os.path.exists(os.path.join(stage, rel)):
                continue
            sl, ol = open(os.path.join(stage, rel)).read().split('\n'), open(p).read().split('\n')
            changed = False
            for i, (s, o) in enumerate(zip(sl, ol)):
                sm, om = list(NUM.finditer(s)), list(NUM.finditer(o))
                if len(sm) != len(om) or len(sm) < 2:
                    continue
                sv = [ival(m.group(1)) for m in sm]
                ov = [ival(m.group(1)) for m in om]
                subs = {}
                for j, q in enumerate(sv):
                    if q < 0x1000:
                        continue
                    parts = [((k,), b, ov[k]) for k, b in enumerate(sv) if k != j and b == q * 8]
                    parts += [((k, l), b + c, ov[k] + ov[l]) for k, b in enumerate(sv) for l, c in enumerate(sv)
                              if len({j, k, l}) == 3 and b >= 0x10000 and c < 0x1000 and b + c == q * 8]
                    for ks, b, nb in parts[:1]:
                        want = nb // 8 if nb % 8 == 0 else None
                        if want is None:
                            X.rev.append((rel, i + 1, hex(q), '-', f'FAIL quotient ({q} = {b} / 8 in the donor; the '
                                          f'partner became {nb}, not a multiple of 8)'))
                            X.chk.append(X.rev[-1]); fails += 1
                        elif ov[j] != want:
                            subs[j] = fmt_like(om[j].group(1), want)
                            X.chk.append((rel, i + 1, hex(q), hex(want), f'geometry derived quotient ({b} / 8 -> '
                                          f'{nb} / 8)'))
                            X.explained[(rel, i + 1, q)] = 'geometry'
                for j in sorted(subs, reverse=True):
                    o = o[:om[j].start()] + subs[j] + o[om[j].end():]
                if subs:
                    ol[i] = o; changed = True; n += len(subs)
            if changed:
                open(p, 'w').write('\n'.join(ol))
    return n, fails


TOKREF = re.compile(r"port_core_refused_[0-9a-f]+|(?<![A-Za-z0-9_'.])(?:0x[0-9a-fA-F]+|\d+)(?![0-9A-Za-z_])")


def hash_roles(stage, out, X):
    """the trace store's HASH of a pc list (Reusable/YF0p.v tfib_dhash; A/AF0m.v TFIB_HASH) and its BUCKET (hash mod
    d_tab_words: the `tfib_hash_buckets` example) are decided by ROLE, never by a definition name: after the pass each
    is recomputed from the pc list the same file states, as relocated (grant's hand values A/AF0m.v:529-530 are
    exactly this of its TFIB_TR0). A list with a refused element refuses its hash and bucket (per-image-hash).
    Returns the number of numerals written."""
    n = 0
    for rel in sorted(X.remapped):
        p, sp = os.path.join(out, rel), os.path.join(stage, rel)
        if rel in X.generated or not os.path.exists(sp) or not os.path.exists(p):
            continue
        st = open(sp).read()
        roles = hash_role_values(st, X.dtab)
        if not roles:
            continue
        sl, ol = st.split('\n'), open(p).read().split('\n')
        newlist = {}  # donor pc list -> relocated list (None: an element is refused)
        for s, o in zip(sl, ol):
            sm, om = list(PCLIST.finditer(s)), list(PCLIST.finditer(o))
            if len(sm) != len(om):
                continue
            for x, y in zip(sm, om):
                t0 = tuple(int(v, 16) for v in re.split(r'\s*;\s*', x.group(1).strip()))
                t1 = None if REFUSED in y.group(1) else tuple(int(v, 16) for v in re.split(r'\s*;\s*', y.group(1).strip()))
                newlist[t0] = t1 if newlist.get(t0, t1) == t1 else None  # two relocations of one list: refused
        changed = False
        for i, (s, o) in enumerate(zip(sl, ol)):
            so, no = list(TOKREF.finditer(s)), list(TOKREF.finditer(o))
            if len(so) != len(no):
                continue
            subs = {}
            for j, m in enumerate(so):
                v = ival(m.group(0))
                if v not in roles:
                    continue
                kind, t0 = roles[v]
                t1 = newlist.get(t0)
                if t1 is None:
                    subs[j] = f'{REFUSED}{v:x}'
                    X.refusals.append((rel, i + 1, hex(v), 'per-image-hash'))
                    X.rev.append((rel, i + 1, hex(v), '-', f'per-image-hash ({kind} of the pc list '
                                  f'[{"; ".join(hex(x) for x in t0)}], which has a refused element: recompute with '
                                  f'the kit\'s depot.py)'))
                    continue
                h = dhash(list(t1))
                w = h if kind == 'hash' else h % X.dtab
                subs[j] = fmt_like(m.group(0), w)
                X.explained[(rel, i + 1, v)] = 'per-image hash'
                X.written[(rel, i + 1, v)] = {w}
                X.chk.append((rel, i + 1, hex(v), hex(w), f'per-image-hash {kind} recomputed (tfib_dhash of the '
                              f'relocated pc list [{"; ".join(hex(x) for x in t1)}]'
                              + (f' mod {X.dtab})' if kind == 'bucket' else ')')))
            for j in sorted(subs, reverse=True):
                o = o[:no[j].start()] + subs[j] + o[no[j].end():]
            if subs:
                ol[i] = o; changed = True; n += len(subs)
        if changed:
            open(p, 'w').write('\n'.join(ol))
    return n


def derived_names(stage, out, X):
    """MIRROR rule: a numeral DERIVED from a named address moves exactly as that name moves. `Definition N : Z := M + k`
    (M a `Definition M : Z := 0x...` of any staged file) makes N's donor value M + k; a numeral equal to that value on
    a line that names N (identity A/AE39.v:30 `mc_bounds : MC_LO = 0x10350 /\\ MC_HI = 0x10370`, MC_HI := ONES + 8)
    is written as M's written value + k: when M does not move, neither does it (identity had moved 0x10370 to another
    constant's 0x10378). Returns the number of numerals written."""
    base = {}  # name -> (donor value, written value or None)
    texts = {}
    for f in sorted(X.remapped):
        sp, p = os.path.join(stage, f), os.path.join(out, f)
        if os.path.exists(sp) and os.path.exists(p) and f not in X.generated:
            texts[f] = (open(sp).read(), open(p).read())
    dre = re.compile(r"Definition\s+([A-Za-z_][\w']*)\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+|" + REFUSED + r"[0-9a-f]+)\s*\.")
    for f, (st, ot) in texts.items():
        sv = {m.group(1): m.group(2) for m in dre.finditer(st)}
        ov = {m.group(1): m.group(2) for m in dre.finditer(ot)}
        for n, v in sv.items():
            if n in ov and v.startswith('0x'):
                base.setdefault(n, (int(v, 16), None if ov[n].startswith(REFUSED) else int(ov[n], 16)))
    der, consts = {}, {}
    cre = re.compile(r"Definition\s+([A-Za-z_][\w']*)\s*:\s*Z\s*:=\s*(\d+|0x[0-9a-fA-F]+)\s*\.")
    for t in [st for st, _ in texts.values()] + [open(p).read() for p in (os.path.join(X.a.src_lib, 'YG0f.v'),
                                                                          os.path.join(X.a.src_lib, 'Reusable', 'YG0f.v'))
                                                if os.path.exists(p)]:
        for m in cre.finditer(strip_comments(t)):
            consts.setdefault(m.group(1), ival(m.group(2)))
    rx = re.compile(r"Definition\s+([A-Za-z_][\w']*)\s*:\s*Z\s*:=\s*([A-Za-z_][\w']*)\s*(?:\+\s*(\d+|0x[0-9a-fA-F]+|"
                    r"[A-Za-z_][\w']*))?\s*\.")
    for f, (st, _) in texts.items():
        for m in rx.finditer(strip_comments(st)):
            if m.group(2) in base and m.group(1) not in base:
                o, w = base[m.group(2)]
                kt = m.group(3)
                k = 0 if not kt else (ival(kt) if kt[0].isdigit() else consts.get(kt))
                if k is None:
                    continue
                der[m.group(1)] = (o + k, None if w is None else w + k, m.group(2), k)
    if not der:
        return 0
    n = 0
    names = re.compile(r"(?<![\w'.])(" + '|'.join(re.escape(x) for x in der) + r")(?![\w'])")
    for f, (st, ot) in texts.items():
        sl, ol = strip_comments(st).split('\n'), ot.split('\n')
        if len(sl) != len(ol):
            continue
        changed = False
        for i, (s, o) in enumerate(zip(sl, ol)):
            hit = {m.group(1) for m in names.finditer(s)}
            if not hit or re.match(r'\s*Definition\s+(' + '|'.join(re.escape(x) for x in hit) + r')\b', s):
                continue
            so, no = list(TOKREF.finditer(st.split('\n')[i])), list(TOKREF.finditer(o))
            if len(so) != len(no):
                continue
            subs = {}
            for nm in hit:
                old, new, m0, k = der[nm]
                for j, t in enumerate(so):
                    if ival(t.group(0)) != old:
                        continue
                    if new is None:
                        subs[j] = f'{REFUSED}{old:x}'
                        X.refusals.append((f, i + 1, hex(old), 'derived-name'))
                        X.rev.append((f, i + 1, hex(old), '-', f'derived-name ({nm} = {m0} + {k}; {m0} is refused)'))
                    elif no[j].group(0).startswith(REFUSED) or ival(no[j].group(0)) != new:
                        subs[j] = fmt_like(t.group(0), new)
                        X.chk.append((f, i + 1, hex(old), hex(new), f'derived-name {nm} = {m0} + {k} (written as {m0} '
                                      f'moved: {base[m0][0]:#x} -> {base[m0][1]:#x}; the pass had written '
                                      f'{no[j].group(0)})'))
                        X.explained[(f, i + 1, old)] = 'derived name'
                        X.refusals[:] = [r for r in X.refusals if not (r[0] == f and r[1] == i + 1 and
                                                                       r[2] == hex(old))]
            for j in sorted(subs, reverse=True):
                o = o[:no[j].start()] + subs[j] + o[no[j].end():]
            if subs:
                ol[i] = o; changed = True; n += len(subs)
        if changed:
            open(os.path.join(out, f), 'w').write('\n'.join(ol))
    return n


def rename_gate(a, out, kept, X):
    """--rename OLD=NEW against the slot / patched files: after the overrides and patches, OLD must be declared by no
    staged file (a slot regenerated or a frozen file with the donor's names brings it back: identity's frozen AF0m
    declared TfibSyms while 502 uses said IdentTfibSyms), and a NEW name the staged files use must be declared by a
    staged or kept file. FAIL rows otherwise. Returns the number of FAIL rows."""
    if not a.rename:
        return 0
    decl, uses = collections.defaultdict(set), collections.defaultdict(list)
    texts = {}
    for root, _, fs in os.walk(out):
        for f in fs:
            if f.endswith('.v'):
                p = os.path.join(root, f)
                texts[os.path.relpath(p, out)] = strip_comments(open(p).read())
    for rel, t in texts.items():
        for n in decl_names(t):
            decl[n].add(rel)
    for rel in kept:
        d = os.path.join(a.target_lib, dst_path(rel, a.reusable_dir))
        if os.path.exists(d):
            for n in decl_names(strip_comments(open(d).read())):
                decl[n].add(d)
    n = 0
    for r in a.rename:
        old, new = r.split('=', 1)
        for rel in sorted(decl.get(old, ())):
            if rel in texts:
                row = (rel, 0, old, new, f'FAIL rename-old-declared ({rel} declares {old}, which --rename {r} renames '
                                         f'everywhere else: a slot or patch brought the donor\'s name back)')
                X.rev.append(row); X.chk.append(row); n += 1
        if new not in decl:
            rx = re.compile(r"(?<![\w'.])" + re.escape(new) + r"(?![\w'])")
            users = [rel for rel, t in texts.items() if rx.search(t)]
            if users:
                row = (users[0], 0, old, new, f'FAIL rename-new-undeclared ({new} is used in {len(users)} staged files '
                                              f'and declared by none, staged or kept)')
                X.rev.append(row); X.chk.append(row); n += 1
    return n


def decode_gate(out, X):
    """the independent decoder decode_check.py (ISA-manual encodings, not LPS, not this script's
    decode_text) re-decodes every `decode_any (W%bv ...) = Some (...)` of stage-out: each MISMATCH is a FAIL row (on
    53ec3af2afc9's grant stage-out A/AE3e.v:408 `Jal 0 2091732` over 0xf95ff06f, true 2097044). Returns (FAIL rows,
    the summary line)."""
    if not DECODE_CHECK or not os.path.exists(DECODE_CHECK):
        return 0, f'{DECODE_CHECK or "--decode-check"} missing'
    r = subprocess.run([sys.executable, DECODE_CHECK, '--dir', out], stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       text=True)
    n = 0
    for l in r.stdout.split('\n'):
        if l.startswith('MISMATCH'):
            row = ('-', 0, '-', '-', f'FAIL decode-check {l[9:300]}')
            X.rev.append(row); X.chk.append(row); n += 1
    summ = next((l for l in r.stdout.split('\n') if l.startswith('statements')), r.stdout.strip()[-200:])
    return n, summ


PAIR_FORMS = [  # (addr, len / end) pairs of hole / chunk / region definitions: (regex, kind of the second numeral)
    (re.compile(r'\bmkChunk\s+' + _V + r'\s*\(\s*CImg\s+\(?\s*' + _V), 'len'),
    (re.compile(r'\bmkRegion\s+\w+\s+' + _V + r'\s+' + _V), 'end'),
    (re.compile(r'\bCH\s+\w+\s+' + _V + r'\s+' + _V), 'len'),
    (re.compile(r'\(\s*' + _V + r'\s*,\s*' + _V + r'(?:\s*-\s*' + _V + r')?\s*\)'), 'len'),
]


def pair_rows_gate(a, stage, out, X):
    """every (addr, len) / (lo, hi) pair inside a hole / chunk / region definition (A/AF0m.v's Tfib_zero_shadow /
    Tfib_owned_static holes, A/AD2j.v's mkRegion / mkChunk, A/AD1k.v's CH rows; their Y twins), in hex AND decimal,
    is a ROW ADDRESS: one left at the donor's value (a generated slot not yet regenerated, a frozen file) FAILs when
    the rules give the target another address for it (`row-address-stale`, with that address: relA2's AF0m holes
    (0x21448, 4) -> 0x21ce4, AD2j 136268 -> 138472), or when no rule gives one and the target's bytes there are not the
    donor's (`row-address-unresolved`). A moved row passes. Rows go to rowaddr.tsv; one FAIL row per file."""
    names = {'AF0m.v', 'YF0m.v', 'AD2j.v', 'YD2j.v', 'AD1k.v', 'YD1k.v'}
    hl, hh = X.OG.hull
    tab, nfail = [], 0
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if f not in names:
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            sp = os.path.join(stage, rel)
            if not os.path.exists(sp):
                continue
            sl, ol = strip_comments(open(sp).read()).split('\n'), strip_comments(open(p).read()).split('\n')
            if len(sl) != len(ol):
                continue
            bad = []
            for i, (s, o) in enumerate(zip(sl, ol), 1):
                so, no = list(TOKREF.finditer(s)), list(TOKREF.finditer(o))
                if len(so) != len(no):
                    continue
                idx = {m.start(): k for k, m in enumerate(so)}
                for rx, kind in PAIR_FORMS:
                    for m in rx.finditer(s):
                        ka, kb = idx.get(m.start(1)), idx.get(m.start(2))
                        if ka is None or kb is None:
                            continue
                        A0, B0 = ival(so[ka].group(0)), ival(so[kb].group(0))
                        A1 = no[ka].group(0)
                        if not hl <= A0 < hh or A1.startswith(REFUSED) or ival(A1) != A0:
                            continue  # not an image address, refused, or moved: not left at the donor's
                        n = (B0 - A0) if kind == 'end' else (B0 - A0 if m.lastindex >= 3 and m.group(3) else B0)
                        if n <= 0 or n > 1 << 24:
                            continue
                        bnd = {X.NG.role.get(r) for r in X.OG.by.get(A0, [])} - {None}
                        want = (min(bnd) if len(bnd) == 1 else None) if bnd else \
                            (X.object_value(A0) if X.old.sec(A0) else None)  # a header bound: its role's value
                        if want is not None and want != A0:
                            st = f'row-address-stale (the rules give {want:#x})'
                        elif want is None:
                            ob, nb = X.old.read(A0, min(n, 64)), X.new.read(A0, min(n, 64))
                            st = None if ob is not None and ob == nb else 'row-address-unresolved (no rule, the ' \
                                                                          'target\'s bytes there differ)'
                        else:
                            st = None
                        tab.append((rel, i, so[ka].group(0), n, '-' if want is None else hex(want), st or 'ok'))
                        if st:
                            bad.append(f'{i}:{so[ka].group(0)}')
            if bad:
                row = (rel, 0, '-', '-', f'FAIL row-address ({len(bad)} (addr, len) rows left at the donor\'s value; '
                                         f'first {", ".join(bad[:4])}; rowaddr.tsv)')
                X.rev.append(row); X.chk.append(row); nfail += 1
    with open(os.path.join(a.work, 'rowaddr.tsv'), 'w') as fh:
        fh.write('file\tline\taddr\tlen\trules_give\tstatus\n')
        for r in tab:
            fh.write('\t'.join(map(str, r)) + '\n')
    return nfail


def row_symbols(out, X, R, new):
    """every ADDRESS of an `(ANum A)` row of A/AF0m.v / YF0m.v outside the generated classes must lie inside a sized
    symbol of the TARGET (its unstripped twin) or in its .got; a row left at a donor address that resolves to nothing
    (scene YF0m row 82 `z8 (ANum 0x9ee98) 0xa2ae0`) is a FAIL row."""
    from resolve_code import all_syms
    syms = sorted((lo, hi) for lo, hi, _ in all_syms(X.a.target_syms)) if X.a.target_syms else []
    los = [s[0] for s in syms]
    got = X.NG.sec.get('.got')
    n = 0
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if f not in ('AF0m.v', 'YF0m.v'):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            sp = os.path.join(X.a.work, 'stage', rel)
            sls = open(sp).read().split('\n') if os.path.exists(sp) else []
            for i, l in enumerate(open(p).read().split('\n'), 1):
                olds = [int(x, 16) for x in re.findall(r'ANum\s+(0x[0-9a-fA-F]+)', sls[i - 1])] if i <= len(sls) else []
                for j, m in enumerate(re.finditer(r'ANum\s+(0x[0-9a-fA-F]+)', l)):
                    a = int(m.group(1), 16)
                    if X.explained.get((rel, i, a)) == 'generated slot' or a >= SHADOW:
                        continue
                    k = bisect.bisect_right(los, a) - 1
                    ok = (k >= 0 and a < syms[k][1]) or (got and got[0] <= a < got[1])
                    if not ok and j < len(olds):
                        # the row stands when the release MOVED the address (a rule decided it), or when the target
                        # holds the donor's bytes at the same place (an anonymous .rodata constant that did not move)
                        ob, nb = X.old.read(olds[j], 8), new.read(a, 8)
                        ok = olds[j] != a or (bool(ob) and ob == nb)
                    if not ok:
                        row = (rel, i, hex(a), '-', f'FAIL row-address-unresolved ({a:#x} was left at the donor\'s, is '
                                                    f'inside no target symbol, not in .got, and does not hold the '
                                                    f'donor\'s bytes)')
                        X.rev.append(row); X.chk.append(row); n += 1
    return n


def bound_order(out, X):
    """every `<p>_lo` / `<p>_hi` definition pair of a staged file must have lo <= hi after the run (an inverted bound:
    scene asan-ubsan's tfib_asan_globals_lo 0xa2ae0 > hi 0xa0440 under the old tool); FAIL rows otherwise."""
    n = 0
    dre = re.compile(r"Definition\s+(\w+)_(lo|hi)\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+)\s*\.")
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            if rel in X.generated:
                continue
            t = open(p).read()
            d = {}
            for m in dre.finditer(t):
                d[(m.group(1), m.group(2))] = (int(m.group(3), 16), t.count('\n', 0, m.start()) + 1)
            for (b, side), (v, ln) in d.items():
                if side == 'lo' and (b, 'hi') in d and v > d[(b, 'hi')][0]:
                    hv = d[(b, 'hi')][0]
                    row = (rel, ln, hex(v), hex(hv), f'FAIL inverted-bound ({b}_lo {v:#x} > {b}_hi {hv:#x})')
                    X.rev.append(row); X.chk.append(row); n += 1
    return n


def replace_pairs(out, X):
    """`replace (Z_to_bv 64 D : word) with (0xH%bv : word)` (or the reverse): both sides state ONE value in two forms;
    a pair whose sides disagree after the run FAILS (scene: the hex side moved, the decimal kept)."""
    rx = re.compile(r'replace\s*\(\s*(?:Z_to_bv\s+64\s+)?\(?\s*(0x[0-9a-fA-F]+|\d+)\s*\)?\s*(?:%bv)?\s*:\s*word\s*\)\s*'
                    r'with\s*\(\s*(?:Z_to_bv\s+64\s+)?\(?\s*(0x[0-9a-fA-F]+|\d+)\s*\)?\s*(?:%bv)?\s*:\s*word\s*\)')
    n = 0
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            for i, l in enumerate(open(p).read().split('\n'), 1):
                for m in rx.finditer(l):
                    x, y = ival(m.group(1)), ival(m.group(2))
                    if x != y:
                        row = (rel, i, m.group(1), m.group(2), f'FAIL replace-pair (the two sides of the replace state '
                               f'{x:#x} and {y:#x}: one side was moved, the other not)')
                        X.rev.append(row); X.chk.append(row); n += 1
    return n


def cell_gates(a, out):
    """the three cell gates of the pre-push run, on stage-out: shadowcheck (TARGET.debug AF0m.v), ownedcheck (AF0m.v
    --elf TARGET.debug), cellcheck (STAGE_DIR ELF). Returns [(gate, ok, summary line)]; the lines go to cellgates.txt.
    AF0m's generated classes are slots until the unit puts its collector's rows in: before that, shadowcheck and
    ownedcheck report the donor's rows as wrong (expected); --prepush makes any failure fail the run."""
    res = []
    dbg = a.target_syms if a.target_syms and not a.target_syms.endswith('.txt') else a.target_elf
    for af in sorted({os.path.join(r, f) for r, _, fs in os.walk(out) for f in fs if f in ('AF0m.v', 'YF0m.v')}):
        for gate, cmd in (('shadowcheck', [sys.executable, os.path.join(CELL_GATES or '', 'shadowcheck.py'), dbg, af]),
                          ('ownedcheck', [sys.executable, os.path.join(CELL_GATES or '', 'ownedcheck.py'), af, '--elf', dbg])):
            if not CELL_GATES or not os.path.exists(cmd[1]):
                res.append((gate, False, f'{cmd[1]} missing')); continue
            r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            last = [l for l in r.stdout.strip().split('\n') if l.strip()][-1:] or ['(no output)']
            res.append((f'{gate} {os.path.relpath(af, out)}', r.returncode == 0, last[0][:300]))
    if CELLCHECK and os.path.exists(CELLCHECK):
        r = subprocess.run([sys.executable, CELLCHECK, out, a.target_elf], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           text=True)
        last = (r.stderr.strip().split('\n') or ['(no output)'])[-1]
        bad = re.search(r'(\d+) mismatch', last)
        res.append(('cellcheck', r.returncode == 0 and bad is not None and bad.group(1) == '0', last[:300]))
        open(os.path.join(a.work, 'cellcheck.tsv'), 'w').write(r.stdout)
    with open(os.path.join(a.work, 'cellgates.txt'), 'w') as fh:
        for g, ok, line in res:
            fh.write(f'{g}\t{"PASS" if ok else "FAIL"}\t{line}\n')
    return res


def split_ranges(stage, out, X, R):
    """`(START, N%nat)` code ranges (ff_ranges, icpt_ranges, fs_ranges): the N donor instructions from START are cut
    into maximal RUNS of instructions whose code has a twin and whose twins are contiguous in the target; each run
    becomes one tuple at its twin's start with the run's own instruction count. A donor function without a twin (cgif's
    fopen-side code, its fopen / fclose trampolines) ends its run and appears in no tuple; a target function between
    two twins starts a new tuple. grant's hand-adapted A/AE34.v is the same split by hand. Every emitted tuple is then
    checked by the range-content gate against its own donor run; the stage / stage-out numeral pairing on a split line
    no longer holds, so those donor numerals are marked explained for the symbol gate."""
    tr = re.compile(r'\(\s*(0x[0-9a-fA-F]+)\s*,\s*(\d+)%nat\s*\)')
    nsplit = nfail = 0
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            sp = os.path.join(stage, rel)
            if rel in X.generated or not os.path.exists(sp):
                continue
            sl, ol = open(sp).read().split('\n'), open(p).read().split('\n')
            if len(sl) != len(ol):
                continue
            changed = False
            for ln, (s, o) in enumerate(zip(sl, ol), 1):
                sm, om = list(tr.finditer(s)), list(tr.finditer(o))
                if not sm or len(sm) != len(om) or 'startup_plan_tfib_ranges' in s or (rel, ln) in X.override_lines:
                    continue  # (an --override row on the line is the porter's: pcap AE34.v:25 row 8, 40 trampolines)
                newo, last, lsplit = [], 0, False
                for x, y in zip(sm, om):
                    lo0, cnt = int(x.group(1), 16), int(x.group(2))
                    k = R.co.index_of(lo0)
                    if k is None or not X.is_exec(lo0):
                        continue
                    runs, cur = [], None  # cur = [target start, n instructions, donor start, donor bytes]
                    for kk in range(k, min(k + cnt, len(R.co.pcs))):
                        pc, ln_ = R.co.pcs[kk], R.co.lens[kk]
                        t = R.map_code(pc)
                        if t is not None and cur is not None and t == cur[0] + cur[3]:
                            cur[1] += 1; cur[3] += ln_
                            continue
                        if cur is not None:
                            runs.append(cur); cur = None
                        if t is not None:
                            cur = [t, 1, pc, ln_]
                    if cur is not None:
                        runs.append(cur)
                    whole = len(runs) == 1 and runs[0][1] == cnt
                    if whole:
                        continue  # one run covering the whole donor range: the ordinary relocation stands
                    lsplit = True
                    # runs whose twins overlap or touch in the target are ONE target range (knock A/AE34.v:25: the
                    # donor's two copies of a function twin to one, (0x4250c, 47) twice -> once; 1009 donor words ->
                    # (0x504b0, 714), not (0x504b0, 2); (0x504b8, 712))
                    merged = []
                    for t, n, d0, db in sorted(runs):
                        if merged and t <= merged[-1][1]:
                            merged[-1][1] = max(merged[-1][1], t + db)
                        else:
                            merged.append([t, t + db])
                    parts = []
                    for t0, t1 in merged:
                        i0, i1 = R.cn.index_of(t0), R.cn.index_of(t1)
                        n = (i1 if i1 is not None else len(R.cn.pcs)) - i0 if i0 is not None else None
                        parts.append(f'({t0:#x}, {n}%nat)' if n else None)
                    text = '; '.join(p for p in parts if p) if all(parts) else \
                        '; '.join(f'({t:#x}, {n}%nat)' for t, n, _, _ in runs)
                    newo.append((y.start(), y.end(), text, runs, lo0, cnt))
                if not lsplit:
                    continue
                for st, en, text, runs, lo0, cnt in reversed(newo):
                    if text:
                        o = o[:st] + text + o[en:]
                    else:  # no run at all: the tuple goes with one separator
                        m = re.match(r'\s*;\s*', o[en:])
                        if m:
                            o = o[:st] + o[en + m.end():]
                        else:
                            m2 = re.search(r';\s*$', o[:st])
                            o = (o[:m2.start()] if m2 else o[:st]) + o[en:]
                    X.chk.append((rel, ln, hex(lo0), text or '-', f'range-split ({lo0:#x}, {cnt}) into {len(runs)} '
                                  f'run(s): {text or "none (no donor code here has a twin)"}'))
                    for t, n, d0, dbytes in runs:
                        nfail += _span_check(X, R, rel, ln, d0, dbytes, t)
                    nsplit += 1
                for v in re.findall(r'0x[0-9a-fA-F]+|\d+', s):
                    X.explained[(rel, ln, ival(v))] = 'range split'
                ol[ln - 1] = o
                changed = True
            if changed:
                open(p, 'w').write('\n'.join(ol))
    return nsplit, nfail


def range_gate(a, out, X, R):
    """every `<p>_A_<f>` / `<p>_E_<f>` pair the staged files define (cgif's function table, A/AB1w.v) must satisfy
    start < end, and end = the target function's own end or the start of a target function. FAIL rows otherwise."""
    n = 0
    nstarts = set(R.nhi)
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            rel = os.path.relpath(os.path.join(root, f), out)
            if rel in X.generated:
                continue  # a generated slot is regenerated per unit, not checked against the donor
            t = open(os.path.join(root, f)).read()
            sp = os.path.join(a.work, 'stage', rel)
            st = open(sp).read() if os.path.exists(sp) else ''
            dre = r"Definition\s+(\w+)\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+)\s*\."
            defs = {m.group(1): (int(m.group(2), 16), t.count('\n', 0, m.start()) + 1) for m in re.finditer(dre, t)}
            odefs = {m.group(1): int(m.group(2), 16) for m in re.finditer(dre, st)}
            for name, (s, ln) in defs.items():
                m = re.match(r'(\w*?)_A_(\w+)$', name)
                ename = f'{m.group(1)}_E_{m.group(2)}' if m else None
                if not m or ename not in defs:
                    continue
                e, eln = defs[ename]
                if not X.new.sec(s) or not X.new.sec(s)[2] & 4:
                    continue
                os_, oe = odefs.get(name), odefs.get(ename)
                moved = os_ is not None and oe is not None and oe - os_ == e - s and \
                    R.same_fn_at(os_, oe, s, lo12_tolerant=True)  # the source range itself, moved
                ok = s < e and (R.nhi.get(s) == e or e in nstarts or moved)
                if not ok:
                    why = 'start >= end' if s >= e else (f'end {e:#x} is neither the target function\'s own end '
                                                        f'({R.nhi.get(s, 0):#x}) nor a target function start')
                    row = (rel, eln, hex(e), hex(e), f'FAIL range {m.group(2)}: [{s:#x}, {e:#x}) {why}')
                    X.rev.append(row); X.chk.append(row); n += 1
            # every relocated code interval `(LO <= x < HI)`: LO is a target function start whose donor counterpart
            # starts at the donor LO (a range start never takes the end rule)
            iv = re.compile(r'\(\s*(0x[0-9a-fA-F]+)\s*<=\s*[\w\']+\s*<\s*(0x[0-9a-fA-F]+|' + REFUSED + r'[0-9a-f]+)\s*\)')
            for ln, (sl, ol) in enumerate(zip(st.split('\n'), t.split('\n')), 1):
                sm, om = list(iv.finditer(sl)), list(iv.finditer(ol))
                if len(sm) != len(om):
                    continue
                for x, y in zip(sm, om):
                    lo0 = int(x.group(1), 16)
                    if lo0 not in R.ohi or not X.is_exec(lo0):
                        continue
                    lo1 = int(y.group(1), 16)
                    if R.map_code(lo0) != lo1 or lo1 not in R.nhi:
                        row = (rel, ln, hex(lo0), hex(lo1), f'FAIL range-start ({lo0:#x} starts a donor function; the '
                               f'target value {lo1:#x} is not the start of its twin '
                               f'{"-" if R.map_code(lo0) is None else hex(R.map_code(lo0))})')
                        X.rev.append(row); X.chk.append(row); n += 1
                    elif y.group(2).startswith('0x'):
                        n += _span_check(X, R, rel, ln, lo0, int(x.group(2), 16) - lo0, lo1)
            # (START, N%nat) code ranges (ff_ranges, icpt_ranges, fs_ranges): the N instructions from START cover in
            # the target exactly the twins of the donor functions they cover, nothing the donor lacks
            tr = re.compile(r'\(\s*(0x[0-9a-fA-F]+|' + REFUSED + r'[0-9a-f]+)\s*,\s*(\d+)%nat\s*\)')
            for ln, (sl, ol) in enumerate(zip(st.split('\n'), t.split('\n')), 1):
                sm, om = list(tr.finditer(sl)), list(tr.finditer(ol))
                if len(sm) != len(om) or 'startup_plan_tfib_ranges' in sl or \
                        any(X.explained.get((rel, ln, int(x.group(1), 16))) == 'range split' for x in sm
                            if x.group(1).startswith('0x')):
                    continue  # a split line was checked run by run when it was split (split_ranges)
                for x, y in zip(sm, om):
                    if not x.group(1).startswith('0x') or not y.group(1).startswith('0x'):
                        continue
                    lo0, lo1, cnt = int(x.group(1), 16), int(y.group(1), 16), int(x.group(2))
                    k = R.co.index_of(lo0)
                    if k is None or not X.is_exec(lo0):
                        continue
                    n += _span_check(X, R, rel, ln, lo0, sum(R.co.lens[k:k + cnt]), lo1)
    return n


def _span_check(X, R, rel, ln, lo0, span, lo1):
    """FAIL row when the target range [lo1, lo1 + span) is not the donor range [lo0, lo0 + span) moved: a donor
    function start inside it whose twin is elsewhere, or a target function inside it with no donor twin there (it
    would be widened over code the donor does not have)."""
    if span <= 0:
        return 0
    bad = []
    i = bisect.bisect_left(R.olos, lo0)
    while i < len(R.olos) and R.olos[i] < lo0 + span:
        s = R.olos[i]
        if R.map_code(s) != lo1 + (s - lo0):
            bad.append(f'donor function {s:#x} -> {"-" if R.map_code(s) is None else hex(R.map_code(s))}')
        i += 1
    nl = R._nlos
    j = bisect.bisect_right(nl, lo1)
    while j < len(nl) and nl[j] < lo1 + span:
        t = nl[j]
        if R.map_code(lo0 + (t - lo1)) != t:
            bad.append(f'target function {R.nname.get(t, hex(t))} at {t:#x} has no donor twin there')
        j += 1
    if not bad:
        return 0
    row = (rel, ln, hex(lo0), hex(lo1), f'FAIL range-content ([{lo0:#x}, +{span:#x}) -> [{lo1:#x}, ...): '
           + '; '.join(bad[:3]) + (f'; +{len(bad) - 3} more' if len(bad) > 3 else '') + ')')
    X.rev.append(row); X.chk.append(row)
    return 1


def startup_ranges(stage, out, X, R):
    """`startup_plan_tfib_ranges` (A/AB05.v / YB05.v:2243, the start-up walk's fetch table: (start, word count)) in a
    RELOCATED AB05 (a unit without a start-up collector; with one, AB05 is a generated slot, never relocated, and
    grant's AB05 stays untouched) is EMITTED from the target's own function table: every donor function a donor range
    covers (from .text's start on) is replaced by its twin's whole [st_value, st_value + st_size), the twins are merged
    into runs, 4-aligned, and nothing starts below the target's .text (scene: cgif's (0x30000, 1040) moved below
    .text; asan-ubsan range 11 missed asan.module_ctor / dtor). Returns the number of lists emitted."""
    rx = re.compile(r'(Definition\s+startup_plan_tfib_ranges\s*:\s*list\s*\(Z\s*\*\s*nat\)\s*:=\s*)\[(.*?)\](%Z)?\s*\.')
    tr = re.compile(r'\(\s*(0x[0-9a-fA-F]+)\s*,\s*(\d+)%nat\s*\)')
    olo, nlo = X.OG.sec['.text'][0], X.NG.sec['.text'][0]
    n = 0
    for rel in sorted(X.remapped):
        if os.path.basename(rel) not in ('AB05.v', 'YB05.v') or rel in X.generated:
            continue
        sl, ol = open(os.path.join(stage, rel)).read().split('\n'), open(os.path.join(out, rel)).read().split('\n')
        for i, s in enumerate(sl):
            m = rx.search(s)
            if not m or i >= len(ol):
                continue
            spans, missing = [], []
            for x in tr.finditer(m.group(2)):
                s0 = int(x.group(1), 16)
                a0, b0 = max(s0, olo), s0 + 4 * int(x.group(2))
                k = bisect.bisect_right(R.olos, a0) - 1
                k = max(k, 0)
                first = None
                while k < len(R.olos) and R.olos[k] < b0:
                    lo = R.olos[k]
                    if R.ohi[lo] > a0:
                        t = R.map_code(lo)
                        if t is not None and t in R.nhi and R.nhi[t] > t:
                            spans.append((t & ~3, (R.nhi[t] + 3) & ~3))
                            first = t if first is None else min(first, t)
                        else:
                            missing.append(lo)
                    k += 1
                if s0 <= olo < b0 and first is not None and first > nlo:
                    # the donor range covers the donor's .text start (its _start, a symbol of size 0 that pairs with
                    # nothing): the target range covers the target's .text start the same way
                    spans.append((nlo, first & ~3))
            runs = []
            for lo, hi in sorted(spans):
                lo = max(lo, nlo)
                if runs and lo <= runs[-1][1]:
                    runs[-1][1] = max(runs[-1][1], hi)
                else:
                    runs.append([lo, hi])
            body = '; '.join(f'({lo:#x}, {(hi - lo) // 4}%nat)' for lo, hi in runs)
            mo = rx.search(ol[i])
            if not mo:
                continue
            ol[i] = ol[i][:mo.start(2)] + body + ol[i][mo.end(2):]
            for v in re.findall(r'0x[0-9a-fA-F]+|\d+', m.group(2)):
                X.explained[(rel, i + 1, ival(v))] = 'startup ranges emitted'
            X.refusals[:] = [r for r in X.refusals if not (r[0] == rel and r[1] == i + 1)]
            X.chk.append((rel, i + 1, '-', '-', f'startup_plan_tfib_ranges emitted from the target\'s function table: '
                                                f'{len(runs)} runs over {len(spans)} twin functions'))
            if missing:
                X.rev.append((rel, i + 1, '-', '-', f'startup-ranges: {len(missing)} donor functions in the donor ranges '
                              f'have no twin (first {missing[0]:#x}): not covered'))
            n += 1
        open(os.path.join(out, rel), 'w').write('\n'.join(ol))
    return n


def merged_spans(a, out, X, R):
    """AB1w rows whose [A, E) covers more than one target function (the donor convention's MERGED spans: thunk_417cc,
    thunk_96f9c, MmapFixedOrDieOnFatalError, target_run (E = emit_printf's start: target_run + oft_exit_guard),
    pthread_key_create_body_tsd_init): KEPT as the donor-relative end rule gives them, never narrowed by the tool;
    listed in ab1w-merged.tsv and as check rows (a unit whose walks do not step through both narrows its own)."""
    rows = []
    rx = re.compile(r"Definition\s+(\w*?)_A_(\w+)\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+)\s*\.\s*Definition\s+\1_E_\2\s*:\s*Z\s*:="
                    r"\s*(0x[0-9a-fA-F]+)")
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if f not in ('AB1w.v', 'YB1w.v'):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            for i, l in enumerate(open(p).read().split('\n'), 1):
                for m in rx.finditer(l):
                    s, e = int(m.group(3), 16), int(m.group(4), 16)
                    j = bisect.bisect_right(R._nlos, s)
                    inner = [R.nname.get(x, hex(x)) for x in R._nlos[j:bisect.bisect_left(R._nlos, e)]
                             if R.nhi.get(x, x) > x]
                    if inner:
                        rows.append((rel, i, m.group(2), hex(s), hex(e), ' '.join(inner)[:200]))
                        X.chk.append((rel, i, hex(s), hex(e), f'function-table merged span kept {m.group(2)} (also '
                                      f'covers {", ".join(inner)[:120]}: donor-relative end)'))
    with open(os.path.join(a.work, 'ab1w-merged.tsv'), 'w') as fh:
        fh.write('file\tline\trow\tA\tE\talso_covers\n')
        for r in rows:
            fh.write('\t'.join(map(str, r)) + '\n')
    return len(rows)


def emit_function_table(out, X, R, prog):
    """A/AB1w.v (YB1w.v) is EMITTED as the TARGET's function range table: a donor `<p>_A_f`/`<p>_E_f` pair whose
    value was refused (cgif-only code: no twin) or whose twin is another function (symbol identity) is DROPPED with
    its definitions (the line stays, so line numbers do not move); the target's own program functions (FUNC symbols
    in the target's program block that pair with no donor function) are added with their measured starts and ends.
    A dropped name used anywhere else in the staged files is a FAIL row."""
    paired = set(R.pairs.values()) | set(R.tramp.values()) | set(R.entries.values())
    # the target's program block: from the twin end of the last paired donor function before the donor block to the
    # twin start of the first paired donor function after it
    if not prog:
        X.rev.append(('-', 0, '-', '-', 'function-table: --old-prog LO:HI not given (the donor program block): '
                                         'the target\'s own program functions are NOT added; give --old-prog'))
        prog = [(0, 0)]
    plo, phi = min(lo for lo, _ in prog), max(hi for _, hi in prog)
    before = [lo for lo in R.olos if R.ohi[lo] <= plo and R.map_code(lo) is not None]
    after = [lo for lo in R.olos if lo >= phi and R.map_code(lo) is not None]
    nlo = R.map_code(before[-1]) + (R.ohi[before[-1]] - before[-1]) if before else None
    nhi = R.map_code(after[0]) if after else None
    def fn_end(lo):
        # E = st_value + st_size; a size-0 symbol (identity: _start, __set_thread_area) ends at the next function start
        if R.nhi[lo] > lo:
            return R.nhi[lo]
        k = bisect.bisect_right(R._nlos, lo)
        return R._nlos[k] if k < len(R._nlos) else lo
    own = [(lo, fn_end(lo), R.nname.get(lo, f'fn_{lo:x}')) for lo in R._nlos
           if nlo is not None and nhi is not None and nlo <= lo < nhi and lo not in paired and lo in R.nhi]
    sent = re.compile(r"Definition\s+(\w*?)_([AE])_(\w+)\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+|" + REFUSED + r"[0-9a-f]+)\s*\.\s*")
    nfail, emitted, dropped_all = 0, [], {}
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            t = open(p).read()
            if len(re.findall(r'Definition\s+\w*?_A_\w+\s*:\s*Z\s*:=', t)) < 10:
                continue
            lines = t.split('\n')
            pairs = collections.defaultdict(dict)
            for i, l in enumerate(lines):
                for m in sent.finditer(l):
                    pairs[(m.group(1), m.group(3))][m.group(2)] = (i, m.group(4))
            drop = {k for k, v in pairs.items() if any(x[1].startswith(REFUSED) for x in v.values())}
            for k, v in pairs.items():  # symbol identity of the written start
                if k in drop or 'A' not in v or v['A'][1].startswith(REFUSED):
                    continue
                ov = None
                sl = open(os.path.join(X.a.work, 'stage', rel)).read().split('\n')[v['A'][0]]
                mm = re.search(r"Definition\s+" + re.escape(f'{k[0]}_A_{k[1]}') + r"\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+)", sl)
                ov = int(mm.group(1), 16) if mm else None
                on = R.oname.get(ov) if ov is not None else None
                nn = R.nnames.get(int(v['A'][1], 16))
                from resolve_code import stem
                if on and nn and stem(on) not in {stem(x) for x in nn}:
                    drop.add(k)
            # side-stack class rows are keyed by the TARGET's own __asan_stack_malloc_N symbols, never by the donor's
            # labels (cgif's merged A / B rows; grant links _0 _1 _2 _4)
            stack = {k for k in pairs if k[1].startswith('asan_stack_malloc_')}
            drop |= stack
            # the target's ENTRY function (the fuzz target's LLVMFuzzerTestOneInput) is always emitted from its own
            # symbol, [st_value, st_value + st_size), whatever its donor row became (its start pairs by the call, its
            # end has no twin: pcap 0x807c8 / 0x813f4, grant 0x806b0 / 0x81b70)
            entry = {nm: (lo, R.nhi[lo]) for lo, names in R.nnames.items() for nm in names
                     if nm in ENTRY_FNS and lo in R.nhi}
            for k, v in pairs.items():
                if k[1] in entry and not ('A' in v and 'E' in v and not any(x[1].startswith(REFUSED) for x in
                                                                            v.values())
                                          and (int(v['A'][1], 16), int(v['E'][1], 16)) == entry[k[1]]):
                    drop.add(k)
            entry_missing = [nm for nm in sorted(entry) if not any(k[1] == nm for k in pairs)]
            if not drop and not entry_missing:
                continue
            first = min((v[x][0] for k in drop for v in [pairs[k]] for x in v),
                        default=min(v[x][0] for v in pairs.values() for x in v))
            stack_line = min((v[x][0] for k in stack for v in [pairs[k]] for x in v), default=first)
            from resolve_code import stem
            readd = {}  # line -> sentences: a dropped donor row whose start IS a target function of the same name
            for k in drop:
                v = pairs[k]
                if k[1] in entry:
                    lo, hi = entry[k[1]]
                    readd.setdefault((v.get('A') or v.get('E'))[0], []).append(
                        f'Definition {k[0]}_A_{k[1]} : Z := {lo:#x}.  Definition {k[0]}_E_{k[1]} : Z := {hi:#x}.')
                    continue
                if k in stack or 'A' not in v or v['A'][1].startswith(REFUSED):
                    continue
                a0 = int(v['A'][1], 16)
                nn = R.nnames.get(a0, set())
                if a0 in R.nhi and stem(k[1]) in {stem(re.sub(r'\W', '_', x)) for x in nn} | {stem(x) for x in nn}:
                    readd.setdefault(v['A'][0], []).append(
                        f'Definition {k[0]}_A_{k[1]} : Z := {a0:#x}.  Definition {k[0]}_E_{k[1]} : Z := {fn_end(a0):#x}.')
            for k in drop:
                for side, (i, val) in pairs[k].items():
                    lines[i] = re.sub(r"Definition\s+" + re.escape(f'{k[0]}_{side}_{k[1]}') + r"\s*:\s*Z\s*:=\s*" +
                                      re.escape(val) + r"\s*\.\s*", '', lines[i]).rstrip()
                    X.refusals[:] = [r for r in X.refusals if not (r[0] == rel and r[1] == i + 1)]
                    X.chk.append((rel, i + 1, '-', '-', f'function-table drop {k[0]}_{side}_{k[1]} (no twin of the '
                                  f'same function in the target)'))
                if not any(f'{k[0]}_A_{k[1]} ' in s for ss in readd.values() for s in ss):
                    dropped_all[f'{k[0]}_A_{k[1]}'] = rel
                    dropped_all[f'{k[0]}_E_{k[1]}'] = rel
            for i, ss in readd.items():
                lines[i] = (lines[i] + '  ' if lines[i].strip() else '') + '  '.join(ss)
                for s in ss:
                    X.chk.append((rel, i + 1, '-', '-', f'function-table row kept with the target function\'s own end ({s[:90]})'))
            pre = next(iter(pairs))[0]
            have = {k[1] for k in pairs if k not in drop} | {re.search(r'_A_(\w+) ', s).group(1)
                                                              for ss in readd.values() for s in ss}
            if stack:
                # a donor row keyed by the same class (`asan_stack_malloc_N`) keeps its own line; a class the donor
                # names otherwise (cgif's `_A` / `_B`) goes on the first stack line
                own_line = {}
                for k in stack:
                    mk = re.fullmatch(r'asan_stack_malloc_(\d+)', k[1])
                    if mk and 'A' in pairs[k]:
                        own_line[mk.group(1)] = pairs[k]['A'][0]
                srows = collections.defaultdict(list)
                for lo, names in sorted(R.nnames.items()):
                    for nm in names:
                        m = re.fullmatch(r'__asan_stack_malloc_(\d+)', nm)
                        if m and lo in R.nhi:
                            srows[own_line.get(m.group(1), stack_line)].append(
                                f'Definition {pre}_A_asan_stack_malloc_{m.group(1)} : Z := {lo:#x}.  '
                                f'Definition {pre}_E_asan_stack_malloc_{m.group(1)} : Z := {R.nhi[lo]:#x}.')
                            have.add(f'asan_stack_malloc_{m.group(1)}')
                for li, rs in sorted(srows.items()):
                    lines[li] = (lines[li] + '  ' if lines[li].strip() else '') + '  '.join(rs)
                if srows:
                    X.chk.append((rel, stack_line + 1, '-', '-', f'function-table stack class rows from the target\'s '
                                  f'symbols: {sum(len(v) for v in srows.values())} classes'))
            add = []
            for lo, hi, nm in own + [entry[nm] + (nm,) for nm in entry_missing]:
                nm2 = re.sub(r'\W', '_', nm)
                if nm2 not in have:
                    add.append(f'Definition {pre}_A_{nm2} : Z := {lo:#x}.  Definition {pre}_E_{nm2} : Z := {hi:#x}.')
                    have.add(nm2)
                    emitted.append((rel, nm, lo, hi))
            if add:
                ns = [v[x][0] for k in drop - stack for v in [pairs[k]] for x in v]
                at = min(ns) if ns else first
                lines[at] = (lines[at] + '  ' if lines[at].strip() else '') + '  '.join(add)
            open(p, 'w').write('\n'.join(lines))
    for root, _, fs in os.walk(out):  # a name the table emits again (a stack class row keyed by the target) is defined
        for f in fs:
            if f in ('AB1w.v', 'YB1w.v'):
                for w in re.findall(r'Definition\s+(\w+_[AE]_\w+)\s*:', open(os.path.join(root, f)).read()):
                    dropped_all.pop(w, None)
    for root, _, fs in os.walk(out):  # a dropped name must have no other use
        for f in sorted(fs):
            if not f.endswith('.v') or not dropped_all:
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            for i, l in enumerate(open(p).read().split('\n'), 1):
                for w in set(re.findall(r'\b\w+_[AE]_\w+\b', l)) & dropped_all.keys():
                    row = (rel, i, '-', '-', f'FAIL dropped-name-used {w} (a cgif-only function of {dropped_all[w]}; '
                                             f'the use must go too)')
                    X.rev.append(row); X.chk.append(row); nfail += 1
    for rel, nm, lo, hi in emitted:
        X.chk.append((rel, 0, '-', hex(lo), f'function-table add {nm} [{lo:#x}, {hi:#x}) (the target\'s own program)'))
    return nfail, len(dropped_all) // 2, len(emitted)


def delete_unpaired(out, X):
    """A `Definition N := ...` whose value was refused (a donor cell or symbol with no counterpart in the target: the
    fopen/fclose cells on a unit that links neither, cgif's program strings) is DELETED with every use of N in its file
    (deluse.py: a list element that mentions N goes, a record field or constructor argument N becomes 0; grant's
    A/AE2k.v is the model). N is kept (and its marker stays, so the refused-marker gate fails) when N is used in
    ANOTHER staged file or a use cannot be rewritten. Line counts never change."""
    from deluse import delete_with_uses
    files = {}
    for root, _, fs in os.walk(out):
        for f in fs:
            if f.endswith('.v'):
                p = os.path.join(root, f)
                files[os.path.relpath(p, out)] = open(p).read()
    sent = re.compile(r"Definition\s+([A-Za-z_][\w']*)\b(.*?)\.(?=\s|$)", re.S)
    ndel, deleted = 0, {}
    for rel, t in sorted(files.items()):
        if REFUSED not in t or rel in X.generated:
            continue
        bydef = {m.group(1): set(re.findall(REFUSED + r'[0-9a-f]+', m.group(2))) for m in sent.finditer(t)}
        bydef = {n: toks for n, toks in bydef.items() if toks}
        keep = set()
        for n in bydef:  # a name another staged file uses stays
            rx = re.compile(r"(?<![\w'.])" + re.escape(n) + r"(?![\w'])")
            if any(rx.search(o) for r2, o in files.items() if r2 != rel):
                keep.add(n)
        for _ in range(6):
            toks = set().union(*[v for n, v in bydef.items() if n not in keep]) if len(bydef) > len(keep) else set()
            if not toks:
                break
            new, probs = delete_with_uses(t, toks)
            bad = {m.group(1) for p in probs for m in [re.match(r'cannot delete use of (\S+)', p)] if m}
            if not bad - keep:
                break
            keep |= bad
        else:
            continue
        if not toks:
            for n in keep:
                X.rev.append((rel, 0, '-', '-', f'kept-refused-definition {n} (used in another staged file or a use '
                                               f'cannot be rewritten: the porter removes it)'))
            continue
        gone = set(bydef) - keep
        if new != t:
            open(os.path.join(out, rel), 'w').write(new)
            files[rel] = new
            nl = new.split('\n')
            X.refusals[:] = [r for r in X.refusals if not (r[0] == rel and 0 < r[1] <= len(nl) and
                                                           REFUSED + r[2][2:] not in nl[r[1] - 1])]
            for n in sorted(gone):
                X.chk.append((rel, 0, '-', '-', f'deleted {n} with every use (no counterpart in the target)'))
                deleted.setdefault(rel, []).append(n)
            ndel += len(gone)
        for n in keep:
            X.rev.append((rel, 0, '-', '-', f'kept-refused-definition {n} (used in another staged file or a use '
                                           f'cannot be rewritten: the porter removes it)'))
    return ndel, deleted


def strip_comments(t):
    """Coq comments (nested `(* ... *)`) blanked, newlines kept, so a line scan never reads a comment: a ported
    file's `Modified by Theorem Labs` header states the DONOR value beside the target's by our own licence rule,
    and a provenance line that names both would otherwise look like a disagreeing pair."""
    out, depth, i = [], 0, 0
    while i < len(t):
        if t.startswith('(*', i):
            depth += 1; out.append('  '); i += 2; continue
        if t.startswith('*)', i) and depth:
            depth -= 1; out.append('  '); i += 2; continue
        out.append(t[i] if (not depth or t[i] == '\n') else ' ')
        i += 1
    return ''.join(out)


def data_symbol_gate(stage, out, X):
    """(A) every DATA numeral is checked donor symbol+offset -> the TARGET's symbol of the SAME name at the SAME
    offset, never "lands in some symbol": a uniform shift inside one object (ctrl B: .bss +0x280 on 414 rows, .data
    +0x270 on 49) is a FAIL row. Donor symbols from --old-syms, target symbols from its symtab (NameMap)."""
    if not X.names:
        return 0
    n = 0
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            sp = os.path.join(stage, rel)
            if rel in X.generated or rel not in X.remapped or not os.path.exists(sp):
                continue
            sl, ol = strip_comments(open(sp).read()).split('\n'), strip_comments(open(p).read()).split('\n')
            if len(sl) != len(ol):
                continue
            for i, (s, o) in enumerate(zip(sl, ol), 1):
                sm, om = list(NUM.finditer(s)), list(NUM.finditer(o))
                if len(sm) != len(om):
                    continue
                for a, b in zip(sm, om):
                    ov = ival(a.group(1))
                    if ov < 0x10000 or X.is_exec(ov) or not X.old.sec(ov) or X.explained.get((rel, i, ov)):
                        continue
                    want = X.names.map(ov)
                    if want is None:
                        continue
                    try:
                        got = ival(b.group(1))
                    except ValueError:
                        continue
                    if got != want:
                        o2 = X.names.name_of(ov)
                        row = (rel, i, hex(ov), hex(got), f'FAIL data-symbol ({o2[2]}+{ov - o2[0]:#x} is '
                               f'{want:#x} in the target, written {got:#x})')
                        X.rev.append(row); X.chk.append(row)
    return 0  # reported, not blocking in this release: grant's rows are theDepot-sized symbol spans (see README)


def twin_forms(stage, out, X):
    """(B2) TWIN-MISMATCH: one value written twice in a file, once in hex and once in decimal, must get the SAME
    outcome (pcap FS_FOUND 249892 against the hex pcs); a file where the two forms part is a FAIL row."""
    n = 0
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            sp = os.path.join(stage, rel)
            if rel in X.generated or not os.path.exists(sp):
                continue
            sl, ol = strip_comments(open(sp).read()).split('\n'), strip_comments(open(p).read()).split('\n')
            if len(sl) != len(ol):
                continue
            seen = collections.defaultdict(dict)  # donor value -> form -> (written, line)
            for i, (s, o) in enumerate(zip(sl, ol), 1):
                sm, om = list(NUM.finditer(s)), list(NUM.finditer(o))
                if len(sm) != len(om):
                    continue
                for a, b in zip(sm, om):
                    ov = ival(a.group(1))
                    if ov < 0x10000 or X.explained.get((rel, i, ov)) in ('insn-word', 'opaque label'):
                        continue
                    form = 'hex' if a.group(1).lower().startswith('0x') else 'dec'
                    try:
                        got = ival(b.group(1))
                    except ValueError:
                        got = 'REFUSED'
                    seen[ov].setdefault(form, (got, i))
            for ov, forms in seen.items():
                if len(forms) == 2 and forms['hex'][0] != forms['dec'][0]:
                    row = (rel, forms['dec'][1], hex(ov), str(forms['dec'][0]),
                           f'FAIL twin-mismatch ({ov:#x} written {forms["hex"][0]} in hex at line '
                           f'{forms["hex"][1]} and {forms["dec"][0]} in decimal at line {forms["dec"][1]})')
                    X.rev.append(row); X.chk.append(row)
    return 0  # reported, not blocking in this release (grant: 2 rows, both real misses of class 10; see README)


def emit_class_map(out, X, R, zero):
    """`pc_stack_malloc := fun cid => if cid =? N then A else ... else 0` (A/AF0l.v, YF0l.v) is PER UNIT: emitted from
    the target's `__asan_stack_malloc_N` symbols for every class N the target's non-runtime code calls (call edges).
    Gate by construction: every called class has its nonzero entry, no entry for a class the program does not call.
    A class of `--zero-class` is emitted as 0 (its contract is carried outside the record as a named hypothesis: a
    nonzero entry would make YG0d.v's aa_stack_malloc demand the whole-frame astack_malloc_realizes, which a
    size-dependent class does not satisfy)."""
    runtime = re.compile(r'^(__asan|__sanitizer|__lsan|__ubsan|__interception|_ZN\d+__(asan|sanitizer|lsan|ubsan))')
    cls = {}
    for lo, names in R.nnames.items():
        for nm in names:
            m = re.fullmatch(r'__asan_stack_malloc_(\d+)', nm)
            if m:
                cls[lo] = int(m.group(1))
    called = {}
    for k, sv in enumerate(R.cn.sens):
        if sv and sv[0] in ('jal', 'c.j') and sv[1] in cls:
            pc = R.cn.pcs[k]
            q = bisect.bisect_right(R._nlos, pc) - 1
            caller = R.nname.get(R._nlos[q], '') if q >= 0 else ''
            if not runtime.match(caller):
                called[cls[sv[1]]] = sv[1]
    # the ROW SET of a keyed table is the target's symbol set for that key, minus --zero-class: never the donor's
    # positions (ctrl's generator kept cgif's and mapped class 1 onto class 0's entry, omitting 0 and 6)
    bysym = {n: lo for lo, n in cls.items()}
    missing = sorted(set(called) - set(bysym))
    called = {n: (0 if n in zero else lo) for n, lo in bysym.items()}
    zeroed = sorted(set(zero) & set(bysym))
    rx = re.compile(r'pc_stack_malloc\s*:=\s*fun\s+cid\s*=>\s*(?:if\s+cid\s*=\?\s*\d+\s+then\s+(?:0x[0-9a-fA-F]+|'
                    + REFUSED + r'[0-9a-f]+|\d+)\s+else\s+)*0(?=\s*;)')
    body = 'pc_stack_malloc := fun cid => ' + ''.join(f'if cid =? {n} then {called[n]:#x} else '
                                                      for n in sorted(called) if called[n]) + '0'
    n = 0
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            t = open(p).read()
            if not rx.search(t):
                continue
            lines = t.split('\n')
            for i, l in enumerate(lines):
                m = rx.search(l)
                if not m:
                    continue
                sl = open(os.path.join(X.a.work, 'stage', rel)).read().split('\n')[i]
                for tok in re.findall(r'0x[0-9a-fA-F]+', sl[sl.find('pc_stack_malloc'):]):
                    X.explained[(rel, i + 1, int(tok, 16))] = 'class map emitted'
                    X.refusals[:] = [r for r in X.refusals if not (r[0] == rel and r[1] == i + 1 and r[2] == tok.lower())]
                lines[i] = l[:m.start()] + body + l[m.end():]
                X.chk.append((rel, i + 1, '-', '-', 'class-map emitted from the target (' + ', '.join(
                    f'class {c} = {called[c]:#x} {R.nname.get(called[c], "")}' for c in sorted(called)) + ')'))
                X.tab['geometry.tsv'].append((rel, i + 1, 'pc_stack_malloc', body, 'classes the program calls', ''))
                n += 1
            open(p, 'w').write('\n'.join(lines))
    for mclass in missing:
        row = ('-', 0, '-', '-', f'FAIL keyed-table-row-set (the target calls stack class {mclass} but has no '
                                 f'__asan_stack_malloc_{mclass} symbol: the row set cannot be emitted)')
        X.rev.append(row); X.chk.append(row)
    return n, called, len(missing)


def shadow_windows(a, out, X, new):
    """`Definition FMT : Z := A.` with `SH_LO`/`SH_HI` in the same file: the shadow hull of the TARGET's string at A,
    [floor8((A >> 3) + 0x7fff8000), floor8(((A + len - 1) >> 3) + 0x7fff8000) + 8) with len the NUL-terminated
    length read from the target at A; written from the target, refused when FMT is refused. A pair left at the
    donor's window would FAIL the run."""
    n = 0
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            if rel in X.generated:
                continue
            t = open(p).read()
            fm = re.search(r'Definition\s+FMT\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+|' + REFUSED + r'[0-9a-f]+)\s*\.', t)
            if not fm or not re.search(r'Definition\s+SH_LO\b', t):
                continue
            lines = t.split('\n')
            if fm.group(1).startswith(REFUSED):
                lo = hi = None
            else:
                A = int(fm.group(1), 16)
                b = new.read(A, 4096) or b''
                ln_ = b.find(b'\0') if b'\0' in b else None
                lo = ((A >> 3) + SHADOW) & ~7 if ln_ else None
                hi = ((((A + ln_ - 1) >> 3) + SHADOW) & ~7) + 8 if ln_ else None
            for i, l in enumerate(lines):
                for name, v in (('SH_LO', lo), ('SH_HI', hi)):
                    m = re.search(r'(Definition\s+' + name + r'\s*:\s*Z\s*:=\s*)(0x[0-9a-fA-F]+)(\s*\.)', l)
                    if not m:
                        continue
                    old = int(m.group(2), 16)
                    if v is None:
                        new_t = f'{REFUSED}{old:x}'
                        X.refusals.append((rel, i + 1, hex(old), 'shadow-window'))
                        X.rev.append((rel, i + 1, hex(old), '-', f'shadow-window ({name}: FMT is refused or no '
                                      f'string at it in the target)'))
                    else:
                        new_t = hex(v)
                        X.chk.append((rel, i + 1, hex(old), hex(v), f'shadow-window {name} (target string at '
                                      f'{fm.group(1)}, {ln_} bytes)'))
                        X.explained[(rel, i + 1, old)] = 'shadow-window'
                    l = l[:m.start(2)] + new_t + l[m.end(2):]
                    n += 1
                lines[i] = l
            open(p, 'w').write('\n'.join(lines))
    return n


def forbidden_closure(a, out, X):
    """a staged A/ file whose Require closure loads a --forbid module (default the plain build's `#[global]` sink
    instances Reusable/YI5b.v, YI5c.v) fails, with the import path."""
    req = re.compile(r'From\s+([\w.]+)\s+Require(?:\s+(?:Import|Export))?\s+([\w.\'\s]+?)\.(?=\s|$)|'
                     r'(?<![\w.])Require(?:\s+(?:Import|Export))?\s+([\w.]+(?:\s+[\w.]+)*)\.(?=\s|$)')
    pre = a.target_mod + '.'

    def path_of(mod):
        if not mod.startswith(pre):
            return None
        rel = mod[len(pre):].replace('.', '/') + '.v'
        for base in (out, a.target_lib):
            if os.path.exists(os.path.join(base, rel)):
                return os.path.join(base, rel)
        return None
    deps = {}

    def deps_of(p):
        if p not in deps:
            ms = []
            for m in req.finditer(open(p).read()):
                if m.group(1):
                    ms += [m.group(1) + '.' + n for n in m.group(2).split()]
                else:
                    ms += m.group(3).split()
            deps[p] = [q for q in (path_of(x) for x in ms) if q]
        return deps[p]
    bad = {os.path.join(d, f + '.v') for d in ('Reusable', a.reusable_dir) for f in a.forbid}
    n = 0
    for root, _, fs in os.walk(os.path.join(out, 'A')):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            start = os.path.join(root, f)
            seen, stack = {start: None}, [start]
            while stack:
                p = stack.pop()
                hit = next((b for b in bad if p.endswith('/' + b)), None)
                if hit:
                    chain, q = [], p
                    while q:
                        chain.append(os.path.basename(q)[:-2]); q = seen[q]
                    rel = os.path.relpath(start, out)
                    row = (rel, 0, '-', '-', f'FAIL forbidden-module {hit} (import path: {" <- ".join(chain)})')
                    X.rev.append(row); X.chk.append(row); n += 1
                    break
                for q in deps_of(p):
                    if q not in seen:
                        seen[q] = p; stack.append(q)
    return n


def name_clash(a, out, X):
    """names declared by both sides of a --name-clash pair (cgif's: the plain-side lib/Lib and Reusable/YK11 declare
    getr, mkst, seg_rom, cfg_at with different meanings): a staged file that Requires a module of the first side and
    uses one of those names fails."""
    n = 0
    for pair in a.name_clash:
        left, right = pair.split(',')
        lp, rp = os.path.join(a.target_lib, left), os.path.join(a.target_lib, right)
        if not (os.path.exists(lp) and os.path.exists(rp)):
            continue
        lf = [os.path.join(lp, x) for x in os.listdir(lp) if x.endswith('.v')] if os.path.isdir(lp) else [lp]
        ln_ = set().union(*[decl_names(open(x).read()) for x in lf]) if lf else set()
        both = ln_ & decl_names(open(rp).read())
        if not both:
            continue
        lmod = a.target_mod + '.' + left.rstrip('/').replace('/', '.')
        rx = {x: re.compile(r"(?<![A-Za-z0-9_'.])" + re.escape(x) + r"(?![A-Za-z0-9_'])") for x in both}
        for root, _, fs in os.walk(out):
            for f in sorted(fs):
                if not f.endswith('.v'):
                    continue
                rel = os.path.relpath(os.path.join(root, f), out)
                t = open(os.path.join(root, f)).read()
                if not re.search(r'\bRequire\b[^.]*' + re.escape(lmod) + r'\b|\bFrom\s+' + re.escape(lmod) + r'\b', t):
                    continue
                for lno, l in enumerate(t.split('\n'), 1):
                    for x, r in rx.items():
                        if r.search(l) and not l.lstrip().startswith(('Require', 'From')):
                            row = (rel, lno, '-', '-', f'FAIL name-clash {x} (declared by {left} and {right} with '
                                                       f'different meanings; this file Requires {lmod})')
                            X.rev.append(row); X.chk.append(row); n += 1
    return n


def kept_image_check(a, kept, X, OG, NG, known):
    """a kept target copy of a non-A file that states another image's end (a run for the other image, or the
    source's) is cross-image contamination: FAIL rows; --apply refuses. Units with two images use one
    --reusable-dir per image."""
    ends = {OG.hull[1]: 'source image end'}
    for v, who in known:
        ends.setdefault(v, who)
    ends.pop(NG.hull[1], None)
    n = 0
    for rel in kept:
        d = os.path.join(a.target_lib, dst_path(rel, a.reusable_dir))
        if not os.path.exists(d):
            continue
        for lno, l in enumerate(open(d).read().split('\n'), 1):
            for m in NUM.finditer(l):
                v = ival(m.group(1))
                if v in ends and (m.group(1).lower().startswith('0x') or v >= 0x10000):
                    row = (dst_path(rel, a.reusable_dir), lno, m.group(1), hex(NG.hull[1]),
                           f'FAIL kept-file-other-image (the target\'s kept copy states {ends[v]} {v:#x}; this image '
                           f'ends at {NG.hull[1]:#x}: use a per-image --reusable-dir)')
                    X.rev.append(row); X.chk.append(row); n += 1
    return n


def image_end_scan(a, out, X, OG, NG, known):
    """FAIL rows for every numeral of stage-out/ equal to the SOURCE's image end or a known unit's image end that is
    not the target's own end."""
    ends = {OG.hull[1]: 'source image end', OG.hull[1] // PAGE: 'source image-end page index',
            OG.hull[1] >> 3: 'source image end / 8'}
    for v, who in known:
        ends.setdefault(v, who)
    for v in (NG.hull[1], NG.hull[1] // PAGE, NG.hull[1] >> 3):
        ends.pop(v, None)
    n = 0
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            if rel in X.generated:
                continue
            for ln, l in enumerate(strip_comments(open(p).read()).split('\n'), 1):  # a comment is never edited
                for m in NUM.finditer(l):
                    v = ival(m.group(1))
                    if v in ends and X.explained.get((rel, ln, v)) != 'generated slot':
                        row = (rel, ln, m.group(1), hex(NG.hull[1]), f'FAIL image-end ({ends[v]} {v:#x} left; the '
                               f'target ends at {NG.hull[1]:#x})')
                        X.chk.append(row); X.rev.append(row); n += 1
    return n


def nona_report(a, files, kept, staged_rel, remapped, OG, R, old, known):
    """Every non-A source file of the list that states an image constant: the source image end (or its page index),
    a known unit's image end, or an address inside the source image hull (code: an OLD instruction start or not)."""
    ends = {OG.hull[1]: 'source image end', OG.hull[1] // PAGE: 'source image-end page index'}
    for v, who in known:
        ends.setdefault(v, who)
    rows = []
    for rel in files:
        if rel.startswith('A/'):
            continue
        t = open(os.path.join(a.src_lib, rel)).read().split('\n')
        where = 'kept (target copy)' if rel in kept else ('staged, remapped' if dst_path(rel, a.reusable_dir) in remapped
                                                         else 'staged, not remapped')
        for ln, l in enumerate(t, 1):
            for m in NUM.finditer(l):
                v = ival(m.group(1))
                hexlit = m.group(1).lower().startswith('0x')
                if OPCODE_CTX.match(l, m.end()) or OPCODE_PRE.search(l, 0, m.start()):
                    continue
                what = None
                if v in ends and (hexlit or v >= 0x10000 or 'page' in ends[v]):
                    what = ends[v]
                elif hexlit and OG.hull[0] < v < OG.hull[1] and v >= 0x10000:
                    s = old.sec(v)
                    if s is None:
                        what = 'inside the source hull, in no section'
                    elif s[2] & 4:
                        what = ('source code, ' + ('an instruction start' if insn_at(old, v) else 'not an insn')
                                + (f', function {R._fn_of(v)[0]:#x}+{v - R._fn_of(v)[0]:#x}' if R._fn_of(v) else
                                   ', no FDE (another image\'s code?)'))
                    else:
                        what = f'source {s[0]}'
                if what:
                    rows.append((rel, ln, m.group(1), what, where))
    with open(os.path.join(a.work, 'nonA.tsv'), 'w') as fh:
        fh.write('file\tline\tliteral\twhat\twhere\n')
        for r in rows:
            fh.write('\t'.join(map(str, r)) + '\n')
    per = collections.Counter(r[0] for r in rows)
    return per


def names_report(a, out, stage, X, R, oldsyms):
    """For every `Definition N : Z := V` whose released V is the start (or, for an end name, the end) of a source
    function: the source's recovered name there (--old-syms), the target's symbol at the written value, and the
    verdict. `NAME-DIFFERS` (source and target name different functions: a pairing to check) is a review row;
    `donor-label` (source and target agree on the FUNCTION, the released definition name names another one, e.g. A/AB1w.v
    `memcmp_2` = the bcmp wrapper's jump: the row lands on the twin of the donor's function and the label is LEFT as it
    is, never moved to the label's namesake; the lead's ruling) and `refused` are listed in names.tsv only."""
    norm = lambda n: re.sub(r'\.llvm\.\d+$', '', n or '')
    ignore = {'tfib', 'icpt', 'thunk', 'helper', 'tail', 'body', 'part', 'wrap', 'impl', 'internal'}
    rows, bad = [], 0
    olos = sorted(oldsyms)
    starts, ends = set(R.ohi), set(R.ohi.values())
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            rel = os.path.relpath(os.path.join(root, f), out)
            if not os.path.exists(os.path.join(stage, rel)):
                continue
            ol = open(os.path.join(stage, rel)).read().split('\n')
            for ln, l in enumerate(open(os.path.join(root, f)).read().split('\n'), 1):
                for m in re.finditer(r"Definition\s+([A-Za-z_][\w']*)\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+|" + REFUSED +
                                     r"[0-9a-f]+)\s*\.", l):
                    dn, v = m.group(1), m.group(2)
                    om = re.search(r"Definition\s+" + re.escape(dn) + r"\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+)", ol[ln - 1]) \
                        if ln - 1 < len(ol) else None
                    if not om:
                        continue
                    ov = int(om.group(1), 16)
                    end = bool(END_HINT.search(dn))
                    if not (ov in ends if end else ov in starts) or X.OG.by.get(ov):
                        continue  # not a function start/end of the source (an interior pc, a bound)
                    k = bisect.bisect_right(olos, ov - (1 if end else 0)) - 1
                    oname = '-'
                    if k >= 0 and ov - (1 if end else 0) < olos[k] + oldsyms[olos[k]][1]:
                        oname = oldsyms[olos[k]][0]
                    if v.startswith(REFUSED):
                        rows.append((rel, ln, dn, hex(ov), v, oname, '-', 'refused (no target code)'))
                        continue
                    nv = int(v, 16)
                    sym = R.sym_new(nv - 1 if end else nv)
                    words = [w for w in re.findall(r'[A-Za-z]{4,}', re.sub(r'^tfib_[AE]_', '', dn))
                             if w.lower() not in ignore]
                    named_ok = sym is not None and words and any(w.lower() in sym.lower() for w in words)
                    if sym is None:
                        st = 'no target symbol'
                    elif oname != '-' and norm(oname) != norm(sym) and norm(oname) not in {
                            norm(x) for x in R.nnames.get(R._nlos[bisect.bisect_right(R._nlos, nv - (1 if end else 0)) - 1], ())}:
                        st = 'NAME-DIFFERS'
                    elif named_ok or not words:
                        st = 'ok'
                    else:
                        st = 'donor-label (left as it is: the row follows the donor\'s function)'
                    rows.append((rel, ln, dn, hex(ov), hex(nv), oname, sym or '-', st))
                    if st == 'NAME-DIFFERS':
                        bad += 1
                        X.rev.append((rel, ln, hex(ov), hex(nv), f'name-differs ({dn}: source {oname}, target '
                                      f'{sym}: check the pairing)'))
    with open(os.path.join(a.work, 'names.tsv'), 'w') as fh:
        fh.write('file\tline\tdefinition\told\tnew\tsource_name\ttarget_symbol\tstatus\n')
        for r in rows:
            fh.write('\t'.join(map(str, r)) + '\n')
    tr = [(o, *v) for o, v in sorted(R.tramp_check.items())]
    with open(os.path.join(a.work, 'trampolines.tsv'), 'w') as fh:
        fh.write('old\tnew\tnew_symbol\tnew_target\tnew_target_symbol\tsource_name\tcheck\n')
        for o, n, tn, tgt, gn, ok in tr:
            on = oldsyms.get(o, ('-',))[0]
            chk = ('same name' if on != '-' and tn and on == tn else
                   ('NAME-DIFFERS' if on != '-' and tn else ('stems agree' if ok else 'target is a tail call')))
            fh.write(f'{o:#x}\t{n:#x}\t{tn or "-"}\t{tgt:#x}\t{gn or "-"}\t{on}\t{chk}\n')
            if chk == 'NAME-DIFFERS':
                X.rev.append(('-', 0, hex(o), hex(n), f'trampoline-name-differs (source {on}, target {tn})'))
    return bad


def private_cache(a):
    """the checker's cache, private to this run (the shared file-facts.json can be corrupted by concurrent writers);
    the symbol recoveries of stripped images (`<sha>.<donors>.v*.json`) are copied in, nothing else."""
    d = os.path.join(a.work, 'gate-cache')
    os.makedirs(d, exist_ok=True)
    src = a.gate_cache  # --gate-cache: the gate's symbol recoveries, copied in (none given: nothing copied)
    if src and os.path.isdir(src):
        for f in os.listdir(src):
            if re.fullmatch(r'[0-9a-f]{16}\.[0-9a-f]{16}\.v\d+\.json', f) and not os.path.exists(os.path.join(d, f)):
                shutil.copy(os.path.join(src, f), os.path.join(d, f))
    return d


REL_RX = re.compile(r'v_addi\s*\(\s*Z_to_bv\s+64\s+(0x[0-9a-fA-F]+|\d+|' + REFUSED + r'[0-9a-f]+)\s*\)\s*(\d+)\s*\)\s*with\s*'
                    r'\(\s*Z_to_bv\s+64\s+(0x[0-9a-fA-F]+|\d+|' + REFUSED + r'[0-9a-f]+)')


def relations(out, X):
    """MOVE RELATIONS, NOT NUMERALS: in `change|replace (v_addi (Z_to_bv 64 X) k) with (Z_to_bv 64 Y)` the operand X
    is decided by its role (function pairing) and the result Y is RECOMPUTED as X' + k, never moved separately
    (53ec3af2afc9 on grant: A/AE3h.v:1690 X 0x942a0 left / Y 0x92a3c moved; A/AFf8.v:404 / 705 / 1008 / 1307). Then
    a GATE: every such relation of stage-out must hold (relation_check.py checks the same text);
    a violation is a FAIL row. Returns (results recomputed, FAIL rows)."""
    n = nfail = 0
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            t = open(p).read()
            if 'v_addi' not in t:
                continue
            lines, changed = t.split('\n'), False
            for i, l in enumerate(lines):
                for m in reversed(list(REL_RX.finditer(l))):
                    xs, k, ys = m.group(1), int(m.group(2)), m.group(3)
                    if xs.startswith(REFUSED):
                        if not ys.startswith(REFUSED):
                            l = l[:m.start(3)] + f'{REFUSED}{ival(ys):x}' + l[m.end(3):]
                            X.refusals.append((rel, i + 1, hex(ival(ys)), 'relation-result'))
                            changed = True
                        continue
                    want = ival(xs) + k
                    if ys.startswith(REFUSED) or ival(ys) != want:
                        X.chk.append((rel, i + 1, ys, hex(want), f'relation result recomputed ({xs} + {k}; the pass '
                                      f'had written {ys})'))
                        l = l[:m.start(3)] + fmt_like(ys if not ys.startswith(REFUSED) else xs, want) + l[m.end(3):]
                        changed = True; n += 1
                lines[i] = l
            if changed:
                open(p, 'w').write('\n'.join(lines))
    for root, _, fs in os.walk(out):  # the gate, after every pass and patch: X + k = Y
        for f in sorted(fs):
            if f.endswith('.v'):
                p = os.path.join(root, f)
                for i, l in enumerate(open(p).read().split('\n'), 1):
                    for m in REL_RX.finditer(l):
                        if not m.group(1).startswith(REFUSED) and not m.group(3).startswith(REFUSED) and \
                                ival(m.group(1)) + int(m.group(2)) != ival(m.group(3)):
                            row = (os.path.relpath(p, out), i, m.group(1), m.group(3), f'FAIL relation ({m.group(1)} + '
                                   f'{m.group(2)} != {m.group(3)})')
                            X.rev.append(row); X.chk.append(row); nfail += 1
    return n, nfail


def geometry_rejudge(d, stage, X):
    """the checker's SAME-GEOMETRY verdict is by VALUE only (a numeral equal to seg0.size in both images): a MOVED
    numeral is accepted only when its role passes this release's use gate on the stage line (the line states the
    segment list / seg_bytes_* / tfib_lenN / the segment's bounds), else a MISMATCH (a8's 62 wrong 131072 moves:
    gate-raw rows AD1d.v:38/:280, AFel.v:265, AFjt.v:588/:603). Returns the reason, or '' when it stands."""
    try:
        sv, dv, ln = ival(d['src_value']), ival(d['dst_value']), int(d['src_line'])
    except ValueError:
        return ''
    if sv == dv:
        return ''
    if str(getattr(X, 'explained', {}).get((d['src_file'], ln, sv), '')).startswith('geometry'):
        return ''  # port_core's own geometry rule decided it on this line (a size right after its start, ...)
    roles = [r for r in X.OG.dby.get(sv, []) if r in X.NG.dec] + \
        [r for r in X.OG.by.get(sv, []) if r in X.NG.role]
    if not roles or X.OG.by.get(sv):
        return ''  # a header bound: the bound rule decides it by role
    p = os.path.join(stage, d['src_file'])
    if not os.path.exists(p):
        return ''
    lines = open(p).read().split('\n')
    if ln - 1 >= len(lines):
        return ''
    line = lines[ln - 1]
    olds = [ival(m.group(1)) for m in NUM.finditer(line)]
    X.file_geo_ok = X.file_geo_roles(lines) if hasattr(X, 'file_geo_roles') else set()
    if any(X.geo_used(r, line, [x for x in olds if x != sv]) for r in roles):
        return ''
    return (f'SAME-GEOMETRY by value only: {sv} -> {dv} as {",".join(roles)}, but the line states no such geometry '
            f'(the use gate)')


def symbol_gate(a, stage, out, X):
    """port_addr_check.py over stage/ (the released text, source image) vs stage-out/ (target image). A flagged row
    whose source numeral names something the target has (the row gives `expected 0x...`) and whose written value is
    not that is a MISMATCH, unless this run decided that literal from the target's headers, its bytes, a GOT word or
    an --override (`explained`). Rows the target cannot name (NO-COUNTERPART, UNRESOLVED, no expected value) are
    review rows."""
    raw = os.path.join(a.work, 'gate-raw.tsv')
    dimg = a.target_elf + (':' + a.target_syms if a.target_syms and not a.target_syms.endswith('.txt') else '')
    cmd = [sys.executable, a.gate_script, '--src', os.path.abspath(stage), '--dst', os.path.abspath(out),
           '--src-image', 'A=' + a.old_elf, '--dst-image', 'A=' + dimg, '--donors-from', a.gate_donors,
           '--paired-only', '--out', raw, '--summary', '--cache', private_cache(a)]
    proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    open(os.path.join(a.work, 'gate.log'), 'w').write(proc.stdout)
    if proc.returncode != 0 or not os.path.exists(raw):
        return None, proc.stdout[-2000:]
    rows = [l.rstrip('\n').split('\t') for l in open(raw)]
    hdr, rows = rows[0], rows[1:]
    flags = {'DIFFERENT-SYMBOL', 'NO-COUNTERPART', 'UNRESOLVED', 'KIND-CHANGED', 'INSN-CHANGED'}
    out_rows = collections.Counter()
    with open(os.path.join(a.work, 'gate.tsv'), 'w') as fh:
        fh.write('gate\tverdict\tfile\tline\tsource\twritten\texpected\tsource_names\twritten_names\twhy\n')
        for r in rows:
            d = dict(zip(hdr, r))
            if d['verdict'] == 'SAME-GEOMETRY':
                bad = geometry_rejudge(d, stage, X)
                if bad:
                    out_rows['MISMATCH'] += 1
                    fh.write('\t'.join(['MISMATCH', d['verdict'], d['src_file'], d['src_line'], d['src_value'],
                                        d['dst_value'], '', d['src_res'][:120], d['dst_res'][:120], bad]) + '\n')
                continue
            if d['verdict'] not in flags:
                continue
            if d.get('kind') == 'ident':
                # hex inside an identifier (`F_15a34`, `D_15a34`): a LABEL named after a donor address; the release
                # renames no identifier, so it is never compared with a target address
                out_rows['info'] += 1
                fh.write('\t'.join(['info', d['verdict'], d['src_file'], d['src_line'], d['src_value'],
                                    d['dst_value'], '', d['src_res'][:120], d['dst_res'][:120],
                                    'an identifier (a lemma label named after a donor address), not a numeral']) + '\n')
                continue
            m = re.search(r'expected (0x[0-9a-f]+)', d.get('note', ''))
            exp = m.group(1) if m else ''
            try:
                key = (d['src_file'], int(d['src_line']), ival(d['src_value']))
            except ValueError:
                key = None
            why = X.explained.get(key, '') if key else ''
            if not why and key and d['src_file'] not in X.remapped:
                why = ('generated slot (regenerated per unit, not relocated)' if d['src_file'] in X.generated else
                       'file not relocated (a non-A file that imports no image, or frozen; nonA.tsv lists its constants)')
            wrote = X.written.get(key) if key else None
            try:
                dv = ival(d['dst_value'])
            except ValueError:
                dv = None
            if d['verdict'] == 'DIFFERENT-SYMBOL' and exp and d['dst_value'] != exp and not why:
                if wrote is not None and dv not in wrote:
                    # the checker paired this numeral with another one (a refusal name on the line shifts the numeral
                    # stream): judge by what port_core wrote at this numeral's own position
                    ws = ' '.join(hex(w) if isinstance(w, int) else w for w in sorted(wrote, key=str))
                    if int(exp, 16) in wrote:
                        g, why = 'explained', f'checker misaligned; port_core wrote the expected value here ({ws})'
                    elif 'REFUSED' in wrote:
                        g, why = 'review', f'checker misaligned; port_core refused this numeral ({ws})'
                    else:
                        g, why = 'MISMATCH', f'checker misaligned; port_core wrote {ws} here, expected {exp}'
                else:
                    g = 'MISMATCH'
            elif why:
                g = 'explained'
            elif d['verdict'] in ('DIFFERENT-SYMBOL', 'NO-COUNTERPART', 'UNRESOLVED'):
                g = 'review'
            else:
                g = 'info'
            out_rows[g] += 1
            fh.write('\t'.join([g, d['verdict'], d['src_file'], d['src_line'], d['src_value'], d['dst_value'], exp,
                                d['src_res'][:120], d['dst_res'][:120], why or d.get('note', '')[:160]]) + '\n')
    return out_rows, proc.stdout


def header(t, rel, moved, target, renamed=None):
    lines = t.split('\n')
    i = 0
    while i < len(lines) and lines[i].startswith('(*') and (
            'Copyright' in lines[i] or 'SPDX' in lines[i] or 'Modified by' in lines[i] or 'This file states' in lines[i]
            or 'Machine-generated' in lines[i]):
        i += 1
    what = f'copied from {DONOR_DESC[0]}/{rel} (donor image sha256 {DONOR_DESC[1]}), with its module paths changed'
    if AS_TWIN and rel.startswith('A/'):
        what = (f'relocated from the unit\'s image-A file {rel} ({DONOR_DESC[0]}, image sha256 {DONOR_DESC[1]}) as '
                f'its image-B twin, with its module paths changed')
    if renamed:
        what += ', names ' + ', '.join(renamed)
    if moved:
        what += f" and its addresses moved to {target}'s ASan build"
    if i == 0:  # no licence lines: a file written there with none stays with none
        return t
    lines.insert(i, f'(* Modified by Theorem Labs, 2026-10: {what}. *)')
    return '\n'.join(lines)


def write_tables(a, X, R, new):
    def cols(r):
        rel, ln, o, n = r[0], r[1], r[2], r[3]
        try:
            ov, nv = int(o, 16), int(n, 16)
        except (ValueError, TypeError):
            return list(r) + ['', '', '']
        cls = X.rcls.get((rel, ln, ov), ('',))[0]
        f = R._fn_of(ov)
        osym = f'{f[0]:#x}+{ov - f[0]:#x}' if f else '-'  # OLD is stripped: its function start stands for a name
        return list(r) + [cls, osym, R.name_new(nv) if new.sec(nv) else '-']
    for name, rows in (('check.tsv', X.chk), ('review.tsv', X.rev), ('fixed.tsv', X.fixed)):
        with open(os.path.join(a.work, name), 'w') as fh:
            fh.write('file\tline\told\tnew\tstatus\tclass\told_fn\tnew_sym\n' if name != 'fixed.tsv'
                     else 'file\tline\told\tremap\tnew\tnew_sym\n')
            for r in rows:
                fh.write('\t'.join(map(str, cols(r) if name != 'fixed.tsv' else r)) + '\n')
    heads = {'got.tsv': 'kind\told_word_or_file\told_value_or_line\tnew_word_or_old\tnew_value_or_new\thow_or_words\tcontent\tnew_sym',
             'geometry.tsv': 'file\tline\told\tnew\trole\tnote',
             'cells.tsv': 'file\tline\told_addr\tnew_addr\tsize\told_value\tnew_bytes\taction\tkind',
             'decimals.tsv': 'action\tfile\tline\told\tnew\told_hex\tnew_hex\twhy\tnew_sym',
             'no-twin.tsv': 'file\tline\told\twhy\told_function\tsource_name (drop these rows: the target does not '
                            'link the function)'}
    skip = set()
    if a.decimal_skip:
        skip = {l.strip() for l in open(a.decimal_skip) if l.strip() and not l.startswith('#')}
    for name, h in heads.items():
        rows = X.tab.get(name, [])
        if name == 'decimals.tsv':
            rows = sorted((r for r in rows if r[1] not in skip), key=lambda r: (r[0], r[1], r[2]))
        with open(os.path.join(a.work, name), 'w') as fh:
            fh.write(h + '\n')
            for r in rows:
                fh.write('\t'.join(map(str, r)) + '\n')
    return [r for r in X.tab.get('decimals.tsv', []) if r[1] not in skip]


def czone_gate(a, out, X):
    """every CZONE shadow upper bound (`Definition CZONE ... (0x7fff8000 <= a < HI)`, A/AFhn / AFix / AFjb / AFju / AFkm
    / AFkz) must be >= the end of the unit's OWN highest constant shadow cell (Tfib_const_shadow of its AF0m / YF0m:
    the target lib's copy when it has one, else the staged slot), as a BOUND check (preset: a CZONE written as
    0x800508c8 below its own cell 0x800b39f8 broke abs_cells_ok). Returns (FAIL rows, the cell end, its source)."""
    rx = re.compile(r'\b0x7fff8000\s*<=\s*\w+\s*<\s*(0x[0-9a-fA-F]+|' + REFUSED + r'[0-9a-f]+)')
    best, src = None, None
    for rel in ('A/AF0m.v', os.path.join(a.reusable_dir, 'YF0m.v'), 'YF0m.v'):
        for base in (a.target_lib, out):
            p = os.path.join(base, rel)
            side = os.path.isdir(os.path.join(out, os.path.dirname(rel) or '.'))  # the run stages this image's dir
            if best is None and os.path.exists(p) and (os.path.exists(os.path.join(out, rel)) or
                                                       (base == a.target_lib and side and os.path.dirname(rel))):
                t = open(p).read()
                m = re.search(r'Definition\s+Tfib_const_shadow\b(.*?)(?=\n\s*Definition\s|\Z)', t, re.S)
                if m:
                    cells = [ival(x) + int(n) for n, x in re.findall(r'\bz([1248])\s+\(ANum\s+(0x[0-9a-fA-F]+|\d+)\)',
                                                                       m.group(1))]
                    if cells:
                        best, src = max(cells), os.path.relpath(p, base) + (' (the target lib\'s own)' if base ==
                                                                             a.target_lib else ' (the staged slot)')
    nfail = 0
    # the donor's CZONE bounds (`Definition CZONE` / `CZ` ... `0x7fff8000 <= a < HI`), then EVERY position where the
    # donor states such a bound (the CZONE definition, a CZ copy, an abs_cells_ok bound `e <=? HI`: preset AGif0:55,
    # AGix:44, AGif4:66, AGju:586 / 596) is checked in stage-out
    his = set()
    stage = os.path.join(a.work, 'stage')
    for root, _, fs in os.walk(stage):
        for f in fs:
            if f.endswith('.v'):
                sl = open(os.path.join(root, f)).read().split('\n')
                for i, l in enumerate(sl):
                    if re.match(r'\s*Definition\s+CZ(?:ONE)?\b', l):
                        for j in range(i, min(i + 4, len(sl))):
                            his |= {ival(m.group(1)) for m in rx.finditer(sl[j]) if not m.group(1).startswith(REFUSED)}
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if not f.endswith('.v'):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, out)
            sp = os.path.join(stage, rel)
            if not his or not os.path.exists(sp):
                continue
            sl, ol = open(sp).read().split('\n'), open(p).read().split('\n')
            for j, (s, o) in enumerate(zip(sl, ol)):
                so, no = list(TOKREF.finditer(s)), list(TOKREF.finditer(o))
                if len(so) != len(no):
                    continue
                for x, y in zip(so, no):
                    if x.group(0).startswith(REFUSED) or ival(x.group(0)) not in his:
                        continue
                    tok = y.group(0)
                    hi = None if tok.startswith(REFUSED) else ival(tok)
                    if best is None:
                        X.chk.append((rel, j + 1, x.group(0), tok, 'czone-bound (no constant shadow cells found to '
                                                                     'check against)'))
                    elif hi is None or hi < best:
                        row = (rel, j + 1, tok, hex(best), f'FAIL czone-bound (the CZONE shadow bound {tok} is below '
                               f'the end {best:#x} of the unit\'s own highest constant shadow cell, {src})')
                        X.rev.append(row); X.chk.append(row); nfail += 1
                        X.required_extra.append((rel, f'CZONE shadow bound at line {j + 1}: >= {best:#x} (the end of '
                                                      f'the unit\'s highest constant shadow cell, {src})'))
                    else:
                        X.chk.append((rel, j + 1, x.group(0), tok, f'czone-bound ok ({tok} >= {best:#x}, {src})'))
    return nfail, best, src


def comment_runs(t):
    """per line of t: the [start, end) runs of characters inside Coq comments (nested `(* ... *)`, delimiters
    included)."""
    runs, depth, i, line, ls = [[]], 0, 0, 0, 0
    cur = None
    while i < len(t):
        if t[i] == '\n':
            if cur is not None:
                runs[line].append((cur, i - ls)); cur = 0 if depth else None
            runs.append([]); line += 1; i += 1; ls = i
            if depth:
                cur = 0
            continue
        if t.startswith('(*', i):
            if not depth:
                cur = i - ls
            depth += 1; i += 2; continue
        if t.startswith('*)', i) and depth:
            depth -= 1; i += 2
            if not depth:
                runs[line].append((cur, i - ls)); cur = None
            continue
        i += 1
    if cur is not None:
        runs[line].append((cur, len(t) - ls))
    return runs


def restore_comments(stage, out, X, rels):
    """COMMENTS are never edited: every comment of a staged file is written back from the donor text after
    the tool's own passes (a pass that read a numeral inside a comment moved it: preset AGif0:48). A line whose
    comments cannot be paired one to one is a FAIL row (comment-edited). The provenance header added at the end is
    the only comment the tool writes. Returns the number of FAIL rows."""
    nfail = 0
    for rel in rels:
        p, sp = os.path.join(out, rel), os.path.join(stage, rel)
        if not os.path.exists(p) or not os.path.exists(sp):
            continue
        st, ot = open(sp).read(), open(p).read()
        if '(*' not in st and '(*' not in ot:
            continue
        sl, ol = st.split('\n'), ot.split('\n')
        if len(sl) != len(ol):
            continue
        sr, orr = comment_runs(st), comment_runs(ot)
        changed = False
        for i, (s, o) in enumerate(zip(sl, ol)):
            a, b = sr[i], orr[i]
            ca, cb = [s[x:y] for x, y in a], [o[x:y] for x, y in b]
            if ca == cb:
                continue
            if len(a) != len(b):
                row = (rel, i + 1, '-', '-', 'FAIL comment-edited (the tool changed the comments of this line and they '
                                             'cannot be paired with the donor\'s)')
                X.rev.append(row); X.chk.append(row); nfail += 1
                continue
            for (x, y), txt in sorted(zip(b, ca), reverse=True):
                o = o[:x] + txt + o[y:]
            ol[i] = o; changed = True
            X.chk.append((rel, i + 1, '-', '-', 'comment restored (a pass had edited a numeral inside a comment)'))
        if changed:
            open(p, 'w').write('\n'.join(ol))
    return nfail


def label_gate(stage, out, X):
    """LABEL positions are never moved (the keep-labels ruling): a numeral in an mcheck / spin / ISpin / FCheck /
    stag label position whose written value differs from the donor's is a FAIL row (an --override row there is the
    porter's and passes). Returns the number of FAIL rows."""
    n = 0
    for rel in sorted(X.remapped):
        p, sp = os.path.join(out, rel), os.path.join(stage, rel)
        if rel in X.generated or not os.path.exists(sp) or not os.path.exists(p):
            continue
        sl, ol = open(sp).read().split('\n'), open(p).read().split('\n')
        for i, (s, o) in enumerate(zip(sl, ol), 1):
            ls = label_starts(s)
            if not ls:
                continue
            so, no = list(TOKREF.finditer(s)), list(TOKREF.finditer(o))
            if len(so) != len(no):
                continue
            for k, m in enumerate(so):
                if m.start() in ls and no[k].group(0) != m.group(0) and \
                        X.explained.get((rel, i, ival(m.group(0)))) != 'override':
                    row = (rel, i, m.group(0), no[k].group(0), f'FAIL label-moved (argument of {ls[m.start()]}: an '
                                                               f'opaque label keeps the donor\'s value)')
                    X.rev.append(row); X.chk.append(row); n += 1
    return n


def partner_gate(stage, out, X):
    """the (lo, hi) PARTNER rule: a hex interval `LO <= a < HI`, or a pair `(LO, HI)` of two addresses (HI > LO), is ONE
    object: when one bound moved and the other was left at the donor's value with no rule deciding it, the pair is
    half-relocated (fmb2 ReusableB/YE23.v:37: start 0x8000c55c -> 0x8000bcb4, end left at 0x8000c574): a FAIL row.
    The bounds are decided by their own roles in the pass (an interval end in the image's shadow by the granule of
    its bound); this gate catches what no rule decided. Returns the number of FAIL rows."""
    stay = {(r[0], r[1], r[2]) for r in X.chk if len(r) > 4 and r[2] == r[3] and not str(r[4]).startswith('FAIL')}
    hx = r"(?:0x[0-9a-fA-F]+|" + REFUSED + r"[0-9a-f]+)"
    pair_rx = [re.compile(r"(?P<lo>0x[0-9a-fA-F]+)\s*<=\s*[\w']+\s*<\s*(?P<hi>" + hx + ")"),
               re.compile(r'\(\s*(?P<lo>0x[0-9a-fA-F]+)\s*,\s*(?P<hi>0x[0-9a-fA-F]+)\s*\)'),
               re.compile(r"(?P<lo>0x[0-9a-fA-F]+)\s*<=\s*(?P<v>[\w']+)\s*/\\\s*(?P=v)\s*\+\s*[\w']+\s*<=\s*(?P<hi>" + hx +
                          ")")]
    n = 0
    for rel in sorted(X.remapped):
        p, sp = os.path.join(out, rel), os.path.join(stage, rel)
        if rel in X.generated or not os.path.exists(sp) or not os.path.exists(p):
            continue
        sl, ol = strip_comments(open(sp).read()).split('\n'), strip_comments(open(p).read()).split('\n')
        for i, (s, o) in enumerate(zip(sl, ol), 1):
            so, no = list(TOKREF.finditer(s)), list(TOKREF.finditer(o))
            if len(so) != len(no) or '0x' not in s:
                continue
            idx = {m.start(): k for k, m in enumerate(so)}
            for rx in pair_rx:
                for m in rx.finditer(s):
                    a, b = idx.get(m.start('lo')), idx.get(m.start('hi'))
                    if a is None or b is None:
                        continue
                    lo0, hi0 = ival(so[a].group(0)), ival(so[b].group(0))
                    if hi0 <= lo0 or lo0 < 0x10000:
                        continue
                    t1, t2 = no[a].group(0), no[b].group(0)
                    if t1.startswith(REFUSED) or t2.startswith(REFUSED):
                        continue
                    lo1, hi1 = ival(t1), ival(t2)
                    moved = (lo1 != lo0, hi1 != hi0)
                    if moved[0] == moved[1]:
                        continue
                    left = hi0 if moved[0] else lo0
                    if (rel, i, hex(left)) in stay or X.explained.get((rel, i, left)):
                        continue
                    row = (rel, i, hex(left), hex(left), f'FAIL partner-left ([{lo0:#x}, {hi0:#x}) -> [{lo1:#x}, '
                           f'{hi1:#x}): the {"start" if moved[0] else "end"} moved, the '
                           f'{"end" if moved[0] else "start"} was left at the donor\'s value by no rule)')
                    X.rev.append(row); X.chk.append(row); n += 1
    return n


def globals_rows(X, staged_rel):
    """the registered globals are UNIT-SHAPED: a target whose asan_globals descriptor count (64 bytes each) differs
    from the donor's (cgif 3, grant 13, fm 16) gets one required.tsv row for each staged AE37 / AE3i (YE37 / YE3i):
    their descriptor lists, redzone windows and chunk holes come from the target's own asan_globals (--patch). With
    the same count, a different number of READ-ONLY globals (descriptor address in a non-writable section) still
    gets a row for AE3i / YE3i, whose img_ro_chunks holes are those globals' redzones (a8 scene)."""
    def count(elf, geo):
        s = geo.sec.get('asan_globals')
        if not s:
            return None, None
        n, ro = (s[1] - s[0]) // 64, 0
        for i in range(n):
            g = elf.q(s[0] + 64 * i)
            sec = elf.sec(g) if g else None
            ro += bool(sec and not sec[2] & 1)
        return n, ro
    (on, oro), (nn, nro) = count(X.old, X.OG), count(X.new, X.NG)
    if on is None or nn is None:
        return
    for rel in staged_rel:
        b = os.path.basename(rel)
        if on != nn and b in ('AE37.v', 'YE37.v', 'AE3i.v', 'YE3i.v'):
            X.required_extra.append((rel, f'unit-shaped: the target registers {nn} globals ({nro} read-only), the '
                                          f'donor {on} ({oro}): --patch from the target\'s asan_globals (descriptors, '
                                          f'redzone windows, chunk holes)'))
        elif oro != nro and b in ('AE3i.v', 'YE3i.v'):
            X.required_extra.append((rel, f'unit-shaped: the target has {nro} read-only registered globals, the '
                                          f'donor {oro}: img_ro_chunks\' holes are their redzones; --patch from the '
                                          f'target\'s asan_globals'))


def drop_cgif_listings(a, stage, out, staged, remapped, R, old, OG):
    """an object LISTING (`<lib>_listing : ptable` of `PW <word>` instruction words: cgif's own library code, e.g.
    YI0x..YI10) is located by its own words: its longest run of consecutive PW words, as little-endian bytes, searched
    in the .text of the donor, of the donor's other image and of the target (the donor's recovered symbols name no cgif
    program function, and a listing's first words are a common prologue: four listings share their first 16). Found
    once in the donor inside --old-prog, or in the donor's other image, and NOT in the target: the donor program's
    code with no twin, so it is NOT staged (removed from stage/ and stage-out/), one required.tsv row each; the unit
    states its own listing. Returns [(file, why)]."""
    def text_of(path):
        g = Geo(path)
        if '.text' not in g.sec:
            return 0, b''
        lo, hi = g.sec['.text']
        return lo, Elf(path).read(lo, hi - lo) or b''
    if not a.old_prog or '.text' not in OG.sec:
        return []
    prog = [tuple(int(x, 16) for x in r.split(':')) for r in a.old_prog]
    tlo, text = OG.sec['.text'][0], old.read(OG.sec['.text'][0], OG.sec['.text'][1] - OG.sec['.text'][0]) or b''
    twin = text_of(a.twin_image)[1] if getattr(a, 'twin_image', None) else b''
    target = text_of(a.target_elf)[1]
    out_rows = []
    for f in list(staged):
        rel = os.path.relpath(f, stage)
        t = open(f).read()
        i = t.find('_listing')
        if i < 0 or not re.search(r'_listing\s*:\s*ptable\b', t) or not re.search(r'\bPW\s+0x', t):
            continue
        best, cur = [], []
        for it in re.findall(r'(PW\s+0x[0-9a-fA-F]+|P[A-Za-z]+[^;]*);', t[i:]):
            if it.startswith('PW'):
                cur.append(int(it.split()[1], 16))
                continue
            best, cur = (cur, []) if len(cur) > len(best) else (best, [])
        best = cur if len(cur) > len(best) else best
        if len(best) < 32:
            continue  # too short a run to place it
        pat = b''.join(struct.pack('<I', w & 0xffffffff) for w in best)
        if target.find(pat) >= 0:
            continue  # the target holds the same code: the listing has a twin
        k = text.find(pat)
        where = None
        if k >= 0 and text.find(pat, k + 1) < 0 and any(p <= tlo + k < q for p, q in prog):
            where = f'at {tlo + k:#x} in the donor, inside --old-prog'
        elif k < 0 and twin and twin.find(pat) >= 0:
            where = "in the donor's other image"
        if where:
            why = (f'cgif program listing (a run of {len(best)} of its words is {where}; the target holds no such code): '
                   f'not staged; the unit states its own listing')
            for d in (stage, out):
                if os.path.exists(os.path.join(d, rel)):
                    os.remove(os.path.join(d, rel))
            staged.remove(f)
            remapped.discard(rel)
            out_rows.append((rel, why))
    return out_rows


def old_syms_for(a):
    """the source's recovered symbols for --old-elf ITSELF: the given --old-syms, else the file of the image's own
    sha256 (OLD_SYMS_TXT, else <--syms-cache>/<sha16>.<SYMS_DONORS>.v4.json, else another donor set's cache of the
    image). A file that belongs to another image is refused (a scene asan-ubsan run with the asan donor's
    names got MISMATCH 946): a cache named for another image hash, a known text of another image, or names whose
    starts miss the image's own FDE starts."""
    sha = hashlib.sha256(open(a.old_elf, 'rb').read()).hexdigest()[:16]
    p = a.old_syms
    if p is None:
        p = OLD_SYMS_TXT.get(sha)
        if p is None and SYMS_CACHE and os.path.isdir(SYMS_CACHE):
            cands = sorted(f for f in os.listdir(SYMS_CACHE) if f.startswith(sha + '.') and f.endswith('.v4.json'))
            pick = [f for f in cands if f == f'{sha}.{SYMS_DONORS}.v4.json'] or cands
            p = os.path.join(SYMS_CACHE, pick[0]) if pick else None
        if p is None:
            print(f'port_core: no recovered symbols known for --old-elf (sha256 {sha}...): running without --old-syms',
                  file=sys.stderr)
            return None
    base = os.path.basename(p)
    m = re.match(r'([0-9a-f]{16})\.[0-9a-f]{16}\.v\d+\.json$', base)
    other = {s for s, t in OLD_SYMS_TXT.items() if os.path.abspath(t) == os.path.abspath(p)}
    if (m and m.group(1) != sha) or (other and sha not in other):
        sys.exit(f'port_core: --old-syms {p} belongs to another image ({(m.group(1) if m else sorted(other)[0])}...), '
                 f'not to --old-elf {a.old_elf} ({sha}...): give the symbols of the --old-elf image (asan-ubsan: '
                 f'{SYMS_CACHE}/1c29845fe6058de6.{SYMS_DONORS}.v4.json)')
    from resolve_code import fde_ranges, old_syms_list
    fl = sorted(fde_ranges(a.old_elf))
    starts = {lo for lo, _ in fl}
    los = [lo for lo, _ in fl]
    inside = hit = 0
    for lo, n, _ in old_syms_list(p):
        k = bisect.bisect_right(los, lo) - 1
        if n > 0 and k >= 0 and lo < fl[k][1]:
            inside += 1
            hit += lo in starts
    if inside >= 50 and hit < inside // 2:
        sys.exit(f'port_core: --old-syms {p} does not fit --old-elf {a.old_elf}: only {hit} of {inside} of its names '
                 f'inside the image\'s FDE ranges start a function there (another image\'s symbols)')
    return p


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--src-lib', default='proofs/cgif/cgif_file_fuzzer/lib')
    p.add_argument('--src-mod', default='OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib')
    p.add_argument('--src-images', default='OssFuzzTheorems.cgif.cgif_file_fuzzer.images')
    p.add_argument('--old-elf', required=True, help='cgif_file_fuzzer.asan (sha256 7093581a...)')
    p.add_argument('--old-prog', action='append', default=[], help='LO:HI hex, OLD program code with no counterpart')
    p.add_argument('--old-syms', default=None, help="the source image's recovered symbols (`name addr size` lines, or "
                   "port_addr_check.py's recovery cache `<image sha16>.<donors>.v4.json`). Default: the one of "
                   "--old-elf's OWN sha256 (cgif asan: cgif_file_fuzzer.asan.recovered-syms.txt; asan-ubsan: "
                   "the gate's recovery cache file 1c29845fe6058de6.978e0a064c5a4c6e.v4.json). A file of another image is refused. "
                   "Pairs FDE-less code, breaks ties between identical functions, names data objects")
    p.add_argument('--target-lib', required=True, help='proofs/<p>/<h>/lib of the target')
    p.add_argument('--target-mod', required=True, help='e.g. OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib')
    p.add_argument('--target-images', required=True, help='e.g. OssFuzzTheorems.libreac.fuzz_grant.images')
    p.add_argument('--target-name', required=True, help='e.g. libreac/fuzz_grant (header text)')
    p.add_argument('--target-elf', required=True)
    p.add_argument('--target-syms', default=None, help="the target ELF's unstripped twin or nm text (function names, for pairing by function); default: its FDEs")
    p.add_argument('--files', required=True, help='file with one cgif lib-relative path per line (A/X.v, X.v)')
    p.add_argument('--work', default=None)
    p.add_argument('--apply', action='store_true', help='copy the result into --target-lib (only when every gate passes)')
    p.add_argument('--rename', action='append', default=[], help='OLD=NEW identifier rename (whole words), e.g. TfibB=GrantB')
    p.add_argument('--reusable-dir', default='Reusable', help='where the non-A files go under --target-lib (module suffix too)')
    p.add_argument('--override', action='append', default=[], help='per-unit table of hand values: file<TAB>line<TAB>old<TAB>new, applied after the relocation pass')
    p.add_argument('--patch', action='append', default=[], help='per-unit STRUCTURAL fix: a unified diff against stage-out '
                   '(paths A/X.v, Reusable/X.v; write it with `diff -u` from a run\'s stage-out), applied with zero fuzz '
                   'after the overrides and BEFORE every check; a hunk that does not apply fails the run')
    p.add_argument('--remap-all', action='store_true', help='move addresses in every staged file, not only A/')
    p.add_argument('--remap-images', action='store_true', help="also move addresses in a staged non-A file that imports the source images module (cgif_file's asan-ubsan side is its root Y* files)")
    p.add_argument('--known-image-end', action='append', default=[], help='HEX[=WHO]: another image end that must not survive (FAIL rows)')
    p.add_argument('--known-elf', action='append', default=[], help='ELF: another unit\'s image; its image end must not survive (FAIL rows)')
    p.add_argument('--decimal-skip', default=None, help='file list: leave these files out of decimals.tsv (e.g. a start-up slot another run regenerates)')
    p.add_argument('--gate-script', default=None, help='port_addr_check.py (the symbol gate); required unless --no-gate')
    p.add_argument('--gate-donors', default=None, help="port_addr_check.py --donors-from (symbolised images it recovers the source's names from); required unless --no-gate")
    p.add_argument('--gate-cache', default=None, help="dir of the symbol gate's recoveries of stripped images (<image sha16>.<donors "
                   'sha16>.v*.json): copied into the private gate cache of --work; default: none (the gate recovers them)')
    p.add_argument('--cell-gates', default=None, help='dir of shadowcheck.py and ownedcheck.py (the cell gates); default: skipped')
    p.add_argument('--cellcheck', default=None, help='cellcheck.py (a cell gate); default: skipped')
    p.add_argument('--decode-check', default=None, help='decode_check.py, the independent decoder (a gate); default: skipped')
    p.add_argument('--syms-cache', default=None, help="dir of port_addr_check's recovery caches (<image sha16>.<donors sha16>.v4.json), "
                   'read only when --old-syms is not given')
    p.add_argument('--no-gate', action='store_true', help='skip the symbol gate (development only: --apply refuses without it)')
    p.add_argument('--prepush', action='store_true', help='the pre-push run (after the unit put its generated slots '
                   'and overrides in): the cell gates shadowcheck / ownedcheck / cellcheck must pass, or the run fails')
    p.add_argument('--zero-class', action='append', type=int, default=[], help="a stack class the emitted AF0l map "
                   'gives 0 (its contract is carried outside the record as a named hypothesis; scene: 8). Give it on '
                   'both images')
    p.add_argument('--with-walks', action='store_true', help='also stage walk-files.txt beside this script (the closure '
                   'of the class-keyed side-stack walks and the exitN/oblF tactic files): any unit that ports program '
                   'walks or the asan-ubsan side')
    p.add_argument('--no-stage', action='append', default=None, help="a source file never staged (default: YI0a.v and "
                   "YI17.v, cgif's ff_lib_shape instance; the unit's A/AD1q.v needs its own shape file)")
    p.add_argument('--name-clash', action='append', default=None, help='LEFT,RIGHT under --target-lib: names both '
                   'declare differently; a staged file that Requires LEFT and uses one fails (default: Lib,Reusable/YK11.v)')
    p.add_argument('--forbid', action='append', default=None, help='a Reusable module no staged A/ file may load '
                   '(default YI5b, YI5c: the plain build\'s #[global] sink instances)')
    p.add_argument('--kit', action='append', default=None, help="a composition-kit module the unit's trunk lib holds "
                   '(default YK18 YK0j YK0t YK1e YK1g YM08 YM09 YQ00..YQ06): staged instead of kept = FAIL')
    p.add_argument('--kernel-dir', default=None, help='with a per-image --reusable-dir: the shared dir (e.g. Reusable) '
                   'for every non-A file that is not per-image (see kernel_split); the per-image files go to '
                   '--reusable-dir and the ones holding image values are relocated (image-specific.txt says why)')
    p.add_argument('--kernel-image', action='append', default=[], help="the unit's OTHER source image (e.g. "
                   'cgif_file_fuzzer.asan-ubsan in the asan run): its image values also make a file per-image, so both '
                   'runs split the files the same way')
    p.add_argument('--twin-image', default=None, help="the donor's OTHER image (the image its Y / A twin files state): "
                   'KEPT-TWIN-EQUAL keeps a numeral both twins state identically where the two images differ. Default: '
                   'the first --kernel-image, else none (give the cgif image of the other build)')
    p.add_argument('--as-twin', action='store_true', help="a NON-cgif donor whose A/ files are a unit's own image-A "
                   'text (grant A -> grant B): stage each A/A<x>.v as <reusable-dir>/Y<x>.v (module lib.A.A<x> -> '
                   'lib.<reusable-dir>.Y<x>, its A/ Requires pointed at the Y twins), relocated onto --target-elf')
    p.add_argument('--generated', action='append', default=None, help='a per-image GENERATED source file: staged as a '
                   'slot (module paths renamed, numerals untouched), never relocated, listed in required.tsv as '
                   '"regenerate from the start-up collector". Given, it REPLACES the default list (A/AB01 AB03 AB05 '
                   'AB12 AB1m AD2i AD2j AD1k AB1v AB1h AB1k ACej, YD2j); each A/ entry brings its root Y twin')
    a = p.parse_args()
    global CELL_GATES, CELLCHECK, DECODE_CHECK, SYMS_CACHE
    CELL_GATES, CELLCHECK, DECODE_CHECK, SYMS_CACHE = a.cell_gates, a.cellcheck, a.decode_check, a.syms_cache
    if not a.no_gate and not (a.gate_script and a.gate_donors):
        sys.exit('port_core: give --gate-script and --gate-donors (the symbol gate), or --no-gate')
    adir = os.path.join(a.src_lib, 'A')
    if not os.path.isdir(adir) or not any(f.endswith('.v') for f in os.listdir(adir)):
        sys.exit(f'port_core: --src-lib {a.src_lib} has no A/*.v files ({adir} is missing or empty). Point it at the '
                 f'donor\'s released lib directory (proofs/cgif/cgif_file_fuzzer/lib: A/ with the ASan files and the '
                 f'Reusable Y*.v beside it); a sparse worktree must check out that whole directory.')

    def _entry_in(path):
        m = re.search(r'Definition\s+tfib_entry\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+)', open(path).read()) \
            if os.path.exists(path) else None
        return int(m.group(1), 16) if m else None

    def _e_entry(elf):
        return struct.unpack_from('<Q', open(elf, 'rb').read(0x20), 0x18)[0] if os.path.exists(elf) else None
    _ee = _e_entry(a.old_elf)
    _lst = [l.strip() for l in open(a.files) if l.strip() and not l.startswith('#')] if os.path.exists(a.files) else []
    for _side, _rel in (('A/', 'A/AB1w.v'), ('Y', 'YB1w.v')):
        _ent = _entry_in(os.path.join(a.src_lib, _rel))
        _uses = any(x.startswith('A/') for x in _lst) if _side == 'A/' else \
            (a.remap_images and any(y_twin(os.path.basename(x), a.src_lib) for x in _lst))
        if _uses and _ent is not None and _ee is not None and _ent != _ee:
            sys.exit(f'port_core: the {_side} files belong to another donor image: {_rel} states tfib_entry {_ent:#x}, '
                     f'--old-elf {a.old_elf} has e_entry {_ee:#x}. An asan-ubsan pass stages the root Y twins only '
                     f'(a --files list with no A/ entries; --with-walks re-adds walk-files.txt\'s A/ entries: fold the '
                     f'walk files\' Y twins into --files instead); an asan pass stages the A/ side against the .asan donor.')
    a.old_syms = old_syms_for(a)
    if a.twin_image is None:
        a.twin_image = a.kernel_image[0] if a.kernel_image else None
    if a.twin_image and not os.path.exists(a.twin_image):
        sys.exit(f'port_core: --twin-image {a.twin_image} does not exist')
    a.work = a.work or os.path.abspath('work-' + a.target_name.replace('/', '-'))
    os.makedirs(a.work, exist_ok=True)
    here = os.path.dirname(os.path.abspath(__file__))
    vers = [(n, hashlib.sha256(open(p, 'rb').read()).hexdigest()) for n, p in
            (('port_core.py', os.path.join(here, 'port_core.py')), ('resolve_code.py', os.path.join(here, 'resolve_code.py')),
             ('gen_traces.py', os.path.join(here, 'gen_traces.py')), ('symbol gate', a.gate_script)) if p and os.path.exists(p)]
    open(os.path.join(a.work, 'versions.txt'), 'w').write(''.join(f'{n}\t{h}\n' for n, h in vers))
    print('port_core: versions: ' + ', '.join(f'{n} {h[:12]}' for n, h in vers), file=sys.stderr)
    mapf = os.path.join(a.work, 'map.json')
    if not os.path.exists(mapf):
        run([sys.executable, os.path.join(KIT, 'elf_symbols.py'), a.old_elf, a.target_elf, '-o', mapf,
             '--summary', os.path.join(a.work, 'map.txt')])
    files = [l.strip() for l in open(a.files) if l.strip() and not l.startswith('#')]
    global DONOR_DESC
    DONOR_DIRS.update(d for d in ('Reusable', 'ReusableB') if os.path.isdir(os.path.join(a.src_lib, d)))
    if a.as_twin:
        AS_TWIN.update(os.path.basename(f)[:-2] for f in files if f.startswith('A/A'))
        AS_TWIN.update(f[:-2] for f in os.listdir(os.path.join(a.src_lib, 'A')) if f.startswith('A') and f.endswith('.v'))
    mrel = re.search(r'proofs/.*', os.path.abspath(a.src_lib))
    DONOR_DESC = (mrel.group(0) if mrel else os.path.abspath(a.src_lib),
                  hashlib.sha256(open(a.old_elf, 'rb').read()).hexdigest()[:12])
    if a.with_walks:
        files += [w for w in (l.strip() for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                                     'walk-files.txt')))
                  if w and not w.startswith('#') and w not in files]
    a.no_stage = a.no_stage if a.no_stage is not None else ['YI0a.v', 'YI17.v']
    a.name_clash = a.name_clash if a.name_clash is not None else ['Lib,Reusable/YK11.v']
    a.kit = set(a.kit if a.kit is not None else
                ['YK18', 'YK0j', 'YK0t', 'YK1e', 'YK1g', 'YM08', 'YM09'] + [f'YQ0{i}' for i in range(7)])
    a.generated = a.generated if a.generated is not None else [
        'A/AB01.v', 'A/AB03.v', 'A/AB05.v', 'A/AB12.v', 'A/AB1m.v', 'A/AD2i.v', 'A/AD2j.v', 'A/AD1k.v', 'A/AB1v.v',
        'A/AB1h.v', 'A/AB1k.v', 'A/ACej.v', 'YD2j.v']
    a.generated += [f'Y{g[3:]}' for g in a.generated if g.startswith('A/A') and f'Y{g[3:]}' not in a.generated]
    skipped = [f for f in files if f in a.no_stage]
    a.img_values = set()
    if a.kernel_dir:
        img_specific = kernel_split(a, files)
        for f in files:
            if not f.startswith('A/'):
                DIRMAP[f] = a.reusable_dir if f in img_specific else a.kernel_dir
                DIRMAP[f.split('/', 1)[1] if f.split('/', 1)[0] in DONOR_DIRS else f] = DIRMAP[f]
        a.img_values = {dst_path(f, a.reusable_dir) for f, w in img_specific.items() if w.startswith('line ')}
        open(os.path.join(a.work, 'image-specific.txt'), 'w').write(
            ''.join(f'{f}\t{w}\n' for f, w in sorted(img_specific.items())))
    files = [f for f in files if f not in a.no_stage]
    stage = os.path.join(a.work, 'stage'); out = os.path.join(a.work, 'stage-out')
    for d in (stage, out):
        shutil.rmtree(d, ignore_errors=True); os.makedirs(d)
    for f in ('auipc.tsv',):  # tables of earlier versions
        if os.path.exists(os.path.join(a.work, f)):
            os.remove(os.path.join(a.work, f))
    kept, renamed, as_twin_src = [], {}, {}
    for rel in files:
        d = dst_path(rel, a.reusable_dir)
        if rel.startswith('A/') and d != rel:
            as_twin_src[d] = rel  # --as-twin: the unit's image-A file A/A<x>.v staged as its Y twin
        if not rel.startswith('A/') and os.path.exists(os.path.join(a.target_lib, d)):
            kept.append(rel); continue
        t = open(os.path.join(a.src_lib, rel)).read()
        os.makedirs(os.path.dirname(os.path.join(stage, d)), exist_ok=True)
        rt = rename_text(t, a)
        a2 = argparse.Namespace(**{**vars(a), 'rename': []})
        if rt != rename_text(t, a2):
            renamed[d] = [r.replace('=', ' -> ') for r in a.rename if re.search(r'\b' + re.escape(r.split('=')[0]) + r'\b', t)]
        open(os.path.join(stage, d), 'w').write(rt)
    open(os.path.join(a.work, 'kept.txt'), 'w').write('\n'.join(kept) + '\n')
    # the composition kit is the unit's trunk text: a kit file the target lib lacks would be staged from the donor
    # (which does not build against the kit) and later overwrite the trunk's copy: --target-lib is not the trunk lib
    kit_staged = [f for f in files if os.path.basename(f)[:-2] in a.kit and f not in kept]
    staged = []
    for root, _, fs in os.walk(stage):
        staged += [os.path.join(root, f) for f in fs if f.endswith('.v')]
    rw = os.path.join(a.work, 'remap-out')
    shutil.rmtree(rw, ignore_errors=True)
    img = [f for f in staged
           if not (os.path.relpath(f, stage) in [dst_path(g, a.reusable_dir) for g in a.generated + FROZEN])
           and (a.remap_all or os.path.relpath(f, stage).startswith('A/') or os.path.relpath(f, stage) in as_twin_src
                or os.path.relpath(f, stage) in a.img_values  # --kernel-dir: a per-image file holding image values
                or (a.remap_images and (a.target_images in open(f).read()  # staging already renamed the images module
                                        or y_twin(os.path.basename(f), a.src_lib))))]
    remapped = {os.path.relpath(f, stage) for f in img}
    run([sys.executable, os.path.join(KIT, 'numeral_map.py'), '--map', mapf, '--old-elf', a.old_elf, '--new-elf', a.target_elf,
         '--report', os.path.join(a.work, 'remap.tsv'), '--rewrite', rw, '--root', stage] + sorted(img),
        stdout=open(os.path.join(a.work, 'remap.log'), 'w'), stderr=subprocess.STDOUT)
    for f in staged:
        rel = os.path.relpath(f, stage)
        src = os.path.join(rw, rel) if os.path.exists(os.path.join(rw, rel)) else f
        os.makedirs(os.path.dirname(os.path.join(out, rel)), exist_ok=True)
        shutil.copy(src, os.path.join(out, rel))
    diff = differing_kept(a, stage, kept)
    old, new = Elf(a.old_elf), Elf(a.target_elf)
    from resolve_code import Resolver
    from elf_symbols import Lookup
    R = Resolver(a.old_elf, a.target_elf, a.target_syms, mapf, a.old_syms)
    OG, NG = Geo(a.old_elf), Geo(a.target_elf)
    dropped_listings = drop_cgif_listings(a, stage, out, staged, remapped, R, Elf(a.old_elf), OG)
    look = Lookup(json.load(open(mapf))['runs'])
    known = []
    for k in a.known_image_end:
        v, _, who = k.partition('=')
        known.append((int(v, 16), who or 'known image end'))
    for e in a.known_elf:
        known.append((Geo(e).hull[1], f'image end of {os.path.basename(e)}'))
    X = Reloc(a, old, new, R, look, OG, NG)
    X.generated = {dst_path(g, a.reusable_dir) for g in a.generated} & {os.path.relpath(f, stage) for f in staged}
    globals_rows(X, [os.path.relpath(f, stage) for f in staged])
    X.run(stage, out, remapped)
    X.regen_decode(out)
    nhash = hash_roles(stage, out, X)
    nderiv = derived_names(stage, out, X)
    nwin = shadow_windows(a, out, X, new)
    ncls, called, nkeyed = emit_class_map(out, X, R, a.zero_class)
    nft, ndrop, nadd = emit_function_table(out, X, R, X.prog)
    nstartup = startup_ranges(stage, out, X, R)
    ndel, del_names = delete_unpaired(out, X)
    yimg = None
    donor_top = [f for f in staged if os.path.basename(f) == 'YImgTop.v']  # a non-cgif donor's own image bounds
    if X.imgtop_users or donor_top:
        # the unit's own image bounds, one file: generated from the target's PT_LOADs unless the target has it
        yrel = os.path.join(a.reusable_dir, 'YImgTop.v')
        imod = a.target_mod + '.' + a.reusable_dir.replace('/', '.')
        if not os.path.exists(os.path.join(a.target_lib, yrel)):
            yimg = yrel
            body = ('(* Generated by port_core.py: the image of this unit\'s build, for the shared files that bound the '
                    f'image (its last PT_LOAD ends at {NG.loads[-1][2]:#x}). One place per unit and image. *)\n'
                    'From Stdlib Require Import ZArith.\n\n'
                    f'Notation IMG_LO := {NG.hull[0]:#x}%Z (only parsing).\n'
                    f'Notation IMG_TOP := {NG.hull[1]:#x}%Z (only parsing).\n')
            for d in (stage, out):
                os.makedirs(os.path.join(d, a.reusable_dir), exist_ok=True)
                open(os.path.join(d, yrel), 'w').write(body)
            if os.path.join(stage, yrel) not in staged:
                staged.append(os.path.join(stage, yrel))
        for rel in sorted(X.imgtop_users):
            # appended to the last `From ... Require` line, so every line keeps the donor's number (overrides,
            # the gate and other units' line references stay valid)
            p = os.path.join(out, rel)
            t = open(p).read().split('\n')
            k = max([i for i, l in enumerate(t) if l.startswith('From ') and 'Require' in l] or [0])
            t[k] = t[k].rstrip() + f' From {imod} Require Import YImgTop.'
            open(p, 'w').write('\n'.join(t))
    fails = collections.Counter()  # FAIL rows of the gates added in this release, by gate
    # the tool's own last passes, on stage/ vs stage-out/ by line BEFORE any --patch can insert lines (pcap AFg1.v: a
    # patch hunk that inserts a line shifted quotients() onto another line's partner, 85491 for 83288)
    nquot, nqfail = quotients(stage, out, X)
    fails['comment-edited'] = restore_comments(stage, out, X, [os.path.relpath(f, stage) for f in staged])
    nov, covered, fails['override-ambiguous'] = apply_overrides(a, stage, out, X)
    npatch, patch_fail, gstage = apply_patches(a, stage, out, X)
    nfail = image_end_scan(a, out, X, OG, NG, known)
    nkn = kept_names(a, out, diff, X)
    nsplit, nsfail = split_ranges(gstage, out, X, R)
    nrange = range_gate(a, out, X, R) + nsfail
    nclash = name_clash(a, out, X)
    a.forbid = a.forbid if a.forbid is not None else ['YI5b', 'YI5c']
    nforbid = forbidden_closure(a, out, X)
    nkimg = kept_image_check(a, kept, X, OG, NG, known)
    for f in kit_staged:
        row = (dst_path(f, a.reusable_dir), 0, '-', '-', 'FAIL kit-file-staged (the target lib lacks this kit file, so the '
               'donor copy was staged; --target-lib must be the unit\'s TRUNK lib, which holds the kit)')
        X.rev.append(row); X.chk.append(row)
    nkit = len(kit_staged)
    nrepl = replace_pairs(out, X) + bound_order(out, X)
    fails['label-moved'] = label_gate(gstage, out, X)
    fails['partner-left'] = partner_gate(gstage, out, X)
    fails['czone-bound'], czone_max, czone_src = czone_gate(a, out, X)
    fails['rename'] = rename_gate(a, out, kept, X)
    nrelfix, fails['relation'] = relations(out, X)
    fails['row-address'] = pair_rows_gate(a, gstage, out, X)
    fails['decode-check'], decode_summary = decode_gate(out, X)
    nmerged = merged_spans(a, out, X, R)
    nrowsym = row_symbols(out, X, R, new)
    ndsym = data_symbol_gate(gstage, out, X)
    ntwin = twin_forms(gstage, out, X)
    nrepl += nqfail + nrowsym + ndsym + ntwin + nkeyed
    nmark = 0  # no staged file may keep a refusal marker: each needs an --override row (required.tsv)
    for root, _, fs in os.walk(out):
        for f in sorted(fs):
            if f.endswith('.v'):
                p = os.path.join(root, f)
                k = open(p).read().count(REFUSED)
                if k:
                    row = (os.path.relpath(p, out), 0, '-', '-', f'FAIL refused-marker ({k} port_core_refused_* '
                           f'left: give each an --override row, see required.tsv)')
                    X.rev.append(row); X.chk.append(row); nmark += 1
    oldsyms = {}
    if a.old_syms:
        from resolve_code import old_syms_list
        for lo, n, name in old_syms_list(a.old_syms):
            oldsyms[lo] = (name, n)
    nnames = names_report(a, out, stage, X, R, oldsyms)
    per_nona = nona_report(a, files, kept, staged, remapped, OG, R, old, known)
    required = [r for r in X.refusals if r[3] != 'old-program-block' and (r[0], r[1], int(r[2], 16)) not in covered]
    required += [(g, 0, '-', ('regenerate with gen_traces.py' if g.endswith('ACej.v') else
                              'regenerate from the start-up collector') +
                  ' (a per-image generated file: staged as a slot, not relocated)') for g in sorted(X.generated)]
    required += [(r, 0, '-', f'regenerate {d} from the start-up collector (a generated class: its released numerals '
                             f'are kept as a slot)') for r, d in sorted(X.gen_defs)]
    required += [(r, 0, '-', why) for r, why in dropped_listings]
    required += [(r, 0, '-', why) for r, why in X.required_extra]  # rows of the gates added in this release
    with open(os.path.join(a.work, 'required.tsv'), 'w') as fh:
        fh.write('file\tline\told\twhy\t(an --override row for each, or the run refuses to apply)\n')
        for r in required:
            fh.write('\t'.join(map(str, r)) + '\n')
    decs = write_tables(a, X, R, new)
    moved = sum(open(f).read() != open(os.path.join(out, os.path.relpath(f, stage))).read() for f in staged)
    gate, glog = (None, 'skipped (--no-gate)') if a.no_gate else symbol_gate(a, gstage, out, X)
    for f in staged:  # the header goes on after the gate: the gate pairs stage/ and stage-out/ line by line
        rel = os.path.relpath(f, stage)
        t0, t1 = open(f).read(), open(os.path.join(out, rel)).read()
        srcrel = as_twin_src.get(rel) or (rel if rel.startswith('A/') else rel.split('/', 1)[1])
        open(os.path.join(out, rel), 'w').write(header(t1, srcrel, t0 != t1, a.target_name, renamed.get(rel)))
    ref = collections.Counter(r[3] for r in X.refusals)
    dk = collections.Counter(d[0] for d in decs)
    print(f'port_core: staged {len(staged)} files ({len(kept)} kept from the target'
          f'{", not staged: " + " ".join(skipped) if skipped else ""}), {moved} with moved addresses; '
          f'{len(X.chk)} ok, {len(X.fixed)} values written over remap\'s (fixed.tsv), {nov} hand values from '
          f'--override; {len(X.rev)} for review (review.tsv); refused {sum(ref.values())} '
          f'({", ".join(f"{k} {v}" for k, v in ref.most_common())}); decimals in the image (decimals.tsv): '
          f'{", ".join(f"{k} {v}" for k, v in sorted(dk.items()))}; '
          f'{nkn} uses of names missing from kept target files; {nnames} name rows to check (names.tsv); '
          f'{sum(1 for v in diff.values() if v)} target-changed files named by staged files (differs.tsv)',
          file=sys.stderr)
    print(f'port_core: FAIL rows: image-end {nfail}, range {nrange}, name-clash {nclash}, kept-file-other-image '
          f'{nkimg}, forbidden-module {nforbid}, kit-file-staged {nkit}, dropped-name-used {nft}, files with refused '
          f'markers {nmark}; shadow windows recomputed {nwin}; class map {ncls} ('
          + ', '.join(f'{c}={v:#x}' for c, v in sorted(called.items())) + f'); function table: dropped {ndrop} donor '
          f'pairs, added {nadd} target functions; deleted {ndel} refused definitions with every use ('
          + '; '.join(f'{r}: {" ".join(ns)}' for r, ns in sorted(del_names.items())) + ')', file=sys.stderr)
    unrel = {k: v for k, v in per_nona.items() if dst_path(k, a.reusable_dir) not in remapped}
    if unrel:
        print('port_core: non-A files not relocated that state image constants (nonA.tsv): ' +
              ', '.join(f'{k} ({v})' for k, v in sorted(unrel.items())), file=sys.stderr)
    cg = cell_gates(a, out)
    for g, ok, line in cg:
        print(f'port_core: cell gate {g}: {"PASS" if ok else "FAIL"}: {line}', file=sys.stderr)
    print(f'port_core: replace-pair / inverted-bound FAIL rows {nrepl}; patches applied {npatch}, failed {patch_fail}; '
          + ', '.join(f'{k} {v}' for k, v in sorted(fails.items())), file=sys.stderr)
    print(f'port_core: hashes recomputed {nhash}; derived names written {nderiv}; relation results recomputed {nrelfix}; '
          f'cgif listings not staged '
          f'{len(dropped_listings)}{" (" + " ".join(r for r, _ in dropped_listings) + ")" if dropped_listings else ""}; '
          f'CZONE bound check against {czone_max and hex(czone_max)} ({czone_src}); decode check: {decode_summary}',
          file=sys.stderr)
    status = 3 if (nfail or nrange or nclash or nkimg or nforbid or nkit or nft or nmark or nrepl or patch_fail or
                   sum(fails.values()) or (a.prepush and not all(ok for _, ok, _ in cg))) else 0
    if required:
        print(f'port_core: {len(required)} values have no rule and no --override row (required.tsv); files: ' +
              ', '.join(sorted({r[0] for r in required})), file=sys.stderr)
        status = status or 4
    if gate is None:
        print(f'port_core: symbol gate: {glog.strip().splitlines()[-1] if glog.strip() else "failed to run"}',
              file=sys.stderr)
        if not a.no_gate:
            status = status or 3
    else:
        print('port_core: symbol gate (gate.tsv): ' + ', '.join(f'{k} {v}' for k, v in sorted(gate.items())) +
              (' -- PASS' if not gate.get('MISMATCH') else ' -- FAIL'), file=sys.stderr)
        if gate.get('MISMATCH'):
            status = 3
    if a.apply:
        # the A/ side was proved against the unit's asan image: refuse to copy A/ files onto another image's tree
        _unit_a = _entry_in(os.path.join(a.target_lib, 'A', 'AB1w.v'))
        _ta = [os.path.relpath(f, stage) for f in staged if os.path.relpath(f, stage).startswith('A/')]
        if _ta and _unit_a is not None and _e_entry(a.target_elf) not in (None, _unit_a):
            print(f'port_core: NOT applied: {len(_ta)} A/ files (first {_ta[0]}) would go onto {a.target_lib}, whose '
                  f'A/AB1w.v states tfib_entry {_unit_a:#x}, but --target-elf {a.target_elf} has e_entry '
                  f'{_e_entry(a.target_elf):#x}: the A/ side belongs to the unit\'s asan image', file=sys.stderr)
            status = status or 3
        elif a.no_gate or status not in (0, 4) or any(r[0] not in X.generated for r in required):
            print('port_core: NOT applied (a gate failed or was skipped, or a required.tsv row other than a generated '
                  'slot is open)', file=sys.stderr)
        else:
            # a --generated slot is NEVER copied over the unit's own file (relA2: AB01 / AB03 hold the unit's 775168 /
            # 1530, the slots cgif's 775680 / 1531); a slot the target lacks is copied for reference and its
            # required.tsv row stays; the rest of the run applies
            for f in staged:
                rel = os.path.relpath(f, stage)
                dst = os.path.join(a.target_lib, rel)
                if rel in X.generated:
                    if os.path.exists(dst):
                        print(f'port_core: slot {rel} NOT copied: the unit\'s own {dst} stays (regenerate it from the '
                              f'start-up collector)', file=sys.stderr)
                        continue
                    print(f'port_core: slot {rel} copied for reference (the target had none; its required.tsv row '
                          f'stays)', file=sys.stderr)
                elif not rel.startswith('A/') and rel not in as_twin_src and os.path.exists(dst):
                    continue
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                shutil.copy(os.path.join(out, rel), dst)
            print(f'port_core: applied to {a.target_lib}', file=sys.stderr)
    sys.exit(status)


if __name__ == '__main__':
    main()
