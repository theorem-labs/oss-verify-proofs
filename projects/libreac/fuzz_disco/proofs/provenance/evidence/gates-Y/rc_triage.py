#!/usr/bin/env python3
"""rc_triage.py -- one triage row for every MISMATCH / MIXED / NO-COUNTERPART row of roundconst v2 on the gates-Y file set.

Usage: rc_triage.py --rc-tsv RC.tsv --roundconst ROUNDCONST_V2.py --lib BASE_LIB --cgif-lib CGIF_LIB
                    --img K=PIN:TWIN [--img ...] --donor K=PIN:TWIN [--donor ...] --out OUT.tsv

RC.tsv is roundconst v2's output (status, verdict, key, dst file:line, ...); BASE_LIB is proofs/libreac/fuzz_disco/lib at
the series base and CGIF_LIB proofs/cgif/cgif_file_fuzzer/lib at the donor commit. --img gives the four target pins
(with their unstripped twins, for .symtab), --donor the four donor pins and twins; keys A / B / P / U as in the run.
ROUNDCONST_V2.py is read for its `geometry` function only, so that the agreeing and disagreeing quantity names of a
value are the gate's own.

A roundconst row says: the value is kept from the donor and equals a donor image quantity whose target counterpart
differs. It does not say the numeral IS that quantity (roundconst README, remaining named gap 5). Each row here gets
the FIRST rule (RULES, in order) that holds; a rule reads the numeral's role from its line (comments stripped) and,
where a measurement settles it, makes the measurement on the target pin and twin and holds only when it agrees. A row
no rule takes is UNTRIAGED; a row read as the donor's quantity kept where the target's differs would be DEFECT. Exit 0
only when every row has a rule and none is DEFECT. Output, one row per input row in input order: class (GENERATED /
ROLE / DEFECT / UNTRIAGED), rule, status, key, where (file:line), value, roundconst class, fact.
"""
import argparse
import bisect
import collections
import re
import struct
import sys

from elftools.elf.elffile import ELFFile

SYSNAMES = {17: 'getcwd', 23: 'dup', 24: 'dup3', 25: 'fcntl', 29: 'ioctl', 35: 'unlinkat', 46: 'ftruncate',
            48: 'faccessat', 56: 'openat', 57: 'close', 62: 'lseek', 63: 'read', 64: 'write', 65: 'readv',
            66: 'writev', 73: 'ppoll', 78: 'readlinkat', 79: 'newfstatat', 80: 'fstat', 93: 'exit', 94: 'exit_group',
            96: 'set_tid_address', 98: 'futex', 99: 'set_robust_list', 113: 'clock_gettime', 124: 'sched_yield',
            129: 'kill', 130: 'tkill', 131: 'tgkill', 134: 'rt_sigaction', 135: 'rt_sigprocmask', 160: 'uname',
            167: 'prctl', 172: 'getpid', 178: 'gettid', 214: 'brk', 215: 'munmap', 220: 'clone', 222: 'mmap',
            226: 'mprotect', 233: 'madvise', 261: 'prlimit64', 278: 'getrandom'}
GENERATED = {
    'YB01': 'the 50 hand-off states, written by the start-up collector run on the fuzz_disco image (Pass1 / Pass2 '
            'drivers, colrun.py 59778df6f00b) and formatted by hsform.py hs; re-checked by YB1m startup_cert in the '
            'kernel, by ifchk (G4-ifchk.md: YF0m cells x 50 states), kimg_overlap (G6-kimg-overlap.md) and codeptr '
            '(G3-codeptr.md, 0 findings)',
    'YB03': 'the join state, written by the start-up collector (Pass1 driver) run on the fuzz_disco image and '
            'formatted by hsform.py js; re-checked by YB1m startup_cert in the kernel, kimg_overlap '
            '(G6-kimg-overlap.md) and codeptr (G3-codeptr.md, 0 findings)'}


def strip_comments(t):
    out, depth, i = [], 0, 0
    while i < len(t):
        if t.startswith('(*', i):
            depth, i = depth + 1, i + 2
            continue
        if t.startswith('*)', i) and depth:
            depth, i = depth - 1, i + 2
            continue
        out.append(t[i] if (not depth or t[i] == '\n') else ' ')
        i += 1
    return ''.join(out)


def sext(v, bits):
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def decode(w):
    """(type, opcode, funct3, rd, rs1, immediate) of a 32-bit RISC-V word, or None"""
    op, rd, f3, rs1 = w & 0x7f, (w >> 7) & 31, (w >> 12) & 7, (w >> 15) & 31
    if op in (0x13, 0x1b, 0x03, 0x67, 0x07):
        return 'I', op, f3, rd, rs1, sext(w >> 20, 12)
    if op in (0x23, 0x27):
        return 'S', op, f3, None, rs1, sext(((w >> 25) << 5) | ((w >> 7) & 31), 12)
    if op == 0x63:
        imm = ((w >> 31) << 12) | (((w >> 7) & 1) << 11) | (((w >> 25) & 0x3f) << 5) | (((w >> 8) & 0xf) << 1)
        return 'B', op, f3, None, rs1, sext(imm, 13)
    if op in (0x37, 0x17):
        return 'U', op, None, rd, None, sext(w >> 12, 20) << 12
    if op == 0x6f:
        imm = ((w >> 31) << 20) | (((w >> 12) & 0xff) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3ff) << 1)
        return 'J', op, None, rd, None, sext(imm, 21)
    return None


class Image:
    """a target pin (bytes, PT_LOADs) with its twin's .symtab and .text bounds; PT_LOAD table of both must agree"""

    def __init__(self, spec):
        pin, _, twin = spec.partition(':')
        self.raw = open(pin, 'rb').read()
        e = ELFFile(open(pin, 'rb'))
        self.loads = [(s['p_vaddr'], s['p_filesz'], s['p_offset'], s['p_memsz'], s['p_align'])
                      for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
        t = ELFFile(open(twin, 'rb'))
        tl = [(s['p_vaddr'], s['p_filesz'], s['p_offset'], s['p_memsz'], s['p_align'])
              for s in t.iter_segments() if s['p_type'] == 'PT_LOAD']
        if [(a, b, d) for a, b, c, d, f in tl] != [(a, b, d) for a, b, c, d, f in self.loads]:
            sys.exit('rc_triage: %s is not a twin of %s' % (twin, pin))
        self.align = sorted({x[4] for x in self.loads})
        txt = t.get_section_by_name('.text')
        self.text = (txt['sh_addr'], txt['sh_addr'] + txt['sh_size'])
        symtab = list(t.get_section_by_name('.symtab').iter_symbols())
        self.funcs = sorted((s['st_value'], s['st_size'], s.name) for s in symtab
                            if s['st_info']['type'] == 'STT_FUNC' and s['st_value'])
        self.objs = {s.name: (s['st_value'], s['st_size']) for s in symtab
                     if s['st_info']['type'] == 'STT_OBJECT' and s['st_value']}
        self.fstart = [f[0] for f in self.funcs]
        words = self.read(self.text[0], self.text[1] - self.text[0])
        if words != txt.data():
            sys.exit('rc_triage: .text of %s differs from its twin' % pin)
        self.imms, self.sysno, self.spadj, self.spoff, self.pairs, self.tpoff = (collections.Counter() for _ in range(6))
        prev = None
        for i in range(0, len(words) - 3, 4):
            d = decode(struct.unpack_from('<I', words, i)[0])
            if not d:
                prev = None
                continue
            ty, op, f3, rd, rs1, imm = d
            self.imms[imm] += 1
            if ty == 'I' and op == 0x13 and f3 == 0 and rd == 17 and rs1 == 0:
                self.sysno[imm] += 1
            if ty == 'I' and op == 0x13 and f3 == 0 and rd == 2 and rs1 == 2:
                self.spadj[imm] += 1
            if ty in ('I', 'S') and rs1 == 2 and op in (0x03, 0x23, 0x07, 0x27):
                self.spoff[imm] += 1
            if ty in ('I', 'S') and rs1 == 4 and op in (0x03, 0x23, 0x07, 0x27, 0x13):
                self.tpoff[imm] += 1
            if prev and prev[0] == 'U' and prev[1] == 0x37 and ty == 'I' and op in (0x13, 0x1b) and f3 == 0 \
                    and rs1 == prev[3]:
                self.pairs[prev[5] + imm] += 1
            prev = d

    def read(self, a, n):
        for va, fs, off, ms, al in self.loads:
            if va <= a and a + n <= va + fs:
                return self.raw[off + a - va:off + a - va + n]
        return None

    def word(self, a):
        b = self.read(a, 4)
        return struct.unpack('<I', b)[0] if b else None

    def func_at(self, a):
        i = bisect.bisect_right(self.fstart, a) - 1
        for j in range(i, max(-1, i - 64), -1):
            st, sz, nm = self.funcs[j]
            if st <= a < st + sz:
                return self.funcs[j]
        return None

    def func_starting(self, a):
        i = bisect.bisect_left(self.fstart, a)
        out = []
        while i < len(self.funcs) and self.funcs[i][0] == a:
            out.append(self.funcs[i])
            i += 1
        return out

    def object_u16(self, name):
        """the 16-bit entries of a named data object of the twin's .symtab, read from the pin, or None"""
        o = self.objs.get(name)
        b = self.read(o[0], o[1]) if o else None
        return list(struct.unpack('<%dH' % (len(b) // 2), b)) if b else None

    def frame(self, st):
        """bytes the function at st takes from sp in its first 16 instructions (sum of `addi sp, sp, -k`)"""
        fr = 0
        for a in range(st, st + 64, 4):
            w = self.word(a)
            d = decode(w) if w is not None else None
            if d and d[0] == 'I' and d[1] == 0x13 and d[2] == 0 and d[3] == 2 and d[4] == 2:
                fr -= d[5]
        return fr

    def callees(self, f):
        """targets of the `jal ra, ..` calls inside function f = (start, size, name)"""
        out = []
        for a in range(f[0], f[0] + f[1], 4):
            w = self.word(a)
            d = decode(w) if w is not None else None
            if d and d[0] == 'J' and d[3] == 1 and a + d[5] not in out:
                out.append(a + d[5])
        return out

    def code(self, v):
        """where v occurs as a constant of this pin's .text"""
        out = []
        if self.spadj.get(-v):
            out.append('`addi sp, sp, -%d` %dx' % (v, self.spadj[-v]))
        if self.spoff.get(v):
            out.append('sp-relative load/store offset %d %dx' % (v, self.spoff[v]))
        for s in (-v, v):
            if self.tpoff.get(s):
                out.append('tp-relative offset %d %dx' % (s, self.tpoff[s]))
        if self.pairs.get(v):
            out.append('lui+addi constant %d %dx' % (v, self.pairs[v]))
        if not out and self.imms.get(v):
            out.append('immediate %d %dx' % (v, self.imms[v]))
        if not out and self.imms.get(-v):
            out.append('immediate -%d %dx' % (v, self.imms[-v]))
        return ('measured in the target pin .text: ' + ', '.join(out)) if out else \
            'the value is no immediate of the target pin .text'


def zeval(expr):
    """value of an arithmetic expression over integer literals (+ - * / mod ^, Z semantics), or None"""
    import warnings
    warnings.simplefilter('ignore', SyntaxWarning)
    if not re.fullmatch(r'(?:\s|\d|[-+*/()^]|mod)+', expr or ''):
        return None
    py = expr.replace('^', '**').replace('mod', '%').replace('/', '//')
    try:
        v = eval(py, {'__builtins__': {}})
    except Exception:
        return None
    return v if isinstance(v, int) else None


def main():
    ap = argparse.ArgumentParser()
    for k in ('rc-tsv', 'roundconst', 'lib', 'cgif-lib', 'out'):
        ap.add_argument('--' + k, required=True)
    ap.add_argument('--img', action='append', required=True)
    ap.add_argument('--donor', action='append', required=True)
    a = ap.parse_args()

    head = open(a.roundconst).read().split('tsv, dspec, tspec, pre = sys.argv[1:5]')[0]
    rc = {}
    exec(compile(head, a.roundconst, 'exec'), rc)
    IMG, D, DC, T = {}, {}, {}, {}
    for s in a.img:
        k, p = s.split('=', 1)
        IMG[k] = Image(p)
        T[k], _ = rc['geometry'](p)
    for s in a.donor:
        k, p = s.split('=', 1)
        D[k], DC[k] = rc['geometry'](p)
    INV = {k: collections.defaultdict(list) for k in D}
    for k, q in D.items():
        for nm, v in q.items():
            if v >= rc['MIN'] or DC[k][nm] not in rc['POSITIONAL']:
                INV[k][v].append(nm)

    def names_of(k, v):
        """the value's surviving donor names: (agreeing in the target, disagreeing)"""
        big = v >= rc['MIN']
        nms = [nm for nm in INV[k].get(v, []) if nm in T[k] or (big and DC[k][nm] not in rc['SYMBOLIC'])]
        return [nm for nm in nms if T[k].get(nm) == v], [nm for nm in nms if T[k].get(nm) != v]

    texts, ctexts = {}, {}

    def lines(rel):
        if rel not in texts:
            texts[rel] = strip_comments(open('%s/%s' % (a.lib, rel), errors='replace').read()).split('\n')
        return texts[rel]

    symdef = {}

    def sym(name):
        """address of a tfib_A_ / src0_A_ code symbol from its Definition in BASE_LIB/Reusable (YB1w / YH03)"""
        if not symdef:
            for f in ('Reusable/YB1w.v', 'Reusable/YH03.v'):
                for m in re.finditer(r'Definition ((?:tfib|src0)_[AE]_\w+)\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+|\d+)\s*\.',
                                     open('%s/%s' % (a.lib, f), errors='replace').read()):
                    symdef.setdefault(m.group(1), (f, int(m.group(2), 0)))
        return symdef.get(name)

    alltexts = {}

    def refcount(name, own):
        """number of BASE_LIB files other than `own` whose text names `name` as a word"""
        if not alltexts:
            import os
            for root, _, fs in os.walk(a.lib):
                for f in fs:
                    if f.endswith('.v'):
                        p = os.path.join(root, f)
                        alltexts[os.path.relpath(p, a.lib)] = open(p, errors='replace').read()
        pat = re.compile(r'(?<![\w\'])%s(?![\w\'])' % re.escape(name))
        return sum(1 for rel, t in alltexts.items() if rel != own and pat.search(t))

    libdefs = {}

    def libdef(name):
        """the integer value of `Definition NAME : Z := <integer expression>.` in BASE_LIB/Reusable, or None"""
        if not libdefs:
            import os
            raw = {}
            for f in sorted(os.listdir('%s/Reusable' % a.lib)):
                if f.endswith('.v'):
                    t = strip_comments(open('%s/Reusable/%s' % (a.lib, f), errors='replace').read())
                    for m in re.finditer(r'Definition\s+(\w+)\s*:\s*Z\s*:=\s*([^.]*?)\s*\.(?:\s|$)', t):
                        raw.setdefault(m.group(1), set()).add(m.group(2))
            libdefs['?'] = None
            for _ in range(3):
                for n, es in raw.items():
                    if n in libdefs or len(es) != 1:
                        continue
                    e = re.sub(r'\b[A-Za-z_]\w*\b', lambda m: '(%d)' % libdefs[m.group(0)]
                               if libdefs.get(m.group(0)) is not None else m.group(0), next(iter(es)))
                    v = zeval(e)
                    if v is not None:
                        libdefs[n] = v
        return libdefs.get(name)

    cgif_defs = {}

    def cgif_def(name):
        """the numerals a `Definition NAME` of the donor lib binds (first one per file), by file"""
        if not cgif_defs:
            import os
            for root, _, fs in os.walk(a.cgif_lib):
                for f in fs:
                    if f.endswith('.v'):
                        t = strip_comments(open(os.path.join(root, f), errors='replace').read())
                        for m in re.finditer(r'Definition\s+(\w+)\s*(?::\s*[\w ]+)?:=\s*([^.]*)\.', t):
                            cgif_defs.setdefault(m.group(1), m.group(2).strip())
        return cgif_defs.get(name)

    wdefs = {}

    def wdef(rel, name):
        if rel not in wdefs:
            wdefs[rel] = {m.group(1): int(m.group(2), 16) for m in re.finditer(
                r'Definition (W_\w+)\s*(?::[^:=]*)?:=\s*\(?\s*(0x[0-9a-fA-F]+)', '\n'.join(lines(rel)))}
        return wdefs[rel].get(name)

    RULES = []

    def rule(name, cls):
        def deco(fn):
            RULES.append((name, cls, fn))
            return fn
        return deco

    # ---- the rules, in order --------------------------------------------------------------------------------------
    @rule('COLLECTOR-STATE', 'GENERATED')
    def _(x):
        g = GENERATED.get(x['base'])
        if g:
            b = x['before']
            role = ('EVar index' if re.search(r'\(EVar\s*$|EVar\s+$', b) else
                    'offset a_off from a symbolic base' if re.search(r'a_off\s*:=\s*-?\s*$', b) else
                    'index of a KRange variable' if re.search(r'KRange \(EVar\s*$', b) else 'a field of a state')
            return 'generated file: %s; the numeral is %s' % (g, role)

    @rule('CODE-WINDOW', 'ROLE')
    def _(x):
        m = re.search(r'build_table\s+\w+\s+(0x[0-9a-fA-F]+)\s+$', x['before'])
        if not m or not x['after'].startswith('%nat'):
            return None
        lo, n, img = int(m.group(1), 16), x['v'], IMG[x['key']]
        hi = lo + 4 * n
        starts = img.func_starting(lo)
        ends = [f for f in img.funcs if f[0] + f[1] == hi and f[1]]
        if not starts or not ends:
            return None
        inside = [f for f in img.funcs if lo <= f[0] and f[0] + f[1] <= hi and f[1]]
        return ('decode-window length in words: build_table %#x %d covers [%#x, %#x); measured on the target twin: '
                '%#x is the start of %s and %#x the end of %s; the window holds %d whole function(s), %d bytes = 4 * %d'
                % (lo, n, lo, hi, lo, starts[0][2][:48], hi, ends[0][2][:48], len(inside), hi - lo, n))

    @rule('CODE-OFFSET', 'ROLE')
    def _(x):
        m = re.search(r'(?:^|[^\w])((?:tfib|src0)_A_\w+)\s*\+\s*$', x['before'])
        if not m:
            return None
        d = sym(m.group(1))
        if not d:
            return None
        base, img = d[1], IMG[x['key']]
        addr = base + x['v']
        f = img.func_at(addr)
        if not f or f[0] != base:
            return None
        fact = ('code offset +%#x inside %s (%s: %#x); measured: %#x lies in %s [%#x, %#x) of the target twin'
                % (x['v'], m.group(1), d[0], base, addr, f[2], f[0], f[0] + f[1]))
        w = re.match(r'\)\)\s*=\s*Some\s*\((0x[0-9a-fA-F]+)%bv', x['after'])
        if w:
            if img.word(addr) != int(w.group(1), 16):
                return None
            fact += '; the pin word there is %s = the stated word' % w.group(1)
        return fact

    @rule('INSN-IMM', 'ROLE')
    def _(x):
        m = re.search(r'decode_any\s+(\(\s*(0x[0-9a-fA-F]+)%bv\s*:\s*bv 32\s*\)|(W_\w+))\s*=\s*Some\s*\((\w+)[^,]*$',
                      x['before'])
        if not m:
            return None
        w = int(m.group(2), 16) if m.group(2) else wdef(x['file'], m.group(3))
        d = decode(w) if w is not None else None
        if not d:
            return None
        imm = d[5] >> 12 if m.group(4) in ('Lui', 'Auipc') else d[5]
        if imm != x['v']:
            return None
        return ('instruction field: the %s immediate of the decoded word %#010x; measured: the word decodes to '
                'immediate %d' % (m.group(4), w, imm))

    @rule('SYSCALL-NO', 'ROLE')
    def _(x):
        v, b = x['v'], x['before']
        if v not in SYSNAMES:
            return None
        if re.search(r'(getr \w+ 17\)?\s*=\s*(Z_to_bv 64\s*|Z64\s*)?|\(getr \w+ 17\)\)\s*=\s*|\bx8\s*=\s*|17\)?\s*=\s*'
                     r'SLit\s+|model 17\s+)$', b) or (re.search(r'\|\s*Some\s+$', b) and re.search(
                         r'svc|sys|reg_lit \w+ 17\b', x['ctx8'])):
            return ('RISC-V Linux syscall number %d = %s (a7 = register 17 holds it at ecall); measured: `addi a7, '
                    'zero, %d` occurs %d times in the target pin .text' % (v, SYSNAMES[v], v, IMG[x['key']].sysno.get(v, 0)))

    @rule('PAGE-4096', 'ROLE')
    def _(x):
        if x['v'] != 4096:
            return None
        b, af, ctx = x['before'], x['after'], x['ctx']
        img = IMG[x['key']]
        if img.align != [4096]:
            return None
        if re.search(r'\b\w*(_len|_size|_extent|_bytes|_count|_words)\s*:?=\s*$', b) and not \
                re.search(r'(page|PG|pg|STACK|BUF|DICT)', b[-40:]):
            return None
        lzw = re.search(r'\b(la_\w+|lzw\w*|MAX_DICT\w*)\b', ctx) or (
            x['base'] in ('YI0t', 'YI0m', 'YO07') and re.search(r'\b(idl|TI|LI|LM|TM|dp|below)\b', ctx))
        use = (
            'alignment (x mod 4096)' if re.search(r'\bmod\s*$', b) else
            'divisibility (4096 | x)' if re.search(r'\(\s*$', b) and re.match(r'\s*\|', af) else
            'page index (x / 4096)' if re.search(r'/\s*$', b) else
            'round up to a page (x + 4096 - 1)' if re.match(r'\s*-\s*(1|UNIT)\b', af) else
            'pages to bytes (n * 4096)' if re.search(r'\*\s*$', b) or re.match(r'\s*\*', af) else
            'page mask -4096 / 2^64 - 4096' if re.search(r'\(-\s*$|2 \^ 64 - $|-$', b) else
            'one page plus an offset (4096 + x)' if re.search(r'\(\s*$', b) and re.match(r'\s*\+', af) else
            '4096 = 2^12 (a rewriting step)' if re.search(r'2 \^ 12\)?\s*with\s*$', b) or
            re.match(r'\s*with \(2 \^ 12\)', af) else
            'divisor of a division / modulo lemma (page arithmetic)' if re.search(
                r'(div_mod|Z_div_mod_eq_full|mod_pos_bound|mul_div_le|div_exact|div_pos|mul_succ_div_gt|div_le_mono|'
                r'div_str_pos|mod_unique|mod_mod_divide|div_small)\b[^;]*$', b[-90:]) else
            'factor of a page-size product (Z.mul_comm 4096 _)' if re.search(r'mul_comm\s*$', b) else
            'the page size folded to its name (change 4096 with PGSZ)' if re.match(r'\s*with\s+PGSZ\b', af) else
            'argument / result of page_round (one page rounds to one page)' if re.search(r'page_round\w*\s*$', b) or
            re.search(r'\(page_round\w* \d+\)\s*with\s*$', b) else
            'GIF LZW: the 4096-entry code table (12-bit codes)' if lzw else
            'PATH_MAX 4096 (path length bound)' if re.search(r'\bpath(_max)?\b', ctx) else
            'errno bound (an error code is below 4096)' if re.search(r'errno|\be\s*<\s*$', ctx + ' ' + b) else
            'address fact floor: a pointer at or above the first page (mkAF 4096 hi al)' if re.search(r'mkAF\s+$', b) else
            'page-scaled variable (escale 4096 (EVar v))' if re.search(r'escale\s+$', b) else
            'lower bound: the first page above the null page (4096 <= x)' if re.match(r'\s*(<=|<)', af) or
            re.search(r'af_lo\s*:=\s*$', b) else
            'upper bound 4096 (x < 4096 / x <= 4096)' if re.search(r'(<|<=|<\?|<=\?)\s*$', b) else
            'named page constant' if re.search(r'(PGSZ|kPage|ESTACK|page_size|page_round\w*|pagesize|PG\w*)\b[^;]*'
                                               r'(:=|=|with)\s*$', b[-60:]) or
            re.search(r'(PGSZ|ESTACK|kPage)\s*:\s*Z\s*:=\s*$', b) else
            'one page past a base (b + 4096)' if re.search(r'\+\s*$', b) else
            'one page below a base (b - 4096)' if re.search(r'[\w)]\s*-\s*$', b) else
            'one-page length (region / mapping / chunk of 4096 bytes)' if re.search(
                r'(mkRegion|zregion|Some \d+%nat, 0,|\(LMem|rg_len|Malloc|KMmap\w*|KMprotect|KMunmap \d+|Z_to_bv 64|w64|'
                r'Z64|SLit|ELit|SOff \d+|ly_\w+ ly,|ASp \w+,|LMem a,|word_mem|chunk_ok_word|zeros\w*|SK0_apart|sv_off|'
                r'\(\w+, mkAF|padd \w+|lit64_small|elenZ_lit|store_ok_all|firstn|rdn|length|PSec|req_size|'
                r'v_lui|place_in_model|z8|footprint|unmap|apart|_apart|region\w*|Forall_c\w+_of_range|'
                r'mem_ok_\w+|covered_sound|Z_lt_le_dec)', b[-70:]) else None)
        if not use:
            return None
        ag, dis = names_of(x['key'], 4096)
        return ('4096 = the page size of both pins (every PT_LOAD p_align 0x1000, measured); use: %s; the value is also '
                'the target\'s own quantity under %d of its %d donor names (e.g. %s); the disagreeing names are %s'
                % (use, len(ag), len(ag) + len(dis), ag[0] if ag else '-',
                   ('spans between two image bounds only' if all(DC[x['key']][n] == 'span' for n in dis) else
                    '; '.join(dis[:3]) + (' (+%d spans)' % (len(dis) - 3) if len(dis) > 3 else ''))))

    def balanced(s, i):
        """the text inside the parenthesis opening at s[i] and the index after its close, or (None, None)"""
        depth = 0
        for j in range(i, len(s)):
            depth += {'(': 1, ')': -1}.get(s[j], 0)
            if depth == 0:
                return s[i + 1:j], j + 1
        return None, None

    def operand(s, i):
        while i < len(s) and s[i] == ' ':
            i += 1
        if i < len(s) and s[i] == '(':
            return balanced(s, i)
        m = re.match(r'[^\s;)]+', s[i:])
        return (m.group(0).rstrip('.'), i + m.end()) if m else (None, None)

    def subst(e):
        return re.sub(r'\b[A-Za-z_]\w*\b', lambda m: '(%d)' % libdef(m.group(0)) if libdef(m.group(0)) is not None
                      else m.group(0), e)

    def sampled_equal(l, r):
        """l = r as Z expressions, each application of names (`ly_reg L ra`) one variable, at sample points
        (distinct multiples of 2^20); None if not evaluable"""
        def norm(e):
            return re.sub(r"[A-Za-z_][\w']*(?:\s+(?!mod\b)[A-Za-z_][\w']*)*",
                          lambda m: m.group(0) if m.group(0) == 'mod' else 'v_' + re.sub(r"\W", '_', m.group(0)), e)
        l, r = norm(l), norm(r)
        names = sorted(set(re.findall(r'\bv_\w+', l + ' ' + r)))
        if not names or len(names) > 6:
            return None
        for k in (3, 7, 11):
            env = {n: '(%d)' % ((k + 2 * i) << 20) for i, n in enumerate(names)}
            f = lambda e: zeval(re.sub(r'\bv_\w+', lambda m: env[m.group(0)], e))
            a, b = f(l), f(r)
            if a is None or b is None or a != b:
                return None if a is None or b is None else False
        return True

    @rule('ARITH-STEP', 'ROLE')
    def _(x):
        t, pos = x['text'], x['pos']
        for m in re.finditer(r'\b(change|replace)\s+', t):
            l, j = operand(t, m.end())
            if l is None or not re.match(r'\s*with\b', t[j:]):
                continue
            r, k = operand(t, j + re.match(r'\s*with\b', t[j:]).end())
            if r is None or not (m.start() <= pos < k):
                continue
            lv, rv = zeval(subst(l)), zeval(subst(r))
            if lv is not None and lv == rv:
                return 'arithmetic identity `%s (%s) with %s`; measured: both sides evaluate to %d' % (
                    m.group(1), l.strip()[:50], r.strip()[:40], lv)
            if m.group(1) == 'replace' and sampled_equal(subst(l), subst(r)):
                return ('a constant of the rewriting identity `replace (%s) with (%s)` (closed by lia); measured: '
                        'both sides agree at sample points' % (l.strip()[:45], r.strip()[:45]))
        m = re.search(r'assert \((?:\w+\s*:\s*)?([^=]+?)\s*=\s*([^=]+?)\)\s*by\b', t)
        if m and m.start() <= pos <= m.end():
            lv, rv = zeval(subst(m.group(1))), zeval(subst(m.group(2)))
            if lv is not None and lv == rv:
                return ('asserted identity `%s = %s` (by reflexivity); measured: both sides evaluate to %d from the '
                        'lib\'s definitions' % (m.group(1).strip()[:45], m.group(2).strip()[:30], lv))
            if sampled_equal(subst(m.group(1)), subst(m.group(2))):
                return 'a constant of the asserted identity `%s = %s`; measured: both sides agree at sample points' % (
                    m.group(1).strip()[:45], m.group(2).strip()[:45])
        return None

    @rule('FRAME-SIZE', 'ROLE')
    def _(x):
        b, img = x['before'], IMG[x['key']]
        m = re.search(r'Definition\s+(\w*(?:FRAME|STK)\w*)\s*:\s*Z\s*:=\s*$', b)
        if not m:
            return None
        v = x['v']
        hit = [f for f in img.funcs if f[1] and img.frame(f[0]) == v]
        if hit:
            return ('stack frame size: %s = %d = the frame of %s (`addi sp, sp, -..` prologue sum, measured on the '
                    'target pin)' % (m.group(1), v, hit[0][2][:48]))
        for am in re.finditer(r'Definition (A_\w+)\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+)\s*\.', x['full']):
            f0 = int(am.group(2), 16)
            f = img.func_at(f0)
            if not f or f[0] != f0:
                continue
            for g0 in img.callees(f):
                g = img.func_at(g0)
                if g and img.frame(f0) + img.frame(g0) == v:
                    return ('stack depth: %s = %d = the frame of %s (%d) + the frame of its callee %s (%d), '
                            'measured on the target pin' % (m.group(1), v, f[2], img.frame(f0), g[2], img.frame(g0)))
        return None

    @rule('VAR-INDEX', 'ROLE')
    def _(x):
        b, af = x['before'], x['after']
        pats = [
            (r'(\(EVar\s*|\bEVar\s+|\bV\s+|\bepg\s+|\bupg\s+)$', 'index of a symbolic variable (EVar / V / epg n) of the abstract state'),
            (r'\bSOff\s+$', 'index n of a symbolic value SOff n k'),
            (r'(\bew\s+\S+\s+|\(ew\s+\S+\s+|ewset \S+(?: \S+ \([^()]*\))? $|\bewset\s+\(.*\)\s+$)', 'index of the environment entry (ew E n / ewset E n)'),
            (r'(\bhavoc\s+\S+\s+|vf_after_icpt\s+|st_ok_after_call \S+ |ss_after_call \S+ \S+ |junk_regs(_ok \S+)? \S+ |'
             r'forget_reg(\s+\S+){3,4}\s+|vf_add_fact \S+ |xafterD\s+|st_ok_add_fact \S+ \S+ \S+ \S+ |'
             r'bt_use_tab \S+ \S+ |vf_icpt_memcpy(_ext)? .* |PG\s+|KZ _\s+|_add_atom \S+ \(.*\) |addfact\s+|'
             r'st_ok_set_regs \S+ |word_of_chunk_at( \S+){4} |region_ok_agree \S+ |regs_atoms_lt_mono )$',
             'index of the next fresh symbolic variable passed to a state step'),
            (r'(env_agree(_refl)?|regs_ok_agree|facts_ok_agree|regs_atoms_lt|facts_atoms_lt|region_atoms_lt|ss_atoms_lt|'
             r'den_off0 \S+|proj1 \S+|Y)\s+\(?$', 'bound / index of the symbolic environment (n = number of variables in scope)'),
            (r'drv_add_statics \S+ \(map snd \S+\)\s+$', 'index of the first fresh variable for the added statics'),
        ]
        for p, role in pats:
            if re.search(p, b):
                if re.search(r'EVar\s*$', b):
                    n = len(re.findall(r'\(EVar %d\)' % x['v'], '\n'.join(lines('Reusable/YB01.v'))))
                    role += ('; measured: `(EVar %d)` occurs %d times in YB01.v, the hand-off states the collector wrote '
                             'from the fuzz_disco image' % (x['v'], n))
                return role
        if re.match(r'%nat\s*,\s*', af) and re.search(r'\(\s*$', b):
            return 'index of an atom / fact of the abstract state ((n%nat, fact))'
        if re.search(r'\(Some\s+$', b) and af.startswith('%nat'):
            return 'index of the symbolic base variable of a region (Some n%nat)'
        if re.search(r'\|\s*$', b) and af.startswith('%nat'):
            return 'match arm on an atom / variable index (| n%nat => ...)'
        if re.search(r'Definition\s+(a[A-Z]\w*|aE\d+|h[A-Z]\w*|K_\w+|e\w+)\s*(:\s*nat\s*)?:=\s*$', b) and \
                af.startswith(('%nat', '.')):
            return 'definition of an atom / variable index name (Definition a.. := n%nat)'
        if re.search(r'\(j <\s*$', b) and re.match(r'\)?%nat', af):
            return 'bound on environment indices (forall j < n, ew E j = ...)'
        if re.search(r'change\s+$', b) and re.match(r'%nat with \(\S+ \+ \d+\)%nat', af):
            return 'a variable index rewritten as a sum'
        if re.search(r'(xvA|xva)\s+$', b):
            return 'index of a symbolic variable (xvA n)'
        return None

    @rule('CHAR-CODE', 'ROLE')
    def _(x):
        full, pos = x['full'], x['fpos']
        lo = full.rfind('[', max(0, pos - 600), pos)
        hi = full.find(']', pos, pos + 600)
        if lo < 0 or hi < 0 or ']' in full[lo + 1:pos] or '[' in full[pos:hi]:
            return None
        vals, other = [], 0
        for s in full[lo + 1:hi].split(';'):
            s = re.sub(r'^Z_to_bv 8\s+', '', s.strip())
            if re.fullmatch(r'0x[0-9a-fA-F]+|\d+', s):
                vals.append(int(s, 0))
            else:
                other += 1
        if len(vals) < 6 or other > 0.2 * len(vals) or any(v > 255 for v in vals):
            return None
        pr = sum(1 for v in vals if 32 <= v < 127 or v in (0, 9, 10))
        if pr < 0.7 * len(vals):
            return None
        s = ''.join(chr(v) if 32 <= v < 127 else '\\x%02x' % v for v in vals)
        return 'character code %d = %r in a byte list; measured: the list decodes to %r' % (x['v'], chr(x['v']), s[:60])

    @rule('TP-OFFSET', 'ROLE')
    def _(x):
        if re.search(r'(\bsrc0_tp|\bms_tp \w+|errno_off \w+\)?\s*with)\s*(-|\(-)\s*$', x['before']) or \
                re.search(r'\bERRNO\s*:\s*Z\s*:=\s*src0_tp\s*-\s*$', x['before']):
            return ('offset of errno from the thread pointer in the model\'s TLS layout (the region based at aTP holds '
                    'the errno word at -%d); %s' % (x['v'], IMG[x['key']].code(x['v'])))

    @rule('STACK-OFFSET', 'ROLE')
    def _(x):
        b = x['before']
        if re.search(r'\b(sp0|spZ\s+\w+|sp|fp|bv_unsigned sp|spZ regs\w*)\s*[-+]\s*(\(\s*-?\s*)?$', b) or re.search(
                r'SOff 2 \(\s*-\s*$|mkRegion \(Some 2%nat\)( \(?-?\s*\d+\)?)* \(?-?\s*$|\(Some 2%nat,\s*-?\s*$|'
                r'region_ok_stack \S+ \S+ _ 2 sp0 \(- ?$|\(Some 2%nat\) \(-$|OSP_\w+\s*:\s*Z\s*:=\s*-$|'
                r'wl_after \S+ \d+ \(-$|s?rz_sym_\w+ .* \(-$', b):
            return 'stack offset from the stack pointer (sp0 / spZ / SOff 2 / a region based on x2); ' + \
                IMG[x['key']].code(x['v'])

    @rule('BASE-OFFSET', 'ROLE')
    def _(x):
        b = x['before'].rstrip()
        m = re.search(r"([A-Za-z_][\w']*|\))\s*([+-])\s*\(?$", b)
        if not m:
            return None
        pre = b[:m.start(2)].rstrip()
        if re.search(r'((tfib|src0)_\w*|img_\w*|IMG\w*|seg_\w*|TSEGS|segs|top\w*|TOP\w*|\d|img_\w+ A)\s*\)?$', pre):
            return None
        fact = IMG[x['key']].code(x['v'])
        if m.group(2) == '+' and re.search(r'\b(CTX|ms_ctx B|LOCK)\s*\(?$', pre):
            o = IMG[x['key']].objs.get('__malloc_context')
            if o and 0 <= x['v'] <= o[1]:
                fact = ('an offset within the allocator context: the target image object __malloc_context has size %d '
                        '(measured), %d <= %d; ' % (o[1], x['v'], o[1])) + fact
        return 'byte offset from a run-time base (`%s N`); %s' % (b[-28:].strip(), fact)

    @rule('FIELD-TABLE', 'ROLE')
    def _(x):
        b, af = x['before'], x['after']
        if (re.search(r'\(\s*$', b) and re.match(r'\s*,\s*\d+%N', af)) or \
                (re.search(r'\bfld \w+ \w+\s+$', b) and re.match(r'\s+\d+\s', af)) or \
                (re.search(r'(c_off := -?|\(\d+%bv,\s*)$', b) and re.match(r'\s*[;)]', af)) or \
                (re.search(r'mkChunk\s+\(?-?\s*$', b) and re.match(r'(\s*\+ 80 \* \w+\)?)?\)?\s+\(C(Val|Data)', af)) or \
                (re.search(r'(\(AF\s+|AF \d+, )$', b) and re.match(r'\s*\)', af)):
            return 'offset of a field within a run-time structure (field / chunk table); ' + IMG[x['key']].code(x['v'])
        return None

    @rule('REGION-OFFSET', 'ROLE')
    def _(x):
        b = x['before']
        if re.search(r'(mkRegion \((Some \w+(%nat)?|None)\)( \([^()]*\)| -?\d+)* \(?-?\s*|\(Some \d+%nat,( -?\d+,)*\s*-?\s*|'
                     r'\bcsn \d+ \+ |\(csn \d+\) |SR_load \(Some \d+%nat\) |Z\.eqb \(r_lo rg\) |'
                     r'zregion \d+ \d+ |word_of_chunk_at( \S+){6} )$', b):
            return ('offset relative to the symbolic base of a region (region bounds lo / hi / wlo / whi, or a chunk '
                    'of it); ' + IMG[x['key']].code(x['v']))

    @rule('MASK', 'ROLE')
    def _(x):
        b = x['before']
        v = x['v']
        if v & (v - 1) == 0 and (re.search(r'(ALU_AND|alu64 ALU_AND|land\w*|SLit)\b[^;]*\(-\s*$', b[-70:]) or
                                 re.search(r'2 \^ 64 - $|\(\(-$', b)):
            return 'alignment mask -%d (x AND -%d rounds x down to a multiple of %d)' % (v, v, v)

    @rule('FUEL', 'ROLE')
    def _(x):
        if re.search(r'\b(irun\d?|span_loop(_ge)?|diag_exit_check|src0_diag_exit_tac \S+ \S+|FUEL|fuel|run_n|nsteps)\s+$',
                     x['before']):
            return 'fuel / step bound of an executable model run (vm_compute); not a quantity of the program'

    @rule('SIZE-CLASS-TABLE', 'ROLE')
    def _(x):
        full, pos = x['full'], x['fpos']
        d = full.rfind('Definition', 0, pos)
        m = re.match(r'Definition\s+(\w+)', full[d:d + 80]) if d >= 0 else None
        if not m or 'size_classes' not in m.group(1) or ('.' in full[d:pos] and not re.search(r'\d\.\d', full[d:pos])):
            return None
        tab = IMG[x['key']].object_u16('__malloc_size_classes')
        if not tab or x['v'] not in tab:
            return None
        return ('an entry of musl\'s size_classes table (%s); measured: the target image object __malloc_size_classes '
                'holds %d at index %d' % (m.group(1), x['v'], tab.index(x['v'])))

    @rule('MODEL-PC', 'ROLE')
    def _(x):
        if re.search(r'(\(PC\s+|\(at_ base\s+|\(mkSS\s+|^\s*\(mkSS\s+)$', x['before']) and x['v'] < 0x10000:
            d = x['full'].rfind('Definition', 0, x['fpos'])
            nm = re.match(r'Definition\s+(\w+)', x['full'][d:d + 80]) if d >= 0 else None
            used = ''
            if nm and re.search(r'mkSS\s*$', x['before']):
                used = '; the definition %s is referenced by %d other lib file(s) (measured)' % (
                    nm.group(1), refcount(nm.group(1), x['file']))
            return ('program counter of the analysed routine relative to its start (PC / at_ base / mkSS n), below the '
                    'image base 0x10000: not an image address or length' + used)

    @rule('ALLOC-MODEL', 'ROLE')
    def _(x):
        m = re.search(r'\b(class_size|class_id|rz_size|max_cached|kBatch\w*|sec_hulls|sec_map_size|HULL_MAX|SEC_LEN_MAX|'
                      r'needed_primary|ck_rz|as_budget|size_to_class|KMmap\w*|KMunmap|KMprotect|KBrk\w*|'
                      r'MMAP_THRESHOLD|set_bounces|st_bounces|bnc_of_leaf|st_b|cat_struct_size|req_size|PSec|PPrim|'
                      r'CTX_SIZE|ctxW|kSecRz|kMallocFill)\b', x['ctx'])
        if m:
            return ('allocator model constant (size class / redzone / cache / batch / bounce bound of the allocator '
                    'model, written from the allocator source; the sentence names %s)' % m.group(1))

    @rule('TEST-DATA', 'ROLE')
    def _(x):
        full, pos = x['full'], x['fpos']
        d = max(full.rfind('Example', 0, pos), full.rfind('Definition', 0, pos), full.rfind('Lemma', 0, pos))
        head = full[d:d + 60] if d >= 0 else ''
        if head.startswith('Example') or re.search(r'\b(probe_sizes|campaign|gen_ans|gen_junk|gen_kans|gen|shape_probe|'
                                                  r'pingpong|wf_random|sdecZ|check)\b', x['before'][-60:] + head):
            return 'input or expected value of an executable test (%s ...), checked by vm_compute' % head[:40].strip()

    @rule('NAMED-CONST', 'ROLE')
    def _(x):
        b = x['before']
        m = (re.search(r'Definition\s+(\w+)\s*(?:\([^)]*\)\s*)*(?::\s*[\w ]+)?:=\s*(?:[\w ]*[+\-*/^]\s*)?\(?-?\s*$', b)
             or re.search(r'assert \(\w+\s*:\s*(\w+)\s*=\s*$', b) or re.search(r'\((\w+)\s*=\s*$', b))
        if not m:
            return None
        name = m.group(1)
        c = cgif_def(name)
        same = c is not None and re.search(r'(?<![\w.])%s(?![\w])' % re.escape(x['lit']), c)
        donor = ((' with the same numeral' if same else ' as %r' % c[:40]) if c is not None else
                 ': no (a fuzz_disco-only name)')
        return 'named model constant %s = %d; the donor lib defines %s%s; %s' % (
            name, x['v'], name, donor, IMG[x['key']].code(x['v']))

    @rule('GIF-TRAILER', 'ROLE')
    def _(x):
        if x['v'] == 0x3b and re.search(r'\[\s*$', x['before']) and x['after'].startswith(']') and \
                re.search(r'gif|trailer', x['ctx'], re.I):
            return 'the GIF trailer byte 0x3B (\';\', GIF89a) appended to the output stream'

    @rule('POW2-EXP', 'ROLE')
    def _(x):
        if re.search(r'2 \^\s*\(?$', x['before']):
            return 'exponent n of a power of two (2 ^ %d = %d)' % (x['v'], 2 ** x['v'])

    @rule('ARGC-BOUND', 'ROLE')
    def _(x):
        if x['v'] == 1024 and re.search(r'\b(V_ARGC|argc\w*|length av|lay_len_av)\b', x['ctx8']):
            return 'argument-count bound 1024 of the harness model (1 <= argc <= 1024: YP08 argc_bounds, YA02 len_av)'

    @rule('OBJECT-END', 'ROLE')
    def _(x):
        m = re.search(r'\((0x[0-9a-fA-F]+)\s*\+\s*$', x['before'])
        if not m:
            return None
        a0, img = int(m.group(1), 16), IMG[x['key']]
        for nm, (st, sz) in img.objs.items():
            if st <= a0 < st + sz and a0 + x['v'] == st + sz:
                return ('length to the end of an object: %s + %d = the end of %s [%#x, %#x) in the target twin '
                        '(measured)' % (m.group(1), x['v'], nm, st, st + sz))
        return None

    @rule('STACK-LIMIT', 'ROLE')
    def _(x):
        if x['v'] == 1024 and re.search(r'8 \* 1024 \* 1024', x['text']):
            return 'the 8 MiB stack limit 8 * 1024 * 1024 of the model (8 * 1024 * 1024 = %d)' % (8 << 20)

    @rule('LZW-384', 'ROLE')
    def _(x):
        if x['v'] != 384 or x['base'] not in ('YCbw', 'YI0s', 'YI0t'):
            return None
        ident = 'replace (12 * (lp + 1) * 2 ^ 32 / 2 ^ 27) with (384 * (lp + 1))'
        if ident not in '\n'.join(lines('Reusable/YCbw.v')) or 12 * 2 ** 32 // 2 ** 27 != 384:
            return None
        return ('the code-length bound constant 384 = 12 * 2^32 / 2^27 of the LZW output-size formula (YCbw.v '
                'states `%s`; measured: 12 * 2^32 / 2^27 = 384)' % ident)

    @rule('MMAP-BOUND', 'ROLE')
    def _(x):
        if re.search(r'MMAP_THRESHOLD', x['ctx8']) and re.search(r'\bIB\b.*\bUNIT\b', x['text']):
            t, ib, un = libdef('MMAP_THRESHOLD'), libdef('IB'), libdef('UNIT')
            if None not in (t, ib, un) and t + ib + un == x['v']:
                return ('lower bound of an mmap length page_round (n + IB + UNIT) under MMAP_THRESHOLD <= n; measured '
                        'from the lib definitions: MMAP_THRESHOLD + IB + UNIT = %d + %d + %d = %d' % (t, ib, un, x['v']))

    @rule('SPEC-BOUND', 'ROLE')
    def _(x):
        b, af = x['before'], x['after']
        w = b[-40:] + ' @ ' + af[:40]
        if re.search(r'(tfib|src0|img|IMG|seg|TOP|top|PT_LOAD)', w):
            return None
        if re.search(r'(<=|<|<=\?|<\?)\s*$', b) or re.match(r'\s*(<=\?|<\?|<=|<)\s', af) or \
                re.search(r'Z\.leb\s+\w+\s+$', b):
            return 'bound in a specification, precondition or comparison on a run-time quantity (`%s`)' % w.strip()[:70]

    @rule('SYM-LITERAL', 'ROLE')
    def _(x):
        if re.search(r'(SLit|ELit|Z64|w64|Z_to_bv 64|lit64_small)\s*\(?-?\s*$', x['before']):
            return 'literal of the abstract machine state (a constant the analysed code computes or loads); ' + \
                IMG[x['key']].code(x['v'])

    @rule('PAGES', 'ROLE')
    def _(x):
        w = x['before'][-60:] + ' @ ' + x['after'][:30]
        m = re.search(r'\b(\d+)\s*\*\s*PGSZ\b', w)
        pg = libdef('PGSZ')
        if m and pg and int(m.group(1)) * pg == x['v']:
            return '%s pages: %s * PGSZ with PGSZ = %d (lib definition) = %d, measured' % (
                m.group(1), m.group(1), pg, x['v'])

    HAND = {
        ('Reusable/YG0s.v:787', 1024): 'witness of a divisibility step in shadow arithmetic: `exists (q * 1024)` after '
                                      '`Z.mod_divide in R3 as [q Hq]`, closed by lia (1024 = 8192 / 8, the shadow scale)',
        ('Reusable/YP08.v:288', 1024): 'value range [1 or 2, 1024] of atom 3, the argument count: the same file\'s '
                                      'argc_bounds (YP08.v:387) states 1 <= length av <= 1024',
    }

    @rule('HAND', 'ROLE')
    def _(x):
        return HAND.get(('%s:%d' % (x['file'], x['line']), x['v']))
    # ---- driver ---------------------------------------------------------------------------------------------------
    rows = [l.rstrip('\n').split('\t') for l in open(a.rc_tsv)][1:]
    occ = collections.Counter()
    out = []
    stats = collections.Counter()
    for r in rows:
        if r[0] == 'SAME':
            continue
        f, ln = r[3].rsplit(':', 1)
        ln, v, k = int(ln), int(r[8], 16), r[2]
        L = lines(f)
        t = L[ln - 1] if ln <= len(L) else ''
        n = occ[(f, ln, v, k)]
        occ[(f, ln, v, k)] += 1
        ms = sorted((m for p in {hex(v), str(v)} for m in re.finditer(r'(?<![\w.])' + re.escape(p) + r'(?![\w])', t, re.I)),
                    key=lambda m: m.start())
        x = dict(file=f, base=f.split('/')[-1][:-2], line=ln, v=v, key=k, text=t, status=r[0])
        if n < len(ms):
            m = ms[n]
            x.update(before=t[max(0, m.start() - 90):m.start()], after=t[m.end():m.end() + 50], pos=m.start(),
                     lit=m.group(0), ctx='\n'.join(L[max(0, ln - 3):ln + 1]), full='\n'.join(L),
                     ctx8='\n'.join(L[max(0, ln - 9):ln + 1]), fpos=sum(len(z) + 1 for z in L[:ln - 1]) + m.start())
            hit = None
            for name, cls, fn in RULES:
                d = fn(x)
                if d:
                    hit = (cls, name, d)
                    break
        else:
            hit = None
        if not hit:
            hit = ('UNTRIAGED', '-', 'numeral not read: %s' % (t[:120] if n < len(ms) else 'not found on its line'))
        stats[(hit[0], hit[1])] += 1
        seen = re.sub(r'\s+', ' ', (x.get('before', '')[-50:] + '@' + x.get('after', '')[:30]).replace('\t', ' '))
        out.append([hit[0], hit[1], r[0], k, r[3], r[8], r[9], re.sub(r'\s+', ' ', hit[2]).strip(), seen.strip()])
    with open(a.out, 'w') as fo:
        fo.write('\t'.join(['class', 'rule', 'status', 'key', 'where', 'value', 'roundconst class', 'fact',
                            'text read (@ = the numeral)']) + '\n')
        for o in out:
            fo.write('\t'.join(o) + '\n')
    print('# rows read %d (MISMATCH / MIXED / NO-COUNTERPART)' % len(out), file=sys.stderr)
    for (c, n), m in sorted(stats.items()):
        print('%-10s %-16s %6d' % (c, n, m), file=sys.stderr)
    bad = sum(m for (c, n), m in stats.items() if c in ('UNTRIAGED', 'DEFECT'))
    print('# UNTRIAGED %d, DEFECT %d' % (stats_sum(stats, 'UNTRIAGED'), stats_sum(stats, 'DEFECT')), file=sys.stderr)
    sys.exit(1 if bad else 0)


def stats_sum(stats, c):
    return sum(m for (cc, n), m in stats.items() if cc == c)


if __name__ == '__main__':
    main()
