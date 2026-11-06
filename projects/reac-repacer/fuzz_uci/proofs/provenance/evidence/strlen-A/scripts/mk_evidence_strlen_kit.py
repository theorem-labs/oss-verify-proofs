#!/usr/bin/env python3
"""mk_evidence_strlen_kit.py OUTDIR -- builds the evidence slice OUTDIR = provenance/evidence/strlen-A: fuzz_uci image A's
strlen and memchr chains against fuzz_identity image A's (the released donor), with the comparison kit of record, cmpkit
4bbd3a74be89. It writes OUTDIR/tables/, copies itself to OUTDIR/scripts/, and writes OUTDIR/MANIFEST.md. No host path,
machine name or date is written: an image is named by its file name and sha256. The measurement of targets the kit leaves
unsettled is the one of provenance/evidence/memchr-A/scripts/mk_evidence_memchr_kit.py (class Measure, unchanged).

Inputs, all from the environment:
  UCI_A, UCI_PIN_A   fuzz_uci.asan: the unstripped twin, and the pinned image (projects/reac-repacer/fuzz_uci/harness.yaml)
  ID_A, ID_PIN_A     fuzz_identity.asan: the unstripped twin, and the pinned image (projects/libreac/fuzz_identity/harness.yaml)
  KIT      a directory holding the kit's SHA256SUMS and the seven files it names (commit 3c3e62ee278,
           tools/cmpkit/4bbd3a74be89/). sha256(SHA256SUMS) must start with 4bbd3a74be89 and each file must match its line,
           else the run stops. The seven files are copied into one temporary directory that holds only them, and run there.
  PYTHONPATH   a pyelftools install
usage: mk_evidence_strlen_kit.py EVIDENCE_DIR/strlen-A

Tables (tables/), each the kit's output with image paths replaced by image names:
  twins.txt    drvcmp.py twins: each pinned (stripped) image = its unstripped twin, PT_LOAD bytes
  chain.tsv    strictcmp2.py cmp: the eight chain functions, fuzz_uci (U) : fuzz_identity (R)
  closure.txt  closure_strict2.py U R ___interceptor_strlen,___interceptor_memchr
  jtcheck.tsv  jtcheck.py U R over the 11 table members of the earlier record and every member closure.txt reports
  control.txt  five planted FILE copies of R, each with one 4-byte word changed, run as U : Pn:
               P1 one instruction word of ___interceptor_strlen; P2 its jal to AsanInited re-pointed to the sibling
               trampoline __interceptor_trampoline_strnlen; P3 one instruction word of musl memchr; P4 one instruction word
               of __asan_region_is_poisoned (a closure member only); P5 entry 1 of sysconf's jump table + 4
and this builder's own measurement of the targets jtcheck leaves unsettled (not kit outputs; a reviewer audits them):
  acceptances.tsv  one row per such target: the kit's verdict and the settled verdict side by side. Settled by measurement:
               a C string (its address passed on as a call argument or a return value on every path that uses it) equal
               through its NUL; an unnamed table equal entry by entry over every index its bound allows (a jump table as
               function+offset, a relative pointer table as symbol+offset or, for an unnamed target, as a C string through
               its NUL, a value table over the bytes the index can reach), the bounding instructions named. Anything else is
               'not certified'; bytes the code reads that differ are 'REAL'.
  members.tsv  every member closure.txt reports: the kit's verdict, the roots that reach it, jtcheck, the settled verdict
"""
import ast, hashlib, importlib.util, os, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
KIT_ID, KIT_COMMIT = '4bbd3a74be89', '3c3e62ee278'
DONOR = 'fuzz_identity, recipes 70952e1c8c9'
FNS = ['__interceptor_trampoline_strlen', '___interceptor_strlen', 'strlen', '_ZN11__sanitizer15internal_strlenEPKc',
       '__interceptor_trampoline_memchr', '___interceptor_memchr', 'memchr', '_ZN11__sanitizer15internal_memchrEPKvim']
ROOTS = ['___interceptor_strlen', '___interceptor_memchr']
JT_OLD = ['_ZN6__asan12ErrorGenericC1Ejmmmmbm', '_ZN6__asan9Decorator10ShadowByteEh', '_ZN6__asan16ErrorDescription5PrintEv',
          '_ZN11__sanitizer19GetHandleSignalModeEi', '_ZNK11__sanitizer13SignalContext8DescribeEv',
          '_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE20parseFDEInstructionsERS1_RKNS2_8FDE_InfoERKNS2_8CIE_InfoEmiPNS2_10PrologInfoE',
          '_ZN9libunwind17LocalAddressSpace11getEncodedPERmmhm', '_ZN9libunwind14EHHeaderParserINS_17LocalAddressSpaceEE17getTableEntrySizeEh',
          'sysconf', '__synccall', '__strftime_fmt_1']
# planted copies of R: (tag, function, word offset, kind, expected word or jal target, new word or jal target)
PLANTS = [('P1', '___interceptor_strlen', 0x48, 'word', 0x00090513, 0x00048513),
          ('P2', '___interceptor_strlen', 0x30, 'jal', '_ZN6__asan10AsanInitedEv', '__interceptor_trampoline_strnlen'),
          ('P3', 'memchr', 0x18, 'word', 0x00100813, 0x00200813),
          ('P4', '__asan_region_is_poisoned', 0x0, 'word', 0xfc010113, 0xfc810113),
          ('P5', 'sysconf', 0xdc, 'table', 1, 4)]
SETTLED_CLASSES = ('empty string', 'C string with non-printable bytes', 'C string', 'unnamed table')
PRINTABLE = frozenset(range(32, 127)) | {9, 10, 13}
ARGS = set(range(10, 18))
REGN = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1'] + ['a%d' % i for i in range(8)] + \
       ['s%d' % i for i in range(2, 12)] + ['t3', 't4', 't5', 't6']
LEAK = re.compile(r'(?<![\w.-])/(home|mnt|tmp|root|var|srv|opt|nix|Users)/')


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def sx(v, b):
    v &= (1 << b) - 1
    return v - (1 << b) if v >> (b - 1) & 1 else v


def jimm(x):
    return sx(((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11 | ((x >> 21) & 0x3ff) << 1, 21)


def bimm(x):
    return sx(((x >> 31) & 1) << 12 | ((x >> 7) & 1) << 11 | ((x >> 25) & 0x3f) << 5 | ((x >> 8) & 0xf) << 1, 13)


def jal_word(rd, imm):
    if not (-(1 << 20) <= imm < (1 << 20) and imm % 2 == 0):
        raise SystemExit('mk_evidence_strlen_kit: jal offset %#x out of range' % imm)
    i = imm & 0x1fffff
    return ((i >> 20) & 1) << 31 | ((i >> 1) & 0x3ff) << 21 | ((i >> 11) & 1) << 20 | ((i >> 12) & 0xff) << 12 | rd << 7 | 0x6f


def kit_copy(kit, tmp):
    """check the kit against its SHA256SUMS (whose sha256 is the kit id) and copy exactly its files into tmp"""
    sums = os.path.join(kit, 'SHA256SUMS')
    h = sha(sums)
    if not h.startswith(KIT_ID):
        raise SystemExit('mk_evidence_strlen_kit: SHA256SUMS hashes to %s, not the kit %s' % (h[:12], KIT_ID))
    names = []
    for line in open(sums):
        want, name = line.split()
        if sha(os.path.join(kit, name)) != want:
            raise SystemExit('mk_evidence_strlen_kit: kit file %s does not match SHA256SUMS' % name)
        shutil.copy(os.path.join(kit, name), os.path.join(tmp, name))
        names.append(name)
    if len(names) != 7 or sorted(os.listdir(tmp)) != sorted(names):
        raise SystemExit('mk_evidence_strlen_kit: the kit directory must hold exactly the seven files of SHA256SUMS')
    return h


def plants(rpath, pdir, K):
    """the five planted FILE copies of R (PLANTS); K = the kit's strictcmp2 module (P5 finds the table by the kit's targets)"""
    from elftools.elf.elffile import ELFFile
    e = ELFFile(open(rpath, 'rb'))
    want = {p[1] for p in PLANTS} | {p[4] for p in PLANTS if p[3] == 'jal'} | {p[5] for p in PLANTS if p[3] == 'jal'}
    sym = {}
    for s in e.get_section_by_name('.symtab').iter_symbols():
        if s.name in want and s['st_info']['type'] == 'STT_FUNC' and s['st_size'] > 0:
            sym.setdefault(s.name, set()).add(s['st_value'])
    if any(len(sym.get(n, ())) != 1 for n in want):
        raise SystemExit('mk_evidence_strlen_kit: plant symbols absent or not unique in the donor')
    sym = {n: v.pop() for n, v in sym.items()}

    def foff(a):
        return [g['p_offset'] + a - g['p_vaddr'] for g in e.iter_segments()
                if g['p_type'] == 'PT_LOAD' and g['p_vaddr'] <= a and a + 4 <= g['p_vaddr'] + g['p_filesz']][0]
    raw = open(rpath, 'rb').read(); out = []
    for tag, fn, off, kind, a, b in PLANTS:
        pc = sym[fn] + off; buf = bytearray(raw)
        if kind == 'table':
            img = K.Img(rpath); fa, fz = img.fsym(fn); fb = K.frd(img, fa, fz)
            w = K.bc_words(fb); t = K._g['targets'](fa, fb)
            i = next((j for j, (o, x, n) in enumerate(w) if o == off), None)
            if i is None or i not in t:
                raise SystemExit('mk_evidence_strlen_kit: %s+%#x addresses no table' % (fn, off))
            at = t[i][1] + 4 * a
            o = foff(at); v0 = int.from_bytes(buf[o:o + 4], 'little', signed=True)
            buf[o:o + 4] = (v0 + b).to_bytes(4, 'little', signed=True)
            what = '%s jump-table entry %d at %#x: %s -> %s' % (fn, a, at, (v0 & 0xffffffff).to_bytes(4, 'big').hex(),
                                                              ((v0 + b) & 0xffffffff).to_bytes(4, 'big').hex())
        else:
            o = foff(pc); x = int.from_bytes(buf[o:o + 4], 'little')
            if kind == 'word':
                if x != a:
                    raise SystemExit('mk_evidence_strlen_kit: %s+%#x holds %08x, not %08x' % (fn, off, x, a))
                buf[o:o + 4] = b.to_bytes(4, 'little'); what = '%s+%#x %08x -> %08x' % (fn, off, a, b)
            else:
                if x & 0x7f != 0x6f or pc + jimm(x) != sym[a]:
                    raise SystemExit('mk_evidence_strlen_kit: %s+%#x is not a jal to %s' % (fn, off, a))
                y = jal_word((x >> 7) & 31, sym[b] - pc)
                buf[o:o + 4] = y.to_bytes(4, 'little'); what = '%s+%#x jal %s -> jal %s, %08x -> %08x' % (fn, off, a, b, x, y)
        p = os.path.join(pdir, tag.lower() + '.elf'); open(p, 'wb').write(buf)
        out.append((tag, p, '%s(fuzz_identity copy, %s)' % (tag, what)))
    return out


# ---- parsers of the kit's tables -------------------------------------------------------------------------------------

def chain_rows(t, pair):
    """{fn: (verdict label, line number, line)} for one pair: verdict, plus 'target-differ N' when targets differ"""
    out = {}
    for n, l in enumerate(t.splitlines(), 1):
        f = l.split('\t')
        if l.startswith(('#', 'fn\t', 'CSTR')) or len(f) < 7 or f[1] != pair:
            continue
        td = f[11] if len(f) > 11 else '0'
        k = 0 if td in ('', '0') else len(ast.literal_eval(td)) if td.startswith('[') else int(td)
        out[f[0]] = (f[6] if k == 0 else '%s target-differ %d' % (f[6], k), n, l)
    return out


def chain_diffs(line):
    f = line.split('\t')
    return ast.literal_eval(f[11]) if len(f) > 11 and f[11].startswith('[') else []


CL_SUM = re.compile(r'^(\S+)\tclosure (\d+) functions \(register-indirect call sites inside: (\d+)\)\tEQUAL (\d+)'
                    r'\tEQUAL-mod-pcrel\(all targets equal\) (\d+)\tother (\d+)')


def closure_parse(t):
    """{root: (counts (functions, indirect sites, EQUAL, EQUAL-mod-pcrel, other), {X address: (name, verdict, line no, line)})}"""
    out = {}; cur = None
    for n, l in enumerate(t.splitlines(), 1):
        m = CL_SUM.match(l)
        if m:
            cur = m.group(1); out[cur] = (tuple(int(m.group(k)) for k in range(2, 7)), {}); continue
        m = re.match(r'^   (?!ACCEPT )(\S+) @(0x[0-9a-f]+): (.*)$', l)
        if m and cur is not None:
            rest = m.group(3); k = rest.find(' [')
            out[cur][1][int(m.group(2), 16)] = (m.group(1), (rest[:k] if k >= 0 else rest).strip(), n, l)
    return out


def jt_parse(t):
    """{fn: {line, n, settled, label, det: [(DIFF|UNMEASURED|UNPAIRED, word offset, text, line no)]}}"""
    out = {}; cur = None
    for n, l in enumerate(t.splitlines(), 1):
        if not l.strip() or l.startswith('CSTR'):
            continue
        if not l.startswith(' '):
            f = l.split('\t'); cur = f[0]
            if len(f) >= 9 and f[4].startswith('target differs '):
                td, um, up = (int(f[k].rsplit(' ', 1)[1]) for k in (4, 5, 6))
                ok = td == um == up == 0
                lab = 'settled' if ok else 'not settled: target differs %d, target unmeasured %d, unpaired %d' % (td, um, up)
            else:
                ok = False; lab = 'not settled: ' + ' '.join(f[1:])
            out[cur] = dict(line=l, n=n, settled=ok, label=lab, tables=f[-1] if ok else '', det=[])
        elif cur is not None:
            m = re.match(r'   (DIFF|UNMEASURED|UNPAIRED) \+(0x[0-9a-f]+) (.*)', l)
            if m:
                out[cur]['det'].append((m.group(1), int(m.group(2), 16), m.group(3), n))
    return out


# ---- measurement of a target the kit leaves unsettled (memchr-A's builder, unchanged) --------------------------------

class Measure:
    """reads both images with the kit's own Img / frd / region / targets / qres (strictcmp2.py from the kit directory)"""

    def __init__(self, kitdir, xpath, ypath):
        spec = importlib.util.spec_from_file_location('strictcmp2_kit', os.path.join(kitdir, 'strictcmp2.py'))
        K = importlib.util.module_from_spec(spec); spec.loader.exec_module(K)
        self.K, self.X, self.Y = K, K.Img(xpath), K.Img(ypath)
        self.writes, self.cs = set(K._bc['WRITES_RD']), set(K._bc['CALLER_SAVED'])

    def fsym(self, I, spec):
        nm = spec.split('{')[0]
        c = sorted({(v, z) for v, z, t in I.byname.get(nm, []) if t == 'STT_FUNC' and z > 0})
        if '{' in spec:
            c = [(v, z) for v, z in c if self.K.qname(I, nm, v) == spec]
        return c[0] if len(c) == 1 else None

    def cstr(self, I, a):
        """the bytes at a through the first NUL inside a's region (any byte values), or None"""
        d = self.K.region(I, a)
        k = d.find(b'\0') if d else -1
        return d[:k + 1] if k >= 0 else None

    def consumer(self, w, i):
        """how the address formed by the word at i is used, on every path from it (both ways at a conditional branch,
        in-function `j` followed, 8-byte stack spills and reloads followed): ('index', k, rd, index reg, base regs, path)
        at the first add of it and an index register; ('arg', how) when every path passes it on as a call argument or a
        return value or drops it unused, and one passes it on; else ('none', why)"""
        pos = {o: j for j, (o, x, n) in enumerate(w)}
        start = (i + 1, frozenset({(w[i][1] >> 7) & 31}))
        work = [start]; parent = {start: None}; seen = set(); args = set(); nones = set()

        def push(st, frm):
            parent.setdefault(st, frm); work.append(st)
        while work:
            st = work.pop()
            if st in seen:
                continue
            seen.add(st); k, regs = st
            if len(seen) > 50000:
                nones.add('walk stopped at 50000 states'); continue
            if k >= len(w):
                if not (w[-1][2] == 4 and w[-1][1] & 0x7f == 0x6f and (w[-1][1] >> 7) & 31 == 1):
                    nones.add('walk ran past the function end')
                continue                     # after a call that does not return: the value is dead
            o, x, n = w[k]
            if n != 4:
                nones.add('2-byte parcel at +%#x' % o); continue
            op, rd, f3, r1, r2 = x & 0x7f, (x >> 7) & 31, (x >> 12) & 7, (x >> 15) & 31, (x >> 20) & 31
            an = '/'.join(REGN[r] for r in sorted(regs & ARGS))
            nxt = k + 1
            if op == 0x33 and f3 == 0 and x >> 25 == 0 and (r1 in regs) != (r2 in regs):
                path = []; s = st
                while s is not None:
                    path.append(s[0]); s = parent[s]
                return ('index', k, rd, r2 if r1 in regs else r1, set(r for r in regs if isinstance(r, int)), path[::-1])
            if op == 0x03 and f3 == 3 and r1 == 2 and ('sp', sx(x >> 20, 12)) in regs and rd:
                push((nxt, regs | {rd}), st); continue
            if op in (0x03, 0x07) and r1 in regs:
                nones.add('loaded through at +%#x' % o); continue
            if op == 0x23 and r1 == 2:
                slot = ('sp', sx(((x >> 25) << 5) | ((x >> 7) & 31), 12))
                if r2 in regs and f3 == 3:
                    push((nxt, regs | {slot}), st); continue
                if slot in regs and r2 not in regs:
                    regs = regs - {slot}
                    if not regs:
                        continue
            if op in (0x23, 0x27) and r2 in regs:
                nones.add('stored to memory at +%#x' % o); continue
            if op in (0x6f, 0x67) and rd == 1:
                if regs & ARGS:
                    args.add('passed in %s to the call at +%#x' % (an, o)); continue
                if regs - self.cs:
                    push((nxt, regs - self.cs), st)
                continue
            if op == 0x6f:
                t = o + jimm(x)
                if t in pos:
                    push((pos[t], regs), st)
                elif regs & ARGS:
                    args.add('passed in %s to the tail call at +%#x' % (an, o))
                else:
                    nones.add('tail jump at +%#x' % o)
                continue
            if op == 0x67:
                if r1 == 1 and regs & {10, 11}:
                    args.add('returned in %s at +%#x' % ('/'.join(REGN[r] for r in sorted(regs & {10, 11})), o))
                elif r1 != 1:
                    nones.add('indirect jump at +%#x' % o)
                continue
            if op == 0x63:
                if o + bimm(x) in pos:
                    push((pos[o + bimm(x)], regs), st)
                push((nxt, regs), st); continue
            if op == 0x13 and f3 == 0 and x >> 20 == 0 and r1 in regs and rd:
                push((nxt, regs | {rd}), st); continue
            if rd in regs and op in self.writes:
                if regs - {rd}:
                    push((nxt, regs - {rd}), st)
                continue
            push((nxt, regs), st)
        if nones:
            return ('none', '; '.join(sorted(nones)))
        if args:
            a = sorted(args)
            return ('arg', 'its address is %s%s' % ('; '.join(a[:3]), ' (+%d more)' % (len(a) - 3) if len(a) > 3 else ''))
        return ('none', 'never used')

    def const(self, w, j, r):
        """the value `addi r, zero, K` gives r, scanning back from word j (None if r is written otherwise first)"""
        for q in range(j - 1, max(-1, j - 64), -1):
            o, x, n = w[q]
            if n != 4:
                return None
            if (x >> 7) & 31 == r and x & 0x7f in self.writes:
                return (sx(x >> 20, 12), o) if x & 0x7f == 0x13 and (x >> 12) & 7 == 0 and (x >> 15) & 31 == 0 else None
        return None

    def bound(self, w, i, path, ri):
        """the number of index values and the byte stride: back from the add along the path, then linearly before the
        table word: slli (stride), srli s (2^(64-s) values), andi m (m+1 values), or a branch bltu rK, ri (K+1) /
        bgeu ri, rK (K) with `addi rK, zero, K` before it. -> (count, stride, evidence) or None"""
        cur, stride, ev = ri, 1, []
        for j in list(reversed(path))[1:] + list(range(i, max(-1, i - 24), -1)):
            o, x, n = w[j]
            if n != 4:
                return None
            op, rd, f3, r1, r2 = x & 0x7f, (x >> 7) & 31, (x >> 12) & 7, (x >> 15) & 31, (x >> 20) & 31
            if op == 0x63 and f3 in (6, 7) and (r2 if f3 == 6 else r1) == cur:
                rk = r1 if f3 == 6 else r2
                c = self.const(w, j, rk)
                if c is None:
                    return None
                ev += ['addi %s,zero,%d @+%#x' % (REGN[rk], c[0], c[1]),
                       '%s %s,%s @+%#x' % ('bltu' if f3 == 6 else 'bgeu', REGN[r1], REGN[r2], o)]
                return (c[0] + 1 if f3 == 6 else c[0]), stride, ev
            if rd != cur or op not in self.writes:
                continue
            if op == 0x13 and f3 == 1:
                stride <<= (x >> 20) & 63; cur = r1; ev.append('slli %s,%s,%d @+%#x' % (REGN[rd], REGN[r1], (x >> 20) & 63, o)); continue
            if op == 0x13 and f3 == 5 and x >> 26 == 0:
                s = (x >> 20) & 63
                return 1 << (64 - s), stride, ev + ['srli %s,%s,%d @+%#x' % (REGN[rd], REGN[r1], s, o)]
            if op == 0x13 and f3 == 7 and sx(x >> 20, 12) >= 0:
                return sx(x >> 20, 12) + 1, stride, ev + ['andi %s,%s,%d @+%#x' % (REGN[rd], REGN[r1], sx(x >> 20, 12), o)]
            return None
        return None

    def element(self, w, k, rd, base):
        """after the add at k: (load width, entries added back to the table base, the sum jumped to)"""
        cur = rd; width = None; rel = False
        for j in range(k + 1, min(len(w), k + 6)):
            o, x, n = w[j]
            if n != 4:
                break
            op, d, f3, r1, r2 = x & 0x7f, (x >> 7) & 31, (x >> 12) & 7, (x >> 15) & 31, (x >> 20) & 31
            if width is None:
                if op == 0x03 and r1 == cur and sx(x >> 20, 12) == 0 and f3 in (0, 1, 2, 3, 4, 5, 6):
                    width = {0: 1, 1: 2, 2: 4, 3: 8, 4: 1, 5: 2, 6: 4}[f3]; cur = d
                continue
            if op in (0x33, 0x3b) and f3 == 0 and x >> 25 == 0 and ((r1 == cur and r2 in base) or (r2 == cur and r1 in base)):
                rel = True; cur = d; continue
            if op == 0x67 and d == 0:
                return width, rel, r1 == cur
            if d == cur and op in self.writes:
                break
        return width, rel, False

    def target(self, fn, off):
        """-> (class, detail): the measured class of the target of the word at fn+off (X = U, Y = R)"""
        K, X, Y = self.K, self.X, self.Y
        fx, fy = self.fsym(X, fn), self.fsym(Y, fn)
        if not fx or not fy or fx[1] != fy[1]:
            return 'not certified', 'function not found once in both images'
        bx, by = K.frd(X, *fx), K.frd(Y, *fy)
        w = K.bc_words(bx); tx, ty = K._g['targets'](fx[0], bx), K._g['targets'](fy[0], by)
        i = next((j for j, (o, x, n) in enumerate(w) if o == off), None)
        if i is None or i not in tx or i not in ty:
            return 'not certified', 'no target pair at +%#x' % off
        x, y = tx[i][1], ty[i][1]
        if K.loadwidth(w[i][1]):
            return 'REAL', 'a load of %d bytes reads different bytes at %#x | %#x' % (K.loadwidth(w[i][1]), x, y)
        sa, sb = self.cstr(X, x), self.cstr(Y, y)
        use = self.consumer(w, i)
        if use[0] == 'arg':
            if sa is None or sb is None:
                return 'not certified', '%s; no NUL in its region' % use[1]
            if sa != sb:
                return 'REAL', 'C strings differ: %r | %r (%s)' % (sa, sb, use[1])
            sub = 'empty string' if len(sa) == 1 else 'C string with non-printable bytes' \
                if any(c not in PRINTABLE for c in sa[:-1]) else 'C string'
            return sub, '%r equal through its NUL at %#x | %#x; %s' % (sa, x, y, use[1])
        if use[0] != 'index':
            fact = 'bytes through the NUL %s (%r)' % ('equal' if sa is not None and sa == sb else 'NOT equal', sa) \
                if sa is not None else 'no NUL in its region'
            return 'not certified', 'consumer not followed: %s; %s at %#x | %#x' % (use[1], fact, x, y)
        _, k, rd, ri, base, path = use
        bd = self.bound(w, i, path, ri)
        width, rel, jump = self.element(w, k, rd, base)
        if bd is None or width is None:
            return 'not certified', 'indexed at +%#x; %s' % (w[k][0], 'no index bound found' if bd is None else 'no element load found')
        cnt, stride, ev = bd
        evs = ', '.join(ev)
        if not rel:
            ext = (cnt - 1) * stride + width
            da, db = K.frd(X, x, ext), K.frd(Y, y, ext)
            if da is None or da != db:
                return 'REAL', 'table of %d entries x %d bytes differs within %d bytes at %#x | %#x (%s)' % (cnt, width, ext, x, y, evs)
            return 'unnamed table', 'value table, %d entries of %d bytes (stride %d): the %d bytes its index can reach are ' \
                'equal at %#x | %#x; bound %s' % (cnt, width, stride, ext, x, y, evs)
        ents = []
        for q in range(cnt):
            ea, eb = K.frd(X, x + q * stride, width), K.frd(Y, y + q * stride, width)
            if ea is None or eb is None:
                return 'REAL', 'relative table entry %d not file bytes' % q
            ents.append((x + int.from_bytes(ea, 'little', signed=True), y + int.from_bytes(eb, 'little', signed=True)))
        if jump:
            bad = [q for q, (va, vb) in enumerate(ents) if not (fx[0] <= va < fx[0] + fx[1]) or va - fx[0] != vb - fy[0]]
            if bad:
                return 'REAL', 'jump table entries %s differ as function+offset' % bad[:6]
            return 'unnamed table', 'relative jump table, %d entries: every entry the same function+offset (%d distinct ' \
                'cases) at %#x | %#x; bound %s' % (cnt, len({va - fx[0] for va, vb in ents}), x, y, evs)
        got = []
        for q, (va, vb) in enumerate(ents):
            qa, qb = K.qres(X, va), K.qres(Y, vb)
            if qa and not qa.startswith('(') or qb and not qb.startswith('('):
                if qa != qb:
                    return 'REAL', 'relative table entry %d names %s | %s' % (q, qa, qb)
                got.append(qa); continue
            ca, cb = self.cstr(X, va), self.cstr(Y, vb)
            if ca is None or ca != cb:
                return 'REAL', 'relative table entry %d: unnamed targets differ through their NUL' % q
            got.append(repr(ca))
        return 'unnamed table', 'relative pointer table, %d entries, each the same symbol+offset or (unnamed) the same C string ' \
            'through its NUL (%s) at %#x | %#x; bound %s' % (cnt, ', '.join(got), x, y, evs)


# ---- the run ---------------------------------------------------------------------------------------------------------

def main():
    if len(sys.argv) != 2:
        raise SystemExit('usage: mk_evidence_strlen_kit.py OUTDIR')
    out = os.path.abspath(sys.argv[1])
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    sys.dont_write_bytecode = True
    uci, rid, upin, rpin = env['UCI_A'], env['ID_A'], env['UCI_PIN_A'], env['ID_PIN_A']
    kitdir = tempfile.mkdtemp(prefix='mkkit-'); pdir = tempfile.mkdtemp(prefix='mkkitp-')
    try:
        kit_sha = kit_copy(env['KIT'], kitdir)
        M = Measure(kitdir, uci, rid)
        pl = plants(rid, pdir, M.K)
        names = {uci: 'fuzz_uci.asan(unstripped, sha256 %s)' % sha(uci)[:12],
                 rid: 'fuzz_identity.asan(unstripped, sha256 %s)' % sha(rid)[:12],
                 upin: 'fuzz_uci.asan(pin, sha256 %s)' % sha(upin)[:12],
                 rpin: 'fuzz_identity.asan(pin, sha256 %s)' % sha(rpin)[:12],
                 kitdir + '/': '', pdir + '/': ''}
        names.update({p: d for t, p, d in pl})
        P = {t: p for t, p, d in pl}
        keys = sorted(names, key=len, reverse=True)

        def run(args):
            r = subprocess.run([sys.executable] + args, cwd=kitdir, capture_output=True, text=True, env=env)
            t = r.stdout + r.stderr
            for k in keys:
                t = t.replace(k, names[k])
            if r.returncode:
                raise SystemExit('mk_evidence_strlen_kit: %s failed:\n%s' % (args[0], t))
            return t

        roots = ','.join(ROOTS)
        tabs = {'twins.txt': run(['drvcmp.py', 'twins', upin, uci, rpin, rid]),
                'chain.tsv': run(['strictcmp2.py', 'cmp', ','.join(FNS), 'U=' + uci, 'R=' + rid, 'U:R']),
                'closure.txt': run(['closure_strict2.py', uci, rid, roots])}
        ncl = closure_parse(tabs['closure.txt'])
        if sorted(ncl) != sorted(ROOTS):
            raise SystemExit('mk_evidence_strlen_kit: closure.txt has roots %s' % sorted(ncl))
        rep = {}            # X address -> (name, kit verdict, {root: line no})
        for r in ROOTS:
            for a, (nm, vv, ln, l) in ncl[r][1].items():
                rep.setdefault(a, (nm, vv, {}))[2][r] = ln
        members = JT_OLD + sorted({nm for nm, vv, rl in rep.values()} - set(JT_OLD))
        tabs['jtcheck.tsv'] = run(['jtcheck.py', uci, rid, ','.join(members)])
        ctl = [('strictcmp2.py cmp, the eight chain functions, U : P1, U : P2, U : P3',
                run(['strictcmp2.py', 'cmp', ','.join(FNS), 'U=' + uci, 'P1=' + P['P1'], 'P2=' + P['P2'], 'P3=' + P['P3'],
                     'U:P1,U:P2,U:P3'])),
               ('closure_strict2.py U P1 ' + roots, run(['closure_strict2.py', uci, P['P1'], roots])),
               ('closure_strict2.py U P4 ' + roots, run(['closure_strict2.py', uci, P['P4'], roots])),
               ('jtcheck.py U P5 sysconf', run(['jtcheck.py', uci, P['P5'], 'sysconf']))]
        tabs['control.txt'] = ''.join('== %s\n%s' % (h, t if t.endswith('\n') else t + '\n') for h, t in ctl)

        # ---- settle what the kit leaves unsettled, by measurement
        njt = jt_parse(tabs['jtcheck.tsv'])
        acc = {}           # (fn, off) -> (kit verdict, jtcheck line no, class, detail)

        def settle(fn):
            """(settled verdict, detail) of a reported closure member: the kit's jtcheck, else each target it leaves
            unsettled, measured"""
            j = njt.get(fn)
            if j is None:
                return 'not certified', 'not in jtcheck.tsv'
            if j['settled']:
                return 'settled by the kit (jtcheck)', 'jtcheck.tsv:%d %s' % (j['n'], j['tables'])
            if not j['det']:
                return 'not certified', 'jtcheck.tsv:%d %s' % (j['n'], j['label'])
            got = []
            for kind, off, text, ln in j['det']:
                if kind == 'UNPAIRED':
                    acc[(fn, off)] = ('UNPAIRED ' + text, ln, 'not certified', 'unpaired word (the kit pairs no auipc)')
                elif (fn, off) not in acc:
                    acc[(fn, off)] = ('%s %s' % (kind, text), ln) + M.target(fn, off)
                got.append(acc[(fn, off)][2])
            cls = sorted(set(got))
            if 'REAL' in cls:
                top = 'REAL'
            elif 'not certified' in cls:
                top = 'not certified'
            else:
                top = 'settled by measurement: ' + ' + '.join(cls)
            return top, '; '.join('+%#x %s' % (off, acc[(fn, off)][2]) for kind, off, text, ln in j['det'])

        ntw = tabs['twins.txt'].splitlines()
        tw_ok = len(ntw) == 2 and all('PT_LOAD layout equal: True' in l and l.endswith(': []') for l in ntw)
        nch = chain_rows(tabs['chain.tsv'], 'U:R')
        ch_ok = all(nch.get(f, ('ABSENT',))[0] in ('EQUAL', 'EQUAL-mod-pcrel') for f in FNS)
        mset = {}          # X address -> (name, kit verdict, {root: line}, settled verdict, detail)
        for a, (nm, vv, rl) in sorted(rep.items()):
            c, d = settle(nm) if not re.match(r'(DIFFERENT|SIZE|ABSENT|AMBIGUOUS|UNREADABLE)', vv) else \
                ('REAL', 'instruction words differ or no counterpart: ' + vv)
            mset[a] = (nm, vv, rl, c, d)

        # ---- the planted controls (each against the baseline U : R)
        cc = ctl[0][1]
        crow = {t: chain_rows(cc, 'U:' + t) for t in ('P1', 'P2', 'P3')}

        def others_same(t, fn):
            return all(crow[t].get(f, ('',))[0] == nch.get(f, ('ABSENT',))[0] for f in FNS if f != fn)
        p1_ok = crow['P1'].get('___interceptor_strlen', ('',))[0] == 'DIFFERENT' and others_same('P1', '___interceptor_strlen')
        p2l = crow['P2'].get('___interceptor_strlen', ('', 0, ''))
        p2_ok = p2l[0].startswith('EQUAL-mod-pcrel target-differ') and others_same('P2', '___interceptor_strlen') and \
            any(d[0] == '0x30' and d[3] == 'names' and d[2].startswith('__interceptor_trampoline_strnlen')
                for d in chain_diffs(p2l[2]))
        p3_ok = crow['P3'].get('memchr', ('',))[0] == 'DIFFERENT' and others_same('P3', 'memchr')

        def added(t, fn):
            c = closure_parse(t)
            ok = sorted(c) == sorted(ROOTS)
            for r in ROOTS:
                base = {a: v[0] for a, v in ncl[r][1].items()}
                got = {a: v[0] for a, v in c.get(r, ((), {}))[1].items()}
                extra = {a: got[a] for a in set(got) - set(base)}
                ok = ok and set(base) <= set(got) and list(extra.values()) == [fn] and \
                    c[r][1][next(iter(extra))][1] == 'DIFFERENT'
            return ok
        cl1_ok = added(ctl[1][1], '___interceptor_strlen')
        cl4_ok = added(ctl[2][1], '__asan_region_is_poisoned')
        j5 = jt_parse(ctl[3][1]).get('sysconf', {})
        jt5_ok = njt.get('sysconf', {}).get('settled') and 'target differs 1\t' in j5.get('line', '') and \
            any(kd == 'DIFF' and off == 0xdc for kd, off, tx, ln in j5.get('det', []))
        ctl_ok = {'P1': p1_ok and cl1_ok, 'P2': p2_ok, 'P3': p3_ok, 'P4': cl4_ok, 'P5': bool(jt5_ok)}
        caught = all(ctl_ok.values())

        # ---- write the tables
        tabs['acceptances.tsv'] = 'function\tword\tjtcheck line\tthe kit\'s verdict\tsettled verdict\tmeasurement\n' + ''.join(
            '%s\t+%#x\tjtcheck.tsv:%d\t%s\t%s\t%s\n' % (fn, off, ln, kv, c, d.replace('\t', ' '))
            for (fn, off), (kv, ln, c, d) in sorted(acc.items(), key=lambda e: (njt[e[0][0]]['n'], e[0][1])))
        tabs['members.tsv'] = 'function\tX address\treported under (closure.txt line)\tthe kit\'s verdict\tjtcheck\t' \
            'settled verdict\tdetail\n' + ''.join(
                '%s\t%#x\t%s\t%s\t%s\t%s\t%s\n' % (nm, a, ', '.join('%s (closure.txt:%d)' % (r, rl[r]) for r in ROOTS if r in rl),
                                                   vv, njt[nm]['label'] + ' (jtcheck.tsv:%d)' % njt[nm]['n'] if nm in njt else 'not run',
                                                   c, d.replace('\t', ' '))
                for a, (nm, vv, rl, c, d) in sorted(mset.items()))
        for k, t in tabs.items():
            bad = [p for p in names if p.rstrip('/') and p.rstrip('/') in t] + LEAK.findall(t)
            if bad:
                raise SystemExit('mk_evidence_strlen_kit: a host path is left in %s' % k)
        tdir = os.path.join(out, 'tables')
        os.makedirs(tdir, exist_ok=True)
        for k, t in tabs.items():
            open(os.path.join(tdir, k), 'w').write(t)
        os.makedirs(os.path.join(out, 'scripts'), exist_ok=True)
        if os.path.abspath(__file__) != os.path.join(out, 'scripts', 'mk_evidence_strlen_kit.py'):
            shutil.copy(os.path.abspath(__file__), os.path.join(out, 'scripts', 'mk_evidence_strlen_kit.py'))

        # ---- MANIFEST
        def md(s):
            return str(s).replace('|', '\\|')
        by_jt = sorted(a for a, v in mset.items() if v[3].startswith('settled by the kit'))
        by_ms = sorted(a for a, v in mset.items() if v[3].startswith('settled by measurement'))
        real = sorted(a for a, v in mset.items() if v[3] == 'REAL')
        notc = sorted(a for a, v in mset.items() if v[3] == 'not certified')
        cls_n = {}
        for kv, ln, c, d in acc.values():
            cls_n[c] = cls_n.get(c, 0) + 1
        certified = not real and not notc
        imgs = [('U', 'fuzz_uci.asan, unstripped twin', uci), ('R', 'fuzz_identity.asan, unstripped twin', rid),
                ('pin', 'fuzz_uci.asan, pinned image', upin), ('pin', 'fuzz_identity.asan, pinned image', rpin)] + \
            [(t, d, p) for t, p, d in pl]
        cnt = {r: ncl[r][0] for r in ROOTS}
        m = ['# provenance/evidence/strlen-A: fuzz_uci image A strlen and memchr chains = fuzz_identity\'s released ones '
             '(cmpkit %s)' % KIT_ID, '',
             'Written by scripts/mk_evidence_strlen_kit.py; not edited by hand. What a reader needs to re-derive why fuzz_uci\'s '
             'lib/A strlen and memchr walks may port fuzz_identity\'s released ones: the code of fuzz_uci image A\'s strlen and '
             'memchr chains equals the donor\'s up to relocation. Donor: %s (PR #399): '
             'proofs/libreac/fuzz_identity/lib/A/Rt/StrlenDef.v:36 `astrlen_realizes`, proved as '
             'proofs/libreac/fuzz_identity/lib/A/Rt/Strlen.v:26 `strlen_icpt_contract`; '
             'proofs/libreac/fuzz_identity/lib/A/Rt/MemchrDef.v:25 `amemchr_realizes`, proved as '
             'proofs/libreac/fuzz_identity/lib/A/Rt/Memchr.v:574 `memchr_icpt_contract`; the pinned image below is the one '
             'projects/libreac/fuzz_identity/harness.yaml pins at that commit. Tools cited, not shipped: the comparison kit '
             'of record, cmpkit %s (commit %s, tools/cmpkit/%s/; sha256 of its SHA256SUMS %s), its seven files run from one '
             'directory that holds only them. Each verdict is the kit\'s first; where the kit fails closed, the settled '
             'verdict follows it, from a named measurement of this builder (`tables/acceptances.tsv`), or "not certified". '
             'Generation logs are not here.' % (DONOR, KIT_ID, KIT_COMMIT, KIT_ID, kit_sha), '',
             'Images (file name, sha256):', '']
        m += ['- %s: %s, `%s`' % (t, d, sha(p)) for t, d, p in imgs]
        m += ['', '## Verdict', '',
              '- CLAIM: %s' % (
                  'the chain and the whole closures of %s equal the donor\'s up to relocation (kit verdicts, and the '
                  'acceptances below)' % ' and '.join('`%s`' % r for r in ROOTS) if certified and ch_ok and tw_ok else
                  'NARROWED to the chain: the eight chain functions (%s) equal the donor\'s up to relocation on the kit, every '
                  'target equal. The closures of %s are not certified as a whole: %d reported members are listed below as '
                  'not certified%s.' % (', '.join('`%s`' % f for f in FNS), ' and '.join('`%s`' % r for r in ROOTS),
                                        len(notc) + len(real), ' (%d with a REAL difference)' % len(real) if real else '')
                  if ch_ok and tw_ok else 'NOT MET: the chain or the twins check fails on the kit'),
              '- twins (each pin = its unstripped twin, PT_LOAD bytes; `tables/twins.txt`): %s'
              % ('equal outside the ELF header and build-id note' if tw_ok else 'NOT EQUAL'),
              '- chain, U : R (`tables/chain.tsv`), kit verdict (pc-relative words; real, unmeasured, target-differ):']
        for f in FNS:
            r = nch.get(f)
            if r is None:
                m.append('  - `%s`: ABSENT' % f); continue
            x = r[2].split('\t')
            m.append('  - `%s`: %s (%s; %s, %s, %s) `chain.tsv:%d`' % (f, r[0], x[7] or '0', x[8] or '0', x[9] or '0',
                                                                      x[11] if len(x) > 11 else '0', r[1]))
        acc_ch = []
        for f in FNS:
            x = nch[f][2].split('\t') if f in nch else []
            for col in x[12:14]:
                if col.strip():
                    acc_ch.append('`%s`: %s' % (f, md(col.strip())))
        m += ['- the kit\'s own acceptances inside the chain verdicts (value / full-bytes, and C-string; also the CSTR rows of '
              '`chain.tsv`): ' + ('; '.join(acc_ch) if acc_ch else 'none')]
        m += ['- closures (`tables/closure.txt`): ' + '; '.join(
            '`%s`: %d functions, EQUAL %d, EQUAL-mod-pcrel with all targets equal %d, reported %d'
            % (r, cnt[r][0], cnt[r][2], cnt[r][3], cnt[r][4]) for r in ROOTS) +
            '. The reported members, %d distinct functions over both roots (`tables/members.tsv`): settled by the kit\'s '
            'jtcheck %d; settled by measurement %d; not certified %d; REAL %d.'
            % (len(mset), len(by_jt), len(by_ms), len(notc), len(real)),
              '- jtcheck over %d functions, the 11 table members of the earlier record and every reported closure member '
              '(`tables/jtcheck.tsv`): kit: settled %d, not settled %d. Its %d unsettled targets, measured '
              '(`tables/acceptances.tsv`): %s.'
              % (len(njt), sum(1 for j in njt.values() if j['settled']), sum(1 for j in njt.values() if not j['settled']),
                 len(acc), ', '.join('%s %d' % (c, n) for c, n in sorted(cls_n.items()))),
              '- planted controls (`tables/control.txt`): %s' % ', '.join(
                  '%s %s' % (t, 'caught' if ctl_ok[t] else 'NOT CAUGHT') for t in ('P1', 'P2', 'P3', 'P4', 'P5')),
              '',
              'Settled verdicts (this builder\'s measurement on file bytes, read with the kit\'s Img / frd / region / qres; never a '
              'kit EQUAL): "empty string", "C string with non-printable bytes", "C string" = an unnamed target whose address '
              'every path that uses it passes on as a call argument or a return value, equal through its NUL in both images '
              '(the kit fails closed: its C-string rule needs printable bytes, and the region to the next symbol differs). '
              '"unnamed table" = an indexed unnamed .rodata table, equal entry by entry over every index its bound allows: a '
              'jump table as function+offset, a relative pointer table as symbol+offset (an unnamed entry target as a C string '
              'through its NUL), a value table over the bytes its index can reach; the bounding instructions are named in '
              '`tables/acceptances.tsv`. "not certified" = the measurement did not settle it (its consumer or bound was not '
              'followed). "REAL" = bytes the code reads differ.', '',
              '## Reported closure members (the kit\'s verdict, then the settled verdict)', '',
              '| function | X address | reported under | kit verdict | kit line | jtcheck | settled verdict |',
              '|---|---|---|---|---|---|---|']
        short = {'___interceptor_strlen': 'strlen', '___interceptor_memchr': 'memchr'}
        for a, (nm, vv, rl, c, d) in sorted(mset.items()):
            m.append('| `%s` | %#x | %s | %s | %s | %s | %s |' % (
                nm, a, ', '.join(short[r] for r in ROOTS if r in rl), md(vv),
                ', '.join('`closure.txt:%d`' % rl[r] for r in ROOTS if r in rl),
                md('%s (`jtcheck.tsv:%d`)' % (njt[nm]['label'], njt[nm]['n'])) if nm in njt else 'not run', md(c)))
        m += ['']
        if notc or real:
            m += ['## Not certified', '',
                  '| function | X address | kit verdict | unsettled targets (`tables/acceptances.tsv`) |', '|---|---|---|---|']
            m += ['| `%s` | %#x | %s | %s |' % (mset[a][0], a, md(mset[a][1]), md(mset[a][4])) for a in real + notc]
            m += ['']
        groups = {}
        for (fn, off), (kv, ln, c, d) in acc.items():
            if c in SETTLED_CLASSES:
                key = (c, re.sub(r'; (its address is|bound) .*$', '', d))
                groups.setdefault(key, []).append('%s+%#x' % (fn, off))
        m += ['## Acceptances (settled by measurement, not by the kit; a fresh reviewer audits them)', '',
              'Grouped by target and measured bytes; one row per use is in `tables/acceptances.tsv`, with the kit\'s verdict, '
              'and the consumer (the call or return that passes the address on) or the table bound of each use.', '',
              '| settled verdict | measurement | uses |', '|---|---|---|']
        m += ['| %s | %s | %d: %s |' % (md(c), md(d), len(u), md(', '.join('`%s`' % e for e in sorted(u)[:4]) +
                                                              (', ...' if len(u) > 4 else '')))
              for (c, d), u in sorted(groups.items(), key=lambda e: (e[0][0], -len(e[1])))]
        m += ['', '## Planted controls (`tables/control.txt`)', '',
              'Each a FILE copy of R with one 4-byte word changed, compared as U : Pn (the claim\'s pair with the donor planted); '
              'the expected report, and no other row changes against U : R.', '',
              '| plant | sha256 | expected report | caught |', '|---|---|---|---|']
        expect = {'P1': 'strictcmp2: `___interceptor_strlen` DIFFERENT; closure_strict2: `___interceptor_strlen` DIFFERENT under '
                        'both roots, nothing else added',
                  'P2': 'strictcmp2: `___interceptor_strlen` target-differ at +0x30, `names`, '
                        '`__interceptor_trampoline_strnlen`',
                  'P3': 'strictcmp2: `memchr` DIFFERENT',
                  'P4': 'closure_strict2: `__asan_region_is_poisoned` DIFFERENT under both roots, nothing else added',
                  'P5': 'jtcheck: `sysconf` target differs 1, DIFF +0xdc (settled against R)'}
        m += ['| %s | `%s` | %s | %s |' % (md(d), sha(p), expect[t], 'yes' if ctl_ok[t] else 'NO') for t, p, d in pl]
        m += ['', '## Files', '', '| file | kind | role |', '|---|---|---|',
              '| `scripts/env.example.sh` | config | every variable name the builder reads, without values |',
              '| `scripts/run.sh` | script | the run of record |',
              '| `scripts/mk_evidence_strlen_kit.py` | script | this builder: checks and copies the kit, runs it, measures, writes '
              'the tables and this file |',
              '| `tables/twins.txt` | table | drvcmp.py twins: each pin = its unstripped twin |',
              '| `tables/chain.tsv` | table | strictcmp2.py cmp: the eight chain functions, U : R |',
              '| `tables/closure.txt` | table | closure_strict2.py: the closures of `___interceptor_strlen` and '
              '`___interceptor_memchr`, U : R |',
              '| `tables/jtcheck.tsv` | table | jtcheck.py: the 11 table members of the earlier record and every reported '
              'closure member |',
              '| `tables/members.tsv` | table | every reported closure member: the kit\'s verdict next to the settled verdict |',
              '| `tables/acceptances.tsv` | table | each target jtcheck leaves unsettled: the kit\'s verdict, the settled verdict, '
              'the measurement |',
              '| `tables/control.txt` | table | the planted copies P1-P5, as U : Pn, under strictcmp2, closure_strict2, jtcheck |']
        text = '\n'.join(m) + '\n'
        if LEAK.findall(text) or any(p.rstrip('/') and p.rstrip('/') in text for p in names):
            raise SystemExit('mk_evidence_strlen_kit: a host path is left in MANIFEST.md')
        open(os.path.join(out, 'MANIFEST.md'), 'w').write(text)
    finally:
        shutil.rmtree(kitdir); shutil.rmtree(pdir)
    print('mk_evidence_strlen_kit: strlen-A: twins %s, chain %s, closure members %d: jtcheck %d, measurement %d, '
          'not certified %d, REAL %d; controls %s'
          % ('ok' if tw_ok else 'NOT EQUAL', 'settled' if ch_ok else 'NOT SETTLED', len(mset), len(by_jt), len(by_ms),
             len(notc), len(real), 'caught' if caught else 'NOT CAUGHT'))
    if not caught:
        raise SystemExit('mk_evidence_strlen_kit: a planted control was not caught, see %s' % out)


if __name__ == '__main__':
    main()
