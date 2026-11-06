#!/usr/bin/env python3
"""mk_evidence_memchr_kit.py IMAGE OUTDIR -- re-runs the comparisons of mk_evidence_memchr.py (bytecmp 7daa0e2a03d9 +
repin_check 9cbc3553c09e) with the comparison kit of record, cmpkit 4bbd3a74be89, for the evidence slice OUTDIR =
memchr-<IMAGE> (IMAGE = A or B). It writes OUTDIR/tables/cmpkit-4bbd3a74be89/ beside the old tables, copies itself to
OUTDIR/scripts/, and writes (or replaces) one section of OUTDIR/MANIFEST.md. The old tables are read, not changed. No host
path, machine name or date is written: an image is named by its file name and sha256.

Inputs, all from the environment:
  UCI_A, UCI_B, UCI_PIN_A, UCI_PIN_B, BOX_A, BOX_B, BOX_PIN_A, BOX_PIN_B   as for mk_evidence_memchr.py (scripts/env.example.sh)
  KIT      a directory holding the kit's SHA256SUMS and the seven files it names (commit 3c3e62ee278,
           tools/cmpkit/4bbd3a74be89/). sha256(SHA256SUMS) must start with 4bbd3a74be89 and each file must match its line,
           else the run stops. The seven files are copied into one temporary directory that holds only them, and run there.
  PYTHONPATH   a pyelftools install
usage: for i in A B; do python3 mk_evidence_memchr_kit.py $i EVIDENCE_DIR/memchr-$i; done

Tables, each the kit's output with image paths replaced by image names:
  twins.txt    drvcmp.py twins: each pinned (stripped) image = its unstripped twin, PT_LOAD bytes
  chain.tsv    strictcmp2.py cmp: the four chain functions, fuzz_uci (U) : fuzz_boxreg (R)
  closure.txt  closure_strict2.py U R ___interceptor_memchr
  jtcheck.tsv  jtcheck.py U R over the 11 table members of the old record and every member closure.txt reports
  control.txt  two planted copies of R: P1 changes one instruction word of ___interceptor_memchr (the old record's plant),
               P2 re-points its jal at +0x114 to the sibling trampoline __interceptor_trampoline_bcmp; each against R
               under strictcmp2.py cmp, closure_strict2.py and jtcheck.py
and this builder's own measurement of the targets jtcheck leaves unsettled (not kit outputs; a reviewer audits them):
  acceptances.tsv  one row per such target: the kit's verdict and the settled verdict side by side. Settled by measurement:
               a C string (its address passed on as a call argument or a return value on every path that uses it) equal
               through its NUL; an unnamed table equal entry by entry over every index its bound allows (a jump table as
               function+offset, a relative pointer table as symbol+offset or, for an unnamed target, as a C string through
               its NUL, a value table over the bytes the index can reach), the bounding instructions named. Anything else is
               'not certified'; bytes the code reads that differ are 'REAL'.
  changed.tsv  every verdict that differs from the old tables, the kit's line, and the settled verdict
"""
import ast, hashlib, importlib.util, os, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
KIT_ID, KIT_COMMIT = '4bbd3a74be89', '3c3e62ee278'
SUB = 'cmpkit-' + KIT_ID
FNS = ['__interceptor_trampoline_memchr', '___interceptor_memchr', 'memchr', '_ZN11__sanitizer15internal_memchrEPKvim']
ROOT = '___interceptor_memchr'
JT_OLD = ['_ZN6__asan12ErrorGenericC1Ejmmmmbm', '_ZN6__asan9Decorator10ShadowByteEh', '_ZN6__asan16ErrorDescription5PrintEv',
          '_ZN11__sanitizer19GetHandleSignalModeEi', '_ZNK11__sanitizer13SignalContext8DescribeEv',
          '_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE20parseFDEInstructionsERS1_RKNS2_8FDE_InfoERKNS2_8CIE_InfoEmiPNS2_10PrologInfoE',
          '_ZN9libunwind17LocalAddressSpace11getEncodedPERmmhm', '_ZN9libunwind14EHHeaderParserINS_17LocalAddressSpaceEE17getTableEntrySizeEh',
          'sysconf', '__synccall', '__strftime_fmt_1']
PLANT_FN, P1_OFF = '___interceptor_memchr', 0x10
P2_OFF, P2_FROM, P2_TO = 0x114, '_ZN11__sanitizer15internal_memchrEPKvim', '__interceptor_trampoline_bcmp'
SECTION = '## Re-run on the comparison kit cmpkit ' + KIT_ID
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
        raise SystemExit('mk_evidence_memchr_kit: jal offset %#x out of range' % imm)
    i = imm & 0x1fffff
    return ((i >> 20) & 1) << 31 | ((i >> 1) & 0x3ff) << 21 | ((i >> 11) & 1) << 20 | ((i >> 12) & 0xff) << 12 | rd << 7 | 0x6f


def kit_copy(kit, tmp):
    """check the kit against its SHA256SUMS (whose sha256 is the kit id) and copy exactly its files into tmp"""
    sums = os.path.join(kit, 'SHA256SUMS')
    h = sha(sums)
    if not h.startswith(KIT_ID):
        raise SystemExit('mk_evidence_memchr_kit: SHA256SUMS hashes to %s, not the kit %s' % (h[:12], KIT_ID))
    names = []
    for line in open(sums):
        want, name = line.split()
        if sha(os.path.join(kit, name)) != want:
            raise SystemExit('mk_evidence_memchr_kit: kit file %s does not match SHA256SUMS' % name)
        shutil.copy(os.path.join(kit, name), os.path.join(tmp, name))
        names.append(name)
    if len(names) != 7 or sorted(os.listdir(tmp)) != sorted(names):
        raise SystemExit('mk_evidence_memchr_kit: the kit directory must hold exactly the seven files of SHA256SUMS')
    return h


def plants(box, pdir):
    """P1: one non-pc-relative word of the donor's interceptor changed (bit 0 of its top byte, the old record's plant);
    P2: its jal to internal_memchr re-pointed to the sibling trampoline. Both FILE copies of the donor."""
    from elftools.elf.elffile import ELFFile
    e = ELFFile(open(box, 'rb'))
    sym = {}
    for s in e.get_section_by_name('.symtab').iter_symbols():
        if s.name in (PLANT_FN, P2_FROM, P2_TO) and s['st_info']['type'] == 'STT_FUNC':
            sym.setdefault(s.name, set()).add(s['st_value'])
    if any(len(sym.get(n, ())) != 1 for n in (PLANT_FN, P2_FROM, P2_TO)):
        raise SystemExit('mk_evidence_memchr_kit: plant symbols absent or not unique in the donor')
    sym = {n: v.pop() for n, v in sym.items()}

    def foff(a):
        return [g['p_offset'] + a - g['p_vaddr'] for g in e.iter_segments()
                if g['p_type'] == 'PT_LOAD' and g['p_vaddr'] <= a < g['p_vaddr'] + g['p_filesz']][0]
    raw = open(box, 'rb').read()
    o1 = foff(sym[PLANT_FN] + P1_OFF)
    b = bytearray(raw); w0 = b[o1:o1 + 4].hex(); b[o1 + 3] ^= 1; w1 = b[o1:o1 + 4].hex()
    p1 = os.path.join(pdir, 'plant1.elf'); open(p1, 'wb').write(b)
    pc = sym[PLANT_FN] + P2_OFF; o2 = foff(pc)
    b = bytearray(raw); x = int.from_bytes(b[o2:o2 + 4], 'little')
    if x & 0x7f != 0x6f or pc + jimm(x) != sym[P2_FROM]:
        raise SystemExit('mk_evidence_memchr_kit: %s+%#x is not a jal to %s' % (PLANT_FN, P2_OFF, P2_FROM))
    v0 = b[o2:o2 + 4].hex(); b[o2:o2 + 4] = jal_word((x >> 7) & 31, sym[P2_TO] - pc).to_bytes(4, 'little'); v1 = b[o2:o2 + 4].hex()
    p2 = os.path.join(pdir, 'plant2.elf'); open(p2, 'wb').write(b)
    return ((p1, 'PLANT1(fuzz_boxreg copy, %s+%#x %s -> %s)' % (PLANT_FN, P1_OFF, w0, w1)),
            (p2, 'PLANT2(fuzz_boxreg copy, %s+%#x jal %s -> jal %s, %s -> %s)' % (PLANT_FN, P2_OFF, P2_FROM, P2_TO, v0, v1)))


# ---- parsers of the kit's tables and the old tables ------------------------------------------------------------------

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
    """(counts (functions, indirect sites, EQUAL, EQUAL-mod-pcrel, other), {X address: (name, verdict, line no, line)})
    of the first root block (up to a '== ' line)"""
    cnt = None; bad = {}
    for n, l in enumerate(t.splitlines(), 1):
        if l.startswith('== '):
            break
        m = CL_SUM.match(l)
        if m:
            if cnt is not None:
                break
            cnt = tuple(int(m.group(k)) for k in range(2, 7)); continue
        m = re.match(r'^   (?!ACCEPT )(\S+) @(0x[0-9a-f]+): (.*)$', l)
        if m:
            rest = m.group(3); k = rest.find(' [')
            bad[int(m.group(2), 16)] = (m.group(1), (rest[:k] if k >= 0 else rest).strip(), n, l)
    return cnt, bad


def jt_parse(t):
    """{fn: {line, n, settled, label, det: [(DIFF|UNMEASURED|UNPAIRED, word offset, text, line no)]}} for the kit's format
    and for the old jtcheck 2e2f9c2126b2 format"""
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
            elif len(f) >= 5 and f[3].startswith('target differs '):
                td, up = int(f[3].rsplit(' ', 1)[1]), int(f[4].rsplit(' ', 1)[1])
                ok = td == up == 0
                lab = 'settled' if ok else 'not settled: target differs %d, unpaired differing words %d' % (td, up)
            else:
                ok = False; lab = 'not settled: ' + ' '.join(f[1:])
            out[cur] = dict(line=l, n=n, settled=ok, label=lab, tables=f[-1] if ok else '', det=[])
        elif cur is not None:
            m = re.match(r'   (DIFF|UNMEASURED|UNPAIRED) \+(0x[0-9a-f]+) (.*)', l)
            if m:
                out[cur]['det'].append((m.group(1), int(m.group(2), 16), m.group(3), n))
    return out


# ---- measurement of a target the kit leaves unsettled ----------------------------------------------------------------

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
    img, out = sys.argv[1], os.path.abspath(sys.argv[2])
    if img not in ('A', 'B'):
        raise SystemExit('usage: mk_evidence_memchr_kit.py A|B OUTDIR')
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    sys.dont_write_bytecode = True
    v = ('asan', 'asan-ubsan')[img == 'B']
    uci, box, upin, bpin = env['UCI_' + img], env['BOX_' + img], env['UCI_PIN_' + img], env['BOX_PIN_' + img]
    told = os.path.join(out, 'tables')
    old = {f: open(os.path.join(told, f)).read() for f in ('twins.txt', 'chain.tsv', 'closure.txt', 'jtcheck.tsv')}
    kitdir = tempfile.mkdtemp(prefix='mkkit-'); pdir = tempfile.mkdtemp(prefix='mkkitp-')
    try:
        kit_sha = kit_copy(env['KIT'], kitdir)
        (p1, n1), (p2, n2) = plants(box, pdir)
        names = {uci: 'fuzz_uci.%s(unstripped, sha256 %s)' % (v, sha(uci)[:12]),
                 box: 'fuzz_boxreg.%s(unstripped, sha256 %s)' % (v, sha(box)[:12]),
                 upin: 'fuzz_uci.%s(pin, sha256 %s)' % (v, sha(upin)[:12]),
                 bpin: 'fuzz_boxreg.%s(pin, sha256 %s)' % (v, sha(bpin)[:12]),
                 p1: n1, p2: n2, kitdir + '/': '', pdir + '/': ''}
        keys = sorted(names, key=len, reverse=True)

        def run(args):
            r = subprocess.run([sys.executable] + args, cwd=kitdir, capture_output=True, text=True, env=env)
            t = r.stdout + r.stderr
            for k in keys:
                t = t.replace(k, names[k])
            if r.returncode:
                raise SystemExit('mk_evidence_memchr_kit: %s failed:\n%s' % (args[0], t))
            return t

        tabs = {'twins.txt': run(['drvcmp.py', 'twins', upin, uci, bpin, box]),
                'chain.tsv': run(['strictcmp2.py', 'cmp', ','.join(FNS), 'U=' + uci, 'R=' + box, 'U:R']),
                'closure.txt': run(['closure_strict2.py', uci, box, ROOT])}
        ncnt, nbad = closure_parse(tabs['closure.txt'])
        members = JT_OLD + sorted({n for n, vv, ln, l in nbad.values()} - set(JT_OLD))
        tabs['jtcheck.tsv'] = run(['jtcheck.py', uci, box, ','.join(members)])
        ctl = [('strictcmp2.py cmp, the four chain functions, P1 : R and P2 : R',
                run(['strictcmp2.py', 'cmp', ','.join(FNS), 'P1=' + p1, 'P2=' + p2, 'R=' + box, 'P1:R,P2:R'])),
               ('closure_strict2.py P1 R ' + ROOT, run(['closure_strict2.py', p1, box, ROOT])),
               ('closure_strict2.py P2 R ' + ROOT, run(['closure_strict2.py', p2, box, ROOT])),
               ('jtcheck.py P1 R ' + ROOT, run(['jtcheck.py', p1, box, ROOT])),
               ('jtcheck.py P2 R ' + ROOT, run(['jtcheck.py', p2, box, ROOT]))]
        tabs['control.txt'] = ''.join('== %s\n%s' % (h, t if t.endswith('\n') else t + '\n') for h, t in ctl)
        M = Measure(kitdir, uci, box)

        # ---- settle what the kit leaves unsettled, by measurement
        njt = jt_parse(tabs['jtcheck.tsv']); ojt = jt_parse(old['jtcheck.tsv'])
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

        rows = []          # (table, function, pair, old, kit verdict, kit line ref, settled verdict, detail, kit line)
        otw, ntw = old['twins.txt'].splitlines(), tabs['twins.txt'].splitlines()
        tw_ok = len(ntw) == 2 and all('PT_LOAD layout equal: True' in l and l.endswith(': []') for l in ntw)
        for k in range(max(len(otw), len(ntw))):
            a = otw[k] if k < len(otw) else ''; b = ntw[k] if k < len(ntw) else ''
            if a.split(' | ', 2)[2:] != b.split(' | ', 2)[2:]:
                rows.append(('twins', b.split(' | ')[0], 'pin:twin', a, b, 'twins.txt:%d' % (k + 1), '', '', b))
        och, nch = chain_rows(old['chain.tsv'], 'U:R'), chain_rows(tabs['chain.tsv'], 'U:R')
        ch_ok = all(nch.get(f, ('ABSENT',))[0] in ('EQUAL', 'EQUAL-mod-pcrel') for f in FNS)
        for f in FNS:
            a, b = och.get(f, ('ABSENT', 0, ''))[0], nch.get(f, ('ABSENT', 0, ''))[0]
            if a != b:
                c, d = settle(f) if b not in ('EQUAL', 'EQUAL-mod-pcrel') else ('', '')
                rows.append(('chain', f, 'U:R', a, b, 'chain.tsv:%d' % nch.get(f, (0, 0))[1], c, d, nch.get(f, ('', 0, ''))[2]))
        ocnt, obad = closure_parse(old['closure.txt'])
        if ocnt != ncnt:
            lab = 'closure %d functions, EQUAL %d, EQUAL-mod-pcrel %d, other %d'
            rows.append(('closure', ROOT, 'U:R', lab % (ocnt[0], ocnt[2], ocnt[3], ocnt[4]),
                         lab % (ncnt[0], ncnt[2], ncnt[3], ncnt[4]), 'closure.txt:1', '', '', tabs['closure.txt'].splitlines()[0]))
        mset = {}          # reported member name -> (settled verdict, detail, X address)
        SET = 'settled (EQUAL / EQUAL-mod-pcrel, all targets equal)'
        for a in sorted(set(obad) | set(nbad)):
            ov, nv = obad[a][1] if a in obad else SET, nbad[a][1] if a in nbad else SET
            name = (nbad.get(a) or obad.get(a))[0]
            if a in nbad:
                mset[name] = (settle(name) if not re.match(r'(DIFFERENT|SIZE|ABSENT|AMBIGUOUS|UNREADABLE)', nv) else
                              ('REAL', 'instruction words differ or no counterpart: ' + nv)) + (a,)
            if ov != nv:
                c, d = mset.get(name, ('', '', 0))[:2]
                rows.append(('closure', name, 'U:R @%#x' % a, ov, nv, 'closure.txt:%d' % nbad[a][2] if a in nbad else '',
                             c, d, nbad[a][3].strip() if a in nbad else ''))
        for f in JT_OLD:
            a = ojt.get(f, {}).get('label', 'not run'); b = njt.get(f, {}).get('label', 'not run')
            if (a == 'settled') != (b == 'settled'):
                c, d = settle(f)
                rows.append(('jtcheck', f, 'U:R', a, b, 'jtcheck.tsv:%d' % njt[f]['n'], c, d, njt[f]['line']))

        # ---- the planted controls
        cc = ctl[0][1]
        p1r, p2r = chain_rows(cc, 'P1:R'), chain_rows(cc, 'P2:R')
        p1_ok = p1r.get(PLANT_FN, ('',))[0] == 'DIFFERENT' and all(p1r.get(f, ('',))[0] == 'EQUAL' for f in FNS if f != PLANT_FN)
        p2_ok = p2r.get(PLANT_FN, ('',))[0].startswith('EQUAL-mod-pcrel target-differ') and \
            any(d[0] == hex(P2_OFF) for d in chain_diffs(p2r[PLANT_FN][2])) and \
            all(p2r.get(f, ('',))[0] == 'EQUAL' for f in FNS if f != PLANT_FN)
        c1, b1 = closure_parse(ctl[1][1]); c2, b2 = closure_parse(ctl[2][1])
        cl1_ok = [vv[0] for vv in b1.values()] == [PLANT_FN] and b1[next(iter(b1))][1] == 'DIFFERENT'
        cl2_ok = PLANT_FN in [vv[0] for vv in b2.values()]
        j1, j2 = jt_parse(ctl[3][1]).get(ROOT, {}), jt_parse(ctl[4][1]).get(ROOT, {})
        jt1_ok = 'REAL difference' in j1.get('line', '')
        jt2_ok = any(kd == 'DIFF' and off == P2_OFF for kd, off, tx, ln in j2.get('det', []))
        caught = p1_ok and p2_ok and cl1_ok and cl2_ok and jt1_ok and jt2_ok
        ocp = chain_rows(old['chain.tsv'], 'P:R').get(PLANT_FN, ('ABSENT',))[0]
        if ocp != p1r.get(PLANT_FN, ('ABSENT',))[0]:
            rows.append(('control', PLANT_FN, 'P1:R', ocp, p1r.get(PLANT_FN, ('ABSENT',))[0], 'control.txt', '', '', ''))

        # ---- write the tables
        tabs['acceptances.tsv'] = 'function\tword\tjtcheck line\tthe kit\'s verdict\tsettled verdict\tmeasurement\n' + ''.join(
            '%s\t+%#x\tjtcheck.tsv:%d\t%s\t%s\t%s\n' % (fn, off, ln, kv, c, d.replace('\t', ' '))
            for (fn, off), (kv, ln, c, d) in sorted(acc.items(), key=lambda e: (njt[e[0][0]]['n'], e[0][1])))
        tabs['changed.tsv'] = 'table\tfunction\tpair\told verdict\tthe kit\'s verdict\tkit line\tsettled verdict\tdetail\t' \
            'the kit\'s line\n' + ''.join('\t'.join(str(c).replace('\t', ' ') for c in r) + '\n' for r in rows)
        for k, t in tabs.items():
            bad = [p for p in names if p.rstrip('/') and p.rstrip('/') in t] + LEAK.findall(t)
            if bad:
                raise SystemExit('mk_evidence_memchr_kit: a host path is left in %s' % k)
        tdir = os.path.join(told, SUB)
        os.makedirs(tdir, exist_ok=True)
        for k, t in tabs.items():
            open(os.path.join(tdir, k), 'w').write(t)
        os.makedirs(os.path.join(out, 'scripts'), exist_ok=True)
        shutil.copy(os.path.abspath(__file__), os.path.join(out, 'scripts', 'mk_evidence_memchr_kit.py'))

        # ---- MANIFEST section
        def md(s):
            return str(s).replace('|', '\\|')
        nrep = len(nbad)
        by_jt = sorted(n for n, (c, d, a) in mset.items() if c.startswith('settled by the kit'))
        by_ms = sorted(n for n, (c, d, a) in mset.items() if c.startswith('settled by measurement'))
        real = sorted(n for n, (c, d, a) in mset.items() if c == 'REAL')
        notc = sorted(n for n, (c, d, a) in mset.items() if c == 'not certified')
        cls_n = {}
        for kv, ln, c, d in acc.values():
            cls_n[c] = cls_n.get(c, 0) + 1
        certified = not real and not notc
        imgs = [('U', 'fuzz_uci.%s, unstripped twin' % v, uci), ('R', 'fuzz_boxreg.%s, unstripped twin' % v, box),
                ('pin', 'fuzz_uci.%s, pinned image' % v, upin), ('pin', 'fuzz_boxreg.%s, pinned image' % v, bpin),
                ('P1', n1, p1), ('P2', n2, p2)]
        m = [SECTION, '',
             'Written by scripts/mk_evidence_memchr_kit.py; not edited by hand. The sections above and the tables directly '
             'under tables/ were made with bytecmp 7daa0e2a03d9 + repin_check 9cbc3553c09e. This section and `tables/%s/` '
             're-run the same comparisons with the comparison kit of record, cmpkit %s (commit %s, tools/cmpkit/%s/; sha256 of '
             'its SHA256SUMS %s), its seven files run from one directory that holds only them. Tools cited, not shipped. '
             'Each verdict is the kit\'s first; where the kit fails closed, the settled verdict follows it, from a named '
             'measurement of this builder (`acceptances.tsv`), or "not certified".'
             % (SUB, KIT_ID, KIT_COMMIT, KIT_ID, kit_sha), '',
             'Images (file name, sha256):', '']
        m += ['- %s: %s, `%s`' % (t, d, sha(p)) for t, d, p in imgs]
        m += ['', '### Verdict', '',
              '- CLAIM: %s' % (
                  'the chain and the whole closure of `%s` equal the donor\'s up to relocation (kit verdicts, and the '
                  'acceptances below)' % ROOT if certified and ch_ok and tw_ok else
                  'NARROWED to the chain: the four chain functions (%s) equal the donor\'s up to relocation on the kit, every '
                  'target equal. The closure of `%s` is not certified as a whole: %d reported members are listed below as '
                  'not certified%s.' % (', '.join('`%s`' % f for f in FNS), ROOT, len(notc) + len(real),
                                        ' (%d with a REAL difference)' % len(real) if real else '')
                  if ch_ok and tw_ok else 'NOT MET: the chain or the twins check fails on the kit'),
              '- twins (each pin = its unstripped twin, PT_LOAD bytes; `twins.txt`): %s'
              % ('equal outside the ELF header and build-id note (unchanged)' if tw_ok else 'NOT EQUAL'),
              '- chain, U : R (`chain.tsv`), kit verdict (old verdict):']
        m += ['  - `%s`: %s (old: %s)' % (f, nch.get(f, ('ABSENT',))[0], och.get(f, ('ABSENT',))[0]) for f in FNS]
        m += ['- closure of `%s` (`closure.txt`): kit: %d functions, EQUAL %d, EQUAL-mod-pcrel with all targets equal %d, '
              'reported %d (old: %d functions, EQUAL %d, EQUAL-mod-pcrel %d, other %d). Of the %d reported: settled by the kit\'s '
              'jtcheck %d; settled by measurement %d; not certified %d; REAL %d.'
              % (ROOT, ncnt[0], ncnt[2], ncnt[3], ncnt[4], ocnt[0], ocnt[2], ocnt[3], ocnt[4], nrep, len(by_jt), len(by_ms),
                 len(notc), len(real)),
              '- jtcheck over %d functions, the 11 of the old record and every reported closure member (`jtcheck.tsv`): kit: '
              'settled %d, not settled %d (old: 11 run, settled %d). Its %d unsettled targets, measured (`acceptances.tsv`): %s.'
              % (len(njt), sum(1 for j in njt.values() if j['settled']), sum(1 for j in njt.values() if not j['settled']),
                 sum(1 for j in ojt.values() if j['settled']), len(acc),
                 ', '.join('%s %d' % (c, n) for c, n in sorted(cls_n.items()))),
              '- planted control (`control.txt`): P1 %s (chain row %s; closure reports `%s` %s; jtcheck: REAL difference %s); '
              'P2 %s (chain row %s at +%#x; closure %s; jtcheck DIFF at +%#x: %s)'
              % ('caught' if p1_ok and cl1_ok and jt1_ok else 'NOT CAUGHT', p1r.get(PLANT_FN, ('ABSENT',))[0], PLANT_FN,
                 'only' if cl1_ok else 'NOT only', 'yes' if jt1_ok else 'NO',
                 'caught' if p2_ok and cl2_ok and jt2_ok else 'NOT CAUGHT', p2r.get(PLANT_FN, ('ABSENT',))[0], P2_OFF,
                 'reports it' if cl2_ok else 'MISSES it', P2_OFF, 'yes' if jt2_ok else 'NO'),
              '',
              'Settled verdicts (this builder\'s measurement on file bytes, read with the kit\'s Img / frd / region / qres; never a '
              'kit EQUAL): "empty string", "C string with non-printable bytes", "C string" = an unnamed target whose address '
              'every path that uses it passes on as a call argument or a return value, equal through its NUL in both images '
              '(the kit fails closed: its C-string rule needs printable bytes, and the region to the next symbol differs). '
              '"unnamed table" = an indexed unnamed .rodata table, equal entry by entry over every index its bound allows: a '
              'jump table as function+offset, a relative pointer table as symbol+offset (an unnamed entry target as a C string '
              'through its NUL), a value table over the bytes its index can reach; the bounding instructions are named in '
              '`acceptances.tsv`. "not certified" = the measurement did not settle it (its consumer or bound was not '
              'followed). "REAL" = bytes the code reads differ.', '',
              '### Changed verdicts against the old tables', '',
              '| table | function | pair | old verdict | kit verdict | kit line | settled verdict |', '|---|---|---|---|---|---|---|']
        m += ['| %s | `%s` | %s | %s | %s | `%s` | %s |' % tuple(md(c) for c in (r[0], r[1], r[2], r[3], r[4], r[5], r[6] or '-'))
              for r in rows]
        m += ['', 'Each row\'s detail and the kit\'s full line are in `tables/%s/changed.tsv`.' % SUB, '']
        if notc or real:
            m += ['### Not certified', '',
                  '| function | X address | kit verdict | unsettled targets (`acceptances.tsv`) |', '|---|---|---|---|']
            m += ['| `%s` | %#x | %s | %s |' % (n, mset[n][2], md(nbad[mset[n][2]][1]), md(mset[n][1])) for n in real + notc]
            m += ['']
        groups = {}
        for (fn, off), (kv, ln, c, d) in acc.items():
            if c in SETTLED_CLASSES:
                key = (c, re.sub(r'; (its address is|bound) .*$', '', d))
                groups.setdefault(key, []).append('%s+%#x' % (fn, off))
        m += ['### Acceptances (settled by measurement, not by the kit; a fresh reviewer audits them)', '',
              'Grouped by target and measured bytes; one row per use is in `tables/%s/acceptances.tsv`, with the consumer '
              '(the call or return that passes the address on) or the table bound of each use.' % SUB, '',
              '| settled verdict | measurement | uses |', '|---|---|---|']
        m += ['| %s | %s | %d: %s |' % (md(c), md(d), len(u), md(', '.join('`%s`' % e for e in sorted(u)[:4]) +
                                                              (', ...' if len(u) > 4 else '')))
              for (c, d), u in sorted(groups.items(), key=lambda e: (e[0][0], -len(e[1])))]
        m += ['', '### Files', '', '| file | kind | role |', '|---|---|---|',
              '| `scripts/mk_evidence_memchr_kit.py` | script | this re-run\'s builder |',
              '| `tables/%s/twins.txt` | table | drvcmp.py twins: each pin = its unstripped twin |' % SUB,
              '| `tables/%s/chain.tsv` | table | strictcmp2.py cmp: the four chain functions, U : R |' % SUB,
              '| `tables/%s/closure.txt` | table | closure_strict2.py: the closure of `%s`, U : R |' % (SUB, ROOT),
              '| `tables/%s/jtcheck.tsv` | table | jtcheck.py: the old 11 and every reported closure member |' % SUB,
              '| `tables/%s/control.txt` | table | the planted copies P1, P2 against R, under strictcmp2, closure_strict2, jtcheck |' % SUB,
              '| `tables/%s/acceptances.tsv` | table | each target jtcheck leaves unsettled: kit verdict, settled verdict, measurement |' % SUB,
              '| `tables/%s/changed.tsv` | table | every changed verdict, the kit\'s line, and the settled verdict |' % SUB]
        mp = os.path.join(out, 'MANIFEST.md')
        text = open(mp).read()
        k = text.find('\n' + SECTION + '\n')
        if k >= 0:
            e = text.find('\n## ', k + 1)
            text = text[:k + 1] + (text[e + 1:] if e >= 0 else '')
        open(mp, 'w').write(text.rstrip('\n') + '\n\n' + '\n'.join(m) + '\n')
    finally:
        shutil.rmtree(kitdir); shutil.rmtree(pdir)
    print('mk_evidence_memchr_kit: memchr-%s: twins %s, chain %s, closure reported %d (old %d): jtcheck %d, measurement %d, '
          'not certified %d, REAL %d; changed verdicts %d; control %s'
          % (img, 'ok' if tw_ok else 'NOT EQUAL', 'settled' if ch_ok else 'NOT SETTLED', nrep, len(obad), len(by_jt), len(by_ms),
             len(notc), len(real), len(rows), 'caught' if caught else 'NOT CAUGHT'))
    if not caught:
        raise SystemExit('mk_evidence_memchr_kit: the planted control was not caught, see %s' % out)


if __name__ == '__main__':
    main()
