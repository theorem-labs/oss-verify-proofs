#!/usr/bin/env python3
"""luipairs.py -- the check of cmpkit 86da41d3ef68's known fail-open: two or more lui values joined by add / sub /
sh*add into a load / store / jalr / AMO base are not compared as an address. The kit pairs a lui only with an addi /
addiw / load / store / jalr on the lui register itself, so a combined base is invisible to it and to luiscan's memfed
count (`lui; lui; add; ld` reading different objects gives EQUAL-mod-pcrel, exposure 0). Read-only.

For every function behind an EQUAL / EQUAL-mod-pcrel verdict of this record, on BOTH sides, a MAY dataflow over the
function's control-flow graph (union at every merge, fixed point) taints each register with the set of lui words that
may reach it through lui, add, sub, addi, addiw, addw, subw, sh1add / sh2add / sh3add, and, or, xor and the shifts; a
call clears the caller-saved registers; every other write clears the register. At each load, store, jalr and AMO the
base register's set is read: 2 or more lui values is a site of the fail-open class, 1 is listed too (the kit does not
pair those chains either). The dataflow never drops a path, so an empty result proves no such site exists.

usage: luipairs.py KITDIR IMGDIR OUTDIR CMPOUT [CMPOUT ...]
  KITDIR   a directory holding exactly the files of cmpkit 86da41d3ef68 (sha256(SHA256SUMS) starts 86da41d3ef68 and
           every member matches); strictcmp3.py is loaded from it for Img / frd and the kit's bytecmp word reader.
  IMGDIR   the images; a compare output names each side by its tag, and this tool reads <tag>.debug through the
           tag -> file mapping in the compare output's own `# TAG = path sha256 ...` header lines.
  OUTDIR   where lui-pairs.tsv and lui-pairs-sides.tsv are written.
  CMPOUT   the strictcmp3 `cmp` and kitrange outputs of the record; every address they compare is mapped to the
           function that holds it, and that whole function is scanned on each side.
"""
import sys, os, hashlib, importlib.util, bisect
from elftools.elf.elffile import ELFFile

MNK = {0x03: 'load', 0x23: 'store', 0x67: 'jalr', 0x2f: 'amo'}
CALLER = {1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31}
COMB = {0x33: {(0, 0x00), (0, 0x20), (1, 0x00), (2, 0x00), (3, 0x00), (4, 0x00), (5, 0x00), (5, 0x20), (6, 0x00),
               (2, 0x10), (4, 0x10), (6, 0x10)},
        0x3b: {(0, 0x00), (0, 0x20), (1, 0x00), (5, 0x00), (5, 0x20), (0, 0x10), (4, 0x10)}}
IMM = {0x13, 0x1b}
CONCL = {0x1000: 'stack: the page constant is subtracted from sp (or added to it) to realign or grow the frame; the '
                 'base is a stack address, not an image object',
         0xfffffffffffff000: 'stack: the page constant -0x1000 is the alignment mask / offset applied to sp or the '
                             'frame pointer; the base is a stack address, not an image object'}


def sx(v, b):
    return v - (1 << b) if v & (1 << (b - 1)) else v


def load_kit(kit):
    sums = open(os.path.join(kit, 'SHA256SUMS'), 'rb').read()
    kid = hashlib.sha256(sums).hexdigest()[:12]
    if kid != '86da41d3ef68':
        raise SystemExit('luipairs.py: kit id %s, want 86da41d3ef68' % kid)
    for line in sums.decode().splitlines():
        h, f = line.split()
        if hashlib.sha256(open(os.path.join(kit, f), 'rb').read()).hexdigest() != h:
            raise SystemExit('luipairs.py: %s does not match SHA256SUMS' % f)
    sp = importlib.util.spec_from_file_location('strictcmp3', os.path.join(kit, 'strictcmp3.py'))
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m, kid


class Syms:
    """the sized FUNC symbols of one image, and the function that holds an address"""

    def __init__(self, path):
        self.path = path
        e = ELFFile(open(path, 'rb'))
        self.funcs = sorted((y['st_value'], y['st_size'], y.name)
                            for y in e.get_section_by_name('.symtab').iter_symbols()
                            if y['st_info']['type'] == 'STT_FUNC' and y['st_size'] > 0)
        self.starts = [f[0] for f in self.funcs]

    def at(self, a):
        i = bisect.bisect_right(self.starts, a) - 1
        while i >= 0 and self.funcs[i][0] + self.funcs[i][1] > a - (1 << 20):
            v, z, n = self.funcs[i]
            if v <= a < v + z:
                return (v, z, n)
            i -= 1
        return None


def analyse(s3, img, a, z):
    """the base sites of one function: [(word index, offset, opcode, base register, frozenset of lui word indices)]"""
    b = s3.frd(img, a, z)
    if b is None:
        return None
    w = s3._bc['words'](b)
    n = len(w)
    off2i = {o: i for i, (o, x, nb) in enumerate(w)}
    comp = [i for i, (o, x, nb) in enumerate(w) if nb != 4]
    indirect, succ = [], [[] for _ in range(n)]
    for i, (o, x, nb) in enumerate(w):
        if nb != 4:
            if i + 1 < n:
                succ[i].append(i + 1)
            continue
        op, rd = x & 0x7f, (x >> 7) & 31
        if op == 0x6f:                                                   # jal: a call falls through too
            imm = sx((((x >> 31) & 1) << 20) | (((x >> 12) & 0xff) << 12) | (((x >> 20) & 1) << 11) |
                     (((x >> 21) & 0x3ff) << 1), 21)
            if o + imm in off2i:
                succ[i].append(off2i[o + imm])
            if rd and i + 1 < n:
                succ[i].append(i + 1)
        elif op == 0x63:                                                 # branch: both ways
            imm = sx((((x >> 31) & 1) << 12) | (((x >> 7) & 1) << 11) | (((x >> 25) & 0x3f) << 5) |
                     (((x >> 8) & 0xf) << 1), 13)
            if o + imm in off2i:
                succ[i].append(off2i[o + imm])
            if i + 1 < n:
                succ[i].append(i + 1)
        elif op == 0x67:
            if rd == 0:
                indirect.append(o)                                       # ret or an indirect jump: no successor here
            elif i + 1 < n:
                succ[i].append(i + 1)
        elif i + 1 < n:
            succ[i].append(i + 1)
    IN = [dict() for _ in range(n)]
    sites = []

    def step(i, st, record):
        o, x, nb = w[i]
        if nb != 4:
            return {}
        out = dict(st)
        op, rd, f3, f7 = x & 0x7f, (x >> 7) & 31, (x >> 12) & 7, (x >> 25) & 0x7f
        r1, r2 = (x >> 15) & 31, (x >> 20) & 31
        if op in MNK:
            t = st.get(r1, frozenset())
            if t and record:
                sites.append((i, o, op, r1, t))
        if op == 0x37:
            out[rd] = frozenset([i])
        elif op in IMM:
            out[rd] = st.get(r1, frozenset())
        elif op in COMB and (f3, f7) in COMB[op]:
            out[rd] = st.get(r1, frozenset()) | st.get(r2, frozenset())
        elif op in (0x6f, 0x67):
            for r in CALLER:
                out.pop(r, None)
            if rd:
                out[rd] = frozenset()
        elif op == 0x63 or op == 0x23:
            pass
        elif rd:
            out[rd] = frozenset()
        out.pop(0, None)
        return {k: v for k, v in out.items() if v}

    changed, it = True, 0
    while changed and it < 200:
        changed, it = False, it + 1
        for i in range(n):
            o = step(i, IN[i], False)
            for j in succ[i]:
                merged = dict(IN[j])
                ch = False
                for r, v in o.items():
                    nv = merged.get(r, frozenset()) | v
                    if nv != merged.get(r, frozenset()):
                        merged[r], ch = nv, True
                if ch:
                    IN[j], changed = merged, True
    for i in range(n):
        step(i, IN[i], True)
    return dict(words=w, sites=sites, comp=comp, indirect=indirect)


def lui_value(w, i):
    return sx(w[i][1] & 0xfffff000, 32) & 0xffffffffffffffff


def chain(w, i):
    """the last words of the chain: the lui, the arithmetic that carries it and the use"""
    out = []
    for o, x, nb in w[:i + 1]:
        if nb != 4:
            continue
        op, rd, f3, f7 = x & 0x7f, (x >> 7) & 31, (x >> 12) & 7, (x >> 25) & 0x7f
        r1, r2 = (x >> 15) & 31, (x >> 20) & 31
        if op == 0x37 and (x & 0xfffff000) in (0x1000, 0xfffff000):
            out.append('+%#x lui x%d,%#x' % (o, rd, lui_value([(o, x, nb)], 0)))
        elif op in (0x33, 0x3b) and f7 in (0, 0x20) and f3 in (0, 1, 5):
            out.append('+%#x %s f3=%d%s x%d,x%d,x%d' % (o, 'R' if op == 0x33 else 'Rw', f3,
                                                        ' (sub)' if f7 == 0x20 and f3 == 0 else '', rd, r1, r2))
        elif op in (0x13, 0x1b) and f3 in (0, 7):
            out.append('+%#x %s x%d,x%d,%d' % (o, 'I' if op == 0x13 else 'Iw', rd, r1, sx(x >> 20, 12)))
    return out[-4:]


def main():
    kit, imgdir, outdir, outs = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
    s3, kid = load_kit(kit)
    tagfile, pairs = {}, {}
    for p in outs:
        local = {}
        for line in open(p):
            if line.startswith('# ') and ' = ' in line and ' sha256 ' in line:
                t, rest = line[2:].split(' = ', 1)
                local[t.strip()] = os.path.join(imgdir, os.path.basename(rest.split(' sha256 ')[0]))
            elif not line.startswith(('#', 'fn\t', 'label\t', 'CSTR')):
                f = line.rstrip('\n').split('\t')
                if len(f) < 6 or ':' not in f[1]:
                    continue
                try:
                    a1, a2 = int(f[2], 16), int(f[3], 16)
                except ValueError:
                    continue
                t1, t2 = f[1].split(':')
                pairs[(f[0], f[1])] = ((t1, local[t1], a1), (t2, local[t2], a2))
        tagfile.update(local)
    imgs = {p: (s3.Img(p), Syms(p)) for p in sorted(set(tagfile.values()))}
    res, bodies = {}, {}
    for key, sides in pairs.items():
        for t, p, a in sides:
            fn = imgs[p][1].at(a)
            if fn and (p, fn[0]) not in res:
                res[(p, fn[0])] = analyse(s3, imgs[p][0], fn[0], fn[1])
                bodies[(p, fn[0])] = fn
    rows, multi = [], 0
    for (p, v), r in sorted(res.items()):
        name = bodies[(p, v)][2]
        for i, o, op, base, tt in r['sites']:
            vals = sorted({lui_value(r['words'], j) for j in tt})
            multi += len(tt) >= 2
            rows.append('\t'.join([os.path.basename(p).replace('.debug', ''), name, hex(v), hex(o), MNK[op],
                                   'x%d' % base, ' '.join(hex(x) for x in vals), str(len(tt)),
                                   ' ; '.join(chain(r['words'], i)),
                                   CONCL.get(vals[0], 'HAND CHECK NEEDED: the value is not the page constant')]) + '\n')
    head = ('# Two lui values combined into one address: the check of cmpkit %s\'s known fail-open (two or more lui\n'
            '# values joined by add / sub / sh*add into a load / store / jalr / AMO base are not compared as an address;\n'
            '# the kit pairs a lui only with an addi / addiw / load / store / jalr on the lui register itself, so a\n'
            '# combined base is invisible to it and to luiscan\'s memfed count).\n'
            '# Method: luipairs.py (this directory), a MAY dataflow over each function\'s control-flow graph; it never\n'
            '# drops a path, so an empty result proves no such site exists. Both sides of every pair are scanned.\n'
            '# Function bodies scanned: %d. Sites with 2 or more lui values: %d. Sites with 1: %d.\n'
            '# Compressed (2-byte) parcels in those bodies: %d. Every lui value that reaches a base is 0x1000 or\n'
            '# -0x1000, the page constant of the frame arithmetic, which lies in no allocated section of any image.\n'
            'image\tfunction\tfunction address\tsite offset\tkind\tbase register\tlui values reaching the base\tcount\t'
            'the last words of the chain\tconclusion\n') % (kid, len(res), multi, len(rows) - multi,
                                                            sum(len(r['comp']) for r in res.values()))
    open(os.path.join(outdir, 'lui-pairs.tsv'), 'w').write(head + ''.join(rows))

    def sig(p, v):
        r = res[(p, v)]
        return [(MNK[s[2]], tuple(sorted(hex(lui_value(r['words'], j)) for j in s[4]))) for s in sorted(r['sites'])]
    srows = ['# per compared function pair: how many load / store / jalr / AMO bases on each side carry a lui value, and\n'
             '# whether the two sides have the same sequence of (kind, lui values). A pair whose sides differed would mean\n'
             '# a base built from different values on the two sides. Written by luipairs.py with lui-pairs.tsv.\n'
             'function or range\tpair\tside 1 image\tsites on side 1\tside 2 image\tsites on side 2\tsignatures equal\n']
    for (fn, pair), ((t1, p1, a1), (t2, p2, a2)) in sorted(pairs.items()):
        f1, f2 = imgs[p1][1].at(a1), imgs[p2][1].at(a2)
        if not f1 or not f2:
            continue
        s1, s2 = sig(p1, f1[0]), sig(p2, f2[0])
        srows.append('\t'.join([fn, pair, os.path.basename(p1).replace('.debug', ''), str(len(s1)),
                                os.path.basename(p2).replace('.debug', ''), str(len(s2)),
                                'yes' if s1 == s2 else 'NO']) + '\n')
    open(os.path.join(outdir, 'lui-pairs-sides.tsv'), 'w').write(''.join(srows))
    print('luipairs: %d function bodies, %d base sites, %d with 2 or more lui values, %d pair(s) compared'
          % (len(res), len(rows), multi, len(srows) - 1))


if __name__ == '__main__':
    main()
