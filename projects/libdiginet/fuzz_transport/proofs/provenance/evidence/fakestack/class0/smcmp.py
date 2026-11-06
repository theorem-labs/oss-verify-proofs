#!/usr/bin/env python3
"""smcmp.py -- pair and compare, on one image, every code range of a donor's fake-stack class-<C> walk (the
`(0x..., N%nat)` rows of the code tables --tables names) with the target unit's image, and write the --resolve lines
alreloc needs for the files --reloc names. It is class5/class5cmp.py with the donor, the class, the tables, the
relocated files and the model constants made arguments; the steps, the kit and the resolve rules are that file's.
Nothing in it names a target address: every target value is derived from the images given, so a re-pin is a re-run.

usage: smcmp.py --hub HUB --ref REF --src P/H --img A|B --cls C --donor PINNED TWIN --target PINNED TWIN --out DIR
                --tables FILE[:VAR] ... [--reloc FILE ...] [--keep-all FILE ...] [--model FILE] [--tag NAME]
                [--donor-lib PATH]
  FILE     a donor path under the donor's lib at REF (A/Rt/StackMalloc0Tbl.v); VAR defaults to fs_ranges
  --donor-lib  the donor's lib directory at REF (default proofs/<P/H>/lib); a donor released only in the
           projects/<P/H>/proofs/lib layout is read there for the rule-24 compare (alreloc reads proofs/<P/H>/lib only)
  --model  a file of `TOKEN description` lines (`#` starts a comment): numerals of the relocated files that are model
           constants, kept (alreloc's symbol rule would move one that falls inside the image)
  --tag    the output name (default class<C>)

Steps (each a check; any failure exits 1):
 1. each PINNED file equals its TWIN in every allocated section but the build-id note (the twin gives the names, the
    pinned file is the image; the ELF header and the build-id note are the only allowed differences);
 2. the donor ranges are read from REF's tables (`Definition VAR : list (Z * nat) := [...]`);
 3. each donor range start is paired with a target address: the containing FUNC symbol by name + offset when that name
    has one copy in each image; else (several copies, e.g. a local static such as __asan::MemToShadow) by the call that
    reaches it: the target of the `jal` at the same word of a name-paired function of the table (its whole body), on
    both sides, which must be one address;
 4. the whole containing function of each pair is compared by the comparison kit of record (cmpkit 86da41d3ef68, the
    directory KIT names, its SHA256SUMS checked by smrun.sh): strictcmp3's tcmp (bytecmp words + its target
    pass, lui-built addresses included); EQUAL or EQUAL-mod-pcrel with 0 real, 0 unmeasured and 0 differing targets
    passes, for the walked words alone or for the whole function; __asan_stack_malloc_<C> must have one copy of one size
    on each side and its pc-relative words the same form;
 5. resolve lines for the --reloc files (alreloc applies a resolve line before any other rule), as class5cmp.py:
    - a hex numeral that is a pc-relative data target of a compared function with no symbol home (an anonymous .rodata
      constant or a .got cell), or a call target whose function name has several copies, takes the target's value at
      the same word of the paired function (alreloc's `gap` rule maps a .got cell by its offset in .got, wrong when the
      two .got sections differ in layout);
    - these keep their value: the --model numerals, every numeral >= 0x10000 of a file's leading comment block
      (inherited header and notice lines stay byte for byte; an `A..B` range start there names the image, `@<build>`),
      and every numeral >= 0x10000 of a --keep-all file.
 Output: DIR/<tag>-<I>.tsv (one row per range), DIR/resolve-<I>.txt, DIR/<tag>-<I>.txt (summary). The summary also gives
 the totals of words that differ only by a pc-relative offset (walked words; whole functions): the rule-24 closeness
 measure between donors whose compares all pass (fewer such words = the closer code layout)."""
import argparse, hashlib, importlib.util, os, re, subprocess, sys
from elftools.elf.elffile import ELFFile

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('strictcmp3', os.path.join(os.environ['KIT'], 'strictcmp3.py'))
sc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(sc)


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


class Elf:
    def __init__(self, path):
        self.e = ELFFile(open(path, 'rb'))
        self.segs = [(g['p_vaddr'], g['p_filesz'], g.data()) for g in self.e.iter_segments() if g['p_type'] == 'PT_LOAD']
        st = self.e.get_section_by_name('.symtab')
        self.syms = [] if st is None else [(s['st_value'], s['st_size'], s.name, s['st_info']['type'])
                                            for s in st.iter_symbols() if s['st_value'] and s.name and not s.name.startswith('$')]

    def word(self, a):
        for v, fz, d in self.segs:
            if v <= a and a + 4 <= v + fz:
                return int.from_bytes(d[a - v:a - v + 4], 'little')
        raise KeyError(hex(a))

    def funcs(self, name):
        return [x for x in self.syms if x[2] == name and x[3] == 'STT_FUNC' and x[1] > 0]

    def containing(self, a):
        c = [x for x in self.syms if x[3] == 'STT_FUNC' and x[0] <= a < x[0] + x[1]]
        return min(c, key=lambda x: x[1]) if c else None

    def home(self, a):
        return any(x[0] <= a < x[0] + max(x[1], 1) for x in self.syms if x[3] in ('STT_FUNC', 'STT_OBJECT', 'STT_TLS'))


def alloc_equal(p1, p2):
    def secs(p):
        e = ELFFile(open(p, 'rb'))
        return {s.name: (s['sh_addr'], s['sh_size'], b'' if s['sh_type'] == 'SHT_NOBITS' else s.data())
                for s in e.iter_sections() if s['sh_flags'] & 2 and s.name != '.note.gnu.build-id'}
    a, b = secs(p1), secs(p2)
    bad = sorted(set(a) ^ set(b)) + sorted(n for n in a if n in b and a[n] != b[n])
    return not bad, ' '.join(bad)


def sx(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >> (bits - 1) else v


def jal_t(w, pc):
    v = (((w >> 31) & 1) << 20) | (((w >> 12) & 0xff) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3ff) << 1)
    return (pc + sx(v, 21)) % (1 << 64)


def body_targets(img, a, n):
    """{word index: (kind, target)} of the jal words and of the auipc + load / addi / store pairs of the body at a."""
    ws = [img.word(a + 4 * i) for i in range(n)]
    out = {}
    for i, w in enumerate(ws):
        if w & 0x7f == 0x6f:
            out[i] = ('jal', jal_t(w, a + 4 * i))
        elif w & 0x7f == 0x17:
            rd, hi = (w >> 7) & 31, a + 4 * i + sx(w & 0xfffff000, 32)
            for j in range(i + 1, min(i + 4, n)):
                u = ws[j]
                if (u & 0x7f) in (0x03, 0x07, 0x13) and (u >> 15) & 31 == rd:
                    out[i] = ('pcrel', (hi + sx(u >> 20, 12)) % (1 << 64))
                    break
                if (u & 0x7f) in (0x23, 0x27) and (u >> 15) & 31 == rd:
                    out[i] = ('pcrel', (hi + sx(((u >> 25) << 5) | ((u >> 7) & 31), 12)) % (1 << 64))
                    break
    return out


def git_show(hub, ref, path):
    return subprocess.check_output(['git', '-C', hub, 'show', '%s:%s' % (ref, path)]).decode()


def numval(tok):
    return int(tok, 16) if tok.startswith('0x') else int(tok)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--hub', required=True)
    ap.add_argument('--ref', required=True)
    ap.add_argument('--src', required=True, metavar='P/H')
    ap.add_argument('--img', required=True, choices=['A', 'B'])
    ap.add_argument('--cls', required=True, type=int)
    ap.add_argument('--donor', nargs=2, required=True, metavar=('PINNED', 'TWIN'))
    ap.add_argument('--target', nargs=2, required=True, metavar=('PINNED', 'TWIN'))
    ap.add_argument('--out', required=True)
    ap.add_argument('--tables', nargs='+', required=True, metavar='FILE[:VAR]')
    ap.add_argument('--reloc', nargs='*', default=[], metavar='FILE')
    ap.add_argument('--keep-all', nargs='*', default=[], metavar='FILE')
    ap.add_argument('--model', metavar='FILE')
    ap.add_argument('--tag')
    ap.add_argument('--donor-lib')
    a = ap.parse_args()
    tag = a.tag or 'class%d' % a.cls
    donor_lib = a.donor_lib or 'proofs/%s/lib' % a.src
    model = {}
    if a.model:
        for line in open(a.model):
            line = line.split('#', 1)[0].strip()
            if line:
                tok, _, why = line.partition(' ')
                model[tok] = why.strip()
    os.makedirs(a.out, exist_ok=True)
    fails, log = [], []
    for side, (pinned, twin) in (('donor', a.donor), ('target', a.target)):
        ok, why = alloc_equal(pinned, twin)
        log.append('%s: pinned sha256 %s, twin sha256 %s, allocated sections equal (build-id note excepted): %s'
                   % (side, sha(pinned)[:12], sha(twin)[:12], ok))
        if not ok:
            fails.append('%s: pinned and twin differ: %s' % (side, why))
    D, T = Elf(a.donor[1]), Elf(a.target[1])
    I = {'D': sc.Img(a.donor[1]), 'T': sc.Img(a.target[1])}

    texts = {f: git_show(a.hub, a.ref, '%s/%s' % (donor_lib, f)) for f in a.reloc}
    ranges = []
    for spec in a.tables:
        f, _, var = spec.partition(':')
        var = var or 'fs_ranges'
        t = texts[f] if f in texts else git_show(a.hub, a.ref, '%s/%s' % (donor_lib, f))
        m = re.search(r'Definition\s+%s\s*:\s*list\s*\(Z\s*\*\s*nat\)\s*:=(.*?)\.\s*\n' % var, t, re.S)
        if not m:
            fails.append('no %s in %s' % (var, f))
            continue
        ranges += [(f, int(s, 16), int(n)) for s, n in re.findall(r'\((0x[0-9a-f]+),\s*(\d+)%nat\)', m.group(1))]

    body = '__asan_stack_malloc_%d' % a.cls
    d, t = D.funcs(body), T.funcs(body)
    callmap, datamap = {}, {}
    if len(d) != 1 or len(t) != 1 or d[0][1] != t[0][1]:
        fails.append('%s: donor %d copies, target %d copies, or the sizes differ' % (body, len(d), len(t)))
    else:
        da, ta, n = d[0][0], t[0][0], d[0][1] // 4
        dt, tt = body_targets(D, da, n), body_targets(T, ta, n)
        for i in sorted(set(dt) | set(tt)):
            if i not in dt or i not in tt or dt[i][0] != tt[i][0]:
                fails.append('%s word %d: pc-relative form differs' % (body, i))

    # pass 1: the ranges whose function name has one copy on each side; their whole bodies give the call map
    pairs, later = {}, []
    for k, (f, s, n) in enumerate(ranges):
        fn = D.containing(s)
        if fn is None:
            fails.append('%s range 0x%x: in no function' % (f, s))
            continue
        dcopies, tcopies = D.funcs(fn[2]), T.funcs(fn[2])
        if len(dcopies) == 1 and len(tcopies) == 1:
            pairs[k] = ('name', fn, tcopies[0], tcopies[0][0] + (s - fn[0]))
        else:
            later.append((k, fn, dcopies, tcopies))
    seen_fn = set()

    def harvest(fn, tfn):
        if (fn[0], tfn[0]) in seen_fn or tfn[1] != fn[1]:
            return
        seen_fn.add((fn[0], tfn[0]))
        dt, tt = body_targets(D, fn[0], fn[1] // 4), body_targets(T, tfn[0], fn[1] // 4)
        for i in set(dt) & set(tt):
            if dt[i][0] == tt[i][0]:
                (callmap if dt[i][0] == 'jal' else datamap).setdefault(dt[i][1], set()).add(tt[i][1])
    for k in sorted(pairs):
        harvest(pairs[k][1], pairs[k][2])
    # pass 2: several copies of the name: the call that reaches the range start, from a name-paired body
    for k, fn, dcopies, tcopies in later:
        f, s, n = ranges[k]
        if s == fn[0] and s in callmap and len(callmap[s]) == 1:
            ts = next(iter(callmap[s]))
            tfn = T.containing(ts)
            if tfn is None or tfn[2] != fn[2] or ts != tfn[0]:
                fails.append('%s range 0x%x: the call pairs it with 0x%x, not a copy of %s' % (f, s, ts, fn[2]))
                continue
            pairs[k] = ('call', fn, tfn, ts)
            harvest(fn, tfn)
        else:
            fails.append('%s range 0x%x (%s): %d / %d copies and no call pairs it (call targets %s)'
                         % (f, s, fn[2], len(dcopies), len(tcopies), sorted(map(hex, callmap.get(s, ())))))

    rows, tot_r, tot_f, fn_done = [], 0, 0, set()
    for k in sorted(pairs):
        f, s, n = ranges[k]
        how, fn, tfn, ts = pairs[k]
        if tfn[1] != fn[1]:
            fails.append('%s range 0x%x: %s is %d bytes, its pair %d' % (f, s, fn[2], fn[1], tfn[1]))
            continue
        # the walk steps through these n words only: they pass when their own compare is clean, or when the whole
        # function's compare is clean (a range cut inside a function can end between an auipc and the word that consumes
        # it, which the range compare alone reports as unmeasured); both verdicts are recorded
        v, cnt, cls, diff = sc.tcmp(I, 'D', s, 'T', ts, 4 * n)
        cnt = cnt or (0, 0, 0)
        fv, fc, fcl, fd = sc.tcmp(I, 'D', fn[0], 'T', tfn[0], fn[1])
        fc = fc or (0, 0, 0)
        clean = lambda v_, c_, d_: v_ in ('EQUAL', 'EQUAL-mod-pcrel') and c_[1] == 0 and c_[2] == 0 and not d_
        if not (clean(v, cnt, diff) or clean(fv, fc, fd)):
            fails.append('%s range 0x%x (%s): range %s %s %d differ; function %s %s %d differ'
                         % (f, s, fn[2], v, cnt, len(diff), fv, fc, len(fd)))
        tot_r += cnt[0]
        if fn[0] not in fn_done:
            fn_done.add(fn[0])
            tot_f += fc[0]
        fnote = '; '.join(['range: ' + ', '.join('%s %s' % (x[0], x[3]) for x in diff)] * bool(diff) +
                          ['function: ' + ', '.join('%s %s' % (x[0], x[3]) for x in fd)] * bool(fd))
        rows.append((f, '0x%x' % s, n, fn[2], '+0x%x' % (s - fn[0]), how, '0x%x' % ts, '0x%x' % fn[0], '0x%x' % tfn[0],
                     fn[1], v, cnt[0], cnt[1], cnt[2], len(diff), '%s (%d, %d, %d) %d' % (fv, fc[0], fc[1], fc[2], len(fd)),
                     fnote))

    want = {}
    for dv, tvs in datamap.items():
        if not D.home(dv):
            if len(tvs) != 1:
                fails.append('data target 0x%x: target values %s' % (dv, sorted(map(hex, tvs))))
                continue
            want['0x%x' % dv] = '0x%x' % next(iter(tvs))
    for dv, tvs in callmap.items():
        fn = D.containing(dv)
        if fn and len(D.funcs(fn[2])) > 1 and len(tvs) == 1:
            want['0x%x' % dv] = '0x%x' % next(iter(tvs))
    res = []
    for f in a.reloc:
        lines = texts[f].split('\n')
        head = next(k for k, l in enumerate(lines) if l.startswith(('From ', 'Require ')))
        for k, line in enumerate(lines, 1):
            # the two ends of an `A..B` range: alreloc's range rule maps them as one pair and takes no keep line for the
            # end, so in the header neither end is kept; the start's line names this image (`@<build>`), and smrun.sh
            # restores the header block from the donor after writing
            starts = set(re.findall(r'(0x[0-9a-fA-F]+)\s*\.\.\s*', line))
            rng = starts | set(re.findall(r'\.\.\s*(0x[0-9a-fA-F]+)', line))
            for tok in re.findall(r'\b(0x[0-9a-fA-F]+|\d+)\b', line):
                keep = (k <= head or f in a.keep_all) and numval(tok) >= 0x10000 and not (k <= head and tok in rng)
                if keep or tok in model:
                    res.append((f, k, tok, tok))
                elif k <= head and tok in starts:
                    res.append((f, k, tok, '@asan' if a.img == 'A' else '@asan-ubsan'))
                elif tok in want:
                    res.append((f, k, tok, want[tok]))
    res = sorted(set(res), key=lambda r: (r[0], r[1], r[2]))

    hdr = ['file', 'donor_range', 'words', 'function', 'offset', 'paired_by', 'target_range', 'donor_fn', 'target_fn',
           'fn_bytes', 'verdict', 'pcrel', 'real', 'unmeasured', 'targets_differ', 'whole_fn (pcrel, real, unmeasured) differ',
           'note']
    open(os.path.join(a.out, '%s-%s.tsv' % (tag, a.img)), 'w').write(
        '\t'.join(hdr) + '\n' + ''.join('\t'.join(map(str, r)) + '\n' for r in rows))
    open(os.path.join(a.out, 'resolve-%s.txt' % a.img), 'w').write(
        ''.join('[%s] %s:%d %s %s\n' % ((a.src,) + r) for r in res))
    mv = [r for r in res if r[2] != r[3] and not r[3].startswith('@')]
    moved = sorted({(r[2], r[3]) for r in mv})
    summ = log + ['%s ref %s image %s class %d: %d of %d ranges paired and compared; pc-relative words %d (walked), %d '
                  '(whole functions)' % (a.src, a.ref, a.img, a.cls, len(rows), len(ranges), tot_r, tot_f),
                  '%d resolve lines: %d move a value (%s), %d name the image of a header range, the rest keep the value'
                  % (len(res), len(mv), ', '.join('%s -> %s' % m for m in moved),
                     sum(1 for r in res if r[3].startswith('@')))]
    summ += ['FAIL: ' + x for x in fails] or ['PASS']
    open(os.path.join(a.out, '%s-%s.txt' % (tag, a.img)), 'w').write('\n'.join(summ) + '\n')
    print('\n'.join(summ))
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
