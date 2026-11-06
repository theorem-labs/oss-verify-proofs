#!/usr/bin/env python3
"""luiscan.py -- exposure of strictcmp3.py's rule 8 (lui-built absolute values) per image and function, so that a record
that compared on cmpkit 4bbd3a74be89 (strictcmp2.py, which compares every lui word raw) can decide in one run whether a
function needs a re-run. Uses strictcmp3.py's own `lui_scan` (loaded from this directory), so the counts are exactly the
targets strictcmp3 forms. Read-only.

Per sized FUNC symbol (one row per address):
  luis         lui words in the function
  insec (a)    lui targets (pairs and lone lui values) whose value lies in an allocated SECTION of this image: what
               strictcmp3 compares as an address
  inload       the same under the literal test of the unit owner's ruling, any PT_LOAD [p_vaddr, p_vaddr + p_memsz); inload - insec
               is the values in no section (the ELF header, inter-section padding), which name no object
  memfed (b)   lui targets used as a memory / jump base: a load / store / jalr pair, an addi / addiw pair whose result is
               the base of a load / store / jalr / AMO, or a lui read directly as an AMO address
  memfed_out   memory-fed targets in no section of this image (strictcmp3: no image object, a difference)
  luiconst     in-section targets the dataflow settles as constants (every use logical / shift / compare, the unit owner's ruling)
               : `lui-const (dataflow)`, not a difference
  unmeasured   lui words of a function that holds a 2-byte parcel (rule 8 does not follow registers through them)
  exposure     targets that are (a) or (b), plus unmeasured words: what strictcmp3 compares that strictcmp2 did not
A pair compare uses both images: strictcmp3 treats a lui target as an address when EITHER image's value is in a section,
so scan both images of each pair. exposure 0 for a function in BOTH images = rule 8 leaves its strictcmp2 verdict
unchanged (no re-run needed for rule 8; strictcmp3's other changes - the string-label NAME-ONLY rule, ESC in C strings,
the combined verdict, refusing an ambiguous FNLIST name - need a strictcmp3 re-run or `ambiscan.py`).
usage: luiscan.py [--all] [--fns ITEM,ITEM,...] ELF [ELF ...]
  --fns   only these functions (NAME, NAME{FILE} or 0xADDR, as strictcmp3 cmp takes them; every copy of a NAME that
          several functions carry is scanned and marked)
  --all   a row for every function (default: only functions with luis > 0)
Output: TSV rows `ROW image function addr size luis insec inload memfed memfed_out luiconst unmeasured exposure`, one `TOTAL` per
image (functions scanned, functions with a lui, functions with exposure > 0, column sums) and a final `TOTAL all` line."""
import sys, os, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('strictcmp3', os.path.join(HERE, 'strictcmp3.py'))
s3 = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(s3)

def scan(I, a, z):
    b = s3.frd(I, a, z)
    if b is None: return None
    tg, unm = s3.lui_scan(b)
    luis = sum(1 for o, x, n in s3.bc_words(b) if n == 4 and x & 0x7f == 0x37)
    ins = {i for i, (k, v, m, g) in tg.items() if s3.insec(I, v)}
    inl = {i for i, (k, v, m, g) in tg.items() if s3.inload(I, v)}
    mem = {i for i, (k, v, m, g) in tg.items() if m}
    con = {i for i, (k, v, m, g) in tg.items() if g and not m}      # settled as a constant by the dataflow
    return luis, len(ins), len(inl), len(mem), len(mem - ins), len(ins & con), len(unm), len((ins | mem) - con) + len(unm)

def main(argv):
    allrows = '--all' in argv; argv = [x for x in argv if x != '--all']; fns = None
    if '--fns' in argv:
        k = argv.index('--fns'); fns = argv[k + 1].split(','); argv = argv[:k] + argv[k + 2:]
    if not argv: raise SystemExit(__doc__)
    print('ROW\timage\tfunction\taddr\tsize\tluis\tinsec\tinload\tmemfed\tmemfed_out\tluiconst\tunmeasured\texposure')
    grand = [0] * 11
    for p in argv:
        I = s3.Img(p); tag = os.path.basename(p)
        print('# image %s sha256 %s' % (p, s3.sha(p)[:12]))
        if fns is None:
            fl = sorted({(v, z) for v, z, nm, t in I.syms if t == 'STT_FUNC' and z > 0})
            names = {}
            for v, z, nm, t in I.syms:
                if t == 'STT_FUNC' and z > 0: names.setdefault((v, z), nm)
            items = [(v, z, names[(v, z)], '') for v, z in fl]
        else:
            items = []
            for f in fns:
                c = s3.fcopies(I, f)
                if not c: print('ABSENT\t%s\t%s' % (tag, f))
                for v, z, nm in c: items.append((v, z, nm, ' (one of %d copies of %s)' % (len(c), f) if len(c) > 1 else ''))
        tot = [0] * 11
        for v, z, nm, note in items:
            r = scan(I, v, z)
            if r is None:
                print('UNREADABLE\t%s\t%s\t%#x\t%d' % (tag, nm, v, z)); continue
            tot[0] += 1; tot[1] += r[0] > 0; tot[2] += r[7] > 0
            for j in range(8): tot[3 + j] += r[j]
            if allrows or r[0]:
                print('ROW\t%s\t%s%s\t%#x\t%d\t%s' % (tag, s3.qname(I, nm, v) or nm, note, v, z, '\t'.join(map(str, r))))
        print('TOTAL\t%s\tfunctions %d\twith-lui %d\twith-exposure %d\tluis %d\tinsec %d\tinload %d\tmemfed %d'
              '\tmemfed_out %d\tluiconst %d\tunmeasured %d\texposure %d' % ((tag,) + tuple(tot)))
        grand = [g + t for g, t in zip(grand, tot)]
    print('TOTAL\tall\tfunctions %d\twith-lui %d\twith-exposure %d\tluis %d\tinsec %d\tinload %d\tmemfed %d'
          '\tmemfed_out %d\tluiconst %d\tunmeasured %d\texposure %d' % tuple(grand))

if __name__ == '__main__':
    main(sys.argv[1:])
