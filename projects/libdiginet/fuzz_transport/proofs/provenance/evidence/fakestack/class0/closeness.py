#!/usr/bin/env python3
"""closeness.py -- the rule-24 closeness measure over cands.sh's outputs.

usage: closeness.py CLS OUTDIR        (OUTDIR/<H>-<I>/class<CLS>-<I>.tsv as smcmp.py writes, one per candidate)

Every candidate's walked code is EQUAL or EQUAL-mod-pcrel to fuzz_transport's where its compare passes: the same
instruction words but for pc-relative offsets. The measure is taken over what each relocation carries, the donor's own
code table:
 1. the walked words (the words the relocated walk executes) that differ by a pc-relative offset; fewer is closer;
 2. tie-break: the whole functions those ranges lie in: first their differing targets (a target strictcmp3 reports as
    different, even outside the walked words), then their words that differ by a pc-relative offset.
For information it also prints the same two counts over only the functions every candidate of the image walks. A
candidate whose compare fails is listed, not ranked: its table does not relocate whole."""
import csv, glob, os, sys


def counts(v, only=None):
    seen, w, f, t = set(), 0, 0, 0
    for x in v:
        if only is not None and x['function'] not in only:
            continue
        w += int(x['pcrel'])
        if x['function'] not in seen:
            seen.add(x['function'])
            wf = x['whole_fn (pcrel, real, unmeasured) differ']
            f += int(wf.split('(')[1].split(',')[0])
            t += int(wf.rsplit(')', 1)[1])
    return w, t, f


def main():
    cls, out = int(sys.argv[1]), sys.argv[2]
    rows, passed = {}, {}
    for p in sorted(glob.glob(os.path.join(out, '*', 'class%d-*.tsv' % cls))):
        k = os.path.basename(os.path.dirname(p))
        rows[k] = list(csv.DictReader(open(p), delimiter='\t'))
        passed[k] = open(p[:-4] + '.txt').read().rstrip().endswith('PASS')
    for img in 'AB':
        ds = {k: v for k, v in rows.items() if k.endswith('-' + img)}
        if not ds:
            continue
        common = set.intersection(*[set(x['function'] for x in v) for v in ds.values()])
        print('class %d image %s (own table: walked words differing by a pc-relative offset; whole functions: differing '
              'targets, words differing by a pc-relative offset | the same over the %d functions every candidate walks)'
              % (cls, img, len(common)))
        res = []
        for k, v in ds.items():
            w, t, f = counts(v)
            cw, ct, cf = counts(v, common)
            body = next(('%s -> %s' % (x['donor_fn'], x['target_fn']) for x in v
                         if x['function'] == '__asan_stack_malloc_%d' % cls), '?')
            res.append((not passed[k], w, t, f, k, len(v), cw, ct, cf, body))
        for rank, (failed, w, t, f, k, n, cw, ct, cf, body) in enumerate(sorted(res), 1):
            print('  %-17s %-20s %2d ranges: walked %3d; whole: %d targets, %3d | common: walked %3d; whole: %d, %3d; '
                  '__asan_stack_malloc_%d %s' % ('FAIL (not ranked)' if failed else str(rank), k, n, w, t, f, cw, ct, cf,
                                                 cls, body))
        print('  functions every candidate walks: %s' % ' '.join(sorted(common)))


if __name__ == '__main__':
    main()
