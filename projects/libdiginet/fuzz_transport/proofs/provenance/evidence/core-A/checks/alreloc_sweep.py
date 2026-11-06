#!/usr/bin/env python3
"""A wider planted control of the alreloc cross-check (libdiginet/fuzz_transport image-A core): N positions picked at
random (seeded) among the positions the base run decided `port_core right` whose stage-out value is an image value,
each written into a COPY of stage-out as value + 8 (same notation). Kind: measurement; it proves no function.

  alreloc_sweep.py --rows OUT/alreloc-crosscheck-rows.tsv --stage-out COPY --n N --seed S --plants PLANTS.tsv

A position qualifies when: its decision is `port_core right`, its stage-out value lies in [0x10000, 0x7fffffffffff),
it is not inside a comment (groups notice / comment / other-image-comment), its stage-out line holds no other plant.
PLANTS.tsv has the columns of alreloc_plant.py's (plant, file, out_line, tok, port_core, planted, why), so
alreloc-xcheck-control.sh's verdict reads it the same way (SWEEP="N SEED").
"""
import argparse, os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from alreloc_decide import TOK, val, hx  # noqa: E402

SKIP = ('notice', 'comment', 'other-image-comment')


def main():
    ap = argparse.ArgumentParser()
    for k in ('rows', 'stage-out', 'n', 'seed', 'plants'):
        ap.add_argument('--' + k, required=True)
    a = ap.parse_args()
    L = open(a.rows).read().split('\n')
    h = L[0].split('\t')
    rows = [dict(zip(h, l.split('\t'))) for l in L[1:] if l]
    cand = [r for r in rows if r['decision'].startswith('port_core right') and r['out_line'] != '-' and
            r['port_core'] != '-' and r['group'] not in SKIP and 0x10000 <= val(r['port_core']) < 0x7fffffffffff]
    rng = random.Random(int(a.seed))
    rng.shuffle(cand)
    picked, lines = [], set()
    for r in cand:
        f = r['file'].split('/lib/', 1)[-1]
        if (f, r['out_line']) in lines:
            continue
        lines.add((f, r['out_line']))
        picked.append((f, r))
        if len(picked) == int(a.n):
            break
    with open(a.plants, 'w') as fh:
        fh.write('plant\tfile\tout_line\ttok\tport_core\tplanted\twhy\n')
        for f, r in sorted(picked, key=lambda x: (x[0], int(x[1]['out_line']))):
            p = os.path.join(a.stage_out, f)
            S = open(p).read().split('\n')
            i = int(r['out_line']) - 1
            m = list(TOK.finditer(S[i]))[int(r['tok'])]
            assert m.group(1) == r['port_core'], (f, r['out_line'], m.group(1), r['port_core'])
            v = val(r['port_core']) + 8
            new = hx(v) if r['port_core'][:2].lower() == '0x' else str(v)
            S[i] = S[i][:m.start()] + new + S[i][m.end():]
            open(p, 'w').write('\n'.join(S))
            fh.write('\t'.join(['sweep:' + r['group'], f, r['out_line'], r['tok'], r['port_core'], new,
                                'value + 8 (base decision: %s)' % r['decision'][:60].replace('\t', ' ')]) + '\n')
    print('alreloc_sweep.py: %d candidates, %d planted (seed %s)' % (len(cand), len(picked), a.seed))


if __name__ == '__main__':
    main()
