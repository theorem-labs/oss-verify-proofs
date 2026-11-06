#!/usr/bin/env python3
"""kitsum.py -- per row of a strictcmp2.py cmp output: the kit verdict, the settled verdict, and the old record's verdict
for the same pair.

Kit verdict SAME: strictcmp2 verdict EQUAL or EQUAL-mod-pcrel, real 0, unmeasured 0 and target-differ 0 (every
pc-relative target the same symbol + offset, or equal bytes under the kit's rules); anything else NOT-SAME, with the
kinds of its target differences. Settled verdict: the kit verdict when it is SAME; else SAME only when every target
difference of the row has a settle.py row (SETTLED.tsv) whose verdict starts with SAME; else NOT-SAME. An old record is
matched on its (address 1, address 2) columns, so a pair whose addresses the kit's Img.fsym does not give is MISSING.
re-run: SAME when the settled verdict is SAME and every old verdict is EQUAL / EQUAL-mod-pcrel; CHANGED when the settled
verdict is NOT-SAME and the old verdicts said EQUAL / EQUAL-mod-pcrel.

Usage: kitsum.py OUT.tsv SETTLED.tsv [LABEL=OLD.tsv:ADDR1COL:ADDR2COL:VERDICTCOL ...]"""
import ast, collections, csv, sys

SAMEV = ('EQUAL', 'EQUAL-mod-pcrel')


def kit_rows(path):
    rows = []
    for line in open(path):
        if line.startswith(('#', 'fn\t', 'CSTR\t')):
            continue
        c = line.rstrip('\n').split('\t')
        if len(c) < 7:
            continue
        v = c[6]
        if v in ('ABSENT', 'SIZE') or len(c) < 12:
            rows.append(dict(fn=c[0], pair=c[1], a1=c[2], a2=c[3], v=v, pcrel='', real='', unm='', nd=0, words=[],
                             kinds=v, kit='NOT-SAME'))
            continue
        d = [] if c[11] == '0' else ast.literal_eval(c[11])
        kinds = collections.Counter(x[3] for x in d)
        same = v in SAMEV and c[8] == '0' and c[9] == '0' and not d
        rows.append(dict(fn=c[0], pair=c[1], a1=c[2], a2=c[3], v=v, pcrel=c[7], real=c[8], unm=c[9], nd=len(d),
                         words=[x[0] for x in d], kinds=' '.join('%s:%d' % kv for kv in sorted(kinds.items())) or '-',
                         kit='SAME' if same else 'NOT-SAME'))
    return rows


def main():
    rows = kit_rows(sys.argv[1])
    st = collections.defaultdict(dict)
    for r in csv.DictReader(open(sys.argv[2]), delimiter='\t'):
        st[(r['pair'], r['addr1'], r['addr2'])][r['word']] = (r['measurement'], r['settled'])
    old = []
    for spec in sys.argv[3:]:
        label, rest = spec.split('=', 1)
        path, c1, c2, cv = rest.rsplit(':', 3)
        t = list(csv.DictReader(open(path), delimiter='\t'))
        old.append((label, {(int(r[c1], 16), int(r[c2], 16)): r[cv] for r in t}))
    print('fn\tpair\taddr1\taddr2\tstrictcmp2\tpcrel\treal\tunmeasured\ttarget-differ\tdiffer-kinds\tkit\tsettled\t'
          + ''.join('old %s\t' % l for l, _ in old) + 're-run')
    seen = {l: set() for l, _ in old}
    tally = collections.Counter()
    for r in rows:
        if r['kit'] == 'SAME':
            sv = 'SAME (kit)'
        else:
            s = st.get((r['pair'], r['a1'], r['a2']), {})
            ok = r['nd'] > 0 and r['real'] == '0' and r['unm'] == '0' and r['v'] in SAMEV and \
                all(wd in s and s[wd][1].startswith('SAME') for wd in r['words'])
            sv = 'SAME (settled: %s)' % ', '.join('%s %s' % (wd, s[wd][0]) for wd in r['words']) if ok else 'NOT-SAME'
        k = (int(r['a1'], 16), int(r['a2'], 16)) if r['a1'] not in ('None', '') and r['a2'] not in ('None', '') else None
        ov = []
        for l, t in old:
            if k in t:
                seen[l].add(k)
            ov.append(t.get(k, 'MISSING'))
        allold = all(o in SAMEV for o in ov)
        tag = ('SAME' if sv.startswith('SAME') else 'CHANGED') if allold else 'CHECK'
        tally[tag] += 1
        print('\t'.join(str(x) for x in (r['fn'], r['pair'], r['a1'], r['a2'], r['v'], r['pcrel'], r['real'], r['unm'],
                                         r['nd'], r['kinds'], r['kit'], sv)) + ''.join('\t' + o for o in ov) + '\t' + tag)
    for l, t in old:
        for k in sorted(set(t) - seen[l]):
            tally['MISSING'] += 1
            print('MISSING\t%s\t%#x\t%#x\told verdict %s: no kit row at these addresses' % (l, k[0], k[1], t[k]))
    n = collections.Counter(r['kit'] for r in rows)
    print('# rows %d; kit %s; re-run %s' % (len(rows), dict(sorted(n.items())), dict(sorted(tally.items()))))


if __name__ == '__main__':
    main()
