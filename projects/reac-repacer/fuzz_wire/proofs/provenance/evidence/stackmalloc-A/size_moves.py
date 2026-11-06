#!/usr/bin/env python3
"""size_moves.py OUT.tsv RUN... -- every numeral a port_core relocation CHANGED whose DONOR value is a power of two or
page-aligned (a multiple of 0x1000): the moves an address gate can pass although a size / length / bound / mask must
not move (port_addr_check 0d24592683b6 reads a consistent size move as SAME-SYMBOL).

RUN = NAME=DIR, a port_core work directory: DIR/stage/<F> is the donor text staged at its target path (the stage map),
DIR/stage-out/<F> the relocated text, DIR/{check,fixed,review,decimals}.tsv the run's own rows. The two texts are
aligned by difflib over lines (port_core rewrites numerals in place and adds header lines): every replaced block of
equal length is paired line by line (a block of unequal length is reported), and inside a paired line the numerals
are paired in order (a line whose numeral count changed is reported). For each move whose donor value v satisfies v > 0 and
(v & (v - 1) == 0 or v % 0x1000 == 0): the run, file:line, donor and wire value, the run's own row for it (status /
symbol), and where that relocated line is in the FINAL tree (FINAL/<F>, by exact line text; `-` if the final file
does not carry the line, e.g. a knock hunk not taken).
"""
import difflib, os, re, sys

NUM = re.compile(r"(?<![\w.'])(0x[0-9a-fA-F]+|\d+)(?![\w'])")


def val(s):
    return int(s, 16) if s.lower().startswith('0x') else int(s)


def sized(v):
    return v > 0 and (v & (v - 1) == 0 or v % 0x1000 == 0)


def rows_of(d):
    out = {}
    for t in ('check.tsv', 'fixed.tsv', 'review.tsv', 'decimals.tsv'):
        p = os.path.join(d, t)
        if not os.path.exists(p):
            continue
        L = open(p).read().splitlines()
        h = L[0].split('\t')
        for l in L[1:]:
            r = dict(zip(h, l.split('\t')))
            try:
                k = (r['file'], int(r['line']), val(r['old']), val(r['new']))
            except (KeyError, ValueError):
                continue
            out.setdefault(k, []).append('%s:%s %s' % (t[:-4], r.get('status', r.get('action', '-'))[:60],
                                                       r.get('new_sym', '-')))
    return out


def main():
    out, final, runs = sys.argv[1], sys.argv[2], sys.argv[3:]
    fin_cache = {}
    res, unpaired = [], []
    for spec in runs:
        name, d = spec.split('=', 1)
        tab = rows_of(d)
        st = os.path.join(d, 'stage')
        for dp, _, fn in os.walk(st):
            for f in sorted(fn):
                if not f.endswith('.v'):
                    continue
                rel = os.path.relpath(os.path.join(dp, f), st)
                so = os.path.join(d, 'stage-out', rel)
                if not os.path.exists(so):
                    continue
                a = open(os.path.join(dp, f), errors='replace').read().split('\n')
                b = open(so, errors='replace').read().split('\n')
                if rel not in fin_cache:
                    fp = os.path.join(final, rel)
                    fl = open(fp, errors='replace').read().split('\n') if os.path.exists(fp) else []
                    idx = {}
                    for i, l in enumerate(fl):
                        idx.setdefault(l, []).append(i + 1)
                    fin_cache[rel] = idx
                paired = []
                for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
                    if tag != 'replace':
                        continue
                    if i2 - i1 == j2 - j1:
                        paired += [(a[i1 + k], b[j1 + k], j1 + k + 1) for k in range(i2 - i1)]
                    else:
                        unpaired.append('%s %s: block %d-%d -> %d-%d' % (name, rel, i1 + 1, i2, j1 + 1, j2))
                for la, lb, ln in paired:
                    na, nb = NUM.findall(la), NUM.findall(lb)
                    if len(na) != len(nb):
                        unpaired.append('%s %s:%d numerals %d -> %d' % (name, rel, ln, len(na), len(nb)))
                        continue
                    for x, y in zip(na, nb):
                        vx, vy = val(x), val(y)
                        if vx == vy or not sized(vx):
                            continue
                        row = tab.get((rel, ln, vx, vy), ['-'])
                        fl = fin_cache[rel].get(lb, [])
                        res.append((name, rel, ln, x, y, '; '.join(row), ','.join(map(str, fl[:3])) or '-',
                                    lb.strip()[:220]))
    with open(out, 'w') as o:
        o.write('run\tfile\tstage-out line\tdonor\twire\trun row (status symbol)\tfinal-tree line(s)\tline text\n')
        for r in res:
            o.write('\t'.join(map(str, r)) + '\n')
    open(out + '.unpaired', 'w').write('\n'.join(unpaired) + '\n')
    print('size_moves: %d move(s) of a power-of-two / page-aligned donor value; %d block(s) / line(s) not paired '
          '(listed in %s.unpaired)' % (len(res), len(unpaired), os.path.basename(out)))


if __name__ == '__main__':
    main()
