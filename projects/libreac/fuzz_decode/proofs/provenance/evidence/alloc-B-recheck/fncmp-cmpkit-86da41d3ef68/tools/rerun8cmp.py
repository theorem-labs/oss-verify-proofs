#!/usr/bin/env python3
"""rerun8cmp.py -- how this addendum relates to the 8-function re-run it extends: that re-run's log (alloc-reloc/B/
fncmp.cmpkit-4bbd3a74be89.log: strictcmp2 on S = the record's symtwin and on T = the donor's unstripped twin, each against
E = decode B's unstripped twin) and its settlements (alloc-reloc/cmpkit-4bbd3a74be89/settled.tsv).
For each of the 8 functions: this record's C:D row (out/<compare>-cmp.out; C = the donor's unstripped twin, D = decode B's
unstripped twin, i.e. the same image pair as T:E) beside the T:E and S:E rows, field by field (the WORD verdict, pcrel, real,
unmeasured, accepted targets, target differences, by word; strictcmp3 prints a COMBINED verdict in the verdict column and
the word verdict last, strictcmp2 only the word verdict, so the word verdicts are compared and the combined one is shown);
then each settled difference beside this record's measurement of the same word. Prints every row where they disagree.
usage: rerun8cmp.py  (RERUN8_LOG / RERUN8_SETTLED override the paths)"""
import ast, hashlib, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common

LOG = os.environ.get('RERUN8_LOG', os.path.join(common.HERE, '..', 'fncmp.cmpkit-4bbd3a74be89.log'))
SET = os.environ.get('RERUN8_SETTLED', os.path.join(common.HERE, '..', '..', 'cmpkit-4bbd3a74be89', 'settled.tsv'))
COLS = ['verdict', 'pcrel', 'real', 'unmeasured', 'targets', 'target-differ']


def rows_of(lines, pair):
    """the compare rows of one pair (their size columns are numbers; the kit-summary rows of the same pair are not)"""
    out = {}
    for l in lines:
        c = l.rstrip('\n').split('\t')
        if len(c) > 11 and c[1] == pair and c[0] != 'CSTR' and c[4].isdigit() and c[5].isdigit():
            td = c[11]
            words = sorted(x[0] for x in ast.literal_eval(td)) if td.startswith('[') else []
            wv = c[15] if len(c) > 15 and c[15] else c[6]              # strictcmp3: the word verdict is the last column
            out[c[0]] = dict(zip(COLS, [wv, c[7], c[8], c[9], c[10], ','.join(words) or '0']), combined=c[6])
    return out


def main():
    rr = open(LOG).read().split('\n')
    mine = rows_of(open(os.path.join(common.OUT, common.CMP_OUT)).read().split('\n'), 'C:D')
    T, S = rows_of(rr, 'T:E'), rows_of(rr, 'S:E')
    print('# the re-run log %s sha256 %s; its settled.tsv %s sha256 %s' % (
        os.path.basename(LOG), hashlib.sha256(open(LOG, 'rb').read()).hexdigest()[:12], os.path.basename(SET),
        hashlib.sha256(open(SET, 'rb').read()).hexdigest()[:12]))
    print('fn\tfield\tthis record (C:D)\tre-run T:E\tre-run S:E\tC:D vs T:E\tC:D vs S:E')
    for fn in sorted(mine):
        print('%s\tcombined verdict (this kit)\t%s' % (fn[:60], mine[fn]['combined']))
    dis = []
    for fn in sorted(set(mine) | set(T) | set(S)):
        for k in COLS:
            m, t, s = mine.get(fn, {}).get(k, '-'), T.get(fn, {}).get(k, '-'), S.get(fn, {}).get(k, '-')
            print('%s\t%s\t%s\t%s\t%s\t%s\t%s' % (fn[:60], k, m, t, s, 'same' if m == t else 'DIFFER', 'same' if m == s else 'DIFFER'))
            if m != t:
                dis.append(('T:E', fn, k, m, t))
            if m != s:
                dis.append(('S:E', fn, k, m, s))
    print('## re-run settlements beside this record (bytes read from the images by this script)')
    import importlib.util, re
    sc = common.kit_module(common.CMP_PY)
    C, D = sc.Img(common.CGIF_B_TWIN), sc.Img(common.DECODE_B_TWIN)
    hdr = None
    for l in open(SET):
        c = l.rstrip('\n').split('\t')
        if hdr is None:
            hdr = c; continue
        d = dict(zip(hdr, c))
        b1 = re.findall(r'bytes ([0-9a-f]+)', d['side 1']); b2 = re.findall(r'bytes ([0-9a-f]+)', d['side 2'])
        g1 = re.findall(r'cell (0x[0-9a-f]+) \(\.got\), 8 file bytes ([0-9a-f]+)', d['side 1'])
        g2 = re.findall(r'cell (0x[0-9a-f]+) \(\.got\), 8 file bytes ([0-9a-f]+)', d['side 2'])
        line = '%s %s +%s: the re-run measurement %s, settled %s' % (d['pair'], d['fn'][:60], d['word'], d['measurement'], d['settled'])
        if b1 and b2 and re.search(r'table 0x', d['side 1']) and re.search(r'table 0x', d['side 2']):
            t1 = re.findall(r'table (0x[0-9a-f]+)', d['side 1'])[0]; t2 = re.findall(r'table (0x[0-9a-f]+)', d['side 2'])[0]
            mine = sc.frd(C, int(t1, 16), len(b1[0]) // 2).hex(), sc.frd(D, int(t2, 16), len(b2[0]) // 2).hex()
            line += '; re-run table %s / %s, %d bytes; the images here: %s' % (t1, t2, len(b1[0]) // 2,
                                                                             'IDENTICAL to the re-run' if mine == (b1[0], b2[0]) else 'DIFFER')
        if g1 and g2:
            mine = sc.frd(C, int(g1[0][0], 16), 8).hex(), sc.frd(D, int(g2[0][0], 16), 8).hex()
            line += '; re-run .got cells %s / %s = %s / %s; the images here: %s' % (g1[0][0], g2[0][0], g1[0][1], g2[0][1],
                                                                               'IDENTICAL to the re-run' if mine == (g1[0][1], g2[0][1]) else 'DIFFER')
        print(line)
    print('## disagreements (this record C:D against re-run T:E / S:E): %d' % len(dis))
    for d in dis:
        print('  %s %s %s: this record %s, re-run %s' % d)


if __name__ == '__main__':
    main()
