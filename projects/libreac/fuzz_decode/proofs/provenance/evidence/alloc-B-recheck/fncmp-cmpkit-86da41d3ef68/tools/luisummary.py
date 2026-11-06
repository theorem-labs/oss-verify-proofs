#!/usr/bin/env python3
"""luisummary.py -- the RECORD.md tables of the lui settlement, from scans/luiclass.tsv: the class counts, and every NOT
CERTIFIED row with the kinds of its unsettled uses (a row can have several). Writes scans/luiclass-summary.md.
usage: luisummary.py"""
import collections, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common

KINDS = [('no field cited', 'a STORE into a field with no citation'),
         ('beyond its signature', 'a callee reads it beyond its signature (a variadic register save: ARG-BEYOND-READ)'),
         ('indirect call', 'an indirect call that may read the register (its pointer type unknown)'),
         ('depth / recursion', 'dead-at-call analysis cut (depth / recursion)'),
         ('no direct caller', 'handed back to a function with no direct caller'),
         ('depth limit', 'a follow-up left at the depth limit (4 levels)'),
         ('not followed', 'an argument not followed into its callee (a variadic argument)'),
         ('syscall', 'a syscall argument with no contract cited'),
         ('verdict', 'luitrace verdict REVIEW (a V-derived base, or the two traces differ)'),
         ('only this image has', 'a V-derived base in a follow-up only one image has'),
         ('path leaves', 'a path leaving a callee with the value live')]


def kind(u):
    for k, text in KINDS:
        if k in u:
            return text
    return 'dead-at-call analysis UNKNOWN (the cause at the end of the callee chain)'


def main():
    rows, tot, classes = [], collections.Counter(), collections.Counter()
    n = collections.Counter()
    for l in list(open(os.path.join(common.SCANS, 'luiclass.tsv')))[1:]:
        c = l.rstrip('\n').split('\t')
        src = 'lui-in-section' if c[4] == 'luitrace.tsv' else 'lui-const'
        n[src] += 1
        if not c[6].startswith('NOT'):
            classes[(src, c[6])] += 1
            continue
        n[src + ' NOT CERTIFIED'] += 1
        ks = collections.Counter(kind(u) for u in c[8].split(' ;; '))
        for k in ks:
            tot[k] += 1
        short = re.sub(r'^_ZN?K?\d+__(sanitizer|asan|lsan)', '', c[0])[:52]
        rows.append('| %s | %s | %s | %s | %s |' % (src, short, c[2], c[3], '; '.join('%s (%d)' % (k, m) for k, m in
                                                                                ks.most_common())))
    out = ['rows: %s' % dict(sorted(n.items())), '', '| kit row | class (the classes of its uses) | rows |', '|---|---|---|']
    out += ['| %s | %s | %d |' % (s, k, m) for (s, k), m in sorted(classes.items())]
    out += ['', '| reason (a NOT CERTIFIED row can have several) | rows |', '|---|---|']
    out += ['| %s | %d |' % (k, m) for k, m in tot.most_common()]
    out += ['', '| kit row | member | word | V | unsettled uses (how many of each kind) |', '|---|---|---|---|---|'] + rows
    open(os.path.join(common.SCANS, 'luiclass-summary.md'), 'w').write('\n'.join(out) + '\n')
    print('\n'.join(out[:3]))


if __name__ == '__main__':
    main()
