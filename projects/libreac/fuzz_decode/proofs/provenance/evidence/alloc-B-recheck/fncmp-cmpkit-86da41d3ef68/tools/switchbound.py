#!/usr/bin/env python3
"""switchbound.py -- an independent measurement of every rel4 jump table of this record whose bound the kit's jtcheck
does not give (it refused the table) or whose bound settle.py's adjacent-guard pattern does not find: the bound comes from
the code by data-flow, not from a fixed pattern.
For each (function, table word) in out/fulldiff.tsv whose measurement is `indexed load with no bound found` or a
rel4-jump table, in BOTH images, by address:
  1. the dispatch after the table word: `slli i2, i, 2 ; add p, i2, T ; lw e, 0(p) ; add t, e, T ; jr t` (T = the table
     register the word writes);
  2. the guard: the `bltu B, i` (or `bgeu i, B` taken to the default) on every path before the dispatch that bounds i,
     found as the last branch on i before the slli in the same block chain; B's value at that branch from the flow-sensitive
     constant data-flow (luitrace.Ctx.vals: li / lui / addi chains, through loops and branches, the value at that point),
     so 0 <= i <= B;
  3. the entries 0..B: target_k = T + entry_k must be inside the function, and target_k - function start must be equal
     in both images.
Writes out/switchbound.tsv and prints each table and the counts. usage: switchbound.py"""
import collections, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common, escape, luitrace


def find(ctx, a, z, word):
    img = ctx.img
    ins = img.dis(a, z)
    at = {o: k for k, (o, m, p, n) in enumerate(ins)}
    k = at[word]
    T = ins[k][2].split(',')[0].strip()
    # the dispatch
    seq = ins[k + 1:k + 5]
    m1 = re.match(r'(\w+), (\w+), (\w+)$', seq[0][2]) if seq and seq[0][1] == 'add' else None
    if not m1 or T not in (m1.group(2), m1.group(3)):
        return None, 'no `add p, i2, T` after the table word'
    i2 = m1.group(3) if m1.group(2) == T else m1.group(2)
    p = m1.group(1)
    if not (seq[1][1] == 'lw' and re.match(r'(\w+), 0\(%s\)$' % p, seq[1][2])):
        return None, 'no `lw e, 0(p)`'
    e = seq[1][2].split(',')[0].strip()
    if not (seq[2][1] == 'add' and set(x.strip() for x in seq[2][2].split(',')[1:]) == {e, T}):
        return None, 'no `add t, e, T`'
    t = seq[2][2].split(',')[0].strip()
    if not (seq[3][1] == 'jr' and seq[3][2].strip() == t):
        return None, 'no `jr t`'
    # the slli that makes i2, before the table word
    j = next((j for j in range(k - 1, max(-1, k - 8), -1) if ins[j][1] == 'slli' and ins[j][2].startswith(i2 + ',')), None)
    if j is None:
        return None, 'no `slli i2, i, 2` before the table word'
    sl = [x.strip() for x in ins[j][2].split(',')]
    if int(sl[2], 0) != 2:
        return None, 'the scale is not 4 bytes'
    i = sl[1]
    # the guard: the last bltu B, i / bgeu i, B before the slli (in this block chain)
    g = next((g for g in range(j - 1, max(-1, j - 12), -1) if ins[g][1] in ('bltu', 'bgeu')), None)
    if g is None:
        return None, 'no bltu / bgeu guard before the slli'
    gops = [x.strip() for x in ins[g][2].split(',')]
    if ins[g][1] == 'bltu' and gops[1] == i:
        B = gops[0]
    elif ins[g][1] == 'bgeu' and gops[0] == i:
        B = gops[1]
    else:
        return None, 'the guard %s %s does not bound %s' % (ins[g][1], ins[g][2], i)
    # nothing between the guard and the slli writes i
    for x in ins[g + 1:j]:
        if x[2] and x[2].split(',')[0].strip() == i and x[1] not in ('sd', 'sw', 'sh', 'sb') and not x[1].startswith('b'):
            return None, 'i is rewritten between the guard and the scale'
    v = ctx.vals(a, z, g, B)
    how = 'by data-flow'
    if not v and B.startswith('s'):
        # SINGLE-DEF: a callee-saved B whose only writes in the function are ONE `addi B, zero, K` / `li B, K` and the
        # epilogue restore `ld B, off(sp)` (after which no instruction reads B before a `ret`): B = K at every later point
        # (calls preserve callee-saved registers)
        defs = [(n_, x) for n_, x in enumerate(ins) if x[2] and x[2].split(',')[0].strip() == B and x[1] not in
                ('sd', 'sw', 'sh', 'sb') and not x[1].startswith('b')]
        consts = [(n_, x) for n_, x in defs if (x[1] == 'addi' and re.match(r'%s, zero, (-?(?:0x[0-9a-f]+|\d+))$' % B, x[2]))
                  or (x[1] == 'li' and re.match(r'%s, (-?(?:0x[0-9a-f]+|\d+))$' % B, x[2]))]
        restores = [(n_, x) for n_, x in defs if x[1] == 'ld' and re.match(r'%s, (0x[0-9a-f]+|\d+)\(sp\)$' % B, x[2])]
        def restore_ok(n_):
            for y in ins[n_ + 1:]:
                ops_ = [t.strip() for t in y[2].split(',')] if y[2] else []
                if B in ops_[1:] or ('(%s)' % B) in y[2]:
                    return False
                if y[1] == 'ret' or (y[1] == 'jr' and y[2] == 'ra'):
                    return True
            return False
        if len(consts) == 1 and len(defs) == 1 + len(restores) and all(restore_ok(n_) for n_, x in restores) \
                and consts[0][0] < g:
            v = {('const', int(consts[0][1][2].split(',')[-1], 0))}
            how = 'single definition +%#x `%s %s` (only other writes: the epilogue restore%s %s)' % (
                consts[0][1][0], consts[0][1][1], consts[0][1][2], 's' if len(restores) > 1 else '',
                ', '.join('+%#x' % x[0] for n_, x in restores))
    if not v or not all(x[0] == 'const' for x in v) or len(v) != 1:
        return None, 'the bound register %s holds %s at the guard' % (B, sorted(v, key=str)[:4])
    bound = list(v)[0][1]
    tb = img.wtarget.get(a + word)
    return dict(table=tb, bound=bound, guard='+%#x %s %s' % (ins[g][0], ins[g][1], ins[g][2]), B=B, i=i, how=how,
                dispatch='+%#x..+%#x' % (ins[k + 1][0], ins[k + 4][0])), None


def main():
    X, Y = luitrace.Ctx(common.CGIF_B_TWIN), luitrace.Ctx(common.DECODE_B_TWIN)
    rows = [l.rstrip('\n').split('\t') for l in list(open(os.path.join(common.OUT, 'fulldiff.tsv')))[1:]]
    # only the tables no other measurement settles: fulldiff DIFFERS rows that jtcheck did not accept (tables.tsv)
    tabled = {(t[0], int(t[1], 16)) for t in (l.rstrip('\n').split('\t') for l in
                                              list(open(os.path.join(common.OUT, 'tables.tsv')))[1:]) if t[2] != 'DIFFERS'}
    want = [r for r in rows if r[5] == 'DIFFERS' and (r[0], int(r[3], 16)) not in tabled]
    out, cnt = [], collections.Counter()
    for r in want:
        fn, ax, ay, word = r[0], int(r[1], 16), int(r[2], 16), int(r[3], 16)
        zx = X.img.I.fsym(fn)[1]
        dx, ex = find(X, ax, zx, word)
        dy, ey = find(Y, ay, zx, word)
        if dx is None or dy is None:
            v, why = 'NO-BOUND', '%s | %s' % (ex, ey)
        elif dx['bound'] != dy['bound']:
            v, why = 'DIFFERS', 'bound %d vs %d' % (dx['bound'], dy['bound'])
        else:
            n = dx['bound'] + 1
            bad, outside = [], 0
            for kk in range(n):
                ec = int.from_bytes(escape.sc.frd(X.img.I, dx['table'] + 4 * kk, 4), 'little', signed=True)
                ed = int.from_bytes(escape.sc.frd(Y.img.I, dy['table'] + 4 * kk, 4), 'little', signed=True)
                tx, ty = dx['table'] + ec - ax, dy['table'] + ed - ay
                if not (0 <= tx < zx):
                    outside += 1
                if tx != ty:
                    bad.append(kk)
            v = 'RELJUMP' if not bad and not outside else 'DIFFERS'
            why = '%d entries (guard %s, %s = %d at the guard, %s; index %s; dispatch %s): function-relative ' \
                  'targets %s%s' % (n, dx['guard'], dx['B'], dx['bound'], dx['how'], dx['i'], dx['dispatch'],
                                    'equal' if not bad else 'DIFFER at %s' % bad[:5],
                                    '' if not outside else '; %d outside the function' % outside)
        cnt[v] += 1
        out.append((fn, '%#x' % word, v, '%#x' % dx['table'] if dx else '-', '%#x' % dy['table'] if dy else '-', why))
    with open(os.path.join(common.OUT, 'switchbound.tsv'), 'w') as f:
        f.write('function\tword\tmeasurement\tX table\tY table\tdetail\n')
        for r in out:
            f.write('\t'.join(r) + '\n')
    print('rel4 jump tables measured by data-flow bound: %d: %s' % (len(out), dict(sorted(cnt.items()))))
    for r in out:
        print('  %s %s %s %s' % (r[0][:60], r[1], r[2], r[5][:200]))


if __name__ == '__main__':
    main()
