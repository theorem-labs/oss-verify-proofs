#!/usr/bin/env python3
"""tail_generalize.py LIB_A -- glue rule (E5, form (a) as ruled): in lemma tail_ext_ok of exactly three files
(A/AFjm.v, A/AFis.v, A/AFj6.v), the knock text's closing `... unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia) end.` becomes
`... unfold TFIB_IMG_LO, TFIB_IMG_END in *; destruct X4 as [X|X]; [lia | right; exact X]) end.` (measured: in place,
the kernel's lia front-end fails on X4 -> goal while the atom is a Section constant (BSLv / SSLOTv); split on X4's
first disjunct, the false one is closed by lia and the rest is X4's own text). Each file must contain the closing
exactly once inside tail_ext_ok; anything else refuses (exit 1). Prints each site (file:line, before -> after)."""
import os, sys

SITES = (('AFjm.v', 'BSLv'), ('AFis.v', 'SSLOTv'), ('AFj6.v', 'SSLOTv'))
OLD = 'clear - X4; unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia) end.'
la = sys.argv[1]
for f, c in SITES:
    p = os.path.join(la, f)
    t = open(p).read()
    i = t.index('Lemma tail_ext_ok')
    j = t.index('Qed.', i)
    if t.count(OLD) != 1 or not (i < t.index(OLD) < j):
        sys.exit('tail_generalize: %s: the closing is not exactly once inside tail_ext_ok' % f)
    new = OLD.replace('in *; lia) end.', 'in *; destruct X4 as [X|X]; [lia | right; exact X]) end.')
    ln = t.count('\n', 0, t.index(OLD)) + 1
    open(p, 'w').write(t.replace(OLD, new))
    print('tail_generalize: A/%s:%d: `%s` -> `%s`' % (f, ln, OLD, new))
print('tail_generalize: 3 sites')
