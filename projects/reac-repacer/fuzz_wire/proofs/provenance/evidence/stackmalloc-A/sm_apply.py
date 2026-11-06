#!/usr/bin/env python3
"""sm_apply.py WORK LIB DONOR_LIB OUT_LIST -- copy port_core's stage-out (WORK/stage-out/<F>, every .v file) into LIB by
port_core --apply's own rule for a new file (nothing in LIB is overwritten: a file LIB already holds is refused), with
the DONOR's header: the leading run of one-line comments `(* Copyright ... *)`, `(* SPDX-License-Identifier: ... *)`
and `(* Modified by ... *)` of DONOR_LIB/<F>, byte for byte, in place of the stage-out's (the unit owner's ruling,
2026-10-31 18:12Z: a file copied or relocated from an Anthropic-headed file keeps its donor's header lines as copied,
`Modified by` lines included; licence-lines (C) later rewrites them through the unit's path-map row). The stage-out's
own leading block (the donor's lines, which port_core's renames may reach, and port_core's notice) is not copied.
DONOR_LIB: the donor's released lib in repository layout, unnormalised (`git archive 98c99a85e4
projects/libreac/fuzz_grant/proofs/lib`), <F> at the same relative path (A/Rt/..., Reusable/...).
It refuses (exit 1, nothing written) unless, for every file: the donor's header is at least its two licence lines and
each is a whole comment on its line; no other line of the donor or of the stage-out below its block is such a line; and
LIB does not hold the file. Writes the copied paths (relative to LIB) to OUT_LIST."""
import os
import re
import sys

LIC = re.compile(r'^\(\* (?:Copyright |SPDX-License-Identifier: |Modified by ).*\*\)$')
LOOSE = re.compile(r'^\(\* (?:Copyright|SPDX|Modified by)')


def lead(lines):
    k = 0
    while k < len(lines) and LIC.match(lines[k]):
        k += 1
    return k


def main():
    work, lib, don, out = sys.argv[1:5]
    so = os.path.join(work, 'stage-out')
    files = sorted(os.path.relpath(os.path.join(d, f), so) for d, _, fs in os.walk(so) for f in fs if f.endswith('.v'))
    plan, bad = [], []
    for f in files:
        S = open(os.path.join(so, f), encoding='utf-8').read().split('\n')
        try:
            D = open(os.path.join(don, f), encoding='utf-8').read().split('\n')
        except FileNotFoundError:
            bad.append('%s: the donor lib has no such file' % f)
            continue
        ks, kd = lead(S), lead(D)
        if kd < 2:
            bad.append('%s: the donor has %d leading licence lines' % (f, kd))
        if any(LOOSE.match(x) for x in S[ks:]) or any(LOOSE.match(x) for x in D[kd:]):
            bad.append('%s: a licence line below the leading block' % f)
        if os.path.exists(os.path.join(lib, f)):
            bad.append('%s: LIB already holds it' % f)
        plan.append((f, D[:kd], S[ks:]))
    if bad:
        sys.exit('sm_apply: REFUSED, nothing written: ' + '; '.join(bad))
    with open(out, 'w') as o:
        for f, head, body in plan:
            p = os.path.join(lib, f)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, 'w', encoding='utf-8') as w:
                w.write('\n'.join(head + body))
            o.write(f + '\n')
            print('sm_apply: %s: the donor\'s %d header line(s), then %d line(s) byte-equal to the stage-out below its '
                  'own header' % (f, len(head), len(body)))


if __name__ == '__main__':
    main()
