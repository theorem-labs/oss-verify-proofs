#!/usr/bin/env python3
"""hdrcheck.py STAGE_OUT DON -- the header form port_core 83f5203d2a2f writes, checked on every relocated file.

For each .v file under STAGE_OUT/A and STAGE_OUT/Reusable, with its donor file in DON (the normalised donor lib: A/<f>
stays A/<f>, Reusable/<f> is <f> at DON's top):
  1. the donor's notice block (its first lines that are `(* Copyright ... *)`, `(* SPDX-License-Identifier: ... *)`,
     `(* Modified by ... *)` or `(* This file states or restates instruction words ... *)`) is the file's first lines,
     byte for byte;
  2. the next line is the one registered port_core provenance line (tools registry, 'Tool-written comment formats');
  3. no other line of the file is a `(* Modified by Theorem Labs` line or a provenance line.
Exit 0 when every file passes, 1 otherwise; one line per refused file, then a summary line."""
import os
import re
import sys

NOTICE = re.compile(r'\(\* (?:Copyright |SPDX-License-Identifier: |Modified by |This file states or restates instruction words )'
                    r'.*\*\)\Z')
PROV = re.compile(r'^\(\* Relocated from (proofs/[A-Za-z0-9_./-]+\.v) at ([0-9a-f]{12}) by port_core ([0-9a-f]{12}) onto '
                  r'([A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+) \((plain|ubsan|asan|asan-ubsan)\)\. \*\)$')
OURS = re.compile(r'\(\* Modified by Theorem Labs')


def block(lines):
    n = 0
    while n < len(lines) and NOTICE.match(lines[n]):
        n += 1
    return lines[:n]


def main():
    so, don = sys.argv[1], sys.argv[2]
    bad = 0
    total = 0
    for sub in ('A', 'Reusable'):
        d = os.path.join(so, sub)
        for name in sorted(os.listdir(d)):
            if not name.endswith('.v'):
                continue
            total += 1
            rel = f'{sub}/{name}'
            dp = os.path.join(don, rel if sub == 'A' else name)
            got = open(os.path.join(d, name)).read().split('\n')
            want = block(open(dp).read().split('\n'))
            why = []
            if got[:len(want)] != want:
                why.append('donor notice block differs')
            if len(got) <= len(want) or not PROV.match(got[len(want)]):
                why.append('no registered provenance line after the notice block')
            extra = [i + 1 for i, line in enumerate(got) if i != len(want) and
                     (PROV.match(line) or (i >= len(want) and OURS.match(line)))]
            if extra:
                why.append('extra provenance / Modified-by line(s) at ' + ','.join(map(str, extra)))
            if why:
                bad += 1
                print(f'REFUSED {rel}: ' + '; '.join(why))
    print(f'hdrcheck: {total} files, {total - bad} in form, {bad} refused')
    sys.exit(1 if bad else 0)


main()
