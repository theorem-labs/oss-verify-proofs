#!/usr/bin/env python3
"""hypaudit-B.py WORK: values in HYPOTHESIS positions of a port_core run (registry 22:09Z, the release lead 22:06Z).

A hypothesis-position line: it holds `mkAF` (an atom range), `afact` / `region_ok` / `mkRegion` facts, or opens a
`Hypothesis` / `Variable ... :` / `Context` binder. For every staged file, each such line of stage-out is paired with
the donor line it came from (difflib on the two texts), and the numerals are compared in order. LISTED counts every
hypothesis-position line; DIFFERS the ones whose numerals differ from the donor's; each differing line is printed
with both numeral lists, for a hand derivation (a green build is not evidence for these)."""
import difflib, os, re, sys

work = sys.argv[1]
st, so = f'{work}/stage', f'{work}/stage-out'
HYP = re.compile(r'\bmkAF\b|\bafact\b|\bregion_ok\b|\bmkRegion\b|^\s*(Hypothesis|Hypotheses|Variable|Variables|Context)\b')
NUM = re.compile(r'\b0x[0-9a-fA-F]+\b|\b\d+\b')
listed, differs = 0, []
for dp, _, fs in os.walk(so):
    for fn in sorted(fs):
        if not fn.endswith('.v'):
            continue
        rel = os.path.relpath(os.path.join(dp, fn), so)
        if not os.path.exists(f'{st}/{rel}'):
            continue
        a = open(f'{st}/{rel}', errors='replace').read().split('\n')
        b = open(f'{so}/{rel}', errors='replace').read().split('\n')
        sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
        pair = {}
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag == 'equal' or (tag == 'replace' and i2 - i1 == j2 - j1):
                for k in range(j2 - j1):
                    pair[j1 + k] = i1 + k
        for j, line in enumerate(b):
            if line.lstrip().startswith('(*') or not HYP.search(line):
                continue
            listed += 1
            i = pair.get(j)
            na, nb = (NUM.findall(a[i]) if i is not None else None), NUM.findall(line)
            if na != nb:
                differs.append((rel, j + 1, None if i is None else i + 1, na, nb))
print(f'LISTED {listed}  DIFFERS-FROM-DONOR {len(differs)}')
for rel, j, i, na, nb in differs:
    ch = [(x, y) for x, y in zip(na or [], nb) if x != y] if na is not None else 'unpaired'
    print(f'{rel}:{j} (donor line {i}): {ch}')
