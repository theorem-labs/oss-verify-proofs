#!/usr/bin/env python3
"""flag_stub.py SRC.v OUT.v -- a FLAG-EQUIVALENT stub of a lib file, for the grant baseline of rules E6 / E7.

The Zify flag a file's body sees depends only on which modules load, in which order, and on the
`Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= ..` sentences they run when loaded. A file of the
baseline tree that does not compile (its proof fails, or a start-up module the baseline lacks) is replaced by a stub
that keeps exactly those parts, in their order: every Require sentence, every Section / Module / End line, and every
Ltac flag sentence (Local or not). Nothing else is kept, so the stub compiles, and loading it has the same effect on
the flag as loading the original would. The stub is used only to let the probes of OTHER files load; a stubbed file's
own value is still probed from its own Require block (flag_probe.py), which the stub keeps."""
import re, sys

src, out = sys.argv[1:3]
t = open(src, encoding='utf-8').read()
# drop comments (strings honoured), keep line structure
o, d, i, s = [], 0, 0, False
while i < len(t):
    two = t[i:i + 2]
    if not s and two == '(*':
        d, i = d + 1, i + 2
        continue
    if d and two == '*)':
        d, i = d - 1, i + 2
        continue
    if d == 0:
        if t[i] == '"':
            s = not s
        o.append(t[i])
    elif t[i] == '\n':
        o.append('\n')
    i += 1
code = ''.join(o)
keep = []
for m in re.finditer(r'(?:^|(?<=\.\s))\s*((?:From\s+\S+\s+)?Require\b[^.]*\.(?=\s|$)|(?:Local\s+|Global\s+)?Ltac\s+Zify\.zify_convert_to_euclidean_division_equations_flag\s*::=\s*constr:\((?:true|false)\)\.|Section\s+[\w\']+\.|Module\s+[\w\']+\.|End\s+[\w\']+\.)', code, re.S | re.M):
    keep.append(' '.join(m.group(1).split()))
open(out, 'w', encoding='utf-8').write('(* flag-equivalent stub of %s *)\n' % src.rsplit('/', 1)[-1] + '\n'.join(keep) + '\n')
print('flag_stub: %s -> %d sentence(s)' % (src.rsplit('/', 1)[-1], len(keep)))
