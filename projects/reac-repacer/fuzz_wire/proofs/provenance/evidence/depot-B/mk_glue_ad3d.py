#!/usr/bin/env python3
"""mk_glue_ad3d.py KNOCK_AF0R OUT -- lib/A/AD3dEnv.v of reac-repacer/fuzz_wire: glue, closure (B).

A/AD3d.v (knock donor) Requires knock's A/AF0r.v for ONE name, env_agree_Ereg_app; AF0r (knock's class-1 fake-stack walk)
stays out by ruling (B), and the grant lineage this unit carries has no lemma with that statement (searched: the unit's
lib holds env_agree_havoc_ge and env_agree_le only). So that lemma's text, statement and proof, is copied VERBATIM from
KNOCK_AF0R (proofs/libreac/fuzz_knock/lib/A/AF0r.v at 88154566652a, lines 312-318) into its own file, with knock's
Requires of the kernel modules it reads (YP0m: env / ew; YI04: Ereg, ew_Ereg_extra; YP06:
env_agree) with
module paths mapped to this unit. Above the Require lines it copies KNOCK_AF0R's own Copyright and SPDX lines (its
lines 1-2), byte for byte as read from that file, and it writes no `Modified by` notice: licence-lines --apply adds the
notice afterwards. The file states no stack class. The script refuses unless lines 1-2 of KNOCK_AF0R are a Copyright
line and an SPDX line, and lines 312-318 are exactly the lemma (header `Lemma env_agree_Ereg_app` ... `Qed.`).
--image B: lib/B/YD3dEnv.v for B/YD3d.v, from KNOCK_AF0R = knock's image-B twin proofs/libreac/fuzz_knock/lib/AU/YF0r.v at
88154566652a, whose lemma is lines 313-319 (the same seven lines). --unit-mod M: the unit's lib module path (default
OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib); the Requires name M.Reusable."""
import os, sys

args = sys.argv[1:]
lo, M = 312, 'OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib'
while args[:1] in (['--image'], ['--unit-mod']):
    if args[0] == '--image':
        lo = {'A': 312, 'B': 313}[args[1]]
    else:
        M = args[1]
    args = args[2:]
src, out = args[:2]
L = open(src).read().split('\n')
body = L[lo - 1:lo + 6]
if not (body[0].startswith('Lemma env_agree_Ereg_app : ') and body[-1] == 'Qed.' and L[lo + 6].startswith('Lemma ')):
    sys.exit('mk_glue_ad3d: lines %d-%d of %s are not the lemma env_agree_Ereg_app' % (lo, lo + 6, src))
# the donor's licence lines, as the donor file has them (never typed here)
lic = L[0:2]
if not (lic[0].startswith('(* Copyright ') and lic[0].endswith(' *)') and lic[1].startswith('(* SPDX-License-Identifier: ')
        and lic[1].endswith(' *)')):
    sys.exit('mk_glue_ad3d: lines 1-2 of %s are not a Copyright line and an SPDX line' % src)
U = M + '.Reusable'
txt = '\n'.join(lic + [
    'From %s Require YZ00.' % U,
    'From Stdlib Require Import ZArith NArith List Lia.',
    'From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.',
    'From %s Require Import YP0m YP06 YI04.' % U,
    'Import ListNotations.',
    'Unset Lia Cache. Unset Nia Cache.',
] + body) + '\n'
for bad in ('stack_malloc', 'CID', 'FS_'):
    if bad in txt:
        sys.exit('mk_glue_ad3d: class text %r in the glue' % bad)
open(out, 'w').write(txt)
print('mk_glue_ad3d: wrote %s (%d lines; lemma from %s:%d-%d)' % (out.split('/lib/')[-1], len(txt.splitlines()),
                                                                 os.path.basename(src), lo, lo + 6))
