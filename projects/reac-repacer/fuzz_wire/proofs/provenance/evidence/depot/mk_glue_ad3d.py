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
line and an SPDX line, and lines 312-318 are exactly the lemma (header `Lemma env_agree_Ereg_app` ... `Qed.`)."""
import sys

src, out = sys.argv[1:3]
L = open(src).read().split('\n')
body = L[311:318]
if not (body[0].startswith('Lemma env_agree_Ereg_app : ') and body[-1] == 'Qed.' and L[318].startswith('Lemma ')):
    sys.exit('mk_glue_ad3d: lines 312-318 of %s are not the lemma env_agree_Ereg_app' % src)
# the donor's licence lines, as the donor file has them (never typed here)
lic = L[0:2]
if not (lic[0].startswith('(* Copyright ') and lic[0].endswith(' *)') and lic[1].startswith('(* SPDX-License-Identifier: ')
        and lic[1].endswith(' *)')):
    sys.exit('mk_glue_ad3d: lines 1-2 of %s are not a Copyright line and an SPDX line' % src)
U = 'OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib.Reusable'
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
print('mk_glue_ad3d: wrote %s (%d lines; lemma from AF0r.v:312-318)' % (out.split('/lib/')[-1], len(txt.splitlines())))
