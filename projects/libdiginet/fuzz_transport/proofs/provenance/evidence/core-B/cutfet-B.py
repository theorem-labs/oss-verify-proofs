#!/usr/bin/env python3
"""cutfet-B.py STAGE_OUT OUT.patch: B-yfet-cost.patch for libdiginet/fuzz_transport's image-B core.

B/YFet.v (decode's B text) proves four `v = AV (ANum 0)` facts by unfolding the whole constant record
(cbv [Tfib_const ...] in Hc) and destructing the membership In c (Tfib_const ly) cell by cell, which is quadratic
in the record's cells. The image-A core's row TCA measured the A twin (A/AFet.v) at 43 GB / 2.2 h with transport's
3080 cells and replaced each block by one forallb check decided by vm_compute (8 s / 0.7 GB): the image-A core's run
of record 9f022aeb9a21, its patch afet-cost.patch (sha256 9f5dfea19198). This writes the same replacement for B's four
blocks.
Proof text only: the statements are unchanged. Exactly four blocks must match; a fresh unified diff, -p0 from
stage-out, 3 lines of context."""
import difflib, sys

so, out = sys.argv[1:3]
f = 'B/YFet.v'
OLD1 = ('{ clear - Hc TC. rewrite TC in Hc. cbv [Tfib_const Tfib_const_sym Tfib_const_abs Tfib_const_shadow app In '
        'z8 z4 z2 z1 c8 c4 c2 c1] in Hc.\n')
OLD2 = 'repeat (destruct Hc as [Hc|Hc]; [first [congruence | discriminate] |]). destruct Hc. }\n'
NEW1 = ('{ clear - Hc TC. rewrite TC in Hc. match type of Hc with In (ACell ?a ?w _) ?l => match goal with |- _ = AV ?r '
        '=> assert (CK : forallb (fun c0 : acell => if andb (aexp_eqb (c_at c0) a) (Nat.eqb (c_w c0) w) then match '
        'c_val c0 with AV e0 => aexp_eqb e0 r | _ => false end else true) l = true) by (vm_compute; reflexivity) end '
        'end.\n')
NEW2 = ('pose proof (proj1 (forallb_forall _ _) CK _ Hc) as K. cbn in K. destruct v as [e0|m0 v0]; cbn in K; '
        '[|discriminate K]. destruct e0; cbn in K; try discriminate K. apply Z.eqb_eq in K. rewrite K. reflexivity. }\n')
txt = open(f'{so}/{f}').read().splitlines(keepends=True)
hits = [i for i in range(len(txt) - 1) if txt[i] == OLD1 and txt[i + 1] == OLD2]
assert len(hits) == 4, hits
new = list(txt)
for i in hits:
    new[i], new[i + 1] = NEW1, NEW2
open(out, 'w').write(''.join(difflib.unified_diff(txt, new, f, f, n=3)))
print(f'{out}: {f} blocks at lines {[i + 1 for i in hits]} replaced')
