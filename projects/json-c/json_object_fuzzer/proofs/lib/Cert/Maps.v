(* SPDX-License-Identifier: MIT *)
(* The LPS 727298f3 renumbering maps of the recorded start-up plans of Q0qZ.v, one per build, applied
   where the plans are checked ([PlanRegen.psh]); read off the new start-up run, never chosen.

   LPS 727298f3 gives the launch two more plan variables ([V_G] = 11, [V_GID] = 12: NX0 11 -> 13) and
   more of the auxv to read, so the start-up run adds its fresh variables at other numbers than the run
   the recorded plans were written against.  The launch's own variables (below the old NX0, 11) keep
   their numbers.

   A table [(t, d)] (thresholds in the OLD numbering, [PlanRegen.tshift]) moves an old variable by the
   [d] of the last threshold at or below it.  Where the recorded stage-1 plan names EVar 78 (its
   PDropRange at pc 0x6a8c4), the run's map base is 4096 * EVar 82, in both builds and at both
   CONFIG_RSEQ values; the recorded plans name no variable between 11 and 77, so the first step is
   placed at the old NX0.  With the plans renumbered by that table and cut at each recorded [PBump m],
   the largest counter c that reaches it gives a step [(m, c - m)] where c is above [m + d] (stage 1:
   PBump 364 is reached with counter 370, so [(364, 6)]; PBumps 220, 249, 374 and 465 with 214, 251,
   370 and 463; stage 2: PBump 478 with the stage-1 hand-off counter 483, PBump 2252 with 2248), the
   same in both builds and at both CONFIG_RSEQ values.  With this table the stage-1 and both stage-2
   certificates answer COk.  A certificate re-checks the renumbered plan, so a wrong map can only make
   it fail. *)
From Stdlib Require Import List.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cert Require Import PlanRegen.
Import ListNotations.

(* the ASan build (Q0qZ's jo6 plans) *)
Definition jo6_vsh : nat -> nat := tshift [(11, 4); (364, 6)].
(* the ASan+UBSan build (Q0qZ's job6 plans) *)
Definition job6_vsh : nat -> nat := tshift [(11, 4); (364, 6)].
