(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from CertS1Both.v: its definitions (fuels, instruction table, the LPS 727298f3 renumbering map vsh1 and join-counter floor, the run record's fixed filter for the computed join states against the recorded ones, which keeps a variable-free fact only when the recorded join state names it, the renumbered plan, the check run once with collectors at its hand-offs and joins, the result shape), split from the per-CONFIG_RSEQ certificates so they build in parallel. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl PlanRegen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import A_Hooks5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import AsanPlanImagesB PlanS1Both JS1Both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Open Scope Z_scope.

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
Definition XN0 := A_Hooks5.XN5 BSEGS BOTH5 NX0.

(* [comment removed for export] *)
Definition IT1 : itab := mk_itab_ranges BSEGS s1_plan_ranges.
Lemma IT1_ok : AX2.itab_sound BSEGS IT1.
Proof. apply APS.mk_itab_ranges_sound. Qed.

(* LPS 727298f3 renumbering, read from probes (notes/probe-yajl-ruby__json_fuzzer.md, P1, P2 and
   P5): before this plan's PBump 95 the run names its fresh variables 4 later than the recorded
   run (P5: the image words at 0x5e14a8 and 0x601590, EVar 44 and EVar 61 in the recorded join
   state, are EVar 48 and EVar 65 in the computed one); the PBump resets the counter, and at its
   PDropRange of EVar 95 the run's map bases are the recorded 95, 225, 226, 244-246 (identity).
   After the PVia 11 join the run names the recorded 275 at the join state's counter and the
   recorded 340 two numbers later than the recorded plan did (P2: join counter 263, map bases
   263 and 330, against 275 and 340), at both CONFIG_RSEQ values.  The join state keeps the
   recorded counter 275 ([jfloor]), so 275 stays and 340 moves by 2.  The plan names no variable
   from 12 to 94, so the first step moves only the recorded join states' facts that [jkeep]
   compares against. *)
Definition vsh1 : nat -> nat := tshift [(12%nat, 4%nat); (95%nat, 0%nat); (340%nat, 2%nat)].
(* the recorded join states' counters (P1, ZZ_S1B_RECJS: js_11 275, js_2 438), renumbered *)
Definition jfloor (j : nat) : nat := if Nat.eqb j 11 then vsh1 275 else if Nat.eqb j 2 then vsh1 438 else 0.

(* The join states are filtered by the run record's fixed rule ([PlanRegen.filt_rec]): a fact that
   names a launch variable and no fresh one is kept, any other fact (on a fresh variable, or naming
   no variable) only if the recorded join state (JS1Both.v), renumbered by [vsh1], names it too.
   Unfiltered, this build's PVia 11 join state holds about 9330 facts (probe P2, ZZ_C1B_TAB_R0/R1)
   where the recorded one holds about 570, and every check after the join runs over them; 8788 of
   them are variable-free words the recorded join state does not hold (probe P6B/P6C, OSSV-509),
   which a filter that kept every variable-free fact carried into every hand-off and main-entry
   state (about 9940 facts each, against 1131 recorded). *)
Definition jrec (j : nat) : option acs :=
  if Nat.eqb j 11 then Some js_11 else if Nat.eqb j 2 then Some js_2 else None.
Definition jkeep (j : nat) (cs : acs) : acs := filt_rec vsh1 NX0 (jrec j) cs.

(* The plan, renumbered, with its join states [J]; the recorded join states are not the plan's
   (they serve only as [jkeep]'s reference). *)
Definition s1_plan_r (r : Z) (J : nat -> option acs) : plan :=
  pjs J (psh vsh1 (s1_plan (init_acs_of r BOTH5) (init_acs_of r BOTH5))).
(* [s1_coll r]: the check with no tables yet, written as [check_coll]: it hands each state it
   reaches at a hand-off to [hvisitj] and each state an arm of a via reaches at its [PMerge] to
   [jvisit] (with the filter [jkeep] and the floor [jfloor]), so one run makes the hand-off and join
   tables ([PlanRegen.collect_hjf1]).  [check_coll] checks a via's arms before its continuation and
   runs the continuation from the join state the arms made, so the plan's own join states (the
   launch state here) are read only where no arm reaches the via's [PMerge]. *)
Definition s1_coll (r : Z) (t : hjtab) : cres * hjtab :=
  check_coll BSEGS IT1 BOTH5 NX0 AsanInit.LIMIT r XN0 XE0 XB0 KC0 BFUEL _ hvisitj (jvisit jfloor jkeep) jget
    FUEL None (init_acs_of r BOTH5) (psh vsh1 (s1_plan (init_acs_of r BOTH5) (init_acs_of r BOTH5))) t.


Definition s1_shape : shape :=
  SCase (EVar 6) 10
    (SCase (EVar 10) 0 (SCase (EVar 5) 524277 (SHole 0) (SHole 1))
       (SCase (EVar 10) 6 (SCase (EVar 5) 524277 (SHole 0) (SHole 1)) (SCase (EVar 5) 524277 (SHole 0) (SHole 1))))
    (SCase (EVar 10) 0 (SCase (EVar 5) 524277 (SHole 0) (SHole 1))
       (SCase (EVar 10) 6 (SCase (EVar 5) 524277 (SHole 0) (SHole 1)) (SCase (EVar 5) 524277 (SHole 0) (SHole 1)))).
