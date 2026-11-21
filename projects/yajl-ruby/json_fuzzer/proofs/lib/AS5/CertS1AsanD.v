(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from CertS1Asan.v: its definitions (fuels, instruction table, the LPS 727298f3 renumbering map vsh1 and join-counter floor, the renumbered plan, the check run once with collectors at its hand-offs and joins, the result shape), split from the per-CONFIG_RSEQ certificates so they build in parallel. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl PlanRegen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import AsanPlanImages5 A_Hooks5 PlanS1Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Open Scope Z_scope.

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
Definition XN0 := A_Hooks5.XN5 ASEGS ASAN5 NX0.

(* [comment removed for export] *)
Definition IT1 : itab := mk_itab_ranges ASEGS s1_plan_ranges.
Lemma IT1_ok : AX2.itab_sound ASEGS IT1.
Proof. apply APS.mk_itab_ranges_sound. Qed.

(* LPS 727298f3: the start state has V_GID (12, the old NX0) and the auxv facts of the model's
   vector, so the run adds its fresh variables at other numbers.  The map is read from probes
   (notes/probe-yajl-ruby__json_fuzzer.md, P1 and P2): where the plan names EVar 95 (its
   PDropRange at pc 0x5ae84) the run's map base is 4096 * EVar 99 (+4), and after the PVia 11
   join the run's map bases are 4096 * EVar 279 for the recorded 275 (+4) and 4096 * EVar 346 for
   the recorded 340 (+6), at both CONFIG_RSEQ values.  No variable between 275 and 340 is named by
   the plan, so the second step is placed at 340. *)
Definition vsh1 : nat -> nat := tshift [(12%nat, 4%nat); (340%nat, 6%nat)].
(* the recorded join states' counters (P1, ZZ_S1A_RECJS: js_11 275, js_2 438), renumbered: a join
   state computed here keeps at least that counter *)
Definition jfloor (j : nat) : nat := if Nat.eqb j 11 then vsh1 275 else if Nat.eqb j 2 then vsh1 438 else 0.

(* The plan, renumbered, with its join states [J]; the recorded join states are not used. *)
Definition s1_plan_r (r : Z) (J : nat -> option acs) : plan :=
  pjs J (psh vsh1 (s1_plan (init_acs_of r ASAN5) (init_acs_of r ASAN5))).
(* [s1_coll r]: the check with no tables yet, written as [check_coll]: it hands each state it
   reaches at a hand-off to [hvisitj] and each state an arm of a via reaches at its [PMerge] to
   [jvisit] (every join state kept whole beyond [keep_lt], with the floor [jfloor]), so one run
   makes the hand-off and join tables ([PlanRegen.collect_hjf1]).  [check_coll] checks a via's arms
   before its continuation and runs the continuation from the join state the arms made, so the
   plan's own join states (the launch state here) are read only where no arm reaches the via's
   [PMerge]. *)
Definition s1_coll (r : Z) (t : hjtab) : cres * hjtab :=
  check_coll ASEGS IT1 ASAN5 NX0 AsanInit.LIMIT r XN0 XE0 XB0 KC0 BFUEL _ hvisitj (jvisit jfloor (fun _ a => a)) jget
    FUEL None (init_acs_of r ASAN5) (psh vsh1 (s1_plan (init_acs_of r ASAN5) (init_acs_of r ASAN5))) t.


Definition s1_shape : shape :=
  SCase (EVar 6) 10
    (SCase (EVar 10) 0 (SCase (EVar 5) 524277 (SHole 0) (SHole 1))
       (SCase (EVar 10) 6 (SCase (EVar 5) 524277 (SHole 0) (SHole 1)) (SCase (EVar 5) 524277 (SHole 0) (SHole 1))))
    (SCase (EVar 10) 0 (SCase (EVar 5) 524277 (SHole 0) (SHole 1))
       (SCase (EVar 10) 6 (SCase (EVar 5) 524277 (SHole 0) (SHole 1)) (SCase (EVar 5) 524277 (SHole 0) (SHole 1)))).
