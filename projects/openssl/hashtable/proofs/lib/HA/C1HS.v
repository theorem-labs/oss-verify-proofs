(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up hand-off states are computed in the build from the check's own run and kept against the recorded ones, renumbered by [C1_F]). *)
(* LPS 727298f3: the start-up hand-off states (hand-offs 0 and 1), computed in the build from the run
   (the method of jsoncons/fuzz_bigint's PlanRegenK.v and double-conversion/string_to_double_fuzzer's
   MainHSAsan.v).

   The recorded plan [C1.c1_plan] is checked renumbered by [C1_F], a total monotone map read from probe
   runs of this plan at both CONFIG_RSEQ values: the new run's fresh variables sit 5 above the recorded
   ones up to the old 334 and 7 above from the old 335 on (old 100 is new 105 at [PBump 100]; old 399
   is new 406 at [PBump 399]; the run reaches the hand-offs with counter 521 where the recorded states
   have 514).  The hand-off table is collected by rerunning the check at r = 0 and r = 1 from the empty
   table ([PlanRegen.collect_runs]); one table serves both values.  The recorded states
   ([C1HSRec], in the launch layout the plan was written against) fix the order of the facts each
   computed state keeps ([PlanRegen.keep_facts]); every kept fact is the run's own, and [C1Cert]
   checks the run against these states again. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CxPlan HAPlanImage HAAtable HACheck0 C1 C1HSRec PlanRegen.
Import ListNotations. Import AX2. Import APC. Import CAP.
Open Scope Z_scope.

Definition C1_F : nat -> nat := vshift_tab [(13%nat, 5%nat); (335%nat, 2%nat)].
Definition c1_plan_r : plan := psh C1_F c1_plan.
Definition C1_IT0 : itab := APC.mk_itab_ranges HASEGS c1_ranges.
Definition c1_run (r : Z) (hs : nat -> option acs) : cres :=
  CAP.check HASEGS C1_IT0 HAT NX0 AsanInit.LIMIT ha0_XN ha0_XE ha0_XB hs 0 true false true 400000 3000 None
    (init_acs_r r HAT) c1_plan_r.
Definition C1_HSL : list (nat * acs) := Eval vm_compute in collect_runs 2 [c1_run 0; c1_run 1] [].

Definition c1_hs0_ (_ : unit) : acs := Eval vm_compute in
  keep_facts NX0 (ash C1_F c1_hs0_rec) (hstate C1_HSL c1_hs0_rec 0).
Abbreviation c1_hs0 := (c1_hs0_ tt).
Definition c1_hs1_ (_ : unit) : acs := Eval vm_compute in
  keep_facts NX0 (ash C1_F c1_hs1_rec) (hstate C1_HSL c1_hs1_rec 1).
Abbreviation c1_hs1 := (c1_hs1_ tt).

Definition C1_HS (h : nat) : option acs := match h with 0%nat => Some c1_hs0 | 1%nat => Some c1_hs1 | _ => None end.
#[global] Opaque c1_hs0_ c1_hs1_.
