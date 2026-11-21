(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the recorded hand-off states replaced by the states seg100 .. seg105 reach at LPS 727298f3 from both CONFIG_RSEQ values, computed in the build and met into one table; the plans renumbered by a map read from a probe. *)
(* [comment removed for export] *)

(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab
  BothImages BothPlanImages BoStartup BoStartupPlan BoStartupRanges AsPlanRegen BoStartupHS1 BoStartupHSC BoStartupHSA.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* LPS 727298f3: the main entry's states, hand-offs 0 .. 5, computed in the build: seg100 .. seg105
   renumbered by [vsh_100] (the same map, a probe of the run: seg100 .. seg105 reach the six main-entry hand-offs from both values with the fresh counter at 6609 = 6602 + 7), run from both CONFIG_RSEQ values' states at 100 .. 105, and the
   two values' states at each hand-off met ([AsPlanRegen.join_states]: equal registers, maps and
   bounds, a probe of the run: each of the twelve runs checks against the met table), so the main phase reads one table.  [vsh_main] is the numbering the main phase's
   recorded constants move by. *)
Definition vsh_100 : nat -> nat := tshift [(13%nat, 5%nat); (326%nat, 7%nat)].
Definition vsh_main : nat -> nat := vsh_100.
Definition startup_plan_seg100_k : plan := psh vsh_100 startup_plan_seg100.
Definition startup_plan_seg101_k : plan := psh vsh_100 startup_plan_seg101.
Definition startup_plan_seg102_k : plan := psh vsh_100 startup_plan_seg102.
Definition startup_plan_seg103_k : plan := psh vsh_100 startup_plan_seg103.
Definition startup_plan_seg104_k : plan := psh vsh_100 startup_plan_seg104.
Definition startup_plan_seg105_k : plan := psh vsh_100 startup_plan_seg105.
Definition HSF_both_list : list (nat * acs) := Eval vm_compute in collect_runs 2 [seg_run startup_plan_seg100_xranges startup_plan_seg100_k HSA_both_100_0; seg_run startup_plan_seg101_xranges startup_plan_seg101_k HSA_both_101_0; seg_run startup_plan_seg102_xranges startup_plan_seg102_k HSA_both_102_0; seg_run startup_plan_seg103_xranges startup_plan_seg103_k HSA_both_103_0; seg_run startup_plan_seg104_xranges startup_plan_seg104_k HSA_both_104_0; seg_run startup_plan_seg105_xranges startup_plan_seg105_k HSA_both_105_0; seg_run startup_plan_seg100_xranges startup_plan_seg100_k HSA_both_100_1; seg_run startup_plan_seg101_xranges startup_plan_seg101_k HSA_both_101_1; seg_run startup_plan_seg102_xranges startup_plan_seg102_k HSA_both_102_1; seg_run startup_plan_seg103_xranges startup_plan_seg103_k HSA_both_103_1; seg_run startup_plan_seg104_xranges startup_plan_seg104_k HSA_both_104_1; seg_run startup_plan_seg105_xranges startup_plan_seg105_k HSA_both_105_1] [].
Definition HSF_both_0 : acs := Eval vm_compute in hstate HSF_both_list HSA_both_100_0 0.
Definition HSF_both_1 : acs := Eval vm_compute in hstate HSF_both_list HSA_both_100_0 1.
Definition HSF_both_2 : acs := Eval vm_compute in hstate HSF_both_list HSA_both_100_0 2.
Definition HSF_both_3 : acs := Eval vm_compute in hstate HSF_both_list HSA_both_100_0 3.
Definition HSF_both_4 : acs := Eval vm_compute in hstate HSF_both_list HSA_both_100_0 4.
Definition HSF_both_5 : acs := Eval vm_compute in hstate HSF_both_list HSA_both_100_0 5.

Definition HSF_both_table : list (nat * acs) := [(0%nat, HSF_both_0); (1%nat, HSF_both_1); (2%nat, HSF_both_2); (3%nat, HSF_both_3); (4%nat, HSF_both_4); (5%nat, HSF_both_5)].
Definition HSF_both (h : nat) : option acs := hs_lookup h HSF_both_table.
