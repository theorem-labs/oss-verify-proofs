(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the recorded hand-off states replaced by the states seg91 and seg94 reach at LPS 727298f3, computed in the build, one per CONFIG_RSEQ value; the plans renumbered by a map read from a probe. *)
(* [comment removed for export] *)

(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab
  AsImages AsPlanImages AsStartup AsStartupPlan AsStartupRanges AsPlanRegen AsStartupHS1 AsStartupHSC.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

(* LPS 727298f3: the states at hand-offs 100 .. 105, computed in the build from each CONFIG_RSEQ
   value's states at 91 and 94; seg91 and seg94 renumbered by [vsh_91] (the same map, a probe of the run: seg91 and seg94 reach 100 .. 105 at both values with the fresh counter at 450 = 443 + 7). *)
Definition vsh_91 : nat -> nat := tshift [(13%nat, 5%nat); (326%nat, 7%nat)].
Definition startup_plan_seg91_k : plan := psh vsh_91 startup_plan_seg91.
Definition startup_plan_seg94_k : plan := psh vsh_91 startup_plan_seg94.
Definition seg_run (xr : list (Z * nat)) (p : plan) (s : acs) (T : nat -> option acs) : cres :=
  check ASEGS (mk_itab_ranges ASEGS xr) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 T CERT_KC0 CERT_BFUEL CERT_FUEL None s p.
Definition HSA_asan_list_0 : list (nat * acs) := Eval vm_compute in collect_runs 2 [seg_run startup_plan_seg91_xranges startup_plan_seg91_k HSC_asan_91_0; seg_run startup_plan_seg94_xranges startup_plan_seg94_k HSC_asan_94_0] [].
Definition HSA_asan_list_1 : list (nat * acs) := Eval vm_compute in collect_runs 2 [seg_run startup_plan_seg91_xranges startup_plan_seg91_k HSC_asan_91_1; seg_run startup_plan_seg94_xranges startup_plan_seg94_k HSC_asan_94_1] [].
Definition HSA_asan_100_0 : acs := Eval vm_compute in hstate HSA_asan_list_0 HSC_asan_91_0 100.
Definition HSA_asan_101_0 : acs := Eval vm_compute in hstate HSA_asan_list_0 HSC_asan_91_0 101.
Definition HSA_asan_102_0 : acs := Eval vm_compute in hstate HSA_asan_list_0 HSC_asan_91_0 102.
Definition HSA_asan_103_0 : acs := Eval vm_compute in hstate HSA_asan_list_0 HSC_asan_91_0 103.
Definition HSA_asan_104_0 : acs := Eval vm_compute in hstate HSA_asan_list_0 HSC_asan_91_0 104.
Definition HSA_asan_105_0 : acs := Eval vm_compute in hstate HSA_asan_list_0 HSC_asan_91_0 105.
Definition HSA_asan_100_1 : acs := Eval vm_compute in hstate HSA_asan_list_1 HSC_asan_91_1 100.
Definition HSA_asan_101_1 : acs := Eval vm_compute in hstate HSA_asan_list_1 HSC_asan_91_1 101.
Definition HSA_asan_102_1 : acs := Eval vm_compute in hstate HSA_asan_list_1 HSC_asan_91_1 102.
Definition HSA_asan_103_1 : acs := Eval vm_compute in hstate HSA_asan_list_1 HSC_asan_91_1 103.
Definition HSA_asan_104_1 : acs := Eval vm_compute in hstate HSA_asan_list_1 HSC_asan_91_1 104.
Definition HSA_asan_105_1 : acs := Eval vm_compute in hstate HSA_asan_list_1 HSC_asan_91_1 105.
Definition HSA_asan_table_0 : list (nat * acs) := [(100%nat, HSA_asan_100_0); (101%nat, HSA_asan_101_0); (102%nat, HSA_asan_102_0); (103%nat, HSA_asan_103_0); (104%nat, HSA_asan_104_0); (105%nat, HSA_asan_105_0)].
Definition HSA_asan_table_1 : list (nat * acs) := [(100%nat, HSA_asan_100_1); (101%nat, HSA_asan_101_1); (102%nat, HSA_asan_102_1); (103%nat, HSA_asan_103_1); (104%nat, HSA_asan_104_1); (105%nat, HSA_asan_105_1)].
Definition HSA_asan_0 (h : nat) : option acs := hs_lookup h HSA_asan_table_0.
Definition HSA_asan_1 (h : nat) : option acs := hs_lookup h HSA_asan_table_1.
Definition HSA_asan_r (r : Z) : nat -> option acs := if Z.eqb r 1 then HSA_asan_1 else HSA_asan_0.
