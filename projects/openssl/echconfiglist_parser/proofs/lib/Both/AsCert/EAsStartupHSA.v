(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the recorded hand-off states replaced by the states seg91 and seg94 reach at LPS 727298f3 from both CONFIG_RSEQ values, computed in the build and met into one table; the plans renumbered by a map read from a probe; the recorded states kept in EAsStartupHSARec.v. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanInit AsHSTab AsPlanRegen.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages AsStartup EAsStartupPlan EAsStartupRanges EAsStartupHS1 EAsStartupHSC.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* LPS 727298f3: the S6 hand-offs 0 .. 3, computed in the build: seg91 and seg94 from both CONFIG_RSEQ
   values' states at 91 and 94, met into ONE table ([collect_runs]: a missing state becomes the reached
   one, a state another run does not entail becomes the join of the two); [vsh_s6] (seg91 and seg94 from both values' states at 91 and 94 reach the S6 hand-offs 0 .. 3 at counter 463 (recorded 455) with the seg90 map unchanged; every one of the four runs checks against the met table).
   [EAsStartupCerts.cert3] re-checks every value's run against this table. *)
Definition vsh_s6 : nat -> nat := tshift [(44%nat, 6%nat); (326%nat, 8%nat)].
Definition startup_plan_seg91_k : plan := psh vsh_s6 startup_plan_seg91.
Definition startup_plan_seg94_k : plan := psh vsh_s6 startup_plan_seg94.
Definition seg_run (xr : list (Z * nat)) (p : plan) (s : acs) (T : nat -> option acs) : cres :=
  check ASEGS (mk_itab_ranges ASEGS xr) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 T 0%nat 400000%nat 3000%nat None s p.
Definition HSA_easan_list : list (nat * acs) := Eval vm_compute in collect_runs 3 [seg_run startup_plan_seg91_xranges startup_plan_seg91_k HSC_easan_91_0; seg_run startup_plan_seg94_xranges startup_plan_seg94_k HSC_easan_94_0; seg_run startup_plan_seg91_xranges startup_plan_seg91_k HSC_easan_91_1; seg_run startup_plan_seg94_xranges startup_plan_seg94_k HSC_easan_94_1] [].
Definition HSA_easan_0 : acs := Eval vm_compute in hstate HSA_easan_list HSC_easan_91_0 0.
Definition HSA_easan_1 : acs := Eval vm_compute in hstate HSA_easan_list HSC_easan_91_0 1.
Definition HSA_easan_2 : acs := Eval vm_compute in hstate HSA_easan_list HSC_easan_91_0 2.
Definition HSA_easan_3 : acs := Eval vm_compute in hstate HSA_easan_list HSC_easan_91_0 3.

Definition HSA_easan_table : list (nat * acs) := [(0%nat, HSA_easan_0); (1%nat, HSA_easan_1); (2%nat, HSA_easan_2); (3%nat, HSA_easan_3)].
Definition HSA_easan (h : nat) : option acs := hs_lookup h HSA_easan_table.
