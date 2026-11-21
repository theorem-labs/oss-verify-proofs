(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: lemmas added for the revision. *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab
  AsStartupPlan AsImages AsPlanImages AsStartup AsanPlanF AsPlanRegen AsStartupHS1 AsStartupHSC.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

(* LPS 727298f3, design 1: the hand-off states at 100..105, per CONFIG_RSEQ value, collected
   from that value's runs of segments 91 and 94 (under [G1]) into one table per value. *)
Definition startup_plan_seg91_k : plan := psh G1 startup_plan_seg91.
Definition startup_plan_seg94_k : plan := psh G1 startup_plan_seg94.

Definition seg91_run (S : acs) (js : nat -> option acs) : cres :=
  FC.check_f ASEGS (mk_itab_ranges ASEGS startup_plan_seg91_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 js
    CERT_KC0 CERT_BFUEL CERT_FUEL None S startup_plan_seg91_k.
Definition seg94_run (S : acs) (js : nat -> option acs) : cres :=
  FC.check_f ASEGS (mk_itab_ranges ASEGS startup_plan_seg94_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 js
    CERT_KC0 CERT_BFUEL CERT_FUEL None S startup_plan_seg94_k.

Definition HSA_asan_list_r0 : list (nat * acs) := Eval vm_compute in
  collect_handoffs 8 (seg94_run HSC_asan_94_r0) (collect_handoffs 8 (seg91_run HSC_asan_91_r0) []).
Definition HSA_asan_100_r0 : acs := Eval vm_compute in hstate HSA_asan_list_r0 HSC_asan_91_r0 100.
Definition HSA_asan_101_r0 : acs := Eval vm_compute in hstate HSA_asan_list_r0 HSC_asan_91_r0 101.
Definition HSA_asan_102_r0 : acs := Eval vm_compute in hstate HSA_asan_list_r0 HSC_asan_91_r0 102.
Definition HSA_asan_103_r0 : acs := Eval vm_compute in hstate HSA_asan_list_r0 HSC_asan_91_r0 103.
Definition HSA_asan_104_r0 : acs := Eval vm_compute in hstate HSA_asan_list_r0 HSC_asan_91_r0 104.
Definition HSA_asan_105_r0 : acs := Eval vm_compute in hstate HSA_asan_list_r0 HSC_asan_91_r0 105.
Definition HSA_asan_table_r0 : list (nat * acs) := [(100%nat, HSA_asan_100_r0); (101%nat, HSA_asan_101_r0); (102%nat, HSA_asan_102_r0); (103%nat, HSA_asan_103_r0); (104%nat, HSA_asan_104_r0); (105%nat, HSA_asan_105_r0)].
Definition HSA_asan_r0 (h : nat) : option acs := hs_lookup h HSA_asan_table_r0.

Definition HSA_asan_list_r1 : list (nat * acs) := Eval vm_compute in
  collect_handoffs 8 (seg94_run HSC_asan_94_r1) (collect_handoffs 8 (seg91_run HSC_asan_91_r1) []).
Definition HSA_asan_100_r1 : acs := Eval vm_compute in hstate HSA_asan_list_r1 HSC_asan_91_r1 100.
Definition HSA_asan_101_r1 : acs := Eval vm_compute in hstate HSA_asan_list_r1 HSC_asan_91_r1 101.
Definition HSA_asan_102_r1 : acs := Eval vm_compute in hstate HSA_asan_list_r1 HSC_asan_91_r1 102.
Definition HSA_asan_103_r1 : acs := Eval vm_compute in hstate HSA_asan_list_r1 HSC_asan_91_r1 103.
Definition HSA_asan_104_r1 : acs := Eval vm_compute in hstate HSA_asan_list_r1 HSC_asan_91_r1 104.
Definition HSA_asan_105_r1 : acs := Eval vm_compute in hstate HSA_asan_list_r1 HSC_asan_91_r1 105.
Definition HSA_asan_table_r1 : list (nat * acs) := [(100%nat, HSA_asan_100_r1); (101%nat, HSA_asan_101_r1); (102%nat, HSA_asan_102_r1); (103%nat, HSA_asan_103_r1); (104%nat, HSA_asan_104_r1); (105%nat, HSA_asan_105_r1)].
Definition HSA_asan_r1 (h : nat) : option acs := hs_lookup h HSA_asan_table_r1.

Definition HSA_asan_k (b : bool) := if b then HSA_asan_r1 else HSA_asan_r0.
