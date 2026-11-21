(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: lemmas added for the revision. *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab
  AsStartupPlan AsImages AsPlanImages AsStartup AsanPlanF AsPlanRegen AsStartupHS1 AsStartupHSC AsStartupHSA.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

(* LPS 727298f3, design 1: the main phase's entry states, hand-offs 0..5, ONE table for both
   CONFIG_RSEQ values: collected from the r = 0 runs of segments 100..105 (under [G1]) and then
   from the r = 1 runs, a state one run does not entail joined with the one it reaches
   ([collect_handoffs]).  At these hand-offs the two values' states differ only in the auxv
   tail facts (the CONFIG_RSEQ pairs, AT_NULL, the vector's length), which the join drops
   (Probe 4, a farm round). *)
Definition startup_plan_seg100_k : plan := psh G1 startup_plan_seg100.
Definition startup_plan_seg101_k : plan := psh G1 startup_plan_seg101.
Definition startup_plan_seg102_k : plan := psh G1 startup_plan_seg102.
Definition startup_plan_seg103_k : plan := psh G1 startup_plan_seg103.
Definition startup_plan_seg104_k : plan := psh G1 startup_plan_seg104.
Definition startup_plan_seg105_k : plan := psh G1 startup_plan_seg105.

Definition seg100_run (S : acs) (js : nat -> option acs) : cres :=
  FC.check_f ASEGS (mk_itab_ranges ASEGS startup_plan_seg100_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 js
    CERT_KC0 CERT_BFUEL CERT_FUEL None S startup_plan_seg100_k.
Definition seg101_run (S : acs) (js : nat -> option acs) : cres :=
  FC.check_f ASEGS (mk_itab_ranges ASEGS startup_plan_seg101_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 js
    CERT_KC0 CERT_BFUEL CERT_FUEL None S startup_plan_seg101_k.
Definition seg102_run (S : acs) (js : nat -> option acs) : cres :=
  FC.check_f ASEGS (mk_itab_ranges ASEGS startup_plan_seg102_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 js
    CERT_KC0 CERT_BFUEL CERT_FUEL None S startup_plan_seg102_k.
Definition seg103_run (S : acs) (js : nat -> option acs) : cres :=
  FC.check_f ASEGS (mk_itab_ranges ASEGS startup_plan_seg103_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 js
    CERT_KC0 CERT_BFUEL CERT_FUEL None S startup_plan_seg103_k.
Definition seg104_run (S : acs) (js : nat -> option acs) : cres :=
  FC.check_f ASEGS (mk_itab_ranges ASEGS startup_plan_seg104_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 js
    CERT_KC0 CERT_BFUEL CERT_FUEL None S startup_plan_seg104_k.
Definition seg105_run (S : acs) (js : nat -> option acs) : cres :=
  FC.check_f ASEGS (mk_itab_ranges ASEGS startup_plan_seg105_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 js
    CERT_KC0 CERT_BFUEL CERT_FUEL None S startup_plan_seg105_k.

Definition HSF_asan_list : list (nat * acs) := Eval vm_compute in
  collect_handoffs 8 (seg105_run HSA_asan_105_r1) (collect_handoffs 8 (seg104_run HSA_asan_104_r1) (collect_handoffs 8 (seg103_run HSA_asan_103_r1) (collect_handoffs 8 (seg102_run HSA_asan_102_r1) (collect_handoffs 8 (seg101_run HSA_asan_101_r1) (collect_handoffs 8 (seg100_run HSA_asan_100_r1) (collect_handoffs 8 (seg105_run HSA_asan_105_r0) (collect_handoffs 8 (seg104_run HSA_asan_104_r0) (collect_handoffs 8 (seg103_run HSA_asan_103_r0) (collect_handoffs 8 (seg102_run HSA_asan_102_r0) (collect_handoffs 8 (seg101_run HSA_asan_101_r0) (collect_handoffs 8 (seg100_run HSA_asan_100_r0) ([])))))))))))).
Definition HSF_asan_0 : acs := Eval vm_compute in hstate HSF_asan_list HSA_asan_100_r0 0.
Definition HSF_asan_1 : acs := Eval vm_compute in hstate HSF_asan_list HSA_asan_100_r0 1.
Definition HSF_asan_2 : acs := Eval vm_compute in hstate HSF_asan_list HSA_asan_100_r0 2.
Definition HSF_asan_3 : acs := Eval vm_compute in hstate HSF_asan_list HSA_asan_100_r0 3.
Definition HSF_asan_4 : acs := Eval vm_compute in hstate HSF_asan_list HSA_asan_100_r0 4.
Definition HSF_asan_5 : acs := Eval vm_compute in hstate HSF_asan_list HSA_asan_100_r0 5.
Definition HSF_asan_table : list (nat * acs) := [(0%nat, HSF_asan_0); (1%nat, HSF_asan_1); (2%nat, HSF_asan_2); (3%nat, HSF_asan_3); (4%nat, HSF_asan_4); (5%nat, HSF_asan_5)].
Definition HSF_asan (h : nat) : option acs := hs_lookup h HSF_asan_table.
