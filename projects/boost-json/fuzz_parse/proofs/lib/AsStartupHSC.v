(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: lemmas added for the revision. *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab
  AsStartupPlan AsImages AsPlanImages AsStartup AsanPlanF AsPlanRegen AsStartupHS1.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

(* LPS 727298f3, design 1: segment 90 and every later segment are checked under [G1], the
   root map followed by one more step read from the run: under [G0] segment 90 stops at
   [PRangeGaps 331] with a0 = 4096 * EVar 333, so from 331 every number moves by 2 more
   (Probe 3, a farm round; no later segment needed a step).  The hand-off
   states at 91 and 94 are collected, per CONFIG_RSEQ value, from the run of segment 90 from
   that value's state at 90. *)
Definition G1 (v : nat) : nat := vshift 331 2 (G0 v).
Definition startup_plan_seg90_k : plan := psh G1 startup_plan_seg90.

Definition seg90_run (S : acs) (js : nat -> option acs) : cres :=
  FC.check_f ASEGS (mk_itab_ranges ASEGS startup_plan_seg90_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 js
    CERT_KC0 CERT_BFUEL CERT_FUEL None S startup_plan_seg90_k.

Definition HSC_asan_list_r0 : list (nat * acs) := Eval vm_compute in collect_handoffs 6 (seg90_run HS1_asan_90_r0) [].
Definition HSC_asan_91_r0 : acs := Eval vm_compute in hstate HSC_asan_list_r0 HS1_asan_90_r0 91.
Definition HSC_asan_94_r0 : acs := Eval vm_compute in hstate HSC_asan_list_r0 HS1_asan_90_r0 94.
Definition HSC_asan_table_r0 : list (nat * acs) := [(91%nat, HSC_asan_91_r0); (94%nat, HSC_asan_94_r0)].
Definition HSC_asan_r0 (h : nat) : option acs := hs_lookup h HSC_asan_table_r0.

Definition HSC_asan_list_r1 : list (nat * acs) := Eval vm_compute in collect_handoffs 6 (seg90_run HS1_asan_90_r1) [].
Definition HSC_asan_91_r1 : acs := Eval vm_compute in hstate HSC_asan_list_r1 HS1_asan_90_r1 91.
Definition HSC_asan_94_r1 : acs := Eval vm_compute in hstate HSC_asan_list_r1 HS1_asan_90_r1 94.
Definition HSC_asan_table_r1 : list (nat * acs) := [(91%nat, HSC_asan_91_r1); (94%nat, HSC_asan_94_r1)].
Definition HSC_asan_r1 (h : nat) : option acs := hs_lookup h HSC_asan_table_r1.

Definition HSC_asan_k (b : bool) := if b then HSC_asan_r1 else HSC_asan_r0.
