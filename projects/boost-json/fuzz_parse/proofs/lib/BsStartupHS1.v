(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: lemmas added for the revision. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab
  BsStartupPlan BothImages BothPlanImages BsStartup AsanPlanF AsPlanRegen.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

(* LPS 727298f3, design 1 (OSSV-509): the start-up hand-off states are computed in the build,
   never recorded, ONE CHAIN PER CONFIG_RSEQ VALUE: the root, segment 90, segments 91/94 and
   segments 100..105 are each checked from the value's own states ([_r0] for r = 0, [_r1] for
   r = 1, selected by [_k]), and only the main-phase entry table ([AsStartupHSF]) is joined over
   both values.  A table joined earlier fails: segment 90 run from the state at 90 joined over
   both values stops before any hand-off (probe record notes/probe-boost-json__fuzz_parse.md,
   Probe 4, a farm round), and per value every segment checks COk (Probe 4,
   a farm round).
   The root plan is checked renumbered: at the revision the launch has three variables of its
   own more than the plans were written against ([V_G] 11, [V_R] 12, [V_GID] 13, [NX0] 14), so
   every new variable the run adds moves up.  The map is read from the run (Probe 3): the
   unrenumbered root run stops at its first [PRangeGaps 94] with a0 = 4096 * EVar 99, so from
   main's first fresh variable 11 every number moves by 5 (a farm round). *)
Definition G0 : nat -> nat := vshift 11 5.
Definition startup_plan_k : plan := psh G0 startup_plan.

Definition root_check (r : Z) (js : nat -> option acs) : cres :=
  FC.check_f ASEGS (mk_itab_ranges ASEGS startup_plan_xranges) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 js
    CERT_KC0 CERT_BFUEL CERT_FUEL None (hinit r) startup_plan_k.

Definition HS1_asan_list_r0 : list (nat * acs) := Eval vm_compute in collect_handoffs 4 (root_check 0) [].
Definition HS1_asan_90_r0 : acs := Eval vm_compute in hstate HS1_asan_list_r0 (hinit 0) 90.
Definition HS1_asan_table_r0 : list (nat * acs) := [(90%nat, HS1_asan_90_r0)].
Definition HS1_asan_r0 (h : nat) : option acs := hs_lookup h HS1_asan_table_r0.

Definition HS1_asan_list_r1 : list (nat * acs) := Eval vm_compute in collect_handoffs 4 (root_check 1) [].
Definition HS1_asan_90_r1 : acs := Eval vm_compute in hstate HS1_asan_list_r1 (hinit 1) 90.
Definition HS1_asan_table_r1 : list (nat * acs) := [(90%nat, HS1_asan_90_r1)].
Definition HS1_asan_r1 (h : nat) : option acs := hs_lookup h HS1_asan_table_r1.

Definition HS1_asan_k (b : bool) := if b then HS1_asan_r1 else HS1_asan_r0.
