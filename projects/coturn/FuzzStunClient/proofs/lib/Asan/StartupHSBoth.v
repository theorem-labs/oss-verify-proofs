(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the start-up hand-off state and join states are computed at each compile for each launch rseq layout by MainCol.mc_loop, in place of the recorded state, and startup_plan moved here from StartupPlanBoth.v. *)
(* The start-up's hand-off state and join states are computed at each compile, per launch layout r,
   by MainCol.mc_loop from an empty hand-off table; [startup_plan] is defined here, not in
   StartupPlanBoth.v, so that it carries the computed join states. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan StartupHooks StartupPlanBoth StartupJoinBoth StartupJoin2Both MainCol.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition startup_both_SEGS : list Segment := AsanUbsan.M.loaded_segments.
Definition startup_both_IT : itab := mk_itab_ranges startup_both_SEGS startup_plan_ranges.

(* The start-up certificate's own check (BothStartupCert.v), under hand-off table HS. *)
Definition su_chk (rsb : bool) (HS : nat -> option acs) (p : plan) : cres :=
  check startup_both_SEGS startup_both_IT (BOTH_at (rseq_z rsb)) NX0 target_alloc_limit XN0 XE0 XB0 HS 0%nat 400000%nat 3000%nat None
        (both_init (rseq_z rsb)) p.
(* The collection, per r (rsb = true: r = 1; rsb = false: r = 0), from an EMPTY hand-off table: the first arrival at
   [PHandoff 0] is missing (code 4) and becomes hole 0's entry; each later refused arrival (code 3) is met into it
   ([MainCol.mc_next]); the run ends when the check passes. The join states start from the collector seeds of
   StartupJoinBoth.v ([JS_S2 r]) and StartupJoin2Both.v ([JS_BRK r]): the continuation after a [PVia] is checked
   from its join state before the arms are, so a join needs a start value; a refused [PMerge j] replaces join j
   by the arrivals.
   Nothing here is trusted: BothStartupCert.v re-checks the plan against these states. *)
Definition su_run (rsb : bool) : mc_out :=
  mc_loop (su_chk rsb) (startup_plan_of (JS_S2 (rseq_z rsb)) (JS_BRK (rseq_z rsb))) 40 [] [] [] [] [].
Definition SU_RUN1 : mc_out := Eval vm_compute in su_run true.
Definition SU_RUN0 : mc_out := Eval vm_compute in su_run false.

Definition HS_both_0_r1 : acs := Eval vm_compute in jlook (mc_holes SU_RUN1) 0 (both_init 1).
Definition HS_both_0_r0 : acs := Eval vm_compute in jlook (mc_holes SU_RUN0) 0 (both_init 0).
Definition JS_S2c_r1 : acs := Eval vm_compute in jlook (mc_joins SU_RUN1) 0 (JS_S2 1).
Definition JS_S2c_r0 : acs := Eval vm_compute in jlook (mc_joins SU_RUN0) 0 (JS_S2 0).
Definition JS_BRKc_r1 : acs := Eval vm_compute in jlook (mc_joins SU_RUN1) 1 (JS_BRK 1).
Definition JS_BRKc_r0 : acs := Eval vm_compute in jlook (mc_joins SU_RUN0) 1 (JS_BRK 0).

Definition HS_both_0 (r : Z) : acs := if Z.eqb r 1 then HS_both_0_r1 else HS_both_0_r0.
Definition HS_both (r : Z) (h : nat) : option acs :=
  match h with | 0%nat => Some (HS_both_0 r) | _ => None end.
Definition JS_S2c (r : Z) : acs := if Z.eqb r 1 then JS_S2c_r1 else JS_S2c_r0.
Definition JS_BRKc (r : Z) : acs := if Z.eqb r 1 then JS_BRKc_r1 else JS_BRKc_r0.
(* The shipped start-up plan for launch layout r. *)
Definition startup_plan (r : Z) : plan := startup_plan_of (JS_S2c r) (JS_BRKc r).
