(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the post hand-off state and post join state are computed at each compile for each launch rseq layout by MainCol.mc_loop, in place of the recorded state, and post_plan moved here from PostPlanAsan.v. *)
(* The post hand-off state (main's start) and the post join state are computed at each compile,
   per launch layout r, by MainCol.mc_loop from an empty hand-off table; [post_plan] is defined
   here, not in PostPlanAsan.v, so that it carries the computed join state. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan StartupHooks StartupHSAsan PostPlanAsan PostJoinAsan MainCol.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition post_asan_SEGS : list Segment := Asan.M.loaded_segments.
Definition post_asan_IT : itab := mk_itab_ranges post_asan_SEGS post_plan_ranges.

(* The post certificate's own check (AsanPostCert.v), from the computed start-up hand-off state, under table HS. *)
Definition po_chk (rsb : bool) (HS : nat -> option acs) (p : plan) : cres :=
  check post_asan_SEGS post_asan_IT (ASAN_at (rseq_z rsb)) NX0 target_alloc_limit XNdA XE0 XB0 HS 0%nat 400000%nat 3000%nat None
        (HS_asan_0 (rseq_z rsb)) p.
(* The collection, per r, from an EMPTY hand-off table, as StartupHSAsan.v's: hole 0's entry is the arriving state
   (code 4, then meets on code 3); the join state starts from PostJoinAsan.v's collector seed [JS_POST r] and a
   refused [PMerge 2] replaces it by the arrivals. [VarShift.vsh]'s offset rests on the hole-0 state's next
   variable being 50. Nothing here is trusted: AsanPostCert.v re-checks it. *)
Definition po_run (rsb : bool) : mc_out :=
  mc_loop (po_chk rsb) (post_plan_of (JS_POST (rseq_z rsb))) 40 [] [] [] [] [].
Definition PO_RUN1 : mc_out := Eval vm_compute in po_run true.
Definition PO_RUN0 : mc_out := Eval vm_compute in po_run false.

Definition HS_mainA_0_r1 : acs := Eval vm_compute in jlook (mc_holes PO_RUN1) 0 (HS_asan_0 1).
Definition HS_mainA_0_r0 : acs := Eval vm_compute in jlook (mc_holes PO_RUN0) 0 (HS_asan_0 0).
Definition JS_POSTc_r1 : acs := Eval vm_compute in jlook (mc_joins PO_RUN1) 2 (JS_POST 1).
Definition JS_POSTc_r0 : acs := Eval vm_compute in jlook (mc_joins PO_RUN0) 2 (JS_POST 0).

Definition HS_mainA_0 (r : Z) : acs := if Z.eqb r 1 then HS_mainA_0_r1 else HS_mainA_0_r0.
Definition HS_mainA (r : Z) (h : nat) : option acs :=
  match h with | 0%nat => Some (HS_mainA_0 r) | _ => None end.
Definition JS_POSTc (r : Z) : acs := if Z.eqb r 1 then JS_POSTc_r1 else JS_POSTc_r0.
(* The shipped post plan for launch layout r. *)
Definition post_plan (r : Z) : plan := post_plan_of (JS_POSTc r).
