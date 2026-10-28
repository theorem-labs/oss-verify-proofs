(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import PropExec AsanAcct AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanRehash AsanRehashSound AsanRehashBridge A_PlanImage A_Atable A_HooksDefs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import RT_ibase XR_rehash.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)

Lemma A_seg_below : forall a : word, find_segment A_SEGS (bv_unsigned a) 1 <> None -> bv_unsigned a < 2 ^ 47.
Proof.
  intros a H. destruct (APS.in_hull A_T (bv_unsigned a)) eqn:E; [| exfalso; apply H; exact (A_t_in_hull a E)].
  unfold APS.in_hull in E. apply andb_prop in E as [_ E]. apply Z.ltb_lt in E.
  pose proof A_t_if_hull as (_ & Hh & _). lia.
Qed.

Theorem A_rehash_contract : RHNS.rehash_contract A_SEGS A_RT (img_lo A_T) (img_hi A_T).
Proof.
  apply (RHB.rehash_contract_of_walk A_SEGS A_RT (img_lo A_T) (img_hi A_T) A_seg_below A_t_segs_wx).
  - pose proof A_t_if_hull as ((Hl & _) & _). exact Hl.
  - exact xr_rehash_spec.
Qed.
