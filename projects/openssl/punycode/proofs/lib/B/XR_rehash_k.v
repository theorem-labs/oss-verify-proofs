(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec AsanAcct AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanRehash AsanRehashSound AsanRehashBridge B_PlanImage B_Atable B_HooksDefs.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import RT_iface XR_rehash.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)

Lemma A_seg_below : forall a : word, find_segment B_SEGS (bv_unsigned a) 1 <> None -> bv_unsigned a < 2 ^ 47.
Proof.
  intros a H. destruct (APS.in_hull B_T (bv_unsigned a)) eqn:E; [| exfalso; apply H; exact (B_t_in_hull a E)].
  unfold APS.in_hull in E. apply andb_prop in E as [_ E]. apply Z.ltb_lt in E.
  pose proof B_t_if_hull as (_ & Hh & _). lia.
Qed.

Theorem A_rehash_contract : RHNS.rehash_contract B_SEGS B_RT (img_lo B_T) (img_hi B_T).
Proof.
  apply (RHB.rehash_contract_of_walk B_SEGS B_RT (img_lo B_T) (img_hi B_T) A_seg_below B_t_segs_wx).
  - pose proof B_t_if_hull as ((Hl & _) & _). exact Hl.
  - exact xr_rehash_spec.
Qed.
