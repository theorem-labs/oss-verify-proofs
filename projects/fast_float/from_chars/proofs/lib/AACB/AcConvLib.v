(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChFix FxChSep FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_put3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcHA AcEntry AcCarve AcConv AcConvInvLib AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDepDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvInvLib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDepDen.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Record convp : Type := CONVP { cq_tab : nat ; cq_ss : nat ; cq_d1 : nat ; cq_b1 : nat }.
Definition cq_list (q : convp) : list nat := [cq_tab q; cq_ss q; cq_d1 q; cq_b1 q].
Definition keep_ix (len : nat) (q : convp) : list nat := List.filter (fun k => negb (existsb (Nat.eqb k) (cq_list q))) (seq 0 len).
Definition conv_ix (len : nat) (q : convp) : list nat := keep_ix len q ++ cq_list q.
Definition sm_own_nil (M : smodel) : bool := match sm_own M with [] => true | _ => false end.
Definition rg_tab_b (R : region) : bool :=
  match R with RG b z RZ c => (lin_eqb b (lconst 1865920) && lin_eqb z (lconst 4198400))%bool | _ => false end.
Definition rg_ss_b (R : region) : bool :=
  match R with RG b z RZ c => (lin_eqb b (lconst 1800384) && lin_eqb z (lconst 4096))%bool | _ => false end.
Definition rg_big_b (R : region) (z0 : Z) : bool := match R with RG b z RZ c => lin_eqb z (lconst z0) | _ => false end.

(* [comment removed for export] *)
Lemma res_eq : segments_reserved ASEGS =
  [(Z_to_bv 64 65536, Z_to_bv 64 188416); (Z_to_bv 64 253952, Z_to_bv 64 638976); (Z_to_bv 64 892928, Z_to_bv 64 24576); (Z_to_bv 64 917504, Z_to_bv 64 5619712)].
Proof. vm_compute. reflexivity. Qed.
Lemma res_cov : forall x, 65536 <= x < 6537216 -> covered (segments_reserved ASEGS) x = true.
Proof.
  intros x Hx. rewrite res_eq. unfold covered. cbn [existsb]. unfold in_iv, in_rng, B, S. cbn [fst snd].
  rewrite !u_small64 by (unfold two64; lia).
  destruct (Z_lt_ge_dec x 253952); [rewrite (proj2 (Z.leb_le 65536 x)) by lia; rewrite (proj2 (Z.ltb_lt x (65536 + 188416))) by lia; reflexivity|].
  destruct (Z_lt_ge_dec x 892928); [rewrite (proj2 (Z.leb_le 253952 x)) by lia; rewrite (proj2 (Z.ltb_lt x (253952 + 638976))) by lia; apply orb_true_r|].
  destruct (Z_lt_ge_dec x 917504); [rewrite (proj2 (Z.leb_le 892928 x)) by lia; rewrite (proj2 (Z.ltb_lt x (892928 + 24576))) by lia; rewrite !orb_true_r; reflexivity|].
  rewrite (proj2 (Z.leb_le 917504 x)) by lia. rewrite (proj2 (Z.ltb_lt x (917504 + 5619712))) by lia. rewrite !orb_true_r. reflexivity.
Qed.

Lemma rg_tab_sound : forall R, rg_tab_b R = true -> R = RG (lconst 1865920) (lconst 4198400) RZ (rg_cont R).
Proof.
  intros [b z k c] H. unfold rg_tab_b in H. destruct k; try discriminate. apply andb_prop in H as [H1 H2].
  apply lin_eqb_eq in H1, H2. subst. reflexivity.
Qed.
Lemma rg_ss_sound : forall R, rg_ss_b R = true -> R = RG (lconst 1800384) (lconst 4096) RZ (rg_cont R).
Proof.
  intros [b z k c] H. unfold rg_ss_b in H. destruct k; try discriminate. apply andb_prop in H as [H1 H2].
  apply lin_eqb_eq in H1, H2. subst. reflexivity.
Qed.
Lemma rg_big_sound : forall R z0, rg_big_b R z0 = true -> R = RG (rg_base R) (lconst z0) RZ (rg_cont R).
Proof. intros [b z k c] z0 H. unfold rg_big_b in H. destruct k; try discriminate. apply lin_eqb_eq in H. subst. reflexivity. Qed.
Lemma mod4096_16 : forall x, x mod 4096 = 0 -> x mod 16 = 0.
Proof.
  intros x H. pose proof (Z.div_mod x 4096 ltac:(lia)) as E1. rewrite H, Z.add_0_r in E1. rewrite E1.
  replace (4096 * (x / 4096)) with ((256 * (x / 4096)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma mod4096_8 : forall x, x mod 4096 = 0 -> x mod 8 = 0.
Proof.
  intros x H. pose proof (Z.div_mod x 4096 ltac:(lia)) as E1. rewrite H, Z.add_0_r in E1. rewrite E1.
  replace (4096 * (x / 4096)) with ((512 * (x / 4096)) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma noshadow_range : forall lo z, 0 < z -> (forall w, lo <= w < lo + z -> in_shadow w = false) -> SH_HI <= lo \/ lo + z <= SH_LO.
Proof.
  intros lo z Hz H. destruct (Z_le_gt_dec SH_HI lo) as [X|X]; [left; exact X|]. destruct (Z_le_gt_dec (lo + z) SH_LO) as [Y|Y]; [right; exact Y|].
  exfalso. specialize (H (Z.max lo SH_LO) ltac:(unfold SH_LO, SH_HI in *; lia)). unfold in_shadow in H.
  rewrite (proj2 (Z.leb_le _ _)) in H by lia. rewrite (proj2 (Z.ltb_lt _ _)) in H by (unfold SH_LO, SH_HI in *; lia). discriminate.
Qed.
(* [comment removed for export] *)
