(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeCfg.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue H0PlanImage H0Atable H0Sinv H0CheckG H0Sel H0TgtGlue ConeCfg HTSpec.
From OSSVerify.Proofs.openssl.hashtable.lib Require K0GDrv K0BDrv K1GDrv K1BDrv K2GDrv K2BDrv D3GDrv D3BDrv D4GDrv D4BDrv D5GDrv D5BDrv D6GDrv D6BDrv D7GDrv D7BDrv D8GDrv D8BDrv D9GDrv D9BDrv D10GDrv D10BDrv.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import D10BS0 D10GS0 D3BS0 D3GS0 D4BS0 D4GS0 D5BS0 D5GS0 D6BS0 D6GS0 D7BS0 D7GS0 D8BS0 D8GS0 D9BS0 D9GS0 K0AS0 K0BS0 R1BS0 R1GS0 R2BS0 R2GS0.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import H0FamilyAllDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Theorem family_all : forall (sp0 : word) (k : Z) (content : list byte) (envc : Z) (fs0 : Fs.Fs),
  valid_sp sp0 -> 0 <= envc /\ bv_unsigned sp0 + 192 + 8 * envc < 2 ^ 47 - 32 ->
  forall CS, In CS (CSL k) -> forall (PHIb : env -> Prop) E R' FULL model,
    cs_ok HSEGS H0T 2147483648 (SINVg PHIb sp0 (bv_unsigned sp0 + 192 + 8 * envc)) (argHt (bv_unsigned sp0 + 192 + 8 * envc)) (bv_unsigned sp0) fs0 E CS R' FULL model ->
    EOKc k content CS E ->
    realizes_cfg ConeCfg.CFG HSEGS (mkCfg (mkst R' (Z_to_bv 64 (pc CS)) FULL (PropExec.seg_rom HSEGS)) model) (t_target_ht content fs0).
Proof.
  intros sp0 k content envc fs0 Hsp [He0 He1] CS HCS PHIb E R' FULL model HC HE.
  assert (Hstr : bv_unsigned sp0 + 192 <= bv_unsigned sp0 + 192 + 8 * envc < 2 ^ 47 - 32) by lia.
  assert (Hstr8 : (bv_unsigned sp0 + 192 + 8 * envc) mod 8 = 0).
  { destruct Hsp as (_ & _ & H16). rewrite <- Z.add_assoc, Z.add_mod by lia. assert (H8 : bv_unsigned sp0 mod 8 = 0).
    { rewrite (Z.div_mod (bv_unsigned sp0) 16) by lia. rewrite H16, Z.add_0_r. replace (16 * (bv_unsigned sp0 / 16)) with ((2 * (bv_unsigned sp0 / 16)) * 8) by lia. apply Z.mod_mul. lia. }
    rewrite H8. replace (192 + 8 * envc) with ((24 + envc) * 8) by lia. rewrite Z.mod_mul by lia. reflexivity. }
  pose proof (co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hfs.
  assert (FIN : forall neg calls cnt, crz HSEGS (cfg_of HSEGS R' (pc CS) FULL model) (TGT neg calls cnt (m_fs model)) ->
          ShapeAlg.t_eq (TGT neg calls cnt fs0) (t_target_ht content fs0) ->
          realizes_cfg ConeCfg.CFG HSEGS (mkCfg (mkst R' (Z_to_bv 64 (pc CS)) FULL (PropExec.seg_rom HSEGS)) model) (t_target_ht content fs0)).
  { intros neg calls cnt H1 H2. rewrite Hfs in H1. exact (crz_conseq HSEGS _ _ _ H1 H2). }
  destruct HE as [Htin HE]. unfold CSL in HCS.
  destruct (k =? 0) eqn:Hk0.
  { apply Z.eqb_eq in Hk0. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (K0GDrv.K0G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 HE) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (K0BDrv.K0B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 HE)) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 1) eqn:Hk1.
  { apply Z.eqb_eq in Hk1. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (K1GDrv.K1G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 HE))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (K1BDrv.K1B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 HE)))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 2) eqn:Hk2.
  { apply Z.eqb_eq in Hk2. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (K2GDrv.K2G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 HE))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (K2BDrv.K2B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HE)))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 3) eqn:Hk3.
  { apply Z.eqb_eq in Hk3. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (D3GDrv.D3G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (D3BDrv.D3B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE)))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 4) eqn:Hk4.
  { apply Z.eqb_eq in Hk4. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (D4GDrv.D4G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (D4BDrv.D4B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE)))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 5) eqn:Hk5.
  { apply Z.eqb_eq in Hk5. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (D5GDrv.D5G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (D5BDrv.D5B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE)))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 6) eqn:Hk6.
  { apply Z.eqb_eq in Hk6. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (D6GDrv.D6G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (D6BDrv.D6B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE)))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 7) eqn:Hk7.
  { apply Z.eqb_eq in Hk7. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (D7GDrv.D7G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (D7BDrv.D7B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE)))))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 8) eqn:Hk8.
  { apply Z.eqb_eq in Hk8. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (D8GDrv.D8G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (D8BDrv.D8B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE)))))))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 9) eqn:Hk9.
  { apply Z.eqb_eq in Hk9. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (D9GDrv.D9G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (D9BDrv.D9B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE)))))))))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 10) eqn:Hk10.
  { apply Z.eqb_eq in Hk10. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (D10GDrv.D10G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))))))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (D10BDrv.D10B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))))))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct HCS.
Qed.
