(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeCfg.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue HUPlanImage HUAtable H0Sinv HUCheckG HUSel HUTgtGlue ConeCfg HTSpec.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require UK0GDrv UK0BDrv UK1GDrv UK1BDrv UK2GDrv UK2BDrv UD3GDrv UD3BDrv UD4GDrv UD4BDrv UD5GDrv UD5BDrv UD6GDrv UD6BDrv UD7GDrv UD7BDrv UD8GDrv UD8BDrv UD9GDrv UD9BDrv UD10GDrv UD10BDrv.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import UD10BS0 UD10GS0 UD3BS0 UD3GS0 UD4BS0 UD4GS0 UD5BS0 UD5GS0 UD6BS0 UD6GS0 UD7BS0 UD7GS0 UD8BS0 UD8GS0 UD9BS0 UD9GS0 UK0AS0 UK0BS0 UR1BS0 UR1GS0 UR2BS0 UR2GS0.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUFamilyAllDefs.
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
    { apply (FIN _ _ _ (UK0GDrv.K0G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 HE) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UK0BDrv.K0B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 HE)) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 1) eqn:Hk1.
  { apply Z.eqb_eq in Hk1. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UK1GDrv.K1G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 HE))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UK1BDrv.K1B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 HE)))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 2) eqn:Hk2.
  { apply Z.eqb_eq in Hk2. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UK2GDrv.K2G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 HE))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UK2BDrv.K2B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HE)))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 3) eqn:Hk3.
  { apply Z.eqb_eq in Hk3. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UD3GDrv.D3G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UD3BDrv.D3B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE)))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 4) eqn:Hk4.
  { apply Z.eqb_eq in Hk4. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UD4GDrv.D4G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UD4BDrv.D4B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE)))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 5) eqn:Hk5.
  { apply Z.eqb_eq in Hk5. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UD5GDrv.D5G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UD5BDrv.D5B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE)))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 6) eqn:Hk6.
  { apply Z.eqb_eq in Hk6. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UD6GDrv.D6G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UD6BDrv.D6B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE)))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 7) eqn:Hk7.
  { apply Z.eqb_eq in Hk7. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UD7GDrv.D7G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UD7BDrv.D7B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE)))))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 8) eqn:Hk8.
  { apply Z.eqb_eq in Hk8. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UD8GDrv.D8G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UD8BDrv.D8B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE)))))))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 9) eqn:Hk9.
  { apply Z.eqb_eq in Hk9. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UD9GDrv.D9G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UD9BDrv.D9B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE)))))))))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct (k =? 10) eqn:Hk10.
  { apply Z.eqb_eq in Hk10. subst k.
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UD10GDrv.D10G_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))))))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS as [<-|HCS].
    { apply (FIN _ _ _ (UD10BDrv.D10B_family sp0 _ fs0 Hsp Hstr Hstr8 PHIb (tin_of content) E R' FULL model Htin ((proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HE))))))))))))))))))))) eq_refl eq_refl) HC)). apply tgt_of_content. }
    destruct HCS. }
  destruct HCS.
Qed.
