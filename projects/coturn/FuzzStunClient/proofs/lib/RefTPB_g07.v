(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import
  Spec TargetSpec TargetKDefs RefWorld RefTargetPre RefWorldK RefTargetPreK
  SymExec3 SymPlan SymPlanSoundA RefATB RefTargetEntry_defs RefTargetEntryK_defs
  TargetShape TargetShapeTop RefTargetAssembly RefTargetCover.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefTPBc_g07.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
Import ListNotations.
Import SX2. Import SP.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma cso_k1_77805_81900 : class_shape_ok true s_k1_77805_81900 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_77805_81900 : TPK 1 77805 81900.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 77805 81900 p_k1_77805_81900 s_k1_77805_81900 chk_k1_77805_81900 cso_k1_77805_81900); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_81901_85996 : class_shape_ok true s_k1_81901_85996 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_81901_85996 : TPK 1 81901 85996.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 81901 85996 p_k1_81901_85996 s_k1_81901_85996 chk_k1_81901_85996 cso_k1_81901_85996); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_85997_87356 : class_shape_ok true s_k1_85997_87356 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_85997_87356 : TPK 1 85997 87356.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 85997 87356 p_k1_85997_87356 s_k1_85997_87356 chk_k1_85997_87356 cso_k1_85997_87356); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_87357_90092 : class_shape_ok true s_k1_87357_90092 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_87357_90092 : TPK 1 87357 90092.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 87357 90092 p_k1_87357_90092 s_k1_87357_90092 chk_k1_87357_90092 cso_k1_87357_90092); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_90093_94188 : class_shape_ok true s_k1_90093_94188 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_90093_94188 : TPK 1 90093 94188.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 90093 94188 p_k1_90093_94188 s_k1_90093_94188 chk_k1_90093_94188 cso_k1_90093_94188); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_94189_98284 : class_shape_ok true s_k1_94189_98284 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_94189_98284 : TPK 1 94189 98284.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 94189 98284 p_k1_94189_98284 s_k1_94189_98284 chk_k1_94189_98284 cso_k1_94189_98284); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_98285_102380 : class_shape_ok true s_k1_98285_102380 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_98285_102380 : TPK 1 98285 102380.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 98285 102380 p_k1_98285_102380 s_k1_98285_102380 chk_k1_98285_102380 cso_k1_98285_102380); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_102381_104828 : class_shape_ok true s_k1_102381_104828 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_102381_104828 : TPK 1 102381 104828.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 102381 104828 p_k1_102381_104828 s_k1_102381_104828 chk_k1_102381_104828 cso_k1_102381_104828); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_104829_106476 : class_shape_ok true s_k1_104829_106476 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_104829_106476 : TPK 1 104829 106476.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 104829 106476 p_k1_104829_106476 s_k1_104829_106476 chk_k1_104829_106476 cso_k1_104829_106476); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_106477_110572 : class_shape_ok true s_k1_106477_110572 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_106477_110572 : TPK 1 106477 110572.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 106477 110572 p_k1_106477_110572 s_k1_106477_110572 chk_k1_106477_110572 cso_k1_106477_110572); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_110573_114668 : class_shape_ok true s_k1_110573_114668 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_110573_114668 : TPK 1 110573 114668.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 110573 114668 p_k1_110573_114668 s_k1_110573_114668 chk_k1_110573_114668 cso_k1_110573_114668); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_114669_118764 : class_shape_ok true s_k1_114669_118764 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_114669_118764 : TPK 1 114669 118764.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 114669 118764 p_k1_114669_118764 s_k1_114669_118764 chk_k1_114669_118764 cso_k1_114669_118764); try eassumption; unfold capk; cbn; lia.
Qed.

