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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefTPBc_g08.
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
Lemma cso_k1_118765_122860 : class_shape_ok true s_k1_118765_122860 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_118765_122860 : TPK 1 118765 122860.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 118765 122860 p_k1_118765_122860 s_k1_118765_122860 chk_k1_118765_122860 cso_k1_118765_122860); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_122861_126956 : class_shape_ok true s_k1_122861_126956 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_122861_126956 : TPK 1 122861 126956.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 122861 126956 p_k1_122861_126956 s_k1_122861_126956 chk_k1_122861_126956 cso_k1_122861_126956); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_126957_131051 : class_shape_ok true s_k1_126957_131051 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_126957_131051 : TPK 1 126957 131051.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 126957 131051 p_k1_126957_131051 s_k1_126957_131051 chk_k1_126957_131051 cso_k1_126957_131051); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_131052_131065 : class_shape_ok true s_k1_131052_131065 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_131052_131065 : TPK 1 131052 131065.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 131052 131065 p_k1_131052_131065 s_k1_131052_131065 chk_k1_131052_131065 cso_k1_131052_131065); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_98299_102380 : class_shape_ok1 true s_k2_98299_102380 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_98299_102380 : TPK 2 98299 102380.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 2 20000 400 98299 102380 p_k2_98299_102380 s_k2_98299_102380 chk_k2_98299_102380 cso_k2_98299_102380); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_102381_104828 : class_shape_ok1 true s_k2_102381_104828 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_102381_104828 : TPK 2 102381 104828.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 2 20000 400 102381 104828 p_k2_102381_104828 s_k2_102381_104828 chk_k2_102381_104828 cso_k2_102381_104828); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_104829_106476 : class_shape_ok1 true s_k2_104829_106476 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_104829_106476 : TPK 2 104829 106476.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 2 20000 400 104829 106476 p_k2_104829_106476 s_k2_104829_106476 chk_k2_104829_106476 cso_k2_104829_106476); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_106477_110572 : class_shape_ok1 true s_k2_106477_110572 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_106477_110572 : TPK 2 106477 110572.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 2 20000 400 106477 110572 p_k2_106477_110572 s_k2_106477_110572 chk_k2_106477_110572 cso_k2_106477_110572); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_110573_114668 : class_shape_ok1 true s_k2_110573_114668 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_110573_114668 : TPK 2 110573 114668.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 2 20000 400 110573 114668 p_k2_110573_114668 s_k2_110573_114668 chk_k2_110573_114668 cso_k2_110573_114668); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_114669_118764 : class_shape_ok1 true s_k2_114669_118764 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_114669_118764 : TPK 2 114669 118764.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 2 20000 400 114669 118764 p_k2_114669_118764 s_k2_114669_118764 chk_k2_114669_118764 cso_k2_114669_118764); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_118765_122860 : class_shape_ok1 true s_k2_118765_122860 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_118765_122860 : TPK 2 118765 122860.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 2 20000 400 118765 122860 p_k2_118765_122860 s_k2_118765_122860 chk_k2_118765_122860 cso_k2_118765_122860); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_122861_126956 : class_shape_ok1 true s_k2_122861_126956 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_122861_126956 : TPK 2 122861 126956.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 2 20000 400 122861 126956 p_k2_122861_126956 s_k2_122861_126956 chk_k2_122861_126956 cso_k2_122861_126956); try eassumption; unfold capk; cbn; lia.
Qed.

