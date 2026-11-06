(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import
  Spec TargetSpec TargetKDefs UbWorld UbTargetPre UbWorldK UbTargetPreK
  SymExec3 SymPlan SymPlanSoundA UbATB UbTargetEntry_defs UbTargetEntryK_defs
  TargetShape TargetShapeTop UbTargetAssembly UbTargetCover.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbTPBc_g09.
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
Lemma cso_k2_126957_131051 : class_shape_ok1 true s_k2_126957_131051 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_126957_131051 : TPK 2 126957 131051.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 2 20000 400 126957 131051 p_k2_126957_131051 s_k2_126957_131051 chk_k2_126957_131051 cso_k2_126957_131051); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_131052_262137 : class_shape_ok true s_k2_131052_262137 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_131052_262137 : TPK 2 131052 262137.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 2 20000 400 131052 262137 p_k2_131052_262137 s_k2_131052_262137 chk_k2_131052_262137 cso_k2_131052_262137); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k3_229371_524281 : class_shape_ok true s_k3_229371_524281 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k3_229371_524281 : TPK 3 229371 524281.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 3 20000 400 229371 524281 p_k3_229371_524281 s_k3_229371_524281 chk_k3_229371_524281 cso_k3_229371_524281); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k4_491515_1048569 : class_shape_ok true s_k4_491515_1048569 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k4_491515_1048569 : TPK 4 491515 1048569.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 4 20000 400 491515 1048569 p_k4_491515_1048569 s_k4_491515_1048569 chk_k4_491515_1048569 cso_k4_491515_1048569); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k5_1015803_2097145 : class_shape_ok true s_k5_1015803_2097145 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k5_1015803_2097145 : TPK 5 1015803 2097145.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 5 20000 400 1015803 2097145 p_k5_1015803_2097145 s_k5_1015803_2097145 chk_k5_1015803_2097145 cso_k5_1015803_2097145); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k6_2064379_4194297 : class_shape_ok true s_k6_2064379_4194297 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k6_2064379_4194297 : TPK 6 2064379 4194297.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 6 20000 400 2064379 4194297 p_k6_2064379_4194297 s_k6_2064379_4194297 chk_k6_2064379_4194297 cso_k6_2064379_4194297); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k7_4161531_8388601 : class_shape_ok true s_k7_4161531_8388601 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k7_4161531_8388601 : TPK 7 4161531 8388601.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 7 20000 400 4161531 8388601 p_k7_4161531_8388601 s_k7_4161531_8388601 chk_k7_4161531_8388601 cso_k7_4161531_8388601); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k8_8355835_12566521 : class_shape_ok true s_k8_8355835_12566521 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k8_8355835_12566521 : TPK 8 8355835 12566521.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 8 20000 400 8355835 12566521 p_k8_8355835_12566521 s_k8_8355835_12566521 chk_k8_8355835_12566521 cso_k8_8355835_12566521); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k8_12566522_16777209 : class_shape_ok true s_k8_12566522_16777209 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k8_12566522_16777209 : TPK 8 12566522 16777209.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 8 20000 400 12566522 16777209 p_k8_12566522_16777209 s_k8_12566522_16777209 chk_k8_12566522_16777209 cso_k8_12566522_16777209); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k9_16744443_22347769 : class_shape_ok true s_k9_16744443_22347769 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k9_16744443_22347769 : TPK 9 16744443 22347769.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 9 20000 400 16744443 22347769 p_k9_16744443_22347769 s_k9_16744443_22347769 chk_k9_16744443_22347769 cso_k9_16744443_22347769); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k9_22347770_27951096 : class_shape_ok true s_k9_22347770_27951096 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k9_22347770_27951096 : TPK 9 22347770 27951096.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 9 20000 400 22347770 27951096 p_k9_22347770_27951096 s_k9_22347770_27951096 chk_k9_22347770_27951096 cso_k9_22347770_27951096); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k9_27951097_33554425 : class_shape_ok true s_k9_27951097_33554425 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k9_27951097_33554425 : TPK 9 27951097 33554425.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 9 20000 400 27951097 33554425 p_k9_27951097_33554425 s_k9_27951097_33554425 chk_k9_27951097_33554425 cso_k9_27951097_33554425); try eassumption; unfold capk; cbn; lia.
Qed.

