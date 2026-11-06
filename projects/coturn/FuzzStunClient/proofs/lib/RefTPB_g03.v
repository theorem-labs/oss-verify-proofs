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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefTPBc_g03.
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
Lemma cso_k0_1629_2028 : class_shape_ok true s_k0_1629_2028 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1629_2028 : TP0 1629 2028.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 1629 2028 p_k0_1629_2028 s_k0_1629_2028 chk_k0_1629_2028 cso_k0_1629_2028); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_2029_2332 : class_shape_ok true s_k0_2029_2332 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_2029_2332 : TP0 2029 2332.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 2029 2332 p_k0_2029_2332 s_k0_2029_2332 chk_k0_2029_2332 cso_k0_2029_2332); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_2333_2716 : class_shape_ok true s_k0_2333_2716 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_2333_2716 : TP0 2333 2716.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 2333 2716 p_k0_2333_2716 s_k0_2333_2716 chk_k0_2333_2716 cso_k0_2333_2716); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_2717_3260 : class_shape_ok true s_k0_2717_3260 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_2717_3260 : TP0 2717 3260.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 2717 3260 p_k0_2717_3260 s_k0_2717_3260 chk_k0_2717_3260 cso_k0_2717_3260); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_3261_4076 : class_shape_ok true s_k0_3261_4076 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_3261_4076 : TP0 3261 4076.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 3261 4076 p_k0_3261_4076 s_k0_3261_4076 chk_k0_3261_4076 cso_k0_3261_4076); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_4077_4668 : class_shape_ok true s_k0_4077_4668 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_4077_4668 : TP0 4077 4668.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 4077 4668 p_k0_4077_4668 s_k0_4077_4668 chk_k0_4077_4668 cso_k0_4077_4668); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_4669_5436 : class_shape_ok true s_k0_4669_5436 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_4669_5436 : TP0 4669 5436.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 4669 5436 p_k0_4669_5436 s_k0_4669_5436 chk_k0_4669_5436 cso_k0_4669_5436); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_5437_6540 : class_shape_ok true s_k0_5437_6540 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_5437_6540 : TP0 5437 6540.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 5437 6540 p_k0_5437_6540 s_k0_5437_6540 chk_k0_5437_6540 cso_k0_5437_6540); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_6541_8172 : class_shape_ok true s_k0_6541_8172 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_6541_8172 : TP0 6541 8172.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 6541 8172 p_k0_6541_8172 s_k0_6541_8172 chk_k0_6541_8172 cso_k0_6541_8172); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_8173_9340 : class_shape_ok true s_k0_8173_9340 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_8173_9340 : TP0 8173 9340.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 8173 9340 p_k0_8173_9340 s_k0_8173_9340 chk_k0_8173_9340 cso_k0_8173_9340); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_9341_10908 : class_shape_ok true s_k0_9341_10908 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_9341_10908 : TP0 9341 10908.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 9341 10908 p_k0_9341_10908 s_k0_9341_10908 chk_k0_9341_10908 cso_k0_9341_10908); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_10909_12268 : class_shape_ok true s_k0_10909_12268 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_10909_12268 : TP0 10909 12268.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 10909 12268 p_k0_10909_12268 s_k0_10909_12268 chk_k0_10909_12268 cso_k0_10909_12268); try eassumption; lia.
Qed.

