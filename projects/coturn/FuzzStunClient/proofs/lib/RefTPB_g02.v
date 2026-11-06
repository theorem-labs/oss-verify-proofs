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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefTPBc_g02.
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
Lemma cso_k0_189_236 : class_shape_ok true s_k0_189_236 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_189_236 : TP0 189 236.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 189 236 p_k0_189_236 s_k0_189_236 chk_k0_189_236 cso_k0_189_236); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_237_284 : class_shape_ok true s_k0_237_284 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_237_284 : TP0 237 284.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 237 284 p_k0_237_284 s_k0_237_284 chk_k0_237_284 cso_k0_237_284); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_285_316 : class_shape_ok true s_k0_285_316 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_285_316 : TP0 285 316.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 285 316 p_k0_285_316 s_k0_285_316 chk_k0_285_316 cso_k0_285_316); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_317_396 : class_shape_ok true s_k0_317_396 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_317_396 : TP0 317 396.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 317 396 p_k0_317_396 s_k0_317_396 chk_k0_317_396 cso_k0_317_396); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_397_492 : class_shape_ok true s_k0_397_492 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_397_492 : TP0 397 492.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 397 492 p_k0_397_492 s_k0_397_492 chk_k0_397_492 cso_k0_397_492); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_493_572 : class_shape_ok true s_k0_493_572 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_493_572 : TP0 493 572.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 493 572 p_k0_493_572 s_k0_493_572 chk_k0_493_572 cso_k0_493_572); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_573_668 : class_shape_ok true s_k0_573_668 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_573_668 : TP0 573 668.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 573 668 p_k0_573_668 s_k0_573_668 chk_k0_573_668 cso_k0_573_668); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_669_796 : class_shape_ok true s_k0_669_796 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_669_796 : TP0 669 796.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 669 796 p_k0_669_796 s_k0_669_796 chk_k0_669_796 cso_k0_669_796); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_797_1004 : class_shape_ok true s_k0_797_1004 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_797_1004 : TP0 797 1004.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 797 1004 p_k0_797_1004 s_k0_797_1004 chk_k0_797_1004 cso_k0_797_1004); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_1005_1148 : class_shape_ok true s_k0_1005_1148 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1005_1148 : TP0 1005 1148.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 1005 1148 p_k0_1005_1148 s_k0_1005_1148 chk_k0_1005_1148 cso_k0_1005_1148); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_1149_1340 : class_shape_ok true s_k0_1149_1340 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1149_1340 : TP0 1149 1340.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 1149 1340 p_k0_1149_1340 s_k0_1149_1340 chk_k0_1149_1340 cso_k0_1149_1340); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_1341_1628 : class_shape_ok true s_k0_1341_1628 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1341_1628 : TP0 1341 1628.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 1341 1628 p_k0_1341_1628 s_k0_1341_1628 chk_k0_1341_1628 cso_k0_1341_1628); try eassumption; lia.
Qed.

