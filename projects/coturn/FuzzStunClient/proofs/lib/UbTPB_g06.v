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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbTPBc_g06.
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
Lemma cso_k1_40941_43676 : class_shape_ok1 true s_k1_40941_43676 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_40941_43676 : TPK 1 40941 43676.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 1 20000 400 40941 43676 p_k1_40941_43676 s_k1_40941_43676 chk_k1_40941_43676 cso_k1_40941_43676); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_43677_45036 : class_shape_ok1 true s_k1_43677_45036 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_43677_45036 : TPK 1 43677 45036.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 1 20000 400 43677 45036 p_k1_43677_45036 s_k1_43677_45036 chk_k1_43677_45036 cso_k1_43677_45036); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_45037_49132 : class_shape_ok1 true s_k1_45037_49132 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_45037_49132 : TPK 1 45037 49132.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 1 20000 400 45037 49132 p_k1_45037_49132 s_k1_45037_49132 chk_k1_45037_49132 cso_k1_45037_49132); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_49133_52412 : class_shape_ok1 true s_k1_49133_52412 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_49133_52412 : TPK 1 49133 52412.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 1 20000 400 49133 52412 p_k1_49133_52412 s_k1_49133_52412 chk_k1_49133_52412 cso_k1_49133_52412); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_52413_53228 : class_shape_ok1 true s_k1_52413_53228 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_52413_53228 : TPK 1 52413 53228.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 1 20000 400 52413 53228 p_k1_52413_53228 s_k1_52413_53228 chk_k1_52413_53228 cso_k1_52413_53228); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_53229_57324 : class_shape_ok1 true s_k1_53229_57324 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_53229_57324 : TPK 1 53229 57324.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 1 20000 400 53229 57324 p_k1_53229_57324 s_k1_53229_57324 chk_k1_53229_57324 cso_k1_53229_57324); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_57325_61420 : class_shape_ok1 true s_k1_57325_61420 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_57325_61420 : TPK 1 57325 61420.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 1 20000 400 57325 61420 p_k1_57325_61420 s_k1_57325_61420 chk_k1_57325_61420 cso_k1_57325_61420); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_61421_65516 : class_shape_ok1 true s_k1_61421_65516 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_61421_65516 : TPK 1 61421 65516.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 1 20000 400 61421 65516 p_k1_61421_65516 s_k1_61421_65516 chk_k1_61421_65516 cso_k1_61421_65516); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_65517_69612 : class_shape_ok true s_k1_65517_69612 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_65517_69612 : TPK 1 65517 69612.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 65517 69612 p_k1_65517_69612 s_k1_65517_69612 chk_k1_65517_69612 cso_k1_65517_69612); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_69613_73708 : class_shape_ok true s_k1_69613_73708 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_69613_73708 : TPK 1 69613 73708.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 69613 73708 p_k1_69613_73708 s_k1_69613_73708 chk_k1_69613_73708 cso_k1_69613_73708); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_73709_74876 : class_shape_ok true s_k1_73709_74876 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_73709_74876 : TPK 1 73709 74876.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 73709 74876 p_k1_73709_74876 s_k1_73709_74876 chk_k1_73709_74876 cso_k1_73709_74876); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_74877_77804 : class_shape_ok true s_k1_74877_77804 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_74877_77804 : TPK 1 74877 77804.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 1 20000 400 74877 77804 p_k1_74877_77804 s_k1_74877_77804 chk_k1_74877_77804 cso_k1_74877_77804); try eassumption; unfold capk; cbn; lia.
Qed.

