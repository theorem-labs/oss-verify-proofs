(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec ShapeAlg Spec RefWorld RefTargetPre RefWorldK RefTargetPreK
  SymExec3 SymPlan SymPlanSoundA RefTargetEntry_defs RefTargetEntryK_defs
  RefTargetShape RefTargetShapeTop RefTargetAssembly RefTargetCover.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RefTargetAssemblyTop RefTPBc_g04.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SP.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma cso_k0_669_796 : class_shape_ok true s_k0_669_796 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_669_796 : TP0 669 796.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 669 796 p_k0_669_796 s_k0_669_796 chk_k0_669_796 cso_k0_669_796); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_797_1004 : class_shape_ok true s_k0_797_1004 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_797_1004 : TP0 797 1004.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 797 1004 p_k0_797_1004 s_k0_797_1004 chk_k0_797_1004 cso_k0_797_1004); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_1005_1148 : class_shape_ok true s_k0_1005_1148 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1005_1148 : TP0 1005 1148.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 1005 1148 p_k0_1005_1148 s_k0_1005_1148 chk_k0_1005_1148 cso_k0_1005_1148); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_1149_1340 : class_shape_ok true s_k0_1149_1340 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1149_1340 : TP0 1149 1340.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 1149 1340 p_k0_1149_1340 s_k0_1149_1340 chk_k0_1149_1340 cso_k0_1149_1340); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_1341_1628 : class_shape_ok true s_k0_1341_1628 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1341_1628 : TP0 1341 1628.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 1341 1628 p_k0_1341_1628 s_k0_1341_1628 chk_k0_1341_1628 cso_k0_1341_1628); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_1629_2028 : class_shape_ok true s_k0_1629_2028 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1629_2028 : TP0 1629 2028.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 1629 2028 p_k0_1629_2028 s_k0_1629_2028 chk_k0_1629_2028 cso_k0_1629_2028); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_2029_2332 : class_shape_ok true s_k0_2029_2332 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_2029_2332 : TP0 2029 2332.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 2029 2332 p_k0_2029_2332 s_k0_2029_2332 chk_k0_2029_2332 cso_k0_2029_2332); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_2333_2716 : class_shape_ok true s_k0_2333_2716 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_2333_2716 : TP0 2333 2716.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 2333 2716 p_k0_2333_2716 s_k0_2333_2716 chk_k0_2333_2716 cso_k0_2333_2716); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_2717_3260 : class_shape_ok true s_k0_2717_3260 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_2717_3260 : TP0 2717 3260.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 2717 3260 p_k0_2717_3260 s_k0_2717_3260 chk_k0_2717_3260 cso_k0_2717_3260); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_3261_4076 : class_shape_ok true s_k0_3261_4076 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_3261_4076 : TP0 3261 4076.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 3261 4076 p_k0_3261_4076 s_k0_3261_4076 chk_k0_3261_4076 cso_k0_3261_4076); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_4077_4668 : class_shape_ok true s_k0_4077_4668 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_4077_4668 : TP0 4077 4668.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 4077 4668 p_k0_4077_4668 s_k0_4077_4668 chk_k0_4077_4668 cso_k0_4077_4668); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_4669_5436 : class_shape_ok true s_k0_4669_5436 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_4669_5436 : TP0 4669 5436.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 4669 5436 p_k0_4669_5436 s_k0_4669_5436 chk_k0_4669_5436 cso_k0_4669_5436); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_12269_13084 : class_shape_ok true s_k0_12269_13084 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_12269_13084 : TP0 12269 13084.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 12269 13084 p_k0_12269_13084 s_k0_12269_13084 chk_k0_12269_13084 cso_k0_12269_13084); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_65517_65529 : class_shape_ok true s_k0_65517_65529 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_65517_65529 : TP0 65517 65529.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 65517 65529 p_k0_65517_65529 s_k0_65517_65529 chk_k0_65517_65529 cso_k0_65517_65529); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_104829_106476 : class_shape_ok true s_k1_104829_106476 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_104829_106476 : TPK 1 104829 106476.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 104829 106476 p_k1_104829_106476 s_k1_104829_106476 chk_k1_104829_106476 cso_k1_104829_106476); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_131052_131065 : class_shape_ok true s_k1_131052_131065 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_131052_131065 : TPK 1 131052 131065.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 131052 131065 p_k1_131052_131065 s_k1_131052_131065 chk_k1_131052_131065 cso_k1_131052_131065); try eassumption; unfold capk; cbn; lia.
Qed.

