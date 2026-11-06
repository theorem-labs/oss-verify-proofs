(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec ShapeAlg Spec UbWorld UbTargetPre UbWorldK UbTargetPreK
  SymExec3 SymPlan UbSymPlanSoundA UbTargetEntry_defs UbTargetEntryK_defs
  UbTargetShape UbTargetShapeTop UbTargetAssembly UbTargetCover.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import UbTargetAssemblyTop UbTPBc_g05.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SP.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma cso_k0_13085_16364 : class_shape_ok true s_k0_13085_16364 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_13085_16364 : TP0 13085 16364.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 13085 16364 p_k0_13085_16364 s_k0_13085_16364 chk_k0_13085_16364 cso_k0_13085_16364); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_16365_18700 : class_shape_ok true s_k0_16365_18700 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_16365_18700 : TP0 16365 18700.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 16365 18700 p_k0_16365_18700 s_k0_16365_18700 chk_k0_16365_18700 cso_k0_16365_18700); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_131052_262137 : class_shape_ok true s_k2_131052_262137 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_131052_262137 : TPK 2 131052 262137.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 2 20000 400 131052 262137 p_k2_131052_262137 s_k2_131052_262137 chk_k2_131052_262137 cso_k2_131052_262137); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k3_229371_524281 : class_shape_ok true s_k3_229371_524281 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k3_229371_524281 : TPK 3 229371 524281.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 3 20000 400 229371 524281 p_k3_229371_524281 s_k3_229371_524281 chk_k3_229371_524281 cso_k3_229371_524281); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k4_491515_1048569 : class_shape_ok true s_k4_491515_1048569 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k4_491515_1048569 : TPK 4 491515 1048569.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 4 20000 400 491515 1048569 p_k4_491515_1048569 s_k4_491515_1048569 chk_k4_491515_1048569 cso_k4_491515_1048569); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k5_1015803_2097145 : class_shape_ok true s_k5_1015803_2097145 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k5_1015803_2097145 : TPK 5 1015803 2097145.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 5 20000 400 1015803 2097145 p_k5_1015803_2097145 s_k5_1015803_2097145 chk_k5_1015803_2097145 cso_k5_1015803_2097145); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k6_2064379_4194297 : class_shape_ok true s_k6_2064379_4194297 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k6_2064379_4194297 : TPK 6 2064379 4194297.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 6 20000 400 2064379 4194297 p_k6_2064379_4194297 s_k6_2064379_4194297 chk_k6_2064379_4194297 cso_k6_2064379_4194297); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k7_4161531_8388601 : class_shape_ok true s_k7_4161531_8388601 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k7_4161531_8388601 : TPK 7 4161531 8388601.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 7 20000 400 4161531 8388601 p_k7_4161531_8388601 s_k7_4161531_8388601 chk_k7_4161531_8388601 cso_k7_4161531_8388601); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k8_8355835_16777209 : class_shape_ok true s_k8_8355835_16777209 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k8_8355835_16777209 : TPK 8 8355835 16777209.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 8 20000 400 8355835 16777209 p_k8_8355835_16777209 s_k8_8355835_16777209 chk_k8_8355835_16777209 cso_k8_8355835_16777209); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k9_16744443_33554425 : class_shape_ok true s_k9_16744443_33554425 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k9_16744443_33554425 : TPK 9 16744443 33554425.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 9 20000 400 16744443 33554425 p_k9_16744443_33554425 s_k9_16744443_33554425 chk_k9_16744443_33554425 cso_k9_16744443_33554425); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k10_33521659_67108857 : class_shape_ok true s_k10_33521659_67108857 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k10_33521659_67108857 : TPK 10 33521659 67108857.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 10 20000 400 33521659 67108857 p_k10_33521659_67108857 s_k10_33521659_67108857 chk_k10_33521659_67108857 cso_k10_33521659_67108857); try eassumption; unfold capk; cbn; lia.
Qed.

