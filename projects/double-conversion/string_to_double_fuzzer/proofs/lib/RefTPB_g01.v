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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RefTargetAssemblyTop RefTPBc_g01.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SP.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma cso_k0_317_396 : class_shape_ok true s_k0_317_396 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_317_396 : TP0 317 396.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 317 396 p_k0_317_396 s_k0_317_396 chk_k0_317_396 cso_k0_317_396); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_397_492 : class_shape_ok true s_k0_397_492 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_397_492 : TP0 397 492.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 397 492 p_k0_397_492 s_k0_397_492 chk_k0_397_492 cso_k0_397_492); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_493_572 : class_shape_ok true s_k0_493_572 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_493_572 : TP0 493 572.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 493 572 p_k0_493_572 s_k0_493_572 chk_k0_493_572 cso_k0_493_572); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_573_668 : class_shape_ok true s_k0_573_668 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_573_668 : TP0 573 668.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 573 668 p_k0_573_668 s_k0_573_668 chk_k0_573_668 cso_k0_573_668); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_5437_6540 : class_shape_ok true s_k0_5437_6540 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_5437_6540 : TP0 5437 6540.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 5437 6540 p_k0_5437_6540 s_k0_5437_6540 chk_k0_5437_6540 cso_k0_5437_6540); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_6541_8172 : class_shape_ok true s_k0_6541_8172 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_6541_8172 : TP0 6541 8172.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 6541 8172 p_k0_6541_8172 s_k0_6541_8172 chk_k0_6541_8172 cso_k0_6541_8172); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_8173_9340 : class_shape_ok true s_k0_8173_9340 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_8173_9340 : TP0 8173 9340.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 8173 9340 p_k0_8173_9340 s_k0_8173_9340 chk_k0_8173_9340 cso_k0_8173_9340); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_9341_10908 : class_shape_ok true s_k0_9341_10908 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_9341_10908 : TP0 9341 10908.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 9341 10908 p_k0_9341_10908 s_k0_9341_10908 chk_k0_9341_10908 cso_k0_9341_10908); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_10909_12268 : class_shape_ok true s_k0_10909_12268 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_10909_12268 : TP0 10909 12268.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 10909 12268 p_k0_10909_12268 s_k0_10909_12268 chk_k0_10909_12268 cso_k0_10909_12268); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_18701_20460 : class_shape_ok true s_k0_18701_20460 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_18701_20460 : TP0 18701 20460.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 18701 20460 p_k0_18701_20460 s_k0_18701_20460 chk_k0_18701_20460 cso_k0_18701_20460); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_20461_21820 : class_shape_ok true s_k0_20461_21820 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_20461_21820 : TP0 20461 21820.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 20461 21820 p_k0_20461_21820 s_k0_20461_21820 chk_k0_20461_21820 cso_k0_20461_21820); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_24557_26188 : class_shape_ok true s_k0_24557_26188 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_24557_26188 : TP0 24557 26188.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 24557 26188 p_k0_24557_26188 s_k0_24557_26188 chk_k0_24557_26188 cso_k0_24557_26188); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_43677_45036 : class_shape_ok true s_k0_43677_45036 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_43677_45036 : TP0 43677 45036.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 43677 45036 p_k0_43677_45036 s_k0_43677_45036 chk_k0_43677_45036 cso_k0_43677_45036); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_32763_36844 : class_shape_ok1 true s_k1_32763_36844 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_32763_36844 : TPK 1 32763 36844.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 1 20000 400 32763 36844 p_k1_32763_36844 s_k1_32763_36844 chk_k1_32763_36844 cso_k1_32763_36844); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_73709_74876 : class_shape_ok true s_k1_73709_74876 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_73709_74876 : TPK 1 73709 74876.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 73709 74876 p_k1_73709_74876 s_k1_73709_74876 chk_k1_73709_74876 cso_k1_73709_74876); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_85997_87356 : class_shape_ok true s_k1_85997_87356 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_85997_87356 : TPK 1 85997 87356.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 85997 87356 p_k1_85997_87356 s_k1_85997_87356 chk_k1_85997_87356 cso_k1_85997_87356); try eassumption; unfold capk; cbn; lia.
Qed.

