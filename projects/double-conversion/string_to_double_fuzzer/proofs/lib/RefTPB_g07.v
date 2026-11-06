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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RefTargetAssemblyTop RefTPBc_g07.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SP.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma cso_k1_74877_77804 : class_shape_ok true s_k1_74877_77804 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_74877_77804 : TPK 1 74877 77804.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 74877 77804 p_k1_74877_77804 s_k1_74877_77804 chk_k1_74877_77804 cso_k1_74877_77804); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_77805_81900 : class_shape_ok true s_k1_77805_81900 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_77805_81900 : TPK 1 77805 81900.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 77805 81900 p_k1_77805_81900 s_k1_77805_81900 chk_k1_77805_81900 cso_k1_77805_81900); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_81901_85996 : class_shape_ok true s_k1_81901_85996 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_81901_85996 : TPK 1 81901 85996.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 81901 85996 p_k1_81901_85996 s_k1_81901_85996 chk_k1_81901_85996 cso_k1_81901_85996); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_87357_90092 : class_shape_ok true s_k1_87357_90092 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_87357_90092 : TPK 1 87357 90092.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 87357 90092 p_k1_87357_90092 s_k1_87357_90092 chk_k1_87357_90092 cso_k1_87357_90092); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_90093_94188 : class_shape_ok true s_k1_90093_94188 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_90093_94188 : TPK 1 90093 94188.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 90093 94188 p_k1_90093_94188 s_k1_90093_94188 chk_k1_90093_94188 cso_k1_90093_94188); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_94189_98284 : class_shape_ok true s_k1_94189_98284 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_94189_98284 : TPK 1 94189 98284.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 94189 98284 p_k1_94189_98284 s_k1_94189_98284 chk_k1_94189_98284 cso_k1_94189_98284); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_98285_102380 : class_shape_ok true s_k1_98285_102380 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_98285_102380 : TPK 1 98285 102380.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 98285 102380 p_k1_98285_102380 s_k1_98285_102380 chk_k1_98285_102380 cso_k1_98285_102380); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_102381_104828 : class_shape_ok true s_k1_102381_104828 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_102381_104828 : TPK 1 102381 104828.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 102381 104828 p_k1_102381_104828 s_k1_102381_104828 chk_k1_102381_104828 cso_k1_102381_104828); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_106477_110572 : class_shape_ok true s_k1_106477_110572 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_106477_110572 : TPK 1 106477 110572.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 106477 110572 p_k1_106477_110572 s_k1_106477_110572 chk_k1_106477_110572 cso_k1_106477_110572); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_110573_114668 : class_shape_ok true s_k1_110573_114668 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_110573_114668 : TPK 1 110573 114668.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 110573 114668 p_k1_110573_114668 s_k1_110573_114668 chk_k1_110573_114668 cso_k1_110573_114668); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_114669_118764 : class_shape_ok true s_k1_114669_118764 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_114669_118764 : TPK 1 114669 118764.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 114669 118764 p_k1_114669_118764 s_k1_114669_118764 chk_k1_114669_118764 cso_k1_114669_118764); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_118765_122860 : class_shape_ok true s_k1_118765_122860 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_118765_122860 : TPK 1 118765 122860.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 118765 122860 p_k1_118765_122860 s_k1_118765_122860 chk_k1_118765_122860 cso_k1_118765_122860); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_122861_126956 : class_shape_ok true s_k1_122861_126956 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_122861_126956 : TPK 1 122861 126956.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 122861 126956 p_k1_122861_126956 s_k1_122861_126956 chk_k1_122861_126956 cso_k1_122861_126956); try eassumption; unfold capk; cbn; lia.
Qed.

