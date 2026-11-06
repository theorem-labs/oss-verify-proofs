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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RefTargetAssemblyTop RefTPBc_g02.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SP.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma cso_k0_36845_37436 : class_shape_ok true s_k0_36845_37436 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_36845_37436 : TP0 36845 37436.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 36845 37436 p_k0_36845_37436 s_k0_36845_37436 chk_k0_36845_37436 cso_k0_36845_37436); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_52413_53228 : class_shape_ok true s_k0_52413_53228 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_52413_53228 : TP0 52413 53228.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 52413 53228 p_k0_52413_53228 s_k0_52413_53228 chk_k0_52413_53228 cso_k0_52413_53228); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_37437_40940 : class_shape_ok1 true s_k1_37437_40940 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_37437_40940 : TPK 1 37437 40940.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 1 20000 400 37437 40940 p_k1_37437_40940 s_k1_37437_40940 chk_k1_37437_40940 cso_k1_37437_40940); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_40941_43676 : class_shape_ok1 true s_k1_40941_43676 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_40941_43676 : TPK 1 40941 43676.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 1 20000 400 40941 43676 p_k1_40941_43676 s_k1_40941_43676 chk_k1_40941_43676 cso_k1_40941_43676); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_43677_45036 : class_shape_ok1 true s_k1_43677_45036 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_43677_45036 : TPK 1 43677 45036.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 1 20000 400 43677 45036 p_k1_43677_45036 s_k1_43677_45036 chk_k1_43677_45036 cso_k1_43677_45036); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_45037_49132 : class_shape_ok1 true s_k1_45037_49132 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_45037_49132 : TPK 1 45037 49132.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 1 20000 400 45037 49132 p_k1_45037_49132 s_k1_45037_49132 chk_k1_45037_49132 cso_k1_45037_49132); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_49133_52412 : class_shape_ok1 true s_k1_49133_52412 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_49133_52412 : TPK 1 49133 52412.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 1 20000 400 49133 52412 p_k1_49133_52412 s_k1_49133_52412 chk_k1_49133_52412 cso_k1_49133_52412); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_53229_57324 : class_shape_ok1 true s_k1_53229_57324 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_53229_57324 : TPK 1 53229 57324.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 1 20000 400 53229 57324 p_k1_53229_57324 s_k1_53229_57324 chk_k1_53229_57324 cso_k1_53229_57324); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_57325_61420 : class_shape_ok1 true s_k1_57325_61420 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_57325_61420 : TPK 1 57325 61420.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 1 20000 400 57325 61420 p_k1_57325_61420 s_k1_57325_61420 chk_k1_57325_61420 cso_k1_57325_61420); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_61421_65516 : class_shape_ok1 true s_k1_61421_65516 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_61421_65516 : TPK 1 61421 65516.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 1 20000 400 61421 65516 p_k1_61421_65516 s_k1_61421_65516 chk_k1_61421_65516 cso_k1_61421_65516); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_98299_102380 : class_shape_ok1 true s_k2_98299_102380 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_98299_102380 : TPK 2 98299 102380.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 2 20000 400 98299 102380 p_k2_98299_102380 s_k2_98299_102380 chk_k2_98299_102380 cso_k2_98299_102380); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_102381_104828 : class_shape_ok1 true s_k2_102381_104828 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_102381_104828 : TPK 2 102381 104828.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 2 20000 400 102381 104828 p_k2_102381_104828 s_k2_102381_104828 chk_k2_102381_104828 cso_k2_102381_104828); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_106477_110572 : class_shape_ok1 true s_k2_106477_110572 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_106477_110572 : TPK 2 106477 110572.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 2 20000 400 106477 110572 p_k2_106477_110572 s_k2_106477_110572 chk_k2_106477_110572 cso_k2_106477_110572); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_110573_114668 : class_shape_ok1 true s_k2_110573_114668 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_110573_114668 : TPK 2 110573 114668.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 2 20000 400 110573 114668 p_k2_110573_114668 s_k2_110573_114668 chk_k2_110573_114668 cso_k2_110573_114668); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_114669_118764 : class_shape_ok1 true s_k2_114669_118764 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_114669_118764 : TPK 2 114669 118764.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 2 20000 400 114669 118764 p_k2_114669_118764 s_k2_114669_118764 chk_k2_114669_118764 cso_k2_114669_118764); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_118765_122860 : class_shape_ok1 true s_k2_118765_122860 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_118765_122860 : TPK 2 118765 122860.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 2 20000 400 118765 122860 p_k2_118765_122860 s_k2_118765_122860 chk_k2_118765_122860 cso_k2_118765_122860); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_122861_126956 : class_shape_ok1 true s_k2_122861_126956 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_122861_126956 : TPK 2 122861 126956.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 2 20000 400 122861 126956 p_k2_122861_126956 s_k2_122861_126956 chk_k2_122861_126956 cso_k2_122861_126956); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_126957_131051 : class_shape_ok1 true s_k2_126957_131051 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_126957_131051 : TPK 2 126957 131051.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 2 20000 400 126957 131051 p_k2_126957_131051 s_k2_126957_131051 chk_k2_126957_131051 cso_k2_126957_131051); try eassumption; unfold capk; cbn; lia.
Qed.

