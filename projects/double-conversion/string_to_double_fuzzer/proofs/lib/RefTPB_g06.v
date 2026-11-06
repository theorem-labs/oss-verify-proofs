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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RefTargetAssemblyTop RefTPBc_g06.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SP.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma cso_k0_21821_24556 : class_shape_ok true s_k0_21821_24556 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_21821_24556 : TP0 21821 24556.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 21821 24556 p_k0_21821_24556 s_k0_21821_24556 chk_k0_21821_24556 cso_k0_21821_24556); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_26189_28652 : class_shape_ok true s_k0_26189_28652 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_26189_28652 : TP0 26189 28652.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 26189 28652 p_k0_26189_28652 s_k0_26189_28652 chk_k0_26189_28652 cso_k0_26189_28652); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_28653_32748 : class_shape_ok true s_k0_28653_32748 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_28653_32748 : TP0 28653 32748.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 28653 32748 p_k0_28653_32748 s_k0_28653_32748 chk_k0_28653_32748 cso_k0_28653_32748); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_32749_36844 : class_shape_ok true s_k0_32749_36844 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_32749_36844 : TP0 32749 36844.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 32749 36844 p_k0_32749_36844 s_k0_32749_36844 chk_k0_32749_36844 cso_k0_32749_36844); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_37437_40940 : class_shape_ok true s_k0_37437_40940 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_37437_40940 : TP0 37437 40940.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 37437 40940 p_k0_37437_40940 s_k0_37437_40940 chk_k0_37437_40940 cso_k0_37437_40940); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_40941_43676 : class_shape_ok true s_k0_40941_43676 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_40941_43676 : TP0 40941 43676.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 40941 43676 p_k0_40941_43676 s_k0_40941_43676 chk_k0_40941_43676 cso_k0_40941_43676); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_45037_49132 : class_shape_ok true s_k0_45037_49132 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_45037_49132 : TP0 45037 49132.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 45037 49132 p_k0_45037_49132 s_k0_45037_49132 chk_k0_45037_49132 cso_k0_45037_49132); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_49133_52412 : class_shape_ok true s_k0_49133_52412 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_49133_52412 : TP0 49133 52412.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 49133 52412 p_k0_49133_52412 s_k0_49133_52412 chk_k0_49133_52412 cso_k0_49133_52412); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_53229_57324 : class_shape_ok true s_k0_53229_57324 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_53229_57324 : TP0 53229 57324.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 53229 57324 p_k0_53229_57324 s_k0_53229_57324 chk_k0_53229_57324 cso_k0_53229_57324); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_57325_61420 : class_shape_ok true s_k0_57325_61420 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_57325_61420 : TP0 57325 61420.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 57325 61420 p_k0_57325_61420 s_k0_57325_61420 chk_k0_57325_61420 cso_k0_57325_61420); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_61421_65516 : class_shape_ok true s_k0_61421_65516 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_61421_65516 : TP0 61421 65516.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 61421 65516 p_k0_61421_65516 s_k0_61421_65516 chk_k0_61421_65516 cso_k0_61421_65516); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_65517_69612 : class_shape_ok true s_k1_65517_69612 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_65517_69612 : TPK 1 65517 69612.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 65517 69612 p_k1_65517_69612 s_k1_65517_69612 chk_k1_65517_69612 cso_k1_65517_69612); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_69613_73708 : class_shape_ok true s_k1_69613_73708 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_69613_73708 : TPK 1 69613 73708.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 69613 73708 p_k1_69613_73708 s_k1_69613_73708 chk_k1_69613_73708 cso_k1_69613_73708); try eassumption; unfold capk; cbn; lia.
Qed.

