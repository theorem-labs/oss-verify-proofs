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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RefTargetAssemblyTop RefTPBc_g03.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SP.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma cso_k0_1_12 : class_shape_ok true s_k0_1_12 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1_12 : TP0 1 12.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 1 12 p_k0_1_12 s_k0_1_12 chk_k0_1_12 cso_k0_1_12); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_13_28 : class_shape_ok true s_k0_13_28 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_13_28 : TP0 13 28.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 13 28 p_k0_13_28 s_k0_13_28 chk_k0_13_28 cso_k0_13_28); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_29_44 : class_shape_ok true s_k0_29_44 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_29_44 : TP0 29 44.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 29 44 p_k0_29_44 s_k0_29_44 chk_k0_29_44 cso_k0_29_44); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_45_60 : class_shape_ok true s_k0_45_60 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_45_60 : TP0 45 60.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 45 60 p_k0_45_60 s_k0_45_60 chk_k0_45_60 cso_k0_45_60); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_61_76 : class_shape_ok true s_k0_61_76 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_61_76 : TP0 61 76.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 61 76 p_k0_61_76 s_k0_61_76 chk_k0_61_76 cso_k0_61_76); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_77_92 : class_shape_ok true s_k0_77_92 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_77_92 : TP0 77 92.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 77 92 p_k0_77_92 s_k0_77_92 chk_k0_77_92 cso_k0_77_92); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_93_108 : class_shape_ok true s_k0_93_108 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_93_108 : TP0 93 108.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 93 108 p_k0_93_108 s_k0_93_108 chk_k0_93_108 cso_k0_93_108); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_109_124 : class_shape_ok true s_k0_109_124 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_109_124 : TP0 109 124.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 109 124 p_k0_109_124 s_k0_109_124 chk_k0_109_124 cso_k0_109_124); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_125_140 : class_shape_ok true s_k0_125_140 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_125_140 : TP0 125 140.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 125 140 p_k0_125_140 s_k0_125_140 chk_k0_125_140 cso_k0_125_140); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_141_156 : class_shape_ok true s_k0_141_156 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_141_156 : TP0 141 156.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 141 156 p_k0_141_156 s_k0_141_156 chk_k0_141_156 cso_k0_141_156); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_157_188 : class_shape_ok true s_k0_157_188 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_157_188 : TP0 157 188.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 157 188 p_k0_157_188 s_k0_157_188 chk_k0_157_188 cso_k0_157_188); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_189_236 : class_shape_ok true s_k0_189_236 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_189_236 : TP0 189 236.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 189 236 p_k0_189_236 s_k0_189_236 chk_k0_189_236 cso_k0_189_236); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_237_284 : class_shape_ok true s_k0_237_284 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_237_284 : TP0 237 284.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 237 284 p_k0_237_284 s_k0_237_284 chk_k0_237_284 cso_k0_237_284); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_285_316 : class_shape_ok true s_k0_285_316 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_285_316 : TP0 285 316.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 285 316 p_k0_285_316 s_k0_285_316 chk_k0_285_316 cso_k0_285_316); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_126957_131051 : class_shape_ok true s_k1_126957_131051 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_126957_131051 : TPK 1 126957 131051.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k 1 20000 400 126957 131051 p_k1_126957_131051 s_k1_126957_131051 chk_k1_126957_131051 cso_k1_126957_131051); try eassumption; unfold capk; cbn; lia.
Qed.

