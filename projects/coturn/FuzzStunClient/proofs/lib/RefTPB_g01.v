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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefTPBc_g01.
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
Lemma cso_k0_0_0 : class_shape_ok false s_k0_0_0 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_0_0 : TP0 0 0.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 0 0 p_k0_0_0 s_k0_0_0 chk_k0_0_0 cso_k0_0_0); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_1_12 : class_shape_ok true s_k0_1_12 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1_12 : TP0 1 12.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 1 12 p_k0_1_12 s_k0_1_12 chk_k0_1_12 cso_k0_1_12); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_13_28 : class_shape_ok true s_k0_13_28 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_13_28 : TP0 13 28.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 13 28 p_k0_13_28 s_k0_13_28 chk_k0_13_28 cso_k0_13_28); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_29_44 : class_shape_ok true s_k0_29_44 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_29_44 : TP0 29 44.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 29 44 p_k0_29_44 s_k0_29_44 chk_k0_29_44 cso_k0_29_44); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_45_60 : class_shape_ok true s_k0_45_60 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_45_60 : TP0 45 60.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 45 60 p_k0_45_60 s_k0_45_60 chk_k0_45_60 cso_k0_45_60); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_61_76 : class_shape_ok true s_k0_61_76 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_61_76 : TP0 61 76.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 61 76 p_k0_61_76 s_k0_61_76 chk_k0_61_76 cso_k0_61_76); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_77_92 : class_shape_ok true s_k0_77_92 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_77_92 : TP0 77 92.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 77 92 p_k0_77_92 s_k0_77_92 chk_k0_77_92 cso_k0_77_92); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_93_108 : class_shape_ok true s_k0_93_108 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_93_108 : TP0 93 108.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 93 108 p_k0_93_108 s_k0_93_108 chk_k0_93_108 cso_k0_93_108); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_109_124 : class_shape_ok true s_k0_109_124 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_109_124 : TP0 109 124.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 109 124 p_k0_109_124 s_k0_109_124 chk_k0_109_124 cso_k0_109_124); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_125_140 : class_shape_ok true s_k0_125_140 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_125_140 : TP0 125 140.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 125 140 p_k0_125_140 s_k0_125_140 chk_k0_125_140 cso_k0_125_140); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_141_156 : class_shape_ok true s_k0_141_156 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_141_156 : TP0 141 156.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 141 156 p_k0_141_156 s_k0_141_156 chk_k0_141_156 cso_k0_141_156); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_157_188 : class_shape_ok true s_k0_157_188 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_157_188 : TP0 157 188.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 157 188 p_k0_157_188 s_k0_157_188 chk_k0_157_188 cso_k0_157_188); try eassumption; lia.
Qed.

