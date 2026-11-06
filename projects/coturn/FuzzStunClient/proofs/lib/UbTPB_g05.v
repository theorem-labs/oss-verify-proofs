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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbTPBc_g05.
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
Lemma cso_k0_40941_43676 : class_shape_ok true s_k0_40941_43676 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_40941_43676 : TP0 40941 43676.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 40941 43676 p_k0_40941_43676 s_k0_40941_43676 chk_k0_40941_43676 cso_k0_40941_43676); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_43677_45036 : class_shape_ok true s_k0_43677_45036 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_43677_45036 : TP0 43677 45036.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 43677 45036 p_k0_43677_45036 s_k0_43677_45036 chk_k0_43677_45036 cso_k0_43677_45036); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_45037_49132 : class_shape_ok true s_k0_45037_49132 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_45037_49132 : TP0 45037 49132.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 45037 49132 p_k0_45037_49132 s_k0_45037_49132 chk_k0_45037_49132 cso_k0_45037_49132); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_49133_52412 : class_shape_ok true s_k0_49133_52412 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_49133_52412 : TP0 49133 52412.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 49133 52412 p_k0_49133_52412 s_k0_49133_52412 chk_k0_49133_52412 cso_k0_49133_52412); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_52413_53228 : class_shape_ok true s_k0_52413_53228 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_52413_53228 : TP0 52413 53228.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 52413 53228 p_k0_52413_53228 s_k0_52413_53228 chk_k0_52413_53228 cso_k0_52413_53228); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_53229_57324 : class_shape_ok true s_k0_53229_57324 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_53229_57324 : TP0 53229 57324.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 53229 57324 p_k0_53229_57324 s_k0_53229_57324 chk_k0_53229_57324 cso_k0_53229_57324); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_57325_61420 : class_shape_ok true s_k0_57325_61420 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_57325_61420 : TP0 57325 61420.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 57325 61420 p_k0_57325_61420 s_k0_57325_61420 chk_k0_57325_61420 cso_k0_57325_61420); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_61421_65516 : class_shape_ok true s_k0_61421_65516 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_61421_65516 : TP0 61421 65516.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 61421 65516 p_k0_61421_65516 s_k0_61421_65516 chk_k0_61421_65516 cso_k0_61421_65516); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_65517_65529 : class_shape_ok true s_k0_65517_65529 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_65517_65529 : TP0 65517 65529.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 65517 65529 p_k0_65517_65529 s_k0_65517_65529 chk_k0_65517_65529 cso_k0_65517_65529); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_32763_36844 : class_shape_ok1 true s_k1_32763_36844 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_32763_36844 : TPK 1 32763 36844.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 1 20000 400 32763 36844 p_k1_32763_36844 s_k1_32763_36844 chk_k1_32763_36844 cso_k1_32763_36844); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_36845_37436 : class_shape_ok1 true s_k1_36845_37436 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_36845_37436 : TPK 1 36845 37436.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 1 20000 400 36845 37436 p_k1_36845_37436 s_k1_36845_37436 chk_k1_36845_37436 cso_k1_36845_37436); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_37437_40940 : class_shape_ok1 true s_k1_37437_40940 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_37437_40940 : TPK 1 37437 40940.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_low_k RH 1 20000 400 37437 40940 p_k1_37437_40940 s_k1_37437_40940 chk_k1_37437_40940 cso_k1_37437_40940); try eassumption; unfold capk; cbn; lia.
Qed.

