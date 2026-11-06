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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbTPBc_g04.
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
Lemma cso_k0_12269_13084 : class_shape_ok true s_k0_12269_13084 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_12269_13084 : TP0 12269 13084.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 12269 13084 p_k0_12269_13084 s_k0_12269_13084 chk_k0_12269_13084 cso_k0_12269_13084); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_13085_16364 : class_shape_ok true s_k0_13085_16364 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_13085_16364 : TP0 13085 16364.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 13085 16364 p_k0_13085_16364 s_k0_13085_16364 chk_k0_13085_16364 cso_k0_13085_16364); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_16365_18700 : class_shape_ok true s_k0_16365_18700 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_16365_18700 : TP0 16365 18700.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 16365 18700 p_k0_16365_18700 s_k0_16365_18700 chk_k0_16365_18700 cso_k0_16365_18700); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_18701_20460 : class_shape_ok true s_k0_18701_20460 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_18701_20460 : TP0 18701 20460.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 18701 20460 p_k0_18701_20460 s_k0_18701_20460 chk_k0_18701_20460 cso_k0_18701_20460); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_20461_21820 : class_shape_ok true s_k0_20461_21820 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_20461_21820 : TP0 20461 21820.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 20461 21820 p_k0_20461_21820 s_k0_20461_21820 chk_k0_20461_21820 cso_k0_20461_21820); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_21821_24556 : class_shape_ok true s_k0_21821_24556 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_21821_24556 : TP0 21821 24556.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 21821 24556 p_k0_21821_24556 s_k0_21821_24556 chk_k0_21821_24556 cso_k0_21821_24556); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_24557_26188 : class_shape_ok true s_k0_24557_26188 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_24557_26188 : TP0 24557 26188.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 24557 26188 p_k0_24557_26188 s_k0_24557_26188 chk_k0_24557_26188 cso_k0_24557_26188); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_26189_28652 : class_shape_ok true s_k0_26189_28652 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_26189_28652 : TP0 26189 28652.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 26189 28652 p_k0_26189_28652 s_k0_26189_28652 chk_k0_26189_28652 cso_k0_26189_28652); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_28653_32748 : class_shape_ok true s_k0_28653_32748 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_28653_32748 : TP0 28653 32748.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 28653 32748 p_k0_28653_32748 s_k0_28653_32748 chk_k0_28653_32748 cso_k0_28653_32748); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_32749_36844 : class_shape_ok true s_k0_32749_36844 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_32749_36844 : TP0 32749 36844.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 32749 36844 p_k0_32749_36844 s_k0_32749_36844 chk_k0_32749_36844 cso_k0_32749_36844); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_36845_37436 : class_shape_ok true s_k0_36845_37436 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_36845_37436 : TP0 36845 37436.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 36845 37436 p_k0_36845_37436 s_k0_36845_37436 chk_k0_36845_37436 cso_k0_36845_37436); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_37437_40940 : class_shape_ok true s_k0_37437_40940 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_37437_40940 : TP0 37437 40940.
Proof.
  unfold TP0. intros RH. intros.
  eapply (target_class_sound RH 20000 400 37437 40940 p_k0_37437_40940 s_k0_37437_40940 chk_k0_37437_40940 cso_k0_37437_40940); try eassumption; lia.
Qed.

