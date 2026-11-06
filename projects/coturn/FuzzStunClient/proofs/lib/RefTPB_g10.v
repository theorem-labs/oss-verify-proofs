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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefTPBc_g10.
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
Lemma cso_k10_33521659_40239097 : class_shape_ok true s_k10_33521659_40239097 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k10_33521659_40239097 : TPK 10 33521659 40239097.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 10 20000 400 33521659 40239097 p_k10_33521659_40239097 s_k10_33521659_40239097 chk_k10_33521659_40239097 cso_k10_33521659_40239097); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k10_40239098_46956536 : class_shape_ok true s_k10_40239098_46956536 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k10_40239098_46956536 : TPK 10 40239098 46956536.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 10 20000 400 40239098 46956536 p_k10_40239098_46956536 s_k10_40239098_46956536 chk_k10_40239098_46956536 cso_k10_40239098_46956536); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k10_46956537_53673975 : class_shape_ok true s_k10_46956537_53673975 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k10_46956537_53673975 : TPK 10 46956537 53673975.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 10 20000 400 46956537 53673975 p_k10_46956537_53673975 s_k10_46956537_53673975 chk_k10_46956537_53673975 cso_k10_46956537_53673975); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k10_53673976_60391414 : class_shape_ok true s_k10_53673976_60391414 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k10_53673976_60391414 : TPK 10 53673976 60391414.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 10 20000 400 53673976 60391414 p_k10_53673976_60391414 s_k10_53673976_60391414 chk_k10_53673976_60391414 cso_k10_53673976_60391414); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k10_60391415_67108857 : class_shape_ok true s_k10_60391415_67108857 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k10_60391415_67108857 : TPK 10 60391415 67108857.
Proof.
  unfold TPK. intros RH. intros.
  eapply (target_class_sound_k RH 10 20000 400 60391415 67108857 p_k10_60391415_67108857 s_k10_60391415_67108857 chk_k10_60391415_67108857 cso_k10_60391415_67108857); try eassumption; unfold capk; cbn; lia.
Qed.

