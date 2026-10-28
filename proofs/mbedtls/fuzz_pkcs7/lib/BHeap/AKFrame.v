(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Lemma mo_frame_mat : forall mo mo', mo_mat mo mo' -> mo_frame mo mo'.
Proof. (intros mo mo' dd_H; ddestruct dd_H as (A & _ & _ & B & C & D & E & F)). repeat split; assumption. Qed.

#[using="Type"] Lemma mo_frame_with_vmmaps : forall mo h, mo_frame mo (with_vmmaps h mo).
Proof. intros. destruct mo; repeat split; reflexivity. Qed.
#[using="Type"] Lemma mo_frame_with_mmap_backing : forall mo f a n, mo_frame mo (with_mmap_backing f a n mo).
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b f); destruct mo; repeat split; reflexivity. Qed.
#[using="Type"] Lemma mo_frame_with_mmap_destroyed : forall mo a n h, mo_frame mo (with_mmap_destroyed a n h mo).
Proof. intros. unfold with_mmap_destroyed. destruct mo; repeat split; reflexivity. Qed.
#[using="Type"] Lemma mo_frame_vm_forget_range : forall mo lo hi, mo_frame mo (vm_forget_range lo hi mo).
Proof. intros. destruct mo; repeat split; reflexivity. Qed.

#[using="Type"] Lemma mo_frame_anon_grant : forall f a n mo, mo_frame mo (anon_grant f a n mo).
Proof. intros. unfold anon_grant. eapply mo_frame_trans; [apply mo_frame_with_vmmaps| apply mo_frame_with_mmap_backing]. Qed.
#[using="Type"] Lemma mo_frame_fixrw_fresh : forall f a n mo, mo_frame mo (fixrw_fresh f a n mo).
Proof. intros. unfold fixrw_fresh. eapply mo_frame_trans; [apply mo_frame_with_vmmaps| apply mo_frame_with_mmap_backing]. Qed.
#[using="Type"] Lemma mo_frame_fixrw_commit : forall f a n mo, mo_frame mo (fixrw_commit f a n mo).
Proof.
  intros. unfold fixrw_commit, with_mmap_replacement.
  eapply mo_frame_trans; [apply mo_frame_with_vmmaps|]. eapply mo_frame_trans; [apply mo_frame_vm_forget_range| apply mo_frame_with_mmap_backing].
Qed.
#[using="Type"] Lemma mo_frame_munmap_model : forall a n mo, mo_frame mo (munmap_model a n mo).
Proof. intros. unfold munmap_model. apply mo_frame_with_mmap_destroyed. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma mo_frame_madvise : forall mo a n, mo_frame mo (madvise_dontneed_next mo a n).
Proof. intros. unfold madvise_dontneed_next. destruct mo; repeat split; reflexivity. Qed.
#[using="Type"] Lemma mo_frame_madvise_model : forall a n mo, mo_frame mo (madvise_model a n mo).
Proof. intros. unfold madvise_model. apply mo_frame_madvise. Qed.

(* [comment removed for export] *)
Definition KF (K : Model -> Prop) (mo0 : Model) : Model -> Prop := fun mo => K mo /\ mo_frame mo0 mo.

#[using="Type"] Lemma kinv_KF : forall L CS K mo0, kinv L CS K -> kinv L CS (KF K mo0).
Proof.
  intros L CS K mo0 KL. split.
  - intros mo [HK _]. exact (ki_halted KL mo HK).
  - intros mo [HK _]. exact (ki_top KL mo HK).
  - intros mo acc [HK FR] OK. ddestruct (ki_mat KL mo acc HK OK) as (mo' & E & HK' & MM).
    exists mo'. split; [exact E|]. split; [| exact MM]. split; [exact HK'|]. eapply mo_frame_trans; [exact FR| apply mo_frame_mat; exact MM].
Qed.

End ARUN_1.
