(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import LimBase LimMonad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Arms.
Variable L : Z.

(* [comment removed for export] *)
Lemma fr_arm_17 : forall i m, FR L i m (getcwd_spec (in_arg i 1)) (getcwd_spec (in_arg i 1)).
Proof. intros i m. unfold getcwd_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_19 : forall i m, FR L i m (eventfd2_spec (flag32 (in_arg i 1))) (eventfd2_spec (flag32 (in_arg i 1))).
Proof. intros i m. unfold eventfd2_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_20 : forall i m, FR L i m (epoll_create1_spec (flag32 (in_arg i 0))) (epoll_create1_spec (flag32 (in_arg i 0))).
Proof. intros i m. unfold epoll_create1_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_21 : forall i m, FR L i m (epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3)) (epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3)).
Proof. intros i m. unfold epoll_ctl_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_22 : forall i m, FR L i m (epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5)) (epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5)).
Proof. intros i m. unfold epoll_pwait_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_23 : forall i m, FR L i m (dup_spec (fd32 (in_arg i 0))) (dup_spec (fd32 (in_arg i 0))).
Proof. intros i m. unfold dup_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_24 : forall i m, FR L i m (dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2)) (dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2)).
Proof. intros i m. unfold dup3_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_25 : forall i m, FR L i m (fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2)) (fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2)).
Proof. intros i m. unfold fcntl_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_29 : forall i m, FR L i m (ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1))) (ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1))).
Proof. intros i m. unfold ioctl_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_32 : forall i m, FR L i m (flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1))) (flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1))).
Proof. intros i m. unfold flock_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_35 : forall i m, FR L i m (unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold unlinkat_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_46 : forall i m, FR L i m (ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1)) (ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1)).
Proof. intros i m. unfold ftruncate_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_48 : forall i m, FR L i m (faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold faccessat_spec. fq. Qed.

End Arms.
