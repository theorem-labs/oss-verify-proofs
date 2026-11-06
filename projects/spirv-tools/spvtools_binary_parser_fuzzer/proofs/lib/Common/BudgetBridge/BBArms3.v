(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common.BudgetBridge Require Import BBArmsBase.
Lemma arm_epoll_create1_relim : forall L i eff m, ca_check arm_epoll_create1 i eff (relim L m) = map_cr (relim L) (ca_check arm_epoll_create1 i eff m).
Proof. unif_arm. Qed.
Lemma arm_unlinkat_relim : forall L i eff m, ca_check arm_unlinkat i eff (relim L m) = map_cr (relim L) (ca_check arm_unlinkat i eff m).
Proof. unif_arm. Qed.
Lemma arm_read_relim : forall L i eff m, ca_check arm_read i eff (relim L m) = map_cr (relim L) (ca_check arm_read i eff m).
Proof. unif_arm. Qed.
Lemma arm_readlinkat_relim : forall L i eff m, ca_check arm_readlinkat i eff (relim L m) = map_cr (relim L) (ca_check arm_readlinkat i eff m).
Proof. unif_arm. Qed.
Lemma arm_set_tid_address_relim : forall L i eff m, ca_check arm_set_tid_address i eff (relim L m) = map_cr (relim L) (ca_check arm_set_tid_address i eff m).
Proof. unif_arm. Qed.
Lemma arm_sigaltstack_relim : forall L i eff m, ca_check arm_sigaltstack i eff (relim L m) = map_cr (relim L) (ca_check arm_sigaltstack i eff m).
Proof. unif_arm. Qed.
Lemma arm_getgroups_relim : forall L i eff m, ca_check arm_getgroups i eff (relim L m) = map_cr (relim L) (ca_check arm_getgroups i eff m).
Proof. unif_arm. Qed.
Lemma arm_getgid_relim : forall L i eff m, ca_check arm_getgid i eff (relim L m) = map_cr (relim L) (ca_check arm_getgid i eff m).
Proof. unif_arm. Qed.
Lemma arm_connect_relim : forall L i eff m, ca_check arm_connect i eff (relim L m) = map_cr (relim L) (ca_check arm_connect i eff m).
Proof. unif_arm. Qed.
Lemma arm_sendmsg_relim : forall L i eff m, ca_check arm_sendmsg i eff (relim L m) = map_cr (relim L) (ca_check arm_sendmsg i eff m).
Proof. unif_arm. Qed.
Lemma arm_accept4_relim : forall L i eff m, ca_check arm_accept4 i eff (relim L m) = map_cr (relim L) (ca_check arm_accept4 i eff m).
Proof. unif_arm. Qed.
