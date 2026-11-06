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
Lemma arm_epoll_ctl_relim : forall L i eff m, ca_check arm_epoll_ctl i eff (relim L m) = map_cr (relim L) (ca_check arm_epoll_ctl i eff m).
Proof. unif_arm. Qed.
Lemma arm_ftruncate_relim : forall L i eff m, ca_check arm_ftruncate i eff (relim L m) = map_cr (relim L) (ca_check arm_ftruncate i eff m).
Proof. unif_arm. Qed.
Lemma arm_write_relim : forall L i eff m, ca_check arm_write i eff (relim L m) = map_cr (relim L) (ca_check arm_write i eff m).
Proof. unif_arm. Qed.
Lemma arm_newfstatat_relim : forall L i eff m, ca_check arm_newfstatat i eff (relim L m) = map_cr (relim L) (ca_check arm_newfstatat i eff m).
Proof. unif_arm. Qed.
Lemma arm_futex_relim : forall L i eff m, ca_check arm_futex i eff (relim L m) = map_cr (relim L) (ca_check arm_futex i eff m).
Proof. unif_arm. Qed.
Lemma arm_rt_sigaction_relim : forall L i eff m, ca_check arm_rt_sigaction i eff (relim L m) = map_cr (relim L) (ca_check arm_rt_sigaction i eff m).
Proof. unif_arm. Qed.
Lemma arm_setgroups_relim : forall L i eff m, ca_check arm_setgroups i eff (relim L m) = map_cr (relim L) (ca_check arm_setgroups i eff m).
Proof. unif_arm. Qed.
Lemma arm_getegid_relim : forall L i eff m, ca_check arm_getegid i eff (relim L m) = map_cr (relim L) (ca_check arm_getegid i eff m).
Proof. unif_arm. Qed.
Lemma arm_getsockname_relim : forall L i eff m, ca_check arm_getsockname i eff (relim L m) = map_cr (relim L) (ca_check arm_getsockname i eff m).
Proof. unif_arm. Qed.
Lemma arm_recvmsg_relim : forall L i eff m, ca_check arm_recvmsg i eff (relim L m) = map_cr (relim L) (ca_check arm_recvmsg i eff m).
Proof. unif_arm. Qed.
Lemma arm_wait4_relim : forall L i eff m, ca_check arm_wait4 i eff (relim L m) = map_cr (relim L) (ca_check arm_wait4 i eff m).
Proof. unif_arm. Qed.
