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
Lemma arm_dup3_relim : forall L i eff m, ca_check arm_dup3 i eff (relim L m) = map_cr (relim L) (ca_check arm_dup3 i eff m).
Proof. unif_arm. Qed.
Lemma arm_close_relim : forall L i eff m, ca_check arm_close i eff (relim L m) = map_cr (relim L) (ca_check arm_close i eff m).
Proof. unif_arm. Qed.
Lemma arm_pread64_relim : forall L i eff m, ca_check arm_pread64 i eff (relim L m) = map_cr (relim L) (ca_check arm_pread64 i eff m).
Proof. unif_arm. Qed.
Lemma arm_fdatasync_relim : forall L i eff m, ca_check arm_fdatasync i eff (relim L m) = map_cr (relim L) (ca_check arm_fdatasync i eff m).
Proof. unif_arm. Qed.
Lemma arm_sched_setscheduler_relim : forall L i eff m, ca_check arm_sched_setscheduler i eff (relim L m) = map_cr (relim L) (ca_check arm_sched_setscheduler i eff m).
Proof. unif_arm. Qed.
Lemma arm_setuid_relim : forall L i eff m, ca_check arm_setuid i eff (relim L m) = map_cr (relim L) (ca_check arm_setuid i eff m).
Proof. unif_arm. Qed.
Lemma arm_gettimeofday_relim : forall L i eff m, ca_check arm_gettimeofday i eff (relim L m) = map_cr (relim L) (ca_check arm_gettimeofday i eff m).
Proof. unif_arm. Qed.
Lemma arm_socketpair_relim : forall L i eff m, ca_check arm_socketpair i eff (relim L m) = map_cr (relim L) (ca_check arm_socketpair i eff m).
Proof. unif_arm. Qed.
Lemma arm_recvfrom_relim : forall L i eff m, ca_check arm_recvfrom i eff (relim L m) = map_cr (relim L) (ca_check arm_recvfrom i eff m).
Proof. unif_arm. Qed.
Lemma arm_clone_relim : forall L i eff m, ca_check arm_clone i eff (relim L m) = map_cr (relim L) (ca_check arm_clone i eff m).
Proof. unif_arm. Qed.
Lemma arm_clone3_relim : forall L i eff m, ca_check arm_clone3 i eff (relim L m) = map_cr (relim L) (ca_check arm_clone3 i eff m).
Proof. unif_arm. Qed.
