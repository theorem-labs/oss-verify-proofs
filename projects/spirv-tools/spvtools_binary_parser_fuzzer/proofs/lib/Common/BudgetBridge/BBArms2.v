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
Lemma arm_eventfd2_relim : forall L i eff m, ca_check arm_eventfd2 i eff (relim L m) = map_cr (relim L) (ca_check arm_eventfd2 i eff m).
Proof. unif_arm. Qed.
Lemma arm_flock_relim : forall L i eff m, ca_check arm_flock i eff (relim L m) = map_cr (relim L) (ca_check arm_flock i eff m).
Proof. unif_arm. Qed.
Lemma arm_lseek_relim : forall L i eff m, ca_check arm_lseek i eff (relim L m) = map_cr (relim L) (ca_check arm_lseek i eff m).
Proof. unif_arm. Qed.
Lemma arm_ppoll_relim : forall L i eff m, ca_check arm_ppoll i eff (relim L m) = map_cr (relim L) (ca_check arm_ppoll i eff m).
Proof. unif_arm. Qed.
Lemma arm_exit_group_relim : forall L i eff m, ca_check arm_exit_group i eff (relim L m) = map_cr (relim L) (ca_check arm_exit_group i eff m).
Proof. unif_arm. Qed.
Lemma arm_tgkill_relim : forall L i eff m, ca_check arm_tgkill i eff (relim L m) = map_cr (relim L) (ca_check arm_tgkill i eff m).
Proof. unif_arm. Qed.
Lemma arm_setsid_relim : forall L i eff m, ca_check arm_setsid i eff (relim L m) = map_cr (relim L) (ca_check arm_setsid i eff m).
Proof. unif_arm. Qed.
Lemma arm_geteuid_relim : forall L i eff m, ca_check arm_geteuid i eff (relim L m) = map_cr (relim L) (ca_check arm_geteuid i eff m).
Proof. unif_arm. Qed.
Lemma arm_accept_relim : forall L i eff m, ca_check arm_accept i eff (relim L m) = map_cr (relim L) (ca_check arm_accept i eff m).
Proof. unif_arm. Qed.
Lemma arm_shutdown_relim : forall L i eff m, ca_check arm_shutdown i eff (relim L m) = map_cr (relim L) (ca_check arm_shutdown i eff m).
Proof. unif_arm. Qed.
Lemma arm_madvise_relim : forall L i eff m, ca_check arm_madvise i eff (relim L m) = map_cr (relim L) (ca_check arm_madvise i eff m).
Proof. unif_arm. Qed.
