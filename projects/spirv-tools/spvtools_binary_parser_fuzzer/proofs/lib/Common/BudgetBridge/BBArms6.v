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
Lemma arm_dup_relim : forall L i eff m, ca_check arm_dup i eff (relim L m) = map_cr (relim L) (ca_check arm_dup i eff m).
Proof. unif_arm. Qed.
Lemma arm_openat_relim : forall L i eff m, ca_check arm_openat i eff (relim L m) = map_cr (relim L) (ca_check arm_openat i eff m).
Proof. unif_arm. Qed.
Lemma arm_writev_relim : forall L i eff m, ca_check arm_writev i eff (relim L m) = map_cr (relim L) (ca_check arm_writev i eff m).
Proof. unif_arm. Qed.
Lemma arm_fsync_relim : forall L i eff m, ca_check arm_fsync i eff (relim L m) = map_cr (relim L) (ca_check arm_fsync i eff m).
Proof. unif_arm. Qed.
Lemma arm_clock_gettime_relim : forall L i eff m, ca_check arm_clock_gettime i eff (relim L m) = map_cr (relim L) (ca_check arm_clock_gettime i eff m).
Proof. unif_arm. Qed.
Lemma arm_setgid_relim : forall L i eff m, ca_check arm_setgid i eff (relim L m) = map_cr (relim L) (ca_check arm_setgid i eff m).
Proof. unif_arm. Qed.
Lemma arm_prctl_relim : forall L i eff m, ca_check arm_prctl i eff (relim L m) = map_cr (relim L) (ca_check arm_prctl i eff m).
Proof. unif_arm. Qed.
Lemma arm_socket_relim : forall L i eff m, ca_check arm_socket i eff (relim L m) = map_cr (relim L) (ca_check arm_socket i eff m).
Proof. unif_arm. Qed.
Lemma arm_sendto_relim : forall L i eff m, ca_check arm_sendto i eff (relim L m) = map_cr (relim L) (ca_check arm_sendto i eff m).
Proof. unif_arm. Qed.
Lemma arm_munmap_relim : forall L i eff m, ca_check arm_munmap i eff (relim L m) = map_cr (relim L) (ca_check arm_munmap i eff m).
Proof. unif_arm. Qed.

Lemma arm_getrandom_relim : forall L i eff m, ca_check arm_getrandom i eff (relim L m) = map_cr (relim L) (ca_check arm_getrandom i eff m).
Proof. unif_arm. Qed.
