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
Lemma arm_fcntl_relim : forall L i eff m, ca_check arm_fcntl i eff (relim L m) = map_cr (relim L) (ca_check arm_fcntl i eff m).
Proof. unif_arm. Qed.
Lemma arm_pipe2_relim : forall L i eff m, ca_check arm_pipe2 i eff (relim L m) = map_cr (relim L) (ca_check arm_pipe2 i eff m).
Proof. unif_arm. Qed.
Lemma arm_pwrite64_relim : forall L i eff m, ca_check arm_pwrite64 i eff (relim L m) = map_cr (relim L) (ca_check arm_pwrite64 i eff m).
Proof. unif_arm. Qed.
Lemma arm_timerfd_create_relim : forall L i eff m, ca_check arm_timerfd_create i eff (relim L m) = map_cr (relim L) (ca_check arm_timerfd_create i eff m).
Proof. unif_arm. Qed.
Lemma arm_sched_getaffinity_relim : forall L i eff m, ca_check arm_sched_getaffinity i eff (relim L m) = map_cr (relim L) (ca_check arm_sched_getaffinity i eff m).
Proof. unif_arm. Qed.
Lemma arm_sched_yield_relim : forall L i eff m, ca_check arm_sched_yield i eff (relim L m) = map_cr (relim L) (ca_check arm_sched_yield i eff m).
Proof. unif_arm. Qed.
Lemma arm_setresuid_relim : forall L i eff m, ca_check arm_setresuid i eff (relim L m) = map_cr (relim L) (ca_check arm_setresuid i eff m).
Proof. unif_arm. Qed.
Lemma arm_getpid_relim : forall L i eff m, ca_check arm_getpid i eff (relim L m) = map_cr (relim L) (ca_check arm_getpid i eff m).
Proof. unif_arm. Qed.
Lemma arm_bind_relim : forall L i eff m, ca_check arm_bind i eff (relim L m) = map_cr (relim L) (ca_check arm_bind i eff m).
Proof. unif_arm. Qed.
Lemma arm_setsockopt_relim : forall L i eff m, ca_check arm_setsockopt i eff (relim L m) = map_cr (relim L) (ca_check arm_setsockopt i eff m).
Proof. unif_arm. Qed.
Lemma arm_mmap_relim_b : forall L i eff m, (vm_limit (m_vmmaps m) <= L)%Z -> Sys.Mm.Mmap.mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m = false -> ca_check arm_mmap i eff (relim L m) = map_cr (relim L) (ca_check arm_mmap i eff m).
Proof. intros L i eff m HL HB. revert HL. unif_arm_b HB. Qed.
Lemma arm_faccessat2_relim : forall L i eff m, ca_check arm_faccessat2 i eff (relim L m) = map_cr (relim L) (ca_check arm_faccessat2 i eff m).
Proof. unif_arm. Qed.
