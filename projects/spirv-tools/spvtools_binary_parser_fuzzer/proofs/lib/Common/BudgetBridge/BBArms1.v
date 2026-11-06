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
Lemma arm_getcwd_relim : forall L i eff m, ca_check arm_getcwd i eff (relim L m) = map_cr (relim L) (ca_check arm_getcwd i eff m).
Proof. unif_arm. Qed.
Lemma arm_ioctl_relim : forall L i eff m, ca_check arm_ioctl i eff (relim L m) = map_cr (relim L) (ca_check arm_ioctl i eff m).
Proof. unif_arm. Qed.
Lemma arm_getdents64_relim : forall L i eff m, ca_check arm_getdents64 i eff (relim L m) = map_cr (relim L) (ca_check arm_getdents64 i eff m).
Proof. unif_arm. Qed.
Lemma arm_pselect6_relim : forall L i eff m, ca_check arm_pselect6 i eff (relim L m) = map_cr (relim L) (ca_check arm_pselect6 i eff m).
Proof. unif_arm. Qed.
Lemma arm_exit_relim : forall L i eff m, ca_check arm_exit i eff (relim L m) = map_cr (relim L) (ca_check arm_exit i eff m).
Proof. unif_arm. Qed.
Lemma arm_tkill_relim : forall L i eff m, ca_check arm_tkill i eff (relim L m) = map_cr (relim L) (ca_check arm_tkill i eff m).
Proof. unif_arm. Qed.
Lemma arm_setresgid_relim : forall L i eff m, ca_check arm_setresgid i eff (relim L m) = map_cr (relim L) (ca_check arm_setresgid i eff m).
Proof. unif_arm. Qed.
Lemma arm_getuid_relim : forall L i eff m, ca_check arm_getuid i eff (relim L m) = map_cr (relim L) (ca_check arm_getuid i eff m).
Proof. unif_arm. Qed.
Lemma arm_listen_relim : forall L i eff m, ca_check arm_listen i eff (relim L m) = map_cr (relim L) (ca_check arm_listen i eff m).
Proof. unif_arm. Qed.
Lemma arm_getsockopt_relim : forall L i eff m, ca_check arm_getsockopt i eff (relim L m) = map_cr (relim L) (ca_check arm_getsockopt i eff m).
Proof. unif_arm. Qed.
Lemma arm_mprotect_relim_b : forall L i eff m, (vm_limit (m_vmmaps m) <= L)%Z -> Sys.Mm.Mprotect.mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) m = false -> ca_check arm_mprotect i eff (relim L m) = map_cr (relim L) (ca_check arm_mprotect i eff m).
Proof. intros L i eff m HL HB. revert HL. unif_arm_b HB. Qed.
