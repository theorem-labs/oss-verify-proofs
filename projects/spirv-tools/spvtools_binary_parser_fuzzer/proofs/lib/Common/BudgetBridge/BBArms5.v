(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (brk's budget charge brk_grow_bytes through relim, and the budget cases after the arm unification). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common.BudgetBridge Require Import BBArmsBase.
Lemma arm_epoll_pwait_relim : forall L i eff m, ca_check arm_epoll_pwait i eff (relim L m) = map_cr (relim L) (ca_check arm_epoll_pwait i eff m).
Proof. unif_arm. Qed.
Lemma arm_faccessat_relim : forall L i eff m, ca_check arm_faccessat i eff (relim L m) = map_cr (relim L) (ca_check arm_faccessat i eff m).
Proof. unif_arm. Qed.
Lemma arm_readv_relim : forall L i eff m, ca_check arm_readv i eff (relim L m) = map_cr (relim L) (ca_check arm_readv i eff m).
Proof. unif_arm. Qed.
Lemma arm_fstat_relim : forall L i eff m, ca_check arm_fstat i eff (relim L m) = map_cr (relim L) (ca_check arm_fstat i eff m).
Proof. unif_arm. Qed.
Lemma arm_nanosleep_relim : forall L i eff m, ca_check arm_nanosleep i eff (relim L m) = map_cr (relim L) (ca_check arm_nanosleep i eff m).
Proof. unif_arm. Qed.
Lemma arm_rt_sigprocmask_relim : forall L i eff m, ca_check arm_rt_sigprocmask i eff (relim L m) = map_cr (relim L) (ca_check arm_rt_sigprocmask i eff m).
Proof. unif_arm. Qed.
Lemma arm_uname_relim : forall L i eff m, ca_check arm_uname i eff (relim L m) = map_cr (relim L) (ca_check arm_uname i eff m).
Proof. unif_arm. Qed.
Lemma arm_gettid_relim : forall L i eff m, ca_check arm_gettid i eff (relim L m) = map_cr (relim L) (ca_check arm_gettid i eff m).
Proof. unif_arm. Qed.
Lemma arm_getpeername_relim : forall L i eff m, ca_check arm_getpeername i eff (relim L m) = map_cr (relim L) (ca_check arm_getpeername i eff m).
Proof. unif_arm. Qed.
(* At the revision [Mmap.brk_budget_ok] charges [Mmap.brk_grow_bytes h r],
   a constant [chkunf] does not unfold.  It reads [vm_brk] only, so
   [relim] leaves it alone. *)
Lemma brk_grow_bytes_relim : forall L m r,
  Sys.Mm.Mmap.brk_grow_bytes (m_vmmaps (relim L m)) r = Sys.Mm.Mmap.brk_grow_bytes (m_vmmaps m) r.
Proof. reflexivity. Qed.
#[local] Hint Rewrite brk_grow_bytes_relim : relim.
Lemma arm_brk_relim_b : forall L i eff m, (vm_limit (m_vmmaps m) <= L)%Z -> Sys.Mm.Mmap.brk_budget_refused_b m (in_arg i 0) = false -> ca_check arm_brk i eff (relim L m) = map_cr (relim L) (ca_check arm_brk i eff m).
Proof. intros L i eff m HL HB. revert HL. unif_arm_b2 HB.
  all: limnorm.
  all: budget_cases.
  (* any goal left prints its environment in the build log *) all: exact I.
Qed.
Lemma arm_prlimit64_relim : forall L i eff m, ca_check arm_prlimit64 i eff (relim L m) = map_cr (relim L) (ca_check arm_prlimit64 i eff m).
Proof. unif_arm. Qed.
