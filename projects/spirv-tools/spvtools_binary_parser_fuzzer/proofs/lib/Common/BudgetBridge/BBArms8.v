(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the mmap decline premise place_declined_b). *)
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
(* [Placement.linux_place_is] reads [vm_reserved], [vm_maps],
   [vm_mmap_base] and [vm_init_sp] only, never [vm_limit], so [relim]
   leaves the fresh-grant test alone.  At the revision the mmap checker
   tests it ([Checks/Sys/Mm/Mmap.check_mmap]); [fullunf] does not unfold
   it, so the relim'd and the plain test are made the same one before
   the model is destructed. *)
Lemma lpi_relim : forall L m thp hint nZ x,
  Checks.Placement.linux_place_is (m_vmmaps (relim L m)) thp hint nZ x
  = Checks.Placement.linux_place_is (m_vmmaps m) thp hint nZ x.
Proof. reflexivity. Qed.
(* 727298f3 (#144, #146): [check_mmap] now tests [Mmap.place_declined_b]
   ahead of the [alt] in BOTH placed arms (model Checks/Sys/Mm/Mmap.v:104,
   :135).  It reads [alloc_top] -- so [vm_init_sp] -- [vm_reserved] and
   [vm_maps] off the ledger and the guard gap off the kernel build, and
   never [vm_limit], so [relim] leaves it alone for the same reason
   [lpi_relim] holds.  [fullunf] does not unfold it either, so the relim'd
   and the plain test have to be made the same one before the model is
   destructed. *)
Lemma pdb_relim : forall L m kb hint nZ,
  Sys.Mm.Mmap.place_declined_b kb (m_vmmaps (relim L m)) hint nZ
  = Sys.Mm.Mmap.place_declined_b kb (m_vmmaps m) hint nZ.
Proof. reflexivity. Qed.
Lemma arm_mmap_relim_b : forall L i eff m, (vm_limit (m_vmmaps m) <= L)%Z -> Sys.Mm.Mmap.mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m = false -> ca_check arm_mmap i eff (relim L m) = map_cr (relim L) (ca_check arm_mmap i eff m).
Proof.
  intros L i eff m HL HB. revert HL. revert HB. autorewrite with arm_unfold.
  (* [check_mmap]'s MAP_FIXED|PROT_NONE arm delegates its overflow branch to
     [check_mmap_fixed_overflow] (model Checks/Sys/Mm/Mmap.v:79-88), which
     [fullunf]'s delta list does not carry.  Its result type is [check_result],
     so [dmatch1] refuses it and [dmatch0] sees no match at the head: the
     original side is destructed through [map_cr] (which [fullunf] DOES unfold)
     while the relim side stays an opaque application, and the two can never be
     made equal.  It reads neither [vm_limit] nor any other [m_vmmaps] field -
     it answers [CheckOk m []] or [CheckReject] from [addr], [nZ] and [eff]
     alone, and its one model-touching callee [check_ret_only] is already in
     [fullunf] - so unfolding it here makes both sides decompose over the same
     scrutinees and [unif_fin]'s [reflexivity] closes the branch.  Same repair
     as the earlier one that added [check_unlink_type_result] to [chkunf]. *)
  unfold LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap.check_mmap,
         LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap.check_mmap_fixed_overflow.
  rewrite ?m_kernel_relim, ?lpi_relim, ?pdb_relim.
  destr_model m. fullunf. dmatchB; unif_fin.
  all: limnorm.
  all: budget_cases.
Qed.
Lemma arm_faccessat2_relim : forall L i eff m, ca_check arm_faccessat2 i eff (relim L m) = map_cr (relim L) (ca_check arm_faccessat2 i eff m).
Proof. unif_arm. Qed.
(* At 08b1429 checked_table gained set_robust_list (99), clock_getres (114)
   and pwritev2 (287); none of them reads [vm_limit]
   (recipes/dispatcher-arms.md). *)
Lemma arm_set_robust_list_relim : forall L i eff m, ca_check arm_set_robust_list i eff (relim L m) = map_cr (relim L) (ca_check arm_set_robust_list i eff m).
Proof. unif_arm. Qed.
Lemma arm_clock_getres_relim : forall L i eff m, ca_check arm_clock_getres i eff (relim L m) = map_cr (relim L) (ca_check arm_clock_getres i eff m).
Proof. unif_arm. Qed.
Lemma arm_pwritev2_relim : forall L i eff m, ca_check arm_pwritev2 i eff (relim L m) = map_cr (relim L) (ca_check arm_pwritev2 i eff m).
Proof. unif_arm. Qed.
