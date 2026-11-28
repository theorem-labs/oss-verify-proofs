(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/openssl/bndiv/proofs/lib/Lib/LimArms1.v at commit c395a1e0dfa, whole, with the module path OSSVerify.Proofs.openssl.bndiv.lib.Lib changed to OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts.Lim and nothing else. *)
(* Modified by gabelogan195, 2026-11: copied from projects/skcms/iccprofile_info/proofs/lib/Halts/Lim/LimArms1.v at commit f92feaf8b7, whole, with the module path OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts.Lim changed to OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Halts.Lim and nothing else. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Halts.Lim Require Import LimBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope sys_scope.

Lemma arm_19 : lim_blind (fun i => eventfd2_spec (flag32 (in_arg i 1)) i).
Proof. apply (lim_blind_arm (fun j => eventfd2_spec (flag32 (in_arg j 1)))). intros j. lim_auto. Qed.

Lemma arm_25 : lim_blind (fun i => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => fcntl_spec (fd32 (in_arg j 0)) (cmd32 (in_arg j 1)) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_56 : lim_blind (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => openat_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_64 : lim_blind (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => write_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_73 : lim_blind (fun i => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) i).
Proof. apply (lim_blind_arm (fun j => ppoll_spec (in_arg j 0) (unfds32 (in_arg j 1)) (in_arg j 2) (in_arg j 3) (in_arg j 4))). intros j. lim_auto. Qed.

Lemma arm_85 : lim_blind (fun i => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) i).
Proof. apply (lim_blind_arm (fun j => timerfd_create_spec (clockid32 (in_arg j 0)) (flag32 (in_arg j 1)))). intros j. lim_auto. Qed.

Lemma arm_113 : lim_blind (fun i => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1) i).
Proof. apply (lim_blind_arm (fun j => clock_gettime_spec (clockid32 (in_arg j 0)) (in_arg j 1))). intros j. lim_auto. Qed.

Lemma arm_132 : lim_blind (fun i => sigaltstack_spec (in_arg i 0) (in_arg i 1) i).
Proof. apply (lim_blind_arm (fun j => sigaltstack_spec (in_arg j 0) (in_arg j 1))). intros j. lim_auto. Qed.

Lemma arm_149 : lim_blind (fun i => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i).
Proof. apply (lim_blind_arm (fun j => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg j 0)) (uid32 (in_arg j 1)) (uid32 (in_arg j 2)))). intros j. lim_auto. Qed.

Lemma arm_169 : lim_blind (fun i => gettimeofday_spec (in_arg i 0) (in_arg i 1) i).
Proof. apply (lim_blind_arm (fun j => gettimeofday_spec (in_arg j 0) (in_arg j 1))). intros j. lim_auto. Qed.

Lemma arm_178 : lim_blind (fun i => gettid_spec i).
Proof. apply (lim_blind_arm (fun j => gettid_spec)). intros j. lim_auto. Qed.

Lemma arm_203 : lim_blind (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => connect_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_209 : lim_blind (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i).
Proof. apply (lim_blind_arm (fun j => getsockopt_spec (fd32 (in_arg j 0)) (int32 (in_arg j 1)) (in_arg j 4))). intros j. lim_auto. Qed.

Lemma arm_260 : lim_blind (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i).
Proof. apply (lim_blind_arm (fun j => wait4_spec (pid32 (in_arg j 0)) (in_arg j 1) (waitopts32 (in_arg j 2)) (in_arg j 3))). intros j. lim_auto. Qed.

