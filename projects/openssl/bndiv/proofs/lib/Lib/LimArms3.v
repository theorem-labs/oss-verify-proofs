(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import LimBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope sys_scope.

Lemma arm_21 : lim_blind (fun i => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i).
Proof. apply (lim_blind_arm (fun j => epoll_ctl_spec (fd32 (in_arg j 0)) (int32 (in_arg j 1)) (fd32 (in_arg j 2)) (in_arg j 3))). intros j. lim_auto. Qed.

Lemma arm_32 : lim_blind (fun i => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i).
Proof. apply (lim_blind_arm (fun j => flock_spec (fd32 (in_arg j 0)) (cmd32 (in_arg j 1)))). intros j. lim_auto. Qed.

Lemma arm_59 : lim_blind (fun i => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)) i).
Proof. apply (lim_blind_arm (fun j => pipe2_spec (in_arg j 0) (pipe_flags32 (in_arg j 1)))). intros j. lim_auto. Qed.

Lemma arm_66 : lim_blind (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => writev_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_79 : lim_blind (fun i => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i).
Proof. apply (lim_blind_arm (fun j => newfstatat_spec (fd32 (in_arg j 0)) (in_arg j 1) (flag32 (in_arg j 3)))). intros j. lim_auto. Qed.

Lemma arm_94 : lim_blind (fun i => exit_spec (in_arg i 0) i).
Proof. apply (lim_blind_arm (fun j => exit_spec (in_arg j 0))). intros j. lim_auto. Qed.

Lemma arm_123 : lim_blind (fun i => sched_getaffinity_spec (in_arg i 1) i).
Proof. apply (lim_blind_arm (fun j => sched_getaffinity_spec (in_arg j 1))). intros j. lim_auto. Qed.

Lemma arm_135 : lim_blind (fun i => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. apply (lim_blind_arm (fun j => rt_sigprocmask_spec (how32 (in_arg j 0)) (in_arg j 1) (in_arg j 2) (in_arg j 3))). intros j. lim_auto. Qed.

Lemma arm_158 : lim_blind (fun i => getgroups_spec (in_arg i 0) i).
Proof. apply (lim_blind_arm (fun j => getgroups_spec (in_arg j 0))). intros j. lim_auto. Qed.

Lemma arm_174 : lim_blind (fun i => getid_spec cr_uid i).
Proof. apply (lim_blind_arm (fun j => getid_spec cr_uid)). intros j. lim_auto. Qed.

Lemma arm_199 : lim_blind (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. apply (lim_blind_arm (fun j => socketpair_spec (in_arg j 0) (in_arg j 1) (in_arg j 2) (in_arg j 3))). intros j. lim_auto. Qed.

Lemma arm_205 : lim_blind (fun i => getpeername_spec (fd32 (in_arg i 0)) i).
Proof. apply (lim_blind_arm (fun j => getpeername_spec (fd32 (in_arg j 0)))). intros j. lim_auto. Qed.

Lemma arm_211 : lim_blind (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => sendmsg_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_278 : lim_blind (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => getrandom_spec (in_arg j 0) (in_arg j 1) (in_arg j 2))). intros j. lim_auto. Qed.

