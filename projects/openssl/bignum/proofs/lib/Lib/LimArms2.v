(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import LimBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope sys_scope.

Lemma arm_20 : lim_blind (fun i => epoll_create1_spec (flag32 (in_arg i 0)) i).
Proof. apply (lim_blind_arm (fun j => epoll_create1_spec (flag32 (in_arg j 0)))). intros j. lim_auto. Qed.

Lemma arm_29 : lim_blind (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i).
Proof. apply (lim_blind_arm (fun j => ioctl_spec (fd32 (in_arg j 0)) (cmd32 (in_arg j 1)))). intros j. lim_auto. Qed.

Lemma arm_57 : lim_blind (fun i => close_spec (fd32 (in_arg i 0)) i).
Proof. apply (lim_blind_arm (fun j => close_spec (fd32 (in_arg j 0)))). intros j. lim_auto. Qed.

Lemma arm_65 : lim_blind (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => readv_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_78 : lim_blind (fun i => readlinkat_spec (fd32 (in_arg i 0)) i).
Proof. apply (lim_blind_arm (fun j => readlinkat_spec (fd32 (in_arg j 0)))). intros j. lim_auto. Qed.

Lemma arm_93 : lim_blind (fun i => exit_spec (in_arg i 0) i).
Proof. apply (lim_blind_arm (fun j => exit_spec (in_arg j 0))). intros j. lim_auto. Qed.

Lemma arm_119 : lim_blind (fun i => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => sched_setscheduler_spec (in_arg j 0) (in_arg j 1) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_134 : lim_blind (fun i => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. apply (lim_blind_arm (fun j => rt_sigaction_spec (sig32 (in_arg j 0)) (in_arg j 1) (in_arg j 2) (in_arg j 3))). intros j. lim_auto. Qed.

Lemma arm_157 : lim_blind (fun i => setsid_spec i).
Proof. apply (lim_blind_arm (fun j => setsid_spec)). intros j. lim_auto. Qed.

Lemma arm_172 : lim_blind (fun i => getpid_spec i).
Proof. apply (lim_blind_arm (fun j => getpid_spec)). intros j. lim_auto. Qed.

Lemma arm_198 : lim_blind (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => socket_spec (in_arg j 0) (in_arg j 1) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_204 : lim_blind (fun i => getsockname_spec (fd32 (in_arg i 0)) i).
Proof. apply (lim_blind_arm (fun j => getsockname_spec (fd32 (in_arg j 0)))). intros j. lim_auto. Qed.

Lemma arm_210 : lim_blind (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i).
Proof. apply (lim_blind_arm (fun j => shutdown_spec (fd32 (in_arg j 0)) (int32 (in_arg j 1)))). intros j. lim_auto. Qed.

Lemma arm_261 : lim_blind (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. apply (lim_blind_arm (fun j => prlimit64_spec (in_arg j 0) (in_arg j 1) (in_arg j 2) (in_arg j 3))). intros j. lim_auto. Qed.

