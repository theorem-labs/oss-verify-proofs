(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import LimBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope sys_scope.

Lemma arm_22 : lim_blind (fun i => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i).
Proof. apply (lim_blind_arm (fun j => epoll_pwait_spec (fd32 (in_arg j 0)) (in_arg j 1) (int32 (in_arg j 2)) (in_arg j 4) (in_arg j 5))). intros j. lim_auto. Qed.

Lemma arm_35 : lim_blind (fun i => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => unlinkat_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_61 : lim_blind (fun i => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => getdents64_spec (fd32 (in_arg j 0)) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_67 : lim_blind (fun i => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. apply (lim_blind_arm (fun j => pread64_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2) (in_arg j 3))). intros j. lim_auto. Qed.

Lemma arm_80 : lim_blind (fun i => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1) i).
Proof. apply (lim_blind_arm (fun j => fstat_spec (fd32 (in_arg j 0)) (in_arg j 1))). intros j. lim_auto. Qed.

Lemma arm_96 : lim_blind (fun i => set_tid_address_spec i).
Proof. apply (lim_blind_arm (fun j => set_tid_address_spec)). intros j. lim_auto. Qed.

Lemma arm_124 : lim_blind (fun i => sched_yield_spec i).
Proof. apply (lim_blind_arm (fun j => sched_yield_spec)). intros j. lim_auto. Qed.

Lemma arm_144 : lim_blind (fun i => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) i).
Proof. apply (lim_blind_arm (fun j => setid_spec cred_gids set_cred_gids false (uid32 (in_arg j 0)))). intros j. lim_auto. Qed.

Lemma arm_159 : lim_blind (fun i => setgroups_spec i).
Proof. apply (lim_blind_arm (fun j => setgroups_spec)). intros j. lim_auto. Qed.

Lemma arm_175 : lim_blind (fun i => getid_spec cr_euid i).
Proof. apply (lim_blind_arm (fun j => getid_spec cr_euid)). intros j. lim_auto. Qed.

Lemma arm_200 : lim_blind (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => bind_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_206 : lim_blind (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i).
Proof. apply (lim_blind_arm (fun j => sendto_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2) (in_arg j 3) (in_arg j 4) (in_arg j 5))). intros j. lim_auto. Qed.

Lemma arm_212 : lim_blind (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => recvmsg_spec (fd32 (in_arg j 0)) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_435 : lim_blind (fun i => clone3_spec (in_arg i 0) (in_arg i 1) i).
Proof. apply (lim_blind_arm (fun j => clone3_spec (in_arg j 0) (in_arg j 1))). intros j. lim_auto. Qed.

