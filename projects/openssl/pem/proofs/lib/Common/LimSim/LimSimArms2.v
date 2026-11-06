(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From OSSVerify.Proofs.openssl.pem.lib.Common.LimSim Require Import LimSim.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope. Open Scope bv_scope. Open Scope sys_scope.
Set Default Proof Mode "Classic".

Section Arms.
Variable L0 L : Z.

Lemma sim_arm_82 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => fsync_spec (fd32 (in_arg i 0)) i) (fun i => fsync_spec (fd32 (in_arg i 0)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => fsync_spec (fd32 (in_arg i 0))) (fun i => fsync_spec (fd32 (in_arg i 0)))). sim_arm m HM. Qed.

Lemma sim_arm_83 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => fsync_spec (fd32 (in_arg i 0)) i) (fun i => fsync_spec (fd32 (in_arg i 0)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => fsync_spec (fd32 (in_arg i 0))) (fun i => fsync_spec (fd32 (in_arg i 0)))). sim_arm m HM. Qed.

Lemma sim_arm_85 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) i) (fun i => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1))) (fun i => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)))). sim_arm m HM. Qed.

Lemma sim_arm_93 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => exit_spec (in_arg i 0) i) (fun i => exit_spec (in_arg i 0) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => exit_spec (in_arg i 0)) (fun i => exit_spec (in_arg i 0))). sim_arm m HM. Qed.

Lemma sim_arm_94 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => exit_spec (in_arg i 0) i) (fun i => exit_spec (in_arg i 0) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => exit_spec (in_arg i 0)) (fun i => exit_spec (in_arg i 0))). sim_arm m HM. Qed.

Lemma sim_arm_96 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => set_tid_address_spec i) (fun i => set_tid_address_spec i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => set_tid_address_spec) (fun i => set_tid_address_spec)). sim_arm m HM. Qed.

Lemma sim_arm_98 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) (fun i => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (fun i => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))). sim_arm m HM. Qed.

Lemma sim_arm_101 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => nanosleep_spec (in_arg i 0) (in_arg i 1) i) (fun i => nanosleep_spec (in_arg i 0) (in_arg i 1) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => nanosleep_spec (in_arg i 0) (in_arg i 1)) (fun i => nanosleep_spec (in_arg i 0) (in_arg i 1))). sim_arm m HM. Qed.

Lemma sim_arm_113 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1) i) (fun i => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1)) (fun i => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1))). sim_arm m HM. Qed.

Lemma sim_arm_119 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i) (fun i => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)) (fun i => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_123 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => sched_getaffinity_spec (in_arg i 1) i) (fun i => sched_getaffinity_spec (in_arg i 1) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => sched_getaffinity_spec (in_arg i 1)) (fun i => sched_getaffinity_spec (in_arg i 1))). sim_arm m HM. Qed.

Lemma sim_arm_124 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => sched_yield_spec i) (fun i => sched_yield_spec i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => sched_yield_spec) (fun i => sched_yield_spec)). sim_arm m HM. Qed.

Lemma sim_arm_130 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) i) (fun i => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1))) (fun i => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)))). sim_arm m HM. Qed.

Lemma sim_arm_131 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) i) (fun i => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2))) (fun i => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)))). sim_arm m HM. Qed.

Lemma sim_arm_132 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => sigaltstack_spec (in_arg i 0) (in_arg i 1) i) (fun i => sigaltstack_spec (in_arg i 0) (in_arg i 1) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => sigaltstack_spec (in_arg i 0) (in_arg i 1)) (fun i => sigaltstack_spec (in_arg i 0) (in_arg i 1))). sim_arm m HM. Qed.

Lemma sim_arm_134 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) (fun i => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (fun i => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))). sim_arm m HM. Qed.

Lemma sim_arm_135 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) (fun i => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (fun i => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))). sim_arm m HM. Qed.

Lemma sim_arm_144 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) i) (fun i => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0))) (fun i => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)))). sim_arm m HM. Qed.

Lemma sim_arm_146 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) i) (fun i => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0))) (fun i => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)))). sim_arm m HM. Qed.

Lemma sim_arm_147 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i) (fun i => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2))) (fun i => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)))). sim_arm m HM. Qed.

Lemma sim_arm_149 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i) (fun i => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2))) (fun i => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)))). sim_arm m HM. Qed.

Lemma sim_arm_157 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => setsid_spec i) (fun i => setsid_spec i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => setsid_spec) (fun i => setsid_spec)). sim_arm m HM. Qed.

Lemma sim_arm_158 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getgroups_spec (in_arg i 0) i) (fun i => getgroups_spec (in_arg i 0) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getgroups_spec (in_arg i 0)) (fun i => getgroups_spec (in_arg i 0))). sim_arm m HM. Qed.

Lemma sim_arm_159 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => setgroups_spec i) (fun i => setgroups_spec i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => setgroups_spec) (fun i => setgroups_spec)). sim_arm m HM. Qed.

Lemma sim_arm_160 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => uname_spec (in_arg i 0) i) (fun i => uname_spec (in_arg i 0) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => uname_spec (in_arg i 0)) (fun i => uname_spec (in_arg i 0))). sim_arm m HM. Qed.

Lemma sim_arm_167 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1) i) (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1)) (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1))). sim_arm m HM. Qed.

Lemma sim_arm_169 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => gettimeofday_spec (in_arg i 0) (in_arg i 1) i) (fun i => gettimeofday_spec (in_arg i 0) (in_arg i 1) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => gettimeofday_spec (in_arg i 0) (in_arg i 1)) (fun i => gettimeofday_spec (in_arg i 0) (in_arg i 1))). sim_arm m HM. Qed.

Lemma sim_arm_172 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getpid_spec i) (fun i => getpid_spec i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getpid_spec) (fun i => getpid_spec)). sim_arm m HM. Qed.

Lemma sim_arm_174 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getid_spec cr_uid i) (fun i => getid_spec cr_uid i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getid_spec cr_uid) (fun i => getid_spec cr_uid)). sim_arm m HM. Qed.

End Arms.
