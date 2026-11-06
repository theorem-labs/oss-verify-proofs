(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From OSSVerify.Proofs.openssl.punycode.lib.Common.LimSim Require Import LimSim.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope. Open Scope bv_scope. Open Scope sys_scope.
Set Default Proof Mode "Classic".

Section Arms.
Variable L0 L : Z.

Lemma sim_arm_17 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getcwd_spec (in_arg i 1) i) (fun i => getcwd_spec (in_arg i 1) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getcwd_spec (in_arg i 1)) (fun i => getcwd_spec (in_arg i 1))). sim_arm m HM. Qed.

Lemma sim_arm_19 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => eventfd2_spec (flag32 (in_arg i 1)) i) (fun i => eventfd2_spec (flag32 (in_arg i 1)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => eventfd2_spec (flag32 (in_arg i 1))) (fun i => eventfd2_spec (flag32 (in_arg i 1)))). sim_arm m HM. Qed.

Lemma sim_arm_20 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => epoll_create1_spec (flag32 (in_arg i 0)) i) (fun i => epoll_create1_spec (flag32 (in_arg i 0)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => epoll_create1_spec (flag32 (in_arg i 0))) (fun i => epoll_create1_spec (flag32 (in_arg i 0)))). sim_arm m HM. Qed.

Lemma sim_arm_21 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i) (fun i => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3)) (fun i => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3))). sim_arm m HM. Qed.

Lemma sim_arm_22 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i) (fun i => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5)) (fun i => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5))). sim_arm m HM. Qed.

Lemma sim_arm_23 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => dup_spec (fd32 (in_arg i 0)) i) (fun i => dup_spec (fd32 (in_arg i 0)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => dup_spec (fd32 (in_arg i 0))) (fun i => dup_spec (fd32 (in_arg i 0)))). sim_arm m HM. Qed.

Lemma sim_arm_24 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) i) (fun i => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2)) (fun i => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_25 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i) (fun i => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2)) (fun i => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_29 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i) (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1))) (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)))). sim_arm m HM. Qed.

Lemma sim_arm_32 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i) (fun i => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1))) (fun i => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)))). sim_arm m HM. Qed.

Lemma sim_arm_35 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) (fun i => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (fun i => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_46 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1) i) (fun i => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1)) (fun i => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1))). sim_arm m HM. Qed.

Lemma sim_arm_48 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) (fun i => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (fun i => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_56 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_57 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => close_spec (fd32 (in_arg i 0)) i) (fun i => close_spec (fd32 (in_arg i 0)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => close_spec (fd32 (in_arg i 0))) (fun i => close_spec (fd32 (in_arg i 0)))). sim_arm m HM. Qed.

Lemma sim_arm_59 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)) i) (fun i => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1))) (fun i => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)))). sim_arm m HM. Qed.

Lemma sim_arm_61 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i) (fun i => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2)) (fun i => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_62 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i) (fun i => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2))) (fun i => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)))). sim_arm m HM. Qed.

Lemma sim_arm_63 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_64 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_65 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_66 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_67 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) (fun i => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (fun i => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))). sim_arm m HM. Qed.

Lemma sim_arm_68 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) (fun i => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (fun i => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))). sim_arm m HM. Qed.

Lemma sim_arm_72 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i) (fun i => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)) (fun i => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))). sim_arm m HM. Qed.

Lemma sim_arm_73 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) i) (fun i => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4)) (fun i => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4))). sim_arm m HM. Qed.

Lemma sim_arm_78 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => readlinkat_spec (fd32 (in_arg i 0)) i) (fun i => readlinkat_spec (fd32 (in_arg i 0)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => readlinkat_spec (fd32 (in_arg i 0))) (fun i => readlinkat_spec (fd32 (in_arg i 0)))). sim_arm m HM. Qed.

Lemma sim_arm_79 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i) (fun i => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3))) (fun i => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)))). sim_arm m HM. Qed.

Lemma sim_arm_80 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1) i) (fun i => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1)) (fun i => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1))). sim_arm m HM. Qed.

End Arms.
