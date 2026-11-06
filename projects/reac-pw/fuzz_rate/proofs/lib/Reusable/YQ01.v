(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YQ01.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YQ01.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YQ00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope. Open Scope bv_scope. Open Scope sys_scope.
Set Default Proof Mode "Classic".
Section a.
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
Lemma sim_arm_175 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getid_spec cr_euid i) (fun i => getid_spec cr_euid i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getid_spec cr_euid) (fun i => getid_spec cr_euid)). sim_arm m HM. Qed.
Lemma sim_arm_176 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getid_spec cr_gid i) (fun i => getid_spec cr_gid i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getid_spec cr_gid) (fun i => getid_spec cr_gid)). sim_arm m HM. Qed.
Lemma sim_arm_177 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getid_spec cr_egid i) (fun i => getid_spec cr_egid i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getid_spec cr_egid) (fun i => getid_spec cr_egid)). sim_arm m HM. Qed.
Lemma sim_arm_178 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => gettid_spec i) (fun i => gettid_spec i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => gettid_spec) (fun i => gettid_spec)). sim_arm m HM. Qed.
Lemma sim_arm_198 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i) (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)) (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.
Lemma sim_arm_199 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))). sim_arm m HM. Qed.
Lemma sim_arm_200 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.
Lemma sim_arm_201 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1) i) (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1)) (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1))). sim_arm m HM. Qed.
Lemma sim_arm_202 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i) (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0)) (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0))). sim_arm m HM. Qed.
Lemma sim_arm_203 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.
Lemma sim_arm_204 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getsockname_spec (fd32 (in_arg i 0)) i) (fun i => getsockname_spec (fd32 (in_arg i 0)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getsockname_spec (fd32 (in_arg i 0))) (fun i => getsockname_spec (fd32 (in_arg i 0)))). sim_arm m HM. Qed.
Lemma sim_arm_205 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getpeername_spec (fd32 (in_arg i 0)) i) (fun i => getpeername_spec (fd32 (in_arg i 0)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getpeername_spec (fd32 (in_arg i 0))) (fun i => getpeername_spec (fd32 (in_arg i 0)))). sim_arm m HM. Qed.
Lemma sim_arm_206 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i) (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)) (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))). sim_arm m HM. Qed.
Lemma sim_arm_207 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.
Lemma sim_arm_208 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i) (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4))) (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)))). sim_arm m HM. Qed.
Lemma sim_arm_209 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i) (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4)) (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4))). sim_arm m HM. Qed.
Lemma sim_arm_210 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i) (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1))) (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)))). sim_arm m HM. Qed.
Lemma sim_arm_211 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.
Lemma sim_arm_212 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2) i) (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2)) (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2))). sim_arm m HM. Qed.
Lemma sim_arm_215 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => munmap_spec (in_arg i 0) (in_arg i 1) i) (fun i => munmap_spec (in_arg i 0) (in_arg i 1) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => munmap_spec (in_arg i 0) (in_arg i 1)) (fun i => munmap_spec (in_arg i 0) (in_arg i 1))). sim_arm m HM. Qed.
Lemma sim_arm_220 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => clone_spec (in_arg i 0) i) (fun i => clone_spec (in_arg i 0) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => clone_spec (in_arg i 0)) (fun i => clone_spec (in_arg i 0))). sim_arm m HM. Qed.
Lemma sim_arm_233 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i) (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2))) (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)))). sim_arm m HM. Qed.
Lemma sim_arm_242 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))). sim_arm m HM. Qed.
Lemma sim_arm_260 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i) (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3)) (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3))). sim_arm m HM. Qed.
Lemma sim_arm_261 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))). sim_arm m HM. Qed.
Lemma sim_arm_278 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i) (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)) (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.
Lemma sim_arm_435 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => clone3_spec (in_arg i 0) (in_arg i 1) i) (fun i => clone3_spec (in_arg i 0) (in_arg i 1) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => clone3_spec (in_arg i 0) (in_arg i 1)) (fun i => clone3_spec (in_arg i 0) (in_arg i 1))). sim_arm m HM. Qed.
Lemma sim_arm_439 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))). sim_arm m HM. Qed.
End a.
