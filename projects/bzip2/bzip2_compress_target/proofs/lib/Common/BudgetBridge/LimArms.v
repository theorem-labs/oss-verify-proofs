(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common.BudgetBridge Require Import Relim.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

Ltac arm_start := unfold LI; intros i; cbv beta;
  lazymatch goal with |- forall m o, ?c i m o -> _ => let H := fresh "HLI" in enough (H : LI c) by exact (H i) end.

(* [comment removed for export] *)
Lemma arm_17 : LI (fun i => getcwd_spec (in_arg i 1) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_19 : LI (fun i => eventfd2_spec (flag32 (in_arg i 1)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_20 : LI (fun i => epoll_create1_spec (flag32 (in_arg i 0)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_21 : LI (fun i => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_22 : LI (fun i => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_23 : LI (fun i => dup_spec (fd32 (in_arg i 0)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_24 : LI (fun i => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_25 : LI (fun i => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_29 : LI (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_32 : LI (fun i => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_35 : LI (fun i => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_46 : LI (fun i => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_48 : LI (fun i => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_56 : LI (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_57 : LI (fun i => close_spec (fd32 (in_arg i 0)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_59 : LI (fun i => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_61 : LI (fun i => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_62 : LI (fun i => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_63 : LI (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_64 : LI (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_65 : LI (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_66 : LI (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_67 : LI (fun i => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_68 : LI (fun i => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_72 : LI (fun i => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_73 : LI (fun i => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_78 : LI (fun i => readlinkat_spec (fd32 (in_arg i 0)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_79 : LI (fun i => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_80 : LI (fun i => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_82 : LI (fun i => fsync_spec (fd32 (in_arg i 0)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_83 : LI (fun i => fsync_spec (fd32 (in_arg i 0)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_85 : LI (fun i => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_93 : LI (fun i => exit_spec (in_arg i 0) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_94 : LI (fun i => exit_spec (in_arg i 0) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_96 : LI (fun i => set_tid_address_spec i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_98 : LI (fun i => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_101 : LI (fun i => nanosleep_spec (in_arg i 0) (in_arg i 1) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_113 : LI (fun i => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_119 : LI (fun i => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_123 : LI (fun i => sched_getaffinity_spec (in_arg i 1) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_130 : LI (fun i => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_131 : LI (fun i => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_132 : LI (fun i => sigaltstack_spec (in_arg i 0) (in_arg i 1) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_134 : LI (fun i => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_144 : LI (fun i => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_146 : LI (fun i => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_147 : LI (fun i => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_149 : LI (fun i => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_157 : LI (fun i => setsid_spec i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_158 : LI (fun i => getgroups_spec (in_arg i 0) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_159 : LI (fun i => setgroups_spec i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_160 : LI (fun i => uname_spec (in_arg i 0) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_167 : LI (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_169 : LI (fun i => gettimeofday_spec (in_arg i 0) (in_arg i 1) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_172 : LI (fun i => getpid_spec i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_174 : LI (fun i => getid_spec cr_uid i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_175 : LI (fun i => getid_spec cr_euid i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_176 : LI (fun i => getid_spec cr_gid i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_177 : LI (fun i => getid_spec cr_egid i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_178 : LI (fun i => gettid_spec i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_198 : LI (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_199 : LI (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_200 : LI (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_201 : LI (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_202 : LI (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_203 : LI (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_204 : LI (fun i => getsockname_spec (fd32 (in_arg i 0)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_205 : LI (fun i => getpeername_spec (fd32 (in_arg i 0)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_206 : LI (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_207 : LI (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_208 : LI (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_209 : LI (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_210 : LI (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_211 : LI (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_212 : LI (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_220 : LI (fun i => clone_spec (in_arg i 0) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_242 : LI (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_260 : LI (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_261 : LI (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_278 : LI (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_435 : LI (fun i => clone3_spec (in_arg i 0) (in_arg i 1) i).
Proof. arm_start. li. Qed.

(* [comment removed for export] *)
Lemma arm_439 : LI (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. arm_start. li. Qed.
