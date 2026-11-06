(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import LimBase LimMonad LimFitBase LimFitVm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma pr_arm_17 : forall i m, PR i m (getcwd_spec (in_arg i 1)).
Proof. intros i m. unfold getcwd_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_19 : forall i m, PR i m (eventfd2_spec (flag32 (in_arg i 1))).
Proof. intros i m. unfold eventfd2_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_20 : forall i m, PR i m (epoll_create1_spec (flag32 (in_arg i 0))).
Proof. intros i m. unfold epoll_create1_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_21 : forall i m, PR i m (epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3)).
Proof. intros i m. unfold epoll_ctl_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_22 : forall i m, PR i m (epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5)).
Proof. intros i m. unfold epoll_pwait_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_23 : forall i m, PR i m (dup_spec (fd32 (in_arg i 0))).
Proof. intros i m. unfold dup_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_24 : forall i m, PR i m (dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2)).
Proof. intros i m. unfold dup3_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_25 : forall i m, PR i m (fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2)).
Proof. intros i m. unfold fcntl_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_29 : forall i m, PR i m (ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1))).
Proof. intros i m. unfold ioctl_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_32 : forall i m, PR i m (flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1))).
Proof. intros i m. unfold flock_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_35 : forall i m, PR i m (unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold unlinkat_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_46 : forall i m, PR i m (ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1)).
Proof. intros i m. unfold ftruncate_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_48 : forall i m, PR i m (faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold faccessat_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_56 : forall i m, PR i m (openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold openat_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_57 : forall i m, PR i m (close_spec (fd32 (in_arg i 0))).
Proof. intros i m. unfold close_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_59 : forall i m, PR i m (pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1))).
Proof. intros i m. unfold pipe2_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_61 : forall i m, PR i m (getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2)).
Proof. intros i m. unfold getdents64_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_62 : forall i m, PR i m (lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2))).
Proof. intros i m. unfold lseek_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_63 : forall i m, PR i m (read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold read_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_64 : forall i m, PR i m (write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold write_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_65 : forall i m, PR i m (readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold readv_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_66 : forall i m, PR i m (writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold writev_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_67 : forall i m, PR i m (pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof. intros i m. unfold pread64_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_68 : forall i m, PR i m (pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof. intros i m. unfold pwrite64_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_72 : forall i m, PR i m (pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)).
Proof. intros i m. unfold pselect6_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_73 : forall i m, PR i m (ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4)).
Proof. intros i m. unfold ppoll_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_78 : forall i m, PR i m (readlinkat_spec (fd32 (in_arg i 0))).
Proof. intros i m. unfold readlinkat_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_79 : forall i m, PR i m (newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3))).
Proof. intros i m. unfold newfstatat_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_80 : forall i m, PR i m (fstat_spec (fd32 (in_arg i 0)) (in_arg i 1)).
Proof. intros i m. unfold fstat_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_82 : forall i m, PR i m (fsync_spec (fd32 (in_arg i 0))).
Proof. intros i m. unfold fsync_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_83 : forall i m, PR i m (fsync_spec (fd32 (in_arg i 0))).
Proof. intros i m. unfold fsync_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_85 : forall i m, PR i m (timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1))).
Proof. intros i m. unfold timerfd_create_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_93 : forall i m, PR i m (exit_spec (in_arg i 0)).
Proof. intros i m. unfold exit_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_94 : forall i m, PR i m (exit_spec (in_arg i 0)).
Proof. intros i m. unfold exit_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_96 : forall i m, PR i m (set_tid_address_spec).
Proof. intros i m. unfold set_tid_address_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_98 : forall i m, PR i m (futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof. intros i m. unfold futex_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_101 : forall i m, PR i m (nanosleep_spec (in_arg i 0) (in_arg i 1)).
Proof. intros i m. unfold nanosleep_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_113 : forall i m, PR i m (clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1)).
Proof. intros i m. unfold clock_gettime_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_119 : forall i m, PR i m (sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold sched_setscheduler_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_123 : forall i m, PR i m (sched_getaffinity_spec (in_arg i 1)).
Proof. intros i m. unfold sched_getaffinity_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_124 : forall i m, PR i m (sched_yield_spec).
Proof. intros i m. unfold sched_yield_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_130 : forall i m, PR i m (tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1))).
Proof. intros i m. unfold tkill_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_131 : forall i m, PR i m (tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2))).
Proof. intros i m. unfold tgkill_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_132 : forall i m, PR i m (sigaltstack_spec (in_arg i 0) (in_arg i 1)).
Proof. intros i m. unfold sigaltstack_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_134 : forall i m, PR i m (rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof. intros i m. unfold rt_sigaction_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_144 : forall i m, PR i m (setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0))).
Proof. intros i m. unfold setid_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_146 : forall i m, PR i m (setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0))).
Proof. intros i m. unfold setid_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_147 : forall i m, PR i m (setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2))).
Proof. intros i m. unfold setresid_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_149 : forall i m, PR i m (setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2))).
Proof. intros i m. unfold setresid_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_157 : forall i m, PR i m (setsid_spec).
Proof. intros i m. unfold setsid_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_158 : forall i m, PR i m (getgroups_spec (in_arg i 0)).
Proof. intros i m. unfold getgroups_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_159 : forall i m, PR i m (setgroups_spec).
Proof. intros i m. unfold setgroups_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_160 : forall i m, PR i m (uname_spec (in_arg i 0)).
Proof. intros i m. unfold uname_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_167 : forall i m, PR i m (prctl_spec (int32 (in_arg i 0)) (in_arg i 1)).
Proof. intros i m. unfold prctl_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_169 : forall i m, PR i m (gettimeofday_spec (in_arg i 0) (in_arg i 1)).
Proof. intros i m. unfold gettimeofday_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_172 : forall i m, PR i m (getpid_spec).
Proof. intros i m. unfold getpid_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_174 : forall i m, PR i m (getid_spec cr_uid).
Proof. intros i m. unfold getid_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_175 : forall i m, PR i m (getid_spec cr_euid).
Proof. intros i m. unfold getid_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_176 : forall i m, PR i m (getid_spec cr_gid).
Proof. intros i m. unfold getid_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_177 : forall i m, PR i m (getid_spec cr_egid).
Proof. intros i m. unfold getid_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_178 : forall i m, PR i m (gettid_spec).
Proof. intros i m. unfold gettid_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_198 : forall i m, PR i m (socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold socket_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_199 : forall i m, PR i m (socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof. intros i m. unfold socketpair_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_200 : forall i m, PR i m (bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold bind_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_201 : forall i m, PR i m (listen_spec (fd32 (in_arg i 0)) (in_arg i 1)).
Proof. intros i m. unfold listen_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_202 : forall i m, PR i m (accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0)).
Proof. intros i m. unfold accept4_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_203 : forall i m, PR i m (connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold connect_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_204 : forall i m, PR i m (getsockname_spec (fd32 (in_arg i 0))).
Proof. intros i m. unfold getsockname_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_205 : forall i m, PR i m (getpeername_spec (fd32 (in_arg i 0))).
Proof. intros i m. unfold getpeername_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_206 : forall i m, PR i m (sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)).
Proof. intros i m. unfold sendto_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_207 : forall i m, PR i m (recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold recvfrom_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_208 : forall i m, PR i m (setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4))).
Proof. intros i m. unfold setsockopt_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_209 : forall i m, PR i m (getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4)).
Proof. intros i m. unfold getsockopt_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_210 : forall i m, PR i m (shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1))).
Proof. intros i m. unfold shutdown_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_211 : forall i m, PR i m (sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold sendmsg_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_212 : forall i m, PR i m (recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2)).
Proof. intros i m. unfold recvmsg_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_220 : forall i m, PR i m (clone_spec (in_arg i 0)).
Proof. intros i m. unfold clone_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_242 : forall i m, PR i m (accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof. intros i m. unfold accept4_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_260 : forall i m, PR i m (wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3)).
Proof. intros i m. unfold wait4_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_261 : forall i m, PR i m (prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof. intros i m. unfold prlimit64_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_278 : forall i m, PR i m (getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold getrandom_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_435 : forall i m, PR i m (clone3_spec (in_arg i 0) (in_arg i 1)).
Proof. intros i m. unfold clone3_spec. pr. Qed.

(* [comment removed for export] *)
Lemma pr_arm_439 : forall i m, PR i m (faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof. intros i m. unfold faccessat2_spec. pr. Qed.

Definition arm_fits (a : SpecArm) : Prop := forall i m, PR i m (sa_spec a).

Lemma PR_eta {A} : forall i m (c : SyscallInput -> Sys A),
  PR i m (c i) -> PR i m (fun i0 => c i0 i0).
Proof. intros i m c H. exact H. Qed.

Lemma lookup_arm_in : forall t n a, lookup_arm t n = Some a -> In a t.
Proof.
  induction t as [| b r IH]; intros n a H; cbn [lookup_arm] in H; [discriminate |].
  destruct (Z.eqb (sa_no b) n).
  - injection H as <-. left. reflexivity.
  - right. exact (IH n a H).
Qed.

Lemma spec_table_fits : Forall arm_fits spec_table.
Proof.
  unfold spec_table.
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => getcwd_spec (in_arg i 1))); cbv beta.
    exact (pr_arm_17 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => eventfd2_spec (flag32 (in_arg i 1)))); cbv beta.
    exact (pr_arm_19 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => epoll_create1_spec (flag32 (in_arg i 0)))); cbv beta.
    exact (pr_arm_20 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3))); cbv beta.
    exact (pr_arm_21 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5))); cbv beta.
    exact (pr_arm_22 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => dup_spec (fd32 (in_arg i 0)))); cbv beta.
    exact (pr_arm_23 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2))); cbv beta.
    exact (pr_arm_24 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2))); cbv beta.
    exact (pr_arm_25 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)))); cbv beta.
    exact (pr_arm_29 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)))); cbv beta.
    exact (pr_arm_32 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (pr_arm_35 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1))); cbv beta.
    exact (pr_arm_46 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (pr_arm_48 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (pr_arm_56 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => close_spec (fd32 (in_arg i 0)))); cbv beta.
    exact (pr_arm_57 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)))); cbv beta.
    exact (pr_arm_59 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2))); cbv beta.
    exact (pr_arm_61 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)))); cbv beta.
    exact (pr_arm_62 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (pr_arm_63 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (pr_arm_64 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (pr_arm_65 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (pr_arm_66 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    exact (pr_arm_67 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    exact (pr_arm_68 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))); cbv beta.
    exact (pr_arm_72 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4))); cbv beta.
    exact (pr_arm_73 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => readlinkat_spec (fd32 (in_arg i 0)))); cbv beta.
    exact (pr_arm_78 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)))); cbv beta.
    exact (pr_arm_79 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1))); cbv beta.
    exact (pr_arm_80 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => fsync_spec (fd32 (in_arg i 0)))); cbv beta.
    exact (pr_arm_82 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => fsync_spec (fd32 (in_arg i 0)))); cbv beta.
    exact (pr_arm_83 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)))); cbv beta.
    exact (pr_arm_85 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => exit_spec (in_arg i 0))); cbv beta.
    exact (pr_arm_93 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => exit_spec (in_arg i 0))); cbv beta.
    exact (pr_arm_94 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => set_tid_address_spec)); cbv beta.
    exact (pr_arm_96 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    exact (pr_arm_98 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => nanosleep_spec (in_arg i 0) (in_arg i 1))); cbv beta.
    exact (pr_arm_101 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1))); cbv beta.
    exact (pr_arm_113 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (pr_arm_119 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => sched_getaffinity_spec (in_arg i 1))); cbv beta.
    exact (pr_arm_123 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => sched_yield_spec)); cbv beta.
    exact (pr_arm_124 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)))); cbv beta.
    exact (pr_arm_130 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)))); cbv beta.
    exact (pr_arm_131 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => sigaltstack_spec (in_arg i 0) (in_arg i 1))); cbv beta.
    exact (pr_arm_132 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    exact (pr_arm_134 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    apply pr_rt_sigprocmask. }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)))); cbv beta.
    exact (pr_arm_144 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)))); cbv beta.
    exact (pr_arm_146 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)))); cbv beta.
    exact (pr_arm_147 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)))); cbv beta.
    exact (pr_arm_149 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => setsid_spec)); cbv beta.
    exact (pr_arm_157 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => getgroups_spec (in_arg i 0))); cbv beta.
    exact (pr_arm_158 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => setgroups_spec)); cbv beta.
    exact (pr_arm_159 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => uname_spec (in_arg i 0))); cbv beta.
    exact (pr_arm_160 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1))); cbv beta.
    exact (pr_arm_167 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => gettimeofday_spec (in_arg i 0) (in_arg i 1))); cbv beta.
    exact (pr_arm_169 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => getpid_spec)); cbv beta.
    exact (pr_arm_172 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => getid_spec cr_uid)); cbv beta.
    exact (pr_arm_174 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => getid_spec cr_euid)); cbv beta.
    exact (pr_arm_175 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => getid_spec cr_gid)); cbv beta.
    exact (pr_arm_176 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => getid_spec cr_egid)); cbv beta.
    exact (pr_arm_177 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => gettid_spec)); cbv beta.
    exact (pr_arm_178 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (pr_arm_198 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    exact (pr_arm_199 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (pr_arm_200 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1))); cbv beta.
    exact (pr_arm_201 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0))); cbv beta.
    exact (pr_arm_202 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (pr_arm_203 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => getsockname_spec (fd32 (in_arg i 0)))); cbv beta.
    exact (pr_arm_204 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => getpeername_spec (fd32 (in_arg i 0)))); cbv beta.
    exact (pr_arm_205 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))); cbv beta.
    exact (pr_arm_206 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (pr_arm_207 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)))); cbv beta.
    exact (pr_arm_208 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4))); cbv beta.
    exact (pr_arm_209 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)))); cbv beta.
    exact (pr_arm_210 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (pr_arm_211 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2))); cbv beta.
    exact (pr_arm_212 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => brk_spec (in_arg i 0))); cbv beta.
    apply pr_brk. }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => munmap_spec (in_arg i 0) (in_arg i 1))); cbv beta.
    apply pr_munmap. }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    apply pr_mremap. }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => clone_spec (in_arg i 0))); cbv beta.
    exact (pr_arm_220 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))); cbv beta.
    apply pr_mmap. }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))); cbv beta.
    apply pr_mprotect. }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)))); cbv beta.
    apply pr_madvise. }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    exact (pr_arm_242 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3))); cbv beta.
    exact (pr_arm_260 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    exact (pr_arm_261 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))); cbv beta.
    exact (pr_arm_278 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => clone3_spec (in_arg i 0) (in_arg i 1))); cbv beta.
    exact (pr_arm_435 i m). }
  (* [comment removed for export] *)
  apply Forall_cons.
  { intros i m. cbn [sa_spec]. apply (PR_eta i m (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))); cbv beta.
    exact (pr_arm_439 i m). }
  apply Forall_nil.
Qed.

Theorem syscall_spec_fits : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) -> fits m -> fits m'.
Proof.
  intros i m eff m' evs H. unfold syscall_spec, dispatch in H.
  destruct (lookup_arm spec_table (bv_unsigned (in_sysno i))) as [a |] eqn:E.
  - exact (proj1 (Forall_forall _ _) spec_table_fits a (lookup_arm_in _ _ _ E) i m eff m' evs H).
  - discriminate H.
Qed.

(* [comment removed for export] *)
Lemma init_model_fits : forall reserved brk0 mbase sp lim inp,
  fits (init_model reserved brk0 mbase sp lim inp).
Proof. intros. unfold fits. apply Forall_nil. Qed.
