(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import LimBase LimMonad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Arms.
Variable L : Z.

(* [comment removed for export] *)
Lemma fr_arm_56 : forall i m, FR L i m (openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold openat_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_57 : forall i m, FR L i m (close_spec (fd32 (in_arg i 0))) (close_spec (fd32 (in_arg i 0))).
Proof. intros i m. unfold close_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_59 : forall i m, FR L i m (pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1))) (pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1))).
Proof. intros i m. unfold pipe2_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_61 : forall i m, FR L i m (getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2)) (getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2)).
Proof. intros i m. unfold getdents64_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_62 : forall i m, FR L i m (lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2))) (lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2))).
Proof. intros i m. unfold lseek_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_63 : forall i m, FR L i m (read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold read_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_64 : forall i m, FR L i m (write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold write_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_65 : forall i m, FR L i m (readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold readv_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_66 : forall i m, FR L i m (writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold writev_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_67 : forall i m, FR L i m (pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof. intros i m. unfold pread64_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_68 : forall i m, FR L i m (pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof. intros i m. unfold pwrite64_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_72 : forall i m, FR L i m (pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)) (pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)).
Proof. intros i m. unfold pselect6_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_73 : forall i m, FR L i m (ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4)) (ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4)).
Proof. intros i m. unfold ppoll_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_78 : forall i m, FR L i m (readlinkat_spec (fd32 (in_arg i 0))) (readlinkat_spec (fd32 (in_arg i 0))).
Proof. intros i m. unfold readlinkat_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_79 : forall i m, FR L i m (newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3))) (newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3))).
Proof. intros i m. unfold newfstatat_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_80 : forall i m, FR L i m (fstat_spec (fd32 (in_arg i 0)) (in_arg i 1)) (fstat_spec (fd32 (in_arg i 0)) (in_arg i 1)).
Proof. intros i m. unfold fstat_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_82 : forall i m, FR L i m (fsync_spec (fd32 (in_arg i 0))) (fsync_spec (fd32 (in_arg i 0))).
Proof. intros i m. unfold fsync_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_83 : forall i m, FR L i m (fsync_spec (fd32 (in_arg i 0))) (fsync_spec (fd32 (in_arg i 0))).
Proof. intros i m. unfold fsync_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_85 : forall i m, FR L i m (timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1))) (timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1))).
Proof. intros i m. unfold timerfd_create_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_93 : forall i m, FR L i m (exit_spec (in_arg i 0)) (exit_spec (in_arg i 0)).
Proof. intros i m. unfold exit_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_94 : forall i m, FR L i m (exit_spec (in_arg i 0)) (exit_spec (in_arg i 0)).
Proof. intros i m. unfold exit_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_96 : forall i m, FR L i m (set_tid_address_spec) (set_tid_address_spec).
Proof. intros i m. unfold set_tid_address_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_98 : forall i m, FR L i m (futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof. intros i m. unfold futex_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_101 : forall i m, FR L i m (nanosleep_spec (in_arg i 0) (in_arg i 1)) (nanosleep_spec (in_arg i 0) (in_arg i 1)).
Proof. intros i m. unfold nanosleep_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_113 : forall i m, FR L i m (clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1)) (clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1)).
Proof. intros i m. unfold clock_gettime_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_119 : forall i m, FR L i m (sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)) (sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold sched_setscheduler_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_123 : forall i m, FR L i m (sched_getaffinity_spec (in_arg i 1)) (sched_getaffinity_spec (in_arg i 1)).
Proof. intros i m. unfold sched_getaffinity_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_124 : forall i m, FR L i m (sched_yield_spec) (sched_yield_spec).
Proof. intros i m. unfold sched_yield_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_130 : forall i m, FR L i m (tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1))) (tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1))).
Proof. intros i m. unfold tkill_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_131 : forall i m, FR L i m (tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2))) (tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2))).
Proof. intros i m. unfold tgkill_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_132 : forall i m, FR L i m (sigaltstack_spec (in_arg i 0) (in_arg i 1)) (sigaltstack_spec (in_arg i 0) (in_arg i 1)).
Proof. intros i m. unfold sigaltstack_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_134 : forall i m, FR L i m (rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof. intros i m. unfold rt_sigaction_spec. fq. Qed.

End Arms.
