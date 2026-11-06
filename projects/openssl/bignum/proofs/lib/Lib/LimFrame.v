(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import VmMapsDisjoint BudgetPremise ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Dispatch.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope sys_scope.

Definition wr_sysno (n : Z) : bool :=
  (n =? 214)%Z || (n =? 215)%Z || (n =? 216)%Z || (n =? 222)%Z || (n =? 226)%Z.

Definition arm_frames_vm (c : CheckedArm) : Prop :=
  wr_sysno (ca_no c) = false ->
  forall i eff m m' evs, ca_check c i eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.

Lemma checked_table_frames_vm : Forall arm_frames_vm checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_frames_vm).
  all: unfold arm_frames_vm; intros Hwr i eff m m' evs H;
       autorewrite with arm_unfold in H; autorewrite with arm_unfold in Hwr.
  all: first
    [ discriminate Hwr
    | eapply check_accept4_frame; eassumption
    | eapply check_bind_frame; eassumption
    | eapply check_clock_gettime_frame; eassumption
    | eapply check_clone3_frame; eassumption
    | eapply check_clone_frame; eassumption
    | eapply check_close_frame; eassumption
    | eapply check_connect_frame; eassumption
    | eapply check_dup3_frame; eassumption
    | eapply check_dup_frame; eassumption
    | eapply check_epoll_create1_frame; eassumption
    | eapply check_epoll_ctl_frame; eassumption
    | eapply check_epoll_pwait_frame; eassumption
    | eapply check_eventfd2_frame; eassumption
    | eapply check_exit_frame; eassumption
    | eapply check_faccessat2_frame; eassumption
    | eapply check_faccessat_frame; eassumption
    | eapply check_fcntl_frame; eassumption
    | eapply check_flock_frame; eassumption
    | eapply check_fstat_frame; eassumption
    | eapply check_fsync_frame; eassumption
    | eapply check_ftruncate_frame; eassumption
    | eapply check_futex_frame; eassumption
    | eapply check_getcwd_frame; eassumption
    | eapply check_getdents64_frame; eassumption
    | eapply check_getgroups_frame; eassumption
    | eapply check_getid_frame; eassumption
    | eapply check_getpeername_frame; eassumption
    | eapply check_getpid_frame; eassumption
    | eapply check_getrandom_frame; eassumption
    | eapply check_getsockname_frame; eassumption
    | eapply check_getsockopt_frame; eassumption
    | eapply check_gettid_frame; eassumption
    | eapply check_gettimeofday_frame; eassumption
    | eapply check_ioctl_frame; eassumption
    | eapply check_listen_frame; eassumption
    | eapply check_lseek_frame; eassumption
    | eapply check_madvise_frame; eassumption
    | eapply check_nanosleep_frame; eassumption
    | eapply check_newfstatat_frame; eassumption
    | eapply check_openat_frame; eassumption
    | eapply check_pipe2_frame; eassumption
    | eapply check_ppoll_frame; eassumption
    | eapply check_prctl_frame; eassumption
    | eapply check_pread64_frame; eassumption
    | eapply check_prlimit64_frame; eassumption
    | eapply check_pselect6_frame; eassumption
    | eapply check_pwrite64_frame; eassumption
    | eapply check_read_frame; eassumption
    | eapply check_readlinkat_frame; eassumption
    | eapply check_readv_frame; eassumption
    | eapply check_recvfrom_frame; eassumption
    | eapply check_recvmsg_frame; eassumption
    | eapply check_rt_sigaction_frame; eassumption
    | eapply check_rt_sigprocmask_frame; eassumption
    | eapply check_sched_getaffinity_frame; eassumption
    | eapply check_sched_setscheduler_frame; eassumption
    | eapply check_sched_yield_frame; eassumption
    | eapply check_sendmsg_frame; eassumption
    | eapply check_sendto_frame; eassumption
    | eapply check_set_tid_address_frame; eassumption
    | eapply check_setgroups_frame; eassumption
    | eapply check_setid_frame; eassumption
    | eapply check_setresid_frame; eassumption
    | eapply check_setsid_frame; eassumption
    | eapply check_setsockopt_frame; eassumption
    | eapply check_shutdown_frame; eassumption
    | eapply check_sigaltstack_frame; eassumption
    | eapply check_socket_frame; eassumption
    | eapply check_socketpair_frame; eassumption
    | eapply check_tgkill_frame; eassumption
    | eapply check_timerfd_create_frame; eassumption
    | eapply check_tkill_frame; eassumption
    | eapply check_uname_frame; eassumption
    | eapply check_unlinkat_frame; eassumption
    | eapply check_wait4_frame; eassumption
    | eapply check_write_frame; eassumption
    | eapply check_writev_frame; eassumption
    | fail 1 "no frame lemma for this arm" ].
Qed.

Theorem syscall_spec_frames_vm : forall i m eff m' evs,
  wr_sysno (bv_unsigned (in_sysno i)) = false ->
  syscall_spec i m (Ok eff m' evs) -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros i m eff m' evs Hwr H. apply check_syscall_ok_iff in H. unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk; [| discriminate H].
  pose proof checked_table_frames_vm as Hall. rewrite Forall_forall in Hall.
  apply (Hall c (lookup_ca_In _ _ _ Elk)) with (i := i) (eff := eff) (evs := evs); [| exact H].
  assert (Hno : ca_no c = bv_unsigned (in_sysno i)).
  { clear - Elk. induction checked_table as [|a t IH]; cbn [lookup_ca] in Elk; [discriminate Elk|].
    destruct (Z.eqb (ca_no a) (bv_unsigned (in_sysno i))) eqn:E.
    - injection Elk as <-. apply Z.eqb_eq. exact E.
    - exact (IH Elk). }
  rewrite Hno. exact Hwr.
Qed.
