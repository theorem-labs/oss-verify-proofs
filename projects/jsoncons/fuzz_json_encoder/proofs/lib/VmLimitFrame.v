(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs VmMapsDisjoint.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition arm_preserves_limit (c : CheckedArm) : Prop :=
  forall i eff m m' evs,
    ca_check c i eff m = CheckOk m' evs ->
    vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).

(* [comment removed for export] *)
Ltac lim_close :=
  rewrite ?vmm_brk_next, ?vmm_forget_ranges, ?vmm_mmap_replacement, ?vmm_mmap_backing,
          ?vmm_mmap_destroyed, ?vmm_mremap_next, ?vmm_resize_backing, ?vmm_vmmaps;
  reflexivity.

Ltac lim_arm H := repeat vm_step H; lim_close.

Lemma check_brk_limit : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs ->
  vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
Proof. intros req eff m m' evs H. unfold check_brk in H. lim_arm H. Qed.

Lemma check_munmap_limit : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs ->
  vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
Proof. intros addr len eff m m' evs H. unfold check_munmap in H. cbv zeta in H. lim_arm H. Qed.

Lemma check_mprotect_limit : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs ->
  vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
Proof. intros addr len prot eff m m' evs H. unfold check_mprotect in H. cbv zeta in H. lim_arm H. Qed.

Lemma check_mmap_limit : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
Proof.
  intros addr len prot flags fd off eff m m' evs H. unfold check_mmap in H. cbv zeta in H. lim_arm H.
Qed.

Lemma check_mremap_limit : forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs ->
  vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
Proof.
  intros old old_size new_size flags eff m m' evs H. unfold check_mremap in H. cbv zeta in H. lim_arm H.
Qed.

(* [comment removed for export] *)
Lemma checked_table_preserves_limit : Forall arm_preserves_limit checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_preserves_limit).
  all: unfold arm_preserves_limit; intros i eff m m' evs H;
       autorewrite with arm_unfold in H.
  all: first
    [ eapply check_brk_limit; eassumption
    | eapply check_mmap_limit; eassumption
    | eapply check_munmap_limit; eassumption
    | eapply check_mremap_limit; eassumption
    | eapply check_mprotect_limit; eassumption
    | erewrite check_madvise_frame by eassumption; reflexivity
    | erewrite check_read_frame by eassumption; reflexivity
    | erewrite check_write_frame by eassumption; reflexivity
    | erewrite check_pread64_frame by eassumption; reflexivity
    | erewrite check_pwrite64_frame by eassumption; reflexivity
    | erewrite check_readv_frame by eassumption; reflexivity
    | erewrite check_writev_frame by eassumption; reflexivity
    | erewrite check_openat_frame by eassumption; reflexivity
    | erewrite check_close_frame by eassumption; reflexivity
    | erewrite check_lseek_frame by eassumption; reflexivity
    | erewrite check_ftruncate_frame by eassumption; reflexivity
    | erewrite check_ioctl_frame by eassumption; reflexivity
    | erewrite check_readlinkat_frame by eassumption; reflexivity
    | erewrite check_wait4_frame by eassumption; reflexivity
    | erewrite check_fsync_frame by eassumption; reflexivity
    | erewrite check_getdents64_frame by eassumption; reflexivity
    | erewrite check_flock_frame by eassumption; reflexivity
    | erewrite check_exit_frame by eassumption; reflexivity
    | erewrite check_set_tid_address_frame by eassumption; reflexivity
    | erewrite check_getpid_frame by eassumption; reflexivity
    | erewrite check_gettid_frame by eassumption; reflexivity
    | erewrite check_setsid_frame by eassumption; reflexivity
    | erewrite check_uname_frame by eassumption; reflexivity
    | erewrite check_prctl_frame by eassumption; reflexivity
    | erewrite check_prlimit64_frame by eassumption; reflexivity
    | erewrite check_getrandom_frame by eassumption; reflexivity
    | erewrite check_gettimeofday_frame by eassumption; reflexivity
    | erewrite check_clock_gettime_frame by eassumption; reflexivity
    | erewrite check_nanosleep_frame by eassumption; reflexivity
    | erewrite check_dup_frame by eassumption; reflexivity
    | erewrite check_dup3_frame by eassumption; reflexivity
    | erewrite check_unlinkat_frame by eassumption; reflexivity
    | erewrite check_faccessat_frame by eassumption; reflexivity
    | erewrite check_faccessat2_frame by eassumption; reflexivity
    | erewrite check_pselect6_frame by eassumption; reflexivity
    | erewrite check_ppoll_frame by eassumption; reflexivity
    | erewrite check_newfstatat_frame by eassumption; reflexivity
    | erewrite check_fstat_frame by eassumption; reflexivity
    | erewrite check_getid_frame by eassumption; reflexivity
    | erewrite check_setid_frame by eassumption; reflexivity
    | erewrite check_setresid_frame by eassumption; reflexivity
    | erewrite check_getgroups_frame by eassumption; reflexivity
    | erewrite check_setgroups_frame by eassumption; reflexivity
    | erewrite check_socket_frame by eassumption; reflexivity
    | erewrite check_bind_frame by eassumption; reflexivity
    | erewrite check_listen_frame by eassumption; reflexivity
    | erewrite check_accept4_frame by eassumption; reflexivity
    | erewrite check_fcntl_frame by eassumption; reflexivity
    | erewrite check_sched_setscheduler_frame by eassumption; reflexivity
    | erewrite check_sched_getaffinity_frame by eassumption; reflexivity
    | erewrite check_sched_yield_frame by eassumption; reflexivity          (* [comment removed for export] *)
    | erewrite check_sigaltstack_frame by eassumption; reflexivity
    | erewrite check_rt_sigaction_frame by eassumption; reflexivity
    | erewrite check_tkill_frame by eassumption; reflexivity
    | erewrite check_tgkill_frame by eassumption; reflexivity
    | erewrite check_rt_sigprocmask_frame by eassumption; reflexivity
    | erewrite check_futex_frame by eassumption; reflexivity
    | erewrite check_clone_frame by eassumption; reflexivity
    | erewrite check_clone3_frame by eassumption; reflexivity
    | erewrite check_getsockname_frame by eassumption; reflexivity
    | erewrite check_getpeername_frame by eassumption; reflexivity
    | erewrite check_setsockopt_frame by eassumption; reflexivity
    | erewrite check_getsockopt_frame by eassumption; reflexivity
    | erewrite check_shutdown_frame by eassumption; reflexivity
    | erewrite check_sendto_frame by eassumption; reflexivity
    | erewrite check_sendmsg_frame by eassumption; reflexivity
    | erewrite check_socketpair_frame by eassumption; reflexivity
    | erewrite check_recvfrom_frame by eassumption; reflexivity
    | erewrite check_recvmsg_frame by eassumption; reflexivity
    | erewrite check_connect_frame by eassumption; reflexivity
    | erewrite check_timerfd_create_frame by eassumption; reflexivity
    | erewrite check_eventfd2_frame by eassumption; reflexivity
    | erewrite check_pipe2_frame by eassumption; reflexivity
    | erewrite check_getcwd_frame by eassumption; reflexivity
    | erewrite check_epoll_create1_frame by eassumption; reflexivity
    | erewrite check_epoll_ctl_frame by eassumption; reflexivity
    | erewrite check_epoll_pwait_frame by eassumption; reflexivity
    | fail 1 "VmLimitFrame: no case for this dispatcher arm (give it a *_frame lemma or a *_limit one)" ].
Qed.

Theorem check_syscall_preserves_limit : forall i eff m m' evs,
  check_syscall i eff m = CheckOk m' evs ->
  vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
Proof.
  intros i eff m m' evs H. unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_preserves_limit as Hall.
  rewrite Forall_forall in Hall.
  exact (Hall c (lookup_ca_In _ _ _ Elk) i eff m m' evs H).
Qed.

Corollary syscall_spec_preserves_limit : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
Proof.
  intros i m eff m' evs H.
  eapply check_syscall_preserves_limit. apply check_syscall_ok_iff. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma materialize_preserves_limit : forall m accesses m',
  materialize_model_accesses m accesses = Some m' ->
  vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
Proof.
  intros m accesses m' H.
  destruct (materialize_model_accesses_frame m accesses m' H) as (_ & Hvm & _).
  rewrite Hvm. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma sstep_preserves_limit : forall c evs c',
  sstep segs c evs (SNext c') ->
  vm_limit (m_vmmaps (cfg_model c')) = vm_limit (m_vmmaps (cfg_model c)).
Proof.
  intros c evs c' H. inversion H; subst; cbn [cfg_model].
  - match goal with Ha : mi_account_step _ _ _ = MachineOk _ |- _ =>
      destruct (mi_account_step_model_frame _ _ _ _ _ Ha) as (_ & Hvm & _) end.
    rewrite Hvm. reflexivity.
  - match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ =>
      rewrite (materialize_preserves_limit _ _ _ Hm) end.
    eapply syscall_spec_preserves_limit; eassumption.
  - eapply syscall_spec_preserves_limit; eassumption.
  - eapply syscall_spec_preserves_limit; eassumption.
Qed.

Lemma star_preserves_limit : forall c tr c',
  star segs c tr c' ->
  vm_limit (m_vmmaps (cfg_model c')) = vm_limit (m_vmmaps (cfg_model c)).
Proof.
  intros c tr c' H. induction H as [c | c1 evs c2 tr c3 Hss Hstar IH]; [reflexivity|].
  rewrite IH. exact (sstep_preserves_limit _ _ _ Hss).
Qed.

Variable scfg : SpuriousCfg.

Lemma sstep_cfg_preserves_limit : forall c evs c',
  sstep_cfg segs scfg c evs (SNext c') ->
  vm_limit (m_vmmaps (cfg_model c')) = vm_limit (m_vmmaps (cfg_model c)).
Proof. intros c evs c' H. exact (sstep_preserves_limit _ _ _ (sstep_cfg_sub _ _ _ _ _ H)). Qed.

Lemma star_cfg_preserves_limit : forall c tr c',
  star_cfg segs scfg c tr c' ->
  vm_limit (m_vmmaps (cfg_model c')) = vm_limit (m_vmmaps (cfg_model c)).
Proof. intros c tr c' H. exact (star_preserves_limit _ _ _ (star_cfg_sub _ _ _ _ _ H)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nbr_limit : Z := 2 ^ 39.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition xlim : Z := 2 ^ 34.

(* [comment removed for export] *)
Definition Safe (c : config) : Prop :=
  nbr_limit <= vm_limit (m_vmmaps (cfg_model c))
  \/ ~ reaches_budget_refused_cfg segs scfg c.

Lemma Safe_big : forall c, nbr_limit <= vm_limit (m_vmmaps (cfg_model c)) -> Safe c.
Proof. intros c H. left. exact H. Qed.

Lemma Safe_within_budget : forall c, ~ reaches_budget_refused_cfg segs scfg c -> Safe c.
Proof. intros c H. right. exact H. Qed.

Lemma Safe_step : forall c evs c',
  Safe c -> sstep_cfg segs scfg c evs (SNext c') -> Safe c'.
Proof.
  intros c evs c' [Hbig | Hnr] Hss.
  - left. rewrite (sstep_cfg_preserves_limit _ _ _ Hss). exact Hbig.
  - right. intros (tr & c'' & Hstar & Hb). apply Hnr.
    exists (evs ++ tr), c''. split; [exact (star_cfg_step segs scfg _ _ _ _ _ Hss Hstar) | exact Hb].
Qed.

Lemma Safe_star : forall c tr c',
  Safe c -> star_cfg segs scfg c tr c' -> Safe c'.
Proof.
  intros c tr c' Hs Hstar. induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; [exact Hs|].
  apply IH. exact (Safe_step _ _ _ Hs Hss).
Qed.

(* [comment removed for export] *)
Lemma Safe_not_refused : forall c,
  Safe c -> budget_refused_at segs c -> vm_limit (m_vmmaps (cfg_model c)) < nbr_limit -> False.
Proof.
  intros c [Hbig | Hnr] Hb Hlt; [lia|].
  apply Hnr. exists [], c. split; [apply star_cfg_refl | exact Hb].
Qed.

End WithSegs.

(* [comment removed for export] *)
Lemma init_config_limit : forall segs pc ph sp brk0 mbase rnd lim inp,
  vm_limit (m_vmmaps (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp))) = lim.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma source_limit_small : source_alloc_limit < nbr_limit.
Proof. unfold nbr_limit, source_alloc_limit. lia. Qed.

Lemma nbr_limit_target : nbr_limit <= target_alloc_limit.
Proof. unfold nbr_limit, target_alloc_limit. lia. Qed.

(* [comment removed for export] *)
Lemma Safe_init_big : forall scfg segs pc ph sp brk0 mbase rnd lim inp,
  nbr_limit <= lim -> Safe segs scfg (init_config segs pc ph sp brk0 mbase rnd lim inp).
Proof. intros. left. rewrite init_config_limit. assumption. Qed.

Lemma Safe_init_within_budget : forall scfg segs pc ph sp brk0 mbase rnd lim inp,
  ~ run_scfg_budget_refused scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mbase rnd) inp ->
  Safe segs scfg (init_config segs pc ph sp brk0 mbase rnd lim inp).
Proof. intros scfg segs pc ph sp brk0 mbase rnd lim inp H. right. exact H. Qed.
