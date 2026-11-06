From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics Fs State Monad Specs Run MemImageType StackLayout.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs VmMapsDisjoint.
Import ListNotations.

Definition vm_fixed (h' h : VmMaps) : Prop :=
  vm_init_sp h' = vm_init_sp h /\ vm_limit h' = vm_limit h.

Lemma vm_fixed_refl : forall h, vm_fixed h h.
Proof. intros h. split; reflexivity. Qed.

Lemma vm_fixed_trans : forall a b c, vm_fixed a b -> vm_fixed b c -> vm_fixed a c.
Proof. intros a b c [E1 E2] [E3 E4]. split; congruence. Qed.

Lemma frame_vm_fixed : forall m m' : Model,
  m_vmmaps m' = m_vmmaps m -> vm_fixed (m_vmmaps m') (m_vmmaps m).
Proof. intros m m' E. rewrite E. apply vm_fixed_refl. Qed.

Ltac isp_leaf :=
  rewrite ?vmm_brk_next, ?vmm_mmap_destroyed, ?vmm_mmap_replacement,
    ?vmm_mmap_backing, ?vmm_mremap_next, ?vmm_mprotect_next, ?vmm_vmmaps;
  unfold vm_fixed; split; reflexivity.

Ltac isp H := cbv zeta in H; repeat vm_step H; isp_leaf.

Lemma check_brk_vm_fixed : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs -> vm_fixed (m_vmmaps m') (m_vmmaps m).
Proof. intros req eff m m' evs H. unfold check_brk in H. isp H. Qed.

Lemma check_munmap_vm_fixed : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs -> vm_fixed (m_vmmaps m') (m_vmmaps m).
Proof. intros addr len eff m m' evs H. unfold check_munmap in H. isp H. Qed.

Lemma check_mprotect_vm_fixed : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs ->
  vm_fixed (m_vmmaps m') (m_vmmaps m).
Proof. intros addr len prot eff m m' evs H. unfold check_mprotect in H. isp H. Qed.

Lemma check_mmap_vm_fixed : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  vm_fixed (m_vmmaps m') (m_vmmaps m).
Proof.
  intros addr len prot flags fd off eff m m' evs H. unfold check_mmap in H. isp H.
Qed.

Lemma check_mremap_vm_fixed : forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs ->
  vm_fixed (m_vmmaps m') (m_vmmaps m).
Proof.
  intros old old_size new_size flags eff m m' evs H. unfold check_mremap in H. isp H.
Qed.

Definition arm_keeps_vm_fixed (c : CheckedArm) : Prop :=
  forall i eff m m' evs,
    ca_check c i eff m = CheckOk m' evs -> vm_fixed (m_vmmaps m') (m_vmmaps m).

Lemma checked_table_keeps_vm_fixed : Forall arm_keeps_vm_fixed checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_keeps_vm_fixed).
  all: unfold arm_keeps_vm_fixed; intros i eff m m' evs H;
       autorewrite with arm_unfold in H.
  all: first
    [ eapply check_brk_vm_fixed; eassumption
    | eapply check_mmap_vm_fixed; eassumption
    | eapply check_munmap_vm_fixed; eassumption
    | eapply check_mremap_vm_fixed; eassumption
    | eapply check_mprotect_vm_fixed; eassumption
    | apply frame_vm_fixed; first
      [ eapply check_madvise_frame; eassumption
      | eapply check_read_frame; eassumption
      | eapply check_write_frame; eassumption
      | eapply check_pread64_frame; eassumption
      | eapply check_pwrite64_frame; eassumption
      | eapply check_readv_frame; eassumption
      | eapply check_writev_frame; eassumption
      | eapply check_openat_frame; eassumption
      | eapply check_close_frame; eassumption
      | eapply check_lseek_frame; eassumption
      | eapply check_ftruncate_frame; eassumption
      | eapply check_ioctl_frame; eassumption
      | eapply check_readlinkat_frame; eassumption
      | eapply check_wait4_frame; eassumption
      | eapply check_fsync_frame; eassumption
      | eapply check_getdents64_frame; eassumption
      | eapply check_flock_frame; eassumption
      | eapply check_exit_frame; eassumption
      | eapply check_set_tid_address_frame; eassumption
      | eapply check_getpid_frame; eassumption
      | eapply check_gettid_frame; eassumption
      | eapply check_setsid_frame; eassumption
      | eapply check_uname_frame; eassumption
      | eapply check_prctl_frame; eassumption
      | eapply check_prlimit64_frame; eassumption
      | eapply check_getrandom_frame; eassumption
      | eapply check_gettimeofday_frame; eassumption
      | eapply check_clock_gettime_frame; eassumption
      | eapply check_nanosleep_frame; eassumption
      | eapply check_dup_frame; eassumption
      | eapply check_dup3_frame; eassumption
      | eapply check_unlinkat_frame; eassumption
      | eapply check_faccessat_frame; eassumption
      | eapply check_faccessat2_frame; eassumption
      | eapply check_pselect6_frame; eassumption
      | eapply check_ppoll_frame; eassumption
      | eapply check_newfstatat_frame; eassumption
      | eapply check_fstat_frame; eassumption
      | eapply check_getid_frame; eassumption
      | eapply check_setid_frame; eassumption
      | eapply check_setresid_frame; eassumption
      | eapply check_getgroups_frame; eassumption
      | eapply check_setgroups_frame; eassumption
      | eapply check_socket_frame; eassumption
      | eapply check_bind_frame; eassumption
      | eapply check_listen_frame; eassumption
      | eapply check_accept4_frame; eassumption
      | eapply check_fcntl_frame; eassumption
      | eapply check_sched_setscheduler_frame; eassumption
      | eapply check_sched_getaffinity_frame; eassumption
      | eapply check_sched_yield_frame; eassumption
      | eapply check_sigaltstack_frame; eassumption
      | eapply check_rt_sigaction_frame; eassumption
      | eapply check_tkill_frame; eassumption
      | eapply check_tgkill_frame; eassumption
      | eapply check_rt_sigprocmask_frame; eassumption
      | eapply check_futex_frame; eassumption
      | eapply check_clone_frame; eassumption
      | eapply check_clone3_frame; eassumption
      | eapply check_getsockname_frame; eassumption
      | eapply check_getpeername_frame; eassumption
      | eapply check_setsockopt_frame; eassumption
      | eapply check_getsockopt_frame; eassumption
      | eapply check_shutdown_frame; eassumption
      | eapply check_sendto_frame; eassumption
      | eapply check_sendmsg_frame; eassumption
      | eapply check_socketpair_frame; eassumption
      | eapply check_recvfrom_frame; eassumption
      | eapply check_recvmsg_frame; eassumption
      | eapply check_connect_frame; eassumption
      | eapply check_timerfd_create_frame; eassumption
      | eapply check_eventfd2_frame; eassumption
      | eapply check_pipe2_frame; eassumption
      | eapply check_getcwd_frame; eassumption
      | eapply check_epoll_create1_frame; eassumption
      | eapply check_epoll_ctl_frame; eassumption
      | eapply check_epoll_pwait_frame; eassumption ] ].
Qed.

Theorem check_syscall_vm_fixed : forall i eff m m' evs,
  check_syscall i eff m = CheckOk m' evs -> vm_fixed (m_vmmaps m') (m_vmmaps m).
Proof.
  intros i eff m m' evs H. unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_keeps_vm_fixed as Hall.
  rewrite Forall_forall in Hall.
  exact (Hall c (lookup_ca_In _ _ _ Elk) i eff m m' evs H).
Qed.

Corollary syscall_spec_vm_fixed : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) -> vm_fixed (m_vmmaps m') (m_vmmaps m).
Proof.
  intros i m eff m' evs H.
  apply (check_syscall_vm_fixed i eff m m' evs).
  apply check_syscall_ok_iff. exact H.
Qed.

Corollary syscall_spec_init_sp : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
Proof. intros i m eff m' evs H. exact (proj1 (syscall_spec_vm_fixed i m eff m' evs H)). Qed.

Corollary syscall_spec_vm_limit : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
Proof. intros i m eff m' evs H. exact (proj2 (syscall_spec_vm_fixed i m eff m' evs H)). Qed.

Lemma materialize_model_accesses_vm_fixed : forall model' acc model'',
  materialize_model_accesses model' acc = Some model'' ->
  vm_fixed (m_vmmaps model'') (m_vmmaps model').
Proof.
  intros model' acc model'' H.
  apply materialize_model_accesses_frame in H as (_ & E & _).
  apply frame_vm_fixed. exact E.
Qed.

Lemma materialize_model_accesses_init_sp : forall model' acc model'',
  materialize_model_accesses model' acc = Some model'' ->
  vm_init_sp (m_vmmaps model'') = vm_init_sp (m_vmmaps model').
Proof.
  intros model' acc model'' H.
  exact (proj1 (materialize_model_accesses_vm_fixed model' acc model'' H)).
Qed.

Lemma materialize_model_accesses_vm_limit : forall model' acc model'',
  materialize_model_accesses model' acc = Some model'' ->
  vm_limit (m_vmmaps model'') = vm_limit (m_vmmaps model').
Proof.
  intros model' acc model'' H.
  exact (proj2 (materialize_model_accesses_vm_fixed model' acc model'' H)).
Qed.

Lemma mi_account_step_vm_fixed : forall segs ms model ms' model',
  mi_account_step segs ms model = MachineOk (ms', model') ->
  vm_fixed (m_vmmaps model') (m_vmmaps model).
Proof.
  intros segs ms model ms' model' H.
  apply mi_account_step_model_frame in H as (_ & E & _).
  apply frame_vm_fixed. exact E.
Qed.

Lemma mi_account_step_init_sp : forall segs ms model ms' model',
  mi_account_step segs ms model = MachineOk (ms', model') ->
  vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model).
Proof.
  intros segs ms model ms' model' H.
  exact (proj1 (mi_account_step_vm_fixed segs ms model ms' model' H)).
Qed.

Lemma mi_account_step_vm_limit : forall segs ms model ms' model',
  mi_account_step segs ms model = MachineOk (ms', model') ->
  vm_limit (m_vmmaps model') = vm_limit (m_vmmaps model).
Proof.
  intros segs ms model ms' model' H.
  exact (proj2 (mi_account_step_vm_fixed segs ms model ms' model' H)).
Qed.

Lemma sstep_cfg_vm_fixed : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  vm_fixed (m_vmmaps (cfg_model c')) (m_vmmaps (cfg_model c)).
Proof.
  intros segs cfg c evs c' H.
  inversion H; subst; cbn [cfg_model];
    first
      [ eapply mi_account_step_vm_fixed; eassumption
      | eapply vm_fixed_trans;
          [ eapply materialize_model_accesses_vm_fixed; eassumption
          | eapply syscall_spec_vm_fixed; eassumption ]
      | eapply syscall_spec_vm_fixed; eassumption ].
Qed.

Lemma sstep_cfg_init_sp : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  vm_init_sp (m_vmmaps (cfg_model c')) = vm_init_sp (m_vmmaps (cfg_model c)).
Proof.
  intros segs cfg c evs c' H. exact (proj1 (sstep_cfg_vm_fixed segs cfg c evs c' H)).
Qed.

Lemma sstep_cfg_vm_limit : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  vm_limit (m_vmmaps (cfg_model c')) = vm_limit (m_vmmaps (cfg_model c)).
Proof.
  intros segs cfg c evs c' H. exact (proj2 (sstep_cfg_vm_fixed segs cfg c evs c' H)).
Qed.

Lemma star_cfg_vm_fixed : forall segs cfg c tr c',
  star_cfg segs cfg c tr c' ->
  vm_fixed (m_vmmaps (cfg_model c')) (m_vmmaps (cfg_model c)).
Proof.
  intros segs cfg c tr c' H.
  induction H as [c | c1 evs c2 tr c3 Hs _ IH]; [apply vm_fixed_refl|].
  exact (vm_fixed_trans _ _ _ IH (sstep_cfg_vm_fixed segs cfg c1 evs c2 Hs)).
Qed.

Lemma star_cfg_init_sp : forall segs cfg c tr c',
  star_cfg segs cfg c tr c' ->
  vm_init_sp (m_vmmaps (cfg_model c')) = vm_init_sp (m_vmmaps (cfg_model c)).
Proof.
  intros segs cfg c tr c' H. exact (proj1 (star_cfg_vm_fixed segs cfg c tr c' H)).
Qed.

Lemma star_cfg_vm_limit : forall segs cfg c tr c',
  star_cfg segs cfg c tr c' ->
  vm_limit (m_vmmaps (cfg_model c')) = vm_limit (m_vmmaps (cfg_model c)).
Proof.
  intros segs cfg c tr c' H. exact (proj2 (star_cfg_vm_fixed segs cfg c tr c' H)).
Qed.

Corollary sstep_cfg_alloc_top : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  alloc_top (m_vmmaps (cfg_model c')) = alloc_top (m_vmmaps (cfg_model c)).
Proof.
  intros segs cfg c evs c' H. unfold alloc_top.
  rewrite (sstep_cfg_init_sp segs cfg c evs c' H). reflexivity.
Qed.

Corollary star_cfg_alloc_top : forall segs cfg c tr c',
  star_cfg segs cfg c tr c' ->
  alloc_top (m_vmmaps (cfg_model c')) = alloc_top (m_vmmaps (cfg_model c)).
Proof.
  intros segs cfg c tr c' H. unfold alloc_top.
  rewrite (star_cfg_init_sp segs cfg c tr c' H). reflexivity.
Qed.

Lemma init_config_vm_limit : forall segs pc ph sp brk mbase rnd lim inp,
  vm_limit (m_vmmaps (cfg_model (init_config segs pc ph sp brk mbase rnd lim inp))) = lim.
Proof.
  intros segs pc ph sp brk mbase rnd lim inp.
  unfold init_config. cbn [cfg_model]. rewrite m_vmmaps_init_model. reflexivity.
Qed.
