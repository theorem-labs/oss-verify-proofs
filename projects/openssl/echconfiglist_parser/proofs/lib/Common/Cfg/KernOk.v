(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11: the run's kernel build and mmap base are constants of the run.
   [State.with_kernel] has one caller, [init_model] (State.v:5035-5036), and every VM setter
   copies [vm_mmap_base], so every step keeps [m_kernel] and [vm_mmap_base (m_vmmaps _)].
   The proof is [PinsOk]'s, invariant for invariant: every outcome of [Specs.syscall_spec] keeps
   [kern_ok] ([kern_spec_ok]), through [ExecutableSpecs.check_syscall_complete_ok] and a walk of
   every arm of [Checks.Sys.Dispatch.checked_table] in [Checks/KillFree.v]'s unfolding, each leaf
   closed by conversion through the setters or by a wrapper lemma below; every step of
   [Run.sstep_cfg] keeps it ([kern_step]): the first-touch accounting and the materialization
   rebuild the VM state by [with_vm_backing], and [with_vdso_bump] rebuilds the vDSO part only;
   the launch makes it ([kern_ok_init]). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs VmMapsDisjoint KillFree.
Import ListNotations.
Open Scope bv_scope.

Section KK.
  Variable kb : KernelBuild.
  Variable mb : word.

(** * The invariant *)

Definition kern_ok (mo : Model) : Prop :=
  m_kernel mo = kb /\ vm_mmap_base (m_vmmaps mo) = mb.

(** What one checker outcome owes. *)
Definition kern_post (m m' : Model) : Prop := kern_ok m -> kern_ok m'.

Lemma kern_ok_eq : forall m m', kern_ok m ->
  m_kernel m' = m_kernel m -> vm_mmap_base (m_vmmaps m') = vm_mmap_base (m_vmmaps m) -> kern_ok m'.
Proof. intros m m' [Hk Hb] Ek Eb. split; [rewrite Ek; exact Hk | rewrite Eb; exact Hb]. Qed.

(** * The model wrappers a post-model can be (their [m_proc] twins: Checks/KillFree.v:197-223) *)

Lemma kk_k_forget : forall rs m, m_kernel (forget_vm_ranges rs m) = m_kernel m.
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. reflexivity.
Qed.

Lemma kk_b_forget : forall rs m, vm_mmap_base (m_vmmaps (forget_vm_ranges rs m)) = vm_mmap_base (m_vmmaps m).
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. reflexivity.
Qed.

Lemma kk_k_brk : forall m req r, m_kernel (with_brk_next m req r) = m_kernel m.
Proof. intros m req r. unfold with_brk_next. cbv zeta. rewrite kk_k_forget. reflexivity. Qed.

Lemma kk_b_brk : forall m req r, vm_mmap_base (m_vmmaps (with_brk_next m req r)) = vm_mmap_base (m_vmmaps m).
Proof. intros m req r. unfold with_brk_next. cbv zeta. rewrite kk_b_forget. reflexivity. Qed.

Lemma kk_k_backing : forall flags a n m, m_kernel (with_mmap_backing flags a n m) = m_kernel m.
Proof. intros flags a n m. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma kk_b_backing : forall flags a n m,
  vm_mmap_base (m_vmmaps (with_mmap_backing flags a n m)) = vm_mmap_base (m_vmmaps m).
Proof. intros flags a n m. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma kk_k_repl : forall flags a n m, m_kernel (with_mmap_replacement flags a n m) = m_kernel m.
Proof. intros flags a n m. unfold with_mmap_replacement. rewrite kk_k_backing. reflexivity. Qed.

Lemma kk_b_repl : forall flags a n m,
  vm_mmap_base (m_vmmaps (with_mmap_replacement flags a n m)) = vm_mmap_base (m_vmmaps m).
Proof. intros flags a n m. unfold with_mmap_replacement. rewrite kk_b_backing. reflexivity. Qed.

(** [ReadWrite.raise_sigpipe] (Sys/Fs/ReadWrite.v:1350-1355). *)
Lemma kk_k_raise : forall m, m_kernel (raise_sigpipe m) = m_kernel m.
Proof.
  intros m. unfold raise_sigpipe.
  destruct (m_sigpipe_default m), (sigpipe_blocked (m_sigmask m)); reflexivity.
Qed.

Lemma kk_b_raise : forall m, vm_mmap_base (m_vmmaps (raise_sigpipe m)) = vm_mmap_base (m_vmmaps m).
Proof.
  intros m. unfold raise_sigpipe.
  destruct (m_sigpipe_default m), (sigpipe_blocked (m_sigmask m)); reflexivity.
Qed.

(** [Signal.sigmask_deliver_model] (Sys/Kernel/Signal.v:1371-1376). *)
Lemma kk_k_sigmask : forall new m, m_kernel (sigmask_deliver_model new m) = m_kernel m.
Proof.
  intros new m. unfold sigmask_deliver_model.
  destruct (m_sigabrt_pending m), (sigabrt_blocked new), (m_sigpipe_pending m),
    (sigpipe_blocked new); reflexivity.
Qed.

Lemma kk_b_sigmask : forall new m, vm_mmap_base (m_vmmaps (sigmask_deliver_model new m)) = vm_mmap_base (m_vmmaps m).
Proof.
  intros new m. unfold sigmask_deliver_model.
  destruct (m_sigabrt_pending m), (sigabrt_blocked new), (m_sigpipe_pending m),
    (sigpipe_blocked new); reflexivity.
Qed.

Create HintDb kk_kept.
#[local] Hint Rewrite kk_k_forget kk_b_forget kk_k_brk kk_b_brk kk_k_backing kk_b_backing
  kk_k_repl kk_b_repl kk_k_raise kk_b_raise kk_k_sigmask kk_b_sigmask : kk_kept.

(** * Closing a leaf of a checker walk *)

(* One field of the post-model against the same field of [m]: by conversion through the setters,
   or through a wrapper above. *)
Ltac kk_fld := first [ reflexivity | (autorewrite with kk_kept; reflexivity) ].

(* The post-model is [m] itself, or keeps both fields; [Hp] is [kern_ok m]. *)
Ltac kk_close Hp :=
  first
  [ exact Hp
  | (refine (kern_ok_eq _ _ Hp _ _); kk_fld) ].

(** * The sub-checkers [kf_step] does not open (Checks/KillFree.v:258-475) *)

Lemma check_efault_or_kk : forall fb eff m m' evs,
  check_efault_or fb eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros fb eff m m' evs H Hp. unfold check_efault_or in H.
  repeat kf_step H; kk_close Hp.
Qed.

(** The SIGPIPE answer is over [raise_sigpipe m] (Checks/Sys/Fs/ReadWrite.v:255-258,
    :5183-5186); unlike [KillFree], nothing here closes the gate, so the branch is walked. *)
Lemma check_sigpipe_write_kk : forall eff m m' evs,
  check_sigpipe_write eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros eff m m' evs H Hp. unfold check_sigpipe_write in H.
  repeat kf_step H; kk_close Hp.
Qed.

Lemma check_sigpipe_writev_kk : forall reads eff m m' evs,
  check_sigpipe_writev reads eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros reads eff m m' evs H Hp. unfold check_sigpipe_writev in H.
  repeat kf_step H; kk_close Hp.
Qed.

Ltac kk_stream_base H Hp :=
  first
  [ exact (check_efault_or_kk _ _ _ _ _ H Hp)
  | exact (check_sigpipe_write_kk _ _ _ _ H Hp) ].

Lemma check_stream_read_empty_kk : forall fd id side st nonblock eff m m' evs,
  check_stream_read_empty fd id side st nonblock eff m = CheckOk m' evs ->
  kern_post m m'.
Proof.
  intros fd id side st nonblock eff m m' evs H Hp.
  unfold check_stream_read_empty, check_stream_read_reset in H. cbv beta iota zeta in H.
  repeat (kf_step H || kk_stream_base H Hp); kk_close Hp.
Qed.

Lemma check_stream_read_kk :
  forall fd id side st nonblock buf count i eff m m' evs,
  check_stream_read fd id side st nonblock buf count i eff m = CheckOk m' evs ->
  kern_post m m'.
Proof.
  intros fd id side st nonblock buf count i eff m m' evs H Hp.
  unfold check_stream_read, check_stream_read_empty, check_stream_read_reset in H. cbv beta iota zeta in H.
  repeat (kf_step H || kk_stream_base H Hp); kk_close Hp.
Qed.

Lemma check_stream_send_kk :
  forall id side st nonblock nosignal n src ledger eff m m' evs,
  check_stream_send id side st nonblock nosignal n src ledger eff m = CheckOk m' evs ->
  kern_post m m'.
Proof.
  intros id side st nonblock nosignal n src ledger eff m m' evs H Hp.
  unfold check_stream_send in H. cbv beta iota zeta in H.
  repeat (kf_step H || kk_stream_base H Hp); kk_close Hp.
Qed.

Lemma check_stream_write_kk :
  forall id side st nonblock nosignal buf count i eff m m' evs,
  check_stream_write id side st nonblock nosignal buf count i eff m = CheckOk m' evs ->
  kern_post m m'.
Proof.
  intros id side st nonblock nosignal buf count i eff m m' evs H.
  unfold check_stream_write in H. exact (check_stream_send_kk _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

Ltac kk_stream H Hp :=
  first
  [ exact (check_stream_read_kk _ _ _ _ _ _ _ _ _ _ _ _ H Hp)
  | exact (check_stream_read_empty_kk _ _ _ _ _ _ _ _ _ H Hp)
  | exact (check_stream_write_kk _ _ _ _ _ _ _ _ _ _ _ _ H Hp)
  | exact (check_stream_send_kk _ _ _ _ _ _ _ _ _ _ _ _ H Hp) ].

(** [rt_sigaction] on SIGPIPE, as [KillFree.check_rt_sigaction_sigpipe_kf] takes it apart; the
    install ([State.with_sigpipe_install], State.v:5493-5503) copies the VM state. *)
Lemma check_rt_sigaction_sigpipe_kk : forall i act oact eff m m' evs,
  check_rt_sigaction_sigpipe i act oact eff m = CheckOk m' evs ->
  kern_post m m'.
Proof.
  intros i act oact eff m m' evs H Hp.
  unfold check_rt_sigaction_sigpipe in H. cbv zeta in H.
  destruct (w_is0 act); cbv beta iota in H.
  { apply check_sigpipe_oact_write_model in H. subst m'. exact Hp. }
  destruct (sigaction_struct (in_mem i) act) as [bs|]; cbv beta iota in H.
  2:{ apply check_ret_only_ok_iff in H. destruct H as (_ & -> & _). exact Hp. }
  destruct (negb (Z.eqb (sigaction_field bs 0) SIG_DFL
                  || Z.eqb (sigaction_field bs 0) SIG_IGN)%bool);
    cbv beta iota in H; [discriminate|].
  destruct (Z.eqb (sigaction_field bs 0) SIG_DFL
            && sigpipe_hidden_pending_possible m)%bool;
    cbv beta iota in H; [discriminate|].
  apply check_copyins_after_ok_iff in H. destruct H as (_ & H).
  apply check_sigpipe_oact_write_model in H. subst m'.
  refine (kern_ok_eq _ _ Hp _ _); reflexivity.
Qed.

(** The new-descriptor answer of [openat] and its kin: the installed model is [mk fd]. *)
Lemma check_open_result_kk : forall eff m mk m' evs,
  check_open_result eff m mk = CheckOk m' evs ->
  (forall fd, kern_post m (mk fd)) ->
  kern_post m m'.
Proof.
  intros eff m mk m' evs H Hmk Hp.
  unfold check_open_result, check_new_fd_result in H.
  repeat kf_step H.
  all: first [ kk_close Hp | exact (Hmk _ Hp) ].
Qed.

Lemma check_readv_imported_kk : forall i fd r iovs0 eff m m' evs,
  check_readv_imported i fd r iovs0 eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd r iovs0 eff m m' evs H Hp.
  unfold check_readv_imported in H. cbv beta iota zeta in H.
  repeat (kf_step H
          || exact (check_efault_or_kk _ _ _ _ _ H Hp)
          || kk_stream H Hp
          || elim (check_readv_gap_frame _ _ H));
  kk_close Hp.
Qed.

Ltac kk_done H Hp :=
  first
  [ exact (check_efault_or_kk _ _ _ _ _ H Hp)
  | exact (check_sigpipe_write_kk _ _ _ _ H Hp)
  | exact (check_sigpipe_writev_kk _ _ _ _ _ H Hp)
  | elim (check_readv_gap_frame _ _ H)
  | kk_stream H Hp
  | exact (check_readv_imported_kk _ _ _ _ _ _ _ _ H Hp)
  | (refine (check_open_result_kk _ _ _ _ _ H _ Hp);
     let fd := fresh "fd" in let Ho := fresh "Ho" in
     intros fd Ho; kk_close Ho) ].

(* [KillFree.kf_frame] with this file's leaf closer. *)
Ltac kk_frame H Hp :=
  cbv beta iota zeta in H;
  repeat (kf_step H || kk_done H Hp); kk_close Hp.

(** * The arms, each unfolded as [Checks/KillFree.v] unfolds it *)

(** [tkill] and [tgkill] (Checks/Sys/Kernel/Signal.v:1166-1211): the abort leaves the VM state. *)
Lemma check_tkill_kk : forall pid sig eff m m' evs,
  check_tkill pid sig eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros pid sig eff m m' evs H Hp.
  unfold check_tkill, check_tkill_self, check_send_sigabrt in H.
  kk_frame H Hp.
Qed.

Lemma check_tgkill_kk : forall tgid pid sig eff m m' evs,
  check_tgkill tgid pid sig eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros tgid pid sig eff m m' evs H Hp.
  unfold check_tgkill, check_tkill_self, check_send_sigabrt in H.
  kk_frame H Hp.
Qed.

(** [rt_sigprocmask] (Checks/Sys/Kernel/Signal.v:832-856): the post-model is
    [sigmask_deliver_model _ m] ([kk_u_sigmask], [kk_r_sigmask]). *)
Lemma check_rt_sigprocmask_kk : forall i how nset oset ss eff m m' evs,
  check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i how nset oset ss eff m m' evs H Hp.
  unfold check_rt_sigprocmask in H. cbv zeta in H.
  kk_frame H Hp.
Qed.

(** The other arms: [Checks/KillFree.v]'s unfolding, one for one. *)

Lemma check_brk_kk : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros req [ret ws zs us cs ci] m m' evs H Hp.
  unfold check_brk in H.
  kk_frame H Hp.
Qed.

Lemma check_mmap_kk : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H Hp.
  unfold check_mmap, check_mmap_fixed_overflow in H.
  cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_munmap_kk : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H Hp.
  unfold check_munmap in H.
  cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_mremap_kk : forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H Hp.
  unfold check_mremap in H.
  cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_mprotect_kk : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros addr len prot [ret ws zs us cs ci] m m' evs H Hp.
  unfold check_mprotect in H.
  cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_madvise_kk : forall addr len advice eff m m' evs,
  check_madvise addr len advice eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros addr len advice [ret ws zs us cs ci] m m' evs H Hp.
  unfold check_madvise in H.
  cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_read_kk : forall i fd buf count eff m m' evs,
  check_read i fd buf count eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd buf count eff m m' evs H Hp.
  unfold check_read, check_read_urandom, check_socket_pending_error, check_access_ok_zero,
    check_eventfd_read in H.
  cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_write_kk : forall i fd buf count eff m m' evs,
  check_write i fd buf count eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd buf count eff m m' evs H Hp.
  unfold check_write, check_write_fault_extend, check_access_ok_zero,
    check_eventfd_write, check_anon_write_fault, check_anon_fault_extend,
    anon_place_fds in H.
  cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_pread64_kk : forall i fd buf count pos eff m m' evs,
  check_pread64 i fd buf count pos eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd buf count pos eff m m' evs H Hp.
  unfold check_pread64, check_read_urandom in H.
  cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_pwrite64_kk : forall i fd buf count pos eff m m' evs,
  check_pwrite64 i fd buf count pos eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd buf count pos eff m m' evs H Hp.
  unfold check_pwrite64, check_write_fault_extend, check_anon_fault_extend in H.
  cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_readv_kk : forall i fd iov iovcnt eff m m' evs,
  check_readv i fd iov iovcnt eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd iov iovcnt eff m m' evs H Hp.
  unfold check_readv in H.
  kk_frame H Hp.
Qed.

Lemma check_writev_kk : forall i fd iov iovcnt eff m m' evs,
  check_writev i fd iov iovcnt eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd iov iovcnt eff m m' evs H Hp.
  unfold check_writev, check_write_fault_extend, check_anon_write_fault,
    check_anon_fault_extend, anon_place_fds in H.
  cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_pwritev2_kk :
  forall i fd iov iovcnt pos_l pos_h flags eff m m' evs,
  check_pwritev2 i fd iov iovcnt pos_l pos_h flags eff m = CheckOk m' evs ->
  kern_post m m'.
Proof.
  intros i fd iov iovcnt pos_l pos_h flags eff m m' evs H Hp.
  unfold check_pwritev2, check_anon_fault_extend in H.
  cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_openat_kk : forall i dirfd pathp flags eff m m' evs,
  check_openat i dirfd pathp flags eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i dirfd pathp flags eff m m' evs H Hp.
  unfold check_openat, Open.check_openat_body, Open.check_openat_resolved, Open.check_openat_sep,
    Open.check_openat_localtime, Open.check_openat_devnull, Open.check_open_devnull,
    Open.check_openat_urandom, Open.check_open_urandom, Open.check_openat_procfd,
    Open.check_openat_tmp, Open.check_openat_read, Open.check_openat_create, Open.check_openat_excl,
    Open.check_openat_dir, Open.check_openat_append, Open.check_openat_rdwr,
    Open.check_openat_rdwr_excl, check_create_wronly, check_open_append, check_open_rdwr in H.
  kk_frame H Hp.
Qed.

Lemma check_close_kk : forall fd eff m m' evs,
  check_close fd eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros fd eff m m' evs H Hp.
  unfold check_close in H.
  kk_frame H Hp.
Qed.

Lemma check_lseek_kk : forall fd off whence eff m m' evs,
  check_lseek fd off whence eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros fd off whence eff m m' evs H Hp.
  unfold check_lseek in H.
  kk_frame H Hp.
Qed.

Lemma check_ftruncate_kk : forall fd len eff m m' evs,
  check_ftruncate fd len eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros fd len eff m m' evs H Hp.
  unfold check_ftruncate in H.
  kk_frame H Hp.
Qed.

Lemma check_ioctl_kk : forall i fd req eff m m' evs,
  check_ioctl i fd req eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd req eff m m' evs H Hp.
  unfold check_ioctl, check_siocgifindex, check_ifreq_writeback in H.
  kk_frame H Hp.
Qed.

Lemma check_readlinkat_kk : forall dirfd eff m m' evs,
  check_readlinkat dirfd eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros dirfd eff m m' evs H Hp.
  unfold check_readlinkat in H.
  kk_frame H Hp.
Qed.

Lemma check_wait4_kk : forall i upid stat_addr options rusage eff m m' evs,
  check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i upid stat_addr options rusage eff m m' evs H Hp.
  unfold check_wait4 in H.
  kk_frame H Hp.
Qed.

Lemma check_fsync_kk : forall fd eff m m' evs,
  check_fsync fd eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros fd eff m m' evs H Hp.
  unfold check_fsync in H.
  kk_frame H Hp.
Qed.

Lemma check_getdents64_kk : forall fd count eff m m' evs,
  check_getdents64 fd count eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros fd count eff m m' evs H Hp.
  unfold check_getdents64 in H.
  kk_frame H Hp.
Qed.

Lemma check_flock_kk : forall fd cmd eff m m' evs,
  check_flock fd cmd eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros fd cmd eff m m' evs H Hp.
  unfold check_flock in H.
  kk_frame H Hp.
Qed.

Lemma check_exit_kk : forall code eff m m' evs,
  check_exit code eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros code eff m m' evs H Hp.
  unfold check_exit in H.
  kk_frame H Hp.
Qed.

Lemma check_set_tid_address_kk : forall eff m m' evs,
  check_set_tid_address eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros eff m m' evs H Hp.
  unfold check_set_tid_address in H.
  kk_frame H Hp.
Qed.

Lemma check_getpid_kk : forall eff m m' evs,
  check_getpid eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  exact check_set_tid_address_kk.
Qed.

Lemma check_gettid_kk : forall eff m m' evs,
  check_gettid eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  exact check_set_tid_address_kk.
Qed.

Lemma check_setsid_kk : forall eff m m' evs,
  check_setsid eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros eff m m' evs H Hp.
  unfold check_setsid in H.
  kk_frame H Hp.
Qed.

Lemma check_uname_kk : forall i name eff m m' evs,
  check_uname i name eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i name eff m m' evs H Hp.
  unfold check_uname, check_uname_copy in H.
  kk_frame H Hp.
Qed.

Lemma check_prctl_kk : forall option_ arg2 eff m m' evs,
  check_prctl option_ arg2 eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros option_ arg2 eff m m' evs H Hp.
  unfold check_prctl in H.
  kk_frame H Hp.
Qed.

Lemma check_prlimit64_kk : forall i pid resource new_rlim old_rlim eff m m' evs,
  check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i pid resource new_rlim old_rlim eff m m' evs H Hp.
  unfold check_prlimit64, check_rlim64_read in H.
  kk_frame H Hp.
Qed.

Lemma check_getrandom_kk : forall i buf cap flags eff m m' evs,
  check_getrandom i buf cap flags eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i buf cap flags eff m m' evs H Hp.
  unfold check_getrandom, check_getrandom_zero in H.
  kk_frame H Hp.
Qed.

Lemma check_gettimeofday_kk : forall i tv tz eff m m' evs,
  check_gettimeofday i tv tz eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i tv tz eff m m' evs H Hp.
  unfold check_gettimeofday in H.
  kk_frame H Hp.
Qed.

Lemma check_clock_gettime_kk : forall i clkid tp eff m m' evs,
  check_clock_gettime i clkid tp eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i clkid tp eff m m' evs H Hp.
  unfold check_clock_gettime in H.
  kk_frame H Hp.
Qed.

Lemma check_clock_getres_kk : forall i clkid tp eff m m' evs,
  check_clock_getres i clkid tp eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i clkid tp eff m m' evs H Hp.
  unfold check_clock_getres, check_clock_getres_result in H.
  kk_frame H Hp.
Qed.

Lemma check_nanosleep_kk : forall i rqtp rmtp eff m m' evs,
  check_nanosleep i rqtp rmtp eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i rqtp rmtp eff m m' evs H Hp.
  unfold check_nanosleep in H.
  kk_frame H Hp.
Qed.

Lemma check_dup_kk : forall oldfd eff m m' evs,
  check_dup oldfd eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros oldfd eff m m' evs H Hp.
  unfold check_dup, check_dup_result in H.
  kk_frame H Hp.
Qed.

Lemma check_dup3_kk : forall oldfd newfd flags eff m m' evs,
  check_dup3 oldfd newfd flags eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros oldfd newfd flags eff m m' evs H Hp.
  unfold check_dup3 in H.
  kk_frame H Hp.
Qed.

Lemma check_unlinkat_kk : forall i dirfd pathp flags eff m m' evs,
  check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i dirfd pathp flags eff m m' evs H Hp.
  unfold check_unlinkat, Namei.check_unlinkat_body, Namei.check_unlinkat_tmp, Namei.check_unlink_found, check_unlink_result,
    Namei.check_unlink_open_tmp, check_unlink_open_result, check_unlink_type_result in H.
  kk_frame H Hp.
Qed.

Lemma check_faccessat_kk : forall i dirfd pathp mode eff m m' evs,
  check_faccessat i dirfd pathp mode eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i dirfd pathp mode eff m m' evs H Hp.
  unfold check_faccessat, Open.check_faccessat_body, check_access_exists in H.
  kk_frame H Hp.
Qed.

Lemma check_faccessat2_kk : forall i dirfd pathp mode flags eff m m' evs,
  check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i dirfd pathp mode flags eff m m' evs H Hp.
  unfold check_faccessat2, Open.check_faccessat_body, check_access_exists in H.
  kk_frame H Hp.
Qed.

Lemma check_pselect6_kk : forall i n32 inp outp exp tsp sig eff m m' evs,
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i n32 inp outp exp tsp sig eff m m' evs H Hp.
  unfold check_pselect6, check_pselect_answer in H.
  kk_frame H Hp.
Qed.

Lemma check_ppoll_kk : forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H Hp.
  unfold check_ppoll, check_pselect_answer in H.
  kk_frame H Hp.
Qed.

Lemma check_newfstatat_kk : forall i dirfd pathp flag eff m m' evs,
  check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i dirfd pathp flag eff m m' evs H Hp.
  unfold check_newfstatat in H.
  kk_frame H Hp.
Qed.

Lemma check_fstat_kk : forall i fd statbuf eff m m' evs,
  check_fstat i fd statbuf eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd statbuf eff m m' evs H Hp.
  unfold check_fstat, check_fstat_file, check_fstat_devnull, check_fstat_urandom,
    check_fstat_chrdev, check_fstat_deliver, check_fstat_deliver_by,
    check_fstat_anon, check_fstat_anon_deliver in H.
  kk_frame H Hp.
Qed.

Lemma check_getid_kk : forall sel eff m m' evs,
  check_getid sel eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros sel eff m m' evs H Hp.
  unfold check_getid in H.
  kk_frame H Hp.
Qed.

Lemma check_setid_kk : forall get put user v eff m m' evs,
  check_setid get put user v eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros get put user v eff m m' evs H Hp.
  unfold check_setid, check_setid_result in H.
  kk_frame H Hp.
Qed.

Lemma check_setresid_kk : forall get put user r e sv eff m m' evs,
  check_setresid get put user r e sv eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros get put user r e sv eff m m' evs H Hp.
  unfold check_setresid, check_setid_result in H.
  kk_frame H Hp.
Qed.

Lemma check_getgroups_kk : forall gidsetsize eff m m' evs,
  check_getgroups gidsetsize eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros gidsetsize eff m m' evs H Hp.
  unfold check_getgroups in H.
  kk_frame H Hp.
Qed.

Lemma check_setgroups_kk : forall eff m m' evs,
  check_setgroups eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros eff m m' evs H Hp.
  unfold check_setgroups in H.
  kk_frame H Hp.
Qed.

Lemma check_socket_kk : forall domain type protocol eff m m' evs,
  check_socket domain type protocol eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros domain type protocol eff m m' evs H Hp.
  unfold check_socket, check_new_fd_result, check_errno_or_list in H.
  kk_frame H Hp.
Qed.

Lemma check_bind_kk : forall i fd addrp addrlen eff m m' evs,
  check_bind i fd addrp addrlen eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd addrp addrlen eff m m' evs H Hp.
  unfold check_bind, check_errno_or_success in H.
  kk_frame H Hp.
Qed.

Lemma check_listen_kk : forall fd backlog eff m m' evs,
  check_listen fd backlog eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros fd backlog eff m m' evs H Hp.
  unfold check_listen, check_errno_or_success, check_errno_only in H.
  kk_frame H Hp.
Qed.

Lemma check_accept4_kk : forall fd addrp addrlenp flags eff m m' evs,
  check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros fd addrp addrlenp flags eff m m' evs H Hp.
  unfold check_accept4, check_new_fd_result, check_errno_or_success, check_errno_only, check_errno_or_list in H.
  kk_frame H Hp.
Qed.

Lemma check_fcntl_kk : forall fd cmd arg eff m m' evs,
  check_fcntl fd cmd arg eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros fd cmd arg eff m m' evs H Hp.
  unfold check_fcntl in H.
  kk_frame H Hp.
Qed.

Lemma check_sched_setscheduler_kk : forall i pid policy param eff m m' evs,
  check_sched_setscheduler i pid policy param eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i pid policy param eff m m' evs H Hp.
  unfold check_sched_setscheduler in H.
  kk_frame H Hp.
Qed.

Lemma check_sched_getaffinity_kk : forall len eff m m' evs,
  check_sched_getaffinity len eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros len eff m m' evs H Hp.
  unfold check_sched_getaffinity in H.
  kk_frame H Hp.
Qed.

Lemma check_sched_yield_kk : forall eff m m' evs,
  check_sched_yield eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros eff m m' evs H Hp.
  unfold check_sched_yield in H.
  kk_frame H Hp.
Qed.

Lemma check_sigaltstack_kk : forall i uss uoss eff m m' evs,
  check_sigaltstack i uss uoss eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i uss uoss eff m m' evs H Hp.
  unfold check_sigaltstack in H.
  kk_frame H Hp.
Qed.

Lemma check_rt_sigaction_kk : forall i sig act oact ss eff m m' evs,
  check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i sig act oact ss eff m m' evs H Hp.
  unfold check_rt_sigaction in H.
  destruct (negb (bv_eqb ss (Z_to_bv 64 8))); cbv beta iota in H;
    [kk_frame H Hp|].
  destruct (Z.eqb (bv_unsigned sig) SIGPIPE); cbv beta iota in H.
  { exact (check_rt_sigaction_sigpipe_kk _ _ _ _ _ _ _ H Hp). }
  kk_frame H Hp.
Qed.

Lemma check_futex_kk : forall i uaddr op val utime eff m m' evs,
  check_futex i uaddr op val utime eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i uaddr op val utime eff m m' evs H Hp.
  unfold check_futex, check_futex_wake_private, check_futex_wait_private in H.
  kk_frame H Hp.
Qed.

Lemma check_set_robust_list_kk : forall len eff m m' evs,
  check_set_robust_list len eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros len eff m m' evs H Hp.
  unfold check_set_robust_list in H.
  kk_frame H Hp.
Qed.

Lemma check_clone_kk : forall flags eff m m' evs,
  check_clone flags eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros flags eff m m' evs H Hp.
  unfold check_clone, check_clone_resolve, check_clone_answer in H.
  kk_frame H Hp.
Qed.

Lemma check_clone3_kk : forall i uargs size eff m m' evs,
  check_clone3 i uargs size eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i uargs size eff m m' evs H Hp.
  unfold check_clone3, check_clone3_resolve, check_clone_answer in H.
  kk_frame H Hp.
Qed.

Lemma check_getsockname_kk : forall i fd eff m m' evs,
  check_getsockname i fd eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd eff m m' evs H Hp.
  unfold check_getsockname, check_stream_getname, check_ret_writes_copyins in H. cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_getpeername_kk : forall i fd eff m m' evs,
  check_getpeername i fd eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd eff m m' evs H Hp.
  unfold check_getpeername, check_stream_getname, check_ret_writes_copyins in H. cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_setsockopt_kk : forall i fd level optlen eff m m' evs,
  check_setsockopt i fd level optlen eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd level optlen eff m m' evs H Hp.
  unfold check_setsockopt, check_stream_setsockopt in H. cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_getsockopt_kk : forall i fd level optlenp eff m m' evs,
  check_getsockopt i fd level optlenp eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd level optlenp eff m m' evs H Hp.
  unfold check_getsockopt, check_stream_getsockopt, check_ret_writes_copyins in H.
  cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_shutdown_kk : forall fd how eff m m' evs,
  check_shutdown fd how eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros fd how eff m m' evs H Hp.
  unfold check_shutdown, check_stream_shutdown in H. cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_sendto_kk : forall i fd buf count flags addrp eff m m' evs,
  check_sendto i fd buf count flags addrp eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd buf count flags addrp eff m m' evs H Hp.
  unfold check_sendto, check_access_ok_zero, check_send_on_socket in H.
  kk_frame H Hp.
Qed.

Lemma check_sendmsg_kk : forall i fd msgp flags eff m m' evs,
  check_sendmsg i fd msgp flags eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd msgp flags eff m m' evs H Hp.
  unfold check_sendmsg, check_send_on_socket in H.
  kk_frame H Hp.
Qed.

Lemma check_socketpair_kk : forall i family type protocol sv eff m m' evs,
  check_socketpair i family type protocol sv eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i family type protocol sv eff m m' evs H Hp.
  unfold check_socketpair, check_socketpair_written, check_socketpair_faulted,
    check_socketpair_unix_written in H.
  cbv zeta in H.
  kk_frame H Hp.
Qed.

Lemma check_recvfrom_kk : forall i fd buf size eff m m' evs,
  check_recvfrom i fd buf size eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd buf size eff m m' evs H Hp.
  unfold check_recvfrom, check_access_ok_zero, check_recv_fd_answer in H.
  kk_frame H Hp.
Qed.

Lemma check_recvmsg_kk : forall fd flags eff m m' evs,
  check_recvmsg fd flags eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros fd flags eff m m' evs H Hp.
  unfold check_recvmsg, check_recv_fd_answer in H.
  kk_frame H Hp.
Qed.

Lemma check_connect_kk : forall i fd addrp addrlen eff m m' evs,
  check_connect i fd addrp addrlen eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fd addrp addrlen eff m m' evs H Hp.
  unfold check_connect in H.
  kk_frame H Hp.
Qed.

Lemma check_timerfd_create_kk : forall clkid flags eff m m' evs,
  check_timerfd_create clkid flags eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros clkid flags eff m m' evs H Hp.
  unfold check_timerfd_create in H.
  kk_frame H Hp.
Qed.

Lemma check_eventfd2_kk : forall i flags eff m m' evs,
  check_eventfd2 i flags eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i flags eff m m' evs H Hp.
  unfold check_eventfd2, check_new_fd_result in H.
  kk_frame H Hp.
Qed.

Lemma check_pipe2_kk : forall i fildes flags eff m m' evs,
  check_pipe2 i fildes flags eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i fildes flags eff m m' evs H Hp.
  unfold check_pipe2, pipe2_model in H.
  kk_frame H Hp.
Qed.

Lemma check_getcwd_kk : forall size eff m m' evs,
  check_getcwd size eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros size eff m m' evs H Hp.
  unfold check_getcwd in H.
  kk_frame H Hp.
Qed.

Lemma check_epoll_create1_kk : forall flags32 eff m m' evs,
  check_epoll_create1 flags32 eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros flags32 eff m m' evs H Hp.
  unfold check_epoll_create1 in H.
  kk_frame H Hp.
Qed.

Lemma check_epoll_ctl_kk : forall i epfd op32 tfd event eff m m' evs,
  check_epoll_ctl i epfd op32 tfd event eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i epfd op32 tfd event eff m m' evs H Hp.
  unfold check_epoll_ctl in H.
  kk_frame H Hp.
Qed.

Lemma check_epoll_pwait_kk : forall i epfd events maxevents32 sigmask sigsetsize eff m m' evs,
  check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i epfd events maxevents32 sigmask sigsetsize eff m m' evs H Hp.
  unfold check_epoll_pwait in H.
  kk_frame H Hp.
Qed.

(** * The table, the dispatcher *)

(** What one dispatcher arm owes, as a property of the table entry. *)
Definition arm_kern (c : CheckedArm) : Prop :=
  forall i eff m m' evs,
    ca_check c i eff m = CheckOk m' evs -> kern_post m m'.

(** Every arm discharges it.  As in [Checks.VmMapsDisjoint], the last
    alternative names the lemma an uncovered arm needs. *)
Lemma checked_table_kern : Forall arm_kern checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_kern).
  all: unfold arm_kern; intros i eff m m' evs H;
       autorewrite with arm_unfold in H.
  all: first
    [ fail
    | eapply check_brk_kk; eassumption
    | eapply check_mmap_kk; eassumption
    | eapply check_munmap_kk; eassumption
    | eapply check_mremap_kk; eassumption
    | eapply check_mprotect_kk; eassumption
    | eapply check_madvise_kk; eassumption
    | eapply check_read_kk; eassumption
    | eapply check_write_kk; eassumption
    | eapply check_pread64_kk; eassumption
    | eapply check_pwrite64_kk; eassumption
    | eapply check_readv_kk; eassumption
    | eapply check_writev_kk; eassumption
    | eapply check_pwritev2_kk; eassumption
    | eapply check_openat_kk; eassumption
    | eapply check_close_kk; eassumption
    | eapply check_lseek_kk; eassumption
    | eapply check_ftruncate_kk; eassumption
    | eapply check_ioctl_kk; eassumption
    | eapply check_readlinkat_kk; eassumption
    | eapply check_wait4_kk; eassumption
    | eapply check_fsync_kk; eassumption
    | eapply check_getdents64_kk; eassumption
    | eapply check_flock_kk; eassumption
    | eapply check_exit_kk; eassumption
    | eapply check_set_tid_address_kk; eassumption
    | eapply check_getpid_kk; eassumption
    | eapply check_gettid_kk; eassumption
    | eapply check_setsid_kk; eassumption
    | eapply check_uname_kk; eassumption
    | eapply check_prctl_kk; eassumption
    | eapply check_prlimit64_kk; eassumption
    | eapply check_getrandom_kk; eassumption
    | eapply check_gettimeofday_kk; eassumption
    | eapply check_clock_gettime_kk; eassumption
    | eapply check_clock_getres_kk; eassumption
    | eapply check_nanosleep_kk; eassumption
    | eapply check_dup_kk; eassumption
    | eapply check_dup3_kk; eassumption
    | eapply check_unlinkat_kk; eassumption
    | eapply check_faccessat_kk; eassumption
    | eapply check_faccessat2_kk; eassumption
    | eapply check_pselect6_kk; eassumption
    | eapply check_ppoll_kk; eassumption
    | eapply check_newfstatat_kk; eassumption
    | eapply check_fstat_kk; eassumption
    | eapply check_getid_kk; eassumption
    | eapply check_setid_kk; eassumption
    | eapply check_setresid_kk; eassumption
    | eapply check_getgroups_kk; eassumption
    | eapply check_setgroups_kk; eassumption
    | eapply check_socket_kk; eassumption
    | eapply check_bind_kk; eassumption
    | eapply check_listen_kk; eassumption
    | eapply check_accept4_kk; eassumption
    | eapply check_fcntl_kk; eassumption
    | eapply check_sched_setscheduler_kk; eassumption
    | eapply check_sched_getaffinity_kk; eassumption
    | eapply check_sched_yield_kk; eassumption
    | eapply check_sigaltstack_kk; eassumption
    | eapply check_rt_sigaction_kk; eassumption
    | eapply check_tkill_kk; eassumption
    | eapply check_tgkill_kk; eassumption
    | eapply check_rt_sigprocmask_kk; eassumption
    | eapply check_futex_kk; eassumption
    | eapply check_set_robust_list_kk; eassumption
    | eapply check_clone_kk; eassumption
    | eapply check_clone3_kk; eassumption
    | eapply check_getsockname_kk; eassumption
    | eapply check_getpeername_kk; eassumption
    | eapply check_setsockopt_kk; eassumption
    | eapply check_getsockopt_kk; eassumption
    | eapply check_shutdown_kk; eassumption
    | eapply check_sendto_kk; eassumption
    | eapply check_sendmsg_kk; eassumption
    | eapply check_socketpair_kk; eassumption
    | eapply check_recvfrom_kk; eassumption
    | eapply check_recvmsg_kk; eassumption
    | eapply check_connect_kk; eassumption
    | eapply check_timerfd_create_kk; eassumption
    | eapply check_eventfd2_kk; eassumption
    | eapply check_pipe2_kk; eassumption
    | eapply check_getcwd_kk; eassumption
    | eapply check_epoll_create1_kk; eassumption
    | eapply check_epoll_ctl_kk; eassumption
    | eapply check_epoll_pwait_kk; eassumption
    | fail 1 "checked_table_kern has no case for this dispatcher arm: give the new checker a *_kk"
             "lemma and add it to the list above" ].
Qed.

Theorem check_syscall_kern : forall i eff m m' evs,
  check_syscall i eff m = CheckOk m' evs -> kern_post m m'.
Proof.
  intros i eff m m' evs H. unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_kern as Hall.
  rewrite Forall_forall in Hall.
  exact (Hall c (lookup_ca_In _ _ _ Elk) i eff m m' evs H).
Qed.

(** * The specification and the step *)

Theorem kern_spec_ok : forall i mo eff mo' evs, kern_ok mo -> syscall_spec i mo (Ok eff mo' evs) ->
  kern_ok mo'.
Proof.
  intros i mo eff mo' evs Hp Hs.
  exact (check_syscall_kern i eff mo mo' evs (check_syscall_complete_ok i eff mo mo' evs Hs) Hp).
Qed.

Lemma kern_ok_with_vdso : forall v m, kern_ok m -> kern_ok (with_vdso v m).
Proof. intros v m P. refine (kern_ok_eq _ _ P _ _); reflexivity. Qed.

Lemma kern_ok_with_vdso_bump : forall m, kern_ok m -> kern_ok (with_vdso_bump m).
Proof. intros m P. refine (kern_ok_eq _ _ P _ _); reflexivity. Qed.

(* the materialization rebuilds the VM state by [with_vm_backing] (State.v:6850-6856) *)
Lemma kern_ok_materialize : forall m acc m',
  materialize_model_accesses m acc = Some m' -> kern_ok m -> kern_ok m'.
Proof.
  intros m acc m' H P. unfold materialize_model_accesses in H.
  destruct (materialize_accesses _ _ _ _ _) as [pages|]; [|discriminate H].
  injection H as <-. refine (kern_ok_eq _ _ P _ _); reflexivity.
Qed.

(* a machine step's first-touch accounting is a materialization (Run.v:460-470) *)
Lemma kern_ok_account : forall segs ms model ms' model',
  mi_account_step segs ms model = MachineOk (ms', model') -> kern_ok model -> kern_ok model'.
Proof.
  intros segs ms model ms' model' H P. unfold mi_account_step in H.
  match type of H with (match ?s with _ => _ end) = _ => destruct s as [r| |]; [|discriminate H|discriminate H] end.
  destruct (materialize_model_accesses model _) as [m1|] eqn:E; [|discriminate H].
  injection H as _ <-. exact (kern_ok_materialize _ _ _ E P).
Qed.

(** Every step of [Run.sstep_cfg] (Run.v:2250-2342), under any spurious-failure configuration. *)
Theorem kern_step : forall segs cfg c evs c', sstep_cfg segs cfg c evs (SNext c') ->
  kern_ok (cfg_model c) -> kern_ok (cfg_model c').
Proof.
  intros segs cfg c0 evs0 c' H. remember (SNext c') as st eqn:Est. revert Est.
  destruct H as [ms model ms' model' Hh Hp Ha
               | ms model Hh Hp Ha
               | ms model Hh Hp Ha Hv
               | ms model fn n eff model' model'' evs Hh Hp Ha Hv Hn Hs Hf Hh' Hm
               | ms model fn n eff model' evs Hh Hp Ha Hv Hn Hs Hf Hh' Hm
               | ms model fn Hh Hp Ha Hv Hu
               | ms model x8 eff model' model'' evs Hh Hp Hs Hsp Hh' Hm
               | ms model x8 eff model' evs Hh Hp Hs Hsp Hh' Hm
               | ms model x8 eff model' evs code Hh Hp Hs Hh' Hk
               | ms model x8 eff model' evs sg Hh Hp Hs Hk
               | ms model x8 Hh Hp Hs ];
    intros Est; try discriminate Est; injection Est as Ec; subst c';
    cbn [cfg_model]; intros P.
  - (* a machine step and its first-touch accounting *)
    exact (kern_ok_account _ _ _ _ _ Ha P).
  - (* a vDSO call *)
    apply kern_ok_with_vdso_bump.
    exact (kern_ok_materialize _ _ _ Hm (kern_spec_ok _ _ _ _ _ P Hs)).
  - (* a system call that returns *)
    exact (kern_ok_materialize _ _ _ Hm (kern_spec_ok _ _ _ _ _ P Hs)).
  - (* exit *)
    exact (kern_spec_ok _ _ _ _ _ P Hs).
  - (* killed *)
    exact (kern_spec_ok _ _ _ _ _ P Hs).
Qed.

End KK.

(** * The launch *)

(** [Run.init_config] (Run.v:1455-1459), with its eight image arguments: the kernel build is the
    input's ([State.m_kernel_init_model]) and the mmap base is the entry's. *)
Lemma kern_ok_init : forall vsegs pc ph sp brk0 mbase rnd lim inp,
  kern_ok (in_kernel inp) mbase (cfg_model (init_config vsegs pc ph sp brk0 mbase rnd lim inp)).
Proof.
  intros vsegs pc ph sp brk0 mbase rnd lim inp.
  unfold init_config. cbn [cfg_model]. split.
  - rewrite m_kernel_with_vdso. apply m_kernel_init_model.
  - reflexivity.
Qed.
