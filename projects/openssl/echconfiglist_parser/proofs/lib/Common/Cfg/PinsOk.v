(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11: the two pins every run keeps well formed.  The model pins the UTS name
   ([State.m_utsname]) and RLIMIT_CORE ([State.m_rlimit_core]) at their first observation, and
   later [uname] / [prlimit64] calls check what they deliver against the pin
   (Checks/Sys/Kernel/Sys.v:71-83, :93-126, :149-177).  A pin longer than the call's copy-out
   window (390 and 16 bytes) would let a later call write past the range its [in_wmem] gate read,
   so the clean-window invariant of [PairCleanAll] carries [pins_ok]: each pin, once set, is no
   longer than its window.
     - Both pins start [None] ([State.init_model], State.v:7807-7825; [Run.init_config] only adds
       the vDSO draw): [pins_ok_init_model], [pins_ok_init].
     - Every outcome of [Specs.syscall_spec] keeps [pins_ok] ([pins_spec_ok]): through
       [ExecutableSpecs.check_syscall_complete_ok] it is an accepted checker call, and every arm of
       [Checks.Sys.Dispatch.checked_table] is walked to its leaves.  The walk is the model's own
       (Checks/KillFree.v): the same per-arm unfolding and its [kf_step], closed here by
       [pk_close].  At a leaf the post-model either keeps both pins by conversion (every setter but
       [with_utsname] and [with_rlimit_core] copies them), or is one of the model wrappers with a
       rewrite lemma below, or is the pin store of [uname] (a name [utsname_wf] accepts: 390 bytes,
       Sys/Kernel/Sys.v:987-994) or of [prlimit64] (a pair [rlim64_wf] accepts, Sys/Kernel/Sys.v:326-328,
       or the 16 bytes [copy_bytes_map] read from [new_rlim]).
     - Every step of [Run.sstep_cfg] keeps it ([pins_step]): the first-touch accounting and the
       materialization keep [m_proc] and [m_lim] ([Run.mi_account_step_model_frame],
       [State.materialize_model_accesses_frame]), and [with_vdso_bump] rebuilds the VM part only. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs VmMapsDisjoint KillFree.
Import ListNotations.
Open Scope bv_scope.

(** * The invariant *)

Definition pins_ok (mo : Model) : Prop :=
  (forall b0, m_utsname mo = Some b0 -> (length b0 <= 390)%nat) /\
  (forall b0, m_rlimit_core mo = Some b0 -> (length b0 <= 16)%nat).

(** What one checker outcome owes. *)
Definition pins_post (m m' : Model) : Prop := pins_ok m -> pins_ok m'.

Lemma pins_ok_eq : forall m m', pins_ok m ->
  m_utsname m' = m_utsname m -> m_rlimit_core m' = m_rlimit_core m -> pins_ok m'.
Proof.
  intros m m' [Hu Hr] Eu Er. split; intros b0 E.
  - rewrite Eu in E. exact (Hu b0 E).
  - rewrite Er in E. exact (Hr b0 E).
Qed.

Lemma pins_ok_frame : forall m m', pins_ok m ->
  m_proc m' = m_proc m -> m_lim m' = m_lim m -> pins_ok m'.
Proof.
  intros m m' P Ep El. apply (pins_ok_eq m m' P).
  - unfold m_utsname. rewrite Ep. reflexivity.
  - unfold m_rlimit_core. rewrite El. reflexivity.
Qed.

(** * The two stores *)

Lemma pk_uts_len : forall bs, utsname_wf bs = true -> (length bs <= 390)%nat.
Proof.
  intros bs Hw. unfold utsname_wf in Hw.
  repeat (apply andb_prop in Hw; destruct Hw as [Hw _]).
  apply Nat.eqb_eq in Hw. rewrite Hw. apply Nat.le_refl.
Qed.

Lemma pk_rlim_len : forall bs, rlim64_wf bs = true -> (length bs <= 16)%nat.
Proof.
  intros bs Hw. unfold rlim64_wf in Hw.
  apply andb_prop in Hw. destruct Hw as [Hw _].
  apply Nat.eqb_eq in Hw. rewrite Hw. apply Nat.le_refl.
Qed.

(** [uname]'s first answer becomes the pin (Checks/Sys/Kernel/Sys.v:157). *)
Lemma pins_ok_uts_wf : forall bs m, utsname_wf bs = true -> pins_ok m ->
  pins_ok (with_utsname bs m).
Proof.
  intros bs m Hw [Hu Hr]. split; intros b0 E.
  - rewrite m_utsname_with_utsname in E. injection E as <-. exact (pk_uts_len bs Hw).
  - rewrite m_rlimit_core_with_utsname in E. exact (Hr b0 E).
Qed.

(** [prlimit64]'s first read becomes the pin (Checks/Sys/Kernel/Sys.v:79). *)
Lemma pins_ok_rlim_wf : forall bs m, rlim64_wf bs = true -> pins_ok m ->
  pins_ok (with_rlimit_core bs m).
Proof.
  intros bs m Hw [Hu Hr]. split; intros b0 E.
  - rewrite m_utsname_with_rlimit_core in E. exact (Hu b0 E).
  - rewrite m_rlimit_core_with_rlimit_core in E. injection E as <-. exact (pk_rlim_len bs Hw).
Qed.

(** [prlimit64]'s write stores the bytes it copied in (Checks/Sys/Kernel/Sys.v:112-124). *)
Lemma pins_ok_rlim_copy : forall (mp : word -> option byte) (a : word) (k : Z)
    (w : list byte) (m : Model),
  copy_bytes_map mp a k = Some w -> (0 <= k <= 16)%Z -> pins_ok m ->
  pins_ok (with_rlimit_core w m).
Proof.
  intros mp a k w m Hc Hk [Hu Hr]. split; intros b0 E.
  - rewrite m_utsname_with_rlimit_core in E. exact (Hu b0 E).
  - rewrite m_rlimit_core_with_rlimit_core in E. injection E as <-.
    unfold copy_bytes_map in Hc.
    destruct (access_okb a k); cbv beta iota in Hc; [|discriminate Hc].
    apply read_bytes_map_length in Hc.
    assert (Hb : (16 < two_pow_64)%Z) by (apply Z.ltb_lt; reflexivity).
    rewrite bv_unsigned_Z_to_bv_u64 in Hc by lia.
    lia.
Qed.

(** * The model wrappers a post-model can be (their [m_proc] twins: Checks/KillFree.v:197-223) *)

Lemma pk_u_forget : forall rs m, m_utsname (forget_vm_ranges rs m) = m_utsname m.
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. reflexivity.
Qed.

Lemma pk_r_forget : forall rs m, m_rlimit_core (forget_vm_ranges rs m) = m_rlimit_core m.
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. reflexivity.
Qed.

Lemma pk_u_brk : forall m req r, m_utsname (with_brk_next m req r) = m_utsname m.
Proof. intros m req r. unfold with_brk_next. cbv zeta. rewrite pk_u_forget. reflexivity. Qed.

Lemma pk_r_brk : forall m req r, m_rlimit_core (with_brk_next m req r) = m_rlimit_core m.
Proof. intros m req r. unfold with_brk_next. cbv zeta. rewrite pk_r_forget. reflexivity. Qed.

Lemma pk_u_backing : forall flags a n m, m_utsname (with_mmap_backing flags a n m) = m_utsname m.
Proof. intros flags a n m. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma pk_r_backing : forall flags a n m,
  m_rlimit_core (with_mmap_backing flags a n m) = m_rlimit_core m.
Proof. intros flags a n m. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma pk_u_repl : forall flags a n m, m_utsname (with_mmap_replacement flags a n m) = m_utsname m.
Proof. intros flags a n m. unfold with_mmap_replacement. rewrite pk_u_backing. reflexivity. Qed.

Lemma pk_r_repl : forall flags a n m,
  m_rlimit_core (with_mmap_replacement flags a n m) = m_rlimit_core m.
Proof. intros flags a n m. unfold with_mmap_replacement. rewrite pk_r_backing. reflexivity. Qed.

(** [ReadWrite.raise_sigpipe] (Sys/Fs/ReadWrite.v:1350-1355), split as
    [VmMapsDisjoint.check_sigpipe_writev_frame] splits it. *)
Lemma pk_u_raise : forall m, m_utsname (raise_sigpipe m) = m_utsname m.
Proof.
  intros m. unfold raise_sigpipe.
  destruct (m_sigpipe_default m), (sigpipe_blocked (m_sigmask m)); reflexivity.
Qed.

Lemma pk_r_raise : forall m, m_rlimit_core (raise_sigpipe m) = m_rlimit_core m.
Proof.
  intros m. unfold raise_sigpipe.
  destruct (m_sigpipe_default m), (sigpipe_blocked (m_sigmask m)); reflexivity.
Qed.

(** [Signal.sigmask_deliver_model] (Sys/Kernel/Signal.v:1371-1376). *)
Lemma pk_u_sigmask : forall new m, m_utsname (sigmask_deliver_model new m) = m_utsname m.
Proof.
  intros new m. unfold sigmask_deliver_model.
  destruct (m_sigabrt_pending m), (sigabrt_blocked new), (m_sigpipe_pending m),
    (sigpipe_blocked new); reflexivity.
Qed.

Lemma pk_r_sigmask : forall new m, m_rlimit_core (sigmask_deliver_model new m) = m_rlimit_core m.
Proof.
  intros new m. unfold sigmask_deliver_model.
  destruct (m_sigabrt_pending m), (sigabrt_blocked new), (m_sigpipe_pending m),
    (sigpipe_blocked new); reflexivity.
Qed.

Create HintDb pk_kept.
#[local] Hint Rewrite pk_u_forget pk_r_forget pk_u_brk pk_r_brk pk_u_backing pk_r_backing
  pk_u_repl pk_r_repl pk_u_raise pk_r_raise pk_u_sigmask pk_r_sigmask : pk_kept.

(** * Closing a leaf of a checker walk *)

(* One pin of the post-model against the same pin of [m]: by conversion through the setters, or
   through a wrapper above. *)
Ltac pk_fld := first [ reflexivity | (autorewrite with pk_kept; reflexivity) ].

(* The post-model is [m] itself, or keeps both pins, or is one of the two stores; [Hp] is
   [pins_ok m]. *)
Ltac pk_close Hp :=
  first
  [ exact Hp
  | lazymatch goal with
    | |- pins_ok (with_utsname _ _) => apply pins_ok_uts_wf; [assumption | exact Hp]
    | |- pins_ok (with_rlimit_core ?w _) =>
        first
        [ (apply pins_ok_rlim_wf; [assumption | exact Hp])
        | match goal with
          | Hc : copy_bytes_map _ _ _ = Some w |- _ =>
              apply (pins_ok_rlim_copy _ _ _ _ _ Hc); [lia | exact Hp]
          end ]
    | |- _ => fail
    end
  | (refine (pins_ok_eq _ _ Hp _ _); pk_fld) ].

(** * The sub-checkers [kf_step] does not open (Checks/KillFree.v:258-475) *)

Lemma check_efault_or_pk : forall fb eff m m' evs,
  check_efault_or fb eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros fb eff m m' evs H Hp. unfold check_efault_or in H.
  repeat kf_step H; pk_close Hp.
Qed.

(** The SIGPIPE answer is over [raise_sigpipe m] (Checks/Sys/Fs/ReadWrite.v:255-258,
    :5183-5186); unlike [KillFree], nothing here closes the gate, so the branch is walked. *)
Lemma check_sigpipe_write_pk : forall eff m m' evs,
  check_sigpipe_write eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros eff m m' evs H Hp. unfold check_sigpipe_write in H.
  repeat kf_step H; pk_close Hp.
Qed.

Lemma check_sigpipe_writev_pk : forall reads eff m m' evs,
  check_sigpipe_writev reads eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros reads eff m m' evs H Hp. unfold check_sigpipe_writev in H.
  repeat kf_step H; pk_close Hp.
Qed.

Ltac pk_stream_base H Hp :=
  first
  [ exact (check_efault_or_pk _ _ _ _ _ H Hp)
  | exact (check_sigpipe_write_pk _ _ _ _ H Hp) ].

Lemma check_stream_read_empty_pk : forall fd id side st nonblock eff m m' evs,
  check_stream_read_empty fd id side st nonblock eff m = CheckOk m' evs ->
  pins_post m m'.
Proof.
  intros fd id side st nonblock eff m m' evs H Hp.
  unfold check_stream_read_empty, check_stream_read_reset in H. cbv beta iota zeta in H.
  repeat (kf_step H || pk_stream_base H Hp); pk_close Hp.
Qed.

Lemma check_stream_read_pk :
  forall fd id side st nonblock buf count i eff m m' evs,
  check_stream_read fd id side st nonblock buf count i eff m = CheckOk m' evs ->
  pins_post m m'.
Proof.
  intros fd id side st nonblock buf count i eff m m' evs H Hp.
  unfold check_stream_read, check_stream_read_empty, check_stream_read_reset in H. cbv beta iota zeta in H.
  repeat (kf_step H || pk_stream_base H Hp); pk_close Hp.
Qed.

Lemma check_stream_send_pk :
  forall id side st nonblock nosignal n src ledger eff m m' evs,
  check_stream_send id side st nonblock nosignal n src ledger eff m = CheckOk m' evs ->
  pins_post m m'.
Proof.
  intros id side st nonblock nosignal n src ledger eff m m' evs H Hp.
  unfold check_stream_send in H. cbv beta iota zeta in H.
  repeat (kf_step H || pk_stream_base H Hp); pk_close Hp.
Qed.

Lemma check_stream_write_pk :
  forall id side st nonblock nosignal buf count i eff m m' evs,
  check_stream_write id side st nonblock nosignal buf count i eff m = CheckOk m' evs ->
  pins_post m m'.
Proof.
  intros id side st nonblock nosignal buf count i eff m m' evs H.
  unfold check_stream_write in H. exact (check_stream_send_pk _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

Ltac pk_stream H Hp :=
  first
  [ exact (check_stream_read_pk _ _ _ _ _ _ _ _ _ _ _ _ H Hp)
  | exact (check_stream_read_empty_pk _ _ _ _ _ _ _ _ _ H Hp)
  | exact (check_stream_write_pk _ _ _ _ _ _ _ _ _ _ _ _ H Hp)
  | exact (check_stream_send_pk _ _ _ _ _ _ _ _ _ _ _ _ H Hp) ].

(** [rt_sigaction] on SIGPIPE, as [KillFree.check_rt_sigaction_sigpipe_kf] takes it apart; the
    install ([State.with_sigpipe_install], State.v:5493-5503) copies both pins. *)
Lemma check_rt_sigaction_sigpipe_pk : forall i act oact eff m m' evs,
  check_rt_sigaction_sigpipe i act oact eff m = CheckOk m' evs ->
  pins_post m m'.
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
  refine (pins_ok_eq _ _ Hp _ _); reflexivity.
Qed.

(** The new-descriptor answer of [openat] and its kin: the installed model is [mk fd]. *)
Lemma check_open_result_pk : forall eff m mk m' evs,
  check_open_result eff m mk = CheckOk m' evs ->
  (forall fd, pins_post m (mk fd)) ->
  pins_post m m'.
Proof.
  intros eff m mk m' evs H Hmk Hp.
  unfold check_open_result, check_new_fd_result in H.
  repeat kf_step H.
  all: first [ pk_close Hp | exact (Hmk _ Hp) ].
Qed.

Lemma check_readv_imported_pk : forall i fd r iovs0 eff m m' evs,
  check_readv_imported i fd r iovs0 eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd r iovs0 eff m m' evs H Hp.
  unfold check_readv_imported in H. cbv beta iota zeta in H.
  repeat (kf_step H
          || exact (check_efault_or_pk _ _ _ _ _ H Hp)
          || pk_stream H Hp
          || elim (check_readv_gap_frame _ _ H));
  pk_close Hp.
Qed.

Ltac pk_done H Hp :=
  first
  [ exact (check_efault_or_pk _ _ _ _ _ H Hp)
  | exact (check_sigpipe_write_pk _ _ _ _ H Hp)
  | exact (check_sigpipe_writev_pk _ _ _ _ _ H Hp)
  | elim (check_readv_gap_frame _ _ H)
  | pk_stream H Hp
  | exact (check_readv_imported_pk _ _ _ _ _ _ _ _ H Hp)
  | (refine (check_open_result_pk _ _ _ _ _ H _ Hp);
     let fd := fresh "fd" in let Ho := fresh "Ho" in
     intros fd Ho; pk_close Ho) ].

(* [KillFree.kf_frame] with this file's leaf closer. *)
Ltac pk_frame H Hp :=
  cbv beta iota zeta in H;
  repeat (kf_step H || pk_done H Hp); pk_close Hp.

(** * The arms, each unfolded as [Checks/KillFree.v] unfolds it *)

(** [tkill] and [tgkill] (Checks/Sys/Kernel/Signal.v:1166-1211): the abort leaves the pins. *)
Lemma check_tkill_pk : forall pid sig eff m m' evs,
  check_tkill pid sig eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros pid sig eff m m' evs H Hp.
  unfold check_tkill, check_tkill_self, check_send_sigabrt in H.
  pk_frame H Hp.
Qed.

Lemma check_tgkill_pk : forall tgid pid sig eff m m' evs,
  check_tgkill tgid pid sig eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros tgid pid sig eff m m' evs H Hp.
  unfold check_tgkill, check_tkill_self, check_send_sigabrt in H.
  pk_frame H Hp.
Qed.

(** [rt_sigprocmask] (Checks/Sys/Kernel/Signal.v:832-856): the post-model is
    [sigmask_deliver_model _ m] ([pk_u_sigmask], [pk_r_sigmask]). *)
Lemma check_rt_sigprocmask_pk : forall i how nset oset ss eff m m' evs,
  check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i how nset oset ss eff m m' evs H Hp.
  unfold check_rt_sigprocmask in H. cbv zeta in H.
  pk_frame H Hp.
Qed.

(** The other arms: [Checks/KillFree.v]'s unfolding, one for one. *)

Lemma check_brk_pk : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros req [ret ws zs us cs ci] m m' evs H Hp.
  unfold check_brk in H.
  pk_frame H Hp.
Qed.

Lemma check_mmap_pk : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H Hp.
  unfold check_mmap, check_mmap_fixed_overflow in H.
  cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_munmap_pk : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H Hp.
  unfold check_munmap in H.
  cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_mremap_pk : forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H Hp.
  unfold check_mremap in H.
  cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_mprotect_pk : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros addr len prot [ret ws zs us cs ci] m m' evs H Hp.
  unfold check_mprotect in H.
  cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_madvise_pk : forall addr len advice eff m m' evs,
  check_madvise addr len advice eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros addr len advice [ret ws zs us cs ci] m m' evs H Hp.
  unfold check_madvise in H.
  cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_read_pk : forall i fd buf count eff m m' evs,
  check_read i fd buf count eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd buf count eff m m' evs H Hp.
  unfold check_read, check_read_urandom, check_socket_pending_error, check_access_ok_zero,
    check_eventfd_read in H.
  cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_write_pk : forall i fd buf count eff m m' evs,
  check_write i fd buf count eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd buf count eff m m' evs H Hp.
  unfold check_write, check_write_fault_extend, check_access_ok_zero,
    check_eventfd_write, check_anon_write_fault, check_anon_fault_extend,
    anon_place_fds in H.
  cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_pread64_pk : forall i fd buf count pos eff m m' evs,
  check_pread64 i fd buf count pos eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd buf count pos eff m m' evs H Hp.
  unfold check_pread64, check_read_urandom in H.
  cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_pwrite64_pk : forall i fd buf count pos eff m m' evs,
  check_pwrite64 i fd buf count pos eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd buf count pos eff m m' evs H Hp.
  unfold check_pwrite64, check_write_fault_extend, check_anon_fault_extend in H.
  cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_readv_pk : forall i fd iov iovcnt eff m m' evs,
  check_readv i fd iov iovcnt eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd iov iovcnt eff m m' evs H Hp.
  unfold check_readv in H.
  pk_frame H Hp.
Qed.

Lemma check_writev_pk : forall i fd iov iovcnt eff m m' evs,
  check_writev i fd iov iovcnt eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd iov iovcnt eff m m' evs H Hp.
  unfold check_writev, check_write_fault_extend, check_anon_write_fault,
    check_anon_fault_extend, anon_place_fds in H.
  cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_pwritev2_pk :
  forall i fd iov iovcnt pos_l pos_h flags eff m m' evs,
  check_pwritev2 i fd iov iovcnt pos_l pos_h flags eff m = CheckOk m' evs ->
  pins_post m m'.
Proof.
  intros i fd iov iovcnt pos_l pos_h flags eff m m' evs H Hp.
  unfold check_pwritev2, check_anon_fault_extend in H.
  cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_openat_pk : forall i dirfd pathp flags eff m m' evs,
  check_openat i dirfd pathp flags eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i dirfd pathp flags eff m m' evs H Hp.
  unfold check_openat, Open.check_openat_body, Open.check_openat_resolved, Open.check_openat_sep,
    Open.check_openat_localtime, Open.check_openat_devnull, Open.check_open_devnull,
    Open.check_openat_urandom, Open.check_open_urandom, Open.check_openat_procfd,
    Open.check_openat_tmp, Open.check_openat_read, Open.check_openat_create, Open.check_openat_excl,
    Open.check_openat_dir, Open.check_openat_append, Open.check_openat_rdwr,
    Open.check_openat_rdwr_excl, check_create_wronly, check_open_append, check_open_rdwr in H.
  pk_frame H Hp.
Qed.

Lemma check_close_pk : forall fd eff m m' evs,
  check_close fd eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros fd eff m m' evs H Hp.
  unfold check_close in H.
  pk_frame H Hp.
Qed.

Lemma check_lseek_pk : forall fd off whence eff m m' evs,
  check_lseek fd off whence eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros fd off whence eff m m' evs H Hp.
  unfold check_lseek in H.
  pk_frame H Hp.
Qed.

Lemma check_ftruncate_pk : forall fd len eff m m' evs,
  check_ftruncate fd len eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros fd len eff m m' evs H Hp.
  unfold check_ftruncate in H.
  pk_frame H Hp.
Qed.

Lemma check_ioctl_pk : forall i fd req eff m m' evs,
  check_ioctl i fd req eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd req eff m m' evs H Hp.
  unfold check_ioctl, check_siocgifindex, check_ifreq_writeback in H.
  pk_frame H Hp.
Qed.

Lemma check_readlinkat_pk : forall dirfd eff m m' evs,
  check_readlinkat dirfd eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros dirfd eff m m' evs H Hp.
  unfold check_readlinkat in H.
  pk_frame H Hp.
Qed.

Lemma check_wait4_pk : forall i upid stat_addr options rusage eff m m' evs,
  check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i upid stat_addr options rusage eff m m' evs H Hp.
  unfold check_wait4 in H.
  pk_frame H Hp.
Qed.

Lemma check_fsync_pk : forall fd eff m m' evs,
  check_fsync fd eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros fd eff m m' evs H Hp.
  unfold check_fsync in H.
  pk_frame H Hp.
Qed.

Lemma check_getdents64_pk : forall fd count eff m m' evs,
  check_getdents64 fd count eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros fd count eff m m' evs H Hp.
  unfold check_getdents64 in H.
  pk_frame H Hp.
Qed.

Lemma check_flock_pk : forall fd cmd eff m m' evs,
  check_flock fd cmd eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros fd cmd eff m m' evs H Hp.
  unfold check_flock in H.
  pk_frame H Hp.
Qed.

Lemma check_exit_pk : forall code eff m m' evs,
  check_exit code eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros code eff m m' evs H Hp.
  unfold check_exit in H.
  pk_frame H Hp.
Qed.

Lemma check_set_tid_address_pk : forall eff m m' evs,
  check_set_tid_address eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros eff m m' evs H Hp.
  unfold check_set_tid_address in H.
  pk_frame H Hp.
Qed.

Lemma check_getpid_pk : forall eff m m' evs,
  check_getpid eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  exact check_set_tid_address_pk.
Qed.

Lemma check_gettid_pk : forall eff m m' evs,
  check_gettid eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  exact check_set_tid_address_pk.
Qed.

Lemma check_setsid_pk : forall eff m m' evs,
  check_setsid eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros eff m m' evs H Hp.
  unfold check_setsid in H.
  pk_frame H Hp.
Qed.

Lemma check_uname_pk : forall i name eff m m' evs,
  check_uname i name eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i name eff m m' evs H Hp.
  unfold check_uname, check_uname_copy in H.
  pk_frame H Hp.
Qed.

Lemma check_prctl_pk : forall option_ arg2 eff m m' evs,
  check_prctl option_ arg2 eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros option_ arg2 eff m m' evs H Hp.
  unfold check_prctl in H.
  pk_frame H Hp.
Qed.

Lemma check_prlimit64_pk : forall i pid resource new_rlim old_rlim eff m m' evs,
  check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i pid resource new_rlim old_rlim eff m m' evs H Hp.
  unfold check_prlimit64, check_rlim64_read in H.
  pk_frame H Hp.
Qed.

Lemma check_getrandom_pk : forall i buf cap flags eff m m' evs,
  check_getrandom i buf cap flags eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i buf cap flags eff m m' evs H Hp.
  unfold check_getrandom, check_getrandom_zero in H.
  pk_frame H Hp.
Qed.

Lemma check_gettimeofday_pk : forall i tv tz eff m m' evs,
  check_gettimeofday i tv tz eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i tv tz eff m m' evs H Hp.
  unfold check_gettimeofday in H.
  pk_frame H Hp.
Qed.

Lemma check_clock_gettime_pk : forall i clkid tp eff m m' evs,
  check_clock_gettime i clkid tp eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i clkid tp eff m m' evs H Hp.
  unfold check_clock_gettime in H.
  pk_frame H Hp.
Qed.

Lemma check_clock_getres_pk : forall i clkid tp eff m m' evs,
  check_clock_getres i clkid tp eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i clkid tp eff m m' evs H Hp.
  unfold check_clock_getres, check_clock_getres_result in H.
  pk_frame H Hp.
Qed.

Lemma check_nanosleep_pk : forall i rqtp rmtp eff m m' evs,
  check_nanosleep i rqtp rmtp eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i rqtp rmtp eff m m' evs H Hp.
  unfold check_nanosleep in H.
  pk_frame H Hp.
Qed.

Lemma check_dup_pk : forall oldfd eff m m' evs,
  check_dup oldfd eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros oldfd eff m m' evs H Hp.
  unfold check_dup, check_dup_result in H.
  pk_frame H Hp.
Qed.

Lemma check_dup3_pk : forall oldfd newfd flags eff m m' evs,
  check_dup3 oldfd newfd flags eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros oldfd newfd flags eff m m' evs H Hp.
  unfold check_dup3 in H.
  pk_frame H Hp.
Qed.

Lemma check_unlinkat_pk : forall i dirfd pathp flags eff m m' evs,
  check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i dirfd pathp flags eff m m' evs H Hp.
  unfold check_unlinkat, Namei.check_unlinkat_body, Namei.check_unlinkat_tmp, Namei.check_unlink_found, check_unlink_result,
    Namei.check_unlink_open_tmp, check_unlink_open_result, check_unlink_type_result in H.
  pk_frame H Hp.
Qed.

Lemma check_faccessat_pk : forall i dirfd pathp mode eff m m' evs,
  check_faccessat i dirfd pathp mode eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i dirfd pathp mode eff m m' evs H Hp.
  unfold check_faccessat, Open.check_faccessat_body, check_access_exists in H.
  pk_frame H Hp.
Qed.

Lemma check_faccessat2_pk : forall i dirfd pathp mode flags eff m m' evs,
  check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i dirfd pathp mode flags eff m m' evs H Hp.
  unfold check_faccessat2, Open.check_faccessat_body, check_access_exists in H.
  pk_frame H Hp.
Qed.

Lemma check_pselect6_pk : forall i n32 inp outp exp tsp sig eff m m' evs,
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i n32 inp outp exp tsp sig eff m m' evs H Hp.
  unfold check_pselect6, check_pselect_answer in H.
  pk_frame H Hp.
Qed.

Lemma check_ppoll_pk : forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H Hp.
  unfold check_ppoll, check_pselect_answer in H.
  pk_frame H Hp.
Qed.

Lemma check_newfstatat_pk : forall i dirfd pathp flag eff m m' evs,
  check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i dirfd pathp flag eff m m' evs H Hp.
  unfold check_newfstatat in H.
  pk_frame H Hp.
Qed.

Lemma check_fstat_pk : forall i fd statbuf eff m m' evs,
  check_fstat i fd statbuf eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd statbuf eff m m' evs H Hp.
  unfold check_fstat, check_fstat_file, check_fstat_devnull, check_fstat_urandom,
    check_fstat_chrdev, check_fstat_deliver, check_fstat_deliver_by,
    check_fstat_anon, check_fstat_anon_deliver in H.
  pk_frame H Hp.
Qed.

Lemma check_getid_pk : forall sel eff m m' evs,
  check_getid sel eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros sel eff m m' evs H Hp.
  unfold check_getid in H.
  pk_frame H Hp.
Qed.

Lemma check_setid_pk : forall get put user v eff m m' evs,
  check_setid get put user v eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros get put user v eff m m' evs H Hp.
  unfold check_setid, check_setid_result in H.
  pk_frame H Hp.
Qed.

Lemma check_setresid_pk : forall get put user r e sv eff m m' evs,
  check_setresid get put user r e sv eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros get put user r e sv eff m m' evs H Hp.
  unfold check_setresid, check_setid_result in H.
  pk_frame H Hp.
Qed.

Lemma check_getgroups_pk : forall gidsetsize eff m m' evs,
  check_getgroups gidsetsize eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros gidsetsize eff m m' evs H Hp.
  unfold check_getgroups in H.
  pk_frame H Hp.
Qed.

Lemma check_setgroups_pk : forall eff m m' evs,
  check_setgroups eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros eff m m' evs H Hp.
  unfold check_setgroups in H.
  pk_frame H Hp.
Qed.

Lemma check_socket_pk : forall domain type protocol eff m m' evs,
  check_socket domain type protocol eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros domain type protocol eff m m' evs H Hp.
  unfold check_socket, check_new_fd_result, check_errno_or_list in H.
  pk_frame H Hp.
Qed.

Lemma check_bind_pk : forall i fd addrp addrlen eff m m' evs,
  check_bind i fd addrp addrlen eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd addrp addrlen eff m m' evs H Hp.
  unfold check_bind, check_errno_or_success in H.
  pk_frame H Hp.
Qed.

Lemma check_listen_pk : forall fd backlog eff m m' evs,
  check_listen fd backlog eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros fd backlog eff m m' evs H Hp.
  unfold check_listen, check_errno_or_success, check_errno_only in H.
  pk_frame H Hp.
Qed.

Lemma check_accept4_pk : forall fd addrp addrlenp flags eff m m' evs,
  check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros fd addrp addrlenp flags eff m m' evs H Hp.
  unfold check_accept4, check_new_fd_result, check_errno_or_success, check_errno_only, check_errno_or_list in H.
  pk_frame H Hp.
Qed.

Lemma check_fcntl_pk : forall fd cmd arg eff m m' evs,
  check_fcntl fd cmd arg eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros fd cmd arg eff m m' evs H Hp.
  unfold check_fcntl in H.
  pk_frame H Hp.
Qed.

Lemma check_sched_setscheduler_pk : forall i pid policy param eff m m' evs,
  check_sched_setscheduler i pid policy param eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i pid policy param eff m m' evs H Hp.
  unfold check_sched_setscheduler in H.
  pk_frame H Hp.
Qed.

Lemma check_sched_getaffinity_pk : forall len eff m m' evs,
  check_sched_getaffinity len eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros len eff m m' evs H Hp.
  unfold check_sched_getaffinity in H.
  pk_frame H Hp.
Qed.

Lemma check_sched_yield_pk : forall eff m m' evs,
  check_sched_yield eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros eff m m' evs H Hp.
  unfold check_sched_yield in H.
  pk_frame H Hp.
Qed.

Lemma check_sigaltstack_pk : forall i uss uoss eff m m' evs,
  check_sigaltstack i uss uoss eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i uss uoss eff m m' evs H Hp.
  unfold check_sigaltstack in H.
  pk_frame H Hp.
Qed.

Lemma check_rt_sigaction_pk : forall i sig act oact ss eff m m' evs,
  check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i sig act oact ss eff m m' evs H Hp.
  unfold check_rt_sigaction in H.
  destruct (negb (bv_eqb ss (Z_to_bv 64 8))); cbv beta iota in H;
    [pk_frame H Hp|].
  destruct (Z.eqb (bv_unsigned sig) SIGPIPE); cbv beta iota in H.
  { exact (check_rt_sigaction_sigpipe_pk _ _ _ _ _ _ _ H Hp). }
  pk_frame H Hp.
Qed.

Lemma check_futex_pk : forall i uaddr op val utime eff m m' evs,
  check_futex i uaddr op val utime eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i uaddr op val utime eff m m' evs H Hp.
  unfold check_futex, check_futex_wake_private, check_futex_wait_private in H.
  pk_frame H Hp.
Qed.

Lemma check_set_robust_list_pk : forall len eff m m' evs,
  check_set_robust_list len eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros len eff m m' evs H Hp.
  unfold check_set_robust_list in H.
  pk_frame H Hp.
Qed.

Lemma check_clone_pk : forall flags eff m m' evs,
  check_clone flags eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros flags eff m m' evs H Hp.
  unfold check_clone, check_clone_resolve, check_clone_answer in H.
  pk_frame H Hp.
Qed.

Lemma check_clone3_pk : forall i uargs size eff m m' evs,
  check_clone3 i uargs size eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i uargs size eff m m' evs H Hp.
  unfold check_clone3, check_clone3_resolve, check_clone_answer in H.
  pk_frame H Hp.
Qed.

Lemma check_getsockname_pk : forall i fd eff m m' evs,
  check_getsockname i fd eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd eff m m' evs H Hp.
  unfold check_getsockname, check_stream_getname, check_ret_writes_copyins in H. cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_getpeername_pk : forall i fd eff m m' evs,
  check_getpeername i fd eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd eff m m' evs H Hp.
  unfold check_getpeername, check_stream_getname, check_ret_writes_copyins in H. cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_setsockopt_pk : forall i fd level optlen eff m m' evs,
  check_setsockopt i fd level optlen eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd level optlen eff m m' evs H Hp.
  unfold check_setsockopt, check_stream_setsockopt in H. cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_getsockopt_pk : forall i fd level optlenp eff m m' evs,
  check_getsockopt i fd level optlenp eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd level optlenp eff m m' evs H Hp.
  unfold check_getsockopt, check_stream_getsockopt, check_ret_writes_copyins in H.
  cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_shutdown_pk : forall fd how eff m m' evs,
  check_shutdown fd how eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros fd how eff m m' evs H Hp.
  unfold check_shutdown, check_stream_shutdown in H. cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_sendto_pk : forall i fd buf count flags addrp eff m m' evs,
  check_sendto i fd buf count flags addrp eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd buf count flags addrp eff m m' evs H Hp.
  unfold check_sendto, check_access_ok_zero, check_send_on_socket in H.
  pk_frame H Hp.
Qed.

Lemma check_sendmsg_pk : forall i fd msgp flags eff m m' evs,
  check_sendmsg i fd msgp flags eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd msgp flags eff m m' evs H Hp.
  unfold check_sendmsg, check_send_on_socket in H.
  pk_frame H Hp.
Qed.

Lemma check_socketpair_pk : forall i family type protocol sv eff m m' evs,
  check_socketpair i family type protocol sv eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i family type protocol sv eff m m' evs H Hp.
  unfold check_socketpair, check_socketpair_written, check_socketpair_faulted,
    check_socketpair_unix_written in H.
  cbv zeta in H.
  pk_frame H Hp.
Qed.

Lemma check_recvfrom_pk : forall i fd buf size eff m m' evs,
  check_recvfrom i fd buf size eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd buf size eff m m' evs H Hp.
  unfold check_recvfrom, check_access_ok_zero, check_recv_fd_answer in H.
  pk_frame H Hp.
Qed.

Lemma check_recvmsg_pk : forall fd flags eff m m' evs,
  check_recvmsg fd flags eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros fd flags eff m m' evs H Hp.
  unfold check_recvmsg, check_recv_fd_answer in H.
  pk_frame H Hp.
Qed.

Lemma check_connect_pk : forall i fd addrp addrlen eff m m' evs,
  check_connect i fd addrp addrlen eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fd addrp addrlen eff m m' evs H Hp.
  unfold check_connect in H.
  pk_frame H Hp.
Qed.

Lemma check_timerfd_create_pk : forall clkid flags eff m m' evs,
  check_timerfd_create clkid flags eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros clkid flags eff m m' evs H Hp.
  unfold check_timerfd_create in H.
  pk_frame H Hp.
Qed.

Lemma check_eventfd2_pk : forall i flags eff m m' evs,
  check_eventfd2 i flags eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i flags eff m m' evs H Hp.
  unfold check_eventfd2, check_new_fd_result in H.
  pk_frame H Hp.
Qed.

Lemma check_pipe2_pk : forall i fildes flags eff m m' evs,
  check_pipe2 i fildes flags eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i fildes flags eff m m' evs H Hp.
  unfold check_pipe2, pipe2_model in H.
  pk_frame H Hp.
Qed.

Lemma check_getcwd_pk : forall size eff m m' evs,
  check_getcwd size eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros size eff m m' evs H Hp.
  unfold check_getcwd in H.
  pk_frame H Hp.
Qed.

Lemma check_epoll_create1_pk : forall flags32 eff m m' evs,
  check_epoll_create1 flags32 eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros flags32 eff m m' evs H Hp.
  unfold check_epoll_create1 in H.
  pk_frame H Hp.
Qed.

Lemma check_epoll_ctl_pk : forall i epfd op32 tfd event eff m m' evs,
  check_epoll_ctl i epfd op32 tfd event eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i epfd op32 tfd event eff m m' evs H Hp.
  unfold check_epoll_ctl in H.
  pk_frame H Hp.
Qed.

Lemma check_epoll_pwait_pk : forall i epfd events maxevents32 sigmask sigsetsize eff m m' evs,
  check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i epfd events maxevents32 sigmask sigsetsize eff m m' evs H Hp.
  unfold check_epoll_pwait in H.
  pk_frame H Hp.
Qed.

(** * The table, the dispatcher *)

(** What one dispatcher arm owes, as a property of the table entry. *)
Definition arm_pins (c : CheckedArm) : Prop :=
  forall i eff m m' evs,
    ca_check c i eff m = CheckOk m' evs -> pins_post m m'.

(** Every arm discharges it.  As in [Checks.VmMapsDisjoint], the last
    alternative names the lemma an uncovered arm needs. *)
Lemma checked_table_pins : Forall arm_pins checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_pins).
  all: unfold arm_pins; intros i eff m m' evs H;
       autorewrite with arm_unfold in H.
  all: first
    [ fail
    | eapply check_brk_pk; eassumption
    | eapply check_mmap_pk; eassumption
    | eapply check_munmap_pk; eassumption
    | eapply check_mremap_pk; eassumption
    | eapply check_mprotect_pk; eassumption
    | eapply check_madvise_pk; eassumption
    | eapply check_read_pk; eassumption
    | eapply check_write_pk; eassumption
    | eapply check_pread64_pk; eassumption
    | eapply check_pwrite64_pk; eassumption
    | eapply check_readv_pk; eassumption
    | eapply check_writev_pk; eassumption
    | eapply check_pwritev2_pk; eassumption
    | eapply check_openat_pk; eassumption
    | eapply check_close_pk; eassumption
    | eapply check_lseek_pk; eassumption
    | eapply check_ftruncate_pk; eassumption
    | eapply check_ioctl_pk; eassumption
    | eapply check_readlinkat_pk; eassumption
    | eapply check_wait4_pk; eassumption
    | eapply check_fsync_pk; eassumption
    | eapply check_getdents64_pk; eassumption
    | eapply check_flock_pk; eassumption
    | eapply check_exit_pk; eassumption
    | eapply check_set_tid_address_pk; eassumption
    | eapply check_getpid_pk; eassumption
    | eapply check_gettid_pk; eassumption
    | eapply check_setsid_pk; eassumption
    | eapply check_uname_pk; eassumption
    | eapply check_prctl_pk; eassumption
    | eapply check_prlimit64_pk; eassumption
    | eapply check_getrandom_pk; eassumption
    | eapply check_gettimeofday_pk; eassumption
    | eapply check_clock_gettime_pk; eassumption
    | eapply check_clock_getres_pk; eassumption
    | eapply check_nanosleep_pk; eassumption
    | eapply check_dup_pk; eassumption
    | eapply check_dup3_pk; eassumption
    | eapply check_unlinkat_pk; eassumption
    | eapply check_faccessat_pk; eassumption
    | eapply check_faccessat2_pk; eassumption
    | eapply check_pselect6_pk; eassumption
    | eapply check_ppoll_pk; eassumption
    | eapply check_newfstatat_pk; eassumption
    | eapply check_fstat_pk; eassumption
    | eapply check_getid_pk; eassumption
    | eapply check_setid_pk; eassumption
    | eapply check_setresid_pk; eassumption
    | eapply check_getgroups_pk; eassumption
    | eapply check_setgroups_pk; eassumption
    | eapply check_socket_pk; eassumption
    | eapply check_bind_pk; eassumption
    | eapply check_listen_pk; eassumption
    | eapply check_accept4_pk; eassumption
    | eapply check_fcntl_pk; eassumption
    | eapply check_sched_setscheduler_pk; eassumption
    | eapply check_sched_getaffinity_pk; eassumption
    | eapply check_sched_yield_pk; eassumption
    | eapply check_sigaltstack_pk; eassumption
    | eapply check_rt_sigaction_pk; eassumption
    | eapply check_tkill_pk; eassumption
    | eapply check_tgkill_pk; eassumption
    | eapply check_rt_sigprocmask_pk; eassumption
    | eapply check_futex_pk; eassumption
    | eapply check_set_robust_list_pk; eassumption
    | eapply check_clone_pk; eassumption
    | eapply check_clone3_pk; eassumption
    | eapply check_getsockname_pk; eassumption
    | eapply check_getpeername_pk; eassumption
    | eapply check_setsockopt_pk; eassumption
    | eapply check_getsockopt_pk; eassumption
    | eapply check_shutdown_pk; eassumption
    | eapply check_sendto_pk; eassumption
    | eapply check_sendmsg_pk; eassumption
    | eapply check_socketpair_pk; eassumption
    | eapply check_recvfrom_pk; eassumption
    | eapply check_recvmsg_pk; eassumption
    | eapply check_connect_pk; eassumption
    | eapply check_timerfd_create_pk; eassumption
    | eapply check_eventfd2_pk; eassumption
    | eapply check_pipe2_pk; eassumption
    | eapply check_getcwd_pk; eassumption
    | eapply check_epoll_create1_pk; eassumption
    | eapply check_epoll_ctl_pk; eassumption
    | eapply check_epoll_pwait_pk; eassumption
    | fail 1 "checked_table_pins has no case for this dispatcher arm: give the new checker a *_pk"
             "lemma and add it to the list above" ].
Qed.

Theorem check_syscall_pins : forall i eff m m' evs,
  check_syscall i eff m = CheckOk m' evs -> pins_post m m'.
Proof.
  intros i eff m m' evs H. unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_pins as Hall.
  rewrite Forall_forall in Hall.
  exact (Hall c (lookup_ca_In _ _ _ Elk) i eff m m' evs H).
Qed.

(** * The specification and the step *)

Theorem pins_spec_ok : forall i mo eff mo' evs, pins_ok mo -> syscall_spec i mo (Ok eff mo' evs) ->
  pins_ok mo'.
Proof.
  intros i mo eff mo' evs Hp Hs.
  exact (check_syscall_pins i eff mo mo' evs (check_syscall_complete_ok i eff mo mo' evs Hs) Hp).
Qed.

Lemma pins_ok_with_vdso : forall v m, pins_ok m -> pins_ok (with_vdso v m).
Proof. intros v m P. refine (pins_ok_eq _ _ P _ _); reflexivity. Qed.

Lemma pins_ok_with_vdso_bump : forall m, pins_ok m -> pins_ok (with_vdso_bump m).
Proof. intros m P. refine (pins_ok_eq _ _ P _ _); reflexivity. Qed.

Lemma pins_ok_materialize : forall m acc m',
  materialize_model_accesses m acc = Some m' -> pins_ok m -> pins_ok m'.
Proof.
  intros m acc m' H P. apply materialize_model_accesses_frame in H.
  destruct H as (_ & _ & _ & _ & _ & Ep & El).
  exact (pins_ok_frame _ _ P Ep El).
Qed.

(** Every step of [Run.sstep_cfg] (Run.v:2250-2342), under any spurious-failure configuration. *)
Theorem pins_step : forall segs cfg c evs c', sstep_cfg segs cfg c evs (SNext c') ->
  pins_ok (cfg_model c) -> pins_ok (cfg_model c').
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
    apply mi_account_step_model_frame in Ha.
    destruct Ha as (_ & _ & _ & _ & _ & Ep & El).
    exact (pins_ok_frame _ _ P Ep El).
  - (* a vDSO call *)
    apply pins_ok_with_vdso_bump.
    exact (pins_ok_materialize _ _ _ Hm (pins_spec_ok _ _ _ _ _ P Hs)).
  - (* a system call that returns *)
    exact (pins_ok_materialize _ _ _ Hm (pins_spec_ok _ _ _ _ _ P Hs)).
  - (* exit *)
    exact (pins_spec_ok _ _ _ _ _ P Hs).
  - (* killed *)
    exact (pins_spec_ok _ _ _ _ _ P Hs).
Qed.

(** * The launch *)

Lemma pins_ok_init_model : forall reserved brk0 mbase sp lim inp,
  pins_ok (init_model reserved brk0 mbase sp lim inp).
Proof.
  intros reserved brk0 mbase sp lim inp. split; intros b0 E.
  - change (None = Some b0) in E. discriminate E.
  - rewrite m_rlimit_core_init_model in E. discriminate E.
Qed.

(** [Run.init_config] (Run.v:1455-1459), with its eight image arguments. *)
Lemma pins_ok_init : forall vsegs pc ph sp brk0 mbase rnd lim inp,
  pins_ok (cfg_model (init_config vsegs pc ph sp brk0 mbase rnd lim inp)).
Proof.
  intros vsegs pc ph sp brk0 mbase rnd lim inp.
  unfold init_config. cbn [cfg_model].
  apply pins_ok_with_vdso. apply pins_ok_init_model.
Qed.
