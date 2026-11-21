(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11: [PairClean.pc_spec_ok] for the 46 arms of the model's
   Sys/SyscallTable.v that write no user memory and that PairClean.v does not prove.

   Each arm is proved as PairClean.v proves its own: [PairClean.pc_spec_of_check] turns an
   outcome of [Specs.syscall_spec] into an accepted call of [ExecutableSpecs.check_syscall];
   the lemma of [Checks/Sys/DispatchCompute.v] (or, for the 13 numbers it has no lemma for,
   its own proof shape, as [PairClean.pc_cs_114]) names the checker the number reaches; one
   walk ([pcq_walk], PairClean.v's [pcl_walk]) splits that checker at every branch, and every
   accepting leaf is an effect with no write, no zero-fill and no copy over a model the
   setters of State.v build from the input model, so [m_kernel] is kept (State.v:7885-8024,
   each by [reflexivity]; [ReadWrite.raise_sigpipe] by [PairClean.pcl_k_raise]).  [m_vmmaps]
   is the model's own [Checks/VmMapsDisjoint.v] [check_*_frame] (the list of
   [checked_table_preserves_vm], VmMapsDisjoint.v:2767-2861; tkill and tgkill:
   Checks/Sys/Kernel/Signal.v:1459-1487).  [PairClean.pc_out_of_nm] puts the two halves
   together.

   The checkers walked (model files under Checks/Sys):
     eventfd2 (19)            Fs/EventFd.v:48-61, Fs/Open.v:71-83
     epoll_create1 (20)       Fs/EventPoll.v:30-35
     epoll_ctl (21)           Fs/EventPoll.v:84-89
     dup (23), dup3 (24)      Fs/File.v:37-88
     fcntl (25)               Fs/Fcntl.v:28-81
     flock (32)               Fs/Locks.v:24-62
     unlinkat (35)            Fs/Namei.v:25-163
     ftruncate (46)           Fs/Open.v:2227-2271
     faccessat (48)           Fs/Open.v:2386-2430
     faccessat2 (439)         Fs/Open.v:2744-2755
     lseek (62)               Fs/ReadWrite.v:7744-7845
     pwrite64 (68)            Fs/ReadWrite.v:4243-4317, :1726-1747
     pwritev2 (287)           Fs/ReadWrite.v:6446-6505, :1742-1747
     fsync (82), fdatasync (83)  Fs/Sync.v:19-37
     timerfd_create (85)      Fs/Timerfd.v:32-41
     futex (98)               Kernel/Futex/Syscalls.v:79-114
     set_robust_list (99)     Kernel/Futex/Syscalls.v:21-25
     sched_setscheduler (119) Kernel/Sched/Syscalls.v:85-105
     sched_yield (124)        Kernel/Sched/Syscalls.v:235-237
     tkill (130), tgkill (131)  Kernel/Signal.v:1166-1211
     setgid (144), setuid (146), setresuid (147), setresgid (149)  Kernel/Sys.v:786-848
     setsid (157)             Kernel/Sys.v:46-57
     setgroups (159)          Kernel/Groups.v:134-136
     prctl (167)              Kernel/Sys.v:189-194
     getpid (172), gettid (178)  Kernel/Sys.v:25-35, Kernel/Fork.v:19-31
     getuid, geteuid, getgid, getegid (174-177)  Kernel/Sys.v:778-780
     socket (198)             Net/Socket.v:189-225, :28-51, :103-110
     bind (200)               Net/Socket.v:231-323
     listen (201)             Net/Socket.v:328-352
     connect (203)            Net/Socket.v:403-443
     sendto (206)             Net/Socket.v:2473-2495, :2433-2463, Fs/ReadWrite.v:802-837, :1040-1045
     setsockopt (208)         Net/Socket.v:1921-1937, :1678-1696
     shutdown (210)           Net/Socket.v:1966-1987, :1834-1844
     sendmsg (211)            Net/Socket.v:2502-2570, :2433-2463
     clone (220), clone3 (435)  Kernel/Fork.v:123-174 *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs MemImageType RiscvSemantics State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require VmMapsDisjoint.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import PairClean.
Import ListNotations.
Open Scope Z_scope.

Section PairCleanQ.
  Variable segs : list Segment.
  Variables vlo vhi : Z.
  (* no writable segment of [segs] holds a byte of the window (PairClean.v's [Hnw]) *)
  Hypothesis Hnw : forall (x : word) s, vlo <= bv_unsigned x < vhi ->
    find_segment segs (bv_unsigned x) 1 = Some s -> seg_writable s = false.

  (** * The checker walk (PairClean.v's [pcl_unfold] and [pcl_walk], under new names) *)

  (* The shared acceptors every checker reaches, and the effect's projections. *)
  Ltac pcq_unfold H :=
    cbv beta iota zeta delta [check_ret_only check_ret_only_copyins clear_copyins with_copyins
      check_copyins check_copyins_after check_copyin_prefix strip_copyin_prefix eff_is_errno
      check_efault_or check_access_ok_zero check_sigpipe_write check_sigpipe_writev
      check_new_fd_result check_open_result
      eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins] in H.

  (* Split the checker hypothesis [H] at every [if] and [match] whose scrutinee is a variable
     or an application, until no branch is left to split; the refusals are then closed by
     [discriminate].  The effect is destructed before the walk, so its fields are variables. *)
  Ltac pcq_walk H :=
    repeat (cbv beta iota zeta delta [eff_ret eff_writes eff_zeros eff_unmaps eff_copies
                                      eff_copyins] in H;
            match type of H with
            | context [match ?x with _ => _ end] =>
                first [ is_var x; destruct x
                      | lazymatch x with _ _ => destruct x eqn:? end ]
            end);
    try discriminate H.

  (* The kernel build of an accepting leaf: every setter keeps it by conversion; the SIGPIPE
     answer of a stream send goes through [ReadWrite.raise_sigpipe] ([PairClean.pcl_k_raise]). *)
  Ltac pcq_kern :=
    first [ reflexivity | (rewrite pcl_k_raise; reflexivity) ].

  (* An accepting leaf of a write-free call: no write, no zero-fill, no copy. *)
  Ltac pcq_leaf H :=
    injection H as <- <-;
    unfold pc_nm; cbn [eff_writes eff_zeros eff_copies];
    refine (conj _ (conj eq_refl (conj eq_refl _))); [apply Forall_nil | pcq_kern].

  (** * The arms, checker by checker *)

  Lemma pcq_eventfd2 : forall i flags eff m m' evs,
    check_eventfd2 i flags eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i flags [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_eventfd2] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_epoll_create1 : forall i flags32 eff m m' evs,
    check_epoll_create1 flags32 eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i flags32 [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_epoll_create1] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_epoll_ctl : forall i epfd op32 tfd event eff m m' evs,
    check_epoll_ctl i epfd op32 tfd event eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i epfd op32 tfd event [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_epoll_ctl] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_dup : forall i oldfd eff m m' evs,
    check_dup oldfd eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i oldfd [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_dup check_dup_result] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_dup3 : forall i oldfd newfd flags eff m m' evs,
    check_dup3 oldfd newfd flags eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i oldfd newfd flags [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_dup3] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_fcntl : forall i fd cmd arg eff m m' evs,
    check_fcntl fd cmd arg eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd cmd arg [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_fcntl] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_flock : forall i fd cmd eff m m' evs,
    check_flock fd cmd eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd cmd [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_flock] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  (* The body and its tails are [Local] to Checks/Sys/Fs/Namei.v; the unfold list is
     [VmMapsDisjoint.check_unlinkat_frame]'s (VmMapsDisjoint.v:2257-2259). *)
  Lemma pcq_unlinkat : forall i dirfd pathp flags eff m m' evs,
    check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i dirfd pathp flags [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_unlinkat Namei.check_unlinkat_body Namei.check_unlinkat_tmp
      Namei.check_unlink_found check_unlink_result Namei.check_unlink_open_tmp
      check_unlink_open_result check_unlink_type_result] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_ftruncate : forall i fd len eff m m' evs,
    check_ftruncate fd len eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd len [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_ftruncate] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  (* The body is [Local] to Checks/Sys/Fs/Open.v ([VmMapsDisjoint.check_faccessat_frame],
     VmMapsDisjoint.v:2268). *)
  Lemma pcq_faccessat : forall i dirfd pathp mode eff m m' evs,
    check_faccessat i dirfd pathp mode eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i dirfd pathp mode [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_faccessat Open.check_faccessat_body check_access_exists] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_faccessat2 : forall i dirfd pathp mode flags eff m m' evs,
    check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i dirfd pathp mode flags [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_faccessat2 Open.check_faccessat_body check_access_exists] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_lseek : forall i fd off whence eff m m' evs,
    check_lseek fd off whence eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd off whence [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_lseek] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  (* The source is only read: its ledger is [eff_copyins]; the file grows in the model. *)
  Lemma pcq_pwrite64 : forall i fd buf count pos eff m m' evs,
    check_pwrite64 i fd buf count pos eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd buf count pos [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_pwrite64 check_write_fault_extend check_anon_fault_extend] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_pwritev2 : forall i fd iov iovcnt pos_l pos_h flags eff m m' evs,
    check_pwritev2 i fd iov iovcnt pos_l pos_h flags eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd iov iovcnt pos_l pos_h flags [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_pwritev2 check_anon_fault_extend] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_fsync : forall i fd eff m m' evs,
    check_fsync fd eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_fsync] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_timerfd_create : forall i clkid flags eff m m' evs,
    check_timerfd_create clkid flags eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i clkid flags [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_timerfd_create] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  (* The wait arm reads four bytes ([eff_copyins]) and writes none. *)
  Lemma pcq_futex : forall i uaddr op val utime eff m m' evs,
    check_futex i uaddr op val utime eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i uaddr op val utime [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_futex check_futex_wake_private check_futex_wait_private] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_set_robust_list : forall i len eff m m' evs,
    check_set_robust_list len eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i len [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_set_robust_list] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_sched_setscheduler : forall i pid policy param eff m m' evs,
    check_sched_setscheduler i pid policy param eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i pid policy param [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_sched_setscheduler] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_sched_yield : forall i eff m m' evs,
    check_sched_yield eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_sched_yield] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_tkill : forall i pid sig eff m m' evs,
    check_tkill pid sig eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i pid sig [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_tkill check_tkill_self check_send_sigabrt] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_tgkill : forall i tgid pid sig eff m m' evs,
    check_tgkill tgid pid sig eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i tgid pid sig [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_tgkill check_tkill_self check_send_sigabrt] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_setid : forall i get put user v eff m m' evs,
    check_setid get put user v eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i get put user v [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_setid check_setid_result] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_setresid : forall i get put user r e s eff m m' evs,
    check_setresid get put user r e s eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i get put user r e s [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_setresid check_setid_result] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_setsid : forall i eff m m' evs,
    check_setsid eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_setsid] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_setgroups : forall i eff m m' evs,
    check_setgroups eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_setgroups] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_prctl : forall i option_ arg2 eff m m' evs,
    check_prctl option_ arg2 eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i option_ arg2 [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_prctl] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  (* [check_getpid] and [check_gettid] are [check_set_tid_address] (Checks/Sys/Kernel/Sys.v:25-35). *)
  Lemma pcq_getpid : forall i eff m m' evs,
    check_getpid eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_getpid check_set_tid_address] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_gettid : forall i eff m m' evs,
    check_gettid eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_gettid check_set_tid_address] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_getid : forall i sel eff m m' evs,
    check_getid sel eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i sel [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_getid] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_socket : forall i domain type protocol eff m m' evs,
    check_socket domain type protocol eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i domain type protocol [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_socket check_errno_or_list] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_bind : forall i fd addrp addrlen eff m m' evs,
    check_bind i fd addrp addrlen eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd addrp addrlen [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_bind check_errno_or_success] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_listen : forall i fd backlog eff m m' evs,
    check_listen fd backlog eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd backlog [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_listen check_errno_or_success check_errno_only] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_connect : forall i fd addrp addrlen eff m m' evs,
    check_connect i fd addrp addrlen eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd addrp addrlen [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_connect] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  (* An AF_INET socket's send ([check_send_on_socket]) or a stream-pair end's
     ([check_stream_write] over [check_stream_send], whose -EPIPE may raise SIGPIPE through
     [check_sigpipe_write]); the payload is only read. *)
  Lemma pcq_sendto : forall i fd buf count flags addrp eff m m' evs,
    check_sendto i fd buf count flags addrp eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd buf count flags addrp [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_sendto check_send_on_socket check_stream_write
      check_stream_send] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_setsockopt : forall i fd level optlen eff m m' evs,
    check_setsockopt i fd level optlen eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd level optlen [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_setsockopt check_stream_setsockopt] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_shutdown : forall i fd how eff m m' evs,
    check_shutdown fd how eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd how [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_shutdown check_stream_shutdown] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_sendmsg : forall i fd msgp flags eff m m' evs,
    check_sendmsg i fd msgp flags eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd msgp flags [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_sendmsg check_send_on_socket] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_clone : forall i flags eff m m' evs,
    check_clone flags eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i flags [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_clone check_clone_resolve check_clone_answer] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  Lemma pcq_clone3 : forall i uargs size eff m m' evs,
    check_clone3 i uargs size eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i uargs size [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_clone3 check_clone3_resolve check_clone_answer] in H.
    pcq_unfold H. pcq_walk H.
    all: pcq_leaf H.
  Qed.

  (** * The dispatch equations [Checks/Sys/DispatchCompute.v] has no lemma for
      ([PairClean.pc_cs_114]'s shape; the checker each arm of Checks/Sys/Dispatch.v names) *)

  Lemma pcq_cs_19 : forall i eff m, bv_unsigned (in_sysno i) = 19 ->
    check_syscall i eff m = check_eventfd2 i (flag32 (in_arg i 1)) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcq_cs_20 : forall i eff m, bv_unsigned (in_sysno i) = 20 ->
    check_syscall i eff m = check_epoll_create1 (flag32 (in_arg i 0)) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcq_cs_21 : forall i eff m, bv_unsigned (in_sysno i) = 21 ->
    check_syscall i eff m
    = check_epoll_ctl i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2))
        (in_arg i 3) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcq_cs_68 : forall i eff m, bv_unsigned (in_sysno i) = 68 ->
    check_syscall i eff m
    = check_pwrite64 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcq_cs_85 : forall i eff m, bv_unsigned (in_sysno i) = 85 ->
    check_syscall i eff m
    = check_timerfd_create (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcq_cs_98 : forall i eff m, bv_unsigned (in_sysno i) = 98 ->
    check_syscall i eff m
    = check_futex i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcq_cs_99 : forall i eff m, bv_unsigned (in_sysno i) = 99 ->
    check_syscall i eff m = check_set_robust_list (in_arg i 1) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcq_cs_130 : forall i eff m, bv_unsigned (in_sysno i) = 130 ->
    check_syscall i eff m = check_tkill (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcq_cs_131 : forall i eff m, bv_unsigned (in_sysno i) = 131 ->
    check_syscall i eff m
    = check_tgkill (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcq_cs_206 : forall i eff m, bv_unsigned (in_sysno i) = 206 ->
    check_syscall i eff m
    = check_sendto i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4)
        eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcq_cs_208 : forall i eff m, bv_unsigned (in_sysno i) = 208 ->
    check_syscall i eff m
    = check_setsockopt i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcq_cs_210 : forall i eff m, bv_unsigned (in_sysno i) = 210 ->
    check_syscall i eff m = check_shutdown (fd32 (in_arg i 0)) (int32 (in_arg i 1)) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcq_cs_211 : forall i eff m, bv_unsigned (in_sysno i) = 211 ->
    check_syscall i eff m
    = check_sendmsg i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  (** * The premise, number by number *)

  Lemma pc_spec_ok_19 : forall i mo, bv_unsigned (in_sysno i) = 19 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcq_cs_19 i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_eventfd2 | eapply VmMapsDisjoint.check_eventfd2_frame];
      exact H.
  Qed.

  Lemma pc_spec_ok_20 : forall i mo, bv_unsigned (in_sysno i) = 20 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcq_cs_20 i eff mo Hn) in H.
    apply pc_out_of_nm;
      [eapply pcq_epoll_create1 | eapply VmMapsDisjoint.check_epoll_create1_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_21 : forall i mo, bv_unsigned (in_sysno i) = 21 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcq_cs_21 i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_epoll_ctl | eapply VmMapsDisjoint.check_epoll_ctl_frame];
      exact H.
  Qed.

  Lemma pc_spec_ok_23 : forall i mo, bv_unsigned (in_sysno i) = 23 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_dup i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_dup | eapply VmMapsDisjoint.check_dup_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_24 : forall i mo, bv_unsigned (in_sysno i) = 24 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_dup3 i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_dup3 | eapply VmMapsDisjoint.check_dup3_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_25 : forall i mo, bv_unsigned (in_sysno i) = 25 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_fcntl i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_fcntl | eapply VmMapsDisjoint.check_fcntl_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_32 : forall i mo, bv_unsigned (in_sysno i) = 32 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_flock i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_flock | eapply VmMapsDisjoint.check_flock_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_35 : forall i mo, bv_unsigned (in_sysno i) = 35 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_unlinkat i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_unlinkat | eapply VmMapsDisjoint.check_unlinkat_frame];
      exact H.
  Qed.

  Lemma pc_spec_ok_46 : forall i mo, bv_unsigned (in_sysno i) = 46 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_ftruncate i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_ftruncate | eapply VmMapsDisjoint.check_ftruncate_frame];
      exact H.
  Qed.

  Lemma pc_spec_ok_48 : forall i mo, bv_unsigned (in_sysno i) = 48 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_faccessat i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_faccessat | eapply VmMapsDisjoint.check_faccessat_frame];
      exact H.
  Qed.

  Lemma pc_spec_ok_62 : forall i mo, bv_unsigned (in_sysno i) = 62 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_lseek i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_lseek | eapply VmMapsDisjoint.check_lseek_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_68 : forall i mo, bv_unsigned (in_sysno i) = 68 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcq_cs_68 i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_pwrite64 | eapply VmMapsDisjoint.check_pwrite64_frame];
      exact H.
  Qed.

  Lemma pc_spec_ok_82 : forall i mo, bv_unsigned (in_sysno i) = 82 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_fsync i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_fsync | eapply VmMapsDisjoint.check_fsync_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_83 : forall i mo, bv_unsigned (in_sysno i) = 83 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_fdatasync i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_fsync | eapply VmMapsDisjoint.check_fsync_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_85 : forall i mo, bv_unsigned (in_sysno i) = 85 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcq_cs_85 i eff mo Hn) in H.
    apply pc_out_of_nm;
      [eapply pcq_timerfd_create | eapply VmMapsDisjoint.check_timerfd_create_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_98 : forall i mo, bv_unsigned (in_sysno i) = 98 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcq_cs_98 i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_futex | eapply VmMapsDisjoint.check_futex_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_99 : forall i mo, bv_unsigned (in_sysno i) = 99 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcq_cs_99 i eff mo Hn) in H.
    apply pc_out_of_nm;
      [eapply pcq_set_robust_list | eapply VmMapsDisjoint.check_set_robust_list_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_119 : forall i mo, bv_unsigned (in_sysno i) = 119 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_sched_setscheduler i eff mo Hn) in H.
    apply pc_out_of_nm;
      [eapply pcq_sched_setscheduler | eapply VmMapsDisjoint.check_sched_setscheduler_frame];
      exact H.
  Qed.

  Lemma pc_spec_ok_124 : forall i mo, bv_unsigned (in_sysno i) = 124 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_sched_yield i eff mo Hn) in H.
    apply pc_out_of_nm;
      [eapply pcq_sched_yield | eapply VmMapsDisjoint.check_sched_yield_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_130 : forall i mo, bv_unsigned (in_sysno i) = 130 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcq_cs_130 i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_tkill | eapply check_tkill_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_131 : forall i mo, bv_unsigned (in_sysno i) = 131 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcq_cs_131 i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_tgkill | eapply check_tgkill_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_144 : forall i mo, bv_unsigned (in_sysno i) = 144 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_setgid i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_setid | eapply VmMapsDisjoint.check_setid_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_146 : forall i mo, bv_unsigned (in_sysno i) = 146 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_setuid i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_setid | eapply VmMapsDisjoint.check_setid_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_147 : forall i mo, bv_unsigned (in_sysno i) = 147 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_setresuid i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_setresid | eapply VmMapsDisjoint.check_setresid_frame];
      exact H.
  Qed.

  Lemma pc_spec_ok_149 : forall i mo, bv_unsigned (in_sysno i) = 149 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_setresgid i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_setresid | eapply VmMapsDisjoint.check_setresid_frame];
      exact H.
  Qed.

  Lemma pc_spec_ok_157 : forall i mo, bv_unsigned (in_sysno i) = 157 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_setsid i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_setsid | eapply VmMapsDisjoint.check_setsid_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_159 : forall i mo, bv_unsigned (in_sysno i) = 159 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_setgroups i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_setgroups | eapply VmMapsDisjoint.check_setgroups_frame];
      exact H.
  Qed.

  Lemma pc_spec_ok_167 : forall i mo, bv_unsigned (in_sysno i) = 167 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_prctl i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_prctl | eapply VmMapsDisjoint.check_prctl_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_172 : forall i mo, bv_unsigned (in_sysno i) = 172 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_getpid i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_getpid | eapply VmMapsDisjoint.check_getpid_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_174 : forall i mo, bv_unsigned (in_sysno i) = 174 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_getuid i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_getid | eapply VmMapsDisjoint.check_getid_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_175 : forall i mo, bv_unsigned (in_sysno i) = 175 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_geteuid i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_getid | eapply VmMapsDisjoint.check_getid_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_176 : forall i mo, bv_unsigned (in_sysno i) = 176 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_getgid i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_getid | eapply VmMapsDisjoint.check_getid_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_177 : forall i mo, bv_unsigned (in_sysno i) = 177 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_getegid i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_getid | eapply VmMapsDisjoint.check_getid_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_178 : forall i mo, bv_unsigned (in_sysno i) = 178 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_gettid i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_gettid | eapply VmMapsDisjoint.check_gettid_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_198 : forall i mo, bv_unsigned (in_sysno i) = 198 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_socket i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_socket | eapply VmMapsDisjoint.check_socket_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_200 : forall i mo, bv_unsigned (in_sysno i) = 200 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_bind i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_bind | eapply VmMapsDisjoint.check_bind_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_201 : forall i mo, bv_unsigned (in_sysno i) = 201 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_listen i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_listen | eapply VmMapsDisjoint.check_listen_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_203 : forall i mo, bv_unsigned (in_sysno i) = 203 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_connect i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_connect | eapply VmMapsDisjoint.check_connect_frame];
      exact H.
  Qed.

  Lemma pc_spec_ok_206 : forall i mo, bv_unsigned (in_sysno i) = 206 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcq_cs_206 i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_sendto | eapply VmMapsDisjoint.check_sendto_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_208 : forall i mo, bv_unsigned (in_sysno i) = 208 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcq_cs_208 i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_setsockopt | eapply VmMapsDisjoint.check_setsockopt_frame];
      exact H.
  Qed.

  Lemma pc_spec_ok_210 : forall i mo, bv_unsigned (in_sysno i) = 210 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcq_cs_210 i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_shutdown | eapply VmMapsDisjoint.check_shutdown_frame];
      exact H.
  Qed.

  Lemma pc_spec_ok_211 : forall i mo, bv_unsigned (in_sysno i) = 211 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcq_cs_211 i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_sendmsg | eapply VmMapsDisjoint.check_sendmsg_frame];
      exact H.
  Qed.

  Lemma pc_spec_ok_220 : forall i mo, bv_unsigned (in_sysno i) = 220 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_clone i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_clone | eapply VmMapsDisjoint.check_clone_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_287 : forall i mo, bv_unsigned (in_sysno i) = 287 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_pwritev2 i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_pwritev2 | eapply VmMapsDisjoint.check_pwritev2_frame];
      exact H.
  Qed.

  Lemma pc_spec_ok_435 : forall i mo, bv_unsigned (in_sysno i) = 435 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_clone3 i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_clone3 | eapply VmMapsDisjoint.check_clone3_frame]; exact H.
  Qed.

  Lemma pc_spec_ok_439 : forall i mo, bv_unsigned (in_sysno i) = 439 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_faccessat2 i eff mo Hn) in H.
    apply pc_out_of_nm; [eapply pcq_faccessat2 | eapply VmMapsDisjoint.check_faccessat2_frame];
      exact H.
  Qed.
End PairCleanQ.
