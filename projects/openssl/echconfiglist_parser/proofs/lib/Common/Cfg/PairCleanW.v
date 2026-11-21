(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11: [PairClean.pc_spec_ok] for the arms of the model's Sys/SyscallTable.v
   that write user memory and that PairClean.v does not prove, and for mremap (216).

   Each arm is proved as PairClean.v proves its own: [PairClean.pc_spec_of_check] turns an
   outcome of [Specs.syscall_spec] into an accepted call of [ExecutableSpecs.check_syscall];
   the lemma of [Checks/Sys/DispatchCompute.v] (or, for the nine numbers it has no lemma for,
   its own proof shape, as [PairClean.pc_cs_114]) names the checker the number reaches; one
   walk ([pcw_walk], PairClean.v's [pcl_walk]) splits that checker at every branch.  At an
   accepting leaf every write is covered by the input's writable view, through the gate the
   checker tested before it: [read_bytes_map (in_wmem i)] of the written range
   ([PairClean.pc_wcov_rb]), [copy_bytes_map (in_wmem i)] ([pcw_wcov_cb2]; the range test
   [access_okb], State.v:1377-1378, bounds the length), [Net.Socket.user_range_writable]
   (Sys/Net/Socket.v:1295-1300, [pcw_urw_cov]), the iovec scatter ([State.scatter_iovecs],
   State.v:1853-1875, [pcw_scatter_cov]), the socketpair destination
   (Sys/Net/Socket.v:3002-3008 over the two stores of :2813-2814, split by
   [State.read_bytes_aux_split], State.v:824-856), or the delivery ([PairClean.pc_cov_delivered]).
   The written lengths come from the predicates the checker tests on the bytes
   ([Uapi.stat_buf_wf], Sys/Uapi.v:1250-1255; [Hrtimer.nanosleep_rem_ok_b],
   Sys/Kernel/Time/Hrtimer.v:43-47; [Kernel.Sys.utsname_wf], Sys/Kernel/Sys.v:987-994;
   [Kernel.Sys.rlim64_wf], :326-328; [Select.pselect_remaining_ok], Sys/Fs/Select.v:929-932)
   or from the encoders ([State.pipe_fd_bytes], State.v:6016-6017;
   [Kernel.Signal.sigpipe_action_bytes], Sys/Kernel/Signal.v:463-466;
   [BvBase.length_Z_to_le_bytes], BvBase.v:107).

   Two arms write bytes a pin of the model holds: a later uname repeats a pinned UTS name that
   [utsname_wf] rejects exactly (Sys/Kernel/Sys.v:1020-1022, Checks/Sys/Kernel/Sys.v:155-156),
   and a prlimit64 read repeats the pinned [struct rlimit64] (Checks/Sys/Kernel/Sys.v:78).
   Nothing in the checker bounds the pin's length, so [pc_spec_ok_160] and [pc_spec_ok_261]
   take [PinsOk.pins_ok] of the model (the pins are no longer than the 390 and 16 bytes the
   gates read).

   pselect6 and ppoll write the answer [Select.pselect_finish] builds (Sys/Fs/Select.v:1025-1063):
   its gate [writes_all_writable] (:677-685) is asked of the writes of the choice [sel = 0],
   and every choice writes the same ranges ([pcw_core_ok]: [Select.fd_set_writeback], :247-251,
   and [Select.ppoll_writeback], :1492-1498, over [Select.ppoll_pick], :1465-1469), so the gate
   covers each choice ([pcw_pa_ok]); the remaining time is the sixteen bytes at [tsp] the gate
   tested with the zero time.

   mremap (Checks/Sys/Mm/Mremap.v:36-96): the in-place grow zero-fills the tail of a range its
   gate tests [region_free] against [vm_reserved ++ ...] (Sys/Mm/Mremap.v:320-334), and the
   move zero-fills the tail of, and copies into the head of, a destination tested
   [region_free] against [vm_reserved ++ vm_maps] (:439-447); [MmVdso.mm_vinv] puts the
   window in [vm_reserved], so both are off the window ([pcw_tail_off], [MmVdso.off_shrink]).

   The ledger fields: [Checks/VmMapsDisjoint.v]'s [check_*_frame] for the calls that do not
   touch the address space ([check_rt_sigprocmask_frame] is Checks/Sys/Kernel/Signal.v's), and
   [Checks/MmapTopFrame.v]'s [check_mremap_top_frame] (:118-124) for mremap.

   The checkers walked (model files under Checks/Sys):
     getcwd (17)              Fs/DPath.v:31-41
     epoll_pwait (22)         Fs/EventPoll.v:141-147
     pipe2 (59)               Fs/Pipe.v:39-93
     getdents64 (61)          Fs/Readdir.v:33-60
     readv (65)               Fs/ReadWrite.v:6940-6968, :6755-6938, :537-545, :466-479
     pread64 (67)             Fs/ReadWrite.v:4174-4241, :38-60
     pselect6 (72)            Fs/Select.v:514-521, :35-53
     ppoll (73)               Fs/Select.v:777-784, :35-53
     readlinkat (78)          Fs/Stat.v:19-22
     newfstatat (79)          Fs/Stat.v:81-98
     fstat (80)               Fs/Stat.v:948-968, :317-361, :550-567, :669-675, :745-779
     nanosleep (101)          Kernel/Time/Hrtimer.v:72-124
     sched_getaffinity (123)  Kernel/Sched/Syscalls.v:23-27
     sigaltstack (132)        Kernel/Signal.v:28-50
     rt_sigaction (134)       Kernel/Signal.v:592-616, :354-374, :210-222, :169-176
     rt_sigprocmask (135)     Kernel/Signal.v:832-856, :747-771, :169-176
     getgroups (158)          Kernel/Groups.v:23-33
     uname (160)              Kernel/Sys.v:169-177, :149-161, :129-131
     socketpair (199)         Net/Socket.v:3352-3373, :3063-3075, :3163-3170, :3228-3249
     accept (202), accept4 (242)  Net/Socket.v:358-395, :45-51, :103-110, Fs/Open.v:71-83
     getsockname (204), getpeername (205)  Net/Socket.v:1896-1919, :1599-1627, :1476-1484
     recvfrom (207)           Net/Socket.v:3496-3512, :3002-3007, Fs/ReadWrite.v:627-653
     getsockopt (209)         Net/Socket.v:1948-1964, :1750-1779, :1476-1484
     recvmsg (212)            Net/Socket.v:3623-3627, :3002-3007
     mremap (216)             Mm/Mremap.v:36-96
     wait4 (260)              Kernel/Exit.v:71-82
     prlimit64 (261)          Kernel/Sys.v:93-126, :71-83
     getrandom (278)          Drivers/Char/Random.v:24-74 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs MemImageType RiscvSemantics State Monad Specs Run Vdso.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Placement.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require VmMapsDisjoint MmapTopFrame.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg VdsoClean.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import MmVdso.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import PairClean.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require PinsOk.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section PairCleanW.
  Variable segs : list Segment.
  Variables vlo vhi : Z.
  (* no writable segment of [segs] holds a byte of the window (PairClean.v's [Hnw]) *)
  Hypothesis Hnw : forall (x : word) s, vlo <= bv_unsigned x < vhi ->
    find_segment segs (bv_unsigned x) 1 = Some s -> seg_writable s = false.

  (** * Writes inside the writable view *)

  (** A write no longer than a range [copy_bytes_map] read through the view; the range test
      [access_okb] (State.v:1377-1378) bounds the length below 2^64. *)
  Lemma pcw_wcov_cb2 : forall (wm : word -> option byte) (a : word) (k : Z) (w bs : list byte),
    copy_bytes_map wm a k = Some w -> Z.of_nat (length bs) <= k -> pc_wcov wm (a, bs).
  Proof.
    intros wm a k w bs H Hl.
    assert (Hk : 0 <= k < two_pow_64).
    { unfold copy_bytes_map in H.
      destruct (access_okb a k) eqn:Ea; cbv beta iota in H; [|discriminate H].
      unfold access_okb in Ea. apply andb_prop in Ea as [E1 _]. apply Z.leb_le in E1.
      unfold TASK_SIZE, two_pow_64 in *. lia. }
    exact (pc_wcov_cb wm a k w bs H Hk Hl).
  Qed.

  (** [Net.Socket.user_range_writable] (Sys/Net/Socket.v:1295-1300). *)
  Lemma pcw_urw_cov : forall (i : SyscallInput) (a : word) (k : Z) (bs : list byte),
    user_range_writable i a k = true -> Z.of_nat (length bs) <= k -> pc_wcov (in_wmem i) (a, bs).
  Proof.
    intros i a k bs H Hl. unfold user_range_writable in H.
    apply andb_prop in H as [Ha H].
    destruct (read_bytes_map (in_wmem i) a (Z_to_bv 64 k)) as [w|] eqn:E; cbv beta iota in H;
      [|discriminate H].
    unfold access_okb in Ha. apply andb_prop in Ha as [Ha _]. apply Z.leb_le in Ha.
    apply (pc_wcov_rb (in_wmem i) a (Z_to_bv 64 k) w bs E).
    rewrite bv_unsigned_Z_to_bv_u64; [exact Hl|]. unfold TASK_SIZE, two_pow_64 in *. lia.
  Qed.

  (** Every write of [State.scatter_iovecs] (State.v:1853-1875) is read through the view first. *)
  Lemma pcw_scatter_cov : forall (wm : word -> option byte) iovs bs ws,
    scatter_iovecs wm iovs bs = Some ws -> Forall (pc_wcov wm) ws.
  Proof.
    intros wm iovs. induction iovs as [|[base len] rest IH]; intros bs ws H.
    - destruct bs as [|b bs']; cbn [scatter_iovecs] in H;
        [injection H as <-; constructor | discriminate H].
    - destruct bs as [|b bs']; cbn [scatter_iovecs] in H; [injection H as <-; constructor|].
      cbv zeta in H.
      match type of H with
      | context [match ?x with _ => _ end] =>
          lazymatch x with firstn _ _ => destruct x as [|h hs] eqn:Eh end
      end; cbv beta iota in H.
      + exact (IH _ _ H).
      + match type of H with
        | context [match ?x with _ => _ end] =>
            lazymatch x with read_bytes_map _ _ _ => destruct x as [w|] eqn:Er end
        end; cbv beta iota in H; [|discriminate H].
        match type of H with
        | context [match ?x with _ => _ end] =>
            lazymatch x with scatter_iovecs _ _ _ => destruct x as [ws'|] eqn:Es end
        end; cbv beta iota in H; [|discriminate H].
        injection H as <-. constructor; [|exact (IH _ _ Es)].
        apply (pc_wcov_rb wm base (len_word (h :: hs)) w (h :: hs) Er).
        assert (Hk : (length (h :: hs) <= word_to_nat len)%nat).
        { rewrite <- Eh, length_firstn, word_to_nat_bounded_eq_min. lia. }
        unfold word_to_nat in Hk. pose proof (word_unsigned_range len) as Hl.
        rewrite len_word_unsigned; [lia|]. unfold two_pow_64 in *. lia.
  Qed.

  (** The two 4-byte stores of socketpair (Sys/Net/Socket.v:2813-2814) inside the 8 bytes its
      destination test reads (:3002-3008). *)
  Lemma pcw_socketpair_cov : forall (wm : word -> option byte) (sv fd1 fd2 : word),
    socketpair_dest_writable wm sv = true -> Forall (pc_wcov wm) (socketpair_writes sv fd1 fd2).
  Proof.
    intros wm sv fd1 fd2 H. unfold socketpair_dest_writable in H.
    apply andb_prop in H as [_ H].
    destruct (read_bytes_map wm sv (Z_to_bv 64 8)) as [w|] eqn:E; cbv beta iota in H;
      [|discriminate H].
    rewrite read_bytes_map_eq in E. unfold word_to_nat in E.
    rewrite bv_unsigned_Z_to_bv_u64 in E by (unfold two_pow_64; lia).
    change (Z.to_nat 8) with (4 + 4)%nat in E.
    rewrite read_bytes_aux_split in E.
    destruct (read_bytes_aux wm sv 4) as [w1|] eqn:E1; cbv beta iota in E; [|discriminate E].
    destruct (read_bytes_aux wm (sv + nat_to_word 4)%bv 4) as [w2|] eqn:E2;
      cbv beta iota in E; [|discriminate E].
    unfold socketpair_writes.
    constructor; [|constructor; [|constructor]].
    - assert (Hn : read_bytes_aux wm sv (length (word_le4 fd1)) <> None)
        by (cbn [length word_le4]; rewrite E1; discriminate).
      exact (pc_wcov_of_aux (word_le4 fd1) wm sv Hn).
    - assert (Hn : read_bytes_aux wm (sv + Z_to_bv 64 4)%bv (length (word_le4 fd2)) <> None).
      { cbn [length word_le4]. change (sv + Z_to_bv 64 4)%bv with (sv + nat_to_word 4)%bv.
        rewrite E2. discriminate. }
      exact (pc_wcov_of_aux (word_le4 fd2) wm (sv + Z_to_bv 64 4)%bv Hn).
  Qed.

  (** * Lengths of the written bytes *)

  Lemma pcw_len_pipe : forall r w, length (pipe_fd_bytes r w) = 8%nat.
  Proof. intros r w. unfold pipe_fd_bytes, le32_bytes. reflexivity. Qed.

  Lemma pcw_len_sigpipe : forall a, length (sigpipe_action_bytes a) = 24%nat.
  Proof.
    intros a. unfold sigpipe_action_bytes.
    rewrite !length_app, !length_Z_to_le_bytes. reflexivity.
  Qed.

  Lemma pcw_stat_len : forall bs, stat_buf_wf bs = true -> length bs = 128%nat.
  Proof.
    intros bs H. unfold stat_buf_wf in H.
    repeat (apply andb_prop in H as [H _]).
    apply Nat.eqb_eq in H. exact H.
  Qed.

  Lemma pcw_nano_len : forall bs, nanosleep_rem_ok_b bs = true -> length bs = 16%nat.
  Proof.
    intros bs H. unfold nanosleep_rem_ok_b in H.
    repeat (apply andb_prop in H as [H _]).
    apply Nat.eqb_eq in H. exact H.
  Qed.

  Lemma pcw_uts_len : forall bs, utsname_wf bs = true -> length bs = 390%nat.
  Proof.
    intros bs H. unfold utsname_wf in H.
    repeat (apply andb_prop in H as [H _]).
    apply Nat.eqb_eq in H. exact H.
  Qed.

  Lemma pcw_rlim_len : forall bs, rlim64_wf bs = true -> length bs = 16%nat.
  Proof.
    intros bs H. unfold rlim64_wf in H.
    repeat (apply andb_prop in H as [H _]).
    apply Nat.eqb_eq in H. exact H.
  Qed.

  (** * pselect6 and ppoll: every choice writes the ranges of the choice [sel = 0] *)

  Definition pcw_sh (w : word * list byte) : word * nat := (fst w, length (snd w)).

  Lemma pcw_waw_shape : forall i ws ws', map pcw_sh ws = map pcw_sh ws' ->
    writes_all_writable i ws = writes_all_writable i ws'.
  Proof.
    intros i ws. unfold writes_all_writable.
    induction ws as [|[a bs] ws IH]; intros [|[a' bs'] ws'] H;
      cbn [map pcw_sh fst snd] in H; try discriminate H; [reflexivity|].
    injection H as Ea El Hr. cbn [forallb fst snd].
    rewrite Ea, El, (IH ws' Hr). reflexivity.
  Qed.

  Lemma pcw_waw_app : forall i l1 l2,
    writes_all_writable i (l1 ++ l2) = (writes_all_writable i l1 && writes_all_writable i l2)%bool.
  Proof. intros i l1 l2. unfold writes_all_writable. apply forallb_app. Qed.

  (** [Select.writes_all_writable] (Sys/Fs/Select.v:677-685) covers each write. *)
  Lemma pcw_waw_cov : forall i ws, writes_all_writable i ws = true ->
    Forall (pc_wcov (in_wmem i)) ws.
  Proof.
    intros i ws. unfold writes_all_writable.
    induction ws as [|[a bs] ws IH]; intros H; [constructor|].
    cbn [forallb fst snd] in H. apply andb_prop in H as [H1 H2].
    constructor; [|exact (IH H2)].
    unfold range_writable in H1.
    destruct (copy_bytes_map (in_wmem i) a (Z.of_nat (length bs))) as [w|] eqn:E;
      cbv beta iota in H1; [|discriminate H1].
    exact (pcw_wcov_cb2 (in_wmem i) a (Z.of_nat (length bs)) w bs E (Z.le_refl _)).
  Qed.

  Lemma pcw_tz_len : Z.of_nat (length pselect_timespec_zero) = 16.
  Proof. reflexivity. Qed.

  (** A core whose every choice writes the ranges of the choice 0. *)
  Definition pcw_core_ok (c : PselectCore) : Prop :=
    match c with
    | PsCoreDone _ ans => forall sel, map pcw_sh (snd (ans sel)) = map pcw_sh (snd (ans 0%Z))
    | _ => True
    end.

  (** An answer whose every choice writes inside the view, and whose remaining time, if any,
      lands on sixteen writable bytes. *)
  Definition pcw_pa_ok (i : SyscallInput) (pa : PselectAnswers) : Prop :=
    forall sel r ws o, pa_ans pa sel = (r, ws, o) ->
      writes_all_writable i ws = true /\
      (forall t s ns, o = Some (t, (s, ns)) -> range_writable i t 16 = true).

  Lemma pcw_fixed_ok : forall i r ws, writes_all_writable i ws = true ->
    pcw_pa_ok i (ps_fixed r ws).
  Proof.
    intros i r ws H sel r' ws' o E. unfold ps_fixed in E. cbn [pa_ans] in E.
    injection E as <- <- <-. split; [exact H | intros t s ns Ho; discriminate Ho].
  Qed.

  Lemma pcw_pa_plain : forall i und (ans : Z -> Z * list (word * list byte)) ws0,
    (forall sel, map pcw_sh (snd (ans sel)) = map pcw_sh ws0) ->
    writes_all_writable i ws0 = true ->
    pcw_pa_ok i (mkPselectAnswers und
                   (fun sel => let '(r, ws) := ans sel in (Z_to_bv 64 r, ws, None))).
  Proof.
    intros i und ans ws0 Hs Hw sel r ws o E. cbn [pa_ans] in E.
    destruct (ans sel) as [r1 ws1] eqn:Es. cbv beta iota in E. injection E as <- <- <-.
    split; [|intros t s ns Ho; discriminate Ho].
    pose proof (Hs sel) as Hs1. rewrite Es in Hs1. cbn [snd] in Hs1.
    rewrite (pcw_waw_shape i ws1 ws0 Hs1). exact Hw.
  Qed.

  Lemma pcw_pa_deadline : forall i und (ans : Z -> Z * list (word * list byte)) ws0 tsp sec nsec,
    (forall sel, map pcw_sh (snd (ans sel)) = map pcw_sh ws0) ->
    writes_all_writable i (ws0 ++ [(tsp, pselect_timespec_zero)]) = true ->
    pcw_pa_ok i (mkPselectAnswers und
                   (fun sel =>
                      let '(r, ws) := ans sel in
                      if Z.eqb r 0
                      then (Z_to_bv 64 0, ws ++ [(tsp, pselect_timespec_zero)], None)
                      else (Z_to_bv 64 r, ws, Some (tsp, (sec, nsec))))).
  Proof.
    intros i und ans ws0 tsp sec nsec Hs Hw sel r ws o E. cbn [pa_ans] in E.
    destruct (ans sel) as [r1 ws1] eqn:Es. cbv beta iota in E.
    pose proof (Hs sel) as Hs1. rewrite Es in Hs1. cbn [snd] in Hs1.
    rewrite pcw_waw_app in Hw. apply andb_prop in Hw as [Hw0 Hwt].
    assert (Hw1 : writes_all_writable i ws1 = true)
      by (rewrite (pcw_waw_shape i ws1 ws0 Hs1); exact Hw0).
    assert (Ht : range_writable i tsp 16 = true).
    { unfold writes_all_writable in Hwt. cbn [forallb fst snd] in Hwt.
      apply andb_prop in Hwt as [Hwt _]. rewrite pcw_tz_len in Hwt. exact Hwt. }
    destruct (Z.eqb r1 0); cbv beta iota in E; injection E as <- <- <-.
    - split; [|intros t s ns Ho; discriminate Ho].
      rewrite pcw_waw_app, Hw1. exact Hwt.
    - split; [exact Hw1|]. intros t s ns Ho. injection Ho as <- <- <-. exact Ht.
  Qed.

  (* An errno answer of [Select.pselect_err] (Sys/Fs/Select.v:902-903): no write. *)
  Ltac pcw_err_ok H :=
    unfold pselect_err in H; injection H as <-; apply pcw_fixed_ok; reflexivity.

  (** [Select.pselect_finish] (Sys/Fs/Select.v:1025-1063). *)
  Lemma pcw_finish_ok : forall i tsp tmo c pa, pcw_core_ok c ->
    pselect_finish i tsp tmo c = Some pa -> pcw_pa_ok i pa.
  Proof.
    intros i tsp tmo c pa Hc H. unfold pselect_finish in H.
    destruct c as [| e | und ans]; cbv beta iota in H.
    - discriminate H.
    - destruct tmo as [| | | | sec nsec]; cbv beta iota in H;
        [ pcw_err_ok H | pcw_err_ok H | pcw_err_ok H | pcw_err_ok H | ].
      destruct (writes_all_writable i [(tsp, pselect_timespec_zero)]) eqn:Ew;
        cbv beta iota in H; [|discriminate H].
      injection H as <-. intros sel r ws o E. cbn [pa_ans] in E. injection E as <- <- <-.
      split; [reflexivity|]. intros t s ns Ho. injection Ho as <- <- <-.
      unfold writes_all_writable in Ew. cbn [forallb fst snd] in Ew.
      apply andb_prop in Ew as [Ew _]. rewrite pcw_tz_len in Ew. exact Ew.
    - unfold pcw_core_ok in Hc. cbv beta iota in Hc.
      destruct (ans 0%Z) as [r0 ws0] eqn:E0. cbn [snd] in Hc. cbv beta iota in H.
      destruct tmo as [| | | | sec nsec]; cbv beta iota in H; try discriminate H.
      + destruct (Z.eqb r0 0); cbv beta iota in H; [discriminate H|].
        destruct (writes_all_writable i ws0) eqn:Ew; cbv beta iota in H; [|discriminate H].
        injection H as <-. exact (pcw_pa_plain i und ans ws0 Hc Ew).
      + destruct (writes_all_writable i ws0) eqn:Ew; cbv beta iota in H; [|discriminate H].
        injection H as <-. exact (pcw_pa_plain i und ans ws0 Hc Ew).
      + destruct (writes_all_writable i (ws0 ++ [(tsp, pselect_timespec_zero)])) eqn:Ew;
          cbv beta iota in H; [|discriminate H].
        injection H as <-. exact (pcw_pa_deadline i und ans ws0 tsp sec nsec Hc Ew).
  Qed.

  Lemma pcw_fdwb_sh : forall p n v,
    map pcw_sh (fd_set_writeback p n v)
    = (if negb (pselect_touches_sets n) then [] else if w_is0 p then [] else [(p, 8%nat)]).
  Proof.
    intros p n v. unfold fd_set_writeback.
    destruct (negb (pselect_touches_sets n)); [reflexivity|].
    destruct (w_is0 p); reflexivity.
  Qed.

  (** [Select.pselect_core] (Sys/Fs/Select.v:846-880). *)
  Lemma pcw_pselect_core_ok : forall i m n32 inp outp exp,
    pcw_core_ok (pselect_core i m n32 inp outp exp).
  Proof.
    intros i m n32 inp outp exp. unfold pselect_core. cbv zeta.
    repeat (match goal with
            | |- context [match ?x with _ => _ end] =>
                first [ is_var x; destruct x | lazymatch x with _ _ => destruct x end ]
            end; cbv beta iota).
    all: try exact I.
    unfold pcw_core_ok. cbv beta iota. intros sel. cbv beta zeta. cbn [snd].
    rewrite !map_app, !pcw_fdwb_sh. reflexivity.
  Qed.

  Lemma pcw_pick_len : forall cs sel, length (ppoll_pick cs sel) = length cs.
  Proof.
    induction cs as [|[[fd lo] hi] cs IH]; intros sel; cbn [ppoll_pick length]; [reflexivity|].
    rewrite IH. reflexivity.
  Qed.

  Lemma pcw_ppwb_sh : forall rs rs' p, length rs = length rs' ->
    map pcw_sh (ppoll_writeback p rs) = map pcw_sh (ppoll_writeback p rs').
  Proof.
    induction rs as [|r rs IH]; intros [|r' rs'] p H; cbn [length] in H;
      try discriminate H; [reflexivity|].
    cbn [ppoll_writeback map pcw_sh fst snd word_le2 length]. injection H as H.
    rewrite (IH rs' _ H). reflexivity.
  Qed.

  (** [Select.ppoll_core] (Sys/Fs/Select.v:1566-1574). *)
  Lemma pcw_ppoll_core_ok : forall i m ufds nfds, pcw_core_ok (ppoll_core i m ufds nfds).
  Proof.
    intros i m ufds nfds. unfold ppoll_core.
    destruct (ppoll_scan i m ufds nfds) as [| e | cs]; try exact I.
    unfold pcw_core_ok. cbv beta iota. intros sel. cbv beta zeta. cbn [snd].
    apply pcw_ppwb_sh. rewrite !pcw_pick_len. reflexivity.
  Qed.

  (** [Select.ppoll_writeback_access] (Sys/Fs/Select.v:1636-1646). *)
  Lemma pcw_wba_ok : forall ufds nfds tmo c, pcw_core_ok c ->
    pcw_core_ok (ppoll_writeback_access ufds nfds tmo c).
  Proof.
    intros ufds nfds tmo c H. destruct c as [| e | und ans]; [exact I | exact I |].
    unfold ppoll_writeback_access. cbv beta iota.
    destruct (access_okb ufds (pollfd_bytes * bv_unsigned nfds)); [exact H|].
    destruct tmo; try exact I.
    destruct (fst (ans 0%Z) =? 0)%Z; exact I.
  Qed.

  (** [Select.pselect6_outcome] (Sys/Fs/Select.v:1108-1124). *)
  Lemma pcw_pselect6_pa : forall i m n32 inp outp exp tsp sig pa,
    pselect6_outcome i m n32 inp outp exp tsp sig = Some pa -> pcw_pa_ok i pa.
  Proof.
    intros i m n32 inp outp exp tsp sig pa H.
    unfold pselect6_outcome in H. cbv zeta in H.
    destruct (pselect_sigpack (in_mem i) sig);
      destruct (pselect_timeout (in_mem i) tsp) as [| | | | sec nsec];
      cbv beta iota in H;
      try (pcw_err_ok H);
      try discriminate H;
      (eapply pcw_finish_ok; [|exact H]; apply pcw_pselect_core_ok).
  Qed.

  (** [Select.ppoll_outcome] (Sys/Fs/Select.v:1699-1718). *)
  Lemma pcw_ppoll_pa : forall i m ufds nfds tsp sig sigsetsize pa,
    ppoll_outcome i m ufds nfds tsp sig sigsetsize = Some pa -> pcw_pa_ok i pa.
  Proof.
    intros i m ufds nfds tsp sig sigsetsize pa H. unfold ppoll_outcome in H.
    destruct (pselect_timeout (in_mem i) tsp) as [| | | | sec nsec]; cbv beta iota in H;
      try (pcw_err_ok H).
    all: destruct (ppoll_sigmask (in_mem i) sig sigsetsize); cbv beta iota in H;
      try (pcw_err_ok H); try discriminate H.
    all: eapply pcw_finish_ok; [|exact H].
    all: apply pcw_wba_ok; apply pcw_ppoll_core_ok.
  Qed.

  (** [Checks.Sys.Fs.Select.check_pselect_answer] (Checks/Sys/Fs/Select.v:35-53): the writes it
      accepts are a choice's writes, then the remaining time at [tsp]. *)
  Lemma pcw_answer_cov : forall i pa rd reads rec eff m m' evs,
    pcw_pa_ok i pa ->
    check_pselect_answer pa rd reads rec eff m = CheckOk m' evs ->
    Forall (pc_wcov (in_wmem i)) (eff_writes eff) /\ eff_zeros eff = [] /\ eff_copies eff = []
    /\ exists sel, m' = rec sel m.
  Proof.
    intros i pa rd reads rec [r' ws' zs us cs ks] m m' evs Hpa H.
    unfold check_pselect_answer in H.
    destruct zs as [|? ?]; [|discriminate H].
    destruct us as [|? ?]; [|discriminate H].
    destruct cs as [|? ?]; [|discriminate H].
    cbv beta iota in H.
    destruct (access_ranges_eqb ks reads); cbv beta iota in H; [|discriminate H].
    cbn [eff_writes eff_zeros eff_copies].
    destruct (pa_ans pa (Z.land (pa_und pa) (rd ws'))) as [[r ws] [[tsp [sec nsec]]|]] eqn:Ea;
      cbv beta iota in H.
    - destruct (Hpa _ _ _ _ Ea) as [Hw Ht].
      pose proof (Ht tsp sec nsec eq_refl) as Htsp.
      match type of H with context [if ?b then _ else _] => destruct b eqn:Hg end;
        cbv beta iota in H; [|discriminate H].
      injection H as <- <-.
      apply andb_prop in Hg as [Hg Hok]. apply andb_prop in Hg as [_ Heq].
      apply writes_eqb_eq in Heq.
      split; [|split; [reflexivity|split; [reflexivity|]]].
      2: { exists (Z.land (pa_und pa) (rd ws')). reflexivity. }
      rewrite Heq. apply Forall_app. split; [exact (pcw_waw_cov i ws Hw)|].
      constructor; [|constructor].
      unfold pselect_remaining_ok in Hok.
      apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [Hl _].
      apply Nat.eqb_eq in Hl.
      unfold range_writable in Htsp.
      destruct (copy_bytes_map (in_wmem i) tsp 16) as [w|] eqn:Ec; cbv beta iota in Htsp;
        [|discriminate Htsp].
      apply (pcw_wcov_cb2 (in_wmem i) tsp 16 w _ Ec). rewrite Hl. lia.
    - destruct (Hpa _ _ _ _ Ea) as [Hw _].
      match type of H with context [if ?b then _ else _] => destruct b eqn:Hg end;
        cbv beta iota in H; [|discriminate H].
      injection H as <- <-.
      apply andb_prop in Hg as [_ Heq]. apply writes_eqb_eq in Heq. subst ws'.
      refine (conj (pcw_waw_cov i ws Hw) (conj eq_refl (conj eq_refl _))).
      eexists. reflexivity.
  Qed.

  (** * Zero-fills and copies of mremap off the window *)

  Lemma pcw_add_unsigned : forall a b : word, bv_unsigned a + bv_unsigned b < two_pow_64 ->
    bv_unsigned (a + b)%bv = bv_unsigned a + bv_unsigned b.
  Proof.
    intros a b H. rewrite bv_add_unsigned. apply bv_wrap_small.
    pose proof (word_unsigned_range a). pose proof (word_unsigned_range b).
    change (bv_modulus 64) with two_pow_64. lia.
  Qed.

  Lemma pcw_prup_nonneg : forall z, 0 <= z -> 0 <= page_round_up_Z z.
  Proof.
    intros z Hz. unfold page_round_up_Z, page_size.
    pose proof (Z.div_pos (z + 4096 - 1) 4096 ltac:(lia) ltac:(lia)). lia.
  Qed.

  Lemma pcw_rf_app_l : forall l1 l2 (lo n : word),
    region_free (l1 ++ l2) lo n = true -> region_free l1 lo n = true.
  Proof.
    intros l1 l2 lo n H. apply region_free_intro. intros a sz Hin.
    exact (region_free_In _ _ _ _ _ H (in_or_app _ _ _ (or_introl Hin))).
  Qed.

  (** The grown tail [[base + oZ, base + nZ)] ([Mremap.mremap_tail], Sys/Mm/Mremap.v:209-213)
      is a sub-range of [[base, base + nZ)]. *)
  Lemma pcw_tail_off : forall (base : word) (oZ nZ : Z),
    0 <= oZ -> oZ < nZ -> bv_unsigned base + nZ < two_pow_64 ->
    range_off vlo vhi (base, Z_to_bv 64 nZ) ->
    Forall (range_off vlo vhi) (mremap_tail base (Z_to_bv 64 oZ) oZ nZ).
  Proof.
    intros base oZ nZ H0 Hlt Hb Ho. unfold mremap_tail.
    rewrite (proj2 (Z.ltb_lt oZ nZ) Hlt). cbv beta iota.
    pose proof (word_unsigned_range base) as Rb.
    assert (Eo : bv_unsigned (Z_to_bv 64 oZ) = oZ)
      by (apply bv_unsigned_Z_to_bv_u64; lia).
    assert (En : bv_unsigned (Z_to_bv 64 nZ) = nZ)
      by (apply bv_unsigned_Z_to_bv_u64; lia).
    assert (Ed : bv_unsigned (Z_to_bv 64 (nZ - oZ)) = nZ - oZ)
      by (apply bv_unsigned_Z_to_bv_u64; lia).
    assert (Ea : bv_unsigned (base + Z_to_bv 64 oZ)%bv = bv_unsigned base + oZ).
    { rewrite pcw_add_unsigned; rewrite Eo; lia. }
    constructor; [|constructor].
    unfold range_off in *. cbn [fst snd] in *.
    rewrite Ea, Ed. rewrite En in Ho. lia.
  Qed.

  (** The in-place grow: [mremap_inplace_grow_b] (Sys/Mm/Mremap.v:320-334) tests the grown range
      [region_free] against [vm_reserved ++ ...]. *)
  Lemma pcw_grow_zeros : forall mo (old : word) (oZ nZ : Z), mm_vinv vlo vhi mo ->
    0 <= oZ -> oZ < nZ ->
    mremap_inplace_grow_b mo old (Z_to_bv 64 oZ) (Z_to_bv 64 nZ) oZ nZ = true ->
    Forall (range_off vlo vhi) (mremap_tail old (Z_to_bv 64 oZ) oZ nZ).
  Proof.
    intros mo old oZ nZ VI H0 Hlt H.
    unfold mremap_inplace_grow_b, mremap_inplace_room_b in H. cbv zeta in H.
    apply andb_prop in H as [H _]. apply andb_prop in H as [Htop Hrf].
    apply Z.leb_le in Htop.
    pose proof (alloc_top_lt (m_vmmaps mo)) as Hac.
    apply pcw_rf_app_l in Hrf.
    pose proof (pc_off_res0 vlo vhi mo old (Z_to_bv 64 nZ) VI Hrf) as Ho.
    apply pcw_tail_off; [exact H0 | exact Hlt | lia | exact Ho].
  Qed.

  (** The move: [mremap_fresh_b] (Sys/Mm/Mremap.v:439-447) tests the destination [region_free]
      against [vm_reserved ++ vm_maps]; the tail and the copied head are sub-ranges of it. *)
  Lemma pcw_move_off : forall mo (oZ nZ : Z) (old r : word), mm_vinv vlo vhi mo ->
    0 <= oZ -> oZ < nZ ->
    mremap_fresh_b mo oZ nZ old (Z_to_bv 64 oZ) r (Z_to_bv 64 nZ) = true ->
    Forall (range_off vlo vhi) (mremap_tail r (Z_to_bv 64 oZ) oZ nZ)
    /\ Forall (fun c => range_off vlo vhi (copy_dst c, copy_len c)) [mkCopy old r (Z_to_bv 64 oZ)].
  Proof.
    intros mo oZ nZ old r VI H0 Hlt H.
    unfold mremap_fresh_b in H. cbv zeta in H.
    apply andb_prop in H as [H _]. apply andb_prop in H as [H Hrf].
    apply andb_prop in H as [H Htop]. apply Z.leb_le in Htop.
    pose proof (alloc_top_lt (m_vmmaps mo)) as Hac.
    pose proof (word_unsigned_range r) as Rr.
    pose proof (vinv_off_res vlo vhi mo r (Z_to_bv 64 nZ) VI Hrf) as Ho.
    split.
    - apply pcw_tail_off; [exact H0 | exact Hlt | lia | exact Ho].
    - constructor; [|constructor]. cbn [copy_dst copy_len].
      apply (off_shrink vlo vhi r (Z_to_bv 64 oZ) (Z_to_bv 64 nZ)); [|exact Ho].
      rewrite !bv_unsigned_Z_to_bv_u64 by (unfold two_pow_64 in *; lia). lia.
  Qed.

  (** * The checker walk (PairClean.v's [pcl_unfold], [pcl_walk], [pcl_norm], [pcl_bound],
        [pcl_kern], under new names; [pcw_norm] adds the [orb] and contradiction cases the
        arms here reach) *)

  Ltac pcw_unfold H :=
    cbv beta iota zeta delta [check_ret_only check_ret_only_copyins clear_copyins with_copyins
      check_copyins check_copyins_after check_copyin_prefix strip_copyin_prefix eff_is_errno
      check_efault_or check_access_ok_zero check_sigpipe_write check_sigpipe_writev
      check_new_fd_result check_open_result
      eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins] in H.

  Ltac pcw_walk H :=
    repeat (cbv beta iota zeta delta [eff_ret eff_writes eff_zeros eff_unmaps eff_copies
                                      eff_copyins] in H;
            match type of H with
            | context [match ?x with _ => _ end] =>
                first [ is_var x; destruct x
                      | lazymatch x with _ _ => destruct x eqn:? end ]
            end);
    try discriminate H.

  Ltac pcw_norm :=
    repeat match goal with
    | Hb : andb _ _ = true |- _ => apply andb_prop in Hb; destruct Hb
    | Hb : orb _ _ = false |- _ => apply orb_false_elim in Hb; destruct Hb
    | Hb : orb false ?b = true |- _ => change (b = true) in Hb
    | Hb : orb true _ = true |- _ => clear Hb
    | Hb : negb _ = true |- _ => apply negb_true_iff in Hb
    | Hb : negb _ = false |- _ => apply negb_false_iff in Hb
    | Hb : bv_eqb _ _ = true |- _ => apply bv_eqb_eq in Hb
    | Hb : listN_eqb _ _ = true |- _ => apply listN_eqb_eq in Hb
    | Hb : listNN_eqb _ _ = true |- _ => apply listNN_eqb_eq in Hb
    | Hb : writes_eqb _ _ = true |- _ => apply writes_eqb_eq in Hb
    | Hb : listCopy_eqb _ _ = true |- _ => apply listCopy_eqb_eq in Hb
    | Hb : access_ranges_eqb _ _ = true |- _ => apply access_ranges_eqb_eq in Hb
    | Hb : Z.leb _ _ = true |- _ => apply Z.leb_le in Hb
    | Hb : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hb
    | Hb : Z.leb _ _ = false |- _ => apply Z.leb_gt in Hb
    | Hb : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in Hb
    | Hb : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hb
    | Hb : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in Hb
    | Hb : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in Hb
    | Hb : true = false |- _ => discriminate Hb
    | Hb : false = true |- _ => discriminate Hb
    | Hb : @cons _ _ _ = @cons _ _ _ |- _ => injection Hb; intros; try clear Hb
    | Hb : @pair _ _ _ _ = @pair _ _ _ _ |- _ => injection Hb; intros; try clear Hb
    | Hb : @nil _ = @cons _ _ _ |- _ => discriminate Hb
    | Hb : @cons _ _ _ = @nil _ |- _ => discriminate Hb
    end; subst.

  (* [Z.of_nat (length L) < two_pow_64] (PairClean.v's [pcl_bound]). *)
  Ltac pcw_bound :=
    try match goal with
        | E : ?t = ?L |- context [length ?L] =>
            lazymatch L with _ :: _ => rewrite <- E end
        end;
    first
      [ (try unfold MAX_RW_COUNT in *; unfold two_pow_64 in *; lia)
      | (eapply Z.le_lt_trans; [apply pc_file_read_len | exact (proj2 (word_unsigned_range _))])
      | (match goal with |- context [length (pipe_take ?q ?k)] => pose proof (pipe_take_length q k) end;
         try unfold MAX_RW_COUNT in *; unfold two_pow_64 in *; lia) ].

  (* The length facts the checker's predicates on the written bytes give, and the pins. *)
  Ltac pcw_lenfacts :=
    repeat match goal with
    | Hb : stat_buf_wf ?bs = true |- _ => pose proof (pcw_stat_len bs Hb); clear Hb
    | Hb : nanosleep_rem_ok_b ?bs = true |- _ => pose proof (pcw_nano_len bs Hb); clear Hb
    | Hb : utsname_wf ?bs = true |- _ => pose proof (pcw_uts_len bs Hb); clear Hb
    | Hb : rlim64_wf ?bs = true |- _ => pose proof (pcw_rlim_len bs Hb); clear Hb
    | Hp : PinsOk.pins_ok ?mo, Hu : m_utsname ?mo = Some ?b |- _ =>
        pose proof (proj1 Hp b Hu); clear Hu
    | Hp : PinsOk.pins_ok ?mo, Hu : m_rlimit_core ?mo = Some ?b |- _ =>
        pose proof (proj2 Hp b Hu); clear Hu
    end.

  Ltac pcw_lit :=
    try unfold NSIG_BYTES; try unfold STAT_SIZE; try unfold NEW_UTSNAME_SIZE;
    unfold two_pow_64; lia.

  (* [Z.of_nat (length bs) <= bv_unsigned n], or [<= k]. *)
  Ltac pcw_len :=
    first
      [ (rewrite len_word_unsigned; [lia | pcw_bound])
      | (try unfold MAX_RW_COUNT in *; try unfold two_pow_64 in *; lia)
      | (pcw_lenfacts;
         rewrite ?bv_unsigned_Z_to_bv_u64 by pcw_lit;
         rewrite ?length_app, ?length_firstn, ?length_Z_to_le_bytes, ?pcw_len_pipe,
           ?pcw_len_sigpipe;
         cbn [length word_le8 word_le4 word_le2 unix_unnamed_addr];
         try unfold NSIG_BYTES in *; try unfold STAT_SIZE in *;
         try unfold NEW_UTSNAME_SIZE in *;
         lia) ].

  (* One write, against the gate the checker tested on its range. *)
  Ltac pcw_cov :=
    match goal with
    | Hr : read_bytes_map (in_wmem ?i) ?a ?n = Some _ |- pc_wcov (in_wmem ?i) (?a, ?bs) =>
        apply (pc_wcov_rb (in_wmem i) a n _ bs Hr); pcw_len
    | Hw : wmem_ok ?i ?a ?n = true |- pc_wcov (in_wmem ?i) (?a, ?bs) =>
        apply (pc_wcov_wok i a n bs Hw); pcw_len
    | Hc : copy_bytes_map (in_wmem ?i) ?a ?k = Some _ |- pc_wcov (in_wmem ?i) (?a, ?bs) =>
        apply (pcw_wcov_cb2 (in_wmem i) a k _ bs Hc); pcw_len
    | Hu : user_range_writable ?i ?a ?k = true |- pc_wcov (in_wmem ?i) (?a, ?bs) =>
        apply (pcw_urw_cov i a k bs Hu); pcw_len
    end.

  (* A leaf's write list, split only where it is a syntactic list. *)
  Ltac pcw_ws :=
    repeat lazymatch goal with
    | |- Forall _ [] => apply Forall_nil
    | |- Forall _ (_ :: _) => apply Forall_cons; [try pcw_cov |]
    end.

  (* The write lists [pcw_ws] leaves: a delivery, a scatter, the socketpair stores. *)
  Ltac pcw_close :=
    first
      [ pcw_cov
      | match goal with
        | Hr : read_bytes_map (in_wmem ?i) ?buf (len_word ?del) = Some _
          |- Forall (pc_wcov (in_wmem ?i)) (delivered_writes ?buf ?del) =>
            apply (pc_cov_delivered (in_wmem i) buf del _ Hr); pcw_bound
        end
      | match goal with
        | Hs : scatter_iovecs (in_wmem ?i) _ _ = Some ?ws |- Forall (pc_wcov (in_wmem ?i)) ?ws =>
            exact (pcw_scatter_cov (in_wmem i) _ _ ws Hs)
        end
      | match goal with
        | Hd : socketpair_dest_writable (in_wmem ?i) ?sv = true
          |- Forall (pc_wcov (in_wmem ?i)) (socketpair_writes ?sv _ _) =>
            apply (pcw_socketpair_cov (in_wmem i) sv _ _ Hd)
        end ].

  Ltac pcw_kern :=
    first
      [ reflexivity
      | (rewrite ?pcl_k_raise, ?pcl_k_sigmask, ?pcl_k_forget, ?pcl_k_brk, ?pcl_k_backing,
           ?pcl_k_repl; reflexivity)
      | (repeat (match goal with
                 | |- context [match ?x with _ => _ end] =>
                     first [ is_var x; destruct x | lazymatch x with _ _ => destruct x end ]
                 end; cbv beta iota);
         rewrite ?pcl_k_raise, ?pcl_k_sigmask, ?pcl_k_forget, ?pcl_k_brk, ?pcl_k_backing,
           ?pcl_k_repl; reflexivity) ].

  (* A leaf of a call that does not touch the address space. *)
  Ltac pcw_nleaf H :=
    injection H as <- <-; pcw_norm;
    unfold pc_nm; cbn [eff_writes eff_zeros eff_copies app];
    refine (conj _ (conj eq_refl (conj eq_refl _))); [pcw_ws | pcw_kern].

  (* mremap's zero-fills and copies. *)
  Ltac pcw_mr_zeros VI :=
    first
      [ apply Forall_nil
      | match goal with
        | Hg : mremap_inplace_grow_b ?mo ?old _ _ ?oZ ?nZ = true
          |- Forall _ (mremap_tail ?old _ ?oZ ?nZ) =>
            apply (pcw_grow_zeros mo old oZ nZ VI); [lia | lia | exact Hg]
        end
      | match goal with
        | Hf : mremap_fresh_b ?mo ?oZ ?nZ ?old _ ?r _ = true
          |- Forall _ (mremap_tail ?r _ ?oZ ?nZ) =>
            exact (proj1 (pcw_move_off mo oZ nZ old r VI ltac:(lia) ltac:(lia) Hf))
        end ].

  Ltac pcw_mr_copies VI :=
    first
      [ apply Forall_nil
      | match goal with
        | Hf : mremap_fresh_b ?mo ?oZ ?nZ ?old _ ?r _ = true |- _ =>
            exact (proj2 (pcw_move_off mo oZ nZ old r VI ltac:(lia) ltac:(lia) Hf))
        end ].

  Ltac pcw_mrleaf H VI :=
    injection H as <- <-; pcw_norm;
    unfold pc_mm; cbn [eff_writes eff_zeros eff_copies];
    refine (conj _ (conj _ (conj _ (conj _ _))));
    [ apply Forall_nil | pcw_mr_zeros VI | pcw_mr_copies VI | reflexivity | reflexivity ].

  (** * The arms, checker by checker *)

  Lemma pcw_n_getcwd : forall i size eff m m' evs,
    check_getcwd size eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i size [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_getcwd] in H. pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
  Qed.

  Lemma pcw_n_epoll_pwait : forall i epfd events maxevents32 sigmask sigsetsize eff m m' evs,
    check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m = CheckOk m' evs ->
    pc_nm i m eff m'.
  Proof.
    intros i epfd events maxevents32 sigmask sigsetsize [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_epoll_pwait] in H. pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
  Qed.

  (* The 8-byte store behind the 8-byte [read_bytes_map] (Fs/Pipe.v:60-75). *)
  Lemma pcw_n_pipe2 : forall i fildes flags eff m m' evs,
    check_pipe2 i fildes flags eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fildes flags [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_pipe2] in H. pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
    all: first
      [ pcw_close
      | (* the two descriptors' 8 bytes ([pipe_fd_bytes], two [le32_bytes]) against the 8-byte read *)
        match goal with
        | Hr : read_bytes_map (in_wmem ?i) ?a ?n = Some _ |- pc_wcov (in_wmem ?i) (?a, ?bs) =>
            apply (pc_wcov_rb (in_wmem i) a n _ bs Hr);
            unfold pipe_fd_bytes, le32_bytes in *;
            rewrite ?bv_unsigned_Z_to_bv_u64 by pcw_lit; cbn; lia
        end ].
  Qed.

  Lemma pcw_n_getdents64 : forall i fd count eff m m' evs,
    check_getdents64 fd count eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd count [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_getdents64] in H. pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
  Qed.

  (* Every delivery is a scatter through [in_wmem] (Fs/ReadWrite.v:6767-6936). *)
  Lemma pcw_n_readv : forall i fd iov iovcnt eff m m' evs,
    check_readv i fd iov iovcnt eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd iov iovcnt [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_readv check_readv_imported check_readv_gap
      check_stream_read_empty check_stream_read_reset] in H.
    pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
    all: pcw_close.
  Qed.

  (* The file delivery behind [read_bytes_map] of it (Fs/ReadWrite.v:4222), the urandom one
     behind :49. *)
  Lemma pcw_n_pread64 : forall i fd buf count pos eff m m' evs,
    check_pread64 i fd buf count pos eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd buf count pos [ret ws zs us cs ci] m m' evs H.
    pose proof (rw_count_clamp_range count) as Rc.
    cbv beta iota zeta delta [check_pread64 check_read_urandom] in H.
    pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
    all: pcw_close.
  Qed.

  Lemma pcw_n_pselect6 : forall i n32 inp outp exp tsp sig eff m m' evs,
    check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i n32 inp outp exp tsp sig eff m m' evs H. unfold check_pselect6 in H.
    destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [pa|] eqn:Ho;
      cbv beta iota in H; [|discriminate H].
    assert (Hpa : pcw_pa_ok i pa) by (eapply pcw_pselect6_pa; exact Ho).
    destruct (pcw_answer_cov i pa _ _ _ eff m m' evs Hpa H) as (Hw & Hz & Hc & sel & Hm).
    unfold pc_nm. rewrite Hm. exact (conj Hw (conj Hz (conj Hc eq_refl))).
  Qed.

  Lemma pcw_n_ppoll : forall i ufds nfds tsp sig sigsetsize eff m m' evs,
    check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i ufds nfds tsp sig sigsetsize eff m m' evs H. unfold check_ppoll in H.
    destruct (ppoll_outcome i m ufds nfds tsp sig sigsetsize) as [pa|] eqn:Ho;
      cbv beta iota in H; [|discriminate H].
    assert (Hpa : pcw_pa_ok i pa) by (eapply pcw_ppoll_pa; exact Ho).
    destruct (pcw_answer_cov i pa _ _ _ eff m m' evs Hpa H) as (Hw & Hz & Hc & sel & Hm).
    unfold pc_nm. rewrite Hm. exact (conj Hw (conj Hz (conj Hc eq_refl))).
  Qed.

  Lemma pcw_n_readlinkat : forall i dirfd eff m m' evs,
    check_readlinkat dirfd eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i dirfd [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_readlinkat] in H. pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
  Qed.

  Lemma pcw_n_newfstatat : forall i dirfd pathp flag eff m m' evs,
    check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i dirfd pathp flag [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_newfstatat] in H. pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
  Qed.

  (* The 128-byte store behind [read_bytes_map] of [STAT_SIZE] bytes, its length from
     [stat_buf_wf] (Fs/Stat.v:323). *)
  Lemma pcw_n_fstat : forall i fd statbuf eff m m' evs,
    check_fstat i fd statbuf eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd statbuf [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_fstat check_fstat_file check_fstat_deliver
      check_fstat_deliver_by check_fstat_chrdev check_fstat_devnull check_fstat_urandom
      check_fstat_anon check_fstat_anon_deliver] in H.
    pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
    all: pcw_close.
  Qed.

  (* The remainder behind [copy_bytes_map (in_wmem i) rmtp 16] (Kernel/Time/Hrtimer.v:94). *)
  Lemma pcw_n_nanosleep : forall i rqtp rmtp eff m m' evs,
    check_nanosleep i rqtp rmtp eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i rqtp rmtp [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_nanosleep] in H. pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
    all: pcw_close.
  Qed.

  Lemma pcw_n_sched_getaffinity : forall i len eff m m' evs,
    check_sched_getaffinity len eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i len [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_sched_getaffinity] in H. pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
  Qed.

  Lemma pcw_n_sigaltstack : forall i uss uoss eff m m' evs,
    check_sigaltstack i uss uoss eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i uss uoss [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_sigaltstack] in H. pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
  Qed.

  (* SIGPIPE's [oact]: the 24 bytes behind the 24-byte [read_bytes_map] (Kernel/Signal.v:215). *)
  Lemma pcw_n_rt_sigaction : forall i sig act oact ss eff m m' evs,
    check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i sig act oact ss [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_rt_sigaction check_rt_sigaction_sigpipe
      check_sigpipe_oact_write check_one_write] in H.
    pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
    all: pcw_close.
  Qed.

  (* [oset]: the 8 bytes behind the 8-byte [read_bytes_map] (Kernel/Signal.v:752). *)
  Lemma pcw_n_rt_sigprocmask : forall i how nset oset ss eff m m' evs,
    check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i how nset oset ss [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_rt_sigprocmask check_write_oset check_write_oset_copyins
      check_one_write] in H.
    pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
    all: pcw_close.
  Qed.

  Lemma pcw_n_getgroups : forall i gidsetsize eff m m' evs,
    check_getgroups gidsetsize eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i gidsetsize [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_getgroups] in H. pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
  Qed.

  (* The name behind the 390-byte [read_bytes_map] (Kernel/Sys.v:174): [utsname_wf] of it, or
     the pin, which [PinsOk.pins_ok] bounds. *)
  Lemma pcw_n_uname : forall i name eff m m' evs, PinsOk.pins_ok m ->
    check_uname i name eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i name [ret ws zs us cs ci] m m' evs Hp H.
    cbv beta iota zeta delta [check_uname check_uname_copy uts_repeat_okb] in H.
    pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
    all: pcw_close.
  Qed.

  (* The two stores behind the 8-byte destination test (Net/Socket.v:3363). *)
  Lemma pcw_n_socketpair : forall i family type protocol sv eff m m' evs,
    check_socketpair i family type protocol sv eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i family type protocol sv [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_socketpair check_socketpair_written
      check_socketpair_unix_written check_socketpair_faulted] in H.
    pcw_unfold H. pcw_walk H.
    (* The checker compares the effect's store list, a cons once walked, with [socketpair_writes]
       ([writes_eqb]); put [socketpair_writes] back in the effect, so the leaf's store list is the
       one [pcw_close]'s socketpair case covers through [socketpair_dest_writable]. *)
    all: try (repeat match goal with Hb : andb _ _ = true |- _ => apply andb_prop in Hb; destruct Hb end;
              match goal with
              | Hw : writes_eqb (?w :: ?ws) (socketpair_writes ?sv ?a ?b) = true |- _ =>
                  apply writes_eqb_eq in Hw; rewrite Hw
              end).
    all: pcw_nleaf H.
    all: pcw_close.
  Qed.

  Lemma pcw_n_accept4 : forall i fd addrp addrlenp flags eff m m' evs,
    check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd addrp addrlenp flags [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_accept4 check_errno_only check_errno_or_list] in H.
    pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
  Qed.

  (* The stores behind [user_range_writable] (Net/Socket.v:1613-1617). *)
  Lemma pcw_n_getsockname : forall i fd eff m m' evs,
    check_getsockname i fd eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_getsockname check_stream_getname
      check_ret_writes_copyins] in H.
    pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
    all: pcw_close.
  Qed.

  Lemma pcw_n_getpeername : forall i fd eff m m' evs,
    check_getpeername i fd eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_getpeername check_stream_getname
      check_ret_writes_copyins] in H.
    pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
    all: pcw_close.
  Qed.

  (* A stream delivery behind [read_bytes_map] of it (Fs/ReadWrite.v:634). *)
  Lemma pcw_n_recvfrom : forall i fd buf size eff m m' evs,
    check_recvfrom i fd buf size eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd buf size [ret ws zs us cs ci] m m' evs H.
    pose proof (rw_count_clamp_range size) as Rc.
    cbv beta iota zeta delta [check_recvfrom check_stream_read check_stream_read_empty
      check_stream_read_reset check_recv_fd_answer] in H.
    pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
    all: pcw_close.
  Qed.

  (* The stores behind [user_range_writable] (Net/Socket.v:1767-1772). *)
  Lemma pcw_n_getsockopt : forall i fd level optlenp eff m m' evs,
    check_getsockopt i fd level optlenp eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd level optlenp [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_getsockopt check_stream_getsockopt
      check_ret_writes_copyins] in H.
    pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
    all: first
      [ pcw_close
      | (* the option value's copy-out is empty when its length is 0, else it takes its
           writability from the disjunction's right side; the optlen store from its own test *)
        match goal with |- context [if ?c =? 0 then _ else _] => destruct (c =? 0) eqn:Ez end;
        cbn [orb app] in *;
        repeat first [ (apply Forall_app; split) | apply Forall_cons | apply Forall_nil ];
        pcw_cov ].
  Qed.

  Lemma pcw_n_recvmsg : forall i fd flags eff m m' evs,
    check_recvmsg fd flags eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd flags [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_recvmsg check_recv_fd_answer] in H.
    pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
  Qed.

  Lemma pcw_n_wait4 : forall i upid stat_addr options rusage eff m m' evs,
    check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i upid stat_addr options rusage [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_wait4] in H. pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
  Qed.

  (* The [struct rlimit64] behind [copy_bytes_map (in_wmem i) old_rlim 16] (Kernel/Sys.v:101):
     [rlim64_wf] of it, or the pin, which [PinsOk.pins_ok] bounds. *)
  Lemma pcw_n_prlimit64 : forall i pid resource new_rlim old_rlim eff m m' evs,
    PinsOk.pins_ok m ->
    check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i pid resource new_rlim old_rlim [ret ws zs us cs ci] m m' evs Hp H.
    cbv beta iota zeta delta [check_prlimit64 check_rlim64_read] in H.
    pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
    all: pcw_close.
  Qed.

  (* The delivery behind [copy_bytes_map (in_wmem i) buf cap] (Drivers/Char/Random.v:40). *)
  Lemma pcw_n_getrandom : forall i buf cap flags eff m m' evs,
    check_getrandom i buf cap flags eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i buf cap flags [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_getrandom check_getrandom_zero] in H.
    pcw_unfold H. pcw_walk H.
    all: pcw_nleaf H.
    all: pcw_close.
  Qed.

  (* mremap (Mm/Mremap.v:36-96): no write; the grow's and the move's zero-fills and the
     move's copy off the window. *)
  Lemma pcw_m_mremap : forall i old old_size new_size flags eff m m' evs, mm_vinv vlo vhi m ->
    check_mremap old old_size new_size flags eff m = CheckOk m' evs -> pc_mm vlo vhi i m eff m'.
  Proof.
    intros i old old_size new_size flags [ret ws zs us cs ci] m m' evs VI H.
    pose proof (pcw_prup_nonneg (bv_unsigned old_size)
                  (proj1 (word_unsigned_range old_size))) as Hon.
    cbv beta iota zeta delta [check_mremap] in H. pcw_unfold H. pcw_walk H.
    all: pcw_mrleaf H VI.
  Qed.

  (** * Clean outcomes, with the ledger frame of each checker *)

  Lemma pcw_o_getcwd : forall i size eff m m' evs,
    check_getcwd size eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i size eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_getcwd; exact H | eapply VmMapsDisjoint.check_getcwd_frame; exact H ].
  Qed.

  Lemma pcw_o_epoll_pwait : forall i epfd events maxevents32 sigmask sigsetsize eff m m' evs,
    check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m = CheckOk m' evs ->
    pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i epfd events maxevents32 sigmask sigsetsize eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_epoll_pwait; exact H
      | eapply VmMapsDisjoint.check_epoll_pwait_frame; exact H ].
  Qed.

  Lemma pcw_o_pipe2 : forall i fildes flags eff m m' evs,
    check_pipe2 i fildes flags eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i fildes flags eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_pipe2; exact H | eapply VmMapsDisjoint.check_pipe2_frame; exact H ].
  Qed.

  Lemma pcw_o_getdents64 : forall i fd count eff m m' evs,
    check_getdents64 fd count eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i fd count eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_getdents64; exact H | eapply VmMapsDisjoint.check_getdents64_frame; exact H ].
  Qed.

  Lemma pcw_o_readv : forall i fd iov iovcnt eff m m' evs,
    check_readv i fd iov iovcnt eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i fd iov iovcnt eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_readv; exact H | eapply VmMapsDisjoint.check_readv_frame; exact H ].
  Qed.

  Lemma pcw_o_pread64 : forall i fd buf count pos eff m m' evs,
    check_pread64 i fd buf count pos eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i fd buf count pos eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_pread64; exact H | eapply VmMapsDisjoint.check_pread64_frame; exact H ].
  Qed.

  Lemma pcw_o_pselect6 : forall i n32 inp outp exp tsp sig eff m m' evs,
    check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs ->
    pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i n32 inp outp exp tsp sig eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_pselect6; exact H | eapply VmMapsDisjoint.check_pselect6_frame; exact H ].
  Qed.

  Lemma pcw_o_ppoll : forall i ufds nfds tsp sig sigsetsize eff m m' evs,
    check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs ->
    pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i ufds nfds tsp sig sigsetsize eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_ppoll; exact H | eapply VmMapsDisjoint.check_ppoll_frame; exact H ].
  Qed.

  Lemma pcw_o_readlinkat : forall i dirfd eff m m' evs,
    check_readlinkat dirfd eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i dirfd eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_readlinkat; exact H | eapply VmMapsDisjoint.check_readlinkat_frame; exact H ].
  Qed.

  Lemma pcw_o_newfstatat : forall i dirfd pathp flag eff m m' evs,
    check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i dirfd pathp flag eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_newfstatat; exact H | eapply VmMapsDisjoint.check_newfstatat_frame; exact H ].
  Qed.

  Lemma pcw_o_fstat : forall i fd statbuf eff m m' evs,
    check_fstat i fd statbuf eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i fd statbuf eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_fstat; exact H | eapply VmMapsDisjoint.check_fstat_frame; exact H ].
  Qed.

  Lemma pcw_o_nanosleep : forall i rqtp rmtp eff m m' evs,
    check_nanosleep i rqtp rmtp eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i rqtp rmtp eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_nanosleep; exact H | eapply VmMapsDisjoint.check_nanosleep_frame; exact H ].
  Qed.

  Lemma pcw_o_sched_getaffinity : forall i len eff m m' evs,
    check_sched_getaffinity len eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i len eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_sched_getaffinity; exact H
      | eapply VmMapsDisjoint.check_sched_getaffinity_frame; exact H ].
  Qed.

  Lemma pcw_o_sigaltstack : forall i uss uoss eff m m' evs,
    check_sigaltstack i uss uoss eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i uss uoss eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_sigaltstack; exact H | eapply VmMapsDisjoint.check_sigaltstack_frame; exact H ].
  Qed.

  Lemma pcw_o_rt_sigaction : forall i sig act oact ss eff m m' evs,
    check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i sig act oact ss eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_rt_sigaction; exact H
      | eapply VmMapsDisjoint.check_rt_sigaction_frame; exact H ].
  Qed.

  Lemma pcw_o_rt_sigprocmask : forall i how nset oset ss eff m m' evs,
    check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i how nset oset ss eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_rt_sigprocmask; exact H | eapply check_rt_sigprocmask_frame; exact H ].
  Qed.

  Lemma pcw_o_getgroups : forall i gidsetsize eff m m' evs,
    check_getgroups gidsetsize eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i gidsetsize eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_getgroups; exact H | eapply VmMapsDisjoint.check_getgroups_frame; exact H ].
  Qed.

  Lemma pcw_o_uname : forall i name eff m m' evs, PinsOk.pins_ok m ->
    check_uname i name eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i name eff m m' evs Hp H. apply pc_out_of_nm;
      [ eapply pcw_n_uname; [exact Hp | exact H]
      | eapply VmMapsDisjoint.check_uname_frame; exact H ].
  Qed.

  Lemma pcw_o_socketpair : forall i family type protocol sv eff m m' evs,
    check_socketpair i family type protocol sv eff m = CheckOk m' evs ->
    pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i family type protocol sv eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_socketpair; exact H | eapply VmMapsDisjoint.check_socketpair_frame; exact H ].
  Qed.

  Lemma pcw_o_accept4 : forall i fd addrp addrlenp flags eff m m' evs,
    check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i fd addrp addrlenp flags eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_accept4; exact H | eapply VmMapsDisjoint.check_accept4_frame; exact H ].
  Qed.

  Lemma pcw_o_getsockname : forall i fd eff m m' evs,
    check_getsockname i fd eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i fd eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_getsockname; exact H
      | eapply VmMapsDisjoint.check_getsockname_frame; exact H ].
  Qed.

  Lemma pcw_o_getpeername : forall i fd eff m m' evs,
    check_getpeername i fd eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i fd eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_getpeername; exact H
      | eapply VmMapsDisjoint.check_getpeername_frame; exact H ].
  Qed.

  Lemma pcw_o_recvfrom : forall i fd buf size eff m m' evs,
    check_recvfrom i fd buf size eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i fd buf size eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_recvfrom; exact H | eapply VmMapsDisjoint.check_recvfrom_frame; exact H ].
  Qed.

  Lemma pcw_o_getsockopt : forall i fd level optlenp eff m m' evs,
    check_getsockopt i fd level optlenp eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i fd level optlenp eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_getsockopt; exact H | eapply VmMapsDisjoint.check_getsockopt_frame; exact H ].
  Qed.

  Lemma pcw_o_recvmsg : forall i fd flags eff m m' evs,
    check_recvmsg fd flags eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i fd flags eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_recvmsg; exact H | eapply VmMapsDisjoint.check_recvmsg_frame; exact H ].
  Qed.

  Lemma pcw_o_wait4 : forall i upid stat_addr options rusage eff m m' evs,
    check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs ->
    pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i upid stat_addr options rusage eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_wait4; exact H | eapply VmMapsDisjoint.check_wait4_frame; exact H ].
  Qed.

  Lemma pcw_o_prlimit64 : forall i pid resource new_rlim old_rlim eff m m' evs,
    PinsOk.pins_ok m ->
    check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs ->
    pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i pid resource new_rlim old_rlim eff m m' evs Hp H. apply pc_out_of_nm;
      [ eapply pcw_n_prlimit64; [exact Hp | exact H]
      | eapply VmMapsDisjoint.check_prlimit64_frame; exact H ].
  Qed.

  Lemma pcw_o_getrandom : forall i buf cap flags eff m m' evs,
    check_getrandom i buf cap flags eff m = CheckOk m' evs -> pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i buf cap flags eff m m' evs H. apply pc_out_of_nm;
      [ eapply pcw_n_getrandom; exact H | eapply VmMapsDisjoint.check_getrandom_frame; exact H ].
  Qed.

  Lemma pcw_o_mremap : forall i old old_size new_size flags eff m m' evs, mm_vinv vlo vhi m ->
    check_mremap old old_size new_size flags eff m = CheckOk m' evs ->
    pc_out_ok vlo vhi i m eff m'.
  Proof.
    intros i old old_size new_size flags eff m m' evs VI H. apply pc_out_of_mm;
      [ eapply pcw_m_mremap; [exact VI | exact H]
      | eapply MmapTopFrame.check_mremap_top_frame; exact H ].
  Qed.

  (** * The premise, number by number *)

  (* [Checks/Sys/DispatchCompute.v] has no lemma for these nine; [PairClean.pc_cs_114]'s proof
     shape, with the checker the table names (Checks/Sys/Dispatch.v:92-95, :148-151, :280-283,
     :346-349, :607-610, :816-819, :871-874, :882-885, :926-929). *)
  Lemma pcw_cs_17 : forall i eff m, bv_unsigned (in_sysno i) = 17 ->
    check_syscall i eff m = check_getcwd (in_arg i 1) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcw_cs_22 : forall i eff m, bv_unsigned (in_sysno i) = 22 ->
    check_syscall i eff m
    = check_epoll_pwait i (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4)
        (in_arg i 5) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcw_cs_61 : forall i eff m, bv_unsigned (in_sysno i) = 61 ->
    check_syscall i eff m = check_getdents64 (fd32 (in_arg i 0)) (in_arg i 2) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcw_cs_67 : forall i eff m, bv_unsigned (in_sysno i) = 67 ->
    check_syscall i eff m
    = check_pread64 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcw_cs_132 : forall i eff m, bv_unsigned (in_sysno i) = 132 ->
    check_syscall i eff m = check_sigaltstack i (in_arg i 0) (in_arg i 1) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcw_cs_199 : forall i eff m, bv_unsigned (in_sysno i) = 199 ->
    check_syscall i eff m
    = check_socketpair i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcw_cs_204 : forall i eff m, bv_unsigned (in_sysno i) = 204 ->
    check_syscall i eff m = check_getsockname i (fd32 (in_arg i 0)) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcw_cs_205 : forall i eff m, bv_unsigned (in_sysno i) = 205 ->
    check_syscall i eff m = check_getpeername i (fd32 (in_arg i 0)) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pcw_cs_209 : forall i eff m, bv_unsigned (in_sysno i) = 209 ->
    check_syscall i eff m
    = check_getsockopt i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pc_spec_ok_17 : forall i mo, bv_unsigned (in_sysno i) = 17 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcw_cs_17 i eff mo Hn) in H. eapply pcw_o_getcwd; exact H.
  Qed.

  Lemma pc_spec_ok_22 : forall i mo, bv_unsigned (in_sysno i) = 22 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcw_cs_22 i eff mo Hn) in H. eapply pcw_o_epoll_pwait; exact H.
  Qed.

  Lemma pc_spec_ok_59 : forall i mo, bv_unsigned (in_sysno i) = 59 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_pipe2 i eff mo Hn) in H. eapply pcw_o_pipe2; exact H.
  Qed.

  Lemma pc_spec_ok_61 : forall i mo, bv_unsigned (in_sysno i) = 61 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcw_cs_61 i eff mo Hn) in H. eapply pcw_o_getdents64; exact H.
  Qed.

  Lemma pc_spec_ok_65 : forall i mo, bv_unsigned (in_sysno i) = 65 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_readv i eff mo Hn) in H. eapply pcw_o_readv; exact H.
  Qed.

  Lemma pc_spec_ok_67 : forall i mo, bv_unsigned (in_sysno i) = 67 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcw_cs_67 i eff mo Hn) in H. eapply pcw_o_pread64; exact H.
  Qed.

  Lemma pc_spec_ok_72 : forall i mo, bv_unsigned (in_sysno i) = 72 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_pselect6 i eff mo Hn) in H. eapply pcw_o_pselect6; exact H.
  Qed.

  Lemma pc_spec_ok_73 : forall i mo, bv_unsigned (in_sysno i) = 73 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_ppoll i eff mo Hn) in H. eapply pcw_o_ppoll; exact H.
  Qed.

  Lemma pc_spec_ok_78 : forall i mo, bv_unsigned (in_sysno i) = 78 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_readlinkat i eff mo Hn) in H. eapply pcw_o_readlinkat; exact H.
  Qed.

  Lemma pc_spec_ok_79 : forall i mo, bv_unsigned (in_sysno i) = 79 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_newfstatat i eff mo Hn) in H. eapply pcw_o_newfstatat; exact H.
  Qed.

  Lemma pc_spec_ok_80 : forall i mo, bv_unsigned (in_sysno i) = 80 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_fstat i eff mo Hn) in H. eapply pcw_o_fstat; exact H.
  Qed.

  Lemma pc_spec_ok_101 : forall i mo, bv_unsigned (in_sysno i) = 101 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_nanosleep i eff mo Hn) in H. eapply pcw_o_nanosleep; exact H.
  Qed.

  Lemma pc_spec_ok_123 : forall i mo, bv_unsigned (in_sysno i) = 123 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_sched_getaffinity i eff mo Hn) in H.
    eapply pcw_o_sched_getaffinity; exact H.
  Qed.

  Lemma pc_spec_ok_132 : forall i mo, bv_unsigned (in_sysno i) = 132 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcw_cs_132 i eff mo Hn) in H. eapply pcw_o_sigaltstack; exact H.
  Qed.

  Lemma pc_spec_ok_134 : forall i mo, bv_unsigned (in_sysno i) = 134 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_rt_sigaction i eff mo Hn) in H. eapply pcw_o_rt_sigaction; exact H.
  Qed.

  Lemma pc_spec_ok_135 : forall i mo, bv_unsigned (in_sysno i) = 135 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_rt_sigprocmask i eff mo Hn) in H.
    eapply pcw_o_rt_sigprocmask; exact H.
  Qed.

  Lemma pc_spec_ok_158 : forall i mo, bv_unsigned (in_sysno i) = 158 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_getgroups i eff mo Hn) in H. eapply pcw_o_getgroups; exact H.
  Qed.

  (** uname writes a pinned name back as it is (Sys/Kernel/Sys.v:1020-1022): the pin's
      length is what [PinsOk.pins_ok] bounds. *)
  Lemma pc_spec_ok_160 : forall i mo, bv_unsigned (in_sysno i) = 160 -> PinsOk.pins_ok mo ->
    pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn Hp. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_uname i eff mo Hn) in H. eapply pcw_o_uname; [exact Hp | exact H].
  Qed.

  Lemma pc_spec_ok_199 : forall i mo, bv_unsigned (in_sysno i) = 199 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcw_cs_199 i eff mo Hn) in H. eapply pcw_o_socketpair; exact H.
  Qed.

  Lemma pc_spec_ok_202 : forall i mo, bv_unsigned (in_sysno i) = 202 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_accept i eff mo Hn) in H. eapply pcw_o_accept4; exact H.
  Qed.

  Lemma pc_spec_ok_204 : forall i mo, bv_unsigned (in_sysno i) = 204 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcw_cs_204 i eff mo Hn) in H. eapply pcw_o_getsockname; exact H.
  Qed.

  Lemma pc_spec_ok_205 : forall i mo, bv_unsigned (in_sysno i) = 205 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcw_cs_205 i eff mo Hn) in H. eapply pcw_o_getpeername; exact H.
  Qed.

  Lemma pc_spec_ok_207 : forall i mo, bv_unsigned (in_sysno i) = 207 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_recvfrom i eff mo Hn) in H. eapply pcw_o_recvfrom; exact H.
  Qed.

  Lemma pc_spec_ok_209 : forall i mo, bv_unsigned (in_sysno i) = 209 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pcw_cs_209 i eff mo Hn) in H. eapply pcw_o_getsockopt; exact H.
  Qed.

  Lemma pc_spec_ok_212 : forall i mo, bv_unsigned (in_sysno i) = 212 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_recvmsg i eff mo Hn) in H. eapply pcw_o_recvmsg; exact H.
  Qed.

  Lemma pc_spec_ok_216 : forall i mo, bv_unsigned (in_sysno i) = 216 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs VI H.
    rewrite (check_syscall_mremap i eff mo Hn) in H. eapply pcw_o_mremap; [exact VI | exact H].
  Qed.

  Lemma pc_spec_ok_242 : forall i mo, bv_unsigned (in_sysno i) = 242 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_accept4 i eff mo Hn) in H. eapply pcw_o_accept4; exact H.
  Qed.

  Lemma pc_spec_ok_260 : forall i mo, bv_unsigned (in_sysno i) = 260 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_wait4 i eff mo Hn) in H. eapply pcw_o_wait4; exact H.
  Qed.

  (** prlimit64 writes a pinned [struct rlimit64] back as it is
      (Checks/Sys/Kernel/Sys.v:78): the pin's length is what [PinsOk.pins_ok] bounds. *)
  Lemma pc_spec_ok_261 : forall i mo, bv_unsigned (in_sysno i) = 261 -> PinsOk.pins_ok mo ->
    pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn Hp. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_prlimit64 i eff mo Hn) in H.
    eapply pcw_o_prlimit64; [exact Hp | exact H].
  Qed.

  Lemma pc_spec_ok_278 : forall i mo, bv_unsigned (in_sysno i) = 278 -> pc_spec_ok vlo vhi i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_getrandom i eff mo Hn) in H. eapply pcw_o_getrandom; exact H.
  Qed.
End PairCleanW.
