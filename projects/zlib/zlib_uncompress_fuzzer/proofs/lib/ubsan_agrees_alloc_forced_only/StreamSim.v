(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/zlib/checksum_fuzzer/proofs/lib/Reusable/YK1d.v at , lines 6-9, 12-46, 54-496, 498-870, 877-878, 882-897, 904-910, 924-926, 941-942, ported to the model. *)
(** * Common.StreamSim — reusable star-semantics infrastructure for binaries
      that loop { n = read(0, buf, cnt); if n <= 0 exit(0); write(1, buf, n) }
      with a single cnt-byte buffer (streamcat).

    TRUST BOUNDARY: image-INDEPENDENT proof library, written against the
    star-based [LinuxProcessSem.Run] trace semantics.

    Channel ids, counts and exit codes are [word = bv 64]; blocks are
    [list byte] with [byte = bv 8].  Following the ExitSim/CatSim
    conventions:

    - the read-syscall number test is Z-characterized: the pending number
      [x8] satisfies [bv_unsigned x8 = 63%Z] (mirroring CatSim's
      [tw_write]; avoids pinning a particular [bv] literal spelling), and
      [ReadPend]/[WrPend] carry that [x8] existentially;
    - fd/channel 0 and 1 are spelled [Z_to_bv 64 0] / [Z_to_bv 64 1]
      (the [init_model] spelling);
    - the chunk size is [cnt : word] with the hypothesis
      [(0 < bv_unsigned cnt)%Z]; block-length bounds are [Z] comparisons
      over [Z.of_nat (length bs)] and [bv_unsigned cnt];
    - block clauses are typed away by [byte = bv 8] ([block_ok] is
      2 conjuncts).

    Under the current model a channel read on fd 0 (count cnt > 0, channel
    not yet at EOF, destination buffer writable-mapped) has EXACTLY these
    admissible outcomes:

    - EOF-now: ret 0, no writes, no events; EOF becomes STICKY in the model,
      so the program's n<=0 exit path is LIVE and ends the trace with
      [ExitEv 0 fs0];
    - any 1..cnt bytes [bs] of the environment's choosing, written into the
      buffer and recorded one byte-carrying [ReadEv 0 b] per byte.  Short
      reads are real.

    A single channel write to fd 1 delivers a nonempty prefix of the
    environment's choosing — one [WriteEv 1 b] per delivered byte — and
    leaves the model untouched.  The binaries therefore echo each block
    through a put-style RETRY loop (WallSim's [to_wall] node): however
    the deliveries chunk, they concatenate to exactly the block, so each
    iteration contributes the [ReadEv]s of its block followed by ALL of
    its [WriteEv]s.  Hence the observable trace set of a streamcat-shaped
    binary is exactly [stream_traces cnt fs0]: the prefixes of

        flat_map iter_ev blocks ++ [ExitEv 0 fs0]

    over all lists of admissible blocks (a prefix of the never-EOF
    infinite run lies within finitely many blocks, so this form also
    covers non-terminating resolutions).

    The per-binary proof supplies a loop-head predicate [LH] and a proof
    that every [LH] state runs (deterministically) to a read-pending ecall
    state ([to_rd]) whose EOF continuation reaches an exit(0) ecall and
    whose every-bytes continuation reaches the echo write-pending state
    with a write-all derivation ([WallSim.to_wall]) of the whole block
    down to an [LH] state.  This file turns that single per-iteration
    fact into the full trace characterization ([stream_obs_iff]), the
    no-error fact, and the pair equivalence ([stream_strong_equiv]). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import SimInv ExitSim CatSim WallSim.

Import ListNotations.
Open Scope bv_scope.

(* ========================================================================= *)
(* Syscall-input decoding facts (in addition to ExitSim/CatSim's).            *)
(* ========================================================================= *)

Lemma in_arg1_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.

(** Which arm answers this number, on the SPEC side.  [syscall_spec] is
    [dispatch spec_table], so fixing the number settles the table lookup by
    conversion -- the same one-line argument [Checks.Sys.DispatchCompute]
    makes for [check_syscall], made here so that this file needs only the
    read checker rather than the module re-exporting every arm's. *)
Lemma syscall_spec_read : forall segs ms x8 model o,
  bv_unsigned x8 = 63%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> read_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
         (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  change (in_sysno (sys_input segs ms x8)) with x8.
  rewrite Hno. reflexivity.
Qed.

Lemma in_arg2_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.

Lemma in_wmem_sys_input : forall segs ms x8,
  in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(* Small word facts.  ([w_is0_pos] lives in [LinuxProcessSem.Specs], which    *)
(* this file imports, so the write-count gate has a single derivation.)       *)
(* ========================================================================= *)

(** The masked exit code of exit(0). *)
Lemma band0_255 : bv_and (Z_to_bv 64 0) (Z_to_bv 64 255) = Z_to_bv 64 0.
Proof.
  apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity.
Qed.

(* ========================================================================= *)
(* Model helpers.                                                             *)
(* ========================================================================= *)

Lemma m_fs_with_stdin : forall s m, m_fs (with_stdin s m) = m_fs m.
Proof. reflexivity. Qed.

Lemma m_halted_with_stdin : forall s m, m_halted (with_stdin s m) = m_halted m.
Proof. reflexivity. Qed.

Lemma m_fds_with_stdin : forall s m, m_fds (with_stdin s m) = m_fds m.
Proof. reflexivity. Qed.

Lemma m_vm_lazy_with_stdin : forall s m,
  m_vm_lazy (with_stdin s m) = m_vm_lazy m.
Proof. reflexivity. Qed.

(** The model invariant maintained across loop iterations: fd 0 is the
    stdin channel, fd 1 the stdout channel WITH A READER ([fd1chan]),
    and the model is not halted.  The reader is there because a write
    to a stdout whose reader has gone KILLS the process (SIGPIPE at the
    default disposition), which the loop's write nodes do not describe
    -- not because the model assumes one.  Nothing is said about WHAT is
    left in [m_stdin]: it shrinks as the loop runs, and each lemma below
    relates it to the blocks delivered so far.  (End of input is the
    stream's own [IEof], so the invariant need not say that stdin has
    not yet delivered EOF.  Nor is there a byte-range condition: the
    stream's elements are [byte].) *)
Definition M_loop (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
  fd1chan model /\
  m_halted model = None /\
  m_vm_lazy model = [].

Lemma init_M_loop : forall reserved brk0 mb sp lim inp,
  in_channel_reader inp = true ->
  M_loop (init_model reserved brk0 mb sp lim inp).
Proof.
  intros reserved brk0 mb sp lim inp Hr.
  split; [reflexivity | split; [apply init_model_fd1chan; exact Hr | split; reflexivity]].
Qed.

(** Consuming a read block preserves the invariant. *)
Lemma M_loop_take : forall k model,
  M_loop model ->
  M_loop (with_stdin (snd (stream_take (m_stdin model) k)) model).
Proof.
  intros k model (H0 & H1 & Hh & Hlazy).
  split; [exact H0 | split; [exact H1 | split; assumption]].
Qed.

Lemma M_loop_fd1chan : forall model, M_loop model -> fd1chan model.
Proof. intros model (H0 & H1 & Hh & Hlazy). exact H1. Qed.

(* ========================================================================= *)
(* The writable-view range check, reduced to a vm_compute-able boolean over   *)
(* the static segment image.  [ms_writable_byte] consults the writable        *)
(* overlay FIRST and falls back to the segment bytes; an overlay entry can     *)
(* only override a defined segment byte with another defined byte, so if the  *)
(* segment view alone is defined on the whole range the writable view is too, *)
(* for EVERY machine state.  Addresses are [word]s; the segment lookup is the *)
(* interpreter's Z-comparison [find_segment] (segments are N-based snapshot   *)
(* data).                                                                     *)
(* ========================================================================= *)

Fixpoint wseg_ok (segs : list Segment) (a : word) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match find_segment segs (bv_unsigned a) 1 with
      | Some seg =>
          (seg_writable seg
           && match segment_byte_at (seg_bytes seg)
                      (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) with
              | Some _ => true
              | None => false
              end
           && wseg_ok segs (a + 1) n')%bool
      | None => false
      end
  end.

Lemma wseg_ok_read_aux : forall segs n a ms,
  wseg_ok segs a n = true ->
  exists w, read_bytes_aux (ms_writable_byte segs ms) a n = Some w.
Proof.
  intros segs n; induction n as [|n IH]; intros a ms H.
  - exists []. reflexivity.
  - cbn [wseg_ok] in H.
    destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
    apply andb_true_iff in H as [H Hrec].
    apply andb_true_iff in H as [Hwr Hbyte].
    destruct (segment_byte_at (seg_bytes seg)
                (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
      [|discriminate].
    destruct (IH (a + 1) ms Hrec) as [w Hw].
    cbn [read_bytes_aux].
    assert (Hdef : exists b0, ms_writable_byte segs ms a = Some b0).
    { unfold ms_writable_byte, wview. destruct (ms_mem ms a) as [b'|].
      - eexists; reflexivity.
      - rewrite Hseg, Hwr, Hb. eexists; reflexivity. }
    destruct Hdef as [b0 Hb0]. rewrite Hb0, Hw. eexists; reflexivity.
Qed.

Lemma wseg_ok_wdef : forall segs (a len : word) ms,
  wseg_ok segs a (word_to_nat len) = true ->
  exists w, read_bytes_map (ms_writable_byte segs ms) a len = Some w.
Proof.
  intros segs a len ms H. rewrite read_bytes_map_eq.
  apply wseg_ok_read_aux. exact H.
Qed.

(* ========================================================================= *)
(* Channel-read spec facts (fd 0, count [cnt]), through the verified checker. *)
(* Parameterized over the chunk count [cnt] (audit 1.1/3.1): every consumer  *)
(* (StreamSim's own loop shape below, DrainSim's 1024-byte shape, ...)       *)
(* instantiates [cnt] directly instead of re-proving this family.            *)
(* [Hcnt : (0 < bv_unsigned cnt)%Z] is needed only to discharge              *)
(* [w_is0 cnt = false] (a literal fact when [cnt] is a numeral, but not      *)
(* definitionally so for an abstract [cnt]).  The pending syscall number is  *)
(* Z-characterized ([bv_unsigned x8 = 63%Z], the dispatcher's test).         *)
(*                                                                          *)
(* Which bytes a read delivers is fixed by the model's remaining input      *)
(* stream [m_stdin]: the two shapes below are end-of-input                  *)
(* ([m_stdin = IEof], return 0) and deliver-the-[length bs]-byte-prefix of  *)
(* the remaining input (which then advances past it).                       *)
(* ========================================================================= *)

(** At least one byte of the destination is writable — the checker's
    fail-closed guard — whenever the whole [cnt]-byte buffer is. *)
Lemma read0_wmem1 : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 w,
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  exists w1, read_bytes_map (in_wmem (sys_input segs ms x8)) (ms_gpr ms 1)
               (Z_to_bv 64 1) = Some w1.
Proof.
  intros cnt Hcnt segs ms x8 w Hw. rewrite in_wmem_sys_input.
  eexists. apply (read_bytes_map_prefix _ _ cnt (Z_to_bv 64 1) w);
    [rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; lia | exact Hw].
Qed.

(** The destination holds everything the stream could supply to this
    count: [read_spec]'s partial-destination decline does not fire when
    the whole [cnt] range is writable, since the bytes the source can
    supply are at most the clamped count. *)
Lemma read0_wmem_need : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 w s,
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  exists wn, read_bytes_map (in_wmem (sys_input segs ms x8)) (ms_gpr ms 1)
               (len_word (fst (stream_take_z s (rw_count_clamp cnt)))) = Some wn.
Proof.
  intros cnt Hcnt segs ms x8 w s Hw. rewrite in_wmem_sys_input.
  eexists. apply (read_bytes_map_prefix _ _ cnt _ w); [|exact Hw].
  rewrite stream_take_z_eq.
  pose proof (stream_take_length (Z.to_nat (rw_count_clamp cnt)) s) as Hlen.
  pose proof (rw_count_clamp_range cnt) as Hcl.
  unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap_small;
    unfold bv_modulus, MAX_RW_COUNT in *; cbn [Z.of_N] in *;
    [ | pose proof (bv_unsigned_in_range 64 cnt) ]; unfold rw_count_clamp in *; lia.
Qed.

Lemma read0_check_eof : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  m_stdin model = IEof ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* the range passes [access_ok]: [vfs_read] tests it before the fd's
     content is consulted, so it is a premise of every read answer *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  check_read (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (mkEffect (Z_to_bv 64 0) [] []) model
    = CheckOk model [].
Proof.
  intros cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok.
  pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
  unfold check_read.
  rewrite Hg0; norm_fd32; rewrite Hfd.
  cbv beta iota.
  change (negb (w_is0 (Z_to_bv 64 0))) with false. cbv beta iota.
  rewrite Hg2, Haok.
  cbn [negb]. cbv beta iota. rewrite Hcnt0. cbv beta iota.
  rewrite Heof. cbv beta iota.
  unfold check_ret_only. rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma read0_check_bytes : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model w bs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* the range passes [access_ok], which [vfs_read] tests before the
     input is consulted *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take (m_stdin model) (length bs)) = bs ->
  check_read (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] []) model
    = CheckOk (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
              (map (ReadEv (Z_to_bv 64 0)) bs).
Proof.
  intros cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok Hlo Hhi Hpre.
  destruct (read0_wmem1 cnt Hcnt segs ms x8 w Hw) as [w1 Hw1].
  destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model) Hw) as [wn Hwn].
  pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
  unfold check_read.
  rewrite Hg0; norm_fd32; rewrite Hfd.
  cbv beta iota.
  change (negb (w_is0 (Z_to_bv 64 0))) with false. cbv beta iota.
  rewrite Hg2, Haok.
  cbn [negb]. cbv beta iota. rewrite Hcnt0. cbv beta iota.
  (* the input cannot have run out: a nonempty prefix was delivered *)
  destruct (m_stdin model) as [|b0 s0] eqn:Hs.
  { exfalso. rewrite stream_take_nil_of_eof in Hpre. subst bs. cbn in Hlo. lia. }
  cbv beta iota.
  rewrite Hw1. cbv beta iota.
  rewrite Hwn. cbv beta iota.
  rewrite !bv_eqb_refl.
  rewrite (proj2 (Z.leb_le 1 (Z.of_nat (length bs))) Hlo).
  rewrite (rw_count_clamp_of_rw _ (proj2 Hcnt)).
  rewrite (proj2 (Z.leb_le (Z.of_nat (length bs)) (bv_unsigned cnt)) Hhi).
  rewrite (proj2 (listN_eqb_eq _ _) Hpre).
  rewrite <- (in_wmem_sys_input segs ms x8) in Hw.
  assert (Hlek : (bv_unsigned (len_word bs) <= bv_unsigned cnt)%Z).
  { unfold len_word. pose proof (bv_unsigned_in_range 64 cnt) as Hr.
    rewrite Z_to_bv_unsigned, bv_wrap_small; [exact Hhi | lia]. }
  rewrite (wmem_ok_of_full _ _ _ _ _ Hw Hlek).
  reflexivity.
Qed.

Lemma read0_ok_eof : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  m_stdin model = IEof ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* the range passes [access_ok]: [vfs_read] tests it before the fd's
     content is consulted, so it is a premise of every read answer *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (Z_to_bv 64 0) [] []) model []).
Proof.
  intros cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok.
  apply (proj2 (syscall_spec_read _ _ _ _ _ Hno)).
  apply check_read_sound_ok. eapply read0_check_eof; eassumption.
Qed.

Lemma read0_ok_bytes : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model w bs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take (m_stdin model) (length bs)) = bs ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] [])
        (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
        (map (ReadEv (Z_to_bv 64 0)) bs)).
Proof.
  intros cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok Hlo Hhi Hpre.
  apply (proj2 (syscall_spec_read _ _ _ _ _ Hno)).
  apply check_read_sound_ok. eapply read0_check_bytes; eassumption.
Qed.

(** Every admissible outcome of the read IS one of the two shapes, and
    WHICH one is decided by the remaining input, not by the environment. *)
Lemma read0_ok_inv : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model buf w eff model' evs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  (* the range passes [access_ok]: [vfs_read] tests it before the fd's
     content is consulted, so it is a premise of every read answer *)
  access_okb buf (bv_unsigned cnt) = true ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  (m_stdin model = IEof /\ eff = mkEffect (Z_to_bv 64 0) [] [] /\
   model' = model /\ evs = [])
  \/ (exists bs,
        (1 <= Z.of_nat (length bs))%Z /\
        (Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
        fst (stream_take (m_stdin model) (length bs)) = bs /\
        eff = mkEffect (len_word bs) [(buf, bs)] [] /\
        model' = with_stdin (snd (stream_take (m_stdin model) (length bs))) model /\
        evs = map (ReadEv (Z_to_bv 64 0)) bs).
Proof.
  intros cnt Hcnt segs ms x8 model buf w eff model' evs
         Hno Hfd Hg0 Hg1 Hg2 Hw Haok Hspec.
  destruct (read0_wmem1 cnt Hcnt segs ms x8 w) as [w1 Hw1];
    [rewrite Hg1; exact Hw|].
  rewrite Hg1 in Hw1.
  destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model)) as [wn Hwn];
    [rewrite Hg1; exact Hw|].
  rewrite Hg1 in Hwn.
  pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
  apply (proj1 (syscall_spec_read _ _ _ _ _ Hno)) in Hspec.
  apply check_read_complete_ok in Hspec.
  unfold check_read in Hspec.
  rewrite Hg0 in Hspec; norm_fd32; rewrite Hfd in Hspec.
  cbv beta iota in Hspec.
  change (negb (w_is0 (Z_to_bv 64 0))) with false in Hspec.
  cbv beta iota in Hspec.
  rewrite Hg1, Hg2, Haok in Hspec.
  cbn [negb] in Hspec. cbv beta iota in Hspec. rewrite Hcnt0 in Hspec. cbv beta iota in Hspec.
  destruct (m_stdin model) as [|b0 s0] eqn:Hs; cbv beta iota in Hspec.
  - (* the input has run out *)
    apply check_ret_only_ok_iff in Hspec.
    destruct Hspec as (-> & -> & ->). left. auto.
  - (* bytes delivered from the head of the remaining input *)
    rewrite Hw1 in Hspec. cbv beta iota in Hspec.
    rewrite Hwn in Hspec. cbv beta iota in Hspec.
    destruct eff as [ret ws zs us cs copyins].
    destruct ws as [|[a bs] [|w2 ws]]; [discriminate| |discriminate].
    destruct zs as [|z zs]; [|discriminate].
    destruct us as [|u us]; [|discriminate].
    destruct cs as [|c cs]; [|discriminate].
    destruct copyins as [|copyin copyins]; [|discriminate].
    destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
              && (1 <=? Z.of_nat (length bs))%Z
              && (Z.of_nat (length bs) <=? rw_count_clamp cnt)%Z
              && listN_eqb (fst (stream_take (ICons b0 s0) (length bs))) bs
              && wmem_ok (sys_input segs ms x8) buf (len_word bs)) eqn:Hb;
      try rewrite Hb in Hspec; [|discriminate].
    inversion Hspec; subst.
    apply andb_true_iff in Hb as [Hb _].
    apply andb_true_iff in Hb as [Hb HE].
    apply andb_true_iff in Hb as [Hb HD].
    apply andb_true_iff in Hb as [Hb HC].
    apply andb_true_iff in Hb as [HA HB].
    apply bv_eqb_eq in HA; subst a.
    apply bv_eqb_eq in HB; subst ret.
    apply Z.leb_le in HC. apply Z.leb_le in HD.
    rewrite (rw_count_clamp_of_rw _ (proj2 Hcnt)) in HD.
    apply listN_eqb_eq in HE.
    right. exists bs. repeat split; try assumption; reflexivity.
Qed.

(** The read never takes the error transition (the destination is writable). *)
Lemma read0_no_unmodeled : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* the range passes [access_ok]: [vfs_read] tests it before the fd's
     content is consulted, so it is a premise of every read answer *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros cnt Hcnt segs ms x8 model w Hno Hfd Hg0 Hg2 Hw Haok Hspec.
  destruct (read0_wmem1 cnt Hcnt segs ms x8 w Hw) as [w1 Hw1].
  destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model) Hw) as [wn Hwn].
  pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
  apply (proj1 (syscall_spec_read _ _ _ _ _ Hno)) in Hspec.
  apply (check_read_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_read in Hspec.
  rewrite Hg0 in Hspec; norm_fd32; rewrite Hfd in Hspec.
  cbv beta iota in Hspec.
  change (negb (w_is0 (Z_to_bv 64 0))) with false in Hspec.
  cbv beta iota in Hspec.
  rewrite Hg2, Haok in Hspec.
  cbn [negb] in Hspec. cbv beta iota in Hspec. rewrite Hcnt0 in Hspec. cbv beta iota in Hspec.
  destruct (m_stdin model) as [|b0 s0] eqn:Hs; cbv beta iota in Hspec.
  { now apply check_ret_only_no_unmodeled in Hspec. }
  rewrite Hw1 in Hspec. cbv beta iota in Hspec.
  rewrite Hwn in Hspec. cbv beta iota in Hspec. discriminate.
Qed.

(* ========================================================================= *)
(* One-step inversion at a read-pending config.                               *)
(* ========================================================================= *)

Lemma sstep_read_inv : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms model buf x8 w evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 63%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  (* the range passes [access_ok]: [vfs_read] tests it before the fd's
     content is consulted, so it is a premise of every read answer *)
  access_okb buf (bv_unsigned cnt) = true ->
  sstep segs (mkCfg ms model) evs st ->
  (m_stdin model = IEof /\ evs = [] /\
   st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model))
  \/ (exists bs,
        (1 <= Z.of_nat (length bs))%Z /\
        (Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
        fst (stream_take (m_stdin model) (length bs)) = bs /\
        evs = map (ReadEv (Z_to_bv 64 0)) bs /\
        st = SNext (mkCfg
               (advance_past_svc (apply_effect ms
                  (mkEffect (len_word bs) [(buf, bs)] [])))
               (with_stdin (snd (stream_take (m_stdin model) (length bs)))
                           model))).
Proof.
  intros cnt Hcnt segs ms model buf x8 w evs st
         Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
                  Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
        as [(Hs & Heff & Hm & Hevs) | (bs & Hlo & Hhi & Hpre & Heff & Hm & Hevs)];
        subst eff model' evs0
    end.
    + match goal with
      | Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
          rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
          inversion Hmat; subst model''
      end.
      left. rewrite apply_effect_no_write.
      split; [exact Hs | split; reflexivity].
    + match goal with
      | Hmat : materialize_model_accesses
                   (with_stdin ?s model) _ = Some ?model'' |- _ =>
          rewrite (materialize_model_accesses_no_lazy (with_stdin s model) _)
            in Hmat by (rewrite m_vm_lazy_with_stdin; exact Hlazy);
          inversion Hmat; subst model''
      end.
      right. exists bs. repeat split; try assumption; reflexivity.
  - (* sstep_syscall_materialization_fault: this loop has no lazy maps *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
                  Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
        as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
      subst model';
      [ rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat
      | rewrite (materialize_model_accesses_no_lazy
                   (with_stdin (snd (stream_take (m_stdin model) (length bs))) model) _)
          in Hmat by (rewrite m_vm_lazy_with_stdin; exact Hlazy) ];
      discriminate
    end.
  - (* sstep_exit: the read leaves the model un-halted *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
                  Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
        as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
        subst model'; [|rewrite m_halted_with_stdin in H6]; congruence
    end.
  - (* sstep_killed: the read leaves the model unkilled, as it leaves it
       un-halted -- [State.m_killed_of_m_halted_none] on the pre-model *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
                  Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
        as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
        subst model';
        [ rewrite (m_killed_of_m_halted_none model Hh) in H6
        | rewrite (m_killed_of_m_halted_none _
                     (eq_trans (m_halted_with_stdin _ model) Hh)) in H6 ];
        discriminate
    end.
  - (* sstep_syscall_unmodeled *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (read0_no_unmodeled _ Hcnt segs ms x8 model w Hno Hfd Hg0 eq_refl Hw
               Haok H3)
    end.
Qed.

(* ========================================================================= *)
(* The trace-set characterization.                                            *)
(* ========================================================================= *)

(** How a run CHUNKS its input: [chunks cnt s blocks s'] says the loop can
    consume [s] as the successive read blocks [blocks], leaving [s']
    unread.  Each block is a nonempty prefix of at most [cnt] bytes of
    what remains — WHICH bytes is fixed by the input, only how many is
    the read's (short-read) nondeterminism. *)
Inductive chunks (cnt : word) : InputStream -> list (list byte) -> InputStream -> Prop :=
| chunks_nil : forall s, chunks cnt s [] s
| chunks_cons : forall s bs blocks s'',
    (1 <= Z.of_nat (length bs))%Z ->
    (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
    fst (stream_take s (length bs)) = bs ->
    chunks cnt (snd (stream_take s (length bs))) blocks s'' ->
    chunks cnt s (bs :: blocks) s''.

(** Chunkings compose and decompose along list concatenation — used by
    consumers (DrainSim) that need to talk about "the blocks before the
    last one". *)
Lemma chunks_app : forall cnt s l1 s1 l2 s2,
  chunks cnt s l1 s1 -> chunks cnt s1 l2 s2 -> chunks cnt s (l1 ++ l2) s2.
Proof.
  intros cnt s l1 s1 l2 s2 H1; revert l2 s2.
  induction H1 as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros l2 s2 H2; cbn [app]; [exact H2|].
  eapply chunks_cons; eauto.
Qed.

Lemma chunks_split : forall cnt l1 l2 s s2,
  chunks cnt s (l1 ++ l2) s2 ->
  exists s1, chunks cnt s l1 s1 /\ chunks cnt s1 l2 s2.
Proof.
  intros cnt l1; induction l1 as [|bs l1 IH]; intros l2 s s2 H; cbn [app] in H.
  - exists s. split; [constructor | exact H].
  - inversion H as [|s0 bs0 blocks0 s3 Hlo Hhi Hpre HC Heq1 Heq2]; subst.
    destruct (IH l2 _ _ HC) as (s1 & H1 & H2).
    exists s1. split; [eapply chunks_cons; eauto | exact H2].
Qed.

(** Inversion for a one-block chunking. *)
Lemma chunks_single_inv : forall cnt s bs s',
  chunks cnt s [bs] s' ->
  (1 <= Z.of_nat (length bs))%Z /\
  (Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
  fst (stream_take s (length bs)) = bs /\
  s' = snd (stream_take s (length bs)).
Proof.
  intros cnt s bs s' H.
  inversion H as [|s0 bs0 blocks0 s2 Hlo Hhi Hpre HC Heq1 Heq2]; subst.
  inversion HC; subst.
  repeat split; assumption || reflexivity.
Qed.

(** One loop iteration's events, reading on channel [rch]: the block is
    read byte-by-byte and echoed byte-by-byte to stdout.  The echo write
    may take several (possibly short) channel writes, but the put-style
    retry loop always delivers the WHOLE block, so — chunking-
    independently — an iteration's write contribution is all of [bs].

    Only the READ channel is a parameter here; the write channel has its
    own parametric family in [ShapeAlg.t_writes_ch]. *)
Definition iter_ev_ch (rch : word) (bs : list byte) : list event :=
  map (ReadEv rch) bs ++ map (WriteEv (Z_to_bv 64 1)) bs.

(** One loop iteration's events, reading on stdin — the only channel a
    read can name ([ReadWrite.read_spec] answers -EBADF on the rest). *)
Definition iter_ev (bs : list byte) : list event :=
  iter_ev_ch (Z_to_bv 64 0) bs.

(** What follows the last block: the loop exits 0 exactly when the input
    has run out.  While input remains, the run has not stopped — the
    trace so far is just a prefix. *)
Definition eof_tail (s : InputStream) (fs : Fs.Fs) : list event :=
  match s with
  | IEof => [ExitEv (Z_to_bv 64 0) fs]
  | ICons _ _ => []
  end.

(** The trace set of an echo loop with a [cnt]-byte buffer reading
    channel [rch] on input [s]: the prefixes of

        flat_map (iter_ev_ch rch) blocks ++ eof_tail s' fs

    over all chunkings of [s] into read blocks. *)
Definition stream_traces_ch (rch : word) (cnt : word) (fs : Fs.Fs)
    (s : InputStream) (tr : list event) : Prop :=
  exists blocks s',
    chunks cnt s blocks s' /\
    is_prefix tr (flat_map (iter_ev_ch rch) blocks ++ eof_tail s' fs).

(** The full observable trace set of a streamcat binary with a [cnt]-byte
    buffer on input [s].  Reads name channel 0 because [ReadWrite.read_spec]
    answers -EBADF on every other.  The exit event appears only in the
    chunkings that reached the end of the input; an INFINITE input
    contributes only the (unbounded, but each finite) block prefixes,
    which is exactly right — such a run never exits. *)
Definition stream_traces (cnt : word) (fs : Fs.Fs) (s : InputStream)
    (tr : list event) : Prop :=
  stream_traces_ch (Z_to_bv 64 0) cnt fs s tr.

Lemma stream_traces_ch_prefix_closed : forall rch cnt fs s tr tr',
  stream_traces_ch rch cnt fs s tr -> is_prefix tr' tr ->
  stream_traces_ch rch cnt fs s tr'.
Proof.
  intros rch cnt fs s tr tr' (blocks & s' & HC & Hp) Hp'.
  exists blocks, s'. split; [exact HC | eapply is_prefix_trans; eauto].
Qed.

Lemma stream_traces_prefix_closed : forall cnt fs s tr tr',
  stream_traces cnt fs s tr -> is_prefix tr' tr -> stream_traces cnt fs s tr'.
Proof. exact (stream_traces_ch_prefix_closed (Z_to_bv 64 0)). Qed.

(* ========================================================================= *)
(* The generic loop theory, parameterized over the [cnt]-byte buffer size.   *)
(* ========================================================================= *)

Section Loop.
Variable segs : list Segment.
Variable LH : machine_state -> Prop.
Variable cnt : word.
(** The chunk size is positive and inside the transfer size the
    model judges ([Uaccess.rw_bytes_max]); every buffer this loop writes is
    a chunk, so this is also what makes the write side modeled. *)
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.

(** The state runs (deterministically) to some loop-head state. *)
Definition lh_next (ms : machine_state) : Prop :=
  exists ms', msteps segs ms ms' /\ LH ms'.

(** A write-pending ecall state echoing block [bs]: the environment may
    deliver any nonempty prefix per syscall, so the binary's put-style
    retry loop must deliver ALL of [bs] — across one or more writes —
    and then run back to a loop head.  That is exactly WallSim's
    write-all node with the loop-head continuation. *)
Definition WrPend (bs : list byte) (ms : machine_state) : Prop :=
  (1 <= length bs)%nat /\
  to_wall segs (Z_to_bv 64 1) ms bs lh_next.

(** Straight line of instructions to a write-pending state for block [bs]. *)
Inductive to_wr (bs : list byte) : machine_state -> Prop :=
| twr_here : forall ms, WrPend bs ms -> to_wr bs ms
| twr_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wr bs ms' -> to_wr bs ms.

(** A read-pending ecall state (fd 0, count [cnt], buffer a1 writable),
    together with both continuations:
    - when the input has run out, the run reaches an exit(0) ecall;
    - on any admissible block, the run reaches the echo write and returns to
      a loop head. *)
Definition ReadPend (ms : machine_state) : Prop :=
  exists buf x8,
  ms_svc_pending ms = Some x8 /\
  bv_unsigned x8 = 63%Z /\
  ms_gpr ms 0 = Z_to_bv 64 0 /\
  ms_gpr ms 1 = buf /\
  ms_gpr ms 2 = cnt /\
  (exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w) /\
  (* the destination range passes [access_ok]: [vfs_read] tests
     [buf + cnt <= TASK_SIZE] before it looks at the input, and being
     mapped is not that — [read_bytes_map] walks the range in word
     arithmetic, which wraps at 2^64.  A binary's read buffer is a
     link-time or allocator address far under [State.TASK_SIZE], so this
     costs a caller one inequality ([Uaccess.access_okb_intro]). *)
  access_okb buf (bv_unsigned cnt) = true /\
  to_exit segs (Z_to_bv 64 0) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\
  (forall bs,
     (1 <= Z.of_nat (length bs))%Z ->
     (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
     to_wr bs (advance_past_svc (apply_effect ms
        (mkEffect (len_word bs) [(buf, bs)] [])))).

(** Straight line of instructions to a read-pending state. *)
(** The [to_wr] analogue of [msteps_to_rd] below: prepend a straight-line
    run to a write-pending derivation.  This is what lets a caller reach
    the echo write through a PROVED [msteps] — e.g. the one a
    [Common/Hoare.v] triple yields via [triple_msteps] — instead of
    stepping the instructions in the [to_wr] derivation itself. *)
Lemma msteps_to_wr : forall bs ms ms',
  msteps segs ms ms' -> to_wr bs ms' -> to_wr bs ms.
Proof.
  intros bs ms ms' H; induction H; [auto|].
  intro Hwr. eapply twr_step; eauto.
Qed.

(** A write phase IS a write-all tail derivation (the [to_wr] instruction
    prefix becomes [twt_step]s in front of the [to_wall] node). *)
Lemma to_wr_wall_tail : forall bs ms,
  to_wr bs ms -> to_wall_tail segs (Z_to_bv 64 1) ms bs lh_next.
Proof.
  intros bs ms H; induction H as [ms HWP | ms ms' Hsvc Hstep Hwr IH].
  - destruct HWP as [Hnb Hw]. apply twt_more; assumption.
  - eapply twt_step; eauto.
Qed.

Inductive to_rd : machine_state -> Prop :=
| trd_here : forall ms, ReadPend ms -> to_rd ms
| trd_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_rd ms' -> to_rd ms.

Lemma msteps_to_rd : forall ms ms',
  msteps segs ms ms' -> to_rd ms' -> to_rd ms.
Proof.
  intros ms ms' H; induction H; [auto|].
  intro Hrd. eapply trd_step; eauto.
Qed.

(** The single per-binary hypothesis: every loop head runs to a read. *)
Hypothesis H_LH : forall ms, LH ms -> to_rd ms.

Lemma lh_next_to_rd : forall ms, lh_next ms -> to_rd ms.
Proof.
  intros ms (ms' & Hm & HL). eapply msteps_to_rd; [exact Hm | apply H_LH, HL].
Qed.

(* ------------------------------------------------------------------------- *)
(* Straight lines are event-free star runs.                                   *)
(* ------------------------------------------------------------------------- *)

Lemma to_rd_star : forall ms model,
  m_halted model = None -> m_vm_lazy model = [] -> to_rd ms ->
  exists msR, ReadPend msR /\
    star segs (mkCfg ms model) [] (mkCfg msR model).
Proof.
  intros ms model Hh Hlazy Hrd.
  induction Hrd as [ms HRP | ms ms' Hsvc Hstep Hrd IH].
  - exists ms. split; [exact HRP | apply star_refl].
  - destruct IH as (msR & HRP & Hstar).
    exists msR. split; [exact HRP|].
    change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma to_wr_star : forall bs ms model,
  m_halted model = None -> m_vm_lazy model = [] -> to_wr bs ms ->
  exists msW, WrPend bs msW /\
    star segs (mkCfg ms model) [] (mkCfg msW model).
Proof.
  intros bs ms model Hh Hlazy Hwr.
  induction Hwr as [ms HWP | ms ms' Hsvc Hstep Hwr IH].
  - exists ms. split; [exact HWP | apply star_refl].
  - destruct IH as (msW & HWP & Hstar).
    exists msW. split; [exact HWP|].
    change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* Admissibility: every stream trace is realized.                             *)
(* ------------------------------------------------------------------------- *)

Lemma stream_star_admits : forall s blocks s',
  chunks cnt s blocks s' ->
  forall ms model,
  M_loop model -> m_stdin model = s -> to_rd ms ->
  exists c, star segs (mkCfg ms model)
              (flat_map iter_ev blocks ++ eof_tail s' (m_fs model)) c.
Proof.
  intros s blocks s' HC.
  induction HC as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros ms model HM Hst Hrd; pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
  - (* no more blocks *)
    cbn [flat_map app].
    destruct s as [|b0 s0] eqn:Hs.
    + (* the input has run out: resolve the read as EOF, then exit(0) *)
      destruct (to_rd_star ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
      destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & _).
      destruct (to_exit_star_admits segs (Z_to_bv 64 0)
                  (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0))) model Hh Hlazy Hex)
        as [c Hstar2].
      exists c.
      assert (HssE : sstep segs (mkCfg msR model) []
                (SNext (mkCfg (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0)))
                              model))).
      { rewrite <- (apply_effect_no_write msR (Z_to_bv 64 0)).
        apply (sstep_syscall segs msR model x8 (mkEffect (Z_to_bv 64 0) [] [])
                 model model []);
          [exact Hh | exact Hsvc | | exact Hh |].
        - rewrite <- Hg1 in Hw, Haok. eapply (read0_ok_eof cnt Hcnt); eassumption.
        - rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity. }
      cbn [eof_tail].
      replace [ExitEv (Z_to_bv 64 0) (m_fs model)]
        with (([] : list event)
                ++ ([] ++ [ExitEv (bv_and (Z_to_bv 64 0) (Z_to_bv 64 255))
                             (m_fs model)]))
        by (rewrite band0_255; reflexivity).
      eapply star_trans; [exact Hstar0|].
      eapply star_step; [exact HssE | exact Hstar2].
    + (* input remains: the empty trace is a prefix of this run *)
      cbn [eof_tail app]. exists (mkCfg ms model). apply star_refl.
  - (* one more block: deliver it, echo ALL of it through the retry
       loop, loop *)
    destruct (to_rd_star ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
    destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
    pose proof (Hbytes bs Hlo Hhi) as Hwr.
    set (advB := advance_past_svc (apply_effect msR
                   (mkEffect (len_word bs) [(buf, bs)] []))) in *.
    set (model' := with_stdin (snd (stream_take s (length bs))) model).
    assert (Hh' : m_halted model' = None) by exact Hh.
    assert (HM' : M_loop model')
      by (unfold model'; rewrite <- Hst; apply M_loop_take; exact HM).
    assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bs)
              (SNext (mkCfg advB model'))).
    { apply (sstep_syscall segs msR model x8
               (mkEffect (len_word bs) [(buf, bs)] []) model' model'
               (map (ReadEv (Z_to_bv 64 0)) bs));
        [exact Hh | exact Hsvc | | exact Hh' |].
      - unfold model'. rewrite <- Hst. rewrite <- Hg1. rewrite <- Hg1 in Hw, Haok.
        eapply (read0_ok_bytes cnt Hcnt); try eassumption.
        rewrite Hst. exact Hpre.
      - rewrite (materialize_model_accesses_no_lazy model' _ (proj2 (proj2 (proj2 HM')))).
        reflexivity. }
    assert (Hfdc' : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model')
      by (apply fd1chan_fdchan; exact Hfd1).
    assert (Hbmbs : buf_modeled bs) by (unfold buf_modeled; lia).
    assert (Hst' : m_stdin model' = snd (stream_take s (length bs)))
      by reflexivity.
    assert (Hcont : forall ms', lh_next ms' ->
              exists c, star segs (mkCfg ms' model')
                (flat_map iter_ev blocks ++ eof_tail s'' (m_fs model')) c).
    { intros ms' Hlh.
      apply (IH ms' model' HM' Hst' (lh_next_to_rd ms' Hlh)). }
    destruct (to_wall_tail_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1)
                fd32_1 advB bs lh_next (to_wr_wall_tail bs advB Hwr) Hbmbs
                model' _ Hh' (proj2 (proj2 (proj2 HM'))) Hfdc' Hcont) as [c Hstar1].
    exists c.
    change (m_fs model') with (m_fs model) in Hstar1.
    cbn [flat_map]. unfold iter_ev at 1; unfold iter_ev_ch.
    rewrite <- !app_assoc.
    replace (map (ReadEv (Z_to_bv 64 0)) bs
               ++ map (WriteEv (Z_to_bv 64 1)) bs
               ++ flat_map iter_ev blocks ++ eof_tail s'' (m_fs model))
      with (([] : list event)
              ++ (map (ReadEv (Z_to_bv 64 0)) bs
                    ++ (map (WriteEv (Z_to_bv 64 1)) bs
                          ++ (flat_map iter_ev blocks
                                ++ eof_tail s'' (m_fs model)))))
      by reflexivity.
    eapply star_trans; [exact Hstar0|].
    eapply star_step; [exact HssR | exact Hstar1].
Qed.

(* ------------------------------------------------------------------------- *)
(* Exhaustiveness: every run trace is a stream trace.                         *)
(* ------------------------------------------------------------------------- *)

Lemma star_loop_only : forall c0 tr c', star segs c0 tr c' ->
  forall ms model, c0 = mkCfg ms model -> M_loop model ->
  (to_rd ms ->
     exists blocks s', chunks cnt (m_stdin model) blocks s' /\
       is_prefix tr (flat_map iter_ev blocks ++ eof_tail s' (m_fs model)))
  /\ (forall bs, (1 <= length bs)%nat -> buf_modeled bs ->
     to_wall_tail segs (Z_to_bv 64 1) ms bs lh_next ->
     exists blocks s',
       chunks cnt (m_stdin model) blocks s' /\
       is_prefix tr (map (WriteEv (Z_to_bv 64 1)) bs
                       ++ flat_map iter_ev blocks
                       ++ eof_tail s' (m_fs model))).
Proof.
  intros c0 tr c' Hstar.
  induction Hstar as [c | c1 evs c2 tr2 c3 Hss Hstar IH];
    intros ms model Heq HM; subst.
  - (* star_refl: the empty trace *)
    split.
    + intros _. exists [], (m_stdin model).
      split; [constructor | apply is_prefix_nil].
    + intros bs _ _ _. exists [], (m_stdin model).
      split; [constructor | apply is_prefix_nil].
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
      by (apply fd1chan_fdchan; exact Hfd1).
    split.
    + (* phase A: on the way to / at the read *)
      intro Hrd. destruct Hrd as [ms (buf & x8 & HRP) | ms ms' Hsvc Hstep Hrd'].
      * (* at the read ecall *)
        destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
        destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs (SNext c2)
                    Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
          as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
          inversion Hc2; subst.
        -- (* end of input: the rest of the run is the exit tail *)
           destruct (to_exit_star_only segs (Z_to_bv 64 0)
                       (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model
                       Hh Hlazy Hex tr2 c3 Hstar) as [-> | ->].
           ++ exists [], (m_stdin model).
              split; [constructor | apply is_prefix_nil].
           ++ exists [], (m_stdin model).
              split; [constructor|].
              rewrite Hs, band0_255. cbn [flat_map app eof_tail].
              apply is_prefix_refl.
        -- (* bytes: the rest of the run is a write-all phase *)
           assert (Hnb : (1 <= length bs)%nat) by lia.
           assert (Hbmbs : buf_modeled bs) by (unfold buf_modeled; lia).
           destruct (proj2 (IH _ _ eq_refl (M_loop_take (length bs) model HM)) bs
                       Hnb Hbmbs (to_wr_wall_tail bs _ (Hbytes bs Hlo Hhi)))
             as (blocks & s' & HCb & Hp).
           exists (bs :: blocks), s'.
           split; [eapply chunks_cons; eassumption|].
           cbn [flat_map]. unfold iter_ev at 1; unfold iter_ev_ch.
           rewrite <- !app_assoc.
           apply is_prefix_app_mono. exact Hp.
      * (* an ordinary instruction *)
        destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
                    Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
        inversion Hc2; subst.
        exact (proj1 (IH _ model eq_refl HM) Hrd').
    + (* phase B: inside the echo write-all (retry) loop *)
      intros bs Hnb Hbm Hwt.
      inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl | msS msS' restS kS HsvcS HstepS Hwt']; subst.
      * (* twt_done: the remainder is [], contradicting nonemptiness *)
        cbn in Hnb. lia.
      * (* twt_more: at the write ecall *)
        destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
                    ms bs lh_next model evs (SNext c2) Hh Hlazy Hfdc Hbm Hwl Hss)
          as (n & Hn1 & Hn2 & Hevs & Hc2 & Hwt2).
        inversion Hc2; subst.
        set (adv := advance_past_svc (set_gpr0 ms (len_word (firstn n bs)))) in *.
        destruct (Nat.eq_dec n (length bs)) as [-> | Hne].
        -- (* full delivery: the remainder is empty; back to the read *)
           rewrite skipn_all in Hwt2.
           destruct (to_wall_tail_nil_msteps segs (Z_to_bv 64 1) adv lh_next Hwt2)
             as (msL & HmL & HlhL).
           destruct (proj1 (IH _ model eq_refl HM)
                       (msteps_to_rd adv msL HmL (lh_next_to_rd msL HlhL)))
             as (blocks & s' & HCb & Hp).
           exists blocks, s'. split; [exact HCb|].
           rewrite firstn_all.
           apply is_prefix_app_mono. exact Hp.
        -- (* short delivery: the remainder is a shorter write-all phase *)
           assert (Hnb' : (1 <= length (skipn n bs))%nat)
             by (rewrite length_skipn; lia).
           destruct (proj2 (IH _ model eq_refl HM) (skipn n bs) Hnb'
                       (buf_modeled_skipn n bs Hbm) Hwt2)
             as (blocks & s' & HCb & Hp).
           exists blocks, s'. split; [exact HCb|].
           rewrite <- (firstn_skipn n bs) at 2.
           rewrite map_app, <- app_assoc.
           apply is_prefix_app_mono. exact Hp.
      * (* twt_step: an ordinary instruction *)
        destruct (sstep_instr_inv segs ms model msS' evs (SNext c2)
                    Hlazy HsvcS HstepS Hss) as [Hevs Hc2].
        inversion Hc2; subst.
        exact (proj2 (IH _ model eq_refl HM) bs Hnb Hbm Hwt').
Qed.

(* ------------------------------------------------------------------------- *)
(* No error: the phase invariant.                                            *)
(* ------------------------------------------------------------------------- *)

Definition sinv (c : config) : Prop :=
  (M_loop (cfg_model c) /\
     (to_rd (cfg_ms c)
      \/ exists bs, (1 <= length bs)%nat /\ buf_modeled bs /\
           to_wall_tail segs (Z_to_bv 64 1) (cfg_ms c) bs lh_next))
  \/ on_path segs (Z_to_bv 64 0) c.

Lemma sinv_step : forall c evs c',
  sinv c -> sstep segs c evs (SNext c') -> sinv c'.
Proof.
  intros [ms model] evs [ms' model'] Hinv Hss.
  destruct Hinv as [[HM Hphase] | Hop]; cbn [cfg_ms cfg_model] in *.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
      by (apply fd1chan_fdchan; exact Hfd1).
    destruct Hphase as [Hrd | (bs & Hnb & Hbm & Hwt)].
    + destruct Hrd as [ms (buf & x8 & HRP) | ms ms1 Hsvc Hstep Hrd'].
      * destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
        destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs
                    (SNext (mkCfg ms' model'))
                    Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
          as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
          inversion Hc2; subst.
        -- right. left. cbn. split; [exact Hh|].
           split; [exact Hlazy | exact Hex].
        -- left. cbn. split; [apply M_loop_take; exact HM|].
           right. exists bs. split; [lia|].
           split; [unfold buf_modeled; lia|].
           exact (to_wr_wall_tail bs _ (Hbytes bs Hlo Hhi)).
      * destruct (sstep_instr_inv segs ms model ms1 evs
                    (SNext (mkCfg ms' model')) Hlazy Hsvc Hstep Hss) as [_ Hc2].
        inversion Hc2; subst.
        left. cbn. split; [exact HM | left; exact Hrd'].
    + inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl
                       | msS msS' restS kS HsvcS HstepS Hwt']; subst.
      * (* twt_done: the remainder is [], contradicting nonemptiness *)
        cbn in Hnb. lia.
      * (* at the write ecall *)
        destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
                    ms bs lh_next model evs (SNext (mkCfg ms' model'))
                    Hh Hlazy Hfdc Hbm Hwl Hss)
          as (n & Hn1 & Hn2 & _ & Hc2 & Hwt2).
        inversion Hc2; subst.
        set (adv := advance_past_svc (set_gpr0 ms (len_word (firstn n bs)))) in *.
        destruct (Nat.eq_dec n (length bs)) as [-> | Hne].
        -- (* full delivery: back to the read phase *)
           rewrite skipn_all in Hwt2.
           destruct (to_wall_tail_nil_msteps segs (Z_to_bv 64 1) adv lh_next Hwt2)
             as (msL & HmL & HlhL).
           left. cbn. split; [exact HM|].
           left. exact (msteps_to_rd adv msL HmL (lh_next_to_rd msL HlhL)).
        -- (* short delivery: a shorter write-all phase *)
           left. cbn. split; [exact HM|].
           right. exists (skipn n bs).
           split; [rewrite length_skipn; lia|].
           split; [apply buf_modeled_skipn; exact Hbm | exact Hwt2].
      * destruct (sstep_instr_inv segs ms model msS' evs
                    (SNext (mkCfg ms' model')) Hlazy HsvcS HstepS Hss) as [_ Hc2].
        inversion Hc2; subst.
        left. cbn. split; [exact HM|].
        right. exists bs.
        split; [exact Hnb | split; [exact Hbm | exact Hwt']].
  - right. eapply on_path_step; eauto.
Qed.

Lemma sinv_no_error : forall c evs, sinv c -> ~ sstep segs c evs SError.
Proof.
  intros [ms model] evs Hinv Hss.
  destruct Hinv as [[HM Hphase] | Hop]; cbn [cfg_ms cfg_model] in *.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
      by (apply fd1chan_fdchan; exact Hfd1).
    destruct Hphase as [Hrd | (bs & Hnb & Hbm & Hwt)].
    + destruct Hrd as [ms (buf & x8 & HRP) | ms ms1 Hsvc Hstep Hrd'].
      * destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
        destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs SError
                    Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
          as [(_ & _ & Hc2) | (bs & _ & _ & _ & _ & Hc2)]; discriminate.
      * destruct (sstep_instr_inv segs ms model ms1 evs SError
                    Hlazy Hsvc Hstep Hss) as [_ Hc2]. discriminate.
    + inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl
                       | msS msS' restS kS HsvcS HstepS Hwt']; subst.
      * cbn in Hnb. lia.
      * exact (to_wall_no_error_sstep segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
                 ms bs lh_next model evs Hh Hlazy Hfdc Hbm Hwl Hss).
      * destruct (sstep_instr_inv segs ms model msS' evs SError
                    Hlazy HsvcS HstepS Hss) as [_ Hc2]. discriminate.
  - eapply on_path_no_error; eauto.
Qed.

Lemma star_sinv : forall c tr c', sinv c -> star segs c tr c' -> sinv c'.
Proof. exact (star_inv segs sinv sinv_step). Qed.

Lemma to_rd_no_error : forall ms model,
  M_loop model -> to_rd ms -> ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model HM Hrd.
  apply (inv_no_reaches_error segs sinv sinv_step sinv_no_error).
  left; cbn; auto.
Qed.

(* ------------------------------------------------------------------------- *)
(* Whole-run packaging from the initial state.                                *)
(* ------------------------------------------------------------------------- *)

(** The whole-run lemmas below are about a launch with a reader on the
    far end of fd 1 ([M_loop]'s [fd1chan]). *)
Lemma stream_obs_iff : forall pc ph sp brk0 mb rnd lim inp,
  to_rd (init_machine_state segs pc ph sp mb rnd inp) ->
  in_channel_reader inp = true ->
  forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
             <-> stream_traces cnt (in_fs inp) (in_stdin inp) tr.
Proof.
  intros pc ph sp brk0 mb rnd lim inp Hrd Hrdr tr.
  set (fs0 := in_fs inp) in *; set (stdin0 := in_stdin inp) in *.
  unfold init_config.
  set (ms0 := init_machine_state segs pc ph sp mb rnd inp) in *.
  pose proof (init_M_loop (segments_reserved segs) brk0 mb sp lim inp Hrdr) as HM0'.
  set (model0 := with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                   (init_model (segments_reserved segs) brk0 mb sp lim inp)) in *.
  assert (HM0 : M_loop model0) by exact HM0'.
  assert (Hst0 : m_stdin model0 = stdin0) by reflexivity.
  assert (Hfs0 : m_fs model0 = fs0) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (proj1 (star_loop_only _ _ _ Hstar ms0 model0 eq_refl HM0) Hrd)
      as (blocks & s' & HC & Hp').
    rewrite Hst0 in HC. rewrite Hfs0 in Hp'.
    apply (stream_traces_prefix_closed cnt fs0 stdin0 tr'); [|exact Hp].
    exists blocks, s'. split; assumption.
  - intros (blocks & s' & HC & Hp).
    destruct (stream_star_admits stdin0 blocks s' HC ms0 model0 HM0 Hst0 Hrd)
      as [c Hstar].
    rewrite Hfs0 in Hstar.
    exists (flat_map iter_ev blocks ++ eof_tail s' fs0), c.
    split; assumption.
Qed.

Lemma stream_no_error : forall pc ph sp brk0 mb rnd lim inp,
  to_rd (init_machine_state segs pc ph sp mb rnd inp) ->
  in_channel_reader inp = true ->
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
  intros pc ph sp brk0 mb rnd lim inp Hrd Hrdr.
  apply to_rd_no_error; [apply init_M_loop; exact Hrdr | exact Hrd].
Qed.

(* ------------------------------------------------------------------------- *)
(* The omni reading.  A stream loop need not terminate (the input stream is  *)
(* coinductive), so its judgments are the coinductive pair: the loop         *)
(* invariant IS a proof of [OmniRun.coexec … never_errors], by coinduction   *)
(* along [sinv_step] and with no [Run.star] in sight, and the trace          *)
(* characterisation is the prefix judgment [OmniRun.cosafe].                 *)
(* ------------------------------------------------------------------------- *)

Lemma to_rd_coexec : forall ms model,
  M_loop model -> to_rd ms -> OmniRun.coexec segs (mkCfg ms model) never_errors.
Proof.
  intros ms model HM Hrd.
  apply (inv_coexec segs sinv sinv_step sinv_no_error). left; cbn; auto.
Qed.

(** Stated at the CONFIGURATION rather than at [omni_corun], because
    [omni_corun] reads [Run.run_segments] of the image's segments while
    this section is parameterised by one segment list.  The callers
    below instantiate [segs] at [run_segments …], which is what
    [omni_corun] unfolds to. *)
Lemma stream_omni_corun : forall pc ph sp brk0 mb rnd lim inp,
  to_rd (init_machine_state segs pc ph sp mb rnd inp) ->
  in_channel_reader inp = true ->
  OmniRun.coexec segs (init_config segs pc ph sp brk0 mb rnd lim inp) never_errors.
Proof.
  intros pc ph sp brk0 mb rnd lim inp Hrd Hrdr. unfold init_config.
  set (model0 := with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                   (init_model (segments_reserved segs) brk0 mb sp lim inp)) in *.
  assert (HM0 : M_loop model0)
    by exact (init_M_loop (segments_reserved segs) brk0 mb sp lim inp Hrdr).
  apply to_rd_coexec; [exact HM0 | exact Hrd].
Qed.

Lemma stream_omni_cosafe : forall pc ph sp brk0 mb rnd lim inp,
  to_rd (init_machine_state segs pc ph sp mb rnd inp) ->
  in_channel_reader inp = true ->
  OmniRun.cosafe segs (init_config segs pc ph sp brk0 mb rnd lim inp)
    (stream_traces cnt (in_fs inp) (in_stdin inp)).
Proof.
  intros pc ph sp brk0 mb rnd lim inp Hrd Hrdr.
  apply cosafe_obs_iff.
  - intros t t' Ht Hp. eapply stream_traces_prefix_closed; eauto.
  - intros tr Hobs. apply (stream_obs_iff pc ph sp brk0 mb rnd lim inp Hrd Hrdr). exact Hobs.
Qed.

End Loop.

(* ========================================================================= *)
(* Pair equivalence: the characterization [stream_traces cnt fs0 stdin0] does *)
(* not mention the binary, so two binaries that both satisfy it are           *)
(* equivalent — ON THE SAME INPUT STREAM, which is what the theorem shape     *)
(* quantifies over.                                                          *)
(* ========================================================================= *)

(** The omni equivalence of two stream loops on the same input stream,
    at the two role budgets, on a launch with a reader on stdout. *)
Lemma stream_omni_strong_equiv :
  forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd inp,
  (forall ms, rLH ms -> to_rd (run_segments source_segs inp rsp rmb) rLH cnt ms) ->
  (forall ms, aLH ms -> to_rd (run_segments target_segs inp asp amb) aLH cnt ms) ->
  to_rd (run_segments source_segs inp rsp rmb) rLH cnt
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) ->
  to_rd (run_segments target_segs inp asp amb) aLH cnt
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) ->
  in_channel_reader inp = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros cnt Hcnt source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd
         inp HrLH HaLH Hr Ha Hrdr.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [exact (stream_omni_corun (run_segments source_segs inp rsp rmb) rLH cnt Hcnt HrLH
                rpc rph rsp rbrk rmb rrnd
                source_alloc_limit inp Hr Hrdr) | apply never_errors_covered]. }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (stream_obs_iff (run_segments source_segs inp rsp rmb) rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd source_alloc_limit inp Hr Hrdr tr).
    rewrite (stream_obs_iff (run_segments target_segs inp asp amb) aLH cnt Hcnt HaLH apc aph asp abrk amb arnd target_alloc_limit inp Ha Hrdr tr).
    reflexivity.
  - exact (stream_omni_corun (run_segments target_segs inp asp amb) aLH cnt Hcnt HaLH apc aph asp abrk amb arnd target_alloc_limit inp Ha Hrdr).
Qed.

Lemma stream_strong_equiv :
  forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim inp,
  (forall ms, rLH ms -> to_rd (run_segments source_segs inp rsp rmb) rLH cnt ms) ->
  (forall ms, aLH ms -> to_rd (run_segments target_segs inp asp amb) aLH cnt ms) ->
  to_rd (run_segments source_segs inp rsp rmb) rLH cnt
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) ->
  to_rd (run_segments target_segs inp asp amb) aLH cnt
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) ->
  in_channel_reader inp = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros cnt Hcnt source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim
         inp HrLH HaLH Hr Ha Hrdr.
  split.
  { apply no_error_run_modeled.
    apply (stream_no_error (run_segments source_segs inp rsp rmb) rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd rlim inp Hr Hrdr). }
  right. split.
  - intro tr. cbn.
    rewrite (stream_obs_iff (run_segments source_segs inp rsp rmb) rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd rlim inp Hr Hrdr tr).
    rewrite (stream_obs_iff (run_segments target_segs inp asp amb) aLH cnt Hcnt HaLH apc aph asp abrk amb arnd alim inp Ha Hrdr tr).
    reflexivity.
  - cbn. apply (stream_no_error (run_segments target_segs inp asp amb) aLH cnt Hcnt HaLH apc aph asp abrk amb arnd alim inp Ha Hrdr).
Qed.
