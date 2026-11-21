(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(** * Common.WallSim — the "write-all" retry node over a channel.

    TRUST BOUNDARY: image-INDEPENDENT proof library (like Common.CatSim),
    built over the [LinuxProcessSem.Run] trace semantics and its omni
    reading [LinuxProcessSem.OmniRun].

    A channel write delivers a nondeterministic NONEMPTY prefix of the
    offered buffer (CatSim's delivered-length family).  Real binaries
    therefore wrap every program-level "write buf" in a put-style retry
    loop: after the write returns a0 = n (1 <= n <= len), the code
    advances the pointer by n, decrements the remaining count by n, and
    reissues the write iff the remainder is nonzero.  Each such loop
    performs one or more write syscalls whose deliveries concatenate to
    exactly the original buffer, so its trace contribution is exactly
    [map (WriteEv ch) buf] — independent of the chunking.

    [to_wall ms rest k] captures that shape: [ms] is a write-pending
    ecall state offering [rest] (nonempty) on [fd]; the machine delivers
    exactly [rest] across one or more (possibly short) channel writes,
    then reaches a state satisfying the continuation PREDICATE [k].
    [to_wall_tail ms rest k] is the between-syscalls form: the machine
    still owes [rest] (instruction steps, then — if [rest] is nonempty —
    another write-pending state; if [rest] is empty, a [k]-state).
    Because the continuation is a predicate, the node composes with any
    downstream shape (StreamSim's loop-head [lh_next], CatSim's
    [to_wexit], ...) without mutual induction across files.

    Conventions follow CatSim's [Section WithSegsCh]: generic over the
    loaded segments [segs] and an (fd, channel) pair with
    [fd32 fd = fd]; the pending syscall number is Z-characterized
    ([bv_unsigned x8 = 64%Z]); buffers are [list byte]. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only Require Import SimInv ExitSim CatSim PropExec SeqExec CatExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.
Section WithFP1.
Context {fx : FPState}.


(** The stdout/stderr fd literals are 32-bit-stable (the [fd32]
    truncation [check_syscall] applies leaves them unchanged) — the
    [Hfd32] instantiations every consumer needs. *)
Lemma fd32_1 : fd32 (Z_to_bv 64 1) = Z_to_bv 64 1.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma fd32_2 : fd32 (Z_to_bv 64 2) = Z_to_bv 64 2.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* ========================================================================= *)
(* Put-loop arithmetic: the delivered length as a word, the pointer bump,    *)
(* and the count decrement, in the forms the per-binary retry-loop proofs    *)
(* meet (a0 = [len_word (firstn n bs)] after the write).                     *)
(* ========================================================================= *)

(** [bv_unsigned] of a modeled block length (all lengths here are far
    below 2^64). *)
Lemma u_len_word : forall {A} (l : list A), (Z.of_nat (length l) < 2^64)%Z ->
  bv_unsigned (len_word l) = Z.of_nat (length l).
Proof.
  intros A l H. unfold len_word. apply Z_to_bv_small.
  unfold bv_modulus. change (Z.of_N 64) with 64%Z. lia.
Qed.

(* [c_lts_0_pos] — [blez a0] falling through on a nonempty delivery —
   lives in PropExec, beside [c_lts_pos_0] and [c_lts_small], and so
   does [c_eq_0_of_u], the [beqz] on full delivery, beside
   [c_eq_0_false]. *)

Lemma len_word_firstn_nat : forall n (bs : list byte),
  (n <= length bs)%nat ->
  len_word (firstn n bs) = nat_to_word n.
Proof.
  intros n bs Hn. unfold len_word, nat_to_word.
  rewrite firstn_length_le by exact Hn. reflexivity.
Qed.

Lemma u_len_word_firstn : forall n (bs : list byte),
  (n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
  bv_unsigned (len_word (firstn n bs)) = Z.of_nat n.
Proof.
  intros n bs Hn Hlen.
  rewrite len_word_unsigned by (rewrite firstn_length_le by exact Hn;
                                unfold two_pow_64; lia).
  rewrite firstn_length_le by exact Hn. reflexivity.
Qed.

(** The pointer bump [add a1,a1,a0] after a delivery of [n] bytes lands
    on the address the suffix-read lemma [SeqExec.rdn_skipn] names. *)
Lemma v_add_len_firstn : forall (p : word) n (bs : list byte),
  (n <= length bs)%nat ->
  v_add p (len_word (firstn n bs)) = p + nat_to_word n.
Proof.
  intros p n bs Hn. rewrite len_word_firstn_nat by exact Hn.
  unfold v_add. apply bv_eq.
  rewrite Z_to_bv_unsigned, bv_add_unsigned. reflexivity.
Qed.

(** [v_add] variant landing on the canonical [Z_to_bv 64 (...)] form. *)
Lemma v_add_len_firstn_Z : forall (p : word) n (bs : list byte),
  (n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
  v_add p (len_word (firstn n bs)) = Z_to_bv 64 (bv_unsigned p + Z.of_nat n).
Proof.
  intros p n bs Hn Hlen. unfold v_add.
  rewrite u_len_word_firstn by assumption. reflexivity.
Qed.

(** [SeqExec.rdn_skipn]'s address, in the canonical form. *)
Lemma word_add_nat_Z : forall (p : word) (k : nat),
  (Z.of_nat k < 2^64)%Z ->
  p + nat_to_word k = Z_to_bv 64 (bv_unsigned p + Z.of_nat k).
Proof.
  intros p k Hk. apply bv_eq.
  rewrite bv_add_unsigned. unfold nat_to_word.
  rewrite Z_to_bv_small
    by (unfold bv_modulus; change (Z.of_N 64) with 64%Z; lia).
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(** The count decrement [sub a2,a2,a0] is the remainder's length. *)
Lemma v_sub_len_firstn : forall n (bs : list byte),
  (n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
  v_sub (len_word bs) (len_word (firstn n bs)) = len_word (skipn n bs).
Proof.
  intros n bs Hn Hlen. apply bv_eq.
  rewrite v_sub_small
    by (rewrite u_len_word_firstn by assumption;
        rewrite len_word_unsigned by (unfold two_pow_64; lia); lia).
  rewrite u_len_word_firstn by assumption.
  rewrite !len_word_unsigned
    by (unfold two_pow_64; rewrite ?length_skipn; lia).
  rewrite length_skipn. lia.
Qed.

Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

(* ========================================================================= *)
(* The write-all node.                                                       *)
(* ========================================================================= *)

(** [to_wall ms rest k]: [ms] is a write-pending ecall state offering
    [rest] (nonempty) on [fd]; the machine delivers exactly [rest] across
    one or more (possibly short) channel writes, then reaches a state
    satisfying [k].  The trace contribution is exactly
    [map (WriteEv ch) rest].  The write node is RET-OBLIVIOUS: the
    continuation must handle every delivered length [n]. *)
Inductive to_wall : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twl_write : forall ms x8 rest k,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = fd ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
    (1 <= length rest)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
       to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
         (skipn n rest) k) ->
    to_wall ms rest k
with to_wall_tail : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twt_done : forall ms k, k ms -> to_wall_tail ms [] k
| twt_more : forall ms rest k,
    (1 <= length rest)%nat ->
    to_wall ms rest k ->
    to_wall_tail ms rest k
| twt_step : forall ms ms' rest k,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wall_tail ms' rest k ->
    to_wall_tail ms rest k.

Scheme to_wall_min := Minimality for to_wall Sort Prop
  with to_wall_tail_min := Minimality for to_wall_tail Sort Prop.
Combined Scheme to_wall_mutind from to_wall_min, to_wall_tail_min.

(** msteps-prepend glue (the ergonomic bridge per-binary loop proofs
    use, mirroring [CatSim.msteps_to_wexit]). *)
Lemma msteps_to_wall_tail : forall ms ms' rest k,
  msteps segs ms ms' -> to_wall_tail ms' rest k -> to_wall_tail ms rest k.
Proof.
  intros ms ms' rest k H; induction H; [auto|].
  intro Hw. eapply twt_step; eauto.
Qed.

(** An empty remainder is a straight instruction line to a [k]-state. *)
Lemma to_wall_tail_nil_msteps : forall ms k,
  to_wall_tail ms [] k -> exists ms', msteps segs ms ms' /\ k ms'.
Proof.
  intros ms k H.
  remember ([] : list byte) as rest eqn:Hrest.
  induction H as [ms k Hk | ms rest k Hnb Hw | ms ms' rest k Hsvc Hstep Ht IH].
  - exists ms. split; [apply mst_refl | exact Hk].
  - subst rest. cbn in Hnb. lia.
  - destruct (IH Hrest) as (ms'' & Hm & Hk).
    exists ms''. split; [eapply mst_step; eauto | exact Hk].
Qed.

Hypothesis Hfd32 : fd32 fd = fd.

(* ========================================================================= *)
(* One-step inversion at the write-pending head, WITH the continuation:      *)
(* the delivered chunk is a nonempty prefix, and the remainder derivation    *)
(* continues at [skipn n rest].  This is the shape the downstream loop      *)
(* invariants ([sinv], [dinv]) and [to_wall_exec_mut] consume (an SError    *)
(* [st] is refuted by the [SNext] equation).                                 *)
(* ========================================================================= *)

Lemma sstep_to_wall_inv : forall ms rest k model evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  buf_modeled rest ->
  to_wall ms rest k ->
  sstep segs (mkCfg ms model) evs st ->
  exists n, (1 <= n)%nat /\ (n <= length rest)%nat /\
    evs = map (WriteEv ch) (firstn n rest) /\
    st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n rest)))) model) /\
    to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
      (skipn n rest) k.
Proof.
  intros ms rest k model evs st Hh Hlazy Hfdc Hbm Hw Hss.
  revert Hbm.
  destruct Hw as [ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont]. intro Hbm.
  destruct (sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs st
              Hh Hlazy Hfdc Hsvc Hno Hg Hr Hok Hbm Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hst).
  exists n. repeat split; try assumption.
  apply (Hcont n Hn1 Hn2).
Qed.

Lemma to_wall_no_error_sstep : forall ms rest k model evs,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  buf_modeled rest ->
  to_wall ms rest k ->
  ~ sstep segs (mkCfg ms model) evs SError.
Proof.
  intros ms rest k model evs Hh Hlazy Hfdc Hbm Hw Hss.
  destruct (sstep_to_wall_inv ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss)
    as (n & _ & _ & _ & Hst & _).
  discriminate Hst.
Qed.

(* ========================================================================= *)
(* Star admissibility: the retry loop realizes the full-buffer trace.        *)
(* One syscall (full delivery) per node suffices as the witness.             *)
(* ========================================================================= *)

Lemma to_wall_star_admits_mut : forall model tr_k,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms rest k, to_wall ms rest k ->
     buf_modeled rest ->
     (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
     exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)
  /\ (forall ms rest k, to_wall_tail ms rest k ->
     buf_modeled rest ->
     (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
     exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c).
Proof.
  intros model tr_k Hh Hlazy Hfdc.
  apply (to_wall_mutind
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
       exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
       exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)).
  - (* twl_write: deliver everything in one syscall *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont IH Hbm Hk.
    destruct (IH (length rest) Hnb (Nat.le_refl _)
                (buf_modeled_skipn (length rest) rest Hbm) Hk) as [c Hstar].
    exists c.
    replace (map (WriteEv ch) rest ++ tr_k)
      with (map (WriteEv ch) (firstn (length rest) rest)
              ++ (map (WriteEv ch) (skipn (length rest) rest) ++ tr_k))
      by (rewrite firstn_all, skipn_all; reflexivity).
    eapply star_step; [| exact Hstar].
    rewrite <- (apply_effect_copyins_no_write ms
                  (len_word (firstn (length rest) rest))
                  [(ms_gpr ms 1, length rest)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, length rest)]
                (mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
             (map (WriteEv ch) (firstn (length rest) rest)));
      [exact Hh | exact Hsvc | | exact Hh |].
    eapply write_ch_ok_n; try eassumption. apply Nat.le_refl.
    rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
  - (* twt_done: hand off to the continuation *)
    intros ms k Hk Hbm Hcont. cbn [map app]. apply (Hcont ms Hk).
  - (* twt_more *)
    intros ms rest k Hnb Hw IH Hbm Hk. exact (IH Hbm Hk).
  - (* twt_step *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm Hk.
    destruct (IH Hbm Hk) as [c Hstar].
    exists c.
    replace (map (WriteEv ch) rest ++ tr_k)
      with (([] : list event) ++ (map (WriteEv ch) rest ++ tr_k)) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma to_wall_star_admits : forall ms rest k,
  to_wall ms rest k ->
  buf_modeled rest ->
  forall model tr_k,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
  exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c.
Proof.
  intros ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk.
  exact (proj1 (to_wall_star_admits_mut model tr_k Hh Hlazy Hfdc) ms rest k Hw Hbm Hk).
Qed.

Lemma to_wall_tail_star_admits : forall ms rest k,
  to_wall_tail ms rest k ->
  buf_modeled rest ->
  forall model tr_k,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
  exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c.
Proof.
  intros ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk.
  exact (proj2 (to_wall_star_admits_mut model tr_k Hh Hlazy Hfdc) ms rest k Hw Hbm Hk).
Qed.

(* ========================================================================= *)
(* Star exhaustiveness: every trace out of the retry loop is a prefix of     *)
(* the full-buffer events followed by whatever the continuation admits.      *)
(* ========================================================================= *)

Lemma to_wall_star_only_mut : forall model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms rest k, to_wall ms rest k ->
     buf_modeled rest ->
     (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
     forall tr c, star segs (mkCfg ms model) tr c ->
     is_prefix tr (map (WriteEv ch) rest ++ T))
  /\ (forall ms rest k, to_wall_tail ms rest k ->
     buf_modeled rest ->
     (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
     forall tr c, star segs (mkCfg ms model) tr c ->
     is_prefix tr (map (WriteEv ch) rest ++ T)).
Proof.
  intros model T Hh Hlazy Hfdc.
  apply (to_wall_mutind
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
       forall tr c, star segs (mkCfg ms model) tr c ->
       is_prefix tr (map (WriteEv ch) rest ++ T))
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
       forall tr c, star segs (mkCfg ms model) tr c ->
       is_prefix tr (map (WriteEv ch) rest ++ T))).
  - (* twl_write *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont IH Hbm HK tr c Hstar.
    inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
    { apply is_prefix_nil. }
    destruct (sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs (SNext c2)
                Hh Hlazy Hfdc Hsvc Hno Hg Hr Hok Hbm Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc2).
    subst evs. inversion Hc2; subst c2.
    pose proof (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK tr2 c Hstar2) as Hp.
    rewrite <- (firstn_skipn n rest) at 2.
    rewrite map_app, <- app_assoc.
    apply is_prefix_app_mono. exact Hp.
  - (* twt_done *)
    intros ms k Hk Hbm HK tr c Hstar. cbn [map app]. exact (HK ms tr c Hk Hstar).
  - (* twt_more *)
    intros ms rest k Hnb Hw IH Hbm HK tr c Hstar. exact (IH Hbm HK tr c Hstar).
  - (* twt_step *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm HK tr c Hstar.
    inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
    { apply is_prefix_nil. }
    destruct (sstep_instr_inv segs ms model ms' evs (SNext c2) Hlazy Hsvc Hstep Hss)
      as [Hevs Hc2].
    subst evs. inversion Hc2; subst c2. cbn [app].
    exact (IH Hbm HK tr2 c Hstar2).
Qed.

Lemma to_wall_star_only : forall ms rest k,
  to_wall ms rest k ->
  buf_modeled rest ->
  forall model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
  forall tr c, star segs (mkCfg ms model) tr c ->
  is_prefix tr (map (WriteEv ch) rest ++ T).
Proof.
  intros ms rest k Hw Hbm model T Hh Hlazy Hfdc HK tr c Hstar.
  exact (proj1 (to_wall_star_only_mut model T Hh Hlazy Hfdc) ms rest k Hw Hbm HK tr c Hstar).
Qed.

(* ========================================================================= *)
(* Ergonomic raw-ecall-record wrapper (mirrors CatExec/SeqExec's [_rec]      *)
(* entry points): the write node at the state [step_ecall] leaves.           *)
(* ========================================================================= *)

Lemma twl_write_rec : forall (k : machine_state -> Prop) rest regs pc mem rom,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = fd ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None;
                   ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some rest ->
  access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12)) = true ->
  (1 <= length rest)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
     to_wall_tail (mkst (regupd regs 10 (len_word (firstn n rest)))
                        (v_addi pc 4) mem rom)
       (skipn n rest) k) ->
  to_wall {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
             ms_svc_pending := Some (getr regs 17); ms_resv := None;
             ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    rest k.
Proof.
  intros k rest regs pc mem rom H17 H10 Hr Hok Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  eapply twl_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hok.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

(* ========================================================================= *)
(* to_wallexit: an exit-after-writes run whose EVERY write goes through a     *)
(* put-style retry loop (a [to_wall] node).  Because each retry loop          *)
(* delivers exactly its full buffer — chunking-independently — the trace      *)
(* set of such a run is the ORIGINAL full-delivery form: the prefixes of      *)
(* [wevents_ch ch bufs ++ [ExitEv code fs]].  This is the wall-node           *)
(* counterpart of [CatSim.to_wexit] (whose ret-oblivious write node keeps     *)
(* serving binaries that genuinely propagate short deliveries).               *)
(*                                                                           *)
(* The base case [bufs = []] is [CatSim.to_wexit ms [] code] — the exit       *)
(* straight line — so all existing per-example exit-path lemmas apply         *)
(* unchanged.                                                                *)
(* ========================================================================= *)

Fixpoint to_wallexit (bufs : list (list byte)) (code : word)
    (ms : machine_state) : Prop :=
  match bufs with
  | [] => to_wexit segs ms [] code
  | buf :: rest =>
      (1 <= length buf)%nat /\
      to_wall_tail ms buf (to_wallexit rest code)
  end.

(** Every finite wall derivation bottoms out in a continuation state
    (deliver everything at each write). *)
Lemma to_wall_k_ex_mut :
  (forall ms rest k, to_wall ms rest k -> exists ms', k ms')
  /\ (forall ms rest k, to_wall_tail ms rest k -> exists ms', k ms').
Proof.
  apply (to_wall_mutind
           (fun ms rest k => exists ms', k ms')
           (fun ms rest k => exists ms', k ms')).
  - intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont IH.
    exact (IH (length rest) Hnb (Nat.le_refl _)).
  - intros ms k Hk. exists ms. exact Hk.
  - intros ms rest k Hnb Hw IH. exact IH.
  - intros ms ms' rest k Hsvc Hstep Ht IH. exact IH.
Qed.

Lemma to_wall_tail_k_ex : forall ms rest k,
  to_wall_tail ms rest k -> exists ms', k ms'.
Proof. exact (proj2 to_wall_k_ex_mut). Qed.

Lemma to_wallexit_bufs_nonempty : forall bufs code ms,
  to_wallexit bufs code ms ->
  Forall (fun b : list byte => (1 <= length b)%nat) bufs.
Proof.
  induction bufs as [|buf rest IH]; intros code ms Hw; [constructor|].
  destruct Hw as [Hnb Hw]. constructor; [exact Hnb|].
  destruct (to_wall_tail_k_ex _ _ _ Hw) as [ms' Hk].
  exact (IH code ms' Hk).
Qed.

(** Single-instruction prepend, in the shape [StepTac.chain_step]
    consumes (the [to_wallexit] counterpart of [CatSim.tw_step]). *)
Lemma twe_step : forall ms ms' bufs code,
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
  intros ms ms' bufs code Hsvc Hstep Hw.
  destruct bufs as [|buf rest].
  - eapply tw_step; eauto.
  - destruct Hw as [Hnb Hw]. split; [exact Hnb|].
    eapply twt_step; eauto.
Qed.

Lemma msteps_to_wallexit : forall ms ms' bufs code,
  msteps segs ms ms' -> to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
  intros ms ms' bufs code Hms Hw. destruct bufs as [|buf rest].
  - exact (msteps_to_wexit segs ms ms' [] code Hms Hw).
  - destruct Hw as [Hnb Hw]. split; [exact Hnb|].
    eapply msteps_to_wall_tail; eauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* The omni reading.  One mutual induction over [to_wall]/[to_wall_tail]     *)
(* gives, for every chunking at once, that the node emits exactly its buffer  *)
(* and then continues into a configuration satisfying the continuation's own  *)
(* judgment; [to_wallexit_exec] then chains the nodes and the exit into the   *)
(* exact full-delivery trace.  The star-only, star-admits and no-error lemmas *)
(* below are its corollaries.                                                  *)
(* ------------------------------------------------------------------------- *)

Lemma to_wall_exec_mut : forall model (Q : post),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms rest k, to_wall ms rest k ->
     buf_modeled rest ->
     (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
     OmniRun.exec segs (mkCfg ms model)
       (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))
  /\ (forall ms rest k, to_wall_tail ms rest k ->
     buf_modeled rest ->
     (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
     OmniRun.exec segs (mkCfg ms model)
       (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o)).
Proof.
  intros model Q Hh Hlazy Hfdc.
  apply (to_wall_mutind
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
       OmniRun.exec segs (mkCfg ms model)
         (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
       OmniRun.exec segs (mkCfg ms model)
         (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))).
  - (* twl_write: every delivered length is a successor, each covered by the IH *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont IH Hbm HK.
    assert (Hw : to_wall ms rest k) by (eapply twl_write; eassumption).
    apply exec_step; [exact Hh | | |].
    + (* progress: deliver everything in one syscall *)
      eexists; eexists.
      apply (sstep_syscall segs ms model x8
               (with_copyins [(ms_gpr ms 1, length rest)]
                  (mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
               (map (WriteEv ch) (firstn (length rest) rest)));
        [exact Hh | exact Hsvc | | exact Hh |].
      * eapply write_ch_ok_n; try eassumption. apply Nat.le_refl.
      * rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
    + intros evs Hss.
      destruct (sstep_to_wall_inv ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss)
        as (n & _ & _ & _ & Habs & _).
      discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_to_wall_inv ms rest k model evs (SNext c') Hh Hlazy Hfdc Hbm Hw Hss)
        as (n & Hn1 & Hn2 & -> & Hc' & _).
      injection Hc' as ->.
      eapply exec_conseq;
        [exact (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK) |].
      intros tr o (tr' & -> & HQ). exists tr'. split; [| exact HQ].
      rewrite <- (firstn_skipn n rest) at 3. rewrite map_app, <- app_assoc. reflexivity.
  - (* twt_done: the continuation's own judgment *)
    intros ms k Hk Hbm HK.
    eapply exec_conseq; [exact (HK ms Hk) |].
    intros tr o HQ. exists tr. split; [reflexivity | exact HQ].
  - (* twt_more *)
    intros ms rest k Hnb Hw IH Hbm HK. exact (IH Hbm HK).
  - (* twt_step: one silent instruction *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm HK.
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbm HK) |]. intros tr o H. cbn [app]. exact H.
Qed.

(** The exit straight line at the bottom of every [to_wallexit]: the
    [bufs = []] fragment of [CatSim.to_wexit], which needs no channel
    assumption. *)
Lemma to_wexit_nil_exec_aux : forall ms bufs code model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_wexit segs ms bufs code ->
  bufs = [] ->
  OmniRun.exec segs (mkCfg ms model)
    (fun tr o => tr = [ExitEv code (m_fs model)] /\ exits_with code tr o).
Proof.
  intros ms bufs code model Hh Hlazy Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH]; intro Hbufs; [| discriminate Hbufs |].
  - apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * cbn beta. rewrite app_nil_r. split; [reflexivity |].
        cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbufs) |]. intros tr o H. cbn [app]. exact H.
Qed.

Lemma to_wexit_nil_exec : forall ms code model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_wexit segs ms [] code ->
  OmniRun.exec segs (mkCfg ms model)
    (fun tr o => tr = [ExitEv code (m_fs model)] /\ exits_with code tr o).
Proof.
  intros ms code model Hh Hlazy Hte.
  exact (to_wexit_nil_exec_aux ms [] code model Hh Hlazy Hte eq_refl).
Qed.

(** THE judgment for a retry-loop run: exactly the full-delivery trace,
    then the exit, on every execution. *)
Lemma to_wallexit_exec : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  OmniRun.exec segs (mkCfg ms model)
    (fun tr o => tr = wevents_ch ch bufs ++ [ExitEv code (m_fs model)]
                 /\ exits_with code tr o).
Proof.
  induction bufs as [|buf rest IH]; intros code ms model Hh Hlazy Hfdc Hbm Hw.
  - cbn [wevents_ch app]. apply to_wexit_nil_exec; assumption.
  - destruct Hw as [Hnb Hw]. apply Forall_cons_iff in Hbm as [Hb Hbs].
    eapply exec_conseq;
      [exact (proj2 (to_wall_exec_mut model _ Hh Hlazy Hfdc) ms buf (to_wallexit rest code)
                Hw Hb (fun ms' Hk => IH code ms' model Hh Hlazy Hfdc Hbs Hk)) |].
    intros tr o (tr' & -> & Heq & Hx). split; [| exact Hx].
    rewrite Heq. cbn [wevents_ch]. rewrite <- app_assoc. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* Star admissibility and exhaustiveness for [to_wallexit] -- the ORIGINAL   *)
(* full-delivery trace set -- as corollaries of [to_wallexit_exec].          *)
(* ------------------------------------------------------------------------- *)

Lemma to_wallexit_star_admits : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  exists c, star segs (mkCfg ms model)
              (wevents_ch ch bufs ++ [ExitEv code (m_fs model)]) c.
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw.
  destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
    as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
  subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  exists c'. exact Hstar.
Qed.

(** Bites.  The judgment names the trace AND the code: it does not exit
    with any other code, its trace is no other list, and it does not
    stay silent.  ([to_wallexit_no_other_exit] would survive a
    postcondition that forgot the writes; [to_wallexit_trace_unique] is
    the one that pins them.) *)
Lemma to_wallexit_no_other_exit : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  forall code', code' <> code ->
  ~ OmniRun.exec segs (mkCfg ms model) (exits_with code').
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw code' Hne Hex.
  destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
    as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'.
  exact (Hne (eq_sym Hx')).
Qed.

Lemma to_wallexit_trace_unique : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  forall tr', tr' <> wevents_ch ch bufs ++ [ExitEv code (m_fs model)] ->
  ~ OmniRun.exec segs (mkCfg ms model) (fun tr _ => tr = tr').
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw tr' Hne Hex.
  destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
    as (tr & o & Hm & Heq & _).
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Heq'. cbn beta in Heq'.
  apply Hne. rewrite <- Heq', Heq. reflexivity.
Qed.

Lemma to_wallexit_not_silent : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  ~ cosafe segs (mkCfg ms model) (fun tr => tr = []).
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw Hc.
  destruct (to_wallexit_star_admits bufs code ms model Hh Hlazy Hfdc Hbm Hw) as (c' & Hstar).
  pose proof (cosafe_star _ _ _ _ _ Hc Hstar) as Hnil.
  destruct (wevents_ch ch bufs); discriminate Hnil.
Qed.

Lemma to_wallexit_star_only : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  forall tr c, star segs (mkCfg ms model) tr c ->
  is_prefix tr (wevents_ch ch bufs ++ [ExitEv code (m_fs model)]).
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw tr c Hstar.
  destruct (exec_realizes _ _ _
              (exec_star _ _ _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw) Hstar))
    as (tr' & o & _ & HQ).
  cbn beta in HQ. destruct HQ as (Heq & _). rewrite <- Heq. apply is_prefix_app.
Qed.

(* ------------------------------------------------------------------------- *)
(* No-error: a corollary of the omni judgment.                               *)
(* ------------------------------------------------------------------------- *)

Lemma to_wallexit_no_error : forall ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model bufs code Hh Hlazy Hfdc Hbm Hw. apply exec_no_error.
  eapply exec_conseq; [exact (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

End WithSegsCh.

(** [to_wallexit] at fd 1, in [CatSim.to_wexit]'s argument order — the
    drop-in replacement for a per-binary [to_wexit] chain whose writes
    all go through put-style retry loops. *)
Abbreviation wexit1 segs ms bufs code :=
  (to_wallexit segs (Z_to_bv 64 1) bufs code ms).

(** The generic-channel event list at fd 1 is [CatSim.wevents]. *)
Lemma wevents_ch_fd1 : forall bufs,
  wevents_ch (Z_to_bv 64 1) bufs = wevents bufs.
Proof.
  induction bufs as [|b bs IH]; cbn [wevents_ch wevents];
    [reflexivity | rewrite IH; reflexivity].
Qed.

(* ========================================================================= *)
(* Run-level packaging: the ORIGINAL full-delivery statements, for binaries   *)
(* whose every write is a put-style retry loop.                               *)
(* ========================================================================= *)

(** The vDSO counter does not move a descriptor's channel: [with_vdso]
    rebuilds the VM subsystem and keeps [m_fd]. *)
Lemma fdchan_with_vdso : forall v m fd ch, fdchan fd ch m -> fdchan fd ch (with_vdso v m).
Proof. intros v m fd ch H; exact H. Qed.

(** The run-level omni judgment of a retry-loop run. *)
Lemma wall_omni_run : forall fd ch, fd32 fd = fd ->
  forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  fdchan fd ch (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp) ->
  bufs_modeled bufs ->
  to_wallexit (run_segments segs inp sp mb) fd bufs code
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (fun tr o => tr = wevents_ch ch bufs ++ [ExitEv code (in_fs inp)]
                 /\ exits_with code tr o).
Proof.
  intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw.
  cbn [omni_run]. unfold init_config.
  exact (to_wallexit_exec (run_segments segs inp sp mb) fd ch Hfd32 bufs code _
           (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           eq_refl eq_refl (fdchan_with_vdso _ _ _ _ Hfdc) Hbm Hw).
Qed.

Lemma wall_obs_iff : forall fd ch, fd32 fd = fd ->
  forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  fdchan fd ch (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp) ->
  bufs_modeled bufs ->
  to_wallexit (run_segments segs inp sp mb) fd bufs code
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  forall tr, obs_trace (run_segments segs inp sp mb)
               (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) tr
             <-> is_prefix tr (wevents_ch ch bufs ++ [ExitEv code (in_fs inp)]).
Proof.
  intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw tr.
  apply exec_obs_iff.
  eapply exec_conseq;
    [exact (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) |].
  intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.

Lemma wall_no_error_run : forall fd ch, fd32 fd = fd ->
  forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  fdchan fd ch (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp) ->
  bufs_modeled bufs ->
  to_wallexit (run_segments segs inp sp mb) fd bufs code
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  ~ reaches_error (run_segments segs inp sp mb)
      (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp).
Proof.
  intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw. apply exec_no_error.
  eapply exec_conseq;
    [exact (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(** The omni equivalence for two retry-loop exit-after-writes binaries
    emitting the same buffers and exit code, at the two role budgets, on
    a launch with a reader on the far end of fd 1: a reader-gone write
    KILLS the process (see [CatSim.fd1chan]), which the retry loop's
    derivation does not describe. *)
Lemma wall_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp,
  to_wallexit (run_segments source_segs inp rsp rmb) (Z_to_bv 64 1) bufs code
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) ->
  to_wallexit (run_segments target_segs inp asp amb) (Z_to_bv 64 1) bufs code
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) ->
  bufs_modeled bufs ->
  in_channel_reader inp = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp
    Hsource Htarget Hbm Hr.
  assert (HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp source_alloc_limit inp))
    by (apply fd1chan_fdchan, init_model_fd1chan; exact Hr).
  assert (HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp target_alloc_limit inp))
    by (apply fd1chan_fdchan, init_model_fd1chan; exact Hr).
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (wall_omni_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 source_segs rpc rph rsp rbrk rmb rrnd
                source_alloc_limit inp bufs code HfdS Hbm Hsource) |].
    intros tr o (_ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code HfdS Hbm Hsource tr).
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
             target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm Htarget).
Qed.

(** The [Equivalence]-level equivalence for two retry-loop exit-after-writes
    binaries emitting the same buffers and exit code — the statement
    [CatSim.cat_strong_equiv_te] had before short channel writes — on a
    launch with a reader. *)
Lemma wall_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp,
  to_wallexit (run_segments source_segs inp rsp rmb) (Z_to_bv 64 1) bufs code
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) ->
  to_wallexit (run_segments target_segs inp asp amb) (Z_to_bv 64 1) bufs code
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) ->
  bufs_modeled bufs ->
  in_channel_reader inp = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         bufs code inp Hsource Htarget Hbm Hr.
  assert (HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp rlim inp))
    by (apply fd1chan_fdchan, init_model_fd1chan; exact Hr).
  assert (HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp alim inp))
    by (apply fd1chan_fdchan, init_model_fd1chan; exact Hr).
  split.
  { apply no_error_run_modeled.
    apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
             source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
             HfdS Hbm Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
               HfdS Hbm Hsource tr).
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               target_segs apc aph asp abrk amb arnd alim inp bufs code
               HfdT Hbm Htarget tr).
    reflexivity.
  - cbn.
    apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
             target_segs apc aph asp abrk amb arnd alim inp bufs code
             HfdT Hbm Htarget).
Qed.
End WithFP1.
