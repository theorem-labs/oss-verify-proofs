(** * Q6AsmSupport — walk-independent plumbing for the face assemblies.

    OWNER: q6-fixedtbl lane (zlib z-repro campaign, 2026-08-20; TL
    assembly-pre-draft assignment).  Everything here is independent of
    the body walk's statement: loop composition and uniqueness, the
    initial reader's byte/stream/wf facts, and the FINISH-flush leave
    lemma (the L0C [zr_leave_done] generalized past its [q_out = o_left]
    premise — at [M_DONE]+[Z_FINISH]+[wsize 0] the window-update guard is
    false REGARDLESS of [wrote]: [m_val M_DONE < m_val M_BAD] holds but
    [< m_val M_CHECK] fails and the flush disjunct dies, so raw/gzip
    tails that never fold [q_out] still leave clean).

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6A.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Loop plumbing beyond L0C's: composition and uniqueness.
   ========================================================================== *)

Lemma zr_iterloop_compose : forall k c q q' n s,
  inf_iter k c q = Some q' ->
  inf_loop n c q' = Some s ->
  inf_loop (k + n) c q = Some s.
Proof.
  induction k as [|k IH]; intros c q q' n s HI HL.
  - cbn [inf_iter] in HI. injection HI as <-. exact HL.
  - cbn [inf_iter] in HI. cbn [Nat.add inf_loop].
    destruct (inf_step c q) as [q1| | | |] eqn:E; try discriminate.
    exact (IH c q1 q' n s HI HL).
Qed.

Lemma zr_loop_uniq : forall n m c q s s',
  inf_loop n c q = Some s ->
  inf_loop m c q = Some s' ->
  s = s'.
Proof.
  induction n as [|n IH]; intros m c q s s' H H'; [discriminate|].
  destruct m as [|m]; [discriminate|].
  cbn [inf_loop] in H, H'.
  destruct (inf_step c q) as [q1| | | |] eqn:E;
    try (congruence).
  exact (IH m c q1 s s' H H').
Qed.

(* ==========================================================================
   2.  The initial reader: bytes, stream, well-formedness.
   ========================================================================== *)

Lemma zr_map_nth_seq : forall (l : list Z) (d : Z),
  map (fun k => nth k l d) (seq 0 (length l)) = l.
Proof.
  induction l as [|a l IH]; intros d; [reflexivity|].
  cbn [length seq map nth].
  f_equal.
  rewrite <- seq_shift, map_map.
  exact (IH d).
Qed.

(** [br_bytes] of a reader positioned [zlen pre] into [pre ++ rest] is
    [rest] — covers raw (pre = []) and gzip (pre = the 10-byte header). *)
Lemma zr_br_bytes_at : forall pre rest h b,
  br_bytes {| br_in := zlist (pre ++ rest); br_have := zlen rest;
              br_next := zlen pre; br_hold := h; br_bits := b |} = rest.
Proof.
  intros pre rest h b.
  unfold br_bytes. cbn [br_in br_next br_have].
  unfold zlen. rewrite Nat2Z.id.
  erewrite map_ext_in.
  2:{ intros k Hk. apply in_seq in Hk.
      unfold zlist.
      replace (Z.to_nat (Z.of_nat (length pre) + Z.of_nat k))
        with (length pre + k)%nat by lia.
      rewrite app_nth2 by lia.
      replace (length pre + k - length pre)%nat with k by lia.
      reflexivity. }
  apply zr_map_nth_seq.
Qed.

(** At [bits = 0] the stream view is exactly the remaining bytes' bits,
    whatever junk sits in [hold] ([zwrite 0 _ = []]). *)
Lemma zr_br_stream_at : forall pre rest h,
  br_stream {| br_in := zlist (pre ++ rest); br_have := zlen rest;
               br_next := zlen pre; br_hold := h; br_bits := 0 |}
  = bytes_bits rest.
Proof.
  intros pre rest h.
  unfold br_stream. cbn [br_bits br_hold].
  rewrite zr_br_bytes_at.
  reflexivity.
Qed.

(** Initial-reader well-formedness from the face's byte premise. *)
Lemma zr_init_brwf : forall enc,
  Forall (fun b => 0 <= b < 256) enc ->
  br_wf {| br_in := zlist enc; br_have := zlen enc;
           br_next := 0; br_hold := 0; br_bits := 0 |}.
Proof.
  intros enc HBy.
  unfold br_wf. cbn [br_bits br_hold br_have br_in].
  refine (conj _ (conj _ (conj _ _))).
  - lia.
  - change (Z.shiftl 1 0) with 1. lia.
  - unfold zlen. lia.
  - intros j. unfold zlist.
    destruct (Nat.lt_ge_cases (Z.to_nat j) (length enc)) as [Hlt|Hge].
    + rewrite Forall_forall in HBy. apply HBy, nth_In, Hlt.
    + rewrite nth_overflow by exact Hge. lia.
Qed.

(* ==========================================================================
   3.  The FINISH-flush leave: [zr_leave_done] without [q_out = o_left].
   ========================================================================== *)

Lemma zr_leave_done_fin : forall c q',
  n_flush c = Z_FINISH ->
  q_ret q' = Z_STREAM_END ->
  h_mode (s_hdr (q_st q')) = M_DONE ->
  w_wsize (s_win (q_st q')) = 0 ->
  snd (inf_leave c q') = Z_STREAM_END
  /\ q_ob (fst (inf_leave c q')) = q_ob q'.
Proof.
  intros c q' Hfl Hret Hmode Hw.
  unfold inf_leave. cbv zeta.
  replace (w_wsize (s_win (q_st (q_restore q'))))
    with (w_wsize (s_win (q_st q'))) by reflexivity.
  rewrite Hw.
  replace (0 =? 0) with true by reflexivity.
  cbn [negb].
  replace (h_mode (s_hdr (q_st (q_restore q'))))
    with (h_mode (s_hdr (q_st q'))) by reflexivity.
  rewrite Hmode.
  replace (m_val M_DONE <? m_val M_CHECK) with false by reflexivity.
  rewrite Hfl.
  replace (Z_FINISH =? Z_FINISH) with true by reflexivity.
  cbn [negb orb andb].
  rewrite ?andb_false_r.
  cbv beta iota.
  unfold inf_leave_tail. cbv zeta.
  lazy [qset_ret qset_out qset_in qset_st qcheck
        q_st q_z q_br q_ob q_in q_out q_ret fst snd].
  match goal with
  | |- context [if ?t then qset_z _ _ else _] => destruct t
  end.
  all: unfold qset_ret, qset_out, qset_in, qset_z, qset_st;
       cbn [q_st q_z q_br q_ob q_in q_out q_ret fst snd].
  all: replace (q_ret (q_restore q')) with (q_ret q') by reflexivity.
  all: rewrite Hret.
  all: replace (Z_STREAM_END =? Z_OK) with false by reflexivity.
  all: rewrite ?andb_false_r.
  all: cbv iota.
  all: cbn [q_ret q_ob fst snd].
  all: split; reflexivity.
Qed.

(** The absorber's half: a non-STREAM_END ret survives the leave — every
    exit path returns MEM/BUF or the state's own ret. *)
Lemma zr_leave_ret_ne : forall c q,
  q_ret q <> Z_STREAM_END ->
  snd (inf_leave c q) <> Z_STREAM_END.
Proof.
  intros c q Hne.
  unfold inf_leave. cbv zeta.
  match goal with |- context [if ?t then _ else _] => destruct t end.
  - destruct (uw (n_walloc c) (n_wfresh c) (q_st (q_restore q))
                 (q_ob (q_restore q))
                 (q_out (q_restore q) - o_left (q_ob (q_restore q))))
      as [st'|].
    + unfold inf_leave_tail. cbv zeta.
      lazy [qset_ret qset_out qset_in qset_z qset_st qcheck
            q_st q_z q_br q_ob q_in q_out q_ret fst snd].
      match goal with |- context [if ?t then Z_BUF_ERROR else _] =>
        destruct t end.
      * unfold Z_BUF_ERROR, Z_STREAM_END. lia.
      * match goal with |- context [if ?t then _ else _] => destruct t end;
          cbn [q_ret];
          replace (q_ret (q_restore q)) with (q_ret q) by reflexivity;
          exact Hne.
    + cbn [snd]. unfold Z_MEM_ERROR, Z_STREAM_END. lia.
  - unfold inf_leave_tail. cbv zeta.
    lazy [qset_ret qset_out qset_in qset_z qset_st qcheck
          q_st q_z q_br q_ob q_in q_out q_ret fst snd].
    match goal with |- context [if ?t then Z_BUF_ERROR else _] =>
      destruct t end.
    + unfold Z_BUF_ERROR, Z_STREAM_END. lia.
    + match goal with |- context [if ?t then _ else _] => destruct t end;
        cbn [q_ret];
        replace (q_ret (q_restore q)) with (q_ret q) by reflexivity;
        exact Hne.
Qed.

Print Assumptions zr_iterloop_compose.
Print Assumptions zr_loop_uniq.
Print Assumptions zr_br_bytes_at.
Print Assumptions zr_br_stream_at.
Print Assumptions zr_init_brwf.
Print Assumptions zr_leave_done_fin.
Print Assumptions zr_leave_ret_ne.

(* ==========================================================================
   4.  Amendment #10 entry discharges: reader alignment + input budget at
       the fresh reader (all three face assemblies enter at bits = 0).
   ========================================================================== *)

From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(** Reader alignment is vacuous at [bits = 0] (empty byte range) — the
    entry discharge for all three face assemblies. *)
Lemma zr_haligned_bits0 : forall b,
  br_bits b = 0 -> W2Stream.br_haligned b.
Proof.
  intros b Hb.
  unfold W2Stream.br_haligned.
  intros j [H1 H2].
  exfalso.
  rewrite Hb in H2.
  change (0 / 8) with 0 in H2.
  lia.
Qed.

(** The compositional input budget at the fresh reader: [bits = 0]
    collapses it to the face's [zlen] premise. *)
Lemma zr_init_budget : forall enc,
  zlen enc <= 4294967290 ->
  br_have {| br_in := zlist enc; br_have := zlen enc; br_next := 0;
             br_hold := 0; br_bits := 0 |}
  + br_bits {| br_in := zlist enc; br_have := zlen enc; br_next := 0;
               br_hold := 0; br_bits := 0 |} / 8 <= 4294967290.
Proof.
  intros enc H.
  cbn [br_have br_bits].
  change (0 / 8) with 0.
  lia.
Qed.

Print Assumptions zr_haligned_bits0.
Print Assumptions zr_init_budget.
