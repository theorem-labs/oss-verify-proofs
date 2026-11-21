(** * ZReproQ6B — Q6 leg (b): the HEAD arm as one declarative 16-bit read.

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-19).  On the
    wrap-5 (zlib) path with an empty accumulator, a CONTINUING [inf_HEAD]
    step either lands in [M_BAD] (absorbed — a BAD run never returns
    [Z_STREAM_END], so the face's success premise kills it) or consumes
    exactly the two header bytes: [read_bits 16] on the entry stream
    returns the exit stream, the accumulator leaves empty ([INITBITS]),
    and the mode moves to [M_TYPE] or [M_DICTID] (the FDICT arm — also
    absorbed later: [M_DICT] with no dictionary is [InfRet Z_NEED_DICT]).
    The output/return bookkeeping and the window size ride along
    untouched, which the leave-vacuity argument reads at the end.

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

(** The bookkeeping a header step must not touch. *)
Definition zr_q6_frame (q q' : InfSt) : Prop :=
  q_ob q' = q_ob q /\ q_in q' = q_in q /\ q_out q' = q_out q
  /\ q_ret q' = q_ret q
  /\ w_wsize (s_win (q_st q')) = w_wsize (s_win (q_st q)).

(** NEEDBITS adds whole bytes and stops as soon as the floor is met, so
    from a known entry the exit bit count is pinned to a window. *)
Lemma zr_nb_go_bits : forall f n b b',
  inf_nb_go f n b = NBOk b' ->
  br_bits b' = br_bits b
  \/ (br_bits b' < n + 8 /\ exists k, br_bits b' = br_bits b + 8 * k).
Proof.
  induction f as [|f IH]; intros n b b' H; cbn [inf_nb_go] in H.
  - destruct (Z.ltb_spec (br_bits b) n); [discriminate|].
    injection H as <-. auto.
  - destruct (Z.ltb_spec (br_bits b) n).
    + destruct (br_pullbyte b) as [b1|] eqn:EP; [|discriminate].
      pose proof (br_pullbyte_step _ _ EP) as (_ & _ & Hb8 & _).
      destruct (IH n b1 b' H) as [HE | (Hlt & k & Hk)].
      * right. split; [lia|]. exists 1. lia.
      * right. split; [lia|]. exists (k + 1). lia.
    + injection H as <-. auto.
Qed.

Lemma zr_nb_bits : forall n b b',
  inf_nb n b = NBOk b' ->
  br_bits b' = br_bits b
  \/ (br_bits b' < n + 8 /\ exists k, br_bits b' = br_bits b + 8 * k).
Proof. intros n b b' H. exact (zr_nb_go_bits (Z.to_nat n) n b b' H). Qed.

Lemma zr_head_sound : forall c q q',
  h_wrap (s_hdr (q_st q)) = 5 ->
  br_wf (q_br q) ->
  br_bits (q_br q) = 0 ->
  inf_HEAD c q = InfCont q' ->
  h_mode (s_hdr (q_st q')) = M_BAD
  \/ (exists v,
        read_bits 16%nat (br_stream (q_br q)) = Some (v, br_stream (q_br q'))
        /\ br_wf (q_br q')
        /\ br_bits (q_br q') = 0
        /\ (h_mode (s_hdr (q_st q')) = M_TYPE
            \/ h_mode (s_hdr (q_st q')) = M_DICTID)
        /\ zr_q6_frame q q').
Proof.
  intros c q q' Hw Hwf Hb0 H.
  unfold inf_HEAD in H. cbv zeta in H.
  rewrite Hw in H.
  (* wrap 5: not raw *)
  change (5 =? 0) with false in H.
  (* NEEDBITS(16) *)
  destruct (inf_nb 16 (q_br q)) as [b1|] eqn:EN; [|discriminate].
  destruct (inf_nb_ok 16 (q_br q) b1 Hwf ltac:(lia) EN)
    as (ES & Hwf1 & Hb16).
  (* wrap 5 has bit 2 clear: the gzip-magic branch is dead *)
  change (Z.land 5 2) with 0 in H.
  change (negb (0 =? 0)) with false in H.
  cbn [andb] in H.
  (* the header-check disjunction: wrap bit 1 is set *)
  change (Z.land 5 1) with 1 in H.
  change (1 =? 0) with false in H.
  cbn [orb] in H.
  destruct (negb ((Z.shiftl (br_bits_of 8 b1) 8 + Z.shiftr (br_hold b1) 8)
                   mod 31 =? 0)) eqn:ECHK.
  { (* bad header check: q' is qbad *)
    injection H as <-. left. reflexivity. }
  destruct (negb (br_bits_of 4 b1 =? Z_DEFLATED)) eqn:ECM.
  { injection H as <-. left. reflexivity. }
  cbv zeta in H.
  destruct (Z.ltb 15 (br_bits_of 4 (br_dropbits 4 b1) + 8)
            || Z.ltb (w_wbits (s_win _))
                     (br_bits_of 4 (br_dropbits 4 b1) + 8)) eqn:EWB.
  { injection H as <-. left. reflexivity. }
  (* the good path: M_TYPE / M_DICTID via FDICT *)
  injection H as <-. right.
  (* NEEDBITS from an empty accumulator stops at exactly 16 bits *)
  assert (Hb1 : br_bits b1 = 16).
  { destruct (zr_nb_bits 16 (q_br q) b1 EN) as [HE | (Hlt & k & Hk)]; lia. }
  exists (br_hold b1).
  split; [|split; [|split; [|split]]].
  - (* the 16-bit read *)
    rewrite <- ES.
    unfold br_stream at 1. rewrite Hb1.
    destruct Hwf1 as (Hw1 & Hh1 & Hv1 & Hr1).
    rewrite Z.shiftl_1_l, Hb1 in Hh1.
    unfold zwrite at 1. change (Z.to_nat 16) with 16%nat.
    rewrite read_bits_write_bits by exact Hh1.
    (* the exit stream is convertible: INITBITS zeroes the accumulator
       (zwrite 0 0 = []) and neither DROPBITS nor INITBITS touches the
       byte tail *)
    reflexivity.
  - (* wf of the exit reader *)
    destruct Hwf1 as (Hw1 & Hh1 & Hv1 & Hr1).
    unfold qset_br, qmode, qcheck, qset_st; cbn [q_br].
    unfold br_initbits, br_dropbits, br_wf;
      cbn [br_bits br_hold br_have br_in].
    rewrite Z.shiftl_1_l.
    repeat split; try lia;
      try (match goal with |- context [br_in b1 ?k] =>
             specialize (Hr1 k); lia end).
  - reflexivity.
  - (* mode: FDICT chooses *)
    match goal with |- context [if ?t then M_TYPE else M_DICTID] =>
      destruct t end; [left | right]; reflexivity.
  - (* frame *)
    unfold zr_q6_frame.
    match goal with |- context [if ?t then M_TYPE else M_DICTID] =>
      destruct t end;
      match goal with |- context [if ?t then set_wbits _ _ else _] =>
        destruct t end;
      repeat split; reflexivity.
Qed.

Print Assumptions zr_head_sound.
