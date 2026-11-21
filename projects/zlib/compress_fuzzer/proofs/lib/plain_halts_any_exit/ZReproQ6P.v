(** * ZReproQ6P — the slow-path symbol trip (LEN-chain layer 2b, stages).

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-20).

    [inf_LEN]'s slow branch falls through LENEXT -> DIST -> DISTEXT ->
    MATCH inside ONE [inf_step], mirroring the C switch.  Each stage
    below analyzes one fallthrough node into starvation-leave vs
    progress, expressing the successor state by PROJECTIONS (never by
    its syntax) so the stages chain without tower blowup.  The trip
    composition and the symbol loop sit on top.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6I ZReproQ6N.
(* Bridge-vocabulary files: Require WITHOUT Import (they define their own
   [br_stream], a duplicate of ZReproQ6A's — see the Q6M header note). *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require DecodeBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZReproQ6M.
(* amendment window 2 (q7-decode per TL grant 2026-08-20; owner review
   trails): the br_haligned preservation toolkit + qualified W2Stream. *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtBrAlign.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The bookkeeping a fallthrough stage must not touch: the output
    record, the entry snapshots, the return code, the table arena
    (which [tbl_of] reads exclusively — [tbl_of_stable]), the window
    record, and the header scalars other than the mode. *)
Definition zr_sframe (q q' : InfSt) : Prop :=
  q_ob q' = q_ob q /\ q_ret q' = q_ret q
  /\ q_in q' = q_in q /\ q_out q' = q_out q
  /\ s_tab (q_st q') = s_tab (q_st q)
  /\ s_win (q_st q') = s_win (q_st q)
  /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
  /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
  (* amendment #10 (q7-decode as TL-confirmed carrier, 2026-08-20): the
     flags clause rides the stage frame — writer census INBOX-0603, no
     step-loop writer; every construction site closes it by the same
     reflexivity that closes h_wrap. *)
  /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
  (* amendment #11: h_check/h_total frame conjuncts — carrier q7-decode;
     g1 census; q6 pre-ruling; #10 shape *)
  /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
  /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q)).

Lemma tbl_of_stable : forall s s' r,
  s_tab s' = s_tab s -> tbl_of s' r = tbl_of s r.
Proof.
  intros s s' r H. destruct r; try reflexivity.
  unfold tbl_of. rewrite H. reflexivity.
Qed.

(* ==========================================================================
   1.  The LENEXT stage: the length extra bits.
   ========================================================================== *)

Lemma zr_lenext_split : forall q,
  br_wf (q_br q) ->
  0 <= u_extra (s_cur (q_st q)) <= 13 ->
  (exists b2, inf_LENEXT q = InfLeave (qset_br q b2))
  \/ (exists qD v,
        inf_LENEXT q = inf_DIST qD
        /\ read_bits (Z.to_nat (u_extra (s_cur (q_st q))))
             (br_stream (q_br q))
           = Some (v, br_stream (q_br qD))
        /\ 0 <= v < 2 ^ u_extra (s_cur (q_st q))
        /\ u_length (s_cur (q_st qD)) = u_length (s_cur (q_st q)) + v
        /\ br_wf (q_br qD)
        /\ (W2Stream.br_haligned (q_br q) -> W2Stream.br_haligned (q_br qD))
        /\ zr_sframe q qD).
Proof.
  intros q Hwf He.
  unfold inf_LENEXT. cbv zeta.
  destruct (Z.eqb_spec (u_extra (s_cur (q_st q))) 0) as [E0|N0].
  - (* no extra field *)
    right. cbv beta iota.
    eexists. exists 0.
    split; [reflexivity|].
    rewrite E0. change (Z.to_nat 0) with 0%nat. cbn [read_bits].
    split; [reflexivity|].
    split. { change (2 ^ 0) with 1. lia. }
    split. { rewrite Z.add_0_r. reflexivity. }
    split; [exact Hwf|].
    split. { intro Hal. exact Hal. }
    repeat split; reflexivity.
  - (* NEEDBITS(extra), then drop *)
    destruct (inf_nb (u_extra (s_cur (q_st q))) (q_br q)) as [b|b] eqn:EN;
      cbv beta iota.
    + right.
      destruct (inf_nb_ok (u_extra (s_cur (q_st q))) (q_br q) b
                  Hwf ltac:(lia) EN) as (ES & Hwfb & Hble).
      eexists. exists (br_bits_of (u_extra (s_cur (q_st q))) b).
      split; [reflexivity|].
      split.
      { rewrite <- ES.
        exact (br_read_agree (u_extra (s_cur (q_st q))) b Hwfb
                 ltac:(lia)). }
      split.
      { exact (DecodeBridge.br_bits_of_in_range
                 (u_extra (s_cur (q_st q))) b ltac:(lia)). }
      split. { reflexivity. }
      split.
      { apply br_wf_dropbits; [exact Hwfb | lia]. }
      split.
      { intro Hal.
        cbn [q_br qmode qset_br qset_st].
        apply br_haligned_dropbits; [lia|].
        refine (inf_nb_align _ _ _ Hwf _ EN Hal); lia. }
      repeat split; reflexivity.
    + left. eexists. reflexivity.
Qed.

(* ==========================================================================
   2.  The DISTEXT stage: the distance extra bits.
   ========================================================================== *)

Lemma zr_distext_split : forall q,
  br_wf (q_br q) ->
  0 <= u_extra (s_cur (q_st q)) <= 13 ->
  (exists b2, inf_DISTEXT q = InfLeave (qset_br q b2))
  \/ (exists qM v,
        inf_DISTEXT q = inf_MATCH qM
        /\ read_bits (Z.to_nat (u_extra (s_cur (q_st q))))
             (br_stream (q_br q))
           = Some (v, br_stream (q_br qM))
        /\ 0 <= v < 2 ^ u_extra (s_cur (q_st q))
        /\ u_offset (s_cur (q_st qM)) = u_offset (s_cur (q_st q)) + v
        /\ u_length (s_cur (q_st qM)) = u_length (s_cur (q_st q))
        /\ h_mode (s_hdr (q_st qM)) = M_MATCH
        /\ br_wf (q_br qM)
        /\ (W2Stream.br_haligned (q_br q) -> W2Stream.br_haligned (q_br qM))
        /\ zr_sframe q qM).
Proof.
  intros q Hwf He.
  unfold inf_DISTEXT. cbv zeta.
  destruct (Z.eqb_spec (u_extra (s_cur (q_st q))) 0) as [E0|N0].
  - right. cbv beta iota.
    eexists. exists 0.
    split; [reflexivity|].
    rewrite E0. change (Z.to_nat 0) with 0%nat. cbn [read_bits].
    split; [reflexivity|].
    split. { change (2 ^ 0) with 1. lia. }
    split. { rewrite Z.add_0_r. reflexivity. }
    split. { reflexivity. }
    split. { reflexivity. }
    split; [exact Hwf|].
    split. { intro Hal. exact Hal. }
    repeat split; reflexivity.
  - destruct (inf_nb (u_extra (s_cur (q_st q))) (q_br q)) as [b|b] eqn:EN;
      cbv beta iota.
    + right.
      destruct (inf_nb_ok (u_extra (s_cur (q_st q))) (q_br q) b
                  Hwf ltac:(lia) EN) as (ES & Hwfb & Hble).
      eexists. exists (br_bits_of (u_extra (s_cur (q_st q))) b).
      split; [reflexivity|].
      split.
      { rewrite <- ES.
        exact (br_read_agree (u_extra (s_cur (q_st q))) b Hwfb
                 ltac:(lia)). }
      split.
      { exact (DecodeBridge.br_bits_of_in_range
                 (u_extra (s_cur (q_st q))) b ltac:(lia)). }
      split. { reflexivity. }
      split. { reflexivity. }
      split. { reflexivity. }
      split.
      { apply br_wf_dropbits; [exact Hwfb | lia]. }
      split.
      { intro Hal.
        cbn [q_br qmode qset_br qset_st].
        apply br_haligned_dropbits; [lia|].
        refine (inf_nb_align _ _ _ Hwf _ EN Hal); lia. }
      repeat split; reflexivity.
    + left. eexists. reflexivity.
Qed.

(* ==========================================================================
   3.  Vocabulary bridge, and the DIST stage.
   ========================================================================== *)

Lemma zr_stream_eq : forall b, ZBitsBridge.br_stream b = br_stream b.
Proof. intro b. reflexivity. Qed.

Lemma zr_dist_split : forall q (dl : list nat) (entd : nat -> Code),
  br_wf (q_br q) ->
  ValidLengths dl 15%nat ->
  ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
      (t_distbits (s_tab (q_st q))) dl 15%nat entd ->
  0 < t_distbits (s_tab (q_st q)) <= 15 ->
  (forall sym cw, code_for dl 15%nat sym = Some cw ->
       sub_dist (entd sym) = false) ->
  inf_DIST q = InfFuel
  \/ (exists q2, inf_DIST q = InfLeave q2 /\ q_ret q2 = q_ret q)
  \/ (exists qb, inf_DIST q = InfCont qb
        /\ h_mode (s_hdr (q_st qb)) = M_BAD)
  \/ (exists qX dsym cw,
        inf_DIST q = inf_DISTEXT qX
        /\ code_for dl 15%nat dsym = Some cw
        /\ hdecode (code_table dl 15%nat) (br_stream (q_br q))
           = Some (dsym, br_stream (q_br qX))
        /\ u_offset (s_cur (q_st qX)) = c_val (entd dsym)
        /\ u_extra (s_cur (q_st qX)) = Z.land (c_op (entd dsym)) 15
        /\ u_length (s_cur (q_st qX)) = u_length (s_cur (q_st q))
        /\ Z.land (c_op (entd dsym)) 64 = 0
        /\ br_wf (q_br qX)
        /\ (W2Stream.br_haligned (q_br q) -> W2Stream.br_haligned (q_br qX))
        /\ zr_sframe q qX).
Proof.
  intros q dl entd Hwf HV Hown Hrb Hsub.
  unfold inf_DIST. cbv zeta.
  pose proof (ZReproQ6M.zr_decode_hdecode_root sub_dist
       (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
       (t_distbits (s_tab (q_st q))) dl 15%nat entd (q_br q)
       Hrb HV Hown Hsub Hwf) as HD.
  destruct (inf_decode sub_dist
              (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
              (t_distbits (s_tab (q_st q))) (q_br q))
    as [h b' nb|b'|] eqn:ED; cbv beta iota.
  - destruct HD as (dsym & cw & C1 & C2 & C3 & C4 & C5 & C6).
    rewrite !zr_stream_eq in C6.
    destruct (Z.eqb_spec (Z.land (c_op h) 64) 0) as [E64|N64];
      cbn [negb]; cbv beta iota.
    + (* progress into DISTEXT *)
      right; right; right.
      eexists. exists dsym, cw.
      split; [reflexivity|].
      split; [exact C1|].
      split; [exact C6|].
      split. { rewrite <- C2. reflexivity. }
      split. { rewrite <- C2. reflexivity. }
      split. { reflexivity. }
      split. { rewrite <- C2. exact E64. }
      split; [exact C5|].
      split.
      { intro Hal.
        exact (zr_decode_align sub_dist _ _ _ _ _ _ Hwf Hrb
                 (zr_own_cbits _ _ _ _ _ Hown)
                 (zr_own_sub sub_dist _ _ _ _ _ Hown Hsub) ED Hal). }
      repeat split; reflexivity.
    + (* invalid distance code *)
      right; right; left.
      eexists. split; [reflexivity | reflexivity].
  - right; left. eexists. split; [reflexivity | reflexivity].
  - left. reflexivity.
Qed.

(* ==========================================================================
   4.  The LEN dispatch stage (slow branch).
   ========================================================================== *)

Lemma zr_len_split : forall q (ll : list nat) (entl : nat -> Code),
  br_wf (q_br q) ->
  ValidLengths ll 15%nat ->
  ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
      (t_lenbits (s_tab (q_st q))) ll 15%nat entl ->
  0 < t_lenbits (s_tab (q_st q)) <= 15 ->
  (forall sym cw, code_for ll 15%nat sym = Some cw ->
       sub_len (entl sym) = false) ->
  (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q))) = false ->
  inf_LEN q = InfFuel
  \/ (exists q2, inf_LEN q = InfLeave q2 /\ q_ret q2 = q_ret q)
  \/ (exists qb, inf_LEN q = InfCont qb
        /\ h_mode (s_hdr (q_st qb)) = M_BAD)
  (* literal *)
  \/ (exists qL sym cw,
        inf_LEN q = InfCont qL
        /\ code_for ll 15%nat sym = Some cw
        /\ hdecode (code_table ll 15%nat) (br_stream (q_br q))
           = Some (sym, br_stream (q_br qL))
        /\ c_op (entl sym) = 0
        /\ u_length (s_cur (q_st qL)) = c_val (entl sym)
        /\ h_mode (s_hdr (q_st qL)) = M_LIT
        /\ br_wf (q_br qL)
        /\ (W2Stream.br_haligned (q_br q) -> W2Stream.br_haligned (q_br qL))
        /\ zr_sframe q qL)
  (* end of block *)
  \/ (exists qT sym cw,
        inf_LEN q = InfCont qT
        /\ code_for ll 15%nat sym = Some cw
        /\ hdecode (code_table ll 15%nat) (br_stream (q_br q))
           = Some (sym, br_stream (q_br qT))
        /\ c_op (entl sym) <> 0
        /\ Z.land (c_op (entl sym)) 32 <> 0
        /\ h_mode (s_hdr (q_st qT)) = M_TYPE
        /\ br_wf (q_br qT)
        /\ (W2Stream.br_haligned (q_br q) -> W2Stream.br_haligned (q_br qT))
        /\ zr_sframe q qT)
  (* length code: fall through to LENEXT *)
  \/ (exists qE sym cw,
        inf_LEN q = inf_LENEXT qE
        /\ code_for ll 15%nat sym = Some cw
        /\ hdecode (code_table ll 15%nat) (br_stream (q_br q))
           = Some (sym, br_stream (q_br qE))
        /\ c_op (entl sym) <> 0
        /\ Z.land (c_op (entl sym)) 32 = 0
        /\ Z.land (c_op (entl sym)) 64 = 0
        /\ u_length (s_cur (q_st qE)) = c_val (entl sym)
        /\ u_extra (s_cur (q_st qE)) = Z.land (c_op (entl sym)) 15
        /\ br_wf (q_br qE)
        /\ (W2Stream.br_haligned (q_br q) -> W2Stream.br_haligned (q_br qE))
        /\ zr_sframe q qE).
Proof.
  intros q ll entl Hwf HV Hown Hrb Hsub Hg.
  unfold inf_LEN. cbv zeta.
  rewrite Hg. cbv beta iota.
  pose proof (ZReproQ6M.zr_decode_hdecode_root sub_len
       (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
       (t_lenbits (s_tab (q_st q))) ll 15%nat entl (q_br q)
       Hrb HV Hown Hsub Hwf) as HD.
  destruct (inf_decode sub_len
              (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
              (t_lenbits (s_tab (q_st q))) (q_br q))
    as [h b' nb|b'|] eqn:ED; cbv beta iota.
  - destruct HD as (sym & cw & C1 & C2 & C3 & C4 & C5 & C6).
    rewrite !zr_stream_eq in C6.
    destruct (Z.eqb_spec (c_op h) 0) as [E0|N0]; cbv beta iota.
    + (* literal *)
      right; right; right; left.
      eexists. exists sym, cw.
      split; [reflexivity|].
      split; [exact C1|].
      split; [exact C6|].
      split. { rewrite <- C2. exact E0. }
      split. { rewrite <- C2. reflexivity. }
      split. { reflexivity. }
      split; [exact C5|].
      split.
      { intro Hal.
        exact (zr_decode_align sub_len _ _ _ _ _ _ Hwf Hrb
                 (zr_own_cbits _ _ _ _ _ Hown)
                 (zr_own_sub sub_len _ _ _ _ _ Hown Hsub) ED Hal). }
      repeat split; reflexivity.
    + destruct (Z.eqb_spec (Z.land (c_op h) 32) 0) as [E32|N32];
        cbn [negb]; cbv beta iota.
      * destruct (Z.eqb_spec (Z.land (c_op h) 64) 0) as [E64|N64];
          cbn [negb]; cbv beta iota.
        -- (* length code: fall through *)
           right; right; right; right; right.
           eexists. exists sym, cw.
           split; [reflexivity|].
           split; [exact C1|].
           split; [exact C6|].
           split. { rewrite <- C2. exact N0. }
           split. { rewrite <- C2. exact E32. }
           split. { rewrite <- C2. exact E64. }
           split. { rewrite <- C2. reflexivity. }
           split. { rewrite <- C2. reflexivity. }
           split; [exact C5|].
           split.
           { intro Hal.
             exact (zr_decode_align sub_len _ _ _ _ _ _ Hwf Hrb
                      (zr_own_cbits _ _ _ _ _ Hown)
                      (zr_own_sub sub_len _ _ _ _ _ Hown Hsub) ED Hal). }
           repeat split; reflexivity.
        -- (* invalid literal/length code *)
           right; right; left.
           eexists. split; [reflexivity | reflexivity].
      * (* end of block *)
        right; right; right; right; left.
        eexists. exists sym, cw.
        split; [reflexivity|].
        split; [exact C1|].
        split; [exact C6|].
        split. { rewrite <- C2. exact N0. }
        split. { rewrite <- C2. exact N32. }
        split. { reflexivity. }
        split; [exact C5|].
        split.
        { intro Hal.
          exact (zr_decode_align sub_len _ _ _ _ _ _ Hwf Hrb
                   (zr_own_cbits _ _ _ _ _ Hown)
                   (zr_own_sub sub_len _ _ _ _ _ Hown Hsub) ED Hal). }
        repeat split; reflexivity.
  - right; left. eexists. split; [reflexivity | reflexivity].
  - left. reflexivity.
Qed.

(* ==========================================================================
   5.  The LIT stage: one literal byte.
   ========================================================================== *)

Lemma zr_ob_write_slice : forall o v,
  0 <= o_put o ->
  ob_slice (ob_write o v) 0 (o_put o + 1)
  = ob_slice o 0 (o_put o) ++ [v].
Proof.
  intros o v Hp.
  unfold ob_slice, ob_write. cbn [o_buf o_put].
  replace (Z.to_nat (o_put o + 1)) with (Z.to_nat (o_put o) + 1)%nat
    by lia.
  rewrite seq_app, map_app.
  f_equal.
  - apply map_ext_in. intros m Hm. apply in_seq in Hm.
    unfold zset.
    rewrite (proj2 (Z.eqb_neq (0 + Z.of_nat m) (o_put o)) ltac:(lia)).
    reflexivity.
  - cbn [seq map].
    f_equal. unfold zset.
    match goal with
    | |- (if ?x =? ?y then _ else _) = _ =>
        rewrite (proj2 (Z.eqb_eq x y) ltac:(lia))
    end.
    reflexivity.
Qed.

Lemma zr_lit_split : forall q,
  0 <= o_put (q_ob q) ->
  0 <= u_length (s_cur (q_st q)) < 256 ->
  (o_left (q_ob q) = 0 /\ inf_LIT q = InfLeave q)
  \/ (exists qL,
        inf_LIT q = InfCont qL
        /\ ob_slice (q_ob qL) 0 (o_put (q_ob qL))
           = ob_slice (q_ob q) 0 (o_put (q_ob q))
             ++ [u_length (s_cur (q_st q))]
        /\ o_put (q_ob qL) = o_put (q_ob q) + 1
        /\ o_left (q_ob qL) = o_left (q_ob q) - 1
        /\ h_mode (s_hdr (q_st qL)) = M_LEN
        /\ q_br qL = q_br q
        /\ q_ret qL = q_ret q /\ q_in qL = q_in q /\ q_out qL = q_out q
        /\ s_tab (q_st qL) = s_tab (q_st q)
        /\ s_win (q_st qL) = s_win (q_st q)
        /\ h_last (s_hdr (q_st qL)) = h_last (s_hdr (q_st q))
        /\ h_wrap (s_hdr (q_st qL)) = h_wrap (s_hdr (q_st q))
        /\ h_flags (s_hdr (q_st qL)) = h_flags (s_hdr (q_st q))
        (* amendment #11: h_check/h_total frame conjuncts — carrier
           q7-decode; g1 census; q6 pre-ruling;
           #10 shape *)
        /\ h_check (s_hdr (q_st qL)) = h_check (s_hdr (q_st q))
        /\ h_total (s_hdr (q_st qL)) = h_total (s_hdr (q_st q))).
Proof.
  intros q Hp Hv.
  unfold inf_LIT. cbv zeta.
  destruct (Z.eqb_spec (o_left (q_ob q)) 0) as [E0|N0].
  - left. split; [exact E0 | reflexivity].
  - right.
    eexists.
    split; [reflexivity|].
    cbn [q_ob q_st qset_ob qmode qset_st].
    split.
    { cbn [q_ob].
      replace (u8 (u_length (s_cur (q_st q))))
        with (u_length (s_cur (q_st q)))
        by (unfold u8; rewrite Z.mod_small by lia; reflexivity).
      change (o_put (ob_write (q_ob q) (u_length (s_cur (q_st q)))))
        with (o_put (q_ob q) + 1).
      apply zr_ob_write_slice. exact Hp. }
    repeat split; reflexivity.
Qed.

(* ==========================================================================
   6.  The entry-interpretation packs (instantiated by Q6F reflection at
       the fixed tables; by the keystone layer at built tables), and THE
       SYMBOL TRIP.
   ========================================================================== *)

(* retained per fleet retention convention; superseded by amendment
   window 2 (q7-decode per TL grant 2026-08-20; owner review trails). *)
Definition zr_len_ents_pre_amend2 (ll : list nat) (entl : nat -> Code) : Prop :=
  forall sym cw, code_for ll 15%nat sym = Some cw ->
    ((sym < 256)%nat /\ c_op (entl sym) = 0
       /\ c_val (entl sym) = Z.of_nat sym)
    \/ (sym = 256%nat /\ c_op (entl sym) <> 0
        /\ Z.land (c_op (entl sym)) 32 <> 0)
    \/ ((257 <= sym)%nat
        /\ exists b0 e0,
             nth_error length_base (sym - 257)%nat = Some b0
             /\ nth_error length_extra (sym - 257)%nat = Some e0
             /\ c_op (entl sym) = 16 + Z.of_nat e0
             /\ Z.land (c_op (entl sym)) 32 = 0
             /\ Z.land (c_op (entl sym)) 64 = 0
             /\ Z.land (c_op (entl sym)) 15 = Z.of_nat e0
             /\ c_val (entl sym) = Z.of_nat b0
             /\ (b0 <= 258)%nat /\ (e0 <= 5)%nat)
    \/ (c_op (entl sym) <> 0
        /\ Z.land (c_op (entl sym)) 32 = 0
        /\ Z.land (c_op (entl sym)) 64 <> 0).

(* amendment window 2: pins 1 (EOB + op&16=0 + op&64<>0), 2 (LEN-invalid
   + op&16=0), 4 (+ 3<=b0), 6 (+ joint b0+2^e0-1<=258).  Spelling mirrors
   W3Trip.w3_len_ents verbatim so the W-chain re-point is by
   delta-conversion. *)
Definition zr_len_ents (ll : list nat) (entl : nat -> Code) : Prop :=
  forall sym cw, code_for ll 15%nat sym = Some cw ->
    ((sym < 256)%nat /\ c_op (entl sym) = 0
       /\ c_val (entl sym) = Z.of_nat sym)
    \/ (sym = 256%nat /\ c_op (entl sym) <> 0
        /\ Z.land (c_op (entl sym)) 32 <> 0
        /\ Z.land (c_op (entl sym)) 16 = 0
        /\ Z.land (c_op (entl sym)) 64 <> 0)
    \/ ((257 <= sym)%nat
        /\ exists b0 e0,
             nth_error length_base (sym - 257)%nat = Some b0
             /\ nth_error length_extra (sym - 257)%nat = Some e0
             /\ c_op (entl sym) = 16 + Z.of_nat e0
             /\ Z.land (c_op (entl sym)) 32 = 0
             /\ Z.land (c_op (entl sym)) 64 = 0
             /\ Z.land (c_op (entl sym)) 15 = Z.of_nat e0
             /\ c_val (entl sym) = Z.of_nat b0
             /\ (3 <= b0)%nat /\ (b0 <= 258)%nat /\ (e0 <= 5)%nat
             /\ (b0 + 2 ^ e0 - 1 <= 258)%nat)
    \/ (c_op (entl sym) <> 0
        /\ Z.land (c_op (entl sym)) 32 = 0
        /\ Z.land (c_op (entl sym)) 16 = 0
        /\ Z.land (c_op (entl sym)) 64 <> 0).

(* retained per fleet retention convention; superseded by amendment
   window 2. *)
Definition zr_dist_ents_pre_amend2 (dl : list nat) (entd : nat -> Code) : Prop :=
  forall sym cw, code_for dl 15%nat sym = Some cw ->
    (exists b0 e0,
        nth_error dist_base sym = Some b0
        /\ nth_error dist_extra sym = Some e0
        /\ c_op (entd sym) = 16 + Z.of_nat e0
        /\ Z.land (c_op (entd sym)) 64 = 0
        /\ Z.land (c_op (entd sym)) 15 = Z.of_nat e0
        /\ c_val (entd sym) = Z.of_nat b0
        /\ 1 <= Z.of_nat b0 <= 32768 /\ (e0 <= 13)%nat)
    \/ Z.land (c_op (entd sym)) 64 <> 0.

(* amendment window 2: pin 3 (DIST-invalid + op&16=0); mirrors
   W3Trip.w3_dist_ents verbatim. *)
Definition zr_dist_ents (dl : list nat) (entd : nat -> Code) : Prop :=
  forall sym cw, code_for dl 15%nat sym = Some cw ->
    (exists b0 e0,
        nth_error dist_base sym = Some b0
        /\ nth_error dist_extra sym = Some e0
        /\ c_op (entd sym) = 16 + Z.of_nat e0
        /\ Z.land (c_op (entd sym)) 64 = 0
        /\ Z.land (c_op (entd sym)) 15 = Z.of_nat e0
        /\ c_val (entd sym) = Z.of_nat b0
        /\ 1 <= Z.of_nat b0 <= 32768 /\ (e0 <= 13)%nat)
    \/ (Z.land (c_op (entd sym)) 64 <> 0
        /\ Z.land (c_op (entd sym)) 16 = 0).

Lemma zr_sframe_trans : forall a b c,
  zr_sframe a b -> zr_sframe b c -> zr_sframe a c.
Proof.
  intros a b c (A1&A2&A3&A4&A5&A6&A7&A8&A9&A10&A11)
         (B1&B2&B3&B4&B5&B6&B7&B8&B9&B10&B11).
  repeat split; congruence.
Qed.

(** THE per-symbol trip: from a slow [M_LEN] entry, the machine's next
    iterate(s) ARE [decode_lit_len]'s answer — or an absorbed arm. *)
Lemma zr_sym_trip : forall c q (ll dl : list nat) (entl entd : nat -> Code),
  ValidLengths ll 15%nat ->
  ValidLengths dl 15%nat ->
  ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
      (t_lenbits (s_tab (q_st q))) ll 15%nat entl ->
  ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
      (t_distbits (s_tab (q_st q))) dl 15%nat entd ->
  0 < t_lenbits (s_tab (q_st q)) <= 15 ->
  0 < t_distbits (s_tab (q_st q)) <= 15 ->
  (forall sym cw, code_for ll 15%nat sym = Some cw ->
       sub_len (entl sym) = false) ->
  (forall sym cw, code_for dl 15%nat sym = Some cw ->
       sub_dist (entd sym) = false) ->
  zr_len_ents ll entl ->
  zr_dist_ents dl entd ->
  br_wf (q_br q) ->
  0 <= o_put (q_ob q) ->
  0 <= o_left (q_ob q) ->
  q_out q = o_put (q_ob q) + o_left (q_ob q) ->
  q_out q <= 4294967295 ->
  w_whave (s_win (q_st q)) = 0 ->
  t_sane (s_tab (q_st q)) <> 0 ->
  h_mode (s_hdr (q_st q)) = M_LEN ->
  (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q))) = false ->
  (exists k q' sy,
     inf_iter k c q = Some q'
     /\ decode_lit_len ll dl (br_stream (q_br q))
        = Some (sy, br_stream (q_br q'))
     /\ match sy with
        | LzLit v =>
            ob_slice (q_ob q') 0 (o_put (q_ob q'))
            = ob_slice (q_ob q) 0 (o_put (q_ob q)) ++ [v]
            /\ h_mode (s_hdr (q_st q')) = M_LEN
        | LzEnd =>
            q_ob q' = q_ob q
            /\ h_mode (s_hdr (q_st q')) = M_TYPE
        | LzRef len dist =>
            (dist =? 0)%nat = false
            /\ Z.of_nat dist <= o_put (q_ob q)
            /\ ob_slice (q_ob q') 0 (o_put (q_ob q'))
               = ob_slice (q_ob q) 0 (o_put (q_ob q))
                 ++ lz_copy (ob_slice (q_ob q) 0 (o_put (q_ob q)))
                            len dist
            /\ h_mode (s_hdr (q_st q')) = M_LEN
        end
     /\ br_wf (q_br q')
     /\ 0 <= o_put (q_ob q')
     /\ 0 <= o_left (q_ob q')
     /\ o_put (q_ob q') + o_left (q_ob q')
        = o_put (q_ob q) + o_left (q_ob q)
     /\ s_tab (q_st q') = s_tab (q_st q)
     /\ s_win (q_st q') = s_win (q_st q)
     /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
     /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
     /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
     /\ (W2Stream.br_haligned (q_br q) -> W2Stream.br_haligned (q_br q'))
     /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
     (* amendment #11: h_check/h_total frame conjuncts — carrier
        q7-decode; g1 census; q6 pre-ruling;
        #10 shape *)
     /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
     /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q)))
  \/ (exists k q',
      inf_iter k c q = Some q' /\ h_mode (s_hdr (q_st q')) = M_BAD)
  \/ (exists n s,
      inf_loop n c q = Some s
      /\ match s with
         | InfLeave q2 => q_ret q2 = q_ret q
         | InfCont _ => False | InfRet _ _ => False | InfDead _ => False
         | InfFuel => True
         end).
Proof.
  intros c q ll dl entl entd HVl HVd Hownl Hownd Hrbl Hrbd Hsubl Hsubd
         Hentsl Hentsd Hwf Hput Hleft Htie Hcap Hwh Hsn Hm Hg.
  assert (HSTEP : inf_step c q = inf_LEN q) by (apply zr_step_at_len; exact Hm).
  destruct (zr_len_split q ll entl Hwf HVl Hownl Hrbl Hsubl Hg)
    as [ EF
       | [ (q2 & EL & ERet)
         | [ (qb & EB & HMb)
           | [ (qL & sym & cw & EC & Hcf & Hhd & Hop0 & HlenL & HmL
                & HwfL & HhaL & HfrL)
             | [ (qT & sym & cw & EC & Hcf & Hhd & HopN & Hl32 & HmT
                  & HwfT & HhaT & HfrT)
               | (qE & sym & cw & EC & Hcf & Hhd & HopN & Hl32 & Hl64
                  & HlenE & HextE & HwfE & HhaE & HfrE) ] ] ] ] ].
  - (* decode fuel *)
    right; right. exists 1%nat, InfFuel.
    split; [ apply inf_loop_one_exit; [ rewrite HSTEP; exact EF | exact I ]
           | exact I ].
  - (* decode starvation leave *)
    right; right. exists 1%nat, (InfLeave q2).
    split; [ apply inf_loop_one_exit; [ rewrite HSTEP; exact EL | exact I ]
           | exact ERet ].
  - (* invalid lit/len code *)
    right; left. exists 1%nat, qb.
    split; [ apply inf_iter_one; rewrite HSTEP; exact EB | exact HMb ].
  - (* ---- literal ---- *)
    destruct (Hentsl sym cw Hcf)
      as [ (Hs256 & _ & Hval)
         | [ (_ & HopC & _) | [ (_ & (b0 & e0 & _ & _ & HopC & _))
           | (HopC & _ & _) ] ] ];
      try (exfalso; congruence);
      try (exfalso; rewrite Hop0 in HopC; lia).
    destruct HfrL as (HObL & HRetL & HInL & HOutL & HTabL & HWinL
                      & HLastL & HWrapL & HFlagL & HCheckL & HTotalL).
    assert (HI1 : inf_iter 1 c q = Some qL)
      by (apply inf_iter_one; rewrite HSTEP; exact EC).
    assert (HlenLv : 0 <= u_length (s_cur (q_st qL)) < 256)
      by (rewrite HlenL, Hval; lia).
    assert (HSTEP2 : inf_step c qL = inf_LIT qL)
      by (apply zr_step_at_lit; exact HmL).
    destruct (zr_lit_split qL ltac:(rewrite HObL; exact Hput) HlenLv)
      as [ (Elz & ELV) | (qL' & ECw & HSl & HPutw & HLeftw & HMw & HBrw
                          & HRetw & HInw & HOutw & HTabw & HWinw & HLastw
                          & HWrapw & HFlagw & HCheckw & HTotalw) ].
    + (* output full: starve on the LIT step *)
      right; right. exists 2%nat, (InfLeave qL).
      split.
      { apply (inf_loop_after_iter 1 c q qL 1 (InfLeave qL) HI1).
        apply inf_loop_one_exit; [ rewrite HSTEP2; exact ELV | exact I ]. }
      rewrite HRetL. reflexivity.
    + (* the literal byte *)
      left. exists 2%nat, qL', (LzLit (Z.of_nat sym)).
      split.
      { change 2%nat with (1 + 1)%nat.
        rewrite (inf_iter_add 1 1 c q qL HI1).
        apply inf_iter_one. rewrite HSTEP2. exact ECw. }
      split.
      { unfold decode_lit_len. rewrite Hhd. cbv beta iota.
        rewrite (proj2 (Nat.ltb_lt sym 256) Hs256). cbv beta iota.
        rewrite HBrw. reflexivity. }
      split.
      { split.
        - rewrite HSl, HObL, HlenL, Hval. reflexivity.
        - exact HMw. }
      split. { rewrite HBrw. exact HwfL. }
      split. { rewrite HPutw, HObL. lia. }
      split.
      { rewrite HLeftw, HObL.
        destruct (Z.eqb_spec (o_left (q_ob qL)) 0) as [E|N].
        - exfalso. unfold inf_LIT in ECw.
          rewrite (proj2 (Z.eqb_eq _ 0) E) in ECw. discriminate.
        - rewrite HObL in N. lia. }
      split. { rewrite HPutw, HLeftw, HObL. lia. }
      split. { rewrite HTabw. exact HTabL. }
      split. { rewrite HWinw. exact HWinL. }
      split. { rewrite HLastw. exact HLastL. }
      split. { rewrite HWrapw. exact HWrapL. }
      split. { rewrite HRetw. exact HRetL. }
      split. { rewrite HInw. exact HInL. }
      split. { rewrite HOutw. exact HOutL. }
      split. { intro Hal. rewrite HBrw. exact (HhaL Hal). }
      split. { rewrite HFlagw. exact HFlagL. }
      split. { rewrite HCheckw. exact HCheckL. }
      rewrite HTotalw. exact HTotalL.
  - (* ---- end of block ---- *)
    destruct (Hentsl sym cw Hcf)
      as [ (_ & HopC & _)
         | [ (Hs256 & _ & _) | [ (_ & (b0 & e0 & _ & _ & _ & Hl32C & _))
           | (_ & Hl32C & _) ] ] ];
      try (exfalso; congruence).
    destruct HfrT as (HObT & HRetT & HInT & HOutT & HTabT & HWinT
                      & HLastT & HWrapT & HFlagT & HCheckT & HTotalT).
    left. exists 1%nat, qT, LzEnd.
    split.
    { apply inf_iter_one. rewrite HSTEP. exact EC. }
    split.
    { unfold decode_lit_len. rewrite Hhd. cbv beta iota.
      rewrite (proj2 (Nat.ltb_ge sym 256) ltac:(lia)).
      rewrite (proj2 (Nat.eqb_eq sym 256) Hs256). cbv beta iota.
      reflexivity. }
    split. { split; [exact HObT | exact HmT]. }
    split. { exact HwfT. }
    split. { rewrite HObT. exact Hput. }
    split. { rewrite HObT. exact Hleft. }
    split. { rewrite HObT. reflexivity. }
    split. { exact HTabT. }
    split. { exact HWinT. }
    split. { exact HLastT. }
    split. { exact HWrapT. }
    split. { exact HRetT. }
    split. { exact HInT. }
    split. { exact HOutT. }
    split. { intro Hal. exact (HhaT Hal). }
    split. { exact HFlagT. }
    split. { exact HCheckT. }
    exact HTotalT.
  - (* ---- length/distance reference ---- *)
    destruct (Hentsl sym cw Hcf)
      as [ (_ & HopC & _)
         | [ (_ & _ & Hl32C & _) | [ (Hs257 & (b0 & e0 & Hb0 & He0 & HopC
              & _ & _ & Hl15 & Hval & _ & Hb0b & He0b & _))
           | (_ & _ & _ & Hl64C) ] ] ];
      try (exfalso; congruence).
    destruct HfrE as (HObE & HRetE & HInE & HOutE & HTabE & HWinE
                      & HLastE & HWrapE & HFlagE & HCheckE & HTotalE).
    (* stage: LENEXT *)
    assert (HextEv : 0 <= u_extra (s_cur (q_st qE)) <= 13)
      by (rewrite HextE, Hl15; lia).
    destruct (zr_lenext_split qE HwfE HextEv)
      as [ (b2 & ELV)
         | (qD & v1 & ECD & HRd1 & Hv1 & HlenD & HwfD & HhaD & HfrD) ].
    { (* starved on length extra *)
      right; right. exists 1%nat, (InfLeave (qset_br qE b2)).
      split.
      { apply inf_loop_one_exit;
          [ rewrite HSTEP, EC; exact ELV | exact I ]. }
      cbn [q_ret qset_br]. exact HRetE. }
    rewrite HextE, Hl15, Nat2Z.id in HRd1.
    destruct HfrD as (HObD & HRetD & HInD & HOutD & HTabD & HWinD
                      & HLastD & HWrapD & HFlagD & HCheckD & HTotalD).
    (* stage: DIST — transport the table hypotheses to qD *)
    assert (HstD : s_tab (q_st qD) = s_tab (q_st q))
      by (rewrite HTabD; exact HTabE).
    assert (HownDq : ZReproQ6M.zr_root_own
              (tbl_of (q_st qD) (t_distcode (s_tab (q_st qD))))
              (t_distbits (s_tab (q_st qD))) dl 15%nat entd).
    { rewrite HstD, (tbl_of_stable (q_st q) (q_st qD) _ HstD).
      exact Hownd. }
    assert (HrbDq : 0 < t_distbits (s_tab (q_st qD)) <= 15)
      by (rewrite HstD; exact Hrbd).
    destruct (zr_dist_split qD dl entd HwfD HVd HownDq HrbDq Hsubd)
      as [ EFd
         | [ (q2d & ELd & ERetd)
           | [ (qbd & EBd & HMbd)
             | (qX & dsym & cwd & ECX & Hcfd & Hhdd & HoffX & HextX
                & HlenX & Hl64d & HwfX & HhaX & HfrX) ] ] ].
    { (* dist decode fuel *)
      right; right. exists 1%nat, InfFuel.
      split; [ apply inf_loop_one_exit;
               [ rewrite HSTEP, EC, ECD; exact EFd | exact I ]
             | exact I ]. }
    { (* dist decode starvation *)
      right; right. exists 1%nat, (InfLeave q2d).
      split.
      { apply inf_loop_one_exit;
          [ rewrite HSTEP, EC, ECD; exact ELd | exact I ]. }
      rewrite ERetd, HRetD. exact HRetE. }
    { (* invalid distance code *)
      right; left. exists 1%nat, qbd.
      split; [ apply inf_iter_one; rewrite HSTEP, EC, ECD; exact EBd
             | exact HMbd ]. }
    destruct (Hentsd dsym cwd Hcfd)
      as [ (b0d & e0d & Hb0d & He0d & HopCd & _ & Hl15d & Hvald
            & Hb0db & He0db)
         | (Hl64Cd & _) ];
      [ | exfalso; congruence ].
    destruct HfrX as (HObX & HRetX & HInX & HOutX & HTabX & HWinX
                      & HLastX & HWrapX & HFlagX & HCheckX & HTotalX).
    (* stage: DISTEXT *)
    assert (HextXv : 0 <= u_extra (s_cur (q_st qX)) <= 13)
      by (rewrite HextX, Hl15d; lia).
    destruct (zr_distext_split qX HwfX HextXv)
      as [ (b2 & ELX)
         | (qM & v2 & ECM & HRd2 & Hv2 & HoffM & HlenM & HmM & HwfM
            & HhaM & HfrM) ].
    { (* starved on distance extra *)
      right; right. exists 1%nat, (InfLeave (qset_br qX b2)).
      split.
      { apply inf_loop_one_exit;
          [ rewrite HSTEP, EC, ECD, ECX; exact ELX | exact I ]. }
      cbn [q_ret qset_br].
      rewrite HRetX, HRetD. exact HRetE. }
    rewrite HextX, Hl15d, Nat2Z.id in HRd2.
    destruct HfrM as (HObM & HRetM & HInM & HOutM & HTabM & HWinM
                      & HLastM & HWrapM & HFlagM & HCheckM & HTotalM).
    (* the composite frame q -> qM *)
    assert (HObQ : q_ob qM = q_ob q) by congruence.
    assert (HRetQ : q_ret qM = q_ret q) by congruence.
    assert (HInQ : q_in qM = q_in q) by congruence.
    assert (HOutQ : q_out qM = q_out q) by congruence.
    assert (HTabQ : s_tab (q_st qM) = s_tab (q_st q)) by congruence.
    assert (HWinQ : s_win (q_st qM) = s_win (q_st q)) by congruence.
    assert (HLastQ : h_last (s_hdr (q_st qM)) = h_last (s_hdr (q_st q)))
      by congruence.
    assert (HWrapQ : h_wrap (s_hdr (q_st qM)) = h_wrap (s_hdr (q_st q)))
      by congruence.
    assert (HFlagQ : h_flags (s_hdr (q_st qM)) = h_flags (s_hdr (q_st q)))
      by congruence.
    assert (HCheckQ : h_check (s_hdr (q_st qM)) = h_check (s_hdr (q_st q)))
      by congruence.
    assert (HTotalQ : h_total (s_hdr (q_st qM)) = h_total (s_hdr (q_st q)))
      by congruence.
    (* values at qM *)
    assert (HoffMv : u_offset (s_cur (q_st qM)) = Z.of_nat b0d + v2)
      by (rewrite HoffM, HoffX, Hvald; reflexivity).
    assert (HlenMv : u_length (s_cur (q_st qM)) = Z.of_nat b0 + v1)
      by (rewrite HlenM, HlenX, HlenD, HlenE, Hval; reflexivity).
    (* concrete extra-value bounds (the 2^atom forms are lia-opaque) *)
    assert (Hv1b : 0 <= v1 < 32).
    { split; [lia|].
      apply (Z.lt_le_trans _ (2 ^ u_extra (s_cur (q_st qE)))); [lia|].
      replace 32 with (2 ^ 5) by reflexivity.
      apply Z.pow_le_mono_r; [lia|].
      rewrite HextE, Hl15. lia. }
    assert (Hv2b : 0 <= v2 < 8192).
    { split; [lia|].
      apply (Z.lt_le_trans _ (2 ^ u_extra (s_cur (q_st qX)))); [lia|].
      replace 8192 with (2 ^ 13) by reflexivity.
      apply Z.pow_le_mono_r; [lia|].
      rewrite HextX, Hl15d. lia. }
    (* MATCH *)
    destruct (zr_match_cases qM
                ltac:(rewrite HObQ; exact Hput)
                ltac:(rewrite HObQ; exact Hleft)
                ltac:(rewrite HObQ, HOutQ; exact Htie)
                ltac:(rewrite HOutQ; exact Hcap)
                ltac:(rewrite HWinQ; exact Hwh)
                ltac:(rewrite HTabQ; exact Hsn)
                ltac:(rewrite HoffMv; lia)
                ltac:(rewrite HlenMv; lia))
      as [ (ElM & ELM)
         | [ (qbm & EBm & HMbm)
           | [ (q' & ECf & Hoffle & Hlenle & HSlf & HPutf & HSumf & HMf
                & HBrf & HLastf & HWrapf & HFlagf & HCheckf & HTotalf
                & HWinf & HTabf & HRetf & HInf & HOutf)
             | (q4 & ECp & HLeft4 & HMode4 & HRet4) ] ] ].
    + (* starved at MATCH entry *)
      right; right. exists 1%nat, (InfLeave qM).
      split.
      { apply inf_loop_one_exit;
          [ rewrite HSTEP, EC, ECD, ECX, ECM; exact ELM | exact I ]. }
      rewrite HRetQ. reflexivity.
    + (* distance too far *)
      right; left. exists 1%nat, qbm.
      split; [ apply inf_iter_one; rewrite HSTEP, EC, ECD, ECX, ECM;
               exact EBm
             | exact HMbm ].
    + (* FULL copy: the LzRef agreement *)
      left.
      exists 1%nat, q',
        (LzRef (b0 + Z.to_nat v1)%nat (b0d + Z.to_nat v2)%nat).
      assert (HI1 : inf_iter 1 c q = Some q')
        by (apply inf_iter_one; rewrite HSTEP, EC, ECD, ECX, ECM;
            exact ECf).
      assert (HlenN : Z.to_nat (u_length (s_cur (q_st qM)))
                      = (b0 + Z.to_nat v1)%nat)
        by (rewrite HlenMv, Z2Nat.inj_add by lia; rewrite Nat2Z.id;
            reflexivity).
      assert (HoffN : Z.to_nat (u_offset (s_cur (q_st qM)))
                      = (b0d + Z.to_nat v2)%nat)
        by (rewrite HoffMv, Z2Nat.inj_add by lia; rewrite Nat2Z.id;
            reflexivity).
      split. { exact HI1. }
      split.
      { unfold decode_lit_len. rewrite Hhd. cbv beta iota.
        rewrite (proj2 (Nat.ltb_ge sym 256) ltac:(lia)).
        rewrite (proj2 (Nat.eqb_neq sym 256) ltac:(lia)).
        cbv beta iota.
        unfold read_extra. rewrite Hb0, He0. cbv beta iota.
        rewrite HRd1. cbv beta iota.
        rewrite Hhdd. cbv beta iota.
        rewrite Hb0d, He0d. cbv beta iota.
        rewrite HRd2. cbv beta iota.
        rewrite HBrf. reflexivity. }
      split.
      { split.
        { apply (proj2 (Nat.eqb_neq _ 0)). lia. }
        split.
        { replace (Z.of_nat (b0d + Z.to_nat v2))
            with (u_offset (s_cur (q_st qM))) by (rewrite HoffMv; lia).
          rewrite <- HObQ. exact Hoffle. }
        split.
        { rewrite HSlf, HObQ, HlenN, HoffN. reflexivity. }
        exact HMf. }
      split. { rewrite HBrf. exact HwfM. }
      split. { rewrite HPutf, HObQ, HlenMv. lia. }
      split.
      { rewrite HObQ in Hlenle, HSumf, HPutf.
        rewrite HlenMv in Hlenle, HPutf. lia. }
      split. { rewrite HSumf, HObQ. reflexivity. }
      split. { rewrite HTabf. exact HTabQ. }
      split. { rewrite HWinf. exact HWinQ. }
      split. { rewrite HLastf. exact HLastQ. }
      split. { rewrite HWrapf. exact HWrapQ. }
      split. { rewrite HRetf. exact HRetQ. }
      split. { rewrite HInf. exact HInQ. }
      split. { rewrite HOutf. exact HOutQ. }
      split. { intro Hal. rewrite HBrf. exact (HhaM (HhaX (HhaD (HhaE Hal)))). }
      split. { rewrite HFlagf. exact HFlagQ. }
      split. { rewrite HCheckf. exact HCheckQ. }
      rewrite HTotalf. exact HTotalQ.
    + (* PARTIAL copy: output exhausted, next trip starves *)
      right; right. exists 2%nat, (InfLeave q4).
      assert (HI1 : inf_iter 1 c q = Some q4)
        by (apply inf_iter_one; rewrite HSTEP, EC, ECD, ECX, ECM;
            exact ECp).
      split.
      { apply (inf_loop_after_iter 1 c q q4 1 (InfLeave q4) HI1).
        apply inf_loop_one_exit;
          [ rewrite (zr_step_at_match c q4
                       ltac:(rewrite HMode4; exact HmM));
            apply zr_match_left0; exact HLeft4
          | exact I ]. }
      rewrite HRet4, HRetQ. reflexivity.
Qed.

Print Assumptions zr_ob_write_slice.
Print Assumptions zr_lit_split.
Print Assumptions zr_sym_trip.

Print Assumptions zr_lenext_split.
Print Assumptions zr_distext_split.
Print Assumptions zr_dist_split.
Print Assumptions zr_len_split.
