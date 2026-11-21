(** * LkStage — the slow-path stage lemmas, GOOD-ONLY (starve/fuel
    arms killed at their sites) (q7-decode leavekill fork, 2026-08-22,
    OFF-TREE SCRATCH).

    Mirrors of ZReproQ6P's stage splits and TripSel's
    [zr_len_split_sel]/[zr_dist_split_sel]/[zr_match_cases_sel], each
    with its leave/fuel arms refuted from availability instead of
    emitted:

    - [lk_len_split_good]/[lk_dist_split_good]: the decode stages with
      DecLeave killed by LkFetch's [lk_decode_no_leave] (declarative
      hdecode success on the entry stream) and DecFuel by
      [lk_decode_no_fuel]; the certified BAD/progress arms verbatim.
    - [lk_lenext_good]/[lk_distext_good]: the extra-bits stages with
      the NEEDBITS starve killed by K1 ([k1_nb_starve_short]) against
      a stream-length floor.
    - [lk_match_full]: the MATCH stage pinned to its full-copy arm by
      the room premises ([u_offset <= o_put], [u_length <= o_left],
      [0 < o_left]).

    PA-EXPORTS: lk_lenext_good, lk_distext_good, lk_len_split_good,
    lk_dist_split_good, lk_match_full. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate
  DecodeBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6M ZReproQ6N ZReproQ6P GtBrAlign.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7LeaveKill.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkNb LkFetch.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The extra-bits stages: starve killed by K1.
   ========================================================================== *)

Lemma lk_lenext_good : forall q,
  br_wf (q_br q) ->
  0 <= u_extra (s_cur (q_st q)) <= 13 ->
  (Z.to_nat (u_extra (s_cur (q_st q)))
   <= length (br_stream (q_br q)))%nat ->
  exists qD v,
    inf_LENEXT q = inf_DIST qD
    /\ read_bits (Z.to_nat (u_extra (s_cur (q_st q))))
         (br_stream (q_br q))
       = Some (v, br_stream (q_br qD))
    /\ 0 <= v < 2 ^ u_extra (s_cur (q_st q))
    /\ u_length (s_cur (q_st qD)) = u_length (s_cur (q_st q)) + v
    /\ br_wf (q_br qD)
    /\ (W2Stream.br_haligned (q_br q) -> W2Stream.br_haligned (q_br qD))
    /\ zr_sframe q qD.
Proof.
  intros q Hwf He Hfloor.
  unfold inf_LENEXT. cbv zeta.
  destruct (Z.eqb_spec (u_extra (s_cur (q_st q))) 0) as [E0|N0].
  - (* no extra field *)
    cbv beta iota.
    eexists. exists 0.
    split; [reflexivity|].
    rewrite E0. change (Z.to_nat 0) with 0%nat. cbn [read_bits].
    split; [reflexivity|].
    split. { change (2 ^ 0) with 1. lia. }
    split. { rewrite Z.add_0_r. reflexivity. }
    split; [exact Hwf|].
    split. { intro Hal. exact Hal. }
    repeat split; reflexivity.
  - destruct (inf_nb (u_extra (s_cur (q_st q))) (q_br q)) as [b|b] eqn:EN;
      cbv beta iota.
    + destruct (inf_nb_ok (u_extra (s_cur (q_st q))) (q_br q) b
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
    + (* starve: killed by K1 against the floor *)
      exfalso.
      destruct (k1_nb_starve_short (u_extra (s_cur (q_st q)))
                  (q_br q) b Hwf ltac:(lia) EN) as (Hshort & _ & _).
      lia.
Qed.

Lemma lk_distext_good : forall q,
  br_wf (q_br q) ->
  0 <= u_extra (s_cur (q_st q)) <= 13 ->
  (Z.to_nat (u_extra (s_cur (q_st q)))
   <= length (br_stream (q_br q)))%nat ->
  exists qM v,
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
    /\ zr_sframe q qM.
Proof.
  intros q Hwf He Hfloor.
  unfold inf_DISTEXT. cbv zeta.
  destruct (Z.eqb_spec (u_extra (s_cur (q_st q))) 0) as [E0|N0].
  - cbv beta iota.
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
    + destruct (inf_nb_ok (u_extra (s_cur (q_st q))) (q_br q) b
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
    + exfalso.
      destruct (k1_nb_starve_short (u_extra (s_cur (q_st q)))
                  (q_br q) b Hwf ltac:(lia) EN) as (Hshort & _ & _).
      lia.
Qed.

(* ==========================================================================
   2.  The decode stages: DecLeave/DecFuel killed by LkFetch.
   ========================================================================== *)

Lemma lk_len_split_good : forall q (ll : list nat) (entl : nat -> Code)
                                 (sym0 : nat) (rem0 : list bool),
  br_wf (q_br q) ->
  ValidLengths ll 15%nat ->
  ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
      (t_lenbits (s_tab (q_st q))) ll 15%nat entl ->
  0 < t_lenbits (s_tab (q_st q)) <= 15 ->
  (forall sym cw, code_for ll 15%nat sym = Some cw ->
       sub_len (entl sym) = false) ->
  (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q))) = false ->
  hdecode (code_table ll 15%nat) (br_stream (q_br q))
  = Some (sym0, rem0) ->
  (exists qb sym cw rem1,
        inf_LEN q = InfCont qb
        /\ h_mode (s_hdr (q_st qb)) = M_BAD
        /\ code_for ll 15%nat sym = Some cw
        /\ hdecode (code_table ll 15%nat) (br_stream (q_br q))
           = Some (sym, rem1)
        /\ c_op (entl sym) <> 0
        /\ Z.land (c_op (entl sym)) 32 = 0
        /\ Z.land (c_op (entl sym)) 64 <> 0)
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
  intros q ll entl sym0 rem0 Hwf HV Hown Hrb Hsub Hg Hhd.
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
      right; left.
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
           right; right; right.
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
        -- (* invalid literal/length code: keep the read *)
           left.
           eexists. exists sym, cw, (br_stream b').
           split; [reflexivity|].
           split; [reflexivity|].
           split; [exact C1|].
           split; [exact C6|].
           split. { rewrite <- C2. exact N0. }
           split. { rewrite <- C2. exact E32. }
           rewrite <- C2. exact N64.
      * (* end of block *)
        right; right; left.
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
  - (* starve: killed by declarative success *)
    exfalso.
    exact (lk_decode_no_leave sub_len _ _ ll 15%nat entl (q_br q)
             sym0 rem0 b' Hrb HV Hown Hsub Hwf Hhd ED).
  - (* fuel: killed unconditionally *)
    exfalso.
    exact (lk_decode_no_fuel sub_len _ _ ll 15%nat entl (q_br q)
             sym0 rem0 Hrb HV Hown Hsub Hwf Hhd ED).
Qed.

Lemma lk_dist_split_good : forall q (dl : list nat) (entd : nat -> Code)
                                  (sym0 : nat) (rem0 : list bool),
  br_wf (q_br q) ->
  ValidLengths dl 15%nat ->
  ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
      (t_distbits (s_tab (q_st q))) dl 15%nat entd ->
  0 < t_distbits (s_tab (q_st q)) <= 15 ->
  (forall sym cw, code_for dl 15%nat sym = Some cw ->
       sub_dist (entd sym) = false) ->
  hdecode (code_table dl 15%nat) (br_stream (q_br q))
  = Some (sym0, rem0) ->
  (exists qb dsym cw rem1,
        inf_DIST q = InfCont qb
        /\ h_mode (s_hdr (q_st qb)) = M_BAD
        /\ code_for dl 15%nat dsym = Some cw
        /\ hdecode (code_table dl 15%nat) (br_stream (q_br q))
           = Some (dsym, rem1)
        /\ Z.land (c_op (entd dsym)) 64 <> 0)
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
  intros q dl entd sym0 rem0 Hwf HV Hown Hrb Hsub Hhd.
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
      right.
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
    + (* invalid distance code: keep the read *)
      left.
      eexists. exists dsym, cw, (br_stream b').
      split; [reflexivity|].
      split; [reflexivity|].
      split; [exact C1|].
      split; [exact C6|].
      rewrite <- C2. exact N64.
  - exfalso.
    exact (lk_decode_no_leave sub_dist _ _ dl 15%nat entd (q_br q)
             sym0 rem0 b' Hrb HV Hown Hsub Hwf Hhd ED).
  - exfalso.
    exact (lk_decode_no_fuel sub_dist _ _ dl 15%nat entd (q_br q)
             sym0 rem0 Hrb HV Hown Hsub Hwf Hhd ED).
Qed.

(* ==========================================================================
   3.  MATCH pinned to the full copy by room.
   ========================================================================== *)

Lemma lk_match_full : forall q,
  0 <= o_put (q_ob q) ->
  0 <= o_left (q_ob q) ->
  q_out q = o_put (q_ob q) + o_left (q_ob q) ->
  q_out q <= 4294967295 ->
  w_whave (s_win (q_st q)) = 0 ->
  t_sane (s_tab (q_st q)) <> 0 ->
  0 < u_offset (s_cur (q_st q)) < 4294967296 ->
  0 <= u_length (s_cur (q_st q)) < 2147483648 ->
  u_offset (s_cur (q_st q)) <= o_put (q_ob q) ->
  u_length (s_cur (q_st q)) <= o_left (q_ob q) ->
  0 < o_left (q_ob q) ->
  exists q',
    inf_MATCH q = InfCont q'
    /\ ob_slice (q_ob q') 0 (o_put (q_ob q'))
       = ob_slice (q_ob q) 0 (o_put (q_ob q))
         ++ lz_copy (ob_slice (q_ob q) 0 (o_put (q_ob q)))
                    (Z.to_nat (u_length (s_cur (q_st q))))
                    (Z.to_nat (u_offset (s_cur (q_st q))))
    /\ o_put (q_ob q') = o_put (q_ob q) + u_length (s_cur (q_st q))
    /\ o_put (q_ob q') + o_left (q_ob q')
       = o_put (q_ob q) + o_left (q_ob q)
    /\ h_mode (s_hdr (q_st q')) = M_LEN
    /\ q_br q' = q_br q
    /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
    /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
    /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
    /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
    /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q))
    /\ s_win (q_st q') = s_win (q_st q)
    /\ s_tab (q_st q') = s_tab (q_st q)
    /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q.
Proof.
  intros q Hput Hleft Htie Hcap Hwh Hsn Hoff Hlen Hoffle Hlenle Hroom.
  unfold inf_MATCH. cbv zeta.
  destruct (Z.eqb_spec (o_left (q_ob q)) 0) as [E0|N0]; [lia|].
  assert (Houtd : u32 (q_out q - o_left (q_ob q)) = o_put (q_ob q)).
  { unfold u32. rewrite Htie.
    replace (o_put (q_ob q) + o_left (q_ob q) - o_left (q_ob q))
      with (o_put (q_ob q)) by lia.
    apply Z.mod_small. lia. }
  rewrite Houtd.
  destruct (Z.ltb_spec (o_put (q_ob q)) (u_offset (s_cur (q_st q))))
    as [Hfar|Hnear]; [lia|].
  destruct (Z.ltb_spec (o_left (q_ob q)) (u_length (s_cur (q_st q))))
    as [Hpart|Hfull]; [lia|].
  destruct (zr_copyn_out (Z.to_nat (u_length (s_cur (q_st q))))
              (w_win (s_win (q_st q))) (q_ob q)
              (u_offset (s_cur (q_st q))) ltac:(lia))
    as (Putn & Lftn & _ & _).
  rewrite Z2Nat.id in Putn, Lftn by lia.
  pose proof (zr_copyn_lz (Z.to_nat (u_length (s_cur (q_st q))))
                (w_win (s_win (q_st q))) (q_ob q)
                (u_offset (s_cur (q_st q))) ltac:(lia)) as Hlz.
  rewrite Z2Nat.id in Hlz by lia.
  rewrite Z.sub_diag.
  change (u32 0) with 0.
  rewrite (proj2 (Z.eqb_eq 0 0) eq_refl).
  eexists. split; [reflexivity|].
  cbn [q_st q_ob qset_ob qset_st qmode].
  split.
  { cbn [q_ob]. rewrite Putn. exact Hlz. }
  split. { exact Putn. }
  split. { rewrite Putn, Lftn. lia. }
  repeat split; try reflexivity.
Qed.

Set Printing Width 2000.
Print Assumptions lk_lenext_good.
Print Assumptions lk_distext_good.
Print Assumptions lk_len_split_good.
Print Assumptions lk_dist_split_good.
Print Assumptions lk_match_full.
