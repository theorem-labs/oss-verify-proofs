(* the zlib 1.4 twin of LkStage, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from LkStage), 1.3.1-only declarations no 1.4 consumer needs. *)
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
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkStage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Spec.PngModel.Inflate14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The extra-bits stages: starve killed by K1.
   ========================================================================== *)



(* ==========================================================================
   2.  The decode stages: DecLeave/DecFuel killed by LkFetch.
   ========================================================================== *)

Lemma lk_len_split_good14 : forall q (ll : list nat) (entl : nat -> Code)
                                 (sym0 : nat) (rem0 : list bool),
  br_wf (q_br q) ->
  ValidLengths ll 15%nat ->
  ZReproQ6M.zr_root_own (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
      (t_lenbits (s_tab (q_st q))) ll 15%nat entl ->
  0 < t_lenbits (s_tab (q_st q)) <= 15 ->
  (forall sym cw, code_for ll 15%nat sym = Some cw ->
       sub_len (entl sym) = false) ->
  (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)) && Z.ltb (br_bits (q_br q)) 8) = false ->
  hdecode (code_table ll 15%nat) (br_stream (q_br q))
  = Some (sym0, rem0) ->
  (exists qb sym cw rem1,
        inf_LEN14 q = InfCont qb
        /\ h_mode (s_hdr (q_st qb)) = M_BAD
        /\ code_for ll 15%nat sym = Some cw
        /\ hdecode (code_table ll 15%nat) (br_stream (q_br q))
           = Some (sym, rem1)
        /\ c_op (entl sym) <> 0
        /\ Z.land (c_op (entl sym)) 32 = 0
        /\ Z.land (c_op (entl sym)) 64 <> 0)
  (* literal *)
  \/ (exists qL sym cw,
        inf_LEN14 q = InfCont qL
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
        inf_LEN14 q = InfCont qT
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
        inf_LEN14 q = inf_LENEXT qE
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
  unfold inf_LEN14. cbv zeta.
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


(* ==========================================================================
   3.  MATCH pinned to the full copy by room.
   ========================================================================== *)


Set Printing Width 2000.
