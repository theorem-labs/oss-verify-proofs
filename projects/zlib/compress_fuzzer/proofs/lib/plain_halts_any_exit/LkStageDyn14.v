(* the zlib 1.4 twin of LkStageDyn, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from LkStageDyn), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * LkStageDyn — the DYN decode stages, GOOD-ONLY (q7-decode
    leavekill fork, 2026-08-22, OFF-TREE SCRATCH).

    Mirrors of Gap7Bed-adjacent [Gap7Trip.zrA_len_split_two_sel] /
    [zrA_dist_split_two_sel] (g1's a working folder, Gap7Trip.v pin recorded
    in the bed receipt) with the absorbed arms killed:

      - DecFuel  -> LkFetch2.lk_decode_two_no_fuel;
      - DecLeave -> LkFetch2.lk_decode_two_no_leave (declarative
        hdecode success on the entry stream);
      - the MARKER BAD arm -> its own [hdecode = None] contradicts the
        success premise;
      - the invalid-coded BAD sites stay VACUOUS at the tight packs,
        exactly as in the _sel originals.

    PA-EXPORTS: lk_len_split_two_good, lk_dist_split_two_good. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6I ZReproQ6N ZReproQ6P.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtBrAlign.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import A1StmtsV3 A1core.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Ents.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkFetch2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkStageDyn.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Spec.PngModel.Inflate14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Lemma lk_len_split_two_good14 :
  forall q (ll : list nat) (entl : nat -> Code)
         (sym0 : nat) (rem0 : list bool),
  br_wf (q_br q) ->
  ValidLengths ll 15%nat ->
  zr_two_own_v3 (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
      (t_lenbits (s_tab (q_st q))) ll entl ->
  0 < t_lenbits (s_tab (q_st q)) <= 15 ->
  zr_len_ents3 ll entl ->
  (length ll <= 286)%nat ->
  (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)) && Z.ltb (br_bits (q_br q)) 8) = false ->
  hdecode (code_table ll 15%nat) (br_stream (q_br q))
  = Some (sym0, rem0) ->
  (exists qL sym cw,
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
  intros q ll entl sym0 rem0 Hwf HV Hown Hrb Hents Hpop Hg Hdec.
  assert (Hents4 : ZReproQ6P.zr_len_ents ll entl).
  { intros sym cw Hcf.
    destruct (Hents sym cw Hcf) as [A | [B | C]];
      [left; exact A | right; left; exact B | right; right; left; exact C]. }
  assert (Hsub : forall sym cw, code_for ll 15%nat sym = Some cw ->
                     sub_len (entl sym) = false)
    by (apply zrA_lents_sub_len; exact Hents4).
  unfold inf_LEN14. cbv zeta.
  rewrite Hg. cbv beta iota.
  pose proof zr_decode_hdecode_two as HD0.
  unfold zr_decode_hdecode_two_STMT in HD0.
  specialize (HD0 sub_len
       (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
       (t_lenbits (s_tab (q_st q))) ll entl (q_br q)
       Hrb HV Hown Hsub zrA_sub_len_ptr zrA_sub_len_marker Hwf).
  destruct (inf_decode sub_len
              (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
              (t_lenbits (s_tab (q_st q))) (q_br q))
    as [h b' nb|b'|] eqn:ED; cbv beta iota.
  - destruct HD0
      as (Hwf' & Hal' & [ (sym & cw & C1 & C2 & C6) | (Hrec & Hnone) ]).
    + destruct (Z.eqb_spec (c_op h) 0) as [E0|N0]; cbv beta iota.
      * (* literal *)
        left.
        eexists. exists sym, cw.
        split; [reflexivity|].
        split; [exact C1|].
        split; [exact C6|].
        split. { rewrite <- C2. exact E0. }
        split. { rewrite <- C2. reflexivity. }
        split. { reflexivity. }
        split; [exact Hwf'|].
        split. { intro Hal. exact (Hal' Hal). }
        repeat split; reflexivity.
      * destruct (Z.eqb_spec (Z.land (c_op h) 32) 0) as [E32|N32];
          cbn [negb]; cbv beta iota.
        -- destruct (Z.eqb_spec (Z.land (c_op h) 64) 0) as [E64|N64];
             cbn [negb]; cbv beta iota.
           ++ (* length: fall through to LENEXT *)
              right; right.
              eexists. exists sym, cw.
              split; [reflexivity|].
              split; [exact C1|].
              split; [exact C6|].
              split. { rewrite <- C2. exact N0. }
              split. { rewrite <- C2. exact E32. }
              split. { rewrite <- C2. exact E64. }
              split. { rewrite <- C2. reflexivity. }
              split. { rewrite <- C2. reflexivity. }
              split; [exact Hwf'|].
              split. { intro Hal. exact (Hal' Hal). }
              repeat split; reflexivity.
           ++ (* invalid lit/len code: VACUOUS at the tight pack *)
              exfalso.
              destruct (Hents sym cw C1)
                as [ (_ & Hop0 & _)
                   | [ (_ & _ & H32ne & _)
                     | (_ & (b0 & e0 & _ & _ & _ & _ & H64eq & _)) ] ];
                congruence.
        -- (* end of block *)
           right; left.
           eexists. exists sym, cw.
           split; [reflexivity|].
           split; [exact C1|].
           split; [exact C6|].
           split. { rewrite <- C2. exact N0. }
           split. { rewrite <- C2. exact N32. }
           split. { reflexivity. }
           split; [exact Hwf'|].
           split. { intro Hal. exact (Hal' Hal). }
           repeat split; reflexivity.
    + (* MARKER read: its no-parse contradicts the success premise *)
      exfalso. rewrite Hnone in Hdec. discriminate.
  - (* starve: killed *)
    exfalso.
    exact (lk_decode_two_no_leave sub_len _ _ ll entl (q_br q)
             sym0 rem0 b' Hrb HV Hown Hsub zrA_sub_len_ptr
             zrA_sub_len_marker Hwf Hdec ED).
  - (* fuel: killed *)
    exfalso.
    exact (lk_decode_two_no_fuel sub_len _ _ ll entl (q_br q)
             sym0 rem0 Hrb HV Hown Hsub zrA_sub_len_ptr
             zrA_sub_len_marker Hwf Hdec ED).
Qed.


Set Printing Width 2000.
