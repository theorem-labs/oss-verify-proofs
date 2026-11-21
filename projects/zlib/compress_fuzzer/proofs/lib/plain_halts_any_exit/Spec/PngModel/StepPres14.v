
From Stdlib Require Import ZArith List Lia Bool.

From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Chunk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ZBitsIn.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import StepReach.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require CodesBuildRows.   (* T2 res-t2: the CODES-build suppliers of rm_tblCL0..3 (R2083 section 2) *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtItTotal.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import CfgBitsTblLeaf.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ItGTblLeafPos ItGTblLeafPosX.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require ItGSubCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import StepPres.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateThy14.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

#[local] Ltac c6bits := try rewrite !br_dropbits_bits; try (cbn [br_dropbits br_bits]); lia.
#[local] Ltac c6hdr := try lazymatch goal with |- (_ -> _) => intros _ end; bsimp; try (cbn [br_consume br_initbits br_have br_bits br_next br_hold br_in]); lia.
#[local] Ltac bsimp_in H := cbn [inf_budget q_mode q_br q_ob q_st q_z q_in q_out q_ret qset_st qset_z qset_br qset_ob qset_in qset_out qset_ret qmode qbad qcheck set_mode set_length set_have set_lens set_check set_total set_last set_ncode set_nlen set_ndist set_offset set_extra set_back set_was set_lencode set_distcode set_lenbits set_distbits set_next set_codes set_bits set_hold set_wbits set_wsize set_whave set_wnext set_alloc set_win set_flags set_dmax set_havedict set_head set_wrap set_work h_mode s_hdr s_win s_cur s_tab s_bld s_hold s_bits u_length u_offset u_extra u_back u_was br_have br_bits br_in br_next br_hold o_left o_put o_buf br_dropbits br_initbits br_bytebits ob_write inf_mrank] in H.
#[local] Ltac b0_pre Hm := unfold Bits0Side; repeat apply conj; intros Hm0; try (destruct Hm0 as [Hm0|[Hm0|Hm0]]);
  unfold q_mode in Hm, Hm0; bsimp_in Hm0; rewrite Hm in Hm0; try discriminate Hm0; clear Hm0.
#[local] Ltac ubk :=
  cbn [q_st qset_st qset_br qset_ob qmode qbad];
  repeat first [ rewrite uback_set_back | rewrite uback_set_length
               | rewrite uback_set_offset | rewrite uback_set_extra
               | rewrite uback_set_was | rewrite uback_set_mode ].

Lemma pres_HEAD14 :
  forall c q, q_mode q = M_HEAD -> ReachCore q -> (h_wrap (s_hdr (q_st q)) = 0 -> br_bits (q_br q) = 0) ->
    (q_mode q = M_HEAD -> q_out q - o_left (q_ob q) = 0) ->
    PresOk c (inf_HEAD14 c q).
Proof.
  intros c q Hm HC Hb0 Hw0. unfold inf_HEAD14. cbv zeta.
  core_facts q HC.
  destruct (Z.eqb (h_wrap (s_hdr (q_st q))) 0) eqn:Ew.
  { apply pres_TYPEDO; [left; unfold q_mode; bsimp; reflexivity| | apply Z.eqb_eq in Ew; pose proof (Hb0 Ew) as E0; change (br_bits (q_br q) <= 14); lia].
    apply (reach_core_conv q); [exact HC|reflexivity..]. }
  destruct (inf_nb 16 (q_br q)) as [b|b] eqn:Enb;
    [| destruct (inf_nb_leave 16 (q_br q) b ltac:(lia) Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Enb)
          as (Lh0 & Lin & Lhold & Lbits & Lbud);
       split;
       [ split;
         [ rc_close q
         | apply reach_mode_hdr0;
           [ left; unfold q_mode; bsimp; unfold q_mode in Hm; exact Hm
           | b0_pre Hm; intros Hg0; exfalso; bsimp_in Hg0; apply Z.eqb_neq in Ew; exact (Ew Hg0)
           | unfold q_mode; bsimp; intros _; exact (Hw0 Hm) ] ]
       | intros _ _; left; exact Lh0 ] ].
  pose proof (inf_nb_ok _ _ _ Enb) as Eok.
  pose proof Enb as Enb'.
  apply inf_nb_bud in Enb' as (E1 & E2 & E3). specialize (E3 Hh).
  destruct (inf_nb_env 16 (q_br q) b ltac:(lia) Fhold Hb
              (fun j => proj1 (rc_bytes q HC j)) F39 Enb)
    as (Nin & Nh & N39).
  destruct (negb (Z.eqb (Z.land (h_wrap (s_hdr (q_st q))) 2) 0)
            && Z.eqb (br_hold b) 35615).
  { (* gzip magic -> FLAGS *)
    destruct (Z.eqb (w_wbits (s_win (q_st q))) 0);
      (split; [rc_close q | rm_off]). }
  match goal with
  | |- context [if ?c then InfCont (qbad _ MSG_HEADER_CHECK) else _] =>
      destruct c
  end.
  { split; [rc_close q | rm_off]. }
  destruct (negb (Z.eqb (br_bits_of 4 b) Z_DEFLATED)).
  { split; [rc_close q | rm_off]. }
  destruct (Z.eqb (w_wbits (s_win (q_st q))) 0);
    match goal with
    | |- context [if ?c then InfCont (qbad _ MSG_WINDOW_SIZE) else _] =>
        destruct c
    end;
    try (split; [rc_close q | rm_off]);
    destruct (Z.eqb (Z.land (br_hold (br_dropbits 4 b)) 512) 0);
    (split; [rc_close q | first [ rm_off | apply reach_mode_hdr; [left; unfold q_mode; bsimp; reflexivity | c6hdr] ] ]).
Qed.

Lemma pres_LEN14 :
  forall c q,
    q_mode q = M_LEN ->
    ReachCore q ->
    LenTblSide q ->
    TblPDSide q ->
    br_bits (q_br q) <= 14 ->
    TblWidSide q ->
    DistSubSide q ->
    PresOk c (inf_LEN14 q).
Proof.
  intros c q Hm HC HL Htp Hb14 Hwd Hds.
  core_facts q HC.
  pose proof HL as (Htbl & Hlcs & Htds & Hltw & Hdtw & Hlbnd & Hlb & Hdb & Hroot0).
  rewrite inf_LEN14_eq. unfold inf_LEN14'. cbv zeta.
  destruct (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)) && Z.ltb (br_bits (q_br q)) 8)
    eqn:Egate.
  - (* fast path: the inflate_fast call node *)
    apply andb_prop in Egate as (Egate & _). apply andb_prop in Egate as (G1 & G2).
    apply Z.leb_le in G1. apply Z.leb_le in G2.
    assert (Hb40 : 0 <= a_bits (len_args q) <= 40)
      by (cbn [len_args a_bits]; lia).
    assert (Hwf : if_wf_lax (len_args q)).
    { split; [exact G1|]. split; [exact G2|].
      split; [exact Hb40|].
      split; [exact Hlb|]. split; [exact Hdb|].
      split; [exact Fsane|].
      split; [exact Fwh|]. split; [exact Fwn|].
      split; [exact (rc_bytes q HC)|]. split; [exact (rc_win q HC)|].
      split; [exact Hltw|]. split; [exact Hdtw|]. exact Hlbnd. }
    assert (Hain : a_avail_in (len_args q) <= 4294967290)
      by (cbn [len_args a_avail_in]; lia).
    assert (Haout : a_avail_out (len_args q) <= 4294967295)
      by (cbn [len_args a_avail_out]; lia).
    destruct (if_model_total_lax (len_args q) Hwf) as (y & EM).
    rewrite EM. cbv beta iota.
    pose proof (if_model_bytes (len_args q) (rc_win q HC) Fob) as HBy.
    rewrite EM in HBy. cbv beta iota in HBy.
    pose proof (if_model_pres (len_args q) Hwf Htbl Hain Haout) as HP.
    rewrite EM in HP.
    cbn [len_args a_avail_in a_bits a_avail_out] in HP.
    destruct HP as (Pbud & Pao & Pbits & Pai0 & Pao0 & Ph0).
    pose proof (if_model_hc (len_args q) Hwf Htbl) as Phc.
    rewrite EM in Phc. cbv beta iota in Phc.
    unfold len_post. cbv zeta.
    destruct (y_exit y) eqn:Eex; cbv beta iota.
    + (* ExLen: mode stays M_LEN *)
      lp_norm. rewrite Hm. cbv beta iota.
      split.
      * apply (reach_core_build q); lpp;
          try reflexivity; try assumption; try lia;
          try (cbv [q_load q_restore]; ksimp; lia).
      * apply reach_mode_scc.
        { left. lp_norm. exact Hm. }
        { apply (len_tbl_side_frame q); [reflexivity | exact HL]. }
        { apply (tblpd_frame q); [reflexivity | exact Htp]. }
        { lpp; first [ lia | (cbv [q_load q_restore]; ksimp; lia) ]. }
        { apply (tblwid_frame q); [lpp; reflexivity | exact Hwd]. }
        { apply (dist_sub_frame q); [lpp; reflexivity | exact Hds]. }
    + (* ExType *)
      lp_norm. cbv beta iota.
      split.
      * apply (reach_core_build q); lpp;
          try reflexivity; try assumption; try lia;
          try (cbv [q_load q_restore]; ksimp; lia).
      * apply reach_mode_hdr; [left; lpp; reflexivity | lpp; first [ lia | (cbv [q_load q_restore]; ksimp; lia) ] ].
    + (* ExBad *)
      lp_norm. cbv beta iota.
      split.
      * apply (reach_core_build q); lpp;
          try reflexivity; try assumption; try lia;
          try (cbv [q_load q_restore]; ksimp; lia).
      * apply reach_mode_inactive. lpp. reflexivity.
  - (* slow path: one decode on the live length table *)
    pose proof (tbl_of_wid015 (q_st q) (t_lencode (s_tab (q_st q))) Famb)
      as Hwid.
    pose proof (tbl_of_val_range (q_st q) (t_lencode (s_tab (q_st q))) Famb)
      as Hvr.
    destruct (inf_decode sub_len
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q))) (q_br q))
      as [h b' nb|b'|] eqn:Edec;
    [ | destruct (inf_decode_leave _ _ _ _ _ Hwid Fhold Hb
            (fun j => proj1 (rc_bytes q HC j)) Edec)
            as (Lh0 & Lin & Lhold & Lbits & Lbud);
        split;
        [ split;
          [ rc_close q
          | apply reach_mode_scc;
            [ left; exact Hm
            | apply (len_tbl_side_frame q); [reflexivity | exact HL]
            | apply (tblpd_frame q); [reflexivity | exact Htp]
            | bsimp;
              exact (inf_decode_leave_le14 _ _ _ _ _ (proj1 Htp) (proj2 Hlb) (proj1 Hwd)
                       (fun i _ Hs => sub_len_nz _ Hs) sub_len_240 Fhold Hb (fun j => proj1 (rc_bytes q HC j)) Edec)
            | apply (tblwid_frame q); [reflexivity | exact Hwd]
            | apply (dist_sub_frame q); [reflexivity | exact Hds] ] ]
        | intros _ _; left; exact Lh0 ]
    | exact I ].
    destruct (inf_decode_env _ _ _ _ _ _ _ Hwid Fhold Hb
                (fun j => proj1 (rc_bytes q HC j)) F39 Edec)
      as (Din & Dh & D39).
    pose proof (inf_decode_bits_nonneg _ _ _ _ _ _ _ Edec) as Db0.
    destruct (inf_decode_bud _ _ _ _ _ _ _ Edec) as (Dbud & Dhave).
    specialize (Dhave Hh).
    destruct (inf_decode_ok_facts _ _ _ _ _ _ _
                (fun i => proj1 (Hwid i)) Edec)
      as ((i0 & Hhe) & Hnb0).
    pose proof (inf_decode_nb_le30 _ _ _ _ _ _ _
                  (fun i => proj2 (Hwid i)) Edec) as Hnb30.
    pose proof (inf_decode_le14 _ _ _ _ _ _ _ (proj1 Htp)
                  (subguard_len_wid _ _ (proj1 Hwd) (fun i => proj1 (Hwid i))) Hb14 Edec) as Hb13.
    assert (Hval : 0 <= c_val h < 65536) by (rewrite Hhe; exact (Hvr i0)).
    destruct (Z.eqb (c_op h) 0) eqn:E0.
    + (* literal -> M_LIT *)
      split.
      * rc_close q.
      * apply reach_mode_scc.
        { right; right. unfold q_mode. bsimp. reflexivity. }
        { apply (len_tbl_side_frame q); [reflexivity | exact HL]. }
        { apply (tblpd_frame q); [reflexivity | exact Htp]. }
        { bsimp. lia. }
        { apply (tblwid_frame q); [reflexivity | exact Hwd]. }
        { apply (dist_sub_frame q); [reflexivity | exact Hds]. }
    + destruct (negb (Z.eqb (Z.land (c_op h) 32) 0)) eqn:E32.
      * (* end of block -> M_TYPE *)
        split; [rc_close q | apply reach_mode_hdr; [left; unfold q_mode; bsimp; reflexivity | bsimp; lia]].
      * destruct (negb (Z.eqb (Z.land (c_op h) 64) 0)) eqn:E64.
        { (* invalid -> M_BAD *)
          split; [rc_close q | rm_off]. }
        (* length base: falls through IN-CALL to LENEXT *)
        apply Bool.negb_false_iff, Z.eqb_eq in E64.
        apply Bool.negb_false_iff, Z.eqb_eq in E32.
        apply Z.eqb_neq in E0.
        assert (Hv1 : 1 <= c_val h).
        { destruct Hlcs as (Lb0 & Leob & Lval).
          eapply inf_decode_val_pos; [exact Lval | exact Edec | | |];
            rewrite Hhe in E0, E32, E64 |- *; assumption. }
        pose proof (land15_range (c_op h)) as He15.
        apply pres_LENEXT;
          [ unfold q_mode; bsimp; reflexivity
          | rc_close q
          | ksimp; lia
          | ksimp; lia
          | ksimp; exact He15
          | ksimp; ubk; lia
          | apply (len_tbl_side_frame q); [reflexivity | exact HL]
          | apply (tblpd_frame q); [reflexivity | exact Htp]
          | ksimp; lia
          | apply (tblwid_frame q); [reflexivity | exact Hwd]
          | apply (dist_sub_frame q); [reflexivity | exact Hds] ].
Qed.

Lemma pres_LEN_14 :
  forall c q, ReachCore q -> LenTblSide q -> TblPDSide q -> br_bits (q_br q) <= 14 -> TblWidSide q -> DistSubSide q ->
    PresOk c (inf_LEN_14 q).
Proof.
  intros c q HC HL Htp Hb14 Hwd Hds. unfold inf_LEN_14.
  apply pres_LEN14.
  - reflexivity.
  - apply (reach_core_conv q); [exact HC|reflexivity..].
  - apply (len_tbl_side_frame q); [reflexivity | exact HL].
  - exact Htp.
  - exact Hb14.
  - exact Hwd.
  - apply (dist_sub_frame q); [reflexivity | exact Hds].
Qed.

Section PresKnot14.

Variable Hdyn : DynTblOk.

(* RSS cure (b1) (ca2-b1 / F45, 2026-09-08): the Qed kernel check of this one term was measured at +6.5 GiB over a 2.24 GiB tactic
   phase; at each of the five reach_core_build sites the goal's state record is `set` as a local definition before the apply, so the premise proofs are
   built over the small name and the kernel term holds one let-bound copy per arm; statement and every other line byte-identical. *)
Lemma pres_CODELENS14 :
  forall c q,
    q_mode q = M_CODELENS ->
    ReachCore q ->
    0 < b_nlen (s_bld (q_st q)) <= 288 ->
    0 < b_ndist (s_bld (q_st q)) <= 32 ->
    257 <= b_nlen (s_bld (q_st q)) <= 286 /\ 1 <= b_ndist (s_bld (q_st q)) <= 30 ->
    TblSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) ->
    TblPD (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) (t_lenbits (s_tab (q_st q))) ->
    br_bits (q_br q) <= 14 ->
    t_lenbits (s_tab (q_st q)) <= 7 ->
    t_lencode (s_tab (q_st q)) = TRcodes 0 ->
    1 <= t_lenbits (s_tab (q_st q)) ->
    2 ^ t_lenbits (s_tab (q_st q)) <= t_next (s_tab (q_st q)) ->
    (forall i, 0 <= i < 2 ^ t_lenbits (s_tab (q_st q)) -> 0 <= c_op (t_codes (s_tab (q_st q)) i) < 256) ->
    PresOk c (inf_CODELENS14 c q).
Proof.
  intros c q Hm HC Hnl Hnd Hnt Htl HtpCL Hb14 Hlb7 Hc0 Hc1 Hc2 Hc3.
  core_facts q HC.
  assert (Hnlen0 : 0 <= b_nlen (s_bld (q_st q))) by lia.
  assert (Hndist0 : 0 <= b_ndist (s_bld (q_st q))) by lia.
  unfold inf_CODELENS14. cbv zeta beta.
  destruct (cl_loop_at_codelens_fuel
              (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
              (t_lenbits (s_tab (q_st q)))
              (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
              {| cl_have := b_have (s_bld (q_st q));
                 cl_lens := b_lens (s_bld (q_st q));
                 cl_br := q_br q |}
              ltac:(cbn [cl_br]; lia) ltac:(cbn [cl_have]; lia))
    as (r & Hr & Hexit).
  rewrite Hr. cbv beta iota.
  pose proof (cl_loop_walk
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r Htl Hh Hb Flens Hr) as HW.
  cbn [cl_br cl_lens cl_have] in HW.
  pose proof (cl_loop_env
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r Htl Hh Hb Fhold
                (fun j => proj1 (rc_bytes q HC j)) F39 Flens Hr) as HE.
  cbn [cl_br cl_lens cl_have] in HE.
  pose proof (cl_loop_chave
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r ltac:(cbn [cl_have]; lia) Hr)
    as HCh.
  pose proof (cl_loop_bits14 (S (Z.to_nat (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q)); cl_lens := b_lens (s_bld (q_st q)); cl_br := q_br q |} r HtpCL Hb14 Hr) as HB14.
  destruct r as [s1|s1|s1 m1|s1|]; cbn [cl_exit] in Hexit;
    try contradiction;
    [ | |
      destruct (cl_loop_leave
          (S (Z.to_nat (b_nlen (s_bld (q_st q))
                        + b_ndist (s_bld (q_st q)))))
          (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
          (t_lenbits (s_tab (q_st q)))
          (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
          {| cl_have := b_have (s_bld (q_st q));
             cl_lens := b_lens (s_bld (q_st q));
             cl_br := q_br q |} s1
          Htl Hh Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) F39 Flens Fbh Hr)
          as (Lh0 & Lin & Lhold & Lbits & Lbud & Llens & Lch);
      cbn [cl_br cl_lens cl_have]
        in Lh0, Lin, Lhold, Lbits, Lbud, Llens, Lch;
      split;
      [ split;
        [ rc_close q
        | apply reach_mode_codelens;
          [ exact Hm | exact Hnl | exact Hnd | exact Hnt | exact Htl | exact HtpCL
          | cbn [q_br qset_br];
            exact (cl_loop_leave_le14 (S (Z.to_nat (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q)); cl_lens := b_lens (s_bld (q_st q)); cl_br := q_br q |} s1 HtpCL Htl Hlb7 Hb14 Hh Hb Fhold (fun j => proj1 (rc_bytes q HC j)) Flens Hr)
          | exact Hlb7 | exact Hc0 | exact Hc1 | exact Hc2 | exact Hc3 ] ]
      | intros _ _; left; exact Lh0 ] ].
  - (* ClDone: the two builds *)
    destruct HW as (W1 & W2 & W3 & W4).
    destruct HE as (Ein & Ehold & E39 & E0b).
    cbv beta iota in HCh.
    cbv beta iota in HB14.
    destruct (Z.eqb (cl_lens s1 256) 0).
    { split.
      - match goal with |- ReachCore ?qq => set (st1 := qq) end.
        apply (reach_core_build q); ksimp;
          try reflexivity; try assumption; try hc_close;
          try (unfold st1; ksimp; lia); try (unfold st1; ksimp; hc_close).
      - rm_off. }
    unfold inf_table.
    assert (HLB1 : GtItTotal.LensBounded (cl_lens s1)
                     (b_nlen (s_bld (q_st q))))
      by (intros i _; apply W4).
    assert (HWF1 : it_wf CT_LENS (cl_lens s1) (b_nlen (s_bld (q_st q))) 9).
    { split; [lia|]. split; [intros i _; apply W4|].
      split; [unfold MAXBITS; lia|].
      right; left; split; [reflexivity | lia]. }
    match goal with
    | |- context [it_model CT_LENS ?l ?cs ?rt ?t0] =>
        remember (it_model CT_LENS l cs rt t0) as R1 eqn:EI1
    end.
    destruct R1 as [o1|].
    2:{ exfalso.
        exact (it_model_total _ _ _ _ _ Hnlen0 HLB1 (eq_sym EI1)). }
    cbv beta iota zeta.
    destruct (negb (Z.eqb (o_ret o1) 0)) eqn:Er1.
    { (* rejected LENS build: codes_wb is INSTALLED on this qbad *)
      split.
      - match goal with |- ReachCore ?qq => set (st2 := qq) end.
        apply (reach_core_build q); ksimp;
          try reflexivity; try assumption; try hc_close;
          try (unfold st2; ksimp; lia); try (unfold st2; ksimp; hc_close).
        exact (dyn_amb_wb Hdyn CT_LENS (cl_lens s1)
                 (b_nlen (s_bld (q_st q))) 9
                 (t_codes (s_tab (q_st q))) 0 o1
                 Famb HWF1
                 (fun Hty => False_ind _ (ct_lens_ne_codes Hty))
                 (eq_sym EI1)).
      - rm_off. }
    apply Bool.negb_false_iff in Er1. apply Z.eqb_eq in Er1.
    assert (HLB2 : GtItTotal.LensBounded
                     (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
                     (b_ndist (s_bld (q_st q))))
      by (intros i _; cbv beta; apply W4).
    assert (HWF2 : it_wf CT_DISTS
                     (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
                     (b_ndist (s_bld (q_st q))) 6).
    { split; [lia|]. split; [intros i _; cbv beta; apply W4|].
      split; [unfold MAXBITS; lia|].
      right; right; split; [reflexivity | lia]. }
    match goal with
    | |- context [it_model CT_DISTS ?l ?cs ?rt ?t0] =>
        remember (it_model CT_DISTS l cs rt t0) as R2 eqn:EI2
    end.
    destruct R2 as [o2|].
    2:{ exfalso.
        exact (it_model_total _ _ _ _ _ Hndist0 HLB2 (eq_sym EI2)). }
    cbv beta iota zeta.
    destruct (negb (Z.eqb (o_ret o2) 0)) eqn:Er2.
    { (* rejected DISTS build: both writes installed on this qbad *)
      split.
      - match goal with |- ReachCore ?qq => set (st3 := qq) end.
        apply (reach_core_build q); ksimp;
          try reflexivity; try assumption; try hc_close;
          try (unfold st3; ksimp; lia); try (unfold st3; ksimp; hc_close).
        exact (dyn_amb_wb Hdyn CT_DISTS
                 (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
                 (b_ndist (s_bld (q_st q))) 6
                 (codes_wb (t_codes (s_tab (q_st q))) 0 (o_tbl o1))
                 (0 + o_used o1) o2
                 (dyn_amb_wb Hdyn CT_LENS (cl_lens s1)
                    (b_nlen (s_bld (q_st q))) 9
                    (t_codes (s_tab (q_st q))) 0 o1
                    Famb HWF1
                    (fun Hty => False_ind _ (ct_lens_ne_codes Hty))
                    (eq_sym EI1))
                 HWF2
                 (fun Hty => False_ind _ (ct_dists_ne_codes Hty))
                 (eq_sym EI2)).
      - rm_off. }
    apply Bool.negb_false_iff in Er2. apply Z.eqb_eq in Er2.
    (* accepted: fall through IN-CALL to LEN_ at the installed state *)
    set (d := {| db_cs := t_codes (s_tab (q_st q));
                 db_lens := cl_lens s1;
                 db_nlen := b_nlen (s_bld (q_st q));
                 db_ndist := b_ndist (s_bld (q_st q));
                 db_o1 := o1; db_o2 := o2 |}).
    assert (Hdok : db_ok d).
    { split; [exact Famb|].
      split; [exact HWF1|].
      split; [exact (eq_sym EI1)|].
      split; [exact Er1|].
      split; [exact HWF2|].
      split; [exact (eq_sym EI2)|].
      exact Er2. }
    match goal with
    | |- context [if _ then InfLeave ?qq else _] =>
        assert (HRC : ReachCore qq); [ | assert (HLT : LenTblSide qq); [ | assert (HTP : TblPDSide qq); [ | assert (HWD : TblWidSide qq); [ | assert (HDS : DistSubSide qq) ] ] ] ]
    end.
    {
      match goal with |- ReachCore ?qq => set (st4 := qq) end.
      apply (reach_core_build q); ksimp;
        try reflexivity; try assumption; try hc_close;
        try (unfold st4; ksimp; lia); try (unfold st4; ksimp; hc_close).
      exact (dyn_amb_wb Hdyn CT_DISTS
               (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
               (b_ndist (s_bld (q_st q))) 6
               (codes_wb (t_codes (s_tab (q_st q))) 0 (o_tbl o1))
               (0 + o_used o1) o2
               (dyn_amb_wb Hdyn CT_LENS (cl_lens s1)
                  (b_nlen (s_bld (q_st q))) 9
                  (t_codes (s_tab (q_st q))) 0 o1
                  Famb HWF1
                  (fun Hty => False_ind _ (ct_lens_ne_codes Hty))
                  (eq_sym EI1))
               HWF2
               (fun Hty => False_ind _ (ct_dists_ne_codes Hty))
               (eq_sym EI2)).
    }
    {
      match goal with
      | |- LenTblSide ?qq =>
          assert (Hinst : db_installed d qq) by (repeat split; reflexivity)
      end.
      split. { exact (dyn_wf_tbl Hdyn d _ Hdok Hinst). }
      split. { exact (dyn_lcside Hdyn d _ Hdok Hinst). }
      split. { exact (dyn_tblside_d Hdyn d _ Hdok Hinst). }
      split. { exact (dyn_two_l Hdyn d _ Hdok Hinst). }
      split. { exact (dyn_two_d Hdyn d _ Hdok Hinst). }
      split. { exact (wf_tbl_len_bounded _
                        (dyn_wf_tbl Hdyn d _ Hdok Hinst)). }
      split. { exact (dyn_lenbits Hdyn d Hdok). }
      split. { exact (dyn_distbits Hdyn d Hdok). }
      exact (dyn_root_opshape Hdyn d _ Hdok Hinst).
    }
    { match goal with
      | |- TblPDSide ?qq =>
          assert (Hinst : db_installed d qq) by (repeat split; reflexivity)
      end.
      split; [exact (tblpd_installed_len d _ Hdok Hinst) | exact (tblpd_installed_dist d _ Hdok Hinst)]. }
    { match goal with
      | |- TblWidSide ?qq =>
          assert (Hinst : db_installed d qq) by (repeat split; reflexivity)
      end.
      exact (tblwid_installed d _ Hdok Hinst). }
    { match goal with
      | |- DistSubSide ?qq =>
          assert (Hinst : db_installed d qq) by (repeat split; reflexivity)
      end.
      exact (dsub_installed d _ Hdok Hinst). }
    destruct (Z.eqb (n_flush c) Z_TREES) eqn:Efl;
      [ split;
        [ split;
          [ exact HRC
          | apply reach_mode_scc;
            [ right; left; unfold q_mode; bsimp; reflexivity
            | exact HLT
            | exact HTP
            | ksimp; exact HB14
            | exact HWD
            | exact HDS ] ]
        | intros Hf _; exfalso; rewrite Hf in Efl; cbv in Efl;
          discriminate ]
      |].
    apply pres_LEN_14.
    + exact HRC.
    + exact HLT.
    + exact HTP.
    + ksimp; exact HB14.
    + exact HWD.
    + exact HDS.
  - (* ClBad: the loop's own rejection *)
    destruct HW as (W1 & W2 & W3 & W4).
    destruct HE as (Ein & Ehold & E39 & E0b).
    cbv beta iota in HCh.
    split.
    + match goal with |- ReachCore ?qq => set (st5 := qq) end.
      apply (reach_core_build q); ksimp;
        try reflexivity; try assumption; try hc_close;
        try (unfold st5; ksimp; lia); try (unfold st5; ksimp; hc_close).
    + rm_off.
Qed.

Lemma pres_LENLENS14 :
  forall c q,
    q_mode q = M_LENLENS ->
    ReachCore q ->
    (forall h, 0 <= h < b_have (s_bld (q_st q)) ->
       0 <= b_lens (s_bld (q_st q)) (inf_order h) <= 7) ->
    0 < b_nlen (s_bld (q_st q)) <= 288 ->
    0 < b_ndist (s_bld (q_st q)) <= 32 ->
    257 <= b_nlen (s_bld (q_st q)) <= 286 /\ 1 <= b_ndist (s_bld (q_st q)) <= 30 ->
    br_bits (q_br q) <= 14 ->
    PresOk c (inf_LENLENS14 c q).
Proof.
  intros c q Hm HC Hpre7 Hnl Hnd Hnt Hb14.
  core_facts q HC.
  unfold inf_LENLENS14. cbv zeta.
  pose proof (ll_go_walk 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hh Hb Flens) as HW.
  pose proof (ll_go_env 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hh Hb Fhold
                (fun j => proj1 (rc_bytes q HC j)) F39) as HE.
  pose proof (ll_go_chave 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Fbh) as HCh.
  pose proof (ll_go_le7 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hpre7) as HL7.
  pose proof (ll_go_bits14 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hb14) as HB14.
  match goal with
  | |- context [ll_go ?f ?nc ?hv0 ?ls0 ?b0] =>
      remember (ll_go f nc hv0 ls0 b0) as LG eqn:ELG
  end.
  destruct LG as [hv ls b|hv ls b];
    [| destruct (ll_go_leave _ _ _ _ _ _ _ _ Hh Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Flens Fbh Hpre7 (eq_sym ELG))
          as (Lh0 & Lin & Lhold & Lbits & Lbud & Llens & Lhv & Lp7);
       split;
       [ split;
         [ rc_close q
         | apply reach_mode_lenlens;
           [ exact Hm | exact Lp7 | exact Hnl | exact Hnd | exact Hnt | bsimp; lia ] ]
       | intros _ _; left; exact Lh0 ] ].
  destruct HW as (W1 & W2 & W3 & W4).
  destruct HE as (Ein & Ehold & E39 & E0b).
  cbv beta iota in HCh.
  cbv beta iota in HB14.
  remember (ll_zero 19 hv ls) as LZ eqn:EZ.
  destruct LZ as [hv1 ls1]. cbv beta iota.
  assert (Hls1 : lens_ok ls1).
  { pose proof (ll_zero_walk 19 hv ls W4) as HZ. rewrite <- EZ in HZ.
    exact HZ. }
  assert (Hhv1 : 0 <= hv1).
  { pose proof (ll_zero_chave 19 hv ls HCh) as HZ2.
    rewrite <- EZ in HZ2. cbn [fst] in HZ2. exact HZ2. }
  cbv beta iota in HL7. destruct HL7 as (Hhvge & Hp7).
  assert (Hg7 : forall h, 0 <= h < 19 -> 0 <= ls1 (inf_order h) <= 7).
  { intros h Hh19.
    pose proof (ll_zero_le7 19 hv ls Hp7
                  ltac:(cbn [Z.of_nat]; lia) h Hh19) as HZ7.
    rewrite <- EZ in HZ7. cbn [snd] in HZ7. exact HZ7. }
  assert (Hguard : CT_CODES = CT_CODES ->
                   forall i, 0 <= i < 19 -> ls1 i <= 7).
  { intros _ i Hi.
    destruct (inf_order_covers i Hi) as (h & Hh19 & E).
    rewrite <- E. exact (proj2 (Hg7 h Hh19)). }
  unfold inf_table.
  assert (HLB : GtItTotal.LensBounded ls1 19) by (intros i _; apply Hls1).
  assert (HWFC : it_wf CT_CODES ls1 19 7).
  { split; [lia|]. split; [intros i _; apply Hls1|].
    split; [unfold MAXBITS; lia|].
    left; split; [reflexivity | lia]. }
  match goal with
  | |- context [it_model CT_CODES ?l ?cs ?rt ?t0] =>
      remember (it_model CT_CODES l cs rt t0) as R1 eqn:EI1
  end.
  destruct R1 as [o1|].
  2:{ exfalso.
      assert (Hc19 : 0 <= 19) by lia.
      exact (it_model_total _ _ _ _ _ Hc19 HLB (eq_sym EI1)). }
  cbv beta iota zeta.
  destruct (negb (Z.eqb (o_ret o1) 0)) eqn:Er1.
  { (* rejected CODES build: codes_wb installed on this qbad *)
    split.
    - apply (reach_core_build q); ksimp;
        try reflexivity; try assumption; try lia; try hc_close.
      exact (dyn_amb_wb Hdyn CT_CODES ls1 19 7
               (t_codes (s_tab (q_st q))) 0 o1
               Famb HWFC Hguard (eq_sym EI1)).
    - rm_off. }
  apply Bool.negb_false_iff in Er1. apply Z.eqb_eq in Er1.
  apply pres_CODELENS14; [unfold q_mode; bsimp; reflexivity| | | | | | | | | | | |].
  - apply (reach_core_build q); ksimp;
      try reflexivity; try assumption; try lia; try hc_close.
    exact (dyn_amb_wb Hdyn CT_CODES ls1 19 7
             (t_codes (s_tab (q_st q))) 0 o1
             Famb HWFC Hguard (eq_sym EI1)).
  - ksimp. lia.
  - ksimp. lia.
  - ksimp. lia.
  - exact (dyn_codes_tblside Hdyn ls1 19 7
             (t_codes (s_tab (q_st q))) o1 Famb HWFC (eq_sym EI1)
             Er1).
  - (* rm_tblpdCL: the CODES build's TblPD through the codes_wb view *)
    unfold tbl_of; ksimp.
    apply tblpd_codes_wb0.
    + apply (it_tblpd_wf CT_CODES ls1 19 7 (fun i => t_codes (s_tab (q_st q)) (0 + i)) o1);
        [lia | intros i _; apply Hls1 | lia | left; split; [reflexivity | lia] | exact (eq_sym EI1) | exact Er1].
    + exact (dyn_amb_wb Hdyn CT_CODES ls1 19 7 (t_codes (s_tab (q_st q))) 0 o1 Famb HWFC Hguard (eq_sym EI1)).
  - ksimp. exact HB14.
  - (* STOP #8 fact at the CODELENS successor: the CODES build's root is <= 7 (it_model root = min root0 max_len) *)
    ksimp.
    exact (codes_build_root7 ls1 _ o1 HWFC (Hguard eq_refl) (eq_sym EI1) Er1).
  - (* rm_tblCL0 (T2 res-t2; R2083 section 2): the successor's lencode is the CODES table at TRcodes 0 *) ksimp. reflexivity.
  - (* rm_tblCL1 (T2) *) ksimp. exact (proj1 (CodesBuildRows.codes_build_rows ls1 _ o1 HWFC (Hguard eq_refl) (eq_sym EI1) Er1)).
  - (* rm_tblCL2 (T2) *) ksimp. pose proof (proj1 (proj2 (CodesBuildRows.codes_build_rows ls1 _ o1 HWFC (Hguard eq_refl) (eq_sym EI1) Er1))) as HU. lia.
  - (* rm_tblCL3 (T2): the op range below the root block, through the codes_wb view at offset 0 *)
    ksimp. intros i Hi. unfold codes_wb. destruct (Z.leb 0 i) eqn:Ei;
      [ rewrite Z.sub_0_r; exact (proj2 (proj2 (CodesBuildRows.codes_build_rows ls1 _ o1 HWFC (Hguard eq_refl) (eq_sym EI1) Er1)) i Hi) | apply Z.leb_gt in Ei; lia ].
Qed.

Lemma pres_TABLE14 :
  forall c q, q_mode q = M_TABLE -> ReachCore q -> br_bits (q_br q) <= 14 -> PresOk c (inf_TABLE14 c q).
Proof.
  intros c q Hm HC Hb14.
  core_facts q HC.
  unfold inf_TABLE14.
  destruct (inf_nb 14 (q_br q)) as [b|b] eqn:Enb;
    [| destruct (inf_nb_leave 14 (q_br q) b ltac:(lia) Hb Fhold
          (fun j => proj1 (rc_bytes q HC j)) Enb)
          as (Lh0 & Lin & Lhold & Lbits & Lbud);
       split;
       [ split;
         [ rc_close q
         | apply reach_mode_hdr; [right; right; unfold q_mode; bsimp; unfold q_mode in Hm; rewrite Hm; reflexivity | bsimp; lia] ]
       | intros _ _; left; exact Lh0 ] ].
  pose proof (inf_nb_ok _ _ _ Enb) as E14.
  pose proof (inf_nb_ok_le _ _ _ Enb) as Ele.
  pose proof Enb as Enb'.
  apply inf_nb_bud in Enb' as (E1 & E2 & E3). specialize (E3 Hh).
  destruct (inf_nb_env 14 (q_br q) b ltac:(lia) Fhold Hb
              (fun j => proj1 (rc_bytes q HC j)) F39 Enb)
    as (Nin & Nh & N39).
  pose proof (bits_of_range 5 b ltac:(lia)) as B1.
  change (2 ^ 5) with 32 in B1.
  pose proof (bits_of_range 5 (br_dropbits 5 b) ltac:(lia)) as B2.
  change (2 ^ 5) with 32 in B2.
  cbv zeta.
  destruct (Z.ltb 286 (br_bits_of 5 b + 257)
            || Z.ltb 30 (br_bits_of 5 (br_dropbits 5 b) + 1)) eqn:Eg.
  { split; [rc_close q | rm_off]. }
  apply Bool.orb_false_iff in Eg. destruct Eg as (Eg1 & Eg2).
  apply Z.ltb_ge in Eg1. apply Z.ltb_ge in Eg2.
  apply pres_LENLENS14; [unfold q_mode; bsimp; reflexivity| | | | | |].
  - rc_close q.
  - ksimp. intros h Hh0. lia.
  - ksimp. lia.
  - ksimp. lia.
  - ksimp. lia.
  - ksimp. c6bits.
Qed.

(** ** The dispatch, the [=InfCont] corollary, and [reach_iter14] *)
Theorem step_pres14 :
  forall c q, ReachSt q -> PresOk c (inf_step14 c q).
Proof.
  intros c q HR. pose proof HR as (HC & HM).
  destruct HM as [Hmatch Hlen1 Hextra Hoffext Hlenub HtblL HtblCL Hbldrng
                  Hlens7 Hback Hnlen257 Htblpd HtblpdCL Hbits14 Hbits0 Hwid Hoff16 Hdsub Hoff1 Hwrote0 HtblCL0 HtblCL1 HtblCL2 HtblCL3].
  unfold inf_step14.
  destruct (q_mode q) eqn:Hm.
  - exact (pres_HEAD14 c q Hm HC (proj1 Hbits0 eq_refl) (fun _ => Hwrote0 eq_refl)).
  - exact (pres_FLAGS c q Hm HC).
  - exact (pres_TIME c q Hm HC).
  - exact (pres_OS c q Hm HC).
  - exact (pres_EXLEN c q Hm HC (proj1 (proj2 Hbits0) eq_refl)).
  - exact (pres_EXTRA c q Hm HC (proj1 (proj2 (proj2 Hbits0)) (or_introl eq_refl))).
  - exact (pres_NAME c q Hm HC (proj1 (proj2 (proj2 Hbits0)) (or_intror (or_introl eq_refl)))).
  - exact (pres_COMMENT c q Hm HC (proj1 (proj2 (proj2 Hbits0)) (or_intror (or_intror eq_refl)))).
  - exact (pres_HCRC c q Hm HC (proj1 (proj2 (proj2 (proj2 Hbits0))) eq_refl)).
  - exact (pres_DICTID c q Hm HC).
  - apply pres_DICT; [exact HC | pose proof (proj2 (proj2 (proj2 (proj2 Hbits0))) (or_introl eq_refl)) as E0; lia].
  - exact (pres_TYPE c q Hm HC (Hbits14 (or_introl eq_refl))).
  - exact (pres_TYPEDO c q (or_introl Hm) HC (Hbits14 (or_intror (or_introl eq_refl)))).
  - exact (pres_STORED c q Hm HC).
  - exact (pres_COPY_ c q HC (proj2 (proj2 (proj2 (proj2 Hbits0))) (or_intror (or_introl eq_refl)))).
  - apply pres_COPY; [exact Hm | exact HC | exact (proj2 (proj2 (proj2 (proj2 Hbits0))) (or_intror (or_intror eq_refl)))].
  - exact (pres_TABLE14 c q Hm HC (Hbits14 (or_intror (or_intror (or_introl eq_refl))))).
  - destruct (Hbldrng (or_introl eq_refl)) as (Bn & Bd).
    exact (pres_LENLENS14 c q Hm HC (Hlens7 eq_refl) Bn Bd
             (Hnlen257 (or_introl eq_refl))
             (Hbits14 (or_intror (or_intror (or_intror (or_introl eq_refl)))))).
  - destruct (Hbldrng (or_intror eq_refl)) as (Bn & Bd).
    exact (pres_CODELENS14 c q Hm HC Bn Bd (Hnlen257 (or_intror eq_refl))
             (HtblCL eq_refl) (proj1 (HtblpdCL eq_refl))
             (Hbits14 (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))
             (proj2 (HtblpdCL eq_refl))
             (HtblCL0 eq_refl) (HtblCL1 eq_refl) (HtblCL2 eq_refl) (HtblCL3 eq_refl)).
  - apply pres_LEN_14;
      [ exact HC | apply HtblL; right; left; reflexivity
      | apply Htblpd; right; left; reflexivity
      | apply Hbits14; do 5 right; left; reflexivity
      | apply Hwid; right; left; reflexivity
      | apply Hdsub; right; left; reflexivity ].
  - apply pres_LEN14;
      [ exact Hm | exact HC | apply HtblL; left; reflexivity
      | apply Htblpd; left; reflexivity
      | apply Hbits14; do 6 right; left; reflexivity
      | apply Hwid; left; reflexivity
      | apply Hdsub; left; reflexivity ].
  - apply pres_LENEXT;
      [ exact Hm
      | exact HC
      | apply Hlen1; left; reflexivity
      | apply (proj1 Hlenub); reflexivity
      | apply Hextra; left; reflexivity
      | apply (proj1 Hback); reflexivity
      | apply HtblL; right; right; left; reflexivity
      | apply Htblpd; right; right; left; reflexivity
      | apply Hbits14; do 7 right; left; reflexivity
      | apply Hwid; right; right; left; reflexivity
      | apply Hdsub; right; right; left; reflexivity ].
  - apply pres_DIST;
      [ exact Hm
      | exact HC
      | apply Hlen1; right; left; reflexivity
      | apply (proj2 Hlenub); left; reflexivity
      | apply (proj1 (proj2 Hback)); reflexivity
      | apply HtblL; right; right; right; left; reflexivity
      | apply Htblpd; right; right; right; left; reflexivity
      | apply Hbits14; do 8 right; left; reflexivity
      | apply Hwid; right; right; right; left; reflexivity
      | apply Hdsub; right; right; right; left; reflexivity ].
  - destruct (Hoffext eq_refl) as (Ho1 & Ho2).
    apply pres_DISTEXT;
      [ exact Hm
      | exact HC
      | apply Hlen1; right; right; reflexivity
      | apply (proj2 Hlenub); right; left; reflexivity
      | apply Hextra; right; reflexivity
      | exact Ho1
      | exact Ho2
      | apply (proj2 (proj2 Hback)); reflexivity
      | apply HtblL; right; right; right; right; left; reflexivity
      | apply Htblpd; right; right; right; right; left; reflexivity
      | apply Hbits14; do 9 right; left; reflexivity
      | apply Hwid; right; right; right; right; left; reflexivity
      | exact (Hoff16 eq_refl)
      | apply Hdsub; do 4 right; left; reflexivity
      | exact (proj1 Hoff1 eq_refl) ].
  - apply pres_MATCH;
      [ exact Hm
      | exact HC
      | exact (Hmatch eq_refl)
      | apply (proj2 Hlenub); right; right; reflexivity
      | apply HtblL; right; right; right; right; right; left; reflexivity
      | apply Htblpd; right; right; right; right; right; left; reflexivity
      | apply Hbits14; do 10 right; left; reflexivity
      | apply Hwid; do 5 right; left; reflexivity
      | apply Hdsub; do 5 right; left; reflexivity
      | exact (proj2 Hoff1 eq_refl) ].
  - apply pres_LIT;
      [ exact Hm
      | exact HC
      | apply HtblL; right; right; right; right; right; right; reflexivity
      | apply Htblpd; do 6 right; reflexivity
      | apply Hbits14; do 11 right; reflexivity
      | apply Hwid; do 6 right; reflexivity
      | apply Hdsub; do 6 right; reflexivity ].
  - exact (pres_CHECK c q Hm HC).
  - exact (pres_LENGTH c q Hm HC).
  - exact (pres_DONE c q Hm HC).
  - exact (pres_BAD c q Hm HC).
  - exact (pres_MEM c q).
  - exact (pres_SYNC c q).
Qed.

Corollary step_pres14_eq :
  forall c q q', ReachSt q -> inf_step14 c q = InfCont q' -> ReachSt q'.
Proof.
  intros c q q' HR HE.
  pose proof (step_pres14 c q HR) as HP.
  rewrite HE in HP. exact HP.
Qed.

(** [ReachSt] along the landed [inf_iter14] (Inflate.v:1783): the state
    after ANY number of fall-through trips is reachable-invariant. *)
Theorem reach_iter14 :
  forall k c q q', ReachSt q -> inf_iter14 k c q = Some q' -> ReachSt q'.
Proof.
  induction k as [|k IH]; intros c q q' HR H.
  - cbn [inf_iter14] in H. injection H as <-. exact HR.
  - rewrite inf_iter14_S in H.
    pose proof (step_pres14 c q HR) as HP.
    destruct (inf_step14 c q) as [q1|q1|q1 r0|m0|] eqn:ES; try discriminate.
    cbv beta iota in HP.
    exact (IH c q1 q' HP H).
Qed.

End PresKnot14.
