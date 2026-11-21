(** * LkK3 — K3: [ZrHuffDynLegSelGood_STMT] discharged (q7-decode
    leavekill fork, 2026-08-22, OFF-TREE SCRATCH).

    Statement: the ratified Gap7LeaveKill.v (md5
    , byte-verbatim copy in this bed).

    MIRROR of g1's DynLegSel.zr_huff_dyn_leg_sel_holds (a working folder
    ) with: the header segment = LkChain's good-only chain, the
    loop = LkLoopDyn's good-only loop, and the loop's new whave-0
    totality context discharged from the chain's own build pack —
    two-level/len-bounded/value-range facts read off the ACCEPTANCE
    covers (B3B5Stmts._acc + it_covers_all + root_chain_hop), never the
    ambient array, so the adversarial entry state costs nothing.

    PA-EXPORT: k3_dyn_leg_good. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits BwStream ZBitsIn Huff DeflateSpec Inftrees Inflate
  InflateFast InflateThy StepReach DynTblOkHolds ItGSubCover ItGAmb
  ItGTblCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6I ZReproQ6N ZReproQ6P ZReproQ6Q.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  Q6TblChain Q6HuffResidue GtBrAlign.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  A1StmtsV3 A1core B3Asm B3B5Stmts W5Bridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require GtDecHsel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Gap7Ents.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import DistV3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7LeaveKill.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  LkBody LkFastDyn LkLoopDyn LkChain.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Theorem k3_dyn_leg_good : ZrHuffDynLegSelGood_STMT.
Proof.
  unfold ZrHuffDynLegSelGood_STMT.
  intros c q lit dst r3 syms r4 out Hc Hwf Hha Hbud Hput Hleft Htie Hcap
    Hwh Hsn Hret Hm Hstrict HcwE Hdec Hres Hroom.
  destruct (lk_table_chain_good c q lit dst r3 Hc Hwf Hha Hput Hm
              Hret Hstrict HcwE)
    as (qL & d & HSL & HwfL & HhaL & Hdisp).
  pose proof (decode_dynamic_tables_strict_weaken _ _ _ _ Hstrict) as HD0.
  destruct Hdisp as (Hstep & Hacc & Hinst & Hlens & Hnl & Hnd & Hb1
                     & Hb2 & Hpre1 & Hpre2 & Hob & Hlast & Hin & Hout
                     & Hwsz & HretL & Hwrap & Hflags & Hcheck & Htotal
                     & HwhL & HsaneL).
  (* LEN export at the v3 head *)
  destruct (B3Asm.dyn_two_own_len_v3 d qL lit dst Hacc Hinst Hlens Hnl
              Hnd Hb1 Hb2 Hpre1)
    as (cL & stL & entl & HpreL & Htiel & Hownl & _).
  assert (Hpopl : (length lit <= 286)%nat) by lia.
  assert (Hpopd : (length dst <= 30)%nat) by lia.
  pose proof (Gap7Ents.zr_len_ents3_of_tie cL (db_lens d) (db_nlen d) 9
                (fun i => db_cs d (0 + i)) stL lit entl HpreL Hpopl Htiel)
    as Hpinsl3.
  (* DIST export at the authorized sibling *)
  destruct (dyn_two_own_dist_v3 d qL lit dst Hacc Hinst Hlens Hnl Hnd
              Hb1 Hb2)
    as (entd & Hownd & Hpinsd1).
  pose proof Hinst as (Il & Ilb & Id & Idb & Icodes).
  set (qm := qmode qL M_LEN).
  (* qm-side facts, each by CONVERSION from the qL/q facts *)
  assert (Ilbm : t_lenbits (s_tab (q_st qm)) = o_bits (db_o1 d))
    by exact Ilb.
  assert (Idbm : t_distbits (s_tab (q_st qm)) = o_bits (db_o2 d))
    by exact Idb.
  assert (Hownl' : zr_two_own_v3
            (tbl_of (q_st qm) (t_lencode (s_tab (q_st qm))))
            (t_lenbits (s_tab (q_st qm))) lit entl)
    by (rewrite Ilbm; exact Hownl).
  assert (Hownd' : zr_two_own_v3
            (tbl_of (q_st qm) (t_distcode (s_tab (q_st qm))))
            (t_distbits (s_tab (q_st qm))) dst entd)
    by (rewrite Idbm; exact Hownd).
  assert (Hlb' : 0 < t_lenbits (s_tab (q_st qm)) <= 15)
    by (rewrite Ilbm; pose proof (B3B5Stmts.dyn_lenbits_acc d Hacc); lia).
  assert (Hdb' : 0 < t_distbits (s_tab (q_st qm)) <= 15)
    by (rewrite Idbm; pose proof (B3B5Stmts.dyn_distbits_acc d Hacc); lia).
  destruct (decode_dynamic_tables_valid _ _ _ _ HD0) as (Vl & Vd).
  assert (Hshm : GtDecHsel.lcode_root_opshape
            (tbl_of (q_st qm) (t_lencode (s_tab (q_st qm))))
            (t_lenbits (s_tab (q_st qm))))
    by (exact (B3B5Stmts.dyn_root_opshape_acc d qL Hacc Hinst)).
  assert (HAL : inf_step c q = inf_step c qm).
  { rewrite (zr_step_at_len c qm ltac:(reflexivity)). exact Hstep. }
  (* ---- the whave-0 totality context at the LEN gate ---- *)
  destruct (B3B5Stmts.db_cover1_acc d Hacc) as (Hc1u & Hroot1 & Hsub1).
  assert (Hcov2 : 2 ^ o_bits (db_o2 d) <= o_used (db_o2 d)
    /\ (forall j, 0 <= j < 2 ^ o_bits (db_o2 d) ->
        RootEntry CT_DISTS (o_bits (db_o2 d)) (o_used (db_o2 d))
          (o_tbl (db_o2 d) j))
    /\ (forall i, 2 ^ o_bits (db_o2 d) <= i < o_used (db_o2 d) ->
        SubEntry CT_DISTS (o_bits (db_o2 d)) (o_tbl (db_o2 d) i))).
  { destruct Hacc as (_ & _ & _ & Hwf2 & Hm2 & Hr2).
    exact (it_covers_all CT_DISTS _ (db_ndist d) 6 _ (db_o2 d)
             (or_intror eq_refl) Hwf2 Hm2 Hr2). }
  destruct Hcov2 as (Hc2u & Hroot2 & Hsub2).
  pose proof (B3B5Stmts.dyn_lenbits_acc d Hacc) as Hb1a.
  pose proof (B3B5Stmts.dyn_distbits_acc d Hacc) as Hb2a.
  pose proof (pow2_pos_z (o_bits (db_o1 d)) ltac:(lia)) as Hp21.
  pose proof (pow2_pos_z (o_bits (db_o2 d)) ltac:(lia)) as Hp22.
  pose proof (db_view_len d qL Hinst) as HVl2.
  pose proof (db_view_dist d qL Hinst) as HVd2.
  assert (Hctx0 : lk_ctx_wf0 (if_ctx (w5_args qm))).
  { assert (Ectx : if_ctx (w5_args qm) = if_ctx (len_args qL))
      by reflexivity.
    rewrite Ectx.
    split.
    { (* lcode_two_level *)
      unfold lcode_two_level.
      cbn [if_ctx f_lcode f_lmask len_args a_lcode a_lenbits].
      rewrite Il, Ilb. cbn [tbl_of].
      intros v x s Hveq Hch.
      pose proof (land_ones_range x (o_bits (db_o1 d)) ltac:(lia)) as Hvr.
      rewrite <- Hveq in Hvr.
      rewrite (HVl2 v ltac:(lia)) in Hch |- *.
      destruct (lc_chains_true_shape _ Hch) as (Hnz & H16 & H64).
      destruct (root_chain_hop CT_LENS (o_bits (db_o1 d))
                  (o_used (db_o1 d)) (o_tbl (db_o1 d)) v s
                  Hb1a Hc1u Hroot1 Hvr Hnz H16 H64)
        as (Hbits & Hop & Htlo & Hthi).
      rewrite (HVl2 (c_val (o_tbl (db_o1 d) v)
                     + if_low (c_op (o_tbl (db_o1 d) v)) s) ltac:(lia)).
      apply leaf_lc_chains_false with (ty := CT_LENS).
      destruct (Hsub1 (c_val (o_tbl (db_o1 d) v)
                       + if_low (c_op (o_tbl (db_o1 d) v)) s)
                  ltac:(lia)) as [HL _].
      exact HL. }
    split.
    { (* dcode_two_level *)
      unfold dcode_two_level.
      cbn [if_ctx f_dcode f_dmask len_args a_dcode a_distbits].
      rewrite Id, Idb. cbn [tbl_of].
      intros v x s Hveq Hch.
      pose proof (land_ones_range x (o_bits (db_o2 d)) ltac:(lia)) as Hvr.
      rewrite <- Hveq in Hvr.
      rewrite (HVd2 v ltac:(lia)) in Hch |- *.
      destruct (dc_chains_true_shape _ Hch) as (H16 & H64).
      assert (Hnz : c_op (o_tbl (db_o2 d) v) <> 0).
      { destruct (Hroot2 v ltac:(lia)) as [Hleaf | Hptr].
        - destruct Hleaf as [HL _]. destruct HL as (_ & H2 & _).
          exact (H2 eq_refl).
        - destruct Hptr as (_ & Hop & _). lia. }
      destruct (root_chain_hop CT_DISTS (o_bits (db_o2 d))
                  (o_used (db_o2 d)) (o_tbl (db_o2 d)) v s
                  Hb2a Hc2u Hroot2 Hvr Hnz H16 H64)
        as (Hbits & Hop & Htlo & Hthi).
      rewrite (HVd2 (c_val (o_tbl (db_o2 d) v)
                     + if_low (c_op (o_tbl (db_o2 d) v)) s) ltac:(lia)).
      apply leaf_dc_chains_false.
      destruct (Hsub2 (c_val (o_tbl (db_o2 d) v)
                       + if_low (c_op (o_tbl (db_o2 d) v)) s)
                  ltac:(lia)) as [HL _].
      exact HL. }
    split.
    { (* lcode_len_bounded *)
      assert (Hleafcase : forall i, 0 <= i < o_used (db_o1 d) ->
                LeafShape CT_LENS (o_tbl (db_o1 d) i)
                \/ RootPtr (o_bits (db_o1 d)) (o_used (db_o1 d))
                     (o_tbl (db_o1 d) i)).
      { intros i Hi.
        destruct (Z_lt_le_dec i (2 ^ o_bits (db_o1 d))) as [Hlt|Hge].
        - destruct (Hroot1 i ltac:(lia)) as [[HL _] | Hptr];
            [left; exact HL | right; exact Hptr].
        - destruct (Hsub1 i ltac:(lia)) as [HL _]. left. exact HL. }
      unfold lcode_len_bounded.
      exists (o_used (db_o1 d)).
      unfold lcode_len_bounded_upto, lcode_index_range, lc_len_ok.
      cbn [if_ctx f_lcode f_lmask len_args a_lcode a_lenbits].
      rewrite Il, Ilb. cbn [tbl_of].
      split.
      { intros v Hv.
        rewrite (HVl2 v Hv).
        destruct (Hleafcase v Hv) as [HL | Hptr].
        - destruct HL as (_ & _ & _ & _ & _ & H6 & _).
          exact (H6 eq_refl).
        - destruct Hptr as (_ & Hop & _).
          intro Hf. exfalso. apply Hf.
          change 16 with (2 ^ 4). apply land_small_pow2; lia. }
      split.
      { intro s.
        pose proof (land_ones_range (f_hold s) (o_bits (db_o1 d))
                      ltac:(lia)).
        lia. }
      { intros v s Hv Hch.
        rewrite (HVl2 v Hv) in Hch |- *.
        destruct (lc_chains_true_shape _ Hch) as (Hnz & H16 & H64).
        assert (Hvr : 0 <= v < 2 ^ o_bits (db_o1 d)).
        { destruct (Z_lt_le_dec v (2 ^ o_bits (db_o1 d))) as [Hlt|Hge];
            [lia | exfalso].
          destruct (Hsub1 v ltac:(lia)) as [HL _].
          rewrite (leaf_lc_chains_false _ _ HL) in Hch.
          discriminate Hch. }
        destruct (root_chain_hop CT_LENS (o_bits (db_o1 d))
                    (o_used (db_o1 d)) (o_tbl (db_o1 d)) v s
                    Hb1a Hc1u Hroot1 Hvr Hnz H16 H64)
          as (_ & _ & Htlo & Hthi).
        lia. } }
    split.
    { (* whave = 0 *)
      change (f_whave (if_ctx (len_args qL)))
        with (w_whave (s_win (q_st qL))).
      rewrite HwhL. exact Hwh. }
    split.
    { (* sane <> 0 *)
      change (f_sane (if_ctx (len_args qL)))
        with (t_sane (s_tab (q_st qL))).
      rewrite HsaneL. exact Hsn. }
    { (* the dcode value pair *)
      intros x s0.
      cbn [if_ctx f_dcode f_dmask len_args a_dcode a_distbits].
      rewrite Id, Idb. cbn [tbl_of]. cbv beta.
      pose proof (land_ones_range x (o_bits (db_o2 d)) ltac:(lia)) as Hvr.
      rewrite (HVd2 (Z.land x (Z.shiftl 1 (o_bits (db_o2 d)) - 1))
                 ltac:(lia)).
      split.
      - destruct (Hroot2 (Z.land x (Z.shiftl 1 (o_bits (db_o2 d)) - 1))
                    ltac:(lia)) as [[HL _] | Hptr].
        + destruct HL as (_ & _ & _ & Hval & _). exact Hval.
        + destruct Hptr as (_ & _ & Hval & _). exact Hval.
      - intro Hch.
        destruct (dc_chains_true_shape _ Hch) as (H16 & H64).
        assert (Hnz : c_op (o_tbl (db_o2 d)
                        (Z.land x (Z.shiftl 1 (o_bits (db_o2 d)) - 1)))
                      <> 0).
        { destruct (Hroot2 (Z.land x (Z.shiftl 1 (o_bits (db_o2 d)) - 1))
                      ltac:(lia)) as [Hleaf | Hptr].
          - destruct Hleaf as [HL _]. destruct HL as (_ & H2 & _).
            exact (H2 eq_refl).
          - destruct Hptr as (_ & Hop & _). lia. }
        destruct (root_chain_hop CT_DISTS (o_bits (db_o2 d))
                    (o_used (db_o2 d)) (o_tbl (db_o2 d))
                    (Z.land x (Z.shiftl 1 (o_bits (db_o2 d)) - 1)) s0
                    Hb2a Hc2u Hroot2 ltac:(lia) Hnz H16 H64)
          as (Hbits & Hop & Htlo & Hthi).
        rewrite (HVd2 (c_val (o_tbl (db_o2 d)
                         (Z.land x (Z.shiftl 1 (o_bits (db_o2 d)) - 1)))
                       + if_low (c_op (o_tbl (db_o2 d)
                           (Z.land x (Z.shiftl 1 (o_bits (db_o2 d)) - 1))))
                           s0)
                   ltac:(lia)).
        destruct (Hsub2 (c_val (o_tbl (db_o2 d)
                            (Z.land x (Z.shiftl 1 (o_bits (db_o2 d)) - 1)))
                         + if_low (c_op (o_tbl (db_o2 d)
                             (Z.land x
                                (Z.shiftl 1 (o_bits (db_o2 d)) - 1)))) s0)
                    ltac:(lia)) as [HL _].
        destruct HL as (_ & _ & _ & Hval & _). exact Hval. } }
  (* reader facts at qm *)
  assert (Eob : q_ob qm = q_ob q) by exact Hob.
  assert (Eout : q_out qm = q_out q) by exact Hout.
  assert (HwfL' : br_wf (q_br qm)) by exact HwfL.
  assert (HhaL' : W2Stream.br_haligned (q_br qm)) by exact HhaL.
  assert (Hput' : 0 <= o_put (q_ob qm)) by (rewrite Eob; exact Hput).
  assert (Hleft' : 0 <= o_left (q_ob qm)) by (rewrite Eob; exact Hleft).
  assert (Htie' : q_out qm = o_put (q_ob qm) + o_left (q_ob qm))
    by (rewrite Eout, Eob; exact Htie).
  assert (Hcap' : q_out qm <= 4294967295) by (rewrite Eout; exact Hcap).
  assert (Ewh : w_whave (s_win (q_st qm)) = w_whave (s_win (q_st q)))
    by exact HwhL.
  assert (Hwh' : w_whave (s_win (q_st qm)) = 0) by (rewrite Ewh; exact Hwh).
  assert (Esn : t_sane (s_tab (q_st qm)) = t_sane (s_tab (q_st q)))
    by exact HsaneL.
  assert (Hsn' : t_sane (s_tab (q_st qm)) <> 0) by (rewrite Esn; exact Hsn).
  assert (ESm : br_stream (q_br qm) = r3) by exact HSL.
  assert (Hbud' : br_have (q_br qm) + br_bits (q_br qm) / 8 <= 4294967290).
  { pose proof (decode_dynamic_tables_le _ _ _ _ HD0) as Hle3.
    assert (HlenS : (length (br_stream (q_br qm))
                     <= length (br_stream (q_br q)))%nat)
      by (rewrite ESm; exact Hle3).
    pose proof (br_budget_mono (q_br q) (q_br qm) Hwf HwfL' HlenS) as HBM.
    lia. }
  (* the good-only selection loop *)
  destruct (lk_sym_loop_dyn_good
              (S (length (br_stream (q_br qm)))) c qm
              lit dst entl entd syms r4 out Vl Vd
              Hownl' Hownd' Hlb' Hdb' Hpinsl3 Hpinsd1 Hpopl Hpopd Hshm
              Hctx0 ltac:(lia) HwfL' Hput' Hleft' Htie' Hcap' Hwh' Hsn'
              ltac:(reflexivity) HhaL' Hbud'
              ltac:(rewrite ESm; exact Hdec)
              ltac:(rewrite Eob; exact Hres)
              ltac:(rewrite Eout; exact Hroom))
    as (k & q' & HI & HS & HR' & HM & C6 & C7 & C8 & C9 & C10 & C11
        & C12 & C13 & CF & CK & CT & C14 & C15 & C16 & CH).
  destruct k as [|k'].
  { exfalso. cbn [inf_iter] in HI. injection HI as <-.
    assert (HmM : h_mode (s_hdr (q_st qm)) = M_LEN) by reflexivity.
    rewrite HmM in HM. discriminate. }
  exists (S k'), q'.
  split. { exact (inf_iter_alias_S c q qm k' q' HAL HI). }
  split. { exact HS. }
  split. { exact C6. }
  split.
  { rewrite Eob in HR'.
    rewrite Hres in HR'. injection HR' as E. exact (eq_sym E). }
  split. { rewrite C9, Eob. reflexivity. }
  split. { exact C7. }
  split. { exact C8. }
  split. { exact HM. }
  split. { assert (El : h_last (s_hdr (q_st qm)) = h_last (s_hdr (q_st q)))
             by exact Hlast.
           rewrite <- El. exact C12. }
  (* zr_blk_frame q q' *)
  assert (Ein : q_in qm = q_in q) by exact Hin.
  assert (EretL : q_ret qm = 0) by exact HretL.
  assert (Ewrap : h_wrap (s_hdr (q_st qm)) = h_wrap (s_hdr (q_st q)))
    by exact Hwrap.
  assert (Eflags : h_flags (s_hdr (q_st qm)) = h_flags (s_hdr (q_st q)))
    by exact Hflags.
  assert (Echeck : h_check (s_hdr (q_st qm)) = h_check (s_hdr (q_st q)))
    by exact Hcheck.
  assert (Etotal : h_total (s_hdr (q_st qm)) = h_total (s_hdr (q_st q)))
    by exact Htotal.
  assert (Ewsz : w_wsize (s_win (q_st qm)) = w_wsize (s_win (q_st q)))
    by exact Hwsz.
  assert (Hbud2 : br_have (q_br q') + br_bits (q_br q') / 8
                  <= 4294967290).
  { assert (HDm : decode_symbols lit dst (br_stream (q_br qm))
                  = Some (syms, r4))
      by (rewrite ESm; exact Hdec).
    pose proof (decode_symbols_shorter _ _ _ _ _ HDm) as HLn.
    pose proof (br_budget_mono (q_br qm) (q_br q') HwfL' C6
                  ltac:(rewrite HS; lia)) as HBM2.
    lia. }
  split.
  { split. { rewrite C15. exact Ein. }
    split. { rewrite C16. exact Eout. }
    split. { rewrite C14, EretL, Hret. reflexivity. }
    split. { rewrite C11. exact Ewsz. }
    split. { rewrite C13. exact Ewrap. }
    split. { rewrite CF. exact Eflags. }
    split. { rewrite CK. exact Echeck. }
    split. { rewrite CT. exact Etotal. }
    split. { rewrite C11. exact Ewh. }
    rewrite C10. exact Esn. }
  split. { exact CH. }
  exact Hbud2.
Qed.

Set Printing Width 2000.
Print Assumptions k3_dyn_leg_good.
