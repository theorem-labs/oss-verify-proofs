(** * Bridge.DMatch.MFast5 — group M: pair D14, S5's emit against RT's
    ([m_fast_emit]).

    The tallies are group D's pairs ([pair_tr_tally_dist],
    [pair_tr_tally_lit]); the match distance S5 passes is
    [wrap32 (strstart - match_start)], which is RT's raw distance because the
    match is live (group R's [ms_fast_emit] and [ms_wrap_dist]).  The LZ
    updates after the tally use the single-setter kit of [MLz]; S5's insert
    loop is [MFast3.m_dfi]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MFill1 MFast1 MFast2
  MFast3 MFast4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require MFill2 MFill3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.
Module SBlk := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk.
Module STr := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Trees.

Lemma rt_ts_ls : forall a b t, RD.setD_ts a (RD.setD_ls b t) = RD.setD_ls b (RD.setD_ts a t).
Proof. intros a b t. destruct t. reflexivity. Qed.

Lemma m_max_lazy : forall s t, geom_rel s t -> DS.ds_max_lazy_match s = RC.dg_max_lazy_match (RD.d_cfg t).
Proof. intros s t H. unfold geom_rel in H. cbv zeta in H. tauto. Qed.

Theorem m_fast_emit : forall s1 p0 po pi,
  dst_rel s1 (RD.setD_ls (RK.df_l1 p0) p0) po pi -> em_inv s1 -> mt_inv p0 ->
  1 <= RC.dg_level (RD.d_cfg p0) <= 3 ->
  RD.ls_strstart (RD.d_ls p0) + 262 <= 65536 -> 1 <= RD.ls_lookahead (RD.d_ls p0) ->
  snd (s5_fast_emit s1) = fst (rt_fast_emit p0)
  /\ dst_rel (fst (s5_fast_emit s1)) (snd (rt_fast_emit p0)) po pi
  /\ em_core (fst (s5_fast_emit s1))
  /\ (snd (s5_fast_emit s1) = false -> em_inv (fst (s5_fast_emit s1))).
Proof.
  intros s1 p0 po pi Hd1 He1 Hm Hlev Hroom Hla1.
  pose proof (m_cfg_facts p0 Hm) as Hc.
  pose proof (mt_ms p0 Hm) as Hms.
  pose proof (mt_fast p0 Hm ltac:(lia)) as Hfa.
  pose proof (mt_ml p0 Hm) as Hml.
  pose proof (RK.mi_str _ Hms) as Hss0.
  destruct Hfa as [Hf1 Hf2]. change RC.MIN_MATCH with 3 in Hf1, Hf2.
  destruct (rt_df_l1_facts p0 Hm Hroom) as (Fw & Fss & Fla & Fbs & Fhw & Fma & Fins & Fpl & Fws & Fpm & Fml & Fms).
  pose proof (mt_ws p0 Hm) as Hws.
  set (l1 := RK.df_l1 p0) in *.
  pose proof Hd1 as Hd1'. apply m_dst_split in Hd1' as [Hl1 Hn1].
  assert (Hgr1 : geom_rel s1 (RD.setD_ls l1 p0)) by (destruct Hn1; assumption).
  pose proof (MFill3.m_s5_geom_cf s1 _ Hgr1 Hc) as Hg1.
  pose proof (lzr_ml _ _ Hl1) as Eml. pose proof (lzr_ss _ _ Hl1) as Ess.
  pose proof (lzr_la _ _ Hl1) as Ela. pose proof (lzr_ms _ _ Hl1) as Ems.
  pose proof (lzr_win _ _ Hl1) as Hrw.
  cbn [RD.d_ls RD.setD_ls] in Eml, Ess, Ela, Ems, Hrw. rewrite Fws, Hws in Hrw.
  unfold s5_fast_emit, rt_fast_emit. cbv zeta. fold l1.
  rewrite Eml. change DS.MIN_MATCH with 3. change RC.MIN_MATCH with 3.
  destruct (Z.leb_spec 3 (RD.ls_matchlen l1)) as [Mt|Lt].
  - (* a match *)
    assert (Hml1 : RD.ls_matchlen l1 <= RD.ls_lookahead (RD.d_ls p0)) by (destruct Fml; lia).
    pose proof (RK.ms_fast_emit p0 Hms (mt_fast p0 Hm ltac:(lia)) Hla1 Mt) as Hlive.
    fold l1 in Hlive. rewrite (cf_max_dist _ Hc) in Hlive.
    assert (Edist : wrap32 (DS.ds_strstart s1 - DS.ds_match_start s1) = RD.ls_strstart l1 - RD.ls_matchstart l1)
      by (rewrite Ess, Ems; apply RK.ms_wrap_dist; mpow; lia).
    rewrite Edist.
    destruct (pair_tr_tally_dist s1 (RD.setD_ls l1 p0) po pi (RD.ls_strstart l1 - RD.ls_matchstart l1)
                (RD.ls_matchlen l1 - 3) Hd1 He1 ltac:(lia)) as (T1 & T2 & T3 & T4).
    cbn [RD.d_cfg RD.d_ts RD.setD_ls] in T1, T2, T3, T4 |- *.
    destruct (STr.tr_tally_dist s1 (RD.ls_strstart l1 - RD.ls_matchstart l1) (RD.ls_matchlen l1 - 3))
      as [st bf] eqn:ET.
    destruct (RT.tr_tally_dist (RD.ls_strstart l1 - RD.ls_matchstart l1) (RD.ls_matchlen l1 - 3)
                (RC.dg_sym_end (RD.d_cfg p0)) (RD.d_ts p0)) as [bf' ts'] eqn:ER.
    cbn [fst snd] in T1, T2, T3, T4 |- *. subst bf'.
    rewrite rt_ts_ls in T1. set (P1 := RD.setD_ts ts' p0) in *.
    pose proof T1 as T1'. apply m_dst_split in T1' as [Hlz Hnl].
    pose proof (lzr_ml _ _ Hlz) as Eml'. pose proof (lzr_la _ _ Hlz) as Ela'.
    pose proof (lzr_ss _ _ Hlz) as Ess'.
    cbn [RD.d_ls RD.setD_ls] in Eml', Ela', Ess'.
    assert (Hgt : geom_rel st (RD.setD_ls l1 P1)) by (destruct Hnl; assumption).
    pose proof (MFill3.m_s5_geom_cf st _ Hgt Hc) as Hgst.
    (* lookahead -= match_length *)
    assert (A1 : lz_rel (DS.set_lookahead st (DS.ds_lookahead st - DS.ds_match_length st))
                        (RD.setD_ls (RD.setL_lookahead (RD.ls_lookahead l1 - RD.ls_matchlen l1) l1) P1))
      by (apply lz_set_lookahead; [exact Hlz | rewrite Ela', Eml'; reflexivity]).
    set (st1 := DS.set_lookahead st (DS.ds_lookahead st - DS.ds_match_length st)) in *.
    set (l2 := RD.setL_lookahead (RD.ls_lookahead l1 - RD.ls_matchlen l1) l1) in *.
    assert (Eml1 : DS.ds_match_length st1 = RD.ls_matchlen l1) by (subst st1; rewrite ds_match_length__set_lookahead; exact Eml').
    assert (Ela1 : DS.ds_lookahead st1 = RD.ls_lookahead l1 - RD.ls_matchlen l1)
      by (subst st1; rewrite ds_lookahead__set_lookahead, Ela', Eml'; reflexivity).
    assert (Elz1 : DS.ds_max_lazy_match st1 = RC.dg_max_lazy_match (RD.d_cfg p0))
      by (subst st1; rewrite ds_max_lazy_match__set_lookahead; exact (m_max_lazy st _ Hgt)).
    rewrite Eml1, Ela1, Elz1.
    assert (Hv1 : nonlz_view st1 = nonlz_view st) by reflexivity.
    assert (Hg_st1 : s5_geom st1) by (exact (MFill3.m_geom_nonlz st st1 Hv1 Hgst)).
    assert (EBR : (RD.ls_matchlen l2 <=? RC.dg_max_lazy_match (RD.d_cfg p0)) && (3 <=? RD.ls_lookahead l2)
                  = (RD.ls_matchlen l1 <=? RC.dg_max_lazy_match (RD.d_cfg p0))
                    && (3 <=? RD.ls_lookahead l1 - RD.ls_matchlen l1)) by (subst l2; rt_ls; reflexivity).
    rewrite EBR.
    rt_ls.
    destruct (Z.leb (RD.ls_matchlen l1) (RC.dg_max_lazy_match (RD.d_cfg p0))
              && Z.leb 3 (RD.ls_lookahead l1 - RD.ls_matchlen l1)) eqn:EB; cbv iota beta.
    + (* insert the strings the match covers *)
      set (n := RD.ls_matchlen l1 - 1).
      assert (A2 : lz_rel (DS.set_match_length st1 n) (RD.setD_ls (RD.setL_matchlen n l2) P1))
        by (apply lz_set_match_length; [exact A1 | reflexivity]).
      set (st2 := DS.set_match_length st1 n) in *.
      assert (Eml2 : DS.ds_match_length st2 = n) by (subst st2; rewrite ds_match_length__set_match_length; reflexivity).
      rewrite Eml2.
      assert (Hv2 : nonlz_view st2 = nonlz_view st) by reflexivity.
      assert (Hg_st2 : s5_geom st2) by (exact (MFill3.m_geom_nonlz st st2 Hv2 Hgst)).
      assert (A2' : lz_rel st2 (RD.setD_ls (RD.setL_matchlen n (RD.setL_matchlen n l2)) P1)) by exact A2.
      assert (Hml258 : RD.ls_matchlen l1 <= 258) by (destruct Fml; lia).
      assert (Q1 : cfg_facts (RD.d_cfg P1)) by exact Hc.
      assert (Q2 : RD.ls_windowsize (RD.setL_matchlen n l2) = 65536) by (subst l2; rt_ls; rewrite Fws; exact Hws).
      assert (Q3 : 1 <= n) by lia.
      assert (Q4 : n <= Z.of_nat (Z.to_nat n)) by lia.
      assert (Q5 : n < Z.of_nat (Z.to_nat n + 1)) by lia.
      assert (Q6 : 0 <= RD.ls_strstart (RD.setL_matchlen n l2)) by (subst l2; rt_ls; rewrite Fss; exact Hss0).
      assert (Q7 : RD.ls_strstart (RD.setL_matchlen n l2) + n + 2 < 65536) by (subst l2; rt_ls; rewrite Fss; lia).
      destruct (m_dfi (Z.to_nat n) (Z.to_nat n + 1) st2 P1 (RD.setL_matchlen n l2) n A2' Hg_st2 Q1 Q2 Q3 Q4 Q5 Q6 Q7)
        as (D1 & D2 & D3).
      cbn [RD.d_cfg] in D1, D3. subst P1. cbn [RD.d_cfg RD.setD_ts] in D1, D3. set (P1 := RD.setD_ts ts' p0) in *.
      subst l2.
      set (l3b := RD.df_insert (Z.to_nat n + 1) (RD.d_cfg p0) n
                    (RD.setL_matchlen n (RD.setL_lookahead (RD.ls_lookahead l1 - RD.ls_matchlen l1) l1))) in *.
      pose proof (lzr_ss _ _ D1) as Ess3. cbn [RD.d_ls RD.setD_ls RD.setL_matchlen RD.ls_strstart] in Ess3.
      assert (A4 : lz_rel (DS.set_strstart (SBlk.deflate_fast_insert (Z.to_nat n) st2)
                             (DS.ds_strstart (SBlk.deflate_fast_insert (Z.to_nat n) st2) + 1))
                          (RD.setD_ls (RD.setL_strstart (RD.ls_strstart l3b + 1) (RD.setL_matchlen 0 l3b)) P1))
        by (apply lz_set_strstart; [exact D1 | rewrite Ess3; reflexivity]).
      cbn [fst snd].
      split; [reflexivity|].
      assert (Hvf : nonlz_view (DS.set_strstart (SBlk.deflate_fast_insert (Z.to_nat n) st2)
                                  (DS.ds_strstart (SBlk.deflate_fast_insert (Z.to_nat n) st2) + 1))
                    = nonlz_view st) by (cbv beta; rewrite <- Hv2, <- D2; reflexivity).
      split.
      * replace (RD.setD_ls (RD.setL_strstart (RD.ls_strstart l3b + 1) (RD.setL_matchlen 0 l3b))
                   (RD.setD_ts ts' (RD.setD_ls l1 p0)))
          with (RD.setD_ls (RD.setL_strstart (RD.ls_strstart l3b + 1) (RD.setL_matchlen 0 l3b))
                   (RD.setD_ls l1 (RD.setD_ts ts' p0))) by (destruct p0; reflexivity).
        eapply m_lz_step; [exact T1 | exact Hvf | exact A4].
      * split; [exact (em_core_frame st _ (MFill2.m_em_of_nonlz _ _ Hvf) T3)|].
        intros E. exact (em_inv_frame st _ (MFill2.m_em_of_nonlz _ _ Hvf) (T4 E)).
    + (* skip them and re-seed the hash *)
      set (mlen := RD.ls_matchlen l1) in *.
      assert (B1 : lz_rel (DS.set_strstart st1 (DS.ds_strstart st1 + mlen))
                          (RD.setD_ls (RD.setL_strstart (RD.ls_strstart l1 + mlen) l2) P1)).
      { apply lz_set_strstart; [exact A1|].
        subst st1. rewrite ds_strstart__set_lookahead, Ess'. reflexivity. }
      set (sb1 := DS.set_strstart st1 (DS.ds_strstart st1 + mlen)) in *.
      assert (B2 : lz_rel (DS.set_match_length sb1 0)
                          (RD.setD_ls (RD.setL_matchlen 0 (RD.setL_strstart (RD.ls_strstart l1 + mlen) l2)) P1))
        by (apply lz_set_match_length; [exact B1 | reflexivity]).
      set (sb2 := DS.set_match_length sb1 0) in *.
      set (l3 := RD.setL_matchlen 0 (RD.setL_strstart (RD.ls_strstart l1 + mlen) l2)) in *.
      assert (Ess2 : DS.ds_strstart sb2 = RD.ls_strstart l1 + mlen).
      { subst sb2 sb1. rewrite ds_strstart__set_match_length, ds_strstart__set_strstart.
        subst st1. rewrite ds_strstart__set_lookahead, Ess'. reflexivity. }
      assert (Ew0 : arr_get (DS.ds_window sb2) (DS.ds_strstart sb2) = RD.ls_window l1 (RD.ls_strstart l1 + mlen)).
      { assert (Hwst : arr_rel (DS.ds_window st) (RD.ls_window l1) 0 65536)
          by (pose proof (lzr_win _ _ Hlz) as W; cbn [RD.d_ls RD.setD_ls] in W; rewrite Fws, Hws in W; exact W).
        rewrite Ess2. subst sb2 sb1 st1.
        rewrite ds_window__set_match_length, ds_window__set_strstart, ds_window__set_lookahead.
        apply Hwst. lia. }
      assert (B3 : lz_rel (DS.set_ins_h sb2 (arr_get (DS.ds_window sb2) (DS.ds_strstart sb2)))
                          (RD.setD_ls (RD.setL_insh (RD.ls_window l1 (RD.ls_strstart l1 + mlen)) l3) P1))
        by (apply lz_set_ins_h; [exact B2 | exact Ew0]).
      set (sb3 := DS.set_ins_h sb2 (arr_get (DS.ds_window sb2) (DS.ds_strstart sb2))) in *.
      assert (Ew1 : arr_get (DS.ds_window sb3) (DS.ds_strstart sb3 + 1) = RD.ls_window l1 (RD.ls_strstart l1 + mlen + 1)).
      { assert (Hwst : arr_rel (DS.ds_window st) (RD.ls_window l1) 0 65536)
          by (pose proof (lzr_win _ _ Hlz) as W; cbn [RD.d_ls RD.setD_ls] in W; rewrite Fws, Hws in W; exact W).
        subst sb3. rewrite ds_strstart__set_ins_h, ds_window__set_ins_h, Ess2. subst sb2 sb1 st1.
        rewrite ds_window__set_match_length, ds_window__set_strstart, ds_window__set_lookahead.
        apply Hwst. lia. }
      assert (Eh : SLz.update_hash sb3 (DS.ds_ins_h sb3) (arr_get (DS.ds_window sb3) (DS.ds_strstart sb3 + 1))
                   = RD.update_hash (RD.d_cfg p0) (RD.ls_window l1 (RD.ls_strstart l1 + mlen))
                       (RD.ls_window l1 (RD.ls_strstart l1 + mlen + 1))).
      { rewrite Ew1. subst sb3. rewrite ds_ins_h__set_ins_h, Ew0.
        apply m_update_hash; [| | exact (cf_hash_mask _ Hc)].
        - rewrite ds_hash_shift__set_ins_h. subst sb2 sb1 st1. rewrite ds_hash_shift__set_match_length,
            ds_hash_shift__set_strstart, ds_hash_shift__set_lookahead, (sg_hash_shift _ Hgst), (cf_hash_shift _ Hc).
          reflexivity.
        - rewrite ds_hash_mask__set_ins_h. subst sb2 sb1 st1. rewrite ds_hash_mask__set_match_length,
            ds_hash_mask__set_strstart, ds_hash_mask__set_lookahead. exact (sg_hash_mask _ Hgst). }
      assert (B4 : lz_rel (DS.set_ins_h sb3 (SLz.update_hash sb3 (DS.ds_ins_h sb3) (arr_get (DS.ds_window sb3) (DS.ds_strstart sb3 + 1))))
                          (RD.setD_ls (RD.setL_insh (RD.update_hash (RD.d_cfg p0) (RD.ls_window l1 (RD.ls_strstart l1 + mlen))
                                                       (RD.ls_window l1 (RD.ls_strstart l1 + mlen + 1))) l3) P1)).
      { pose proof (lz_set_ins_h sb3 P1 _ _ _ B3 Eh) as H. exact H. }
      cbn [fst snd].
      split; [reflexivity|].
      set (sfin := DS.set_ins_h sb3 (SLz.update_hash sb3 (DS.ds_ins_h sb3) (arr_get (DS.ds_window sb3) (DS.ds_strstart sb3 + 1)))) in *.
      assert (Hvf : nonlz_view sfin = nonlz_view st) by reflexivity.
      split.
      * subst P1.
        replace (RD.setD_ls _ (RD.setD_ts ts' (RD.setD_ls l1 p0)))
          with (RD.setD_ls (RD.setL_insh (RD.update_hash (RD.d_cfg p0) (RD.ls_window l1 (RD.ls_strstart l1 + mlen))
                                            (RD.ls_window l1 (RD.ls_strstart l1 + mlen + 1))) l3)
                  (RD.setD_ls l1 (RD.setD_ts ts' p0))) by (subst l3 l2; destruct p0; reflexivity).
        eapply m_lz_step; [exact T1 | exact Hvf | exact B4].
      * split; [exact (em_core_frame st _ (MFill2.m_em_of_nonlz _ _ Hvf) T3)|].
        intros E. exact (em_inv_frame st _ (MFill2.m_em_of_nonlz _ _ Hvf) (T4 E)).
  - (* a literal *)
    assert (Ew : arr_get (DS.ds_window s1) (DS.ds_strstart s1) = RD.ls_window l1 (RD.ls_strstart l1))
      by (rewrite Ess; apply Hrw; rewrite Fss; lia).
    rewrite Ew.
    destruct (pair_tr_tally_lit s1 (RD.setD_ls l1 p0) po pi (RD.ls_window l1 (RD.ls_strstart l1)) Hd1 He1)
      as (T1 & T2 & T3 & T4).
    cbn [RD.d_cfg RD.d_ts RD.setD_ls] in T1, T2, T3, T4 |- *.
    destruct (STr.tr_tally_lit s1 (RD.ls_window l1 (RD.ls_strstart l1))) as [st bf] eqn:ET.
    destruct (RT.tr_tally_lit (RD.ls_window l1 (RD.ls_strstart l1)) (RC.dg_sym_end (RD.d_cfg p0)) (RD.d_ts p0))
      as [bf' ts'] eqn:ER.
    cbn [fst snd] in T1, T2, T3, T4 |- *. subst bf'.
    rewrite rt_ts_ls in T1. set (P1 := RD.setD_ts ts' p0) in *.
    pose proof T1 as T1'. apply m_dst_split in T1' as [Hlz Hnl].
    pose proof (lzr_la _ _ Hlz) as Ela'. pose proof (lzr_ss _ _ Hlz) as Ess'.
    cbn [RD.d_ls RD.setD_ls] in Ela', Ess'.
    assert (C1 : lz_rel (DS.set_lookahead st (DS.ds_lookahead st - 1))
                        (RD.setD_ls (RD.setL_lookahead (RD.ls_lookahead l1 - 1) l1) P1))
      by (apply lz_set_lookahead; [exact Hlz | rewrite Ela'; reflexivity]).
    assert (C2 : lz_rel (DS.set_strstart (DS.set_lookahead st (DS.ds_lookahead st - 1))
                           (DS.ds_strstart (DS.set_lookahead st (DS.ds_lookahead st - 1)) + 1))
                        (RD.setD_ls (RD.setL_strstart (RD.ls_strstart l1 + 1)
                                       (RD.setL_lookahead (RD.ls_lookahead l1 - 1) l1)) P1))
      by (apply lz_set_strstart; [exact C1 | rewrite ds_strstart__set_lookahead, Ess'; reflexivity]).
    split; [reflexivity|].
    set (sfin := DS.set_strstart (DS.set_lookahead st (DS.ds_lookahead st - 1))
                   (DS.ds_strstart (DS.set_lookahead st (DS.ds_lookahead st - 1)) + 1)) in *.
    assert (Hvf : nonlz_view sfin = nonlz_view st) by reflexivity.
    split.
    + subst P1.
      replace (RD.setD_ls (RD.setL_strstart (RD.ls_strstart l1 + 1) (RD.setL_lookahead (RD.ls_lookahead l1 - 1) l1))
                 (RD.setD_ts ts' (RD.setD_ls l1 p0)))
        with (RD.setD_ls (RD.setL_strstart (RD.ls_strstart l1 + 1) (RD.setL_lookahead (RD.ls_lookahead l1 - 1) l1))
                 (RD.setD_ls l1 (RD.setD_ts ts' p0))) by (destruct p0; reflexivity).
      eapply m_lz_step; [exact T1 | exact Hvf | exact C2].
    + split; [exact (em_core_frame st _ (MFill2.m_em_of_nonlz _ _ Hvf) T3)|].
      intros E. exact (em_inv_frame st _ (MFill2.m_em_of_nonlz _ _ Hvf) (T4 E)).
Qed.
