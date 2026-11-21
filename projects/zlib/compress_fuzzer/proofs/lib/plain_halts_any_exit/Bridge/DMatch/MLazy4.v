(** * Bridge.DMatch.MLazy4 — group M: pair D15, S5's three exits against RT's
    ([m_slow_A], [m_slow_B], [m_slow_C]).

    Branch A emits the previous match: S5 passes the distance as
    [wrap32 (strstart - 1 - prev_match)], RT's raw distance because the match
    is live (group R's [ms_slow_emit] and [ms_wrap_dist]); S5's
    [wrap32 (lookahead - (prev_length - 1))] and
    [max_insert = wrap32 (strstart + lookahead - 3)] are exact because the
    pending match fits the lookahead ([ms_slow_inv]) and was found at
    [strstart - 1 >= 0] ([mt_pend]).  The insert loop is [MLazy2.m_dsi].
    Branch B emits the pending literal at [strstart - 1] ([mt_ma]) and may
    flush in the middle (group D's [pair_flush_block_only]).  The tallies
    are group D's pairs. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MFill1 MFast1 MFast2
  MFast4 MFast5 MLazy1 MLazy2 MLazy3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require MFill2 MFill3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.
Module SBlk := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk.
Module STr := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Trees.

Lemma fb_lz_frame : forall t t',
  fb_lz t -> RD.d_cfg t' = RD.d_cfg t ->
  RD.ls_windowsize (RD.d_ls t') = RD.ls_windowsize (RD.d_ls t) ->
  RD.ls_strstart (RD.d_ls t') = RD.ls_strstart (RD.d_ls t) ->
  RD.ls_lookahead (RD.d_ls t') = RD.ls_lookahead (RD.d_ls t) ->
  RD.ls_blockstart (RD.d_ls t') = RD.ls_blockstart (RD.d_ls t) ->
  RD.ls_window (RD.d_ls t') = RD.ls_window (RD.d_ls t) ->
  fb_lz t'.
Proof.
  intros t t' H E1 E2 E3 E4 E5 E6. unfold fb_lz in *. rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.

(* ------------------------------------------------------------------------- *)
(* 1.  Branch C: the current string becomes the pending one                  *)
(* ------------------------------------------------------------------------- *)

Theorem m_slow_C : forall s2 t2 po pi,
  dst_rel s2 t2 po pi -> em_inv s2 ->
  dst_rel (s5_slow_C s2) (rt_slow_C t2) po pi /\ em_inv (s5_slow_C s2).
Proof.
  intros s2 t2 po pi Hd He.
  pose proof Hd as (_ & Hl & _).
  assert (Hl0 : lz_rel s2 (RD.setD_ls (RD.d_ls t2) t2)) by (rewrite rt_setD_ls_eta; exact Hl).
  pose proof (lzr_ss _ _ Hl) as Ess. pose proof (lzr_la _ _ Hl) as Ela.
  assert (A1 : lz_rel (DS.set_match_available s2 1) (RD.setD_ls (RD.setL_matchavail 1 (RD.d_ls t2)) t2))
    by (apply lz_set_match_available; [exact Hl0 | reflexivity]).
  assert (A2 : lz_rel (DS.set_strstart (DS.set_match_available s2 1) (DS.ds_strstart (DS.set_match_available s2 1) + 1))
                      (RD.setD_ls (RD.setL_strstart (RD.ls_strstart (RD.d_ls t2) + 1)
                                     (RD.setL_matchavail 1 (RD.d_ls t2))) t2))
    by (apply lz_set_strstart; [exact A1 | rewrite ds_strstart__set_match_available, Ess; reflexivity]).
  set (sa := DS.set_strstart (DS.set_match_available s2 1) (DS.ds_strstart (DS.set_match_available s2 1) + 1)) in *.
  assert (A3 : lz_rel (DS.set_lookahead sa (DS.ds_lookahead sa - 1))
                      (RD.setD_ls (RD.setL_lookahead (RD.ls_lookahead (RD.d_ls t2) - 1)
                                     (RD.setL_strstart (RD.ls_strstart (RD.d_ls t2) + 1)
                                        (RD.setL_matchavail 1 (RD.d_ls t2)))) t2))
    by (apply lz_set_lookahead; [exact A2 |
          subst sa; rewrite ds_lookahead__set_strstart, ds_lookahead__set_match_available, Ela; reflexivity]).
  assert (Hv : nonlz_view (DS.set_lookahead sa (DS.ds_lookahead sa - 1)) = nonlz_view s2) by reflexivity.
  unfold s5_slow_C, rt_slow_C. cbv zeta. fold sa.
  split.
  - eapply m_lz_step; [exact Hd | exact Hv | exact A3].
  - exact (em_inv_frame s2 _ (MFill2.m_em_of_nonlz _ _ Hv) He).
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  Branch B: the pending literal                                         *)
(* ------------------------------------------------------------------------- *)

(** The [strstart++; lookahead--] that ends branch B. *)
Lemma m_ss_la_step : forall s4 t4 po pi,
  dst_rel s4 t4 po pi ->
  let s5 := DS.set_lookahead (DS.set_strstart s4 (DS.ds_strstart s4 + 1))
              (DS.ds_lookahead (DS.set_strstart s4 (DS.ds_strstart s4 + 1)) - 1) in
  let t5 := RD.setD_ls (RD.setL_lookahead (RD.ls_lookahead (RD.d_ls t4) - 1)
                         (RD.setL_strstart (RD.ls_strstart (RD.d_ls t4) + 1) (RD.d_ls t4))) t4 in
  dst_rel s5 t5 po pi /\ nonlz_view s5 = nonlz_view s4.
Proof.
  intros s4 t4 po pi Hd s5 t5. subst s5 t5.
  pose proof Hd as (_ & Hl & _).
  assert (Hl0 : lz_rel s4 (RD.setD_ls (RD.d_ls t4) t4)) by (rewrite rt_setD_ls_eta; exact Hl).
  pose proof (lzr_ss _ _ Hl) as Ess. pose proof (lzr_la _ _ Hl) as Ela.
  assert (A1 : lz_rel (DS.set_strstart s4 (DS.ds_strstart s4 + 1))
                      (RD.setD_ls (RD.setL_strstart (RD.ls_strstart (RD.d_ls t4) + 1) (RD.d_ls t4)) t4))
    by (apply lz_set_strstart; [exact Hl0 | rewrite Ess; reflexivity]).
  assert (A2 : lz_rel (DS.set_lookahead (DS.set_strstart s4 (DS.ds_strstart s4 + 1))
                         (DS.ds_lookahead (DS.set_strstart s4 (DS.ds_strstart s4 + 1)) - 1))
                      (RD.setD_ls (RD.setL_lookahead (RD.ls_lookahead (RD.d_ls t4) - 1)
                                     (RD.setL_strstart (RD.ls_strstart (RD.d_ls t4) + 1) (RD.d_ls t4))) t4))
    by (apply lz_set_lookahead; [exact A1 | rewrite ds_lookahead__set_strstart, Ela; reflexivity]).
  split; [eapply m_lz_step; [exact Hd | reflexivity | exact A2] | reflexivity].
Qed.

Theorem m_slow_B : forall s2 p0 po pi,
  dst_rel s2 (RD.setD_ls (RK.ds_l2 p0) p0) po pi -> em_inv s2 -> mt_inv p0 ->
  RD.ls_matchavail (RK.ds_l2 p0) <> 0 ->
  dst_rel (s5_slow_B_state s2) (rt_slow_B_state (RD.setD_ls (RK.ds_l2 p0) p0)) po pi
  /\ (DS.cs_avail_out (DS.ds_strm (s5_slow_B_state s2)) <> 0 -> em_inv (s5_slow_B_state s2)).
Proof.
  intros s2 p0 po pi Hd1 He1 Hm Hma2.
  pose proof (mt_ma p0 Hm) as Hma0. pose proof (mt_ws p0 Hm) as Hws.
  destruct (rt_ds_l2_facts p0 Hm) as (Fw & Fss & Fla & Fbs & Fhw & Fma & Fins & Fws & Fpl & Fpm & Fml & Fms).
  set (l2 := RK.ds_l2 p0) in *.
  assert (Hss1 : 1 <= RD.ls_strstart l2) by (rewrite Fss; destruct Hma0 as [M|[M1 M2]]; [rewrite Fma in Hma2; lia | exact M2]).
  pose proof (RK.mi_room _ (mt_ms p0 Hm)) as Hrm. pose proof (RK.mi_look _ (mt_ms p0 Hm)) as Hlk.
  rewrite Hws in Hrm.
  pose proof Hd1 as (_ & Hl1 & _).
  pose proof (lzr_ss _ _ Hl1) as Ess. pose proof (lzr_win _ _ Hl1) as Hrw.
  cbn [RD.d_ls RD.setD_ls] in Ess, Hrw. rewrite Fws, Hws in Hrw.
  assert (Ew : arr_get (DS.ds_window s2) (DS.ds_strstart s2 - 1) = RD.ls_window l2 (RD.ls_strstart l2 - 1))
    by (rewrite Ess; apply Hrw; rewrite Fss in *; lia).
  unfold s5_slow_B_state, rt_slow_B_state. cbv zeta. cbn [RD.d_ls RD.d_cfg RD.d_ts RD.setD_ls].
  rewrite Ew.
  destruct (pair_tr_tally_lit s2 (RD.setD_ls l2 p0) po pi (RD.ls_window l2 (RD.ls_strstart l2 - 1)) Hd1 He1)
    as (T1 & T2 & T3 & T4).
  cbn [RD.d_cfg RD.d_ts RD.setD_ls] in T1, T2, T3, T4.
  destruct (STr.tr_tally_lit s2 (RD.ls_window l2 (RD.ls_strstart l2 - 1))) as [st bf] eqn:ET.
  destruct (RT.tr_tally_lit (RD.ls_window l2 (RD.ls_strstart l2 - 1)) (RC.dg_sym_end (RD.d_cfg p0)) (RD.d_ts p0))
    as [bf' ts'] eqn:ER.
  cbn [fst snd] in T1, T2, T3, T4 |- *. subst bf'.
  destruct bf.
  - (* flush in the middle *)
    assert (Hfb : fb_lz (RD.setD_ts ts' (RD.setD_ls l2 p0))).
    { apply (fb_lz_frame p0); [exact (m_fb_lz p0 Hm) | reflexivity | | | | |]; cbn [RD.d_ls RD.setD_ls RD.setD_ts];
        assumption. }
    destruct (pair_flush_block_only st _ po pi 0 T1 T3 Hfb ltac:(lia)) as [Y1 Y2].
    destruct (m_ss_la_step _ _ po pi Y1) as [Z1 Z2]. cbv zeta in Z1, Z2.
    split; [exact Z1|].
    intros Hav. apply (em_inv_frame _ _ (MFill2.m_em_of_nonlz _ _ Z2)). apply Y2.
    rewrite ds_strm__set_lookahead, ds_strm__set_strstart in Hav. exact Hav.
  - destruct (m_ss_la_step _ _ po pi T1) as [Z1 Z2]. cbv zeta in Z1, Z2.
    split; [exact Z1|].
    intros _. exact (em_inv_frame _ _ (MFill2.m_em_of_nonlz _ _ Z2) (T4 eq_refl)).
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  Branch A: the previous match                                          *)
(* ------------------------------------------------------------------------- *)

Theorem m_slow_A : forall s2 p0 po pi,
  dst_rel s2 (RD.setD_ls (RK.ds_l2 p0) p0) po pi -> em_inv s2 -> mt_inv p0 ->
  4 <= RC.dg_level (RD.d_cfg p0) <= 9 -> 1 <= RD.ls_lookahead (RD.d_ls p0) ->
  RC.MIN_MATCH <= RD.ls_prevlen (RK.ds_l2 p0) -> RD.ls_matchlen (RK.ds_l2 p0) <= RD.ls_prevlen (RK.ds_l2 p0) ->
  snd (s5_slow_A s2) = fst (rt_slow_A (RD.setD_ls (RK.ds_l2 p0) p0))
  /\ dst_rel (fst (s5_slow_A s2)) (snd (rt_slow_A (RD.setD_ls (RK.ds_l2 p0) p0))) po pi
  /\ em_core (fst (s5_slow_A s2))
  /\ (snd (s5_slow_A s2) = false -> em_inv (fst (s5_slow_A s2))).
Proof.
  intros s2 p0 po pi Hd1 He1 Hm Hlev Hla1 Hpl3 Hmlpl.
  pose proof (m_cfg_facts p0 Hm) as Hc. pose proof (mt_ms p0 Hm) as Hms.
  pose proof (mt_ws p0 Hm) as Hws.
  pose proof (RK.mi_room _ Hms) as Hrm. pose proof (RK.mi_str _ Hms) as Hss0. rewrite Hws in Hrm.
  pose proof (RK.ms_slow_emit p0 Hms (mt_slow p0 Hm ltac:(lia)) Hla1 Hpl3 Hmlpl) as Hlive.
  rewrite (cf_max_dist _ Hc) in Hlive.
  destruct (mt_slow p0 Hm ltac:(lia)) as [S1 _].
  pose proof (mt_pend p0 Hm) as Hpend.
  destruct (rt_ds_l2_facts p0 Hm) as (Fw & Fss & Fla & Fbs & Fhw & Fma & Fins & Fws & Fpl & Fpm & Fml & Fms).
  set (l2 := RK.ds_l2 p0) in *.
  change RC.MIN_MATCH with 3 in *.
  assert (Hla2 : RD.ls_prevlen l2 - 1 <= RD.ls_lookahead l2) by (rewrite Fpl, Fla; lia).
  assert (Hss1 : 1 <= RD.ls_strstart l2) by (rewrite Fss; apply Hpend; rewrite <- Fpl; exact Hpl3).
  assert (Hroom2 : RD.ls_strstart l2 + RD.ls_lookahead l2 <= 65536) by (rewrite Fss, Fla; exact Hrm).
  assert (Hpl258 : RD.ls_prevlen l2 <= 258) by (rewrite Fpl; pose proof (mt_ml p0 Hm); lia).
  pose proof Hd1 as Hd1'. apply m_dst_split in Hd1' as [Hl1 Hn1].
  pose proof (lzr_pl _ _ Hl1) as Epl. pose proof (lzr_ss _ _ Hl1) as Ess.
  pose proof (lzr_la _ _ Hl1) as Ela. pose proof (lzr_pm _ _ Hl1) as Epm.
  cbn [RD.d_ls RD.setD_ls] in Epl, Ess, Ela, Epm.
  unfold s5_slow_A, rt_slow_A. cbv zeta. cbn [RD.d_ls RD.d_cfg RD.d_ts RD.setD_ls].
  rewrite Epl, Ess, Ela, Epm. change DS.MIN_MATCH with 3. change RC.MIN_MATCH with 3.
  rewrite (wrap32_id (RD.ls_strstart l2 + RD.ls_lookahead l2 - 3)) by (mpow; lia).
  rewrite (RK.ms_wrap_dist (RD.ls_strstart l2 - 1) (RD.ls_prevmatch l2)) by (mpow; lia).
  set (mi := RD.ls_strstart l2 + RD.ls_lookahead l2 - 3).
  set (dist := RD.ls_strstart l2 - 1 - RD.ls_prevmatch l2) in *.
  destruct (pair_tr_tally_dist s2 (RD.setD_ls l2 p0) po pi dist (RD.ls_prevlen l2 - 3) Hd1 He1 ltac:(lia))
    as (T1 & T2 & T3 & T4).
  cbn [RD.d_cfg RD.d_ts RD.setD_ls] in T1, T2, T3, T4.
  destruct (STr.tr_tally_dist s2 dist (RD.ls_prevlen l2 - 3)) as [st bf] eqn:ET.
  destruct (RT.tr_tally_dist dist (RD.ls_prevlen l2 - 3) (RC.dg_sym_end (RD.d_cfg p0)) (RD.d_ts p0))
    as [bf' ts'] eqn:ER.
  cbn [fst snd] in T1, T2, T3, T4 |- *. subst bf'.
  rewrite rt_ts_ls in T1. set (P1 := RD.setD_ts ts' p0) in *.
  pose proof T1 as T1'. apply m_dst_split in T1' as [Hlz Hnl].
  pose proof (lzr_pl _ _ Hlz) as Epl'. pose proof (lzr_la _ _ Hlz) as Ela'.
  cbn [RD.d_ls RD.setD_ls] in Epl', Ela'.
  assert (Hgt : geom_rel st (RD.setD_ls l2 P1)) by (destruct Hnl; assumption).
  pose proof (MFill3.m_s5_geom_cf st _ Hgt Hc) as Hgst.
  (* lookahead -= prev_length - 1 *)
  rewrite Ela', Epl'.
  rewrite (wrap32_id (RD.ls_lookahead l2 - (RD.ls_prevlen l2 - 1))) by (mpow; lia).
  assert (A1 : lz_rel (DS.set_lookahead st (RD.ls_lookahead l2 - (RD.ls_prevlen l2 - 1)))
                      (RD.setD_ls (RD.setL_lookahead (RD.ls_lookahead l2 - (RD.ls_prevlen l2 - 1)) l2) P1))
    by (apply lz_set_lookahead; [exact Hlz | reflexivity]).
  set (st1 := DS.set_lookahead st (RD.ls_lookahead l2 - (RD.ls_prevlen l2 - 1))) in *.
  (* prev_length -= 2 *)
  assert (Epl1 : DS.ds_prev_length st1 = RD.ls_prevlen l2) by (subst st1; rewrite ds_prev_length__set_lookahead; exact Epl').
  rewrite Epl1.
  set (l3 := RD.setL_prevlen (RD.ls_prevlen l2 - 2)
               (RD.setL_lookahead (RD.ls_lookahead l2 - (RD.ls_prevlen l2 - 1)) l2)) in *.
  assert (A2 : lz_rel (DS.set_prev_length st1 (RD.ls_prevlen l2 - 2)) (RD.setD_ls l3 P1))
    by (apply lz_set_prev_length; [exact A1 | reflexivity]).
  set (st2 := DS.set_prev_length st1 (RD.ls_prevlen l2 - 2)) in *.
  assert (Epl2 : DS.ds_prev_length st2 = RD.ls_prevlen l2 - 2) by (subst st2; rewrite ds_prev_length__set_prev_length; reflexivity).
  rewrite Epl2.
  assert (Ep3 : RD.ls_prevlen l3 = RD.ls_prevlen l2 - 2) by reflexivity.
  rewrite Ep3.
  (* the insert loop *)
  assert (Hv2 : nonlz_view st2 = nonlz_view st) by reflexivity.
  assert (Hg_st2 : s5_geom st2) by (exact (MFill3.m_geom_nonlz st st2 Hv2 Hgst)).
  destruct (m_dsi (Z.to_nat (RD.ls_prevlen l2 - 2)) (Z.to_nat (RD.ls_prevlen l2 - 2) + 1) st2 P1 l3 mi A2 Hg_st2
              ltac:(exact Hc) ltac:(subst l3; rt_ls; rewrite Fws; exact Hws) ltac:(rewrite Ep3; lia)
              ltac:(rewrite Ep3; lia) ltac:(rewrite Ep3; lia) ltac:(subst l3; rt_ls; lia) ltac:(subst mi; lia))
    as (D1 & D2 & D3).
  cbn [RD.d_cfg] in D1, D3. subst P1. cbn [RD.d_cfg RD.setD_ts] in D1, D3. set (P1 := RD.setD_ts ts' p0) in *.
  set (l4 := RD.ds_insert (Z.to_nat (RD.ls_prevlen l2 - 2) + 1) (RD.d_cfg p0) mi l3) in *.
  set (s4 := SBlk.deflate_slow_insert (Z.to_nat (RD.ls_prevlen l2 - 2)) st2 mi) in *.
  (* match_available := 0; match_length := 2; strstart + 1 *)
  pose proof (lzr_ss _ _ D1) as Ess4. cbn [RD.d_ls RD.setD_ls] in Ess4.
  assert (B1 : lz_rel (DS.set_match_available s4 0) (RD.setD_ls (RD.setL_matchavail 0 l4) P1))
    by (apply lz_set_match_available; [exact D1 | reflexivity]).
  assert (B2 : lz_rel (DS.set_match_length (DS.set_match_available s4 0) (3 - 1))
                      (RD.setD_ls (RD.setL_matchlen (3 - 1) (RD.setL_matchavail 0 l4)) P1))
    by (apply lz_set_match_length; [exact B1 | reflexivity]).
  assert (B3 : lz_rel (DS.set_strstart (DS.set_match_length (DS.set_match_available s4 0) (3 - 1))
                         (DS.ds_strstart (DS.set_match_length (DS.set_match_available s4 0) (3 - 1)) + 1))
                      (RD.setD_ls (RD.setL_strstart (RD.ls_strstart l4 + 1)
                                     (RD.setL_matchlen (3 - 1) (RD.setL_matchavail 0 l4))) P1))
    by (apply lz_set_strstart; [exact B2 |
          rewrite ds_strstart__set_match_length, ds_strstart__set_match_available, Ess4; reflexivity]).
  set (sfin := DS.set_strstart (DS.set_match_length (DS.set_match_available s4 0) (3 - 1))
                 (DS.ds_strstart (DS.set_match_length (DS.set_match_available s4 0) (3 - 1)) + 1)) in *.
  assert (Hvf : nonlz_view sfin = nonlz_view st) by (subst sfin; cbv beta; rewrite <- Hv2, <- D2; reflexivity).
  split; [reflexivity|].
  split.
  - subst P1.
    replace (RD.setD_ls (RD.setL_strstart (RD.ls_strstart l4 + 1) (RD.setL_matchlen (3 - 1) (RD.setL_matchavail 0 l4)))
               (RD.setD_ts ts' (RD.setD_ls l2 p0)))
      with (RD.setD_ls (RD.setL_strstart (RD.ls_strstart l4 + 1) (RD.setL_matchlen (3 - 1) (RD.setL_matchavail 0 l4)))
               (RD.setD_ls l2 (RD.setD_ts ts' p0))) by (destruct p0; reflexivity).
    eapply m_lz_step; [exact T1 | exact Hvf | exact B3].
  - split; [exact (em_core_frame st _ (MFill2.m_em_of_nonlz _ _ Hvf) T3)|].
    intros E. exact (em_inv_frame st _ (MFill2.m_em_of_nonlz _ _ Hvf) (T4 E)).
Qed.
