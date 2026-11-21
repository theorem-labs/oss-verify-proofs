(** * Bridge.DMatch.MFast6 — group M: pair D14, one whole [deflate_fast] trip
    ([m_fast_step]).

    S5's [deflate_fast_body] against RT's [df_step]: the top-of-trip fill
    and its early exits ([MFast1.m_early]), the insert and search
    ([MFast2.m_fast_l1]), the emit ([MFast5.m_fast_emit]) and the flush a
    full symbol buffer triggers (group D's [pair_flush_block]).  The trip
    relation [fstep_rel] pairs the two models' outcomes: continue, break, or
    return a block state; after every trip that continues the loop measure
    [zlen zs_in + lookahead] has gone down. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MFill1 MFast1 MFast2
  MFast3 MFast4 MFast5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require MFill2 MFill3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.
Module SBlk := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk.

Definition msr (t : RD.DSt) : Z := Chunk.zlen (RD.zs_in (RD.d_strm t)) + RD.ls_lookahead (RD.d_ls t).

Definition fstep_rel (t0 : RD.DSt) (po pi : list Z) (M0 : Z) (r5 : DS.deflate_state * SBlk.loop_out) (rr : RD.DsStep) : Prop :=
  match r5, rr with
  | (s', SBlk.LCont), RD.DsCont t' => dst_rel s' t' po pi /\ mt_inv t' /\ em_inv s' /\ msr t' < M0
                                     /\ RD.d_cfg t' = RD.d_cfg t0
  | (s', SBlk.LBreak), RD.DsBreak t' => dst_rel s' t' po pi /\ mt_inv t' /\ em_inv s'
  | (s', SBlk.LRet bs), RD.DsRet bs' t' =>
      bs_of bs = bs' /\ dst_rel s' t' po pi /\ mt_inv t'
      /\ (DS.cs_avail_out (DS.ds_strm s') <> 0 -> em_inv s')
  | _, _ => False
  end.

Lemma ds_fill_cfg : forall t, RD.d_cfg (RD.ds_fill t) = RD.d_cfg t.
Proof. intros t. unfold RD.ds_fill, RD.fill_if. destruct (RD.ds_need t); reflexivity. Qed.

Lemma rt_frame_trans : forall a b c, rt_frame a b -> rt_frame b c -> rt_frame a c.
Proof. intros a b c [A1 A2 A3 A4 A5] [B1 B2 B3 B4 B5]. constructor; congruence. Qed.

Lemma s5_flush_none_avail : forall s last,
  snd (SBlk.flush_block s last) = None -> DS.cs_avail_out (DS.ds_strm (fst (SBlk.flush_block s last))) <> 0.
Proof.
  intros s last. unfold SBlk.flush_block. cbv zeta.
  destruct (Z.eqb_spec (DS.cs_avail_out (DS.ds_strm (SLz.flush_block_only s last))) 0); cbn [fst snd];
    [discriminate | intros _; assumption].
Qed.

Lemma fb_lz_of_emit : forall p0 t3, mt_inv p0 -> emit_facts p0 t3 -> fb_lz t3.
Proof.
  intros p0 t3 Hm Ef.
  pose proof (m_cfg_facts p0 Hm) as Hc. pose proof (mt_ms p0 Hm) as Hms.
  destruct Ef as [[F1 F2 F3 F4 F5] Ew Ehw Ema Eml Epl Esum Eadv Ela Ebs Ems Eins Ews].
  destruct (mt_slid p0 Hm) as (slid & Z0 & Z1 & Z2 & Z3 & Z4).
  pose proof (mt_inlen p0 Hm) as Hinl. pose proof (mt_bs p0 Hm) as Hbs. pose proof (mt_win p0 Hm) as Hwin.
  pose proof (RK.mi_winsize _ Hms) as Hwz. pose proof (RK.mi_str _ Hms) as Hst. pose proof (RK.mi_room _ Hms) as Hrm.
  assert (0 <= Chunk.zlen (RD.zs_in (RD.d_strm p0))) by (unfold Chunk.zlen; lia).
  unfold fb_lz. rewrite F1, Ews, Ebs. rewrite (cf_w_size _ Hc) in *.
  split; [lia|]. split; [exact Hwz|]. split; [lia|]. split; [lia|].
  split; [mpow; lia|]. split; [mpow; lia|].
  intros i Hi. rewrite Ew. apply Hwin. lia.
Qed.

Theorem m_fast_step : forall s t po pi flush,
  dst_rel s t po pi -> mt_inv t -> em_inv s -> 1 <= RC.dg_level (RD.d_cfg t) <= 3 ->
  fstep_rel t po pi (msr t) (SBlk.deflate_fast_body s flush) (RD.df_step flush t).
Proof.
  intros s t po pi flush Hd Hm He Hlev.
  destruct (m_early s t po pi flush Hd Hm He) as (E1 & E2 & E3 & E4 & E5 & E6).
  cbv zeta in E1, E2, E3, E4, E5, E6.
  pose proof (RK.ms_df_step flush t (mt_ms t Hm) (mt_fast t Hm ltac:(lia))) as [Rs1 Rs2].
  rewrite m_s5_fast_body_shape. unfold RD.df_step in *. change Base.Z_NO_FLUSH with 0 in *.
  set (p0 := RD.ds_fill t) in *.
  destruct (s5_early s flush) as [s' [o|]] eqn:EE; cbn [fst snd] in E1, E3, E6.
  - destruct o as [| |b]; [destruct E6 | |].
    + (* LBreak *)
      destruct E6 as [C1 C2]. rewrite C1, C2. cbn [fstep_rel].
      split; [exact E1|]. split; [exact E2 | exact E3].
    + (* LRet need_more *)
      destruct E6 as [Eb C1]. subst b. rewrite C1. cbn [fstep_rel].
      split; [reflexivity|]. split; [exact E1|]. split; [exact E2|]. intros _. exact E3.
  - destruct E6 as (C1 & C2 & Hla1). rewrite C1, C2 in *. rewrite m_rt_df_body_shape in *.
    assert (Hlev' : 1 <= RC.dg_level (RD.d_cfg p0) <= 3) by (subst p0; unfold RD.ds_fill, RD.fill_if;
      destruct (RD.ds_need t); [unfold RD.fill_window; cbv zeta; cbn [RD.d_cfg RD.setD_ls RD.setD_strm]|]; lia).
    destruct (m_fast_l1 s' p0 po pi E1 E2 E4 ltac:(lia)) as [L1 L2].
    pose proof (m_lz_step s' (s5_fast_l1 s') p0 (RK.df_l1 p0) po pi E1 L2 L1) as Hd1.
    assert (He1 : em_inv (s5_fast_l1 s')) by (exact (em_inv_frame s' _ (MFill2.m_em_of_nonlz _ _ L2) E3)).
    destruct (m_fast_emit (s5_fast_l1 s') p0 po pi Hd1 He1 E2 Hlev' E4 Hla1) as (X1 & X2 & X3 & X4).
    pose proof (rt_fast_emit_facts p0 E2 ltac:(lia) E4 Hla1) as Ef.
    pose proof (fb_lz_of_emit p0 _ E2 Ef) as Hfb.
    destruct (s5_fast_emit (s5_fast_l1 s')) as [s3 bf] eqn:ES.
    destruct (rt_fast_emit p0) as [bf' t3] eqn:ER.
    cbn [fst snd] in X1, X2, X3, X4, Ef, Hfb, Rs1, Rs2 |- *. subst bf'.
    destruct Ef as [EF Ew Ehw Ema Eml Epl Esum Eadv Ela Ebs Ems Eins Ews].
    pose proof (mt_ma p0 E2) as Hma0. pose proof (mt_ml p0 E2) as Hml0. pose proof (mt_level p0 E2) as Hlv0.
    unfold s5_flush_step, rt_flush_step in *.
    destruct bf.
    + (* a flush *)
      destruct (pair_flush_block s3 t3 po pi 0 X2 X3 Hfb ltac:(lia)) as (Y1 & Y2 & Y3).
      destruct (rt_fb_frame 0 t3) as [FF FL].
      pose proof (s5_flush_none_avail s3 0) as Hnav.
      destruct (SBlk.flush_block s3 0) as [s4 r5] eqn:EF5.
      destruct (RD.flush_block 0 t3) as [r4 t4] eqn:EF4.
      cbn [fst snd] in Y1, Y2, Y3, FF, FL, Hnav, Rs1, Rs2.
      assert (FR : rt_frame p0 t4) by exact (rt_frame_trans _ _ _ EF FF).
      assert (Hmt4 : mt_inv t4).
      { apply (mt_inv_trip p0 t4 E2).
        - destruct r4; exact Rs1.
        - intros _. destruct r4; exact Rs2.
        - intros Hq. exfalso. rewrite (rf_cfg _ _ FR) in Hq. lia.
        - exact FR.
        - rewrite FL. rt_ls. exact Ew.
        - rewrite FL. rt_ls. exact Ehw.
        - rewrite FL. rt_ls. rewrite Ema. destruct Hma0 as [M|[M1 M2]]; [left; exact M | right; split; [exact M1 | lia]].
        - rewrite FL. rt_ls. lia.
        - rewrite FL. rt_ls. rewrite Epl. exact (proj2 Hml0).
        - rewrite FL. rt_ls. exact Esum.
        - rewrite FL. rt_ls. lia.
        - rewrite FL. rt_ls. right; lia.
        - rewrite FL. rt_ls. destruct Ems as [M|M]; [left; exact M | right; lia].
        - rewrite FL. rt_ls. intros Hq. change RC.MIN_MATCH with 3 in Hq. lia. }
      destruct r5 as [bs|]; cbn [option_map] in Y2; subst r4; cbn [fstep_rel].
      * split; [reflexivity|]. split; [exact Y1|]. split; [exact Hmt4 | exact Y3].
      * split; [exact Y1|]. split; [exact Hmt4|]. split; [exact (Y3 (Hnav eq_refl))|].
        split; [|rewrite (rf_cfg _ _ FR); subst p0; apply ds_fill_cfg].
        unfold msr. rewrite (rf_in _ _ FF), FL. rt_ls. rewrite (rf_in _ _ EF). unfold msr in E5.
        subst p0. lia.
    + (* no flush *)
      cbn [fstep_rel].
      split; [exact X2|]. split.
      * apply (mt_inv_trip p0 t3 E2 Rs1 (fun _ => Rs2)).
        -- intros Hq. exfalso. rewrite (rf_cfg _ _ EF) in Hq. lia.
        -- exact EF.
        -- exact Ew.
        -- exact Ehw.
        -- rewrite Ema. destruct Hma0 as [M|[M1 M2]]; [left; exact M | right; split; [exact M1 | lia]].
        -- lia.
        -- rewrite Epl. exact (proj2 Hml0).
        -- exact Esum.
        -- lia.
        -- left; exact Ebs.
        -- destruct Ems as [M|M]; [left; exact M | right; lia].
        -- intros Hq. change RC.MIN_MATCH with 3 in Hq. lia.
      * split; [exact (X4 eq_refl)|].
        split; [|rewrite (rf_cfg _ _ EF); subst p0; apply ds_fill_cfg].
        unfold msr. rewrite (rf_in _ _ EF). unfold msr in E5. subst p0. lia.
Qed.
