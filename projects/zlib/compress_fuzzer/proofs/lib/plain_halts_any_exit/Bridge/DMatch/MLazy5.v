(** * Bridge.DMatch.MLazy5 — group M: pair D15, one whole [deflate_slow] trip
    ([m_slow_step]).

    S5's [deflate_slow_body] against RT's [ds_step]: the top-of-trip fill
    and its early exits ([MFast1.m_early], shared with deflate_fast), the
    insert and lazy search ([MLazy1.m_slow_l2]), then one of the three exits
    ([MLazy4]) with the flush of branch A (group D's [pair_flush_block]).
    The trip relation is deflate_fast's [MFast6.fstep_rel]; the loop
    measure [zlen zs_in + lookahead] goes down on every trip that
    continues. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MFill1 MFast1 MFast4
  MFast6 MLazy1 MLazy3 MLazy4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require MFill2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.
Module SBlk := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk.

Lemma msr_tf : forall t p0 t3,
  trip_facts p0 t3 ->
  Chunk.zlen (RD.zs_in (RD.d_strm p0)) + RD.ls_lookahead (RD.d_ls p0) = msr t ->
  msr t3 < msr t.
Proof.
  intros t p0 t3 [[F1 F2 F3 F4 F5] Ew Ehw Ema Eml Epl Esum Eadv Ela Ebs Ems Epend Ews] E.
  unfold msr in *. rewrite F3. lia.
Qed.

Lemma mt_inv_slow_tf : forall p0 t3,
  mt_inv p0 -> 4 <= RC.dg_level (RD.d_cfg p0) -> RK.ms_inv t3 -> RK.ms_slow_inv t3 ->
  trip_facts p0 t3 -> mt_inv t3.
Proof.
  intros p0 t3 Hm Hlev Hms Hsl Tf.
  apply (mt_inv_of_tf p0 t3 Hm Hms); [| intros _; exact Hsl | exact Tf].
  intros Hq. exfalso. rewrite (rf_cfg _ _ (tf_frame _ _ Tf)) in Hq. lia.
Qed.

Theorem m_slow_step : forall s t po pi flush,
  dst_rel s t po pi -> mt_inv t -> em_inv s -> 4 <= RC.dg_level (RD.d_cfg t) <= 9 ->
  fstep_rel t po pi (msr t) (SBlk.deflate_slow_body s flush) (RD.ds_step flush t).
Proof.
  intros s t po pi flush Hd Hm He Hlev.
  destruct (m_early s t po pi flush Hd Hm He) as (E1 & E2 & E3 & E4 & E5 & E6).
  cbv zeta in E1, E2, E3, E4, E5, E6.
  pose proof (RK.ms_ds_step flush t (mt_ms t Hm) (mt_slow t Hm ltac:(lia))) as [Rs1 Rs2].
  rewrite m_s5_slow_body_shape. unfold RD.ds_step in *. change Base.Z_NO_FLUSH with 0 in *.
  set (p0 := RD.ds_fill t) in *.
  assert (Ecfg : RD.d_cfg p0 = RD.d_cfg t) by (subst p0; apply ds_fill_cfg).
  destruct (s5_early s flush) as [s' [o|]] eqn:EE; cbn [fst snd] in E1, E3, E6.
  - destruct o as [| |b]; [destruct E6 | |].
    + (* LBreak *)
      destruct E6 as [C1 C2]. rewrite C1, C2. cbn [fstep_rel].
      split; [exact E1|]. split; [exact E2 | exact E3].
    + (* LRet need_more *)
      destruct E6 as [Eb C1]. subst b. rewrite C1. cbn [fstep_rel].
      split; [reflexivity|]. split; [exact E1|]. split; [exact E2|]. intros _. exact E3.
  - destruct E6 as (C1 & C2 & Hla1). rewrite C1, C2 in *. rewrite m_rt_ds_body_shape in *.
    assert (Hlev' : 4 <= RC.dg_level (RD.d_cfg p0) <= 9) by (rewrite Ecfg; exact Hlev).
    destruct (m_slow_l2 s' p0 po pi E1 E2 E4 ltac:(lia)) as [L1 L2].
    pose proof (m_lz_step s' (s5_slow_l2 s') p0 (RK.ds_l2 p0) po pi E1 L2 L1) as Hd1.
    assert (He1 : em_inv (s5_slow_l2 s')) by (exact (em_inv_frame s' _ (MFill2.m_em_of_nonlz _ _ L2) E3)).
    set (s2 := s5_slow_l2 s') in *.
    pose proof Hd1 as (_ & Hl1 & _).
    pose proof (lzr_pl _ _ Hl1) as Epl. pose proof (lzr_ml _ _ Hl1) as Eml. pose proof (lzr_ma _ _ Hl1) as Ema.
    cbn [RD.d_ls RD.setD_ls] in Epl, Eml, Ema.
    unfold s5_slow_emit, rt_slow_emit in *. cbv zeta in *. cbn [RD.d_ls RD.setD_ls] in *.
    rewrite Epl, Eml, Ema. change DS.MIN_MATCH with RC.MIN_MATCH.
    destruct ((RC.MIN_MATCH <=? RD.ls_prevlen (RK.ds_l2 p0))
              && (RD.ls_matchlen (RK.ds_l2 p0) <=? RD.ls_prevlen (RK.ds_l2 p0))) eqn:EA.
    + (* branch A: the previous match, then maybe a flush *)
      apply andb_prop in EA as [EA1 EA2]. apply Z.leb_le in EA1, EA2.
      destruct (m_slow_A s2 p0 po pi Hd1 He1 E2 Hlev' Hla1 EA1 EA2) as (X1 & X2 & X3 & X4).
      pose proof (rt_slow_A_facts p0 E2 ltac:(lia) Hla1 EA1 EA2) as Tf.
      destruct (s5_slow_A s2) as [s3 bf] eqn:ES.
      destruct (rt_slow_A (RD.setD_ls (RK.ds_l2 p0) p0)) as [bf' t3] eqn:ER.
      cbn [fst snd] in X1, X2, X3, X4, Tf, Rs1, Rs2 |- *. subst bf'.
      unfold s5_flush_step, rt_flush_step in *.
      destruct bf.
      * destruct (pair_flush_block s3 t3 po pi 0 X2 X3 (fb_lz_of_tf p0 t3 E2 Tf) ltac:(lia)) as (Y1 & Y2 & Y3).
        pose proof (tf_flush p0 t3 0 Tf) as Tf4.
        pose proof (s5_flush_none_avail s3 0) as Hnav.
        destruct (SBlk.flush_block s3 0) as [s4 r5] eqn:EF5.
        destruct (RD.flush_block 0 t3) as [r4 t4] eqn:EF4.
        cbn [fst snd] in Y1, Y2, Y3, Tf4, Hnav, Rs1, Rs2.
        assert (Hmt4 : mt_inv t4)
          by (apply (mt_inv_slow_tf p0 t4 E2 ltac:(lia)); [destruct r4; exact Rs1 | destruct r4; exact Rs2 | exact Tf4]).
        destruct r5 as [bs|]; cbn [option_map] in Y2; subst r4; cbn [fstep_rel].
        -- split; [reflexivity|]. split; [exact Y1|]. split; [exact Hmt4 | exact Y3].
        -- split; [exact Y1|]. split; [exact Hmt4|]. split; [exact (Y3 (Hnav eq_refl))|].
           split; [exact (msr_tf t p0 t4 Tf4 E5)|].
           rewrite (rf_cfg _ _ (tf_frame _ _ Tf4)). exact Ecfg.
      * cbn [fstep_rel].
        split; [exact X2|].
        split; [exact (mt_inv_slow_tf p0 t3 E2 ltac:(lia) Rs1 Rs2 Tf)|].
        split; [exact (X4 eq_refl)|].
        split; [exact (msr_tf t p0 t3 Tf E5)|].
        rewrite (rf_cfg _ _ (tf_frame _ _ Tf)). exact Ecfg.
    + destruct (Z.eqb_spec (RD.ls_matchavail (RK.ds_l2 p0)) 0) as [E0|Hma2]; cbn [negb] in *.
      * (* branch C: the current string becomes the pending one *)
        destruct (m_slow_C s2 (RD.setD_ls (RK.ds_l2 p0) p0) po pi Hd1 He1) as [Y1 Y2].
        pose proof (rt_slow_C_facts p0 E2 Hla1) as Tf.
        cbn [fstep_rel].
        split; [exact Y1|].
        split; [exact (mt_inv_slow_tf p0 _ E2 ltac:(lia) Rs1 Rs2 Tf)|].
        split; [exact Y2|].
        split; [exact (msr_tf t p0 _ Tf E5)|].
        rewrite (rf_cfg _ _ (tf_frame _ _ Tf)). exact Ecfg.
      * (* branch B: the pending literal *)
        destruct (m_slow_B s2 p0 po pi Hd1 He1 E2 Hma2) as [Y1 Y2].
        pose proof (rt_slow_B_facts p0 E2 Hla1 Hma2) as Tf.
        assert (Hav : DS.cs_avail_out (DS.ds_strm (s5_slow_B_state s2))
                      = RD.zs_availout (RD.d_strm (rt_slow_B_state (RD.setD_ls (RK.ds_l2 p0) p0)))).
        { pose proof Y1 as (_ & _ & _ & _ & _ & Hst). unfold strm_rel in Hst. cbv zeta in Hst.
          destruct Hst as (_ & _ & _ & _ & _ & _ & _ & Hz & _). symmetry. exact Hz. }
        unfold s5_slow_B, rt_slow_B in *. cbv zeta in *. rewrite Hav.
        destruct (Z.eqb_spec (RD.zs_availout (RD.d_strm (rt_slow_B_state (RD.setD_ls (RK.ds_l2 p0) p0)))) 0)
          as [Z0|Z0]; cbn [fstep_rel].
        -- split; [reflexivity|]. split; [exact Y1|].
           split; [exact (mt_inv_slow_tf p0 _ E2 ltac:(lia) Rs1 Rs2 Tf)|]. exact Y2.
        -- split; [exact Y1|].
           split; [exact (mt_inv_slow_tf p0 _ E2 ltac:(lia) Rs1 Rs2 Tf)|].
           split; [apply Y2; rewrite Hav; exact Z0|].
           split; [exact (msr_tf t p0 _ Tf E5)|].
           rewrite (rf_cfg _ _ (tf_frame _ _ Tf)). exact Ecfg.
Qed.
