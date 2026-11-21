(** * Bridge.DMatch.MFill4 — group M: pair D17b, [fill_window] whole.

    - [m_fw_loop]: the loops in lockstep.  S5 runs at most 263 trips, RT at
      most [avail_in + 2]; the induction carries both measures at once: a
      trip that does not stop grows the lookahead (the loop continues only
      below 262) and shrinks the unread input ([MFill3.m_fw_body]).
    - [m_highwater]: the [WIN_INIT] zero-fill.
    - [m_fill_window]: [DMatchIface.dm_fill_window].  The [ms_*] part of
      [mt_inv] afterwards is group R's [RiskIface.ms_fill]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require DEmitDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MReadBuf MFill1 MFill2 MFill3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.

(* ------------------------------------------------------------------------- *)
(* 1.  The loops                                                             *)
(* ------------------------------------------------------------------------- *)

Lemma m_avail_zlen : forall s t po pi,
  dst_rel s t po pi -> DS.cs_avail_in (DS.ds_strm s) = Chunk.zlen (RD.zs_in (RD.d_strm t)).
Proof.
  intros s t po pi H. destruct H as (_ & _ & _ & _ & _ & Hst). unfold strm_rel in Hst. cbv zeta in Hst.
  destruct Hst as (Hni & Hai & Hfit & Hby & Hin & _). rewrite <- Hin. symmetry. apply m_zlen_slice. lia.
Qed.

Theorem m_fw_loop : forall n m s t po pi,
  dst_rel s t po pi -> fw_inv t -> RD.ls_lookahead (RD.d_ls t) < 262 ->
  262 - RD.ls_lookahead (RD.d_ls t) <= Z.of_nat n ->
  Chunk.zlen (RD.zs_in (RD.d_strm t)) < Z.of_nat m ->
  let r := RD.fw_loop m (RD.d_cfg t) (RD.d_wrap t) (RD.d_ls t) (RD.d_strm t) in
  let t' := RD.setD_strm (snd r) (RD.setD_ls (fst r) t) in
  dst_rel (SLz.fill_window_loop n s 32768) t' po pi
  /\ fw_inv t'
  /\ RD.ls_strstart (fst r) + 262 <= 65536
  /\ RD.ls_matchlen (fst r) = RD.ls_matchlen (RD.d_ls t)
  /\ RD.ls_prevlen (fst r) = RD.ls_prevlen (RD.d_ls t)
  /\ DEmitDefs.em_view (SLz.fill_window_loop n s 32768) = DEmitDefs.em_view s.
Proof.
  induction n as [|n IH]; intros m s t po pi Hd Hf Hla Hn Hm r t'; [lia|].
  destruct m as [|m]; [unfold Chunk.zlen in Hm; lia|].
  subst r t'. cbn [SLz.fill_window_loop RD.fw_loop].
  destruct (m_fw_body s t po pi Hd Hf Hla) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  cbv zeta in B1, B2, B3, B4, B5, B6, B7, B8.
  destruct (SLz.fill_window_body s 32768) as [s1 brk] eqn:EB.
  destruct (RD.fw_step (RD.d_cfg t) (RD.d_wrap t) (RD.d_ls t) (RD.d_strm t)) as [[brk' l1] st1] eqn:ER.
  cbn [fst snd] in B1, B2, B3, B4, B5, B6, B7, B8. subst brk'.
  set (t1 := RD.setD_strm st1 (RD.setD_ls l1 t)) in *.
  destruct brk.
  - cbn [fst snd]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
    split; [exact B5|]. split; [exact B6|exact B8].
  - destruct (B7 eq_refl) as [G1 G2]. clear B7.
    pose proof (lzr_la _ _ (proj1 (proj1 (m_dst_split _ _ _ _) B2))) as Ela.
    pose proof (m_avail_zlen _ _ _ _ B2) as Eav.
    subst t1. cbn [RD.d_ls RD.d_strm RD.setD_ls RD.setD_strm] in Ela, Eav, G1, G2, B4, B5, B6.
    rewrite Ela, Eav.
    change DS.MIN_LOOKAHEAD with 262. change RC.MIN_LOOKAHEAD with 262.
    destruct (Z.ltb_spec (RD.ls_lookahead l1) 262) as [Lt|Ge]; cbn [andb].
    + destruct (Z.eqb_spec (Chunk.zlen (RD.zs_in st1)) 0) as [Z0|Z0]; cbn [negb].
      * cbn [fst snd]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
        split; [exact B5|]. split; [exact B6|exact B8].
      * set (t1 := RD.setD_strm st1 (RD.setD_ls l1 t)) in *.
        assert (I1 : RD.ls_lookahead (RD.d_ls t1) < 262) by exact Lt.
        assert (I2 : 262 - RD.ls_lookahead (RD.d_ls t1) <= Z.of_nat n) by (subst t1; cbn; lia).
        assert (I3 : Chunk.zlen (RD.zs_in (RD.d_strm t1)) < Z.of_nat m) by (subst t1; cbn; lia).
        destruct (IH m s1 t1 po pi B2 B3 I1 I2 I3) as (C1 & C2 & C3 & C4 & C5 & C6).
        cbv zeta in C1, C2, C3, C4, C5, C6. subst t1.
        cbn [RD.d_cfg RD.d_wrap RD.d_ls RD.d_strm RD.setD_ls RD.setD_strm] in C1, C2, C3, C4, C5, C6.
        replace (RD.setD_strm (snd (RD.fw_loop m (RD.d_cfg t) (RD.d_wrap t) l1 st1))
                   (RD.setD_ls (fst (RD.fw_loop m (RD.d_cfg t) (RD.d_wrap t) l1 st1))
                      (RD.setD_strm st1 (RD.setD_ls l1 t))))
          with (RD.setD_strm (snd (RD.fw_loop m (RD.d_cfg t) (RD.d_wrap t) l1 st1))
                   (RD.setD_ls (fst (RD.fw_loop m (RD.d_cfg t) (RD.d_wrap t) l1 st1)) t))
          in C1, C2 by (destruct t; reflexivity).
        split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
        split; [rewrite C4; exact B5|]. split; [rewrite C5; exact B6|]. rewrite C6. exact B8.
    + cbn [fst snd]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
      split; [exact B5|]. split; [exact B6|exact B8].
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The WIN_INIT zero-fill                                                *)
(* ------------------------------------------------------------------------- *)

(** What [fw_highwater] changes on RT's side: the window (zeroes only) and
    [high_water] (up to the window end); nothing else. *)
Lemma rt_hw_fields : forall l,
  RD.ls_windowsize l = 65536 -> 0 <= RD.ls_strstart l -> 0 <= RD.ls_lookahead l ->
  RD.ls_strstart l + RD.ls_lookahead l <= 65536 -> 0 <= RD.ls_highwater l <= 65536 ->
  let l' := RD.fw_highwater l in
  RD.ls_strstart l' = RD.ls_strstart l /\ RD.ls_lookahead l' = RD.ls_lookahead l
  /\ RD.ls_insert l' = RD.ls_insert l /\ RD.ls_matchlen l' = RD.ls_matchlen l
  /\ RD.ls_prevlen l' = RD.ls_prevlen l /\ RD.ls_matchavail l' = RD.ls_matchavail l
  /\ RD.ls_blockstart l' = RD.ls_blockstart l /\ RD.ls_matchstart l' = RD.ls_matchstart l
  /\ RD.ls_windowsize l' = RD.ls_windowsize l
  /\ 0 <= RD.ls_highwater l' <= 65536
  /\ (forall i, RD.ls_window l' i = 0 \/ RD.ls_window l' i = RD.ls_window l i).
Proof.
  intros l Hws Hss Hla Hroom Hhw l'. subst l'. unfold RD.fw_highwater, RD.WIN_INIT, RC.MAX_MATCH.
  rewrite Hws. cbv zeta.
  repeat match goal with |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b) end;
    rt_ls; repeat split; try lia;
    intros i; unfold RD.win_zero; try (destruct (_ && _)); first [left; reflexivity | right; reflexivity].
Qed.

Lemma m_fill_rel : forall (a : arr) (z : Base.zarr) ofs cnt,
  arr_rel a z 0 65536 -> arr_len a = 65536 -> 0 <= cnt < 2 ^ 32 ->
  arr_rel (arr_fill a ofs (wrap32 cnt) 0) (RD.win_zero ofs cnt z) 0 65536.
Proof.
  intros a z ofs cnt Hr Hl Hc j Hj. rewrite arr_get_fill, wrap32_id by exact Hc.
  unfold arr_inb, RD.win_zero. rewrite Hl.
  destruct (Z.leb_spec ofs j); destruct (Z.ltb_spec j (ofs + Z.max 0 cnt)); destruct (Z.ltb_spec j (ofs + cnt));
    destruct (Z.leb_spec 0 j); destruct (Z.ltb_spec j 65536); cbn [andb]; try lia; try reflexivity;
    apply Hr; lia.
Qed.

Theorem m_highwater : forall s t l,
  lz_rel s (RD.setD_ls l t) -> RD.ls_windowsize l = 65536 ->
  0 <= RD.ls_strstart l -> 0 <= RD.ls_lookahead l -> RD.ls_strstart l + RD.ls_lookahead l <= 65536 ->
  0 <= RD.ls_highwater l <= 65536 ->
  lz_rel (SLz.fill_window_high s) (RD.setD_ls (RD.fw_highwater l) t)
  /\ nonlz_view (SLz.fill_window_high s) = nonlz_view s.
Proof.
  intros s t l Hl Hws Hss Hla Hroom Hhw.
  pose proof (lzr_hw _ _ Hl) as Ehw. pose proof (lzr_wsz _ _ Hl) as Ews. pose proof (lzr_ss _ _ Hl) as Ess.
  pose proof (lzr_la _ _ Hl) as Ela. pose proof (lzr_win _ _ Hl) as Hrw. pose proof (lzr_wlen _ _ Hl) as Hwl.
  cbn [RD.d_ls RD.setD_ls] in Ehw, Ews, Ess, Ela, Hrw, Hwl. rewrite Hws in Ews, Hrw, Hwl.
  unfold SLz.fill_window_high, RD.fw_highwater.
  change DS.WIN_INIT with 258. unfold RD.WIN_INIT, RC.MAX_MATCH.
  rewrite Ehw, Ews, Ess, Ela, Hws. cbv zeta.
  destruct (Z.ltb_spec (RD.ls_highwater l) 65536);
    [| split; [rewrite <- rt_setD_ls_ls with (b := l); exact Hl | reflexivity]].
  destruct (Z.ltb_spec (RD.ls_highwater l) (RD.ls_strstart l + RD.ls_lookahead l)).
  - set (curr := RD.ls_strstart l + RD.ls_lookahead l).
    set (init := if 258 <? 65536 - curr then 258 else 65536 - curr).
    assert (Hi : 0 <= init <= 258) by (subst init; destruct (Z.ltb_spec 258 (65536 - curr)); lia).
    split; [|reflexivity].
    apply lz_set_high_water; [|reflexivity].
    apply lz_set_window; [exact Hl | apply arr_len_fill |].
    rewrite Hws. apply m_fill_rel; [exact Hrw | exact Hwl | mpow; lia].
  - destruct (Z.ltb_spec (RD.ls_highwater l) (RD.ls_strstart l + RD.ls_lookahead l + 258)).
    + set (init := if 65536 - RD.ls_highwater l <? RD.ls_strstart l + RD.ls_lookahead l + 258 - RD.ls_highwater l
                   then 65536 - RD.ls_highwater l
                   else RD.ls_strstart l + RD.ls_lookahead l + 258 - RD.ls_highwater l).
      assert (Hi : 0 <= init <= 65536)
        by (subst init; destruct (Z.ltb_spec (65536 - RD.ls_highwater l)
              (RD.ls_strstart l + RD.ls_lookahead l + 258 - RD.ls_highwater l)); lia).
      split; [|reflexivity].
      apply lz_set_high_water; [|rewrite ds_high_water__set_window, Ehw; reflexivity].
      apply lz_set_window; [exact Hl | apply arr_len_fill |].
      rewrite Hws. apply m_fill_rel; [exact Hrw | exact Hwl | mpow; lia].
    + split; [exact Hl | reflexivity].
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  fill_window                                                           *)
(* ------------------------------------------------------------------------- *)

Theorem m_fill_window : forall s t pre_out pre_in,
  dst_rel s t pre_out pre_in -> mt_inv t ->
  RD.ls_lookahead (RD.d_ls t) < 262 ->
  dst_rel (SLz.fill_window s) (RD.fill_if true t) pre_out pre_in
  /\ mt_inv (RD.fill_if true t)
  /\ RD.ls_strstart (RD.d_ls (RD.fill_if true t)) + 262 <= 65536
  /\ DEmitDefs.em_view (SLz.fill_window s) = DEmitDefs.em_view s.
Proof.
  intros s t po pi Hd Hm Hla.
  pose proof (m_fw_inv_of_mt t Hm) as Hf.
  pose proof (m_s5_geom s t (proj1 Hd) Hm) as Hg.
  (* group R's half of mt_inv afterwards *)
  assert (Hfill : RD.ds_fill t = RD.fill_if true t)
    by (unfold RD.ds_fill, RD.ds_need; change RC.MIN_LOOKAHEAD with 262; rewrite (proj2 (Z.ltb_lt _ _) Hla); reflexivity).
  pose proof (RK.ms_fill t (mt_ms t Hm)) as (Ms1 & Ms2 & Ms3). rewrite Hfill in Ms1, Ms2, Ms3.
  unfold SLz.fill_window. rewrite (sg_w_size _ Hg). cbv zeta.
  unfold RD.fill_if, RD.fill_window in *. cbv zeta in *. cbn [fst snd] in *.
  assert (Hz : 0 <= Chunk.zlen (RD.zs_in (RD.d_strm t))) by (unfold Chunk.zlen; lia).
  pose proof (fi_la t Hf) as Hla0.
  destruct (m_fw_loop 263 (Z.to_nat (Chunk.zlen (RD.zs_in (RD.d_strm t))) + 2) s t po pi Hd Hf Hla)
    as (L1 & L2 & L3 & L4 & L5 & L6); [lia | lia |].
  cbv zeta in L1, L2, L3, L4, L5, L6.
  set (r0 := RD.fw_loop (Z.to_nat (Chunk.zlen (RD.zs_in (RD.d_strm t))) + 2) (RD.d_cfg t) (RD.d_wrap t)
               (RD.d_ls t) (RD.d_strm t)) in *.
  set (sL := SLz.fill_window_loop 263 s 32768) in *.
  rewrite rt_strm_ls in L1, L2 |- *.
  rewrite rt_strm_ls in Ms1, Ms2, Ms3.
  destruct L2 as [Fc Fw Frb Fws Fss Fla Froom Fins Fwin Fma Fbs Fhw Fslid Finl].
  cbn [RD.d_cfg RD.d_wrap RD.d_ls RD.d_strm RD.setD_ls RD.setD_strm] in Fc, Fw, Frb, Fws, Fss, Fla, Froom,
    Fins, Fwin, Fma, Fbs, Fhw, Fslid, Finl.
  pose proof L1 as L1'. apply m_dst_split in L1' as [Hl1 _].
  destruct (m_highwater sL (RD.setD_strm (snd r0) t) (fst r0) Hl1 Fws Fss Fla Froom Fhw) as [H1 H2].
  destruct (rt_hw_fields (fst r0) Fws Fss Fla Froom Fhw) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  split.
  { rewrite <- (rt_setD_ls_ls (RD.fw_highwater (fst r0)) (fst r0)).
    eapply m_lz_step; [exact L1 | exact H2 | rewrite rt_setD_ls_ls; exact H1]. }
  split.
  { destruct Hm as [Hlev Hcfg Hwr Hrb Hms Hfa Hsl Hwin Hma Hml Hbs Hhw Hslid Hinl].
    destruct Fslid as (slid & Z0 & Z1 & Z2 & Z3 & Z4).
    constructor; cbn [RD.d_cfg RD.d_wrap RD.d_ls RD.d_strm RD.setD_ls RD.setD_strm];
      rewrite ?W1, ?W2, ?W3, ?W4, ?W5, ?W6, ?W7, ?W8, ?W9; try assumption.
    all: first
      [ intros Hq; first [apply Ms2 | apply Ms3]; first [apply Hfa | apply Hsl]; exact Hq
      | intros i Hi; destruct (W11 i) as [E|E]; rewrite E; [lia | apply Fwin; exact Hi]
      | rewrite L4, L5; exact Hml
      | exists slid; lia ]. }
  split; [cbn [RD.d_ls RD.setD_ls]; rewrite W1; exact L3|].
  rewrite (m_em_of_nonlz sL (SLz.fill_window_high sL) H2). exact L6.
Qed.
