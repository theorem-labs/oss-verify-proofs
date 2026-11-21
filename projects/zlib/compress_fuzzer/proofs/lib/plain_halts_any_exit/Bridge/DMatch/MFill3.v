(** * Bridge.DMatch.MFill3 — group M: pair D17b, the slide step and one whole trip
    of [fill_window]'s loop ([m_pre], [m_fw_body]). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require DEmitDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MReadBuf MFill1 MFill2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.

Lemma rt_strm_ls : forall a b t, RD.setD_strm a (RD.setD_ls b t) = RD.setD_ls b (RD.setD_strm a t).
Proof. intros a b t. destruct t. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* 1.  RT's slide, field by field                                            *)
(* ------------------------------------------------------------------------- *)

Lemma rt_slide_fields : forall g l more0,
  RC.dg_w_size g = 32768 ->
  let l' := rt_slide g l more0 in
  RD.ls_window l' = RD.win_move 0 32768 (32768 - more0) (RD.ls_window l)
  /\ RD.ls_matchstart l' = RD.ls_matchstart l - 32768
  /\ RD.ls_strstart l' = RD.ls_strstart l - 32768
  /\ RD.ls_blockstart l' = RD.ls_blockstart l - 32768
  /\ RD.ls_insert l' = (if Z.ltb (RD.ls_strstart l - 32768) (RD.ls_insert l)
                        then RD.ls_strstart l - 32768 else RD.ls_insert l)
  /\ RD.ls_lookahead l' = RD.ls_lookahead l /\ RD.ls_matchlen l' = RD.ls_matchlen l
  /\ RD.ls_prevlen l' = RD.ls_prevlen l /\ RD.ls_matchavail l' = RD.ls_matchavail l
  /\ RD.ls_highwater l' = RD.ls_highwater l /\ RD.ls_windowsize l' = RD.ls_windowsize l.
Proof.
  intros g l more0 Hw l'. subst l'. unfold rt_slide, RD.slide_hash. rewrite Hw. cbv zeta.
  rt_ls. destruct (Z.ltb (RD.ls_strstart l - 32768) (RD.ls_insert l)); rt_ls; repeat split; reflexivity.
Qed.

Lemma m_win_move_bytes : forall w cnt i,
  (forall j, 0 <= j < 65536 -> 0 <= w j < 256) -> 0 <= cnt <= 32768 -> 0 <= i < 65536 ->
  0 <= RD.win_move 0 32768 cnt w i < 256.
Proof.
  intros w cnt i Hw Hc Hi. unfold RD.win_move.
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i (0 + cnt)); cbn [andb]; apply Hw; lia.
Qed.

Lemma m_s5_geom_cf : forall s t, geom_rel s t -> cfg_facts (RD.d_cfg t) -> s5_geom s.
Proof.
  intros s t Hg Hc. unfold geom_rel in Hg. cbv zeta in Hg.
  destruct Hg as (_ & Hst & _ & Hws & Hwm & _ & Hhs & Hhm & Hsh & Hlb & _).
  destruct Hc. constructor; congruence.
Qed.

Lemma m_geom_nonlz : forall s s', nonlz_view s' = nonlz_view s -> s5_geom s -> s5_geom s'.
Proof.
  intros s s' Hv Hg. destruct s, s'. unfold nonlz_view in Hv. cbn in Hv.
  injection Hv; intros; subst. destruct Hg. constructor; assumption.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The slide step                                                        *)
(* ------------------------------------------------------------------------- *)

Theorem m_pre : forall s t po pi,
  dst_rel s t po pi -> fw_inv t -> RD.ls_lookahead (RD.d_ls t) < 262 ->
  let p5 := s5_pre s 32768 in
  let pr := rt_pre (RD.d_cfg t) (RD.d_ls t) in
  dst_rel (fst p5) (RD.setD_ls (fst pr) t) po pi
  /\ snd p5 = snd pr
  /\ fw_inv (RD.setD_ls (fst pr) t)
  /\ RD.ls_strstart (fst pr) + 262 <= 65536
  /\ snd pr = 65536 - RD.ls_lookahead (fst pr) - RD.ls_strstart (fst pr)
  /\ RD.ls_lookahead (fst pr) = RD.ls_lookahead (RD.d_ls t)
  /\ RD.ls_matchlen (fst pr) = RD.ls_matchlen (RD.d_ls t)
  /\ RD.ls_prevlen (fst pr) = RD.ls_prevlen (RD.d_ls t)
  /\ DEmitDefs.em_view (fst p5) = DEmitDefs.em_view s.
Proof.
  intros s t po pi Hd Hf Hla262 p5 pr.
  pose proof Hd as Hd'. apply m_dst_split in Hd' as [Hl Hn].
  assert (Hgr : geom_rel s t) by (destruct Hn; assumption).
  pose proof (fi_cfg t Hf) as Fc.
  pose proof (m_s5_geom_cf s t Hgr Fc) as Hg.
  destruct Hf as [Fc' Fw Frb Fws Fss Fla Froom Fins Fwin Fma Fbs Fhw Fslid Finl]. clear Fc'.
  pose proof (lzr_wsz _ _ Hl) as Ewsz. pose proof (lzr_la _ _ Hl) as Ela. pose proof (lzr_ss _ _ Hl) as Ess.
  rewrite Fws in Ewsz.
  assert (Hmore5 : wrap32 (DS.ds_window_size s - DS.ds_lookahead s - DS.ds_strstart s)
                   = 65536 - RD.ls_lookahead (RD.d_ls t) - RD.ls_strstart (RD.d_ls t))
    by (rewrite Ewsz, Ela, Ess; apply wrap32_id; mpow; lia).
  assert (HmoreR : Base.u32 (RD.ls_windowsize (RD.d_ls t) - RD.ls_lookahead (RD.d_ls t) - RD.ls_strstart (RD.d_ls t))
                   = 65536 - RD.ls_lookahead (RD.d_ls t) - RD.ls_strstart (RD.d_ls t))
    by (rewrite Fws; apply Base.u32_id; lia).
  assert (Hc5 : (32768 + (DS.ds_w_size s - DS.MIN_LOOKAHEAD) <=? DS.ds_strstart s)
                = (65274 <=? RD.ls_strstart (RD.d_ls t)))
    by (rewrite (sg_w_size _ Hg), Ess; reflexivity).
  assert (HcR : (RC.dg_w_size (RD.d_cfg t) + RC.dg_max_dist (RD.d_cfg t) <=? RD.ls_strstart (RD.d_ls t))
                = (65274 <=? RD.ls_strstart (RD.d_ls t)))
    by (rewrite (cf_w_size _ Fc), (cf_max_dist _ Fc); reflexivity).
  subst p5 pr. unfold s5_pre, rt_pre. cbv zeta.
  rewrite Hmore5, HmoreR, Hc5, HcR.
  destruct (Z.leb_spec 65274 (RD.ls_strstart (RD.d_ls t))) as [Sl|NSl]; cbn [fst snd].
  - (* the slide *)
    set (more := 65536 - RD.ls_lookahead (RD.d_ls t) - RD.ls_strstart (RD.d_ls t)).
    assert (Hmore : 0 <= more <= 262) by (subst more; lia).
    destruct (m_slide_pre_hash s t more Hl Hg Fws Hmore) as [L5 V5]. cbv zeta in L5, V5.
    unfold s5_slide. cbv zeta.
    pose proof (rt_slide_fields (RD.d_cfg t) (RD.d_ls t) more (cf_w_size _ Fc)) as RF. cbv zeta in RF.
    destruct RF as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
    unfold rt_slide in *. cbv zeta in *. rewrite (cf_w_size _ Fc) in *.
    match type of L5 with lz_rel ?s5c (RD.setD_ls ?l5 t) =>
      assert (G5 : s5_geom s5c) by (exact (m_geom_nonlz s s5c V5 Hg));
      destruct (m_slide_hash s5c (RD.setD_ls l5 t) L5 G5 Fc) as [L6 V6];
      cbn [RD.d_cfg RD.d_ls RD.setD_ls] in L6; rewrite rt_setD_ls_ls in L6
    end.
    split; [eapply m_lz_step; [exact Hd | rewrite V6; exact V5 | exact L6]|].
    split; [rewrite wrap32_id by (mpow; lia); reflexivity|].
    split.
    { destruct Fslid as (slid & S0 & S1 & S2 & S3 & S4).
      constructor; cbn [RD.d_cfg RD.d_wrap RD.d_ls RD.d_strm RD.setD_ls]; rewrite ?R1, ?R2, ?R3, ?R4, ?R5,
        ?R6, ?R7, ?R8, ?R9, ?R10, ?R11; try assumption; try lia.
      all: first
        [ destruct (Z.ltb_spec (RD.ls_strstart (RD.d_ls t) - 32768) (RD.ls_insert (RD.d_ls t))); lia
        | intros i Hi; apply m_win_move_bytes; [exact Fwin | lia | exact Hi]
        | destruct Fma as [M|[M1 M2]]; [left; exact M | right; split; [exact M1|lia]]
        | exists (slid + 32768); lia ]. }
    split; [rewrite R3; lia|].
    split; [rewrite R6, R3; subst more; lia|].
    split; [exact R6|]. split; [exact R7|]. split; [exact R8|].
    apply m_em_of_nonlz. rewrite V6. exact V5.
  - (* no slide *)
    rewrite rt_setD_ls_eta.
    split; [exact Hd|]. split; [reflexivity|].
    split; [constructor; assumption|].
    split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  One trip                                                              *)
(* ------------------------------------------------------------------------- *)

Lemma m_rt_rb_lens : forall wrap size st, 0 <= size ->
  Chunk.zlen (fst (RD.read_buf wrap size st)) = Z.min size (Chunk.zlen (RD.zs_in st))
  /\ Chunk.zlen (RD.zs_in (snd (RD.read_buf wrap size st)))
     = Chunk.zlen (RD.zs_in st) - Z.min size (Chunk.zlen (RD.zs_in st))
  /\ Chunk.zlen (RD.zs_done (snd (RD.read_buf wrap size st)))
     = Chunk.zlen (RD.zs_done st) + Z.min size (Chunk.zlen (RD.zs_in st))
  /\ (forall x, In x (fst (RD.read_buf wrap size st)) -> 0 <= x < 256).
Proof.
  intros wrap size st Hs.
  assert (Hz : 0 <= Chunk.zlen (RD.zs_in st)) by (unfold Chunk.zlen; lia).
  destruct (Z.eq_dec (Z.min size (Chunk.zlen (RD.zs_in st))) 0) as [E|E].
  - rewrite m_rt_read_buf_zero by exact E. cbn [fst snd]. rewrite E.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. intros x [].
  - rewrite m_rt_read_buf_eq by exact E. cbn [fst snd].
    cbn [RD.zs_in RD.zs_done RD.setZ_totalin RD.setZ_adler RD.setZ_done RD.setZ_in].
    unfold Chunk.zlen in *.
    split; [rewrite length_map, length_firstn; lia|].
    split; [rewrite length_skipn; lia|].
    split; [rewrite length_app, length_map, length_firstn; lia|].
    intros x Hx. apply in_map_iff in Hx as (y & <- & _). unfold Base.u8. apply Z.mod_pos_bound. lia.
Qed.

Lemma m_win_blit_bytes : forall dat off w i,
  (forall x, In x dat -> 0 <= x < 256) -> 0 <= w i < 256 -> 0 <= RD.win_blit dat off w i < 256.
Proof.
  intros dat off w i Hd Hw. unfold RD.win_blit. cbv zeta.
  destruct (Z.leb off i && Z.ltb i (off + Chunk.zlen dat)); [|exact Hw].
  unfold Base.zlist. destruct (nth_in_or_default (Z.to_nat (i - off)) dat 0) as [Hin|Hdf].
  - apply Hd, Hin.
  - rewrite Hdf. lia.
Qed.

Theorem m_fw_body : forall s t po pi,
  dst_rel s t po pi -> fw_inv t -> RD.ls_lookahead (RD.d_ls t) < 262 ->
  let r5 := SLz.fill_window_body s 32768 in
  let rr := RD.fw_step (RD.d_cfg t) (RD.d_wrap t) (RD.d_ls t) (RD.d_strm t) in
  let t' := RD.setD_strm (snd rr) (RD.setD_ls (snd (fst rr)) t) in
  snd r5 = fst (fst rr)
  /\ dst_rel (fst r5) t' po pi
  /\ fw_inv t'
  /\ RD.ls_strstart (RD.d_ls t') + 262 <= 65536
  /\ RD.ls_matchlen (RD.d_ls t') = RD.ls_matchlen (RD.d_ls t)
  /\ RD.ls_prevlen (RD.d_ls t') = RD.ls_prevlen (RD.d_ls t)
  /\ (fst (fst rr) = false ->
      RD.ls_lookahead (RD.d_ls t) < RD.ls_lookahead (RD.d_ls t')
      /\ Chunk.zlen (RD.zs_in (RD.d_strm t')) < Chunk.zlen (RD.zs_in (RD.d_strm t)))
  /\ DEmitDefs.em_view (fst r5) = DEmitDefs.em_view s.
Proof.
  intros s t po pi Hd Hf Hla r5 rr t'.
  destruct (m_pre s t po pi Hd Hf Hla) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  cbv zeta in P1, P2, P3, P4, P5, P6, P7, P8, P9.
  subst r5 rr t'. rewrite m_s5_body_shape, m_rt_body_shape.
  destruct (s5_pre s 32768) as [s1 more5] eqn:E5. cbn [fst snd] in P1, P2, P9.
  set (l1 := fst (rt_pre (RD.d_cfg t) (RD.d_ls t))) in *.
  set (more := snd (rt_pre (RD.d_cfg t) (RD.d_ls t))) in *.
  pose proof P1 as P1'. apply m_dst_split in P1' as [Hl1 Hn1].
  assert (Hav : DS.cs_avail_in (DS.ds_strm s1) = Chunk.zlen (RD.zs_in (RD.d_strm t))).
  { destruct Hn1 as (_ & _ & _ & _ & Hst). unfold strm_rel in Hst. cbv zeta in Hst.
    destruct Hst as (Hni & Hai & Hfit & Hby & Hin & _). cbn [RD.d_strm RD.setD_ls] in Hin.
    rewrite <- Hin. symmetry. apply m_zlen_slice. lia. }
  rewrite Hav.
  destruct (Z.eqb_spec (Chunk.zlen (RD.zs_in (RD.d_strm t))) 0) as [E0|E0]; cbn [fst snd].
  - (* no input: stop *)
    replace (RD.setD_strm (RD.d_strm t) (RD.setD_ls l1 t)) with (RD.setD_ls l1 t)
      by (destruct t; reflexivity).
    split; [reflexivity|]. split; [exact P1|]. split; [exact P3|]. split; [exact P4|].
    split; [exact P7|]. split; [exact P8|]. split; [discriminate|]. exact P9.
  - (* read, bump, re-seed *)
    destruct P3 as [Fc Fw Frb Fws Fss Fla Froom Fins Fwin Fma Fbs Fhw Fslid Finl].
    cbn [RD.d_cfg RD.d_wrap RD.d_ls RD.d_strm RD.setD_ls] in Fc, Fw, Frb, Fws, Fss, Fla, Froom, Fins,
      Fwin, Fma, Fbs, Fhw, Fslid, Finl.
    set (off := RD.ls_strstart l1 + RD.ls_lookahead l1).
    assert (Eoff : DS.ds_strstart s1 + DS.ds_lookahead s1 = off).
    { pose proof (lzr_ss _ _ Hl1) as A. pose proof (lzr_la _ _ Hl1) as B.
      cbn [RD.d_ls RD.setD_ls] in A, B. subst off. lia. }
    rewrite Eoff, P2.
    assert (Hm1 : 1 <= more) by lia.
    destruct (m_read_buf_window s1 (RD.setD_ls l1 t) po pi off more P1 Frb ltac:(lia) ltac:(subst off; lia))
      as (Q1 & Q2 & Q3).
    { cbn [RD.d_ls RD.d_strm RD.setD_ls]. subst off. lia. }
    cbn [RD.d_wrap RD.d_ls RD.d_strm RD.setD_ls] in Q1, Q2, Q3.
    destruct (m_rt_rb_lens (RD.d_wrap t) more (RD.d_strm t) ltac:(lia)) as (K1 & K2 & K3 & K4).
    set (dat := fst (RD.read_buf (RD.d_wrap t) more (RD.d_strm t))) in *.
    set (st' := snd (RD.read_buf (RD.d_wrap t) more (RD.d_strm t))) in *.
    destruct (SLz.read_buf s1 (SLz.RB_window off) more) as [s2 n] eqn:ER. cbn [fst snd] in Q1, Q2.
    set (l6 := RD.setL_window (RD.win_blit dat off (RD.ls_window l1)) l1) in *.
    set (T := RD.setD_strm st' t).
    replace (RD.setD_strm st' (RD.setD_ls l6 (RD.setD_ls l1 t))) with (RD.setD_ls l6 T) in Q2
      by (subst T; destruct t; reflexivity).
    pose proof Q2 as Q2'. apply m_dst_split in Q2' as [Hl2 Hn2].
    (* the lookahead bump *)
    assert (L7 : lz_rel (DS.set_lookahead s2 (DS.ds_lookahead s2 + n))
                        (RD.setD_ls (RD.setL_lookahead (RD.ls_lookahead l6 + Chunk.zlen dat) l6) T)).
    { apply lz_set_lookahead; [exact Hl2|]. rewrite Q1.
      pose proof (lzr_la _ _ Hl2) as A. cbn [RD.d_ls RD.setD_ls] in A. rewrite A. reflexivity. }
    set (s3 := DS.set_lookahead s2 (DS.ds_lookahead s2 + n)) in *.
    set (l7 := RD.setL_lookahead (RD.ls_lookahead l6 + Chunk.zlen dat) l6) in *.
    assert (Hg2 : s5_geom s2).
    { apply (m_s5_geom_cf s2 (RD.setD_ls l6 T)); [destruct Hn2; assumption | exact Fc]. }
    assert (Hg3 : s5_geom s3) by (exact (m_geom_nonlz s2 s3 eq_refl Hg2)).
    assert (Hz7 : Chunk.zlen dat = Z.min more (Chunk.zlen (RD.zs_in (RD.d_strm t)))) by exact K1.
    assert (Lws : RD.ls_windowsize l7 = 65536) by (subst l7 l6; rt_ls; exact Fws).
    assert (Lss : RD.ls_strstart l7 = RD.ls_strstart l1) by (subst l7 l6; rt_ls; reflexivity).
    assert (Lla : RD.ls_lookahead l7 = RD.ls_lookahead l1 + Chunk.zlen dat) by (subst l7 l6; rt_ls; reflexivity).
    assert (Lins : RD.ls_insert l7 = RD.ls_insert l1) by (subst l7 l6; rt_ls; reflexivity).
    assert (W1 : RD.ls_windowsize (RD.d_ls (RD.setD_ls l7 T)) = 65536) by exact Lws.
    assert (W2 : 0 <= RD.ls_insert (RD.d_ls (RD.setD_ls l7 T)) <= RD.ls_strstart (RD.d_ls (RD.setD_ls l7 T)))
      by (cbn [RD.d_ls RD.setD_ls]; rewrite Lins, Lss; lia).
    assert (W3 : 0 <= RD.ls_lookahead (RD.d_ls (RD.setD_ls l7 T)))
      by (cbn [RD.d_ls RD.setD_ls]; rewrite Lla; unfold Chunk.zlen; lia).
    assert (W4 : RD.ls_strstart (RD.d_ls (RD.setD_ls l7 T)) + RD.ls_lookahead (RD.d_ls (RD.setD_ls l7 T)) <= 65536)
      by (cbn [RD.d_ls RD.setD_ls]; rewrite Lss, Lla; lia).
    destruct (m_seed s3 (RD.setD_ls l7 T) L7 Hg3 Fc W1 W2 W3 W4) as (S1 & S2 & S3).
    cbn [RD.d_ls RD.d_cfg RD.setD_ls RD.setD_strm] in S1, S2, S3. subst T.
    cbn [RD.d_cfg RD.setD_strm] in S1, S3.
    rewrite rt_setD_ls_ls in S1.
    rewrite rt_strm_ls.
    destruct S3 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
    split; [reflexivity|].
    split.
    { replace (RD.setD_ls (RD.fw_seed (RD.d_cfg t) (rt_blit dat l1)) (RD.setD_strm st' t))
        with (RD.setD_ls (RD.fw_seed (RD.d_cfg t) l7) (RD.setD_ls l6 (RD.setD_strm st' t)))
        by (rewrite rt_setD_ls_ls; reflexivity).
      eapply m_lz_step; [exact Q2 | exact S2 |].
      rewrite rt_setD_ls_ls. exact S1. }
    change (rt_blit dat l1) with l7.
    split.
    { destruct Fslid as (slid & Z0 & Z1 & Z2 & Z3 & Z4).
      constructor; cbn [RD.d_cfg RD.d_wrap RD.d_ls RD.d_strm RD.setD_ls RD.setD_strm];
        rewrite ?B1, ?B2, ?B3, ?B4, ?B5, ?B6, ?B7, ?B8, ?B9, ?B10, ?B11; try assumption.
      all: try (rewrite Lss; lia).
      all: subst l7 l6; rt_ls.
      all: try lia.
      all: first
        [ exact Q3
        | intros i Hi; apply m_win_blit_bytes; [exact K4 | apply Fwin; exact Hi]
        | exists slid; split; [lia|]; split; [rewrite K3; lia|]; lia
        | rewrite K3, K2; lia ]. }
    split; [cbn [RD.d_ls RD.setD_ls]; rewrite B6, Lss; lia|].
    split; [cbn [RD.d_ls RD.setD_ls]; rewrite B3; subst l7 l6; rt_ls; exact P7|].
    split; [cbn [RD.d_ls RD.setD_ls]; rewrite B9; subst l7 l6; rt_ls; exact P8|].
    split.
    { intros _. cbn [RD.d_ls RD.d_strm RD.setD_ls RD.setD_strm].
      assert (0 <= Chunk.zlen (RD.zs_in (RD.d_strm t))) by (unfold Chunk.zlen; lia).
      rewrite B8, K2, Lla. lia. }
    transitivity (DEmitDefs.em_view s3); [exact (m_em_of_nonlz s3 (s5_seed s3) S2)|].
    change (DEmitDefs.em_view s3) with (DEmitDefs.em_view s2).
    pose proof (m_rb_em_view_window s1 off more) as V. rewrite ER in V. cbn [fst] in V.
    rewrite V. exact P9.
Qed.
