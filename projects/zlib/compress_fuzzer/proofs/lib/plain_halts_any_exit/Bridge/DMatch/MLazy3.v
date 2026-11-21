(** * Bridge.DMatch.MLazy3 — group M: pair D15, the three exits of a
    [deflate_slow] trip, cut out of both models.

    After the search a trip either emits the previous match and inserts the
    strings it covers (branch A: [s5_slow_A] / [rt_slow_A], then the flush
    of a full symbol buffer, [s5_flush_step] / [rt_flush_step]), or emits
    the pending literal (branch B: [s5_slow_B] / [rt_slow_B], flushing in
    the middle and returning [need_more] on a full output buffer), or only
    makes the current string the pending one (branch C).  The shape lemmas
    cut each model's trip there.  [trip_facts] collects the RT facts the
    end of a trip needs for [mt_inv] ([mt_inv_of_tf]) and for the flush
    ([fb_lz_of_tf]); [rt_slow_A_facts], [rt_slow_B_facts] and
    [rt_slow_C_facts] give them per branch. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Risk Require MsDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MFill1 MFast1 MFast2
  MFast4 MLazy1 MLazy2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.
Module SBlk := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk.
Module STr := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Trees.

(* ------------------------------------------------------------------------- *)
(* 1.  S5's trip                                                             *)
(* ------------------------------------------------------------------------- *)

(** [deflate_slow_body] after the search, verbatim. *)
Definition s5_slow_emit0 (s : DS.deflate_state) : DS.deflate_state * SBlk.loop_out :=
  if Z.leb DS.MIN_MATCH (DS.ds_prev_length s) && Z.leb (DS.ds_match_length s) (DS.ds_prev_length s) then
    let max_insert := wrap32 (DS.ds_strstart s + DS.ds_lookahead s - DS.MIN_MATCH) in
    let '(s, bflush) := STr.tr_tally_dist s (wrap32 (DS.ds_strstart s - 1 - DS.ds_prev_match s))
                                          (DS.ds_prev_length s - DS.MIN_MATCH) in
    let s := DS.set_lookahead s (wrap32 (DS.ds_lookahead s - (DS.ds_prev_length s - 1))) in
    let s := DS.set_prev_length s (DS.ds_prev_length s - 2) in
    let s := SBlk.deflate_slow_insert (Z.to_nat (DS.ds_prev_length s)) s max_insert in
    let s := DS.set_match_available s 0 in
    let s := DS.set_match_length s (DS.MIN_MATCH - 1) in
    let s := DS.set_strstart s (DS.ds_strstart s + 1) in
    if bflush then
      let '(s, r) := SBlk.flush_block s 0 in
      match r with Some bs => (s, SBlk.LRet bs) | None => (s, SBlk.LCont) end
    else (s, SBlk.LCont)
  else if negb (Z.eqb (DS.ds_match_available s) 0) then
    let '(s, bflush) := STr.tr_tally_lit s (arr_get (DS.ds_window s) (DS.ds_strstart s - 1)) in
    let s := if bflush then SLz.flush_block_only s 0 else s in
    let s := DS.set_strstart s (DS.ds_strstart s + 1) in
    let s := DS.set_lookahead s (DS.ds_lookahead s - 1) in
    if Z.eqb (DS.cs_avail_out (DS.ds_strm s)) 0 then (s, SBlk.LRet SLz.need_more) else (s, SBlk.LCont)
  else
    let s := DS.set_match_available s 1 in
    let s := DS.set_strstart s (DS.ds_strstart s + 1) in
    let s := DS.set_lookahead s (DS.ds_lookahead s - 1) in
    (s, SBlk.LCont).

Definition s5_slow_A (s : DS.deflate_state) : DS.deflate_state * bool :=
  let max_insert := wrap32 (DS.ds_strstart s + DS.ds_lookahead s - DS.MIN_MATCH) in
  let '(s, bflush) := STr.tr_tally_dist s (wrap32 (DS.ds_strstart s - 1 - DS.ds_prev_match s))
                                        (DS.ds_prev_length s - DS.MIN_MATCH) in
  let s := DS.set_lookahead s (wrap32 (DS.ds_lookahead s - (DS.ds_prev_length s - 1))) in
  let s := DS.set_prev_length s (DS.ds_prev_length s - 2) in
  let s := SBlk.deflate_slow_insert (Z.to_nat (DS.ds_prev_length s)) s max_insert in
  let s := DS.set_match_available s 0 in
  let s := DS.set_match_length s (DS.MIN_MATCH - 1) in
  let s := DS.set_strstart s (DS.ds_strstart s + 1) in
  (s, bflush).

Definition s5_slow_B_state (s : DS.deflate_state) : DS.deflate_state :=
  let '(s, bflush) := STr.tr_tally_lit s (arr_get (DS.ds_window s) (DS.ds_strstart s - 1)) in
  let s := if bflush then SLz.flush_block_only s 0 else s in
  let s := DS.set_strstart s (DS.ds_strstart s + 1) in
  DS.set_lookahead s (DS.ds_lookahead s - 1).

Definition s5_slow_B (s : DS.deflate_state) : DS.deflate_state * SBlk.loop_out :=
  let s := s5_slow_B_state s in
  if Z.eqb (DS.cs_avail_out (DS.ds_strm s)) 0 then (s, SBlk.LRet SLz.need_more) else (s, SBlk.LCont).

Definition s5_slow_C (s : DS.deflate_state) : DS.deflate_state :=
  let s := DS.set_match_available s 1 in
  let s := DS.set_strstart s (DS.ds_strstart s + 1) in
  DS.set_lookahead s (DS.ds_lookahead s - 1).

Definition s5_slow_emit (s : DS.deflate_state) : DS.deflate_state * SBlk.loop_out :=
  if Z.leb DS.MIN_MATCH (DS.ds_prev_length s) && Z.leb (DS.ds_match_length s) (DS.ds_prev_length s)
  then s5_flush_step (fst (s5_slow_A s)) (snd (s5_slow_A s))
  else if negb (Z.eqb (DS.ds_match_available s) 0) then s5_slow_B s
  else (s5_slow_C s, SBlk.LCont).

Lemma m_s5_emit_split : forall s, s5_slow_emit0 s = s5_slow_emit s.
Proof.
  intros s. unfold s5_slow_emit0, s5_slow_emit, s5_slow_A, s5_slow_B, s5_slow_B_state, s5_slow_C. cbv zeta.
  destruct (Z.leb DS.MIN_MATCH (DS.ds_prev_length s) && Z.leb (DS.ds_match_length s) (DS.ds_prev_length s)).
  - destruct (STr.tr_tally_dist s (wrap32 (DS.ds_strstart s - 1 - DS.ds_prev_match s))
                (DS.ds_prev_length s - DS.MIN_MATCH)). reflexivity.
  - destruct (negb (Z.eqb (DS.ds_match_available s) 0)); [|reflexivity].
    destruct (STr.tr_tally_lit s (arr_get (DS.ds_window s) (DS.ds_strstart s - 1))). reflexivity.
Qed.

Lemma m_s5_slow_body_shape : forall s flush,
  SBlk.deflate_slow_body s flush
  = match s5_early s flush with
    | (s', Some o) => (s', o)
    | (s', None) => s5_slow_emit (s5_slow_l2 s')
    end.
Proof.
  intros s flush. unfold SBlk.deflate_slow_body. fold (s5_early s flush).
  destruct (s5_early s flush) as [s' [o|]]; [reflexivity|].
  rewrite <- m_s5_emit_split. unfold s5_slow_l2.
  destruct (if Z.leb DS.MIN_MATCH (DS.ds_lookahead s') then SLz.insert_string s' (DS.ds_strstart s')
            else (s', DS.NIL)) as [s0 hh].
  reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  RT's trip                                                             *)
(* ------------------------------------------------------------------------- *)

Definition rt_slow_A (s2 : RD.DSt) : bool * RD.DSt :=
  let g := RD.d_cfg s2 in
  let l2 := RD.d_ls s2 in
  let max_insert := RD.ls_strstart l2 + RD.ls_lookahead l2 - RC.MIN_MATCH in
  let tt := RT.tr_tally_dist (RD.ls_strstart l2 - 1 - RD.ls_prevmatch l2)
                             (RD.ls_prevlen l2 - RC.MIN_MATCH) (RC.dg_sym_end g) (RD.d_ts s2) in
  let l3 := RD.setL_prevlen (RD.ls_prevlen l2 - 2)
              (RD.setL_lookahead (RD.ls_lookahead l2 - (RD.ls_prevlen l2 - 1)) l2) in
  let l4 := RD.ds_insert (Z.to_nat (RD.ls_prevlen l3) + 1) g max_insert l3 in
  let l5 := RD.setL_strstart (RD.ls_strstart l4 + 1)
              (RD.setL_matchlen (RC.MIN_MATCH - 1) (RD.setL_matchavail 0 l4)) in
  (fst tt, RD.setD_ls l5 (RD.setD_ts (snd tt) s2)).

Definition rt_slow_B_state (s2 : RD.DSt) : RD.DSt :=
  let g := RD.d_cfg s2 in
  let l2 := RD.d_ls s2 in
  let tt := RT.tr_tally_lit (RD.ls_window l2 (RD.ls_strstart l2 - 1)) (RC.dg_sym_end g) (RD.d_ts s2) in
  let s3 := RD.setD_ts (snd tt) s2 in
  let s4 := if fst tt then RD.flush_block_only 0 s3 else s3 in
  RD.setD_ls (RD.setL_lookahead (RD.ls_lookahead (RD.d_ls s4) - 1)
               (RD.setL_strstart (RD.ls_strstart (RD.d_ls s4) + 1) (RD.d_ls s4))) s4.

Definition rt_slow_B (s2 : RD.DSt) : RD.DsStep :=
  let s5 := rt_slow_B_state s2 in
  if Z.eqb (RD.zs_availout (RD.d_strm s5)) 0 then RD.DsRet RD.NeedMore s5 else RD.DsCont s5.

Definition rt_slow_C (s2 : RD.DSt) : RD.DSt :=
  let l2 := RD.d_ls s2 in
  RD.setD_ls (RD.setL_lookahead (RD.ls_lookahead l2 - 1)
               (RD.setL_strstart (RD.ls_strstart l2 + 1) (RD.setL_matchavail 1 l2))) s2.

Definition rt_slow_emit (s2 : RD.DSt) : RD.DsStep :=
  let l2 := RD.d_ls s2 in
  if (Z.leb RC.MIN_MATCH (RD.ls_prevlen l2)) && (Z.leb (RD.ls_matchlen l2) (RD.ls_prevlen l2))
  then rt_flush_step (fst (rt_slow_A s2)) (snd (rt_slow_A s2))
  else if negb (Z.eqb (RD.ls_matchavail l2) 0) then rt_slow_B s2
  else RD.DsCont (rt_slow_C s2).

Lemma m_rt_ds_body_shape : forall flush p0,
  RD.ds_body flush p0 = rt_slow_emit (RD.setD_ls (RK.ds_l2 p0) p0).
Proof. intros flush p0. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  RT's end of trip, per branch                                          *)
(* ------------------------------------------------------------------------- *)

Record trip_facts (p0 t3 : RD.DSt) : Prop := mkTripFacts {
  tf_frame : rt_frame p0 t3;
  tf_win : RD.ls_window (RD.d_ls t3) = RD.ls_window (RD.d_ls p0);
  tf_hw : RD.ls_highwater (RD.d_ls t3) = RD.ls_highwater (RD.d_ls p0);
  tf_ma : RD.ls_matchavail (RD.d_ls t3) = 0
          \/ (RD.ls_matchavail (RD.d_ls t3) = 1 /\ 1 <= RD.ls_strstart (RD.d_ls t3));
  tf_ml : 0 <= RD.ls_matchlen (RD.d_ls t3) <= 258;
  tf_pl : 0 <= RD.ls_prevlen (RD.d_ls t3) <= 258;
  tf_sum : RD.ls_strstart (RD.d_ls t3) + RD.ls_lookahead (RD.d_ls t3)
           = RD.ls_strstart (RD.d_ls p0) + RD.ls_lookahead (RD.d_ls p0);
  tf_adv : RD.ls_strstart (RD.d_ls p0) + 1 <= RD.ls_strstart (RD.d_ls t3);
  tf_la : 0 <= RD.ls_lookahead (RD.d_ls t3);
  tf_bs : RD.ls_blockstart (RD.d_ls t3) = RD.ls_blockstart (RD.d_ls p0)
          \/ RD.ls_strstart (RD.d_ls p0) <= RD.ls_blockstart (RD.d_ls t3) <= RD.ls_strstart (RD.d_ls t3);
  tf_ms : RD.ls_matchstart (RD.d_ls t3) = RD.ls_matchstart (RD.d_ls p0)
          \/ 0 <= RD.ls_matchstart (RD.d_ls t3) <= RD.ls_strstart (RD.d_ls t3);
  tf_pend : RC.MIN_MATCH <= RD.ls_matchlen (RD.d_ls t3) -> 1 <= RD.ls_strstart (RD.d_ls t3);
  tf_ws : RD.ls_windowsize (RD.d_ls t3) = RD.ls_windowsize (RD.d_ls p0)
}.

Lemma mt_inv_of_tf : forall p0 t3,
  mt_inv p0 -> RK.ms_inv t3 ->
  (RC.dg_level (RD.d_cfg t3) <= 3 -> RK.ms_fast_inv t3) ->
  (4 <= RC.dg_level (RD.d_cfg t3) -> RK.ms_slow_inv t3) ->
  trip_facts p0 t3 -> mt_inv t3.
Proof.
  intros p0 t3 Hm Hms Hf Hs [F W H MA ML PL S A LA B MS P WS].
  exact (mt_inv_trip p0 t3 Hm Hms Hf Hs F W H MA ML PL S ltac:(lia) B MS P).
Qed.

Lemma fb_lz_of_tf : forall p0 t3, mt_inv p0 -> trip_facts p0 t3 -> fb_lz t3.
Proof.
  intros p0 t3 Hm [[F1 F2 F3 F4 F5] Ew Ehw Ema Eml Epl Esum Eadv Ela Ebs Ems Epend Ews].
  pose proof (m_cfg_facts p0 Hm) as Hc. pose proof (mt_ms p0 Hm) as Hms.
  destruct (mt_slid p0 Hm) as (slid & Z0 & Z1 & Z2 & Z3 & Z4).
  pose proof (mt_inlen p0 Hm) as Hinl. pose proof (mt_bs p0 Hm) as Hbs. pose proof (mt_win p0 Hm) as Hwin.
  pose proof (RK.mi_winsize _ Hms) as Hwz. pose proof (RK.mi_str _ Hms) as Hst. pose proof (RK.mi_room _ Hms) as Hrm.
  assert (0 <= Chunk.zlen (RD.zs_in (RD.d_strm p0))) by (unfold Chunk.zlen; lia).
  unfold fb_lz. rewrite F1, Ews. rewrite (cf_w_size _ Hc) in *.
  split; [lia|]. split; [exact Hwz|]. split; [lia|]. split; [lia|].
  split; [destruct Ebs as [E|E]; [rewrite E|]; mpow; lia|].
  split; [destruct Ebs as [E|E]; [rewrite E|]; mpow; lia|].
  intros i Hi. rewrite Ew. apply Hwin. lia.
Qed.

Lemma tf_flush : forall p0 t3 last, trip_facts p0 t3 -> trip_facts p0 (snd (RD.flush_block last t3)).
Proof.
  intros p0 t3 last [[F1 F2 F3 F4 F5] Ew Ehw Ema Eml Epl Esum Eadv Ela Ebs Ems Epend Ews].
  destruct (rt_fb_frame last t3) as [[G1 G2 G3 G4 G5] FL].
  constructor; rewrite ?FL; rt_ls; try assumption.
  - constructor; congruence.
  - right. lia.
Qed.

Lemma rt_slow_A_facts : forall p0,
  mt_inv p0 -> 4 <= RC.dg_level (RD.d_cfg p0) -> 1 <= RD.ls_lookahead (RD.d_ls p0) ->
  RC.MIN_MATCH <= RD.ls_prevlen (RK.ds_l2 p0) -> RD.ls_matchlen (RK.ds_l2 p0) <= RD.ls_prevlen (RK.ds_l2 p0) ->
  trip_facts p0 (snd (rt_slow_A (RD.setD_ls (RK.ds_l2 p0) p0))).
Proof.
  intros p0 Hm Hlev Hla1 Hpl3 Hmlpl.
  pose proof (m_cfg_facts p0 Hm) as Hc.
  pose proof (mt_ml p0 Hm) as Hml0. pose proof (RK.mi_str _ (mt_ms p0 Hm)) as Hss0.
  destruct (mt_slow p0 Hm Hlev) as [S1 S2]. change RC.MIN_MATCH with 3 in *.
  destruct (rt_ds_l2_facts p0 Hm) as (Fw & Fss & Fla & Fbs & Fhw & Fma & Fins & Fws & Fpl & Fpm & Fml & Fms).
  change RC.MIN_MATCH with 3 in Fml.
  set (l2 := RK.ds_l2 p0) in *.
  assert (Hla2 : RD.ls_prevlen l2 - 1 <= RD.ls_lookahead (RD.d_ls p0)) by (rewrite Fpl in *; lia).
  unfold rt_slow_A. cbv zeta. cbn [RD.d_ls RD.d_cfg RD.setD_ls]. change RC.MIN_MATCH with 3.
  set (mi := RD.ls_strstart l2 + RD.ls_lookahead l2 - 3).
  set (l3 := RD.setL_prevlen (RD.ls_prevlen l2 - 2)
               (RD.setL_lookahead (RD.ls_lookahead l2 - (RD.ls_prevlen l2 - 1)) l2)).
  destruct (rt_dsi_frame (Z.to_nat (RD.ls_prevlen l3) + 1) (RD.d_cfg p0) mi l3
              (cf_hash_mask _ Hc) (cf_w_mask _ Hc) ltac:(subst l3; rt_ls; lia) ltac:(subst l3; rt_ls; lia))
    as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  assert (E3 : RD.ls_window l3 = RD.ls_window l2 /\ RD.ls_strstart l3 = RD.ls_strstart l2
               /\ RD.ls_lookahead l3 = RD.ls_lookahead l2 - (RD.ls_prevlen l2 - 1)
               /\ RD.ls_matchlen l3 = RD.ls_matchlen l2 /\ RD.ls_prevlen l3 = RD.ls_prevlen l2 - 2
               /\ RD.ls_matchstart l3 = RD.ls_matchstart l2 /\ RD.ls_blockstart l3 = RD.ls_blockstart l2
               /\ RD.ls_insert l3 = RD.ls_insert l2 /\ RD.ls_highwater l3 = RD.ls_highwater l2
               /\ RD.ls_windowsize l3 = RD.ls_windowsize l2)
    by (subst l3; rt_ls; repeat split; reflexivity).
  destruct E3 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  constructor; cbn [fst snd RD.d_cfg RD.d_wrap RD.d_ls RD.d_strm RD.setD_ls RD.setD_ts]; rt_ls;
    rewrite ?B1, ?B2, ?B3, ?B4, ?B5, ?B6, ?B7, ?B8, ?B9, ?B10, ?B11, ?B12;
    rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E9, ?E10;
    rewrite ?Fw, ?Fss, ?Fla, ?Fbs, ?Fhw, ?Fma, ?Fins, ?Fws, ?Fpl; try reflexivity; try lia.
  all: first [ constructor; reflexivity | left; reflexivity
             | destruct Fms as [M|M]; [left; exact M | right; lia] ].
Qed.

Lemma rt_slow_B_facts : forall p0,
  mt_inv p0 -> 1 <= RD.ls_lookahead (RD.d_ls p0) ->
  RD.ls_matchavail (RK.ds_l2 p0) <> 0 ->
  trip_facts p0 (rt_slow_B_state (RD.setD_ls (RK.ds_l2 p0) p0)).
Proof.
  intros p0 Hm Hla1 Hma2.
  pose proof (mt_ml p0 Hm) as Hml0. pose proof (RK.mi_str _ (mt_ms p0 Hm)) as Hss0.
  pose proof (mt_ma p0 Hm) as Hma0.
  destruct (rt_ds_l2_facts p0 Hm) as (Fw & Fss & Fla & Fbs & Fhw & Fma & Fins & Fws & Fpl & Fpm & Fml & Fms).
  change RC.MIN_MATCH with 3 in Fml.
  set (l2 := RK.ds_l2 p0) in *.
  assert (Hma : RD.ls_matchavail l2 = 1 /\ 1 <= RD.ls_strstart l2) by (rewrite Fma, Fss; lia).
  unfold rt_slow_B_state. cbv zeta. cbn [RD.d_ls RD.d_cfg RD.setD_ls RD.d_ts].
  set (tt := RT.tr_tally_lit (RD.ls_window l2 (RD.ls_strstart l2 - 1)) (RC.dg_sym_end (RD.d_cfg p0)) (RD.d_ts p0)).
  destruct (fst tt).
  - destruct (rt_fbo_frame 0 (RD.setD_ts (snd tt) (RD.setD_ls l2 p0))) as [[G1 G2 G3 G4 G5] FL].
    cbn [RD.d_cfg RD.d_wrap RD.d_strm RD.d_ls RD.setD_ls RD.setD_ts] in G1, G2, G3, G4, G5, FL.
    constructor; cbn [RD.d_cfg RD.d_wrap RD.d_ls RD.d_strm RD.setD_ls RD.setD_ts]; rewrite ?FL; rt_ls;
      rewrite ?G1, ?G2, ?G3, ?G4, ?G5; rewrite ?Fw, ?Fss, ?Fla, ?Fbs, ?Fhw, ?Fma, ?Fins, ?Fws, ?Fpl;
      try reflexivity; try lia.
    all: first [ constructor; assumption | destruct Fml as [M|M]; lia
               | destruct Fms as [M|M]; [left; exact M | right; lia] ].
  - constructor; cbn [RD.d_cfg RD.d_wrap RD.d_ls RD.d_strm RD.setD_ls RD.setD_ts]; rt_ls;
      rewrite ?Fw, ?Fss, ?Fla, ?Fbs, ?Fhw, ?Fma, ?Fins, ?Fws, ?Fpl; try reflexivity; try lia.
    all: first [ constructor; reflexivity | destruct Fml as [M|M]; lia
               | destruct Fms as [M|M]; [left; exact M | right; lia] ].
Qed.

Lemma rt_slow_C_facts : forall p0,
  mt_inv p0 -> 1 <= RD.ls_lookahead (RD.d_ls p0) ->
  trip_facts p0 (rt_slow_C (RD.setD_ls (RK.ds_l2 p0) p0)).
Proof.
  intros p0 Hm Hla1.
  pose proof (mt_ml p0 Hm) as Hml0. pose proof (RK.mi_str _ (mt_ms p0 Hm)) as Hss0.
  destruct (rt_ds_l2_facts p0 Hm) as (Fw & Fss & Fla & Fbs & Fhw & Fma & Fins & Fws & Fpl & Fpm & Fml & Fms).
  change RC.MIN_MATCH with 3 in Fml.
  set (l2 := RK.ds_l2 p0) in *.
  unfold rt_slow_C. cbn [RD.d_ls RD.d_cfg RD.setD_ls].
  constructor; cbn [RD.d_cfg RD.d_wrap RD.d_ls RD.d_strm RD.setD_ls RD.setD_ts]; rt_ls;
    rewrite ?Fw, ?Fss, ?Fla, ?Fbs, ?Fhw, ?Fma, ?Fins, ?Fws, ?Fpl; try reflexivity; try lia.
  all: first [ constructor; reflexivity | destruct Fml as [M|M]; lia
             | destruct Fms as [M|M]; [left; exact M | right; lia] ].
Qed.
