(** * Bridge.DMatch.MFast4 — group M: pair D14, the symbol a [deflate_fast] trip emits.

    [s5_fast_emit] / [rt_fast_emit]: after the insert and the search, a
    trip tallies a match (then inserts the strings it covers, or skips
    them and re-seeds the hash) or a literal; the flush that a full symbol
    buffer triggers is [s5_flush_step] / [rt_flush_step].  The shape lemmas
    cut each model's trip there.  [m_fast_emit] relates the two emits under
    group D's tally pairs ([DEmitIface]) and the match-start live range
    (group R's [ms_fast_emit]), and returns the RT facts the flush and the
    loop need. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MFill1 MFast1 MFast2 MFast3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require MFill3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.
Module SBlk := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk.
Module STr := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Trees.

(* ------------------------------------------------------------------------- *)
(* 1.  Both trips, cut after the search                                      *)
(* ------------------------------------------------------------------------- *)

Definition s5_fast_emit (s : DS.deflate_state) : DS.deflate_state * bool :=
  if Z.leb DS.MIN_MATCH (DS.ds_match_length s) then
    let '(s, bflush) := STr.tr_tally_dist s (wrap32 (DS.ds_strstart s - DS.ds_match_start s))
                                          (DS.ds_match_length s - DS.MIN_MATCH) in
    let s := DS.set_lookahead s (DS.ds_lookahead s - DS.ds_match_length s) in
    let s :=
      if Z.leb (DS.ds_match_length s) (DS.ds_max_lazy_match s) && Z.leb DS.MIN_MATCH (DS.ds_lookahead s)
      then
        let s := DS.set_match_length s (DS.ds_match_length s - 1) in
        let s := SBlk.deflate_fast_insert (Z.to_nat (DS.ds_match_length s)) s in
        DS.set_strstart s (DS.ds_strstart s + 1)
      else
        let s := DS.set_strstart s (DS.ds_strstart s + DS.ds_match_length s) in
        let s := DS.set_match_length s 0 in
        let s := DS.set_ins_h s (arr_get (DS.ds_window s) (DS.ds_strstart s)) in
        DS.set_ins_h s (SLz.update_hash s (DS.ds_ins_h s) (arr_get (DS.ds_window s) (DS.ds_strstart s + 1)))
    in (s, bflush)
  else
    let '(s, bflush) := STr.tr_tally_lit s (arr_get (DS.ds_window s) (DS.ds_strstart s)) in
    let s := DS.set_lookahead s (DS.ds_lookahead s - 1) in
    let s := DS.set_strstart s (DS.ds_strstart s + 1) in
    (s, bflush).

Definition s5_flush_step (s : DS.deflate_state) (bflush : bool) : DS.deflate_state * SBlk.loop_out :=
  if bflush then
    let '(s, r) := SBlk.flush_block s 0 in
    match r with Some bs => (s, SBlk.LRet bs) | None => (s, SBlk.LCont) end
  else (s, SBlk.LCont).

Lemma m_s5_fast_body_shape : forall s flush,
  SBlk.deflate_fast_body s flush
  = match s5_early s flush with
    | (s', Some o) => (s', o)
    | (s', None) => let (s3, bf) := s5_fast_emit (s5_fast_l1 s') in s5_flush_step s3 bf
    end.
Proof.
  intros s flush. unfold SBlk.deflate_fast_body. fold (s5_early s flush).
  destruct (s5_early s flush) as [s' [o|]]; [reflexivity|].
  unfold s5_fast_l1.
  destruct (if Z.leb DS.MIN_MATCH (DS.ds_lookahead s') then SLz.insert_string s' (DS.ds_strstart s')
            else (s', DS.NIL)) as [s0 hh].
  reflexivity.
Qed.

Definition rt_fast_emit (p0 : RD.DSt) : bool * RD.DSt :=
  let g := RD.d_cfg p0 in
  let l1 := RK.df_l1 p0 in
  let s2 := RD.setD_ls l1 p0 in
  if Z.leb RC.MIN_MATCH (RD.ls_matchlen l1) then
    let tt := RT.tr_tally_dist (RD.ls_strstart l1 - RD.ls_matchstart l1)
                               (RD.ls_matchlen l1 - RC.MIN_MATCH) (RC.dg_sym_end g) (RD.d_ts s2) in
    let l2 := RD.setL_lookahead (RD.ls_lookahead l1 - RD.ls_matchlen l1) l1 in
    let l4 :=
      if (Z.leb (RD.ls_matchlen l2) (RC.dg_max_lazy_match g)) && (Z.leb RC.MIN_MATCH (RD.ls_lookahead l2)) then
        let l3 := RD.setL_matchlen (RD.ls_matchlen l2 - 1) l2 in
        let l3b := RD.df_insert (Z.to_nat (RD.ls_matchlen l3) + 1) g (RD.ls_matchlen l3) l3 in
        RD.setL_strstart (RD.ls_strstart l3b + 1) (RD.setL_matchlen 0 l3b)
      else
        let l3 := RD.setL_matchlen 0 (RD.setL_strstart (RD.ls_strstart l2 + RD.ls_matchlen l2) l2) in
        let h0 := RD.ls_window l3 (RD.ls_strstart l3) in
        RD.setL_insh (RD.update_hash g h0 (RD.ls_window l3 (RD.ls_strstart l3 + 1))) l3 in
    (fst tt, RD.setD_ls l4 (RD.setD_ts (snd tt) s2))
  else
    let tt := RT.tr_tally_lit (RD.ls_window l1 (RD.ls_strstart l1)) (RC.dg_sym_end g) (RD.d_ts s2) in
    (fst tt, RD.setD_ls (RD.setL_strstart (RD.ls_strstart l1 + 1)
                          (RD.setL_lookahead (RD.ls_lookahead l1 - 1) l1))
                        (RD.setD_ts (snd tt) s2)).

Definition rt_flush_step (bflush : bool) (s3 : RD.DSt) : RD.DsStep :=
  if bflush then
    match RD.flush_block 0 s3 with
    | (Some bs, s4) => RD.DsRet bs s4
    | (None, s4) => RD.DsCont s4
    end
  else RD.DsCont s3.

Lemma m_rt_df_body_shape : forall flush p0,
  RD.df_body flush p0 = rt_flush_step (fst (rt_fast_emit p0)) (snd (rt_fast_emit p0)).
Proof.
  intros flush p0. unfold RD.df_body, rt_fast_emit, rt_flush_step, RK.df_l1. cbv zeta.
  match goal with |- context [if Z.leb RC.MIN_MATCH (RD.ls_matchlen ?l1) then _ else _] =>
    destruct (Z.leb RC.MIN_MATCH (RD.ls_matchlen l1)) end; reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  RT's emit, field by field                                             *)
(* ------------------------------------------------------------------------- *)

Lemma rt_dfi_frame : forall m g n l,
  RC.dg_hash_mask g = 32767 -> RC.dg_w_mask g = 32767 ->
  1 <= n -> n < Z.of_nat m -> dfi_frame l (RD.df_insert m g n l) n.
Proof.
  induction m as [|m IH]; intros g n l Hhm Hwm Hn Hm; [lia|].
  cbn [RD.df_insert]. cbv zeta.
  destruct (rt_ins_facts g (RD.ls_strstart (RD.setL_strstart (RD.ls_strstart l + 1) l))
              (RD.setL_strstart (RD.ls_strstart l + 1) l) Hhm Hwm)
    as (_ & _ & _ & _ & Kw & Kss & Kla & Kml & Kpl & Kms & Kpm & Kma & Kbs & Kins & Khw & Kws).
  rt_ls.
  cbn [RD.setL_strstart RD.ls_window RD.ls_strstart RD.ls_lookahead RD.ls_matchlen RD.ls_prevlen
       RD.ls_matchstart RD.ls_prevmatch RD.ls_matchavail RD.ls_blockstart RD.ls_insert RD.ls_highwater
       RD.ls_windowsize] in Kw, Kss, Kla, Kml, Kpl, Kms, Kpm, Kma, Kbs, Kins, Khw, Kws.
  set (l2 := snd (RD.insert_string g (RD.ls_strstart l + 1) (RD.setL_strstart (RD.ls_strstart l + 1) l))) in *.
  destruct (Z.eqb_spec (n - 1) 0) as [E|E].
  - unfold dfi_frame. rewrite Kw, Kss, Kla, Kml, Kpl, Kms, Kpm, Kma, Kbs, Kins, Khw, Kws.
    repeat (split; [reflexivity || lia|]). reflexivity.
  - destruct (IH g (n - 1) l2 Hhm Hwm ltac:(lia) ltac:(lia))
      as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
    unfold dfi_frame. rewrite B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12.
    rewrite Kw, Kss, Kla, Kml, Kpl, Kms, Kpm, Kma, Kbs, Kins, Khw, Kws.
    repeat (split; [reflexivity || lia|]). reflexivity.
Qed.

Record emit_facts (p0 t3 : RD.DSt) : Prop := mkEmitFacts {
  ef_frame : rt_frame p0 t3;
  ef_win : RD.ls_window (RD.d_ls t3) = RD.ls_window (RD.d_ls p0);
  ef_hw : RD.ls_highwater (RD.d_ls t3) = RD.ls_highwater (RD.d_ls p0);
  ef_ma : RD.ls_matchavail (RD.d_ls t3) = RD.ls_matchavail (RD.d_ls p0);
  ef_ml : 0 <= RD.ls_matchlen (RD.d_ls t3) < 3;
  ef_pl : RD.ls_prevlen (RD.d_ls t3) = RD.ls_prevlen (RD.d_ls p0);
  ef_sum : RD.ls_strstart (RD.d_ls t3) + RD.ls_lookahead (RD.d_ls t3)
           = RD.ls_strstart (RD.d_ls p0) + RD.ls_lookahead (RD.d_ls p0);
  ef_adv : RD.ls_strstart (RD.d_ls p0) + 1 <= RD.ls_strstart (RD.d_ls t3);
  ef_la : 0 <= RD.ls_lookahead (RD.d_ls t3);
  ef_bs : RD.ls_blockstart (RD.d_ls t3) = RD.ls_blockstart (RD.d_ls p0);
  ef_ms : RD.ls_matchstart (RD.d_ls t3) = RD.ls_matchstart (RD.d_ls p0)
          \/ 1 <= RD.ls_matchstart (RD.d_ls t3) < RD.ls_strstart (RD.d_ls p0);
  ef_ins : RD.ls_insert (RD.d_ls t3) = RD.ls_insert (RD.d_ls p0);
  ef_ws : RD.ls_windowsize (RD.d_ls t3) = RD.ls_windowsize (RD.d_ls p0)
}.

Lemma rt_fast_emit_facts : forall p0,
  mt_inv p0 -> RC.dg_level (RD.d_cfg p0) <= 3 ->
  RD.ls_strstart (RD.d_ls p0) + 262 <= 65536 -> 1 <= RD.ls_lookahead (RD.d_ls p0) ->
  emit_facts p0 (snd (rt_fast_emit p0)).
Proof.
  intros p0 Hm Hlev Hroom Hla1.
  pose proof (m_cfg_facts p0 Hm) as Hc.
  destruct (mt_fast p0 Hm Hlev) as [Hf1 Hf2]. change RC.MIN_MATCH with 3 in Hf1, Hf2.
  pose proof (mt_ml p0 Hm) as Hml.
  destruct (rt_df_l1_facts p0 Hm Hroom) as (Fw & Fss & Fla & Fbs & Fhw & Fma & Fins & Fpl & Fws & Fpm & Fml & Fms).
  unfold rt_fast_emit. cbv zeta. set (l1 := RK.df_l1 p0) in *.
  change RC.MIN_MATCH with 3.
  destruct (Z.leb_spec 3 (RD.ls_matchlen l1)) as [Mt|Lt]; cbn [snd].
  - assert (Hml1 : RD.ls_matchlen l1 <= RD.ls_lookahead (RD.d_ls p0)) by (destruct Fml; lia).
    rt_ls.
    destruct (Z.leb (RD.ls_matchlen l1) (RC.dg_max_lazy_match (RD.d_cfg p0)) && (3 <=? RD.ls_lookahead l1 - RD.ls_matchlen l1)).
    + set (n := RD.ls_matchlen l1 - 1).
      destruct (rt_dfi_frame (Z.to_nat n + 1) (RD.d_cfg p0) n
                  (RD.setL_matchlen n (RD.setL_lookahead (RD.ls_lookahead l1 - RD.ls_matchlen l1) l1))
                  (cf_hash_mask _ Hc) (cf_w_mask _ Hc) ltac:(lia) ltac:(lia))
        as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
      rt_ls. constructor; cbn [RD.d_cfg RD.d_wrap RD.d_ls RD.d_strm RD.setD_ls RD.setD_ts]; rt_ls;
        rewrite ?B1, ?B2, ?B3, ?B4, ?B5, ?B6, ?B7, ?B8, ?B9, ?B10, ?B11, ?B12; rt_ls;
        rewrite ?Fw, ?Fss, ?Fla, ?Fbs, ?Fhw, ?Fma, ?Fins, ?Fpl, ?Fws; try reflexivity; try lia.
      all: first [ constructor; reflexivity | exact Fms | destruct Fml; lia ].
    + rt_ls. constructor; cbn [RD.d_cfg RD.d_wrap RD.d_ls RD.d_strm RD.setD_ls RD.setD_ts]; rt_ls;
        rewrite ?Fw, ?Fss, ?Fla, ?Fbs, ?Fhw, ?Fma, ?Fins, ?Fpl, ?Fws; try reflexivity; try lia.
      all: first [ constructor; reflexivity | exact Fms | destruct Fml; lia ].
  - rt_ls. constructor; cbn [RD.d_cfg RD.d_wrap RD.d_ls RD.d_strm RD.setD_ls RD.setD_ts]; rt_ls;
      rewrite ?Fw, ?Fss, ?Fla, ?Fbs, ?Fhw, ?Fma, ?Fins, ?Fpl, ?Fws; try reflexivity; try lia.
    all: first [ constructor; reflexivity | exact Fms | destruct Fml; lia ].
Qed.
