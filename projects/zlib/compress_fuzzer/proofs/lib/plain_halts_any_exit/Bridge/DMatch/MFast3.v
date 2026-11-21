(** * Bridge.DMatch.MFast3 — group M: pair D14, the RT-side facts of a trip and the
    insert loop after a match.

    - [rt_lm_facts]: RT's [longest_match] reports a length in
      [[0, lookahead]] and a start that is either the old [match_start] or a
      chain position in [[1, strstart)].
    - [rt_df_l1_facts]: RT's window state after the insert and the search
      ([df_l1]), field by field.
    - [m_dfi]: S5's [deflate_fast_insert] (counter in [match_length], fuel
      exactly that) against RT's [df_insert] (counter [n], fuel [n + 1],
      [match_length] untouched).  Inside the loop S5's [match_length] is
      RT's counter, so the relation is taken against RT's state with
      [match_length := n]; both end with it at 0. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MFill1 MFast2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.
Module SBlk := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk.

(* ------------------------------------------------------------------------- *)
(* 1.  RT's longest_match: range of its answers                              *)
(* ------------------------------------------------------------------------- *)

Lemma rt_lm_loop_facts : forall f c st ms0 b0,
  0 <= RD.x_limit c ->
  (forall i, 0 <= i < 32768 -> RD.x_prev c i = 0 \/ RD.x_prev c i < RD.x_scan c) ->
  RD.x_wmask c = 32767 ->
  1 <= RD.m_cur st < RD.x_scan c ->
  (RD.m_start st = ms0 \/ 1 <= RD.m_start st < RD.x_scan c) -> b0 <= RD.m_best st ->
  let r := RD.lm_loop f c st in
  (RD.m_start r = ms0 \/ 1 <= RD.m_start r < RD.x_scan c) /\ b0 <= RD.m_best r.
Proof.
  induction f as [|f IH]; intros c st ms0 b0 Hlim Hpv Hwm Hcur Hst Hb r; subst r; cbn [RD.lm_loop];
    [split; assumption|].
  assert (Hn : (RD.m_start (RD.lm_next c st) = ms0 \/ 1 <= RD.m_start (RD.lm_next c st) < RD.x_scan c)
               /\ b0 <= RD.m_best (RD.lm_next c st)
               /\ RD.m_cur (RD.lm_next c st) = RD.m_cur st).
  { unfold RD.lm_next. destruct (RD.lm_hit c st) eqn:Eh; cbn [RD.m_start RD.m_best RD.m_cur].
    - unfold RD.lm_hit in Eh. apply andb_prop in Eh as [_ Eh]. apply Z.ltb_lt in Eh.
      split; [right; lia|]. split; [lia | reflexivity].
    - split; [exact Hst|]. split; [exact Hb | reflexivity]. }
  destruct Hn as (N1 & N2 & N3).
  unfold RD.lm_step. cbv zeta. rewrite Hwm.
  destruct (RD.lm_hit c st && (RD.x_nice c <=? RD.lm_len c st)); [split; assumption|].
  pose proof (m_land_wmask (RD.m_cur st)) as Hix.
  destruct (Hpv _ Hix) as [P|P].
  - rewrite P. destruct (Z.ltb_spec (RD.x_limit c) 0); [lia|]. cbn [andb RD.m_start RD.m_best].
    split; assumption.
  - destruct (Z.ltb_spec (RD.x_limit c) (RD.x_prev c (Z.land (RD.m_cur st) 32767))) as [Lt|Ge];
      cbn [andb].
    + destruct (negb (RD.m_chain (RD.lm_next c st) - 1 =? 0)).
      * apply IH; cbn [RD.m_cur RD.m_start RD.m_best]; try assumption. lia.
      * cbn [RD.m_start RD.m_best]. split; assumption.
    + cbn [RD.m_start RD.m_best]. split; assumption.
Qed.

Lemma rt_lm_facts : forall g l cm,
  RC.dg_w_mask g = 32767 -> RC.dg_max_dist g = 32506 ->
  1 <= cm < RD.ls_strstart l -> 0 <= RD.ls_prevlen l <= 258 -> 0 <= RD.ls_lookahead l ->
  (forall i, 0 <= i < 32768 -> RD.ls_prev l i = 0 \/ RD.ls_prev l i < RD.ls_strstart l) ->
  let r := RD.longest_match g l cm in
  (0 <= fst r <= RD.ls_lookahead l /\ fst r <= 258)
  /\ (snd r = RD.ls_matchstart l \/ 1 <= snd r < RD.ls_strstart l).
Proof.
  intros g l cm Hwm Hmd Hcm Hpl Hla Hpv r. subst r.
  pose proof (RD.longest_match_le_MAX g l cm ltac:(change RC.MAX_MATCH with 258; lia)) as Hmax.
  change RC.MAX_MATCH with 258 in Hmax.
  assert (Hrest : 0 <= fst (RD.longest_match g l cm) <= RD.ls_lookahead l
                  /\ (snd (RD.longest_match g l cm) = RD.ls_matchstart l
                      \/ 1 <= snd (RD.longest_match g l cm) < RD.ls_strstart l)).
  { unfold RD.longest_match. cbv zeta. rewrite Hmd, Hwm.
    match goal with |- context [RD.lm_loop ?f ?c ?st] =>
      destruct (rt_lm_loop_facts f c st (RD.ls_matchstart l) (RD.ls_prevlen l)) as [R1 R2];
      cbn [RD.x_limit RD.x_prev RD.x_scan RD.x_wmask RD.m_cur RD.m_start RD.m_best]; try lia;
      try (left; reflexivity); try exact Hpv
    end.
    - destruct (Z.ltb_spec 32506 (RD.ls_strstart l)); unfold RD.NIL; lia.
    - cbn [fst snd]. split; [|exact R1].
      match goal with |- context [if ?c then _ else _] => destruct c eqn:E end;
        [apply Z.leb_le in E | apply Z.leb_gt in E]; lia. }
  destruct Hrest as [A C]. split; [split; [exact A | exact Hmax] | exact C].
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  RT's window state after the insert and the search                     *)
(* ------------------------------------------------------------------------- *)

Lemma rt_df_l1_facts : forall p0,
  mt_inv p0 -> RD.ls_strstart (RD.d_ls p0) + 262 <= 65536 ->
  let l := RD.d_ls p0 in
  let l1 := RK.df_l1 p0 in
  RD.ls_window l1 = RD.ls_window l /\ RD.ls_strstart l1 = RD.ls_strstart l
  /\ RD.ls_lookahead l1 = RD.ls_lookahead l /\ RD.ls_blockstart l1 = RD.ls_blockstart l
  /\ RD.ls_highwater l1 = RD.ls_highwater l /\ RD.ls_matchavail l1 = RD.ls_matchavail l
  /\ RD.ls_insert l1 = RD.ls_insert l /\ RD.ls_prevlen l1 = RD.ls_prevlen l
  /\ RD.ls_windowsize l1 = RD.ls_windowsize l /\ RD.ls_prevmatch l1 = RD.ls_prevmatch l
  /\ (RD.ls_matchlen l1 = RD.ls_matchlen l \/ (0 <= RD.ls_matchlen l1 <= RD.ls_lookahead l /\ RD.ls_matchlen l1 <= 258))
  /\ (RD.ls_matchstart l1 = RD.ls_matchstart l \/ 1 <= RD.ls_matchstart l1 < RD.ls_strstart l).
Proof.
  intros p0 Hm Hroom l l1. subst l l1.
  pose proof (m_cfg_facts p0 Hm) as Hc. pose proof (mt_ms p0 Hm) as Hms.
  pose proof (RK.mi_chain _ Hms) as Hch. pose proof (RK.mi_look _ Hms) as Hla0.
  pose proof (mt_ml p0 Hm) as Hml.
  unfold RK.df_l1. cbv zeta.
  destruct (Z.leb RC.MIN_MATCH (RD.ls_lookahead (RD.d_ls p0))).
  - destruct (rt_ins_prev_ok (RD.d_cfg p0) (RD.d_ls p0) Hc Hch) as (H0 & H1 & Hpv0).
    destruct (rt_ins_facts (RD.d_cfg p0) (RD.ls_strstart (RD.d_ls p0)) (RD.d_ls p0)
                (cf_hash_mask _ Hc) (cf_w_mask _ Hc))
      as (_ & _ & _ & _ & Jw & Jss & Jla & Jml & Jpl & Jms & Jpm & Jma & Jbs & Jins & Jhw & Jws).
    set (r := RD.insert_string (RD.d_cfg p0) (RD.ls_strstart (RD.d_ls p0)) (RD.d_ls p0)) in *.
    destruct (negb (fst r =? RD.NIL) && (RD.ls_strstart (snd r) - fst r <=? RC.dg_max_dist (RD.d_cfg p0))) eqn:EC.
    + apply andb_prop in EC as [EC1 _]. apply negb_true_iff, Z.eqb_neq in EC1. unfold RD.NIL in EC1.
      destruct (rt_lm_facts (RD.d_cfg p0) (snd r) (fst r) (cf_w_mask _ Hc) (cf_max_dist _ Hc))
        as [K1 K2]; rewrite ?Jss, ?Jpl, ?Jla; try lia.
      { intros i Hi. destruct (Hpv0 i Hi) as [_ P]. exact P. }
      rt_ls. rewrite Jw, Jss, Jla, Jbs, Jhw, Jma, Jins, Jpl, Jws, Jpm.
      rewrite ?Jla, ?Jms, ?Jss in K1, K2 |- *.
      repeat (split; [reflexivity|]). split; [right; exact K1 | exact K2].
    + rewrite Jw, Jss, Jla, Jbs, Jhw, Jma, Jins, Jpl, Jws, Jpm, Jml, Jms.
      repeat (split; [reflexivity|]). split; left; reflexivity.
  - cbn [fst snd]. unfold RD.NIL. cbn [Z.eqb negb andb].
    repeat (split; [reflexivity|]). split; left; reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The insert loop after a match                                         *)
(* ------------------------------------------------------------------------- *)

Lemma m_s5_dfi_S : forall f s,
  SBlk.deflate_fast_insert (S f) s
  = let s1 := DS.set_strstart s (DS.ds_strstart s + 1) in
    let s2 := fst (SLz.insert_string s1 (DS.ds_strstart s1)) in
    let s3 := DS.set_match_length s2 (DS.ds_match_length s2 - 1) in
    if negb (Z.eqb (DS.ds_match_length s3) 0) then SBlk.deflate_fast_insert f s3 else s3.
Proof. intros f s. cbn [SBlk.deflate_fast_insert]. cbv zeta. destruct (SLz.insert_string _ _). reflexivity. Qed.

(** The RT fields [df_insert] leaves alone, and where it leaves [strstart]. *)
Definition dfi_frame (l l' : RD.LSt) (n : Z) : Prop :=
  RD.ls_window l' = RD.ls_window l /\ RD.ls_strstart l' = RD.ls_strstart l + n
  /\ RD.ls_lookahead l' = RD.ls_lookahead l /\ RD.ls_matchlen l' = RD.ls_matchlen l
  /\ RD.ls_prevlen l' = RD.ls_prevlen l /\ RD.ls_matchstart l' = RD.ls_matchstart l
  /\ RD.ls_prevmatch l' = RD.ls_prevmatch l /\ RD.ls_matchavail l' = RD.ls_matchavail l
  /\ RD.ls_blockstart l' = RD.ls_blockstart l /\ RD.ls_insert l' = RD.ls_insert l
  /\ RD.ls_highwater l' = RD.ls_highwater l /\ RD.ls_windowsize l' = RD.ls_windowsize l.

Theorem m_dfi : forall f m s T l n,
  lz_rel s (RD.setD_ls (RD.setL_matchlen n l) T) -> s5_geom s -> cfg_facts (RD.d_cfg T) ->
  RD.ls_windowsize l = 65536 ->
  1 <= n -> n <= Z.of_nat f -> n < Z.of_nat m ->
  0 <= RD.ls_strstart l -> RD.ls_strstart l + n + 2 < 65536 ->
  lz_rel (SBlk.deflate_fast_insert f s)
         (RD.setD_ls (RD.setL_matchlen 0 (RD.df_insert m (RD.d_cfg T) n l)) T)
  /\ nonlz_view (SBlk.deflate_fast_insert f s) = nonlz_view s
  /\ dfi_frame l (RD.df_insert m (RD.d_cfg T) n l) n.
Proof.
  induction f as [|f IH]; intros m s T l n Hl Hg Hc Hws Hn1 Hnf Hnm Hss0 Hss1; [lia|].
  destruct m as [|m]; [lia|].
  rewrite m_s5_dfi_S. cbn [RD.df_insert]. cbv zeta.
  set (g := RD.d_cfg T) in *.
  set (ss := RD.ls_strstart l) in *.
  pose proof (lzr_ss _ _ Hl) as Ess. cbn [RD.d_ls RD.setD_ls RD.setL_matchlen RD.ls_strstart] in Ess. fold ss in Ess.
  (* strstart + 1 *)
  assert (A1 : lz_rel (DS.set_strstart s (DS.ds_strstart s + 1))
                      (RD.setD_ls (RD.setL_strstart (ss + 1) (RD.setL_matchlen n l)) T))
    by (apply lz_set_strstart; [exact Hl | rewrite Ess; reflexivity]).
  set (s1 := DS.set_strstart s (DS.ds_strstart s + 1)) in *.
  assert (Ess1 : DS.ds_strstart s1 = ss + 1) by (subst s1; rewrite ds_strstart__set_strstart; lia).
  rewrite Ess1.
  assert (Hg1 : s5_geom s1) by (subst s1; destruct Hg; constructor; assumption).
  set (L1 := RD.setL_strstart (ss + 1) (RD.setL_matchlen n l)).
  (* the insert at strstart + 1 *)
  destruct (m_insert_string s1 (RD.setD_ls L1 T) (ss + 1) A1 Hg1 Hc ltac:(subst L1; rt_ls; exact Hws)
              ltac:(lia) ltac:(lia)) as (_ & I2 & I3).
  cbn [RD.d_ls RD.d_cfg RD.setD_ls] in I2. rewrite rt_setD_ls_ls in I2. fold g in I2.
  set (s2 := fst (SLz.insert_string s1 (ss + 1))) in *.
  pose proof (lzr_ml _ _ I2) as Eml2. cbn [RD.d_ls RD.setD_ls] in Eml2.
  destruct (rt_ins_facts g (ss + 1) L1 (cf_hash_mask _ Hc) (cf_w_mask _ Hc))
    as (_ & _ & _ & _ & Jw & Jss & Jla & Jml & Jpl & Jms & Jpm & Jma & Jbs & Jins & Jhw & Jws).
  rewrite Jml in Eml2. subst L1. cbn [RD.setL_strstart RD.setL_matchlen RD.ls_matchlen] in Eml2.
  (* match_length - 1 *)
  set (l2 := snd (RD.insert_string g (RD.ls_strstart (RD.setL_strstart (ss + 1) l)) (RD.setL_strstart (ss + 1) l))).
  assert (A3 : lz_rel (DS.set_match_length s2 (DS.ds_match_length s2 - 1))
                      (RD.setD_ls (RD.setL_matchlen (n - 1) l2) T)).
  { pose proof (lz_set_match_length s2 T _ (DS.ds_match_length s2 - 1) (n - 1) I2 ltac:(rewrite Eml2; reflexivity))
      as H. exact H. }
  set (s3 := DS.set_match_length s2 (DS.ds_match_length s2 - 1)) in *.
  assert (Eml3 : DS.ds_match_length s3 = n - 1) by (subst s3; rewrite ds_match_length__set_match_length; lia).
  rewrite Eml3.
  assert (Hv3 : nonlz_view s3 = nonlz_view s)
    by (transitivity (nonlz_view s2); [reflexivity|]; transitivity (nonlz_view s1); [exact I3 | reflexivity]).
  (* RT fields of l2 *)
  destruct (rt_ins_facts g (ss + 1) (RD.setL_strstart (ss + 1) l) (cf_hash_mask _ Hc) (cf_w_mask _ Hc))
    as (_ & _ & _ & _ & Kw & Kss & Kla & Kml & Kpl & Kms & Kpm & Kma & Kbs & Kins & Khw & Kws).
  cbn [RD.setL_strstart RD.ls_window RD.ls_strstart RD.ls_lookahead RD.ls_matchlen RD.ls_prevlen
       RD.ls_matchstart RD.ls_prevmatch RD.ls_matchavail RD.ls_blockstart RD.ls_insert RD.ls_highwater
       RD.ls_windowsize] in Kw, Kss, Kla, Kml, Kpl, Kms, Kpm, Kma, Kbs, Kins, Khw, Kws.
  change (snd (RD.insert_string g (ss + 1) (RD.setL_strstart (ss + 1) l))) with l2 in *.
  rt_ls. fold ss. fold l2.
  destruct (Z.eqb_spec (n - 1) 0) as [E0|E0]; cbn [negb].
  - rewrite E0 in A3. split; [exact A3|]. split; [exact Hv3|].
    unfold dfi_frame. rewrite Kw, Kss, Kla, Kml, Kpl, Kms, Kpm, Kma, Kbs, Kins, Khw, Kws.
    repeat (split; [reflexivity || lia|]). reflexivity.
  - assert (Hg3 : s5_geom s3) by (exact (MFill3.m_geom_nonlz s s3 Hv3 Hg)).
    destruct (IH m s3 T l2 (n - 1) A3 Hg3 Hc ltac:(rewrite Kws; exact Hws) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(rewrite Kss; lia) ltac:(rewrite Kss; lia)) as (R1 & R2 & R3).
    fold g in R1, R3.
    split; [exact R1|]. split; [rewrite R2; exact Hv3|].
    destruct R3 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
    unfold dfi_frame. rewrite B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12.
    rewrite Kw, Kss, Kla, Kml, Kpl, Kms, Kpm, Kma, Kbs, Kins, Khw, Kws.
    repeat (split; [reflexivity || lia|]). reflexivity.
Qed.
