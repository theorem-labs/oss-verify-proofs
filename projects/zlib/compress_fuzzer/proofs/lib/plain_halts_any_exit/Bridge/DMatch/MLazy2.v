(** * Bridge.DMatch.MLazy2 — group M: pair D15, the insert loop after a match
    ([m_dsi]).

    S5's [deflate_slow_insert] against RT's [ds_insert]: both count down in
    [prev_length] (the bug-for-bug counter of [deflate.c:1983-1987]) and
    insert at each new [strstart] up to [max_insert]; S5's fuel is the
    counter, RT's the counter + 1.  [m_dsi] relates them and gives RT's
    frame ([dsi_frame]: [strstart] up by the counter, [prev_length] 0,
    every other read field kept). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MFill1 MFast2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require MFill3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.
Module SBlk := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk.

Lemma m_s5_dsi_S : forall f s mi,
  SBlk.deflate_slow_insert (S f) s mi
  = let s1 := DS.set_strstart s (DS.ds_strstart s + 1) in
    let s2 := if Z.leb (DS.ds_strstart s1) mi then fst (SLz.insert_string s1 (DS.ds_strstart s1)) else s1 in
    let s3 := DS.set_prev_length s2 (DS.ds_prev_length s2 - 1) in
    if negb (Z.eqb (DS.ds_prev_length s3) 0) then SBlk.deflate_slow_insert f s3 mi else s3.
Proof. intros f s mi. reflexivity. Qed.

(** The RT fields one conditional insert leaves alone. *)
Definition cin_frame (l l' : RD.LSt) : Prop :=
  RD.ls_window l' = RD.ls_window l /\ RD.ls_strstart l' = RD.ls_strstart l
  /\ RD.ls_lookahead l' = RD.ls_lookahead l /\ RD.ls_matchlen l' = RD.ls_matchlen l
  /\ RD.ls_prevlen l' = RD.ls_prevlen l /\ RD.ls_matchstart l' = RD.ls_matchstart l
  /\ RD.ls_prevmatch l' = RD.ls_prevmatch l /\ RD.ls_matchavail l' = RD.ls_matchavail l
  /\ RD.ls_blockstart l' = RD.ls_blockstart l /\ RD.ls_insert l' = RD.ls_insert l
  /\ RD.ls_highwater l' = RD.ls_highwater l /\ RD.ls_windowsize l' = RD.ls_windowsize l.

(** One conditional insert at [str] (S5's [if strstart <= max_insert]). *)
Lemma m_cond_insert : forall s T l str mi,
  lz_rel s (RD.setD_ls l T) -> s5_geom s -> cfg_facts (RD.d_cfg T) -> RD.ls_windowsize l = 65536 ->
  0 <= str -> mi + 2 < 65536 ->
  let s2 := if Z.leb str mi then fst (SLz.insert_string s str) else s in
  let l2 := if Z.leb str mi then snd (RD.insert_string (RD.d_cfg T) str l) else l in
  lz_rel s2 (RD.setD_ls l2 T) /\ nonlz_view s2 = nonlz_view s /\ cin_frame l l2.
Proof.
  intros s T l str mi Hl Hg Hc Hws Hs0 Hmi s2 l2. subst s2 l2.
  destruct (Z.leb_spec str mi) as [Le|Gt].
  - destruct (m_insert_string s (RD.setD_ls l T) str Hl Hg Hc Hws Hs0 ltac:(lia)) as (_ & I2 & I3).
    cbn [RD.d_ls RD.d_cfg RD.setD_ls] in I2, I3. rewrite rt_setD_ls_ls in I2.
    destruct (rt_ins_facts (RD.d_cfg T) str l (cf_hash_mask _ Hc) (cf_w_mask _ Hc))
      as (_ & _ & _ & _ & Kw & Kss & Kla & Kml & Kpl & Kms & Kpm & Kma & Kbs & Kins & Khw & Kws).
    split; [exact I2|]. split; [exact I3|].
    unfold cin_frame. repeat split; assumption.
  - split; [exact Hl|]. split; [reflexivity|].
    unfold cin_frame. repeat split; reflexivity.
Qed.

(** The RT fields [ds_insert] leaves alone, where it leaves [strstart], and
    its counter at 0. *)
Definition dsi_frame (l l' : RD.LSt) (n : Z) : Prop :=
  RD.ls_window l' = RD.ls_window l /\ RD.ls_strstart l' = RD.ls_strstart l + n
  /\ RD.ls_lookahead l' = RD.ls_lookahead l /\ RD.ls_matchlen l' = RD.ls_matchlen l
  /\ RD.ls_prevlen l' = 0 /\ RD.ls_matchstart l' = RD.ls_matchstart l
  /\ RD.ls_prevmatch l' = RD.ls_prevmatch l /\ RD.ls_matchavail l' = RD.ls_matchavail l
  /\ RD.ls_blockstart l' = RD.ls_blockstart l /\ RD.ls_insert l' = RD.ls_insert l
  /\ RD.ls_highwater l' = RD.ls_highwater l /\ RD.ls_windowsize l' = RD.ls_windowsize l.

Theorem m_dsi : forall f m s T l mi,
  lz_rel s (RD.setD_ls l T) -> s5_geom s -> cfg_facts (RD.d_cfg T) ->
  RD.ls_windowsize l = 65536 ->
  1 <= RD.ls_prevlen l -> RD.ls_prevlen l <= Z.of_nat f -> RD.ls_prevlen l < Z.of_nat m ->
  0 <= RD.ls_strstart l -> mi + 2 < 65536 ->
  lz_rel (SBlk.deflate_slow_insert f s mi) (RD.setD_ls (RD.ds_insert m (RD.d_cfg T) mi l) T)
  /\ nonlz_view (SBlk.deflate_slow_insert f s mi) = nonlz_view s
  /\ dsi_frame l (RD.ds_insert m (RD.d_cfg T) mi l) (RD.ls_prevlen l).
Proof.
  induction f as [|f IH]; intros m s T l mi Hl Hg Hc Hws Hn1 Hnf Hnm Hss0 Hmi; [lia|].
  destruct m as [|m]; [lia|].
  rewrite m_s5_dsi_S. cbn [RD.ds_insert]. cbv zeta.
  set (g := RD.d_cfg T) in *.
  set (ss := RD.ls_strstart l) in *.
  set (n := RD.ls_prevlen l) in *.
  pose proof (lzr_ss _ _ Hl) as Ess. cbn [RD.d_ls RD.setD_ls] in Ess. fold ss in Ess.
  (* strstart + 1 *)
  assert (A1 : lz_rel (DS.set_strstart s (DS.ds_strstart s + 1)) (RD.setD_ls (RD.setL_strstart (ss + 1) l) T))
    by (apply lz_set_strstart; [exact Hl | rewrite Ess; reflexivity]).
  set (s1 := DS.set_strstart s (DS.ds_strstart s + 1)) in *.
  assert (Ess1 : DS.ds_strstart s1 = ss + 1) by (subst s1; rewrite ds_strstart__set_strstart; lia).
  rewrite Ess1. rt_ls. fold ss.
  assert (Hg1 : s5_geom s1) by (subst s1; destruct Hg; constructor; assumption).
  set (L1 := RD.setL_strstart (ss + 1) l) in *.
  (* the conditional insert *)
  destruct (m_cond_insert s1 T L1 (ss + 1) mi A1 Hg1 Hc ltac:(subst L1; rt_ls; exact Hws) ltac:(lia) Hmi)
    as (C1 & C2 & C3).
  cbv zeta in C1, C2, C3.
  fold g in C1, C3.
  set (s2 := if ss + 1 <=? mi then fst (SLz.insert_string s1 (ss + 1)) else s1) in *.
  set (l2 := if ss + 1 <=? mi then snd (RD.insert_string g (ss + 1) L1) else L1) in *.
  destruct C3 as (Kw & Kss & Kla & Kml & Kpl & Kms & Kpm & Kma & Kbs & Kins & Khw & Kws).
  subst L1. rt_ls.
  cbn [RD.setL_strstart RD.ls_window RD.ls_strstart RD.ls_lookahead RD.ls_matchlen RD.ls_prevlen
       RD.ls_matchstart RD.ls_prevmatch RD.ls_matchavail RD.ls_blockstart RD.ls_insert RD.ls_highwater
       RD.ls_windowsize] in Kw, Kss, Kla, Kml, Kpl, Kms, Kpm, Kma, Kbs, Kins, Khw, Kws.
  fold ss n in Kw, Kss, Kla, Kml, Kpl, Kms, Kpm, Kma, Kbs, Kins, Khw, Kws.
  (* prev_length - 1 *)
  pose proof (lzr_pl _ _ C1) as Epl2. cbn [RD.d_ls RD.setD_ls] in Epl2.
  assert (A3 : lz_rel (DS.set_prev_length s2 (DS.ds_prev_length s2 - 1))
                      (RD.setD_ls (RD.setL_prevlen (n - 1) l2) T))
    by (apply lz_set_prev_length; [exact C1 | rewrite Epl2, Kpl; reflexivity]).
  set (s3 := DS.set_prev_length s2 (DS.ds_prev_length s2 - 1)) in *.
  assert (Epl3 : DS.ds_prev_length s3 = n - 1)
    by (subst s3; rewrite ds_prev_length__set_prev_length, Epl2, Kpl; reflexivity).
  rewrite Epl3. rewrite Kpl.
  assert (Hv3 : nonlz_view s3 = nonlz_view s)
    by (transitivity (nonlz_view s2); [reflexivity|]; rewrite C2; reflexivity).
  destruct (Z.eqb_spec (n - 1) 0) as [E0|E0]; cbn [negb].
  - split; [exact A3|]. split; [exact Hv3|].
    unfold dsi_frame. rt_ls. rewrite Kw, Kss, Kla, Kml, Kms, Kpm, Kma, Kbs, Kins, Khw, Kws.
    repeat (split; [reflexivity || lia|]). reflexivity.
  - assert (Hg3 : s5_geom s3) by (exact (MFill3.m_geom_nonlz s s3 Hv3 Hg)).
    destruct (IH m s3 T (RD.setL_prevlen (n - 1) l2) mi A3 Hg3 Hc ltac:(rt_ls; rewrite Kws; exact Hws)
                ltac:(rt_ls; lia) ltac:(rt_ls; lia) ltac:(rt_ls; lia) ltac:(rt_ls; rewrite Kss; lia) Hmi)
      as (R1 & R2 & R3).
    fold g in R1, R3.
    split; [exact R1|]. split; [rewrite R2; exact Hv3|].
    destruct R3 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
    rt_ls. unfold dsi_frame.
    rewrite B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12. rt_ls.
    rewrite Kw, Kss, Kla, Kml, Kms, Kpm, Kma, Kbs, Kins, Khw, Kws.
    repeat (split; [reflexivity || lia|]). reflexivity.
Qed.

(** RT's half alone (the loop facts, without S5). *)
Lemma rt_dsi_frame : forall m g mi l,
  RC.dg_hash_mask g = 32767 -> RC.dg_w_mask g = 32767 ->
  1 <= RD.ls_prevlen l -> RD.ls_prevlen l < Z.of_nat m ->
  dsi_frame l (RD.ds_insert m g mi l) (RD.ls_prevlen l).
Proof.
  induction m as [|m IH]; intros g mi l Hhm Hwm Hn Hm; [lia|].
  cbn [RD.ds_insert]. cbv zeta. rt_ls.
  set (L1 := RD.setL_strstart (RD.ls_strstart l + 1) l).
  assert (C : cin_frame L1 (if RD.ls_strstart l + 1 <=? mi
                            then snd (RD.insert_string g (RD.ls_strstart l + 1) L1) else L1)).
  { destruct (RD.ls_strstart l + 1 <=? mi); [|unfold cin_frame; repeat split; reflexivity].
    destruct (rt_ins_facts g (RD.ls_strstart l + 1) L1 Hhm Hwm)
      as (_ & _ & _ & _ & Kw & Kss & Kla & Kml & Kpl & Kms & Kpm & Kma & Kbs & Kins & Khw & Kws).
    unfold cin_frame. repeat split; assumption. }
  set (l2 := if RD.ls_strstart l + 1 <=? mi then snd (RD.insert_string g (RD.ls_strstart l + 1) L1) else L1) in *.
  destruct C as (Kw & Kss & Kla & Kml & Kpl & Kms & Kpm & Kma & Kbs & Kins & Khw & Kws).
  subst L1. rt_ls.
  cbn [RD.setL_strstart RD.ls_window RD.ls_strstart RD.ls_lookahead RD.ls_matchlen RD.ls_prevlen
       RD.ls_matchstart RD.ls_prevmatch RD.ls_matchavail RD.ls_blockstart RD.ls_insert RD.ls_highwater
       RD.ls_windowsize] in Kw, Kss, Kla, Kml, Kpl, Kms, Kpm, Kma, Kbs, Kins, Khw, Kws.
  rewrite Kpl.
  destruct (Z.eqb_spec (RD.ls_prevlen l - 1) 0) as [E0|E0].
  - unfold dsi_frame. rt_ls. rewrite Kw, Kss, Kla, Kml, Kms, Kpm, Kma, Kbs, Kins, Khw, Kws.
    repeat (split; [reflexivity || lia|]). reflexivity.
  - destruct (IH g mi (RD.setL_prevlen (RD.ls_prevlen l - 1) l2) Hhm Hwm ltac:(rt_ls; lia) ltac:(rt_ls; lia))
      as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
    unfold dsi_frame. rewrite B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12. rt_ls.
    rewrite Kw, Kss, Kla, Kml, Kms, Kpm, Kma, Kbs, Kins, Khw, Kws.
    repeat (split; [reflexivity || lia|]). reflexivity.
Qed.
