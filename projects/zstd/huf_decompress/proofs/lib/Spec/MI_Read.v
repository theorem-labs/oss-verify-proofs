(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (18 recorded proofs replaced by written proofs (rd8_known, known_at, rd8_ftree and 15 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Read () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3rd8C1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6LookupC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeK35stdpp8fin_maps6FinMap01C47Corelib4Init5Logic6eq_indI35stdpp4gmap4gmap00C35stdpp4base4fmapC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldI47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev05C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>peek_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8eq_ind_rI59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6MI_Inv5knownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree5ftreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z8ltb_specK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib4Spec7MI_Read9rd8_ftreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4rd16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3divC47Corelib4Init5Logic9False_indC35stdpp4base5emptyC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC35stdpp8fin_maps<lookup_emptyC59OSSVerify5KrLib4Spec6Malloc8stale_pgC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC35stdpp6option;from_optionC35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc5staleC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalI59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z6shiftrK47Corelib7Numbers7BinNums8positive01c59OSSVerify5KrLib4Spec7MI_Read8land_255C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:shiftr_0_rC56Stdlib6ZArith6BinInt1Z7mul_0_rC59OSSVerify5KrLib4Spec6MI_Inv7byte_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z9mod_smallc59OSSVerify5KrLib4Spec7MI_Read9byte_of_1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Read9byte_of_0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_divc59OSSVerify5KrLib4Spec7MI_Read9byte_of_3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Read9byte_of_2C1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z9div_add_lC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC59OSSVerify5KrLib4Spec6MI_Inv5mslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7area_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Z_mod_mult".
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rd8_known {R} st q v (k : Z -> M R) :
  cell_read (get_shadow st (fst q)) (snd q) = Known v -> rd8 st q k = k v.
Proof. intros H. unfold rd8. rewrite H. reflexivity. Qed.

Lemma known_at st rid o v rid' o' :
  known st (rid, o) v -> o' = o -> rid' = rid -> cell_read (get_shadow st rid') o' = Known v.
Proof. intros H -> ->. exact H. Qed.

(* [comment removed for export] *)
Lemma rd8_ftree {R} L st q (k : Z -> M R) Post :
  (forall v, cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256) ->
  (forall v, 0 <= v < 256 -> ftree L (k v) Post) ->
  ftree L (rd8 st q k) Post.
Proof.
  intros Hk H. unfold rd8. destruct (cell_read _ _) as [v|h] eqn:E.
  - apply H. apply Hk. reflexivity.
  - cbn [ftree]. intros v Hv. unfold peek_answer_ok.
    destruct (Z.leb_spec 0 v), (Z.ltb_spec v 256); cbn [andb]; try lia. apply H. lia.
Qed.

Lemma rd16_ftree {R} L st q (k : Z -> M R) Post :
  (forall q' v, cell_read (get_shadow st (fst q')) (snd q') = Known v -> 0 <= v < 256) ->
  (forall v, 0 <= v < 65536 -> ftree L (k v) Post) ->
  ftree L (rd16 st q k) Post.
Proof.
  intros Hk H. unfold rd16. apply rd8_ftree; [apply Hk|]. intros b0 H0. apply rd8_ftree; [apply Hk|]. intros b1 H1. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma known_byte st rid o v :
  (forall sh o' v' t, s_shadow st !! rid = Some sh -> r_cells sh !! o' = Some (v', t) -> 0 <= v' < 256) ->
  cell_read (get_shadow st rid) o = Known v -> 0 <= v < 256.
Proof.
  intros Hc H. unfold cell_read, get_shadow in H. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn [default id] in H.
  - destruct (r_cells sh !! o) as [[v' t]|] eqn:E2.
    + match type of H with (if ?c then _ else _) = _ => destruct c end; inversion H. subst. eapply Hc; eauto.
    + match type of H with (if ?c then _ else _) = _ => destruct c end; inversion H. lia.
  - rewrite !lookup_empty in H. cbn in H. inversion H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_255 x : 0 <= x -> Z.land x 255 = x mod 256.
Proof. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma byte_of_0 x : 0 <= x -> byte_of x 0 = x mod 256.
Proof. intros. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r. apply land_255. lia. Qed.
Lemma byte_of_1 x : 0 <= x -> byte_of x 1 = (x / 256) mod 256.
Proof. intros. unfold byte_of. replace (8 * 1) with 8 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. apply land_255. apply Z.div_pos; lia. Qed.
Lemma byte_of_2 x : 0 <= x -> byte_of x 2 = (x / 65536) mod 256.
Proof. intros. unfold byte_of. replace (8 * 2) with 16 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. apply land_255. apply Z.div_pos; lia. Qed.
Lemma byte_of_3 x : 0 <= x -> byte_of x 3 = (x / 16777216) mod 256.
Proof. intros. unfold byte_of. replace (8 * 3) with 24 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216. apply land_255. apply Z.div_pos; lia. Qed.

Lemma byte_of_range x k : 0 <= x -> 0 <= k -> 0 <= byte_of x k < 256.
Proof.
  intros. unfold byte_of. rewrite land_255 by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; [lia| apply Z.pow_pos_nonneg; lia]).
  apply Z.mod_pos_bound. lia.
Qed.

Lemma u16_bytes q : 0 <= q < 2^16 -> byte_of q 0 + 256 * byte_of q 1 = q.
Proof. intros. rewrite byte_of_0, byte_of_1 by lia. rewrite (Z.mod_small (q / 256)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). pose proof (Z.div_mod q 256 ltac:(lia)). lia. Qed.

Lemma u32_bytes r : 0 <= r < 2^32 ->
  byte_of r 0 + 256 * byte_of r 1 + 65536 * byte_of r 2 + 16777216 * byte_of r 3 = r.
Proof.
  intros. rewrite byte_of_0, byte_of_1, byte_of_2, byte_of_3 by lia.
  pose proof (Z.div_mod r 256 ltac:(lia)) as E1.
  pose proof (Z.div_mod (r / 256) 256 ltac:(lia)) as E2. rewrite (Z.div_div r 256 256) in E2 by lia. change (256 * 256) with 65536 in E2.
  pose proof (Z.div_mod (r / 65536) 256 ltac:(lia)) as E3. rewrite (Z.div_div r 65536 256) in E3 by lia. change (65536 * 256) with 16777216 in E3.
  rewrite (Z.mod_small (r / 16777216)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  lia.
Qed.

(* [comment removed for export] *)
Lemma land31_idx i r : 0 <= i <= 31 -> 0 <= r -> Z.land (i + 32 * r) 31 = i.
Proof.
  intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
  replace (i + 32 * r) with (i + r * 32) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma shiftr5_res i r : 0 <= i <= 31 -> 0 <= r -> Z.shiftr (i + 32 * r) 5 = r.
Proof.
  intros. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  replace (i + 32 * r) with (r * 32 + i) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma area_of_mslot a k : snd a mod PGSZ = 0 -> 0 <= k < NSLOTS -> area_of (mslot a k) = a.
Proof.
  intros Ha Hk. unfold area_of, mslot, aadd, AREA_HDR, META_SIZE, NSLOTS, PGSZ in *. destruct a as [r o]; cbn in *. f_equal.
  rewrite <- Zplus_mod_idemp_l, Ha. cbn [Z.add]. rewrite Z.mod_small by lia. lia.
Qed.

Lemma mod_pg_mod16 x : x mod PGSZ = 0 -> x mod 16 = 0.
Proof. intros H. unfold PGSZ in H. pose proof (Z.div_mod x 4096 ltac:(lia)). rewrite H in H0.
  rewrite H0. replace (4096 * (x / 4096) + 0) with ((256 * (x / 4096)) * 16) by lia. apply Z_mod_mult. Qed.

Lemma mslot_mod8 a k : snd a mod PGSZ = 0 -> snd (mslot a k) mod 8 = 0.
Proof.
  intros Ha. unfold mslot, aadd, AREA_HDR, META_SIZE. cbn [snd].
  pose proof (Z.div_mod (snd a) 4096 ltac:(lia)). unfold PGSZ in Ha. rewrite Ha in H.
  rewrite H. replace (4096 * (snd a / 4096) + 0 + (24 + 40 * k)) with ((512 * (snd a / 4096) + 3 + 5 * k) * 8) by lia. apply Z_mod_mult.
Qed.
