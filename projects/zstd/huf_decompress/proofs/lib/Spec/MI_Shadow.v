(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (29 recorded proofs replaced by written proofs (stale_hav_add_some, stale_hav_add_none, havoc_units_lookup and 26 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl MI_Kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Shadow () := "C46Stdlib5Lists4List2InC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4base4fmapI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C45stdpp;list_basics4list;filter_consC47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_maps:map_eq_iffC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib4Spec9MI_Shadow8hl_ticksC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC45stdpp;list_basics4list;list_filterC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib4Bool4Bool7Is_trueC35stdpp9decidable;Is_true_decC35stdpp4base6filterC46Stdlib5Lists4List7existsbC47Corelib4Init9Datatypes3orbK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2or01C56Stdlib6NArith6BinNat1N2leK47Corelib4Init5Logic2or02C47Corelib4Init5Logic3notC35stdpp4base6decideI47Corelib4Init6Specif7sumbool00C47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic3and00C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6NArith6BinNat1N3ltbC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6NArith6BinNat1N2ltC56Stdlib6NArith6BinNat1N6ltb_ltC35stdpp4base>Is_true_true_2I47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6NArith6BinNat1N6ltb_geK46Stdlib9micromega6VarMap1t01C47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib4Spec6Malloc7hav_addC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc5staleC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith4Znat3N2Z6inj_ltC56Stdlib6ZArith4Znat3N2Z6inj_leK47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic5False00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums8positive03C46Stdlib4Bool4Bool;andb_true_rC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes2idC56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z4iterC56Stdlib6ZArith6BinInt1Z3lebK46Stdlib9micromega7EnvRing5PExpr01C56Stdlib6ZArith6BinInt5Pos2Z:pos_is_posK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z8leb_specK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppK47Corelib4Init5Logic3and01C45stdpp7numbers1Z6eq_decC35stdpp6option;from_optionC35stdpp7tactics<f_equal_helpC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC57Corelib7BinNums6IntDef1Z3addC47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec6MI_Kit:Z_iter_indC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc;havoc_unitsC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC35stdpp4base6insertK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega3Op201C35stdpp9countable;Z_countableI47Corelib7Numbers7BinNums8positive00C59OSSVerify5KrLib4Spec6Malloc;havoc_pagesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;div_le_monoc59OSSVerify5KrLib4Spec9MI_Shadow:div16_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z7div_addC47Corelib4Init5Logic6eq_indc59OSSVerify5KrLib4Spec9MI_ShadowBhavoc_units_lookupC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof03c59OSSVerify5KrLib4Spec9MI_ShadowBstale_hav_add_someC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_ShadowBstale_hav_add_noneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC46Stdlib9micromega;ZifyClasses;rew_iff_revI35stdpp4base<list_elem_of00C35stdpp4base7elem_ofC35stdpp4base?list_elem_of_InC35stdpp4base8DecisionC45stdpp;list_basics4listClist_elem_of_filterC47Corelib4Init5Logic7and_indC47Corelib4Init5Logic7f_equalc59OSSVerify5KrLib4Spec9MI_Shadow=hav_add_ticksC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_ShadowAhavoc_units_ticksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6NArith6BinNat1N3eqbC56Stdlib6NArith6BinNat1N8eqb_reflC59OSSVerify5KrLib4Spec6MI_KitEget_shadow_upd_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5havocC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N8eqb_specC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z9mul_assocC59OSSVerify5KrLib4Spec6Malloc8stale_pgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_Shadow=default_ticksC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_ShadowBhavoc_pages_lookupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_Shadow?havoc_units_outC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_Shadow5fp_geC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_Shadow5lp_leC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c59OSSVerify5KrLib4Spec9MI_Shadow5lp_alC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_Shadow<havoc_shadowC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool<orb_true_iffc59OSSVerify5KrLib4Spec9MI_Shadow>havoc_units_inC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC45stdpp7numbers1N6eq_decC59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_Shadow?havoc_stale_outC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_ShadowBhavoc_other_regionC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_Shadow>havoc_stale_inC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc9hdr_havocC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses9not_morphC57Corelib7BinNums6IntDef1Z3divc59OSSVerify5KrLib4Spec9MI_ShadowFhdr_havoc_other_regionC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_Shadow@hdr_havoc_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:div_uniqueC46Stdlib4Bool4Bool:orb_true_rC47Corelib4Init5Logic5proj2".
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hl_ticks (hl : list (Z * N)) (t : N) : Prop := forall ch, In ch hl -> (snd ch <= t)%N.

Lemma stale_hav_add_some cov t hl b tk :
  hl_ticks hl t ->
  stale (hav_add cov t hl) b (Some tk) = ((b <? cov) && (tk <? t)%N) || stale hl b (Some tk).
Proof.
  intros Ht. unfold hav_add, stale. cbn [existsb fst snd].
  destruct ((b <? cov) && (tk <? t)%N) eqn:E; cbn [orb]; [reflexivity|].
  induction hl as [|[c h] hl IH]; [reflexivity|].
  assert (Hh : (h <= t)%N) by (apply (Ht (c, h)); left; reflexivity).
  assert (IH' : existsb (fun ch : Z * N => (b <? fst ch) && (tk <? snd ch)%N) (filter (fun ch : Z * N => cov <? fst ch) hl)
                = existsb (fun ch : Z * N => (b <? fst ch) && (tk <? snd ch)%N) hl).
  { apply IH. intros ch Hin. apply Ht. right. exact Hin. }
  rewrite filter_cons. cbn [existsb fst snd]. destruct (decide _) as [D|D]; cbn [existsb fst snd].
  - rewrite IH'. reflexivity.
  - rewrite IH'. destruct ((b <? c) && (tk <? h)%N) eqn:E2; cbn; [|reflexivity].
    exfalso. apply Bool.andb_true_iff in E2 as [E2 E3]. apply Z.ltb_lt in E2. apply N.ltb_lt in E3.
    assert (Hc : ~ cov < c) by (intros X; apply D; apply Is_true_true_2; apply Z.ltb_lt; exact X).
    apply Bool.andb_false_iff in E as [E|E]; [apply Z.ltb_ge in E; lia| apply N.ltb_ge in E; lia].
Qed.

Lemma stale_hav_add_none cov t hl b :
  stale (hav_add cov t hl) b None = (b <? cov) || stale hl b None.
Proof.
  unfold hav_add, stale. cbn [existsb fst snd]. rewrite Bool.andb_true_r.
  destruct (b <? cov) eqn:E; cbn [orb]; [reflexivity|].
  induction hl as [|[c h] hl IH]; [reflexivity|].
  rewrite filter_cons. cbn [existsb fst snd]. destruct (decide _) as [D|D]; cbn [existsb fst snd]; rewrite ?Bool.andb_true_r.
  - rewrite IH. reflexivity.
  - rewrite IH. destruct (Z.ltb_spec b c); cbn; [|reflexivity]. exfalso.
    assert (Hc : ~ cov < c) by (intros X; apply D; apply Is_true_true_2; apply Z.ltb_lt; exact X).
    apply Z.ltb_ge in E. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma havoc_units_lookup x y t h u :
  let u0 := x / 16 in let u1 := (y - 1) / 16 in
  let lastcov := (if y mod 16 =? 0 then 16 else y mod 16) in
  (havoc_units x y t h) !! u =
    if (u0 <=? u) && (u <=? u1) then Some (hav_add (if u =? u1 then lastcov else 16) t (default [] (h !! u))) else h !! u.
Proof.
  cbn zeta. unfold havoc_units.
  set (u0 := x / 16). set (u1 := (y - 1) / 16). set (lastcov := if y mod 16 =? 0 then 16 else y mod 16).
  set (F := fun acc : Z * gmap Z (list (Z * N)) => let (u2, h0) := acc in (u2 + 1, <[u2 := hav_add (if u2 =? u1 then lastcov else 16) t (default [] (h0 !! u2))]> h0)).
  destruct (Z.lt_ge_cases (u1 - u0 + 1) 0) as [Hneg|Hnn].
  - (* [comment removed for export] *)
    destruct (u1 - u0 + 1) eqn:E; try lia. cbn.
    destruct (Z.leb_spec u0 u), (Z.leb_spec u u1); cbn; try reflexivity. lia.
  - assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (u0, h) in fst r = u0 + n /\
              forall v, snd r !! v = if (u0 <=? v) && (v <? u0 + n) then Some (hav_add (if v =? u1 then lastcov else 16) t (default [] (h !! v))) else h !! v).
    { intros n Hn. apply (Z_iter_ind F (fun n r => fst r = u0 + n /\ forall v, snd r !! v = if (u0 <=? v) && (v <? u0 + n) then Some (hav_add (if v =? u1 then lastcov else 16) t (default [] (h !! v))) else h !! v)); [| | exact Hn].
      - cbn. split; [lia|]. intros v. destruct (Z.leb_spec u0 v), (Z.ltb_spec v (u0 + 0)); cbn; try reflexivity. lia.
      - intros k [i tb] Hk [Hi IH]. cbn in Hi. subst i. unfold F. cbn [fst snd]. split; [lia|]. intros v.
        destruct (Z.eq_dec v (u0 + k)) as [->|NE].
        + rewrite lookup_insert_eq. destruct (Z.leb_spec u0 (u0 + k)), (Z.ltb_spec (u0 + k) (u0 + (k + 1))); cbn; try lia.
          f_equal. f_equal. rewrite IH. destruct (Z.leb_spec u0 (u0 + k)), (Z.ltb_spec (u0 + k) (u0 + k)); cbn; try lia. reflexivity.
        + rewrite lookup_insert_ne by congruence. rewrite IH.
          destruct (Z.leb_spec u0 v), (Z.ltb_spec v (u0 + k)), (Z.ltb_spec v (u0 + (k + 1))); cbn; try reflexivity; lia. }
    destruct (GEN (u1 - u0 + 1) Hnn) as [_ G]. rewrite G.
    destruct (Z.leb_spec u0 u), (Z.ltb_spec u (u0 + (u1 - u0 + 1))), (Z.leb_spec u u1); cbn; try reflexivity; lia.
Qed.

Lemma havoc_pages_lookup p0 p1 t h pg :
  (havoc_pages p0 p1 t h) !! pg = if (p0 <=? pg) && (pg <? p1) then Some t else h !! pg.
Proof.
  unfold havoc_pages.
  set (F := fun acc : Z * gmap Z N => let (pg0, h0) := acc in (pg0 + 1, <[pg0 := t]> h0)).
  destruct (Z.lt_ge_cases (p1 - p0) 0) as [Hneg|Hnn].
  - destruct (p1 - p0) eqn:E; try lia. cbn. destruct (Z.leb_spec p0 pg), (Z.ltb_spec pg p1); cbn; try reflexivity. lia.
  - assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (p0, h) in fst r = p0 + n /\
              forall v, snd r !! v = if (p0 <=? v) && (v <? p0 + n) then Some t else h !! v).
    { intros n Hn. apply (Z_iter_ind F (fun n r => fst r = p0 + n /\ forall v, snd r !! v = if (p0 <=? v) && (v <? p0 + n) then Some t else h !! v)); [| | exact Hn].
      - cbn. split; [lia|]. intros v. destruct (Z.leb_spec p0 v), (Z.ltb_spec v (p0 + 0)); cbn; try reflexivity. lia.
      - intros k [i tb] Hk [Hi IH]. cbn in Hi. subst i. unfold F. cbn [fst snd]. split; [lia|]. intros v.
        destruct (Z.eq_dec v (p0 + k)) as [->|NE].
        + rewrite lookup_insert_eq. destruct (Z.leb_spec p0 (p0 + k)), (Z.ltb_spec (p0 + k) (p0 + (k + 1))); cbn; try lia. reflexivity.
        + rewrite lookup_insert_ne by congruence. rewrite IH.
          destruct (Z.leb_spec p0 v), (Z.ltb_spec v (p0 + k)), (Z.ltb_spec v (p0 + (k + 1))); cbn; try reflexivity; lia. }
    destruct (GEN (p1 - p0) Hnn) as [_ G]. rewrite G.
    destruct (Z.leb_spec p0 pg), (Z.ltb_spec pg (p0 + (p1 - p0))), (Z.ltb_spec pg p1); cbn; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma div16_mono a b : a <= b -> a / 16 <= b / 16.
Proof. intros. apply Z.div_le_mono; lia. Qed.

Lemma havoc_units_in x y t h o tko :
  x mod 16 = 0 -> x <= o < y ->
  match tko with Some tk => (tk < t)%N | None => True end ->
  stale (default [] (havoc_units x y t h !! (o / 16))) (o mod 16) tko = true.
Proof.
  intros Hx Ho Htk. rewrite havoc_units_lookup.
  assert (U0 : x / 16 <= o / 16) by (apply div16_mono; lia).
  assert (U1 : o / 16 <= (y - 1) / 16) by (apply div16_mono; lia).
  destruct (Z.leb_spec (x / 16) (o / 16)), (Z.leb_spec (o / 16) ((y - 1) / 16)); try lia. cbn [andb default].
  cbn [default id]. unfold hav_add, stale. cbn [existsb fst snd].
  match goal with |- (?a && ?b) || _ = true => enough (E : a && b = true) by (rewrite E; reflexivity) end.
  apply Bool.andb_true_iff. split.
  - apply Z.ltb_lt. destruct (Z.eqb_spec (o / 16) ((y - 1) / 16)) as [E|NE].
    + destruct (Z.eqb_spec (y mod 16) 0) as [Ey|Ny].
      * pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
      * (* [comment removed for export] *)
        pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (y - 1) 16 ltac:(lia)).
        pose proof (Z.div_mod y 16 ltac:(lia)).
        pose proof (Z.mod_pos_bound o 16 ltac:(lia)). pose proof (Z.mod_pos_bound (y - 1) 16 ltac:(lia)). pose proof (Z.mod_pos_bound y 16 ltac:(lia)).
        assert (y / 16 = (y - 1) / 16 \/ y / 16 = (y - 1) / 16 + 1) by (pose proof (div16_mono (y - 1) y ltac:(lia)); pose proof (div16_mono y (y - 1 + 16) ltac:(lia)); rewrite <- Z.div_add in * by lia; nia).
        lia.
    + pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
  - destruct tko as [tk|]; [apply N.ltb_lt; exact Htk| reflexivity].
Qed.

Lemma havoc_units_out x y t h o tko :
  x mod 16 = 0 -> ~ (x <= o < y) ->
  match tko with Some tk => hl_ticks (default [] (h !! (o / 16))) t | None => True end ->
  stale (default [] (havoc_units x y t h !! (o / 16))) (o mod 16) tko = stale (default [] (h !! (o / 16))) (o mod 16) tko.
Proof.
  intros Hx Ho Htk. rewrite havoc_units_lookup.
  destruct (Z.leb_spec (x / 16) (o / 16)), (Z.leb_spec (o / 16) ((y - 1) / 16)); cbn [andb]; try reflexivity.
  cbn [default id].
  (* [comment removed for export] *)
  assert (Hoy : y <= o).
  { destruct (Z.lt_ge_cases o x); [|lia]. exfalso.
    pose proof (Z.div_mod x 16 ltac:(lia)). pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.mod_pos_bound o 16 ltac:(lia)). nia. }
  assert (E : o / 16 = (y - 1) / 16) by (pose proof (div16_mono (y - 1) o ltac:(lia)); lia).
  rewrite E, Z.eqb_refl.
  pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (y - 1) 16 ltac:(lia)). pose proof (Z.div_mod y 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound o 16 ltac:(lia)). pose proof (Z.mod_pos_bound (y - 1) 16 ltac:(lia)). pose proof (Z.mod_pos_bound y 16 ltac:(lia)).
  assert (Ny : y mod 16 <> 0 /\ y mod 16 <= o mod 16) by nia.
  destruct (Z.eqb_spec (y mod 16) 0) as [|_]; [lia|].
  destruct tko as [tk|].
  - rewrite stale_hav_add_some by (rewrite <- E; exact Htk). destruct (Z.ltb_spec (o mod 16) (y mod 16)); [lia|]. reflexivity.
  - rewrite stale_hav_add_none. destruct (Z.ltb_spec (o mod 16) (y mod 16)); [lia|]. reflexivity.
Qed.

Lemma hav_add_ticks cov t hl : hl_ticks hl t -> hl_ticks (hav_add cov t hl) t.
Proof.
  intros H ch Hin. unfold hav_add in Hin. destruct Hin as [<-|Hin]; [cbn; lia|].
  apply H. apply list_elem_of_In. apply list_elem_of_In in Hin. apply list_elem_of_filter in Hin. tauto.
Qed.

Lemma havoc_units_ticks x y t h :
  (forall u hl, h !! u = Some hl -> hl_ticks hl t) ->
  forall u hl, havoc_units x y t h !! u = Some hl -> hl_ticks hl t.
Proof.
  intros Hh u hl. rewrite havoc_units_lookup. destruct (_ && _).
  - intros E. inversion E. subst. apply hav_add_ticks. destruct (h !! u) as [hl0|] eqn:E0; cbn; [eapply Hh; exact E0| intros ? []].
  - apply Hh.
Qed.

Lemma havoc_units_default_ticks x y t h o :
  (forall u hl, h !! u = Some hl -> hl_ticks hl t) -> hl_ticks (default [] (havoc_units x y t h !! o)) t.
Proof.
  intros Hh. destruct (havoc_units x y t h !! o) as [hl|] eqn:E; cbn; [eapply havoc_units_ticks; eauto| intros ? []].
Qed.

Lemma default_ticks (h : gmap Z (list (Z * N))) t o :
  (forall u hl, h !! u = Some hl -> hl_ticks hl t) -> hl_ticks (default [] (h !! o)) t.
Proof. intros Hh. destruct (h !! o) as [hl|] eqn:E; cbn; [eapply Hh; eauto| intros ? []]. Qed.

Section HAVOC.
Variables (p : aptr) (n : Z) (st : mstate).
Hypothesis Al : snd p mod 16 = 0.
Hypothesis Hn : 0 < n.
Let sh := get_shadow st (fst p).
Hypothesis TK : forall u hl, r_hav sh !! u = Some hl -> hl_ticks hl (s_tick st).
Let a := snd p.
Let b := snd p + n.
Let t := s_tick st.
Let fp := (a + 4095) / 4096.
Let lp := b / 4096.

Lemma havoc_shadow :
  get_shadow (havoc p n st) (fst p) =
    mkShadow (r_cells sh)
      (if fp <? lp then
         (if lp * 4096 <? b then havoc_units (lp * 4096) b t (if a <? fp * 4096 then havoc_units a (fp * 4096) t (r_hav sh) else r_hav sh)
          else (if a <? fp * 4096 then havoc_units a (fp * 4096) t (r_hav sh) else r_hav sh))
       else havoc_units a b t (r_hav sh))
      (if fp <? lp then havoc_pages fp lp t (r_havp sh) else r_havp sh).
Proof.
  unfold havoc. destruct (Z.leb_spec n 0); [lia|]. rewrite get_shadow_upd_shadow, N.eqb_refl.
  subst sh a b t fp lp. destruct (_ <? _); [|reflexivity]. destruct (_ <? _); destruct (_ <? _); reflexivity.
Qed.

Lemma havoc_other_region rid : rid <> fst p -> get_shadow (havoc p n st) rid = get_shadow st rid.
Proof.
  intros NE. unfold havoc. destruct (n <=? 0); [reflexivity|]. rewrite get_shadow_upd_shadow.
  destruct (N.eqb_spec rid (fst p)); [congruence| reflexivity].
Qed.

Lemma fp_ge : a <= fp * 4096.
Proof. subst fp. pose proof (Z.div_mod (a + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (a + 4095) 4096 ltac:(lia)). lia. Qed.
Lemma lp_le : lp * 4096 <= b.
Proof. subst lp. pose proof (Z.div_mod b 4096 ltac:(lia)). pose proof (Z.mod_pos_bound b 4096 ltac:(lia)). lia. Qed.
Lemma fp_al : (fp * 4096) mod 16 = 0.
Proof. rewrite Z.mul_comm. replace 4096 with (16 * 256) by reflexivity. rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. Qed.
Lemma lp_al : (lp * 4096) mod 16 = 0.
Proof. rewrite Z.mul_comm. replace 4096 with (16 * 256) by reflexivity. rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
Lemma havoc_stale_out o tko :
  ~ (a <= o < b) ->
  match tko with Some tk => True | None => True end ->
  let sh' := get_shadow (havoc p n st) (fst p) in
  stale_pg (r_havp sh' !! (o / 4096)) tko || stale (default [] (r_hav sh' !! (o / 16))) (o mod 16) tko
  = stale_pg (r_havp sh !! (o / 4096)) tko || stale (default [] (r_hav sh !! (o / 16))) (o mod 16) tko.
Proof.
  intros Ho _. rewrite havoc_shadow. cbn [r_hav r_havp].
  pose proof fp_ge. pose proof lp_le.
  assert (TKo : forall hh : gmap Z (list (Z * N)), (forall u hl, hh !! u = Some hl -> hl_ticks hl t) ->
            match tko with Some _ => hl_ticks (default [] (hh !! (o / 16))) t | None => True end).
  { intros hh Hh. destruct tko; [apply default_ticks; exact Hh| exact I]. }
  destruct (Z.ltb_spec fp lp).
  - f_equal.
    + rewrite havoc_pages_lookup. destruct (Z.leb_spec fp (o / 4096)), (Z.ltb_spec (o / 4096) lp); cbn [andb]; try reflexivity.
      exfalso. apply Ho. pose proof (Z.div_mod o 4096 ltac:(lia)). pose proof (Z.mod_pos_bound o 4096 ltac:(lia)). nia.
    + destruct (Z.ltb_spec (lp * 4096) b); destruct (Z.ltb_spec a (fp * 4096)).
      * rewrite havoc_units_out; [| apply lp_al| lia| apply TKo; apply havoc_units_ticks; exact TK].
        rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
      * rewrite havoc_units_out; [reflexivity| apply lp_al| lia| apply TKo; exact TK].
      * rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
      * reflexivity.
  - f_equal. rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
Qed.

(* [comment removed for export] *)
Lemma havoc_stale_in o tko :
  a <= o < b ->
  match tko with Some tk => (tk < t)%N | None => True end ->
  let sh' := get_shadow (havoc p n st) (fst p) in
  stale_pg (r_havp sh' !! (o / 4096)) tko || stale (default [] (r_hav sh' !! (o / 16))) (o mod 16) tko = true.
Proof.
  intros Ho Htk. rewrite havoc_shadow. cbn [r_hav r_havp].
  pose proof fp_ge. pose proof lp_le.
  assert (TKo : forall hh : gmap Z (list (Z * N)), (forall u hl, hh !! u = Some hl -> hl_ticks hl t) ->
            match tko with Some _ => hl_ticks (default [] (hh !! (o / 16))) t | None => True end).
  { intros hh Hh. destruct tko; [apply default_ticks; exact Hh| exact I]. }
  apply Bool.orb_true_iff.
  destruct (Z.ltb_spec fp lp).
  - destruct (Z.lt_ge_cases o (fp * 4096)) as [Hhead|Hnh].
    + right. destruct (Z.ltb_spec a (fp * 4096)); [|lia].
      destruct (Z.ltb_spec (lp * 4096) b).
      * rewrite havoc_units_out; [| apply lp_al| nia| apply TKo; apply havoc_units_ticks; exact TK].
        apply havoc_units_in; [exact Al| lia| exact Htk].
      * apply havoc_units_in; [exact Al| lia| exact Htk].
    + destruct (Z.lt_ge_cases o (lp * 4096)) as [Hmid|Htail].
      * left. rewrite havoc_pages_lookup.
        assert (fp <= o / 4096 < lp).
        { split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia]. }
        destruct (Z.leb_spec fp (o / 4096)), (Z.ltb_spec (o / 4096) lp); try lia. cbn [andb].
        destruct tko as [tk|]; cbn; [apply N.ltb_lt; exact Htk| reflexivity].
      * right. destruct (Z.ltb_spec (lp * 4096) b); [|lia].
        apply havoc_units_in; [apply lp_al| lia| exact Htk].
  - right. apply havoc_units_in; [exact Al| lia| exact Htk].
Qed.

(* [comment removed for export] *)
Lemma cell_read_havoc_out q :
  ~ (fst q = fst p /\ a <= snd q < b) ->
  cell_read (get_shadow (havoc p n st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  intros Hq. destruct (N.eq_dec (fst q) (fst p)) as [E|NE].
  - rewrite E. assert (Ho : ~ (a <= snd q < b)) by tauto.
    unfold cell_read. pose proof (havoc_stale_out (snd q)) as SO. cbn zeta in SO.
    replace (r_cells (get_shadow (havoc p n st) (fst p))) with (r_cells sh) by (rewrite havoc_shadow; reflexivity).
    subst sh. destruct (r_cells (get_shadow st (fst p)) !! snd q) as [[v tk]|].
    + rewrite (SO (Some tk) Ho I). reflexivity.
    + rewrite (SO None Ho I). reflexivity.
  - rewrite havoc_other_region by exact NE. reflexivity.
Qed.

Lemma cell_read_havoc_in q :
  fst q = fst p -> a <= snd q < b ->
  (forall v tk, r_cells sh !! snd q = Some (v, tk) -> (tk < t)%N) ->
  exists h, cell_read (get_shadow (havoc p n st) (fst q)) (snd q) = Unknown h.
Proof.
  intros E Ho Htk. rewrite E. unfold cell_read.
  replace (r_cells (get_shadow (havoc p n st) (fst p))) with (r_cells sh) by (rewrite havoc_shadow; reflexivity).
  pose proof (havoc_stale_in (snd q)) as SI. cbn zeta in SI.
  destruct (r_cells sh !! snd q) as [[v tk]|] eqn:Ec.
  - rewrite (SI (Some tk) Ho (Htk v tk eq_refl)). eauto.
  - rewrite (SI None Ho I). eauto.
Qed.

Lemma havoc_cells rid : r_cells (get_shadow (havoc p n st) rid) = r_cells (get_shadow st rid).
Proof.
  destruct (N.eq_dec rid (fst p)) as [->|NE]; [rewrite havoc_shadow; reflexivity| rewrite havoc_other_region by exact NE; reflexivity].
Qed.

Lemma havoc_ticks rid :
  (forall u hl, r_hav (get_shadow st rid) !! u = Some hl -> hl_ticks hl t) ->
  (forall pg tk, r_havp (get_shadow st rid) !! pg = Some tk -> (tk <= t)%N) ->
  (forall u hl, r_hav (get_shadow (havoc p n st) rid) !! u = Some hl -> hl_ticks hl t)
  /\ (forall pg tk, r_havp (get_shadow (havoc p n st) rid) !! pg = Some tk -> (tk <= t)%N).
Proof.
  intros H1 H2. destruct (N.eq_dec rid (fst p)) as [->|NE]; [| rewrite havoc_other_region by exact NE; auto].
  rewrite havoc_shadow. cbn [r_hav r_havp]. split.
  - destruct (fp <? lp); [| apply havoc_units_ticks; exact TK].
    destruct (lp * 4096 <? b); destruct (a <? fp * 4096); repeat apply havoc_units_ticks; exact TK.
  - destruct (fp <? lp); [| exact H2]. intros pg tk. rewrite havoc_pages_lookup. destruct (_ && _); [| apply H2].
    intros X. inversion X. lia.
Qed.
End HAVOC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HDR.
Variables (bp : aptr) (st : mstate).
Hypothesis Al : snd bp mod 16 = 0.
Let sh := get_shadow st (fst bp).
Hypothesis TK : forall u hl, r_hav sh !! u = Some hl -> hl_ticks hl (s_tick st).

Lemma hdr_havoc_shadow :
  get_shadow (hdr_havoc bp st) (fst bp) =
  mkShadow (r_cells sh) (<[snd bp / 16 := hav_add 12 (s_tick st) (default [] (r_hav sh !! (snd bp / 16)))]> (r_hav sh)) (r_havp sh).
Proof. unfold hdr_havoc. rewrite get_shadow_upd_shadow, N.eqb_refl. reflexivity. Qed.

Lemma hdr_havoc_other_region rid : rid <> fst bp -> get_shadow (hdr_havoc bp st) rid = get_shadow st rid.
Proof. intros NE. unfold hdr_havoc. rewrite get_shadow_upd_shadow. destruct (N.eqb_spec rid (fst bp)); [congruence| reflexivity]. Qed.

Lemma cell_read_hdr_havoc_out q :
  ~ (fst q = fst bp /\ snd bp <= snd q < snd bp + 12) ->
  cell_read (get_shadow (hdr_havoc bp st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  intros Hq. destruct (N.eq_dec (fst q) (fst bp)) as [E|NE]; [| rewrite hdr_havoc_other_region by exact NE; reflexivity].
  rewrite E. rewrite hdr_havoc_shadow. unfold cell_read. cbn [r_cells r_hav r_havp]. subst sh.
  destruct (Z.eq_dec (snd q / 16) (snd bp / 16)) as [Eu|Nu].
  - rewrite Eu, lookup_insert_eq. cbn [default id].
    assert (Hb : 12 <= snd q mod 16).
    { pose proof (Z.div_mod (snd q) 16 ltac:(lia)). pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (snd q) 16 ltac:(lia)).
      assert (~ (snd bp <= snd q < snd bp + 12)) by tauto. nia. }
    destruct (r_cells (get_shadow st (fst bp)) !! snd q) as [[v tk]|].
    + rewrite stale_hav_add_some by (apply default_ticks; exact TK). destruct (Z.ltb_spec (snd q mod 16) 12); [lia|]. cbn [andb orb]. rewrite <- Eu. reflexivity.
    + rewrite stale_hav_add_none. destruct (Z.ltb_spec (snd q mod 16) 12); [lia|]. cbn [orb]. rewrite <- Eu. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma cell_read_hdr_havoc_in q :
  fst q = fst bp -> snd bp <= snd q < snd bp + 12 ->
  (forall v tk, r_cells sh !! snd q = Some (v, tk) -> (tk < s_tick st)%N) ->
  exists h, cell_read (get_shadow (hdr_havoc bp st) (fst q)) (snd q) = Unknown h.
Proof.
  intros E Ho Htk. rewrite E, hdr_havoc_shadow. unfold cell_read. cbn [r_cells r_hav r_havp]. subst sh.
  assert (Eu : snd q / 16 = snd bp / 16).
  { pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). symmetry. apply Z.div_unique with (r := snd q - snd bp); lia. }
  rewrite Eu, lookup_insert_eq. cbn [default id].
  assert (Hb : snd q mod 16 < 12).
  { pose proof (Z.div_mod (snd q) 16 ltac:(lia)). pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). nia. }
  destruct (r_cells (get_shadow st (fst bp)) !! snd q) as [[v tk]|] eqn:Ec.
  - unfold hav_add, stale. cbn [existsb fst snd].
    destruct (Z.ltb_spec (snd q mod 16) 12); [|lia]. rewrite (proj2 (N.ltb_lt _ _)) by (eapply Htk; reflexivity).
    cbn [andb orb]. rewrite Bool.orb_true_r. eauto.
  - rewrite stale_hav_add_none. destruct (Z.ltb_spec (snd q mod 16) 12); [|lia]. cbn [orb]. rewrite Bool.orb_true_r. eauto.
Qed.

Lemma hdr_havoc_cells rid : r_cells (get_shadow (hdr_havoc bp st) rid) = r_cells (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst bp)) as [->|NE]; [rewrite hdr_havoc_shadow; reflexivity| rewrite hdr_havoc_other_region by exact NE; reflexivity]. Qed.

Lemma hdr_havoc_ticks rid :
  (forall u hl, r_hav (get_shadow st rid) !! u = Some hl -> hl_ticks hl (s_tick st)) ->
  (forall u hl, r_hav (get_shadow (hdr_havoc bp st) rid) !! u = Some hl -> hl_ticks hl (s_tick st))
  /\ r_havp (get_shadow (hdr_havoc bp st) rid) = r_havp (get_shadow st rid).
Proof.
  intros H1. destruct (N.eq_dec rid (fst bp)) as [->|NE]; [| rewrite hdr_havoc_other_region by exact NE; auto].
  rewrite hdr_havoc_shadow. cbn [r_hav r_havp]. split; [| reflexivity].
  intros u hl. destruct (Z.eq_dec u (snd bp / 16)) as [->|Nu].
  - rewrite lookup_insert_eq. intros X. inversion X. subst. apply hav_add_ticks. apply default_ticks. exact TK.
  - rewrite lookup_insert_ne by congruence. apply H1.
Qed.
End HDR.
