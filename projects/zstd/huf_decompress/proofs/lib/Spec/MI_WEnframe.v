(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (12 recorded proofs replaced by written proofs (fold_off_le, s_shadow_havoc, TKS_havoc and 9 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Read MI_WFree2 MI_WGroup MI_Cnt MI_TF2.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_WEnframe () := "C35stdpp6option;from_optionC47Corelib4Init9Datatypes2IDC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indI35stdpp9countable9Countable00C35stdpp7tactics<f_equal_helpC35stdpp4base;RelDecisionC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appC35stdpp4base4fmapI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6LookupC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeK35stdpp8fin_maps6FinMap01I35stdpp4gmap8gmap_key00I35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC35stdpp8fin_maps@lookup_insert_eqC47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6MI_Cnt6zrangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00c59OSSVerify5KrLib4Spec;MI_WEnframe6fold_fC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00C59OSSVerify5KrLib4Spec6Malloc8fold_offC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6MI_Cnt>forallb_zrangeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic6eq_symC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib4Spec;MI_WEnframe8fold_allC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z6leb_gtI47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;havoc_unitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;havoc_pagesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC56Stdlib6NArith6BinNat1N3eqbC56Stdlib6NArith6BinNat1N8eqb_reflC59OSSVerify5KrLib4Spec6MI_KitEget_shadow_upd_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec9MI_WGroup3TKSC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C46Stdlib5Lists4List2InC56Stdlib6NArith6BinNat1N2leC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00I35stdpp4gmap8gmap_dep00C57Corelib7BinNums6PosDef3Pos7compareC47Corelib4Init9Datatypes7CompOppC35stdpp9countable6encodeC35stdpp4gmapBgmap_dep_ne_lookupC47Corelib4Init9Datatypes2idC47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib4Spec9MI_WGroup;sh_ticks_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit8sh_ticksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_Shadow8hl_ticksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_Shadow;havoc_ticksC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C35stdpp4base5emptyC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC35stdpp8fin_maps<lookup_emptyC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec9MI_Shadow;havoc_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01c59OSSVerify5KrLib4Spec;MI_WEnframe>s_shadow_havocC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec9MI_WGroup4DOMSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Ext7ctrl_eq00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext<ctrl_eq_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Ext7ctrl_eq01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib4Spec6Malloc4wr16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib4Spec6Malloc:enframe_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup3wrsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6Malloc4wr32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WEnframe7ef_listC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib4Spec;MI_WEnframe5lastwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit=aptr_eqb_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitBcell_read_wr8_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;MI_WEnframe9lastw_accC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitCcell_read_wr8_otherC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib4Spec9MI_WGroup7TKS_wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelI59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z6inj_leC59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup6TKS_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Read:known_byteC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z;land_nonnegK47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_ones".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fold_f (s : Z) : bool := forallb (fun off => negb (s <? off) || ((0 <=? fold_off off s) && (fold_off off s <=? s))) (zrange 0 256).
Lemma fold_all : forallb fold_f (zrange 0 256) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WEnframe ()) [] "p;2p;1p;3p-1R0p10000R1p4p710p8P0P1p4p7210p8P0p1000Kp5p710p8p1000gp4p70R0g001\R1p4p710p8P0p10026p4p710R2p8P0p1002Rp4p710R3p8P0p10030p4p7210p8P0p1003MR4p4p710R5p8P0P4p4p7210R4p8P0p1003fp4p710p8P0p1004Hp4p710p8P0p1004ep4p73110R0p8P3P5p8P3P4p8p10057R6p4p73101R7p1005QR8p4p73110p8P7p1005jR9p4p73110p8P7p1006Fp4p710p8P7p1006YR:p4p7201p8P7p1006kp4p7201p8P7p1007=R;p4p73110p8P7p1007QR<p4p73110p8P7p1007eR=p4p73110p8P7p1008?p4p7201p8P6p4p710R>P8p4p710p8P>P9p4p710p8P>P5p8P>P4p8P>P;p4p710p8P>P<p4p710p8P>P=p4p710p8p1008Rp4p7=1111111111100P2p8p1008lp4p710R2P3p8P2P5p8P2P4p8P2P0p8p1009DR2p4p710R=P3p8P=P5p8P=P4p8P=P0p8P2p4p741110R2P7p8P2p1009Xp4p73101p8p100:4p4p7<111111111110p100:Vp4p710R7p8p100;4p4p7<111111111110P7p8p100;Vp4p741110R7P6p4p7511100R0p8P0P7p8p100;op4p741110R7P6p4p76111100R0p8P0P7p8p100<Gp4p741110R7P6p4p771111100R0p8P0P7p8p100<gp4p741110R7P6p4p7:1111111100R6p8P6P7p8P:p4p7200R:P2p8P2P:p8P1j25Tg00=>j10Tg00=cj12Tg00>Aj21Tg00?8j34Tg00?Tj33Tg00?nR1g00@NR:'5g00@ng00ALg00BHg00Bf#0#0#0#0#0#0#0#0#2'134=31:do"). Qed.

Lemma fold_off_le off slack : 0 <= off < 256 -> 0 <= slack -> 0 <= fold_off off slack <= slack.
Proof.
  intros Ho Hs. destruct (Z.ltb_spec slack off) as [LT|GE].
  - pose proof (forallb_zrange fold_f 0 256 slack fold_all ltac:(lia) ltac:(lia)) as H. unfold fold_f in H.
    pose proof (forallb_zrange _ 0 256 off H ltac:(lia) ltac:(lia)) as H2. cbn beta in H2.
    replace (slack <? off) with true in H2 by (symmetry; apply Z.ltb_lt; exact LT). cbn in H2.
    apply andb_true_iff in H2 as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
  - unfold fold_off. replace (slack <? off) with false by (symmetry; apply Z.ltb_ge; exact GE). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma s_shadow_havoc p n st : 0 < n ->
  s_shadow (havoc p n st) = <[fst p := get_shadow (havoc p n st) (fst p)]> (s_shadow st).
Proof.
  intros Hn. unfold havoc at 1. replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia). unfold upd_shadow. cbn -[havoc get_shadow Z.add Z.mul Z.div Z.ltb].
  f_equal. unfold havoc. replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia). rewrite get_shadow_upd_shadow, N.eqb_refl. reflexivity.
Qed.

Lemma TKS_havoc p n st : snd p mod 16 = 0 -> 0 < n -> TKS st (s_tick st) -> TKS (havoc p n st) (s_tick st).
Proof.
  intros Al Hn TK rid sh. rewrite s_shadow_havoc by exact Hn.
  destruct (N.eq_dec rid (fst p)) as [->|NE]; [| rewrite lookup_insert_ne by congruence; apply TK].
  rewrite lookup_insert_eq. intros E. inversion E. subst sh. clear E.
  pose proof (sh_ticks_of st (fst p) TK) as [T1 T2].
  destruct (havoc_ticks p n st Hn ltac:(intros u hl Hu ch Hch; exact (T1 u hl ch Hu Hch)) (fst p)
              ltac:(intros u hl Hu ch Hch; exact (T1 u hl ch Hu Hch)) T2) as [A B].
  split; [| split; [intros u hl ch Hu Hch; exact (A u hl Hu ch Hch)| exact B]].
  rewrite havoc_cells by exact Hn. unfold get_shadow. destruct (s_shadow st !! fst p) as [sh0|] eqn:E0; cbn.
  - exact (proj1 (TK _ _ E0)).
  - intros o w t Ho. rewrite lookup_empty in Ho. discriminate.
Qed.

Lemma DOMS_havoc st0 p n st : 0 < n -> DOMS st0 st -> (exists r, s_regions st0 !! fst p = Some r /\ r_kind r = RKGroup) -> DOMS st0 (havoc p n st).
Proof.
  intros Hn D Hp rid sh. rewrite s_shadow_havoc by exact Hn.
  destruct (N.eq_dec rid (fst p)) as [->|NE]; [intros _; exact Hp|]. rewrite lookup_insert_ne by congruence. apply D.
Qed.

Lemma havoc_ctrl p n st : ctrl_eq st (havoc p n st) /\ s_tick (havoc p n st) = s_tick st.
Proof. unfold havoc. destruct (n <=? 0); [split; [apply ctrl_eq_refl| reflexivity]|]. split; [constructor; reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EF.
Variables (st : mstate) (g : aptr) (idx n off : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let gm := default (0%N, 0) (m_mem mr).
Let c : aptr := aadd gm (UNIT + stride * idx).
Let e : aptr := aadd c (stride - IB).
Let p0 : aptr := if off =? 0 then c else aadd c (UNIT * off).
Let res := snd e - snd p0 - n.
Let q := (snd p0 - (snd gm + UNIT)) / UNIT.

Definition ef_list : list (aptr * Z) :=
  (if negb (off =? 0) then [(aadd c (-2), off); (aadd (aadd c (-2)) 1, Z.shiftr off 8); (aadd c (-3), 224); (aadd p0 (-4), 0)] else [])
  ++ [(aadd p0 (-2), q); (aadd (aadd p0 (-2)) 1, Z.shiftr q 8); (aadd p0 (-3), idx)]
  ++ (if negb (res =? 0) then [(aadd e (- res), 0)] else [])
  ++ (if 5 <=? res then [(aadd e (-4), res); (aadd (aadd e (-4)) 1, Z.shiftr res 8); (aadd (aadd e (-4)) 2, Z.shiftr res 16); (aadd (aadd e (-4)) 3, Z.shiftr res 24); (aadd e (-5), 0)] else [])
  ++ [(aadd p0 (-3), Z.land idx 31 + Z.shiftl (if 5 <=? res then 5 else res) 5)].

Lemma enframe_at_eq : enframe_at st g idx n off = (wrs ef_list st, p0).
Proof.
  unfold enframe_at, set_size, ef_list. unfold q, res, p0, e, c, gm, stride, mr.
  destruct (off =? 0); cbn beta iota delta [wr16 wr32 wrs app negb];
    match goal with |- context [if negb (?x =? 0) then _ else _] => destruct (x =? 0) end; cbn beta iota delta [wrs app negb];
    match goal with |- context [if 5 <=? ?x then _ else _] => destruct (5 <=? x) end; cbn beta iota delta [wrs app negb]; reflexivity.
Qed.

Lemma p0_eq : p0 = aadd c (UNIT * off).
Proof. unfold p0. destruct (Z.eqb_spec off 0) as [->|]; [| reflexivity]. unfold c, aadd. cbn. f_equal. lia. Qed.
End EF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint lastw (l : list (aptr * Z)) (r : aptr) (acc : option Z) : option Z :=
  match l with
  | [] => acc
  | (a, v) :: l' => lastw l' r (if aptr_eqb a r then Some v else acc)
  end.

Lemma lastw_acc l r v : lastw l r (Some v) = match lastw l r None with Some w => Some w | None => Some v end.
Proof.
  revert v. induction l as [|[a w] l IH]; intros v; cbn; [reflexivity|].
  destruct (aptr_eqb a r); [| apply IH]. rewrite !(IH w). destruct (lastw l r None); reflexivity.
Qed.

Lemma wrs_lastw l : forall st r, TKS st (s_tick st) ->
  cell_read (get_shadow (wrs l st) (fst r)) (snd r) =
  match lastw l r None with Some w => Known (Z.land w 255) | None => cell_read (get_shadow st (fst r)) (snd r) end.
Proof.
  induction l as [|[a v] l IH]; intros st r TK; cbn [wrs lastw]; [reflexivity|].
  rewrite IH by (apply TKS_wr8; [cbn; lia| exact TK]).
  destruct (aptr_eqb_spec a r) as [<-|NE].
  - rewrite lastw_acc. destruct (lastw l a None); [reflexivity|]. apply cell_read_wr8_same. apply sh_ticks_of. exact TK.
  - destruct (lastw l r None); [reflexivity|]. apply cell_read_wr8_other. congruence.
Qed.

Lemma known_range X st L BL LS q v : INVL X st L BL LS -> cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256.
Proof.
  intros INV H. eapply known_byte; [| exact H]. intros sh o' v' t Hs Hc. exact (proj1 (proj1 (TKS_of _ _ _ _ _ INV _ _ Hs) o' v' t Hc)).
Qed.

Lemma havoc_0 p st : havoc p 0 st = st.
Proof. reflexivity. Qed.

Lemma land255_range a : 0 <= Z.land a 255 < 256.
Proof.
  split; [apply Z.land_nonneg; right; lia|].
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
