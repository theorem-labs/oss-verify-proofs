(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (29 recorded proofs replaced by written proofs (TKS_of, DOMS_of, TF_tick_new and 26 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_Bits MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree MI_WFree2.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_WGroup () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appC35stdpp4gmap;gmap_lookupC46Stdlib5Lists4List8map_consC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeK35stdpp8fin_maps6FinMap01I35stdpp4gmap4gmap00C35stdpp4base4fmapC35stdpp8fin_maps:map_eq_iffC59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldI47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib4Spec6MI_Inv9ish_ticksC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7ish_domC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup3TKSC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc8set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes3sndC56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic9False_indc59OSSVerify5KrLib4Spec9MI_WGroup2TFC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith4Znat3N2Z6inj_leC56Stdlib6ZArith4Znat3N2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C47Corelib4Init9Datatypes2idI47Corelib4Init5Logic2ex00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C35stdpp4base5emptyC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC35stdpp8fin_maps<lookup_emptyC59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C56Stdlib6NArith6BinNat1N3eqbC59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z4landc59OSSVerify5KrLib4Spec9MI_WGroupEget_shadow_cells_someC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec9MI_WFree2Awr8_shadow_lookupC1?~~~~~~~~~~~~~~~C35stdpp4base6insertK59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9hdr_havocC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc7hav_addC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C45stdpp;list_basics4list;list_filterC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib4Bool4Bool7Is_trueC35stdpp9decidable;Is_true_decC35stdpp4base6filterK47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses;rew_iff_revI35stdpp4base<list_elem_of00C35stdpp4base7elem_ofC35stdpp4base?list_elem_of_InC35stdpp4base8DecisionC45stdpp;list_basics4listClist_elem_of_filterC47Corelib4Init9Datatypes8prod_indC56Stdlib6NArith6BinNat1N7compareC57Corelib7BinNums6IntDef1Z3divI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03c59OSSVerify5KrLib4Spec9MI_WGroup4DOMSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree27wr8_domC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree27wr8_tksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit8sh_ticksC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup3wrsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Ext7ctrl_eq00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext<ctrl_eq_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext;ctrl_eq_wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext=ctrl_eq_transC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib4Spec6MI_KitCcell_read_wr8_otherC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup7TKS_wr8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup8DOMS_wr8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup6TF_wr8C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup8wrs_ctrlC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symc59OSSVerify5KrLib4Spec9MI_WGroup7wrs_TKSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup;sh_ticks_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitBcell_read_wr8_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup>wrs_read_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup7wrs_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9zero_hdrsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup5zlistC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega7EnvRing5PExpr01C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic3iffC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes?RelationClasses=iff_ReflexiveK46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib4Spec9MI_WGroup8in_zlistC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup7g_hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom;hosts_gbaseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4wr16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_sizeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib4Spec6Malloc4wr32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup=zero_hdrs_wrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c59OSSVerify5KrLib4Spec9MI_WGroup7nl_listC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup8bg_gbaseC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib4Spec9MI_WGroup4p_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7g_alignC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9stride_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Z_mod_multC59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z7mod_modC56Stdlib6ZArith6BinInt1Z7add_0_lC56Stdlib6ZArith6BinInt1Z7add_modC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsBsubrelation_properC46Stdlib5Lists4List:in_app_iffK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega:ZMicromega;ZArithProof03c59OSSVerify5KrLib4Spec9MI_WGroup5res16C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6eq_iffC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z7mul_0_rC56Stdlib6ZArith6BinInt1Z7mul_modC46Stdlib5Lists4List7map_appC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc59OSSVerify5KrLib4Spec9MI_WGroup7p_mod16C1?~~~~~~~~~~~~~~~C47Corelib7Classes>Morphisms_PropIiff_iff_iff_impl_morphismC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC59OSSVerify5KrLib4Spec8MI_Pres23inTC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idK46Stdlib9micromega=RingMicromega5Psatz01C59OSSVerify5KrLib4Spec7MI_Geom;sstart_succC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup7nl_in_TC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5knownC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup6TKS_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup7DOMS_ofC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_decC59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8ish_hdr0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup;zlist_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup=wrs_read_lastC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC59OSSVerify5KrLib4Spec6MI_Inv7is_partC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_mapC59OSSVerify5KrLib4Spec6MI_Inv9ig_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_R_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_A_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_M_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_L_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_G_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:inv_S_ctrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup:nl_regionsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup8wrs_DOMSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres2>inv_SH_write_TC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup6wrs_TFC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:land_assocK46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup;nl_residuesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9MI_WGroup5nl_eqC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition TF (st : mstate) : Prop :=
  forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> t = s_tick st -> 12 <= o mod 16.

(* [comment removed for export] *)
Definition TKS (st : mstate) (T : N) : Prop :=
  forall rid sh, s_shadow st !! rid = Some sh ->
      (forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= T)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= T)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= T)%N).
Definition DOMS (st0 st : mstate) : Prop :=
  forall rid sh, s_shadow st !! rid = Some sh -> exists r, s_regions st0 !! rid = Some r /\ r_kind r = RKGroup.

Lemma TKS_of X st L BL LS : INVL X st L BL LS -> TKS st (s_tick st).
Proof. intros INV. exact (ish_ticks _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))). Qed.
Lemma DOMS_of X st L BL LS : INVL X st L BL LS -> DOMS st st.
Proof. intros INV. exact (ish_dom _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))). Qed.

Lemma TF_tick_new st t : TKS st (s_tick st) -> (s_tick st < t)%N -> TF (set_tick t st).
Proof.
  intros TK LT rid sh o v t' Hsh Ho E. cbn in E, Hsh. subst t'. destruct (TK rid sh Hsh) as (C & _ & _). destruct (C o v t Ho) as [_ LE]. exfalso. lia.
Qed.

Lemma get_shadow_cells_some st rid o c : r_cells (get_shadow st rid) !! o = Some c -> exists sh, s_shadow st !! rid = Some sh /\ r_cells sh !! o = Some c.
Proof.
  unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn; [intros H; exists sh; auto|]. rewrite lookup_empty. discriminate.
Qed.

Lemma TF_wr8 st q v : TF st -> 12 <= snd q mod 16 -> TF (wr8 q v st).
Proof.
  intros H Hq rid sh o w t. rewrite (wr8_shadow_lookup st q v rid). destruct (N.eqb_spec rid (fst q)) as [->|NE]; [| apply H].
  intros E. inversion E. subst sh. cbn. destruct (Z.eq_dec o (snd q)) as [->|NEo].
  - rewrite lookup_insert_eq. intros _ _. exact Hq.
  - rewrite lookup_insert_ne by congruence. intros Ho Et. destruct (get_shadow_cells_some _ _ _ _ Ho) as (sh0 & Hs0 & Ho0). exact (H _ _ _ _ _ Hs0 Ho0 Et).
Qed.

Lemma TF_hdr_havoc st b : TF st -> TF (hdr_havoc b st).
Proof.
  intros H rid sh o w t. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst b)) as [->|NE].
  - rewrite lookup_insert_eq. intros E. inversion E. subst sh. cbn. intros Ho Et.
    destruct (get_shadow_cells_some _ _ _ _ Ho) as (sh0 & Hs0 & Ho0). exact (H _ _ _ _ _ Hs0 Ho0 Et).
  - rewrite lookup_insert_ne by congruence. apply H.
Qed.

Lemma TF_ctrl st st' : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> TF st -> TF st'.
Proof. intros E1 E2 H rid sh o v t. rewrite E1, E2. apply H. Qed.

Lemma TKS_hdr_havoc st b : TKS st (s_tick st) -> TKS (hdr_havoc b st) (s_tick st).
Proof.
  intros TK rid sh. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst b)) as [->|NE]; [| rewrite lookup_insert_ne by congruence; apply TK].
  rewrite lookup_insert_eq. intros E. inversion E. subst sh. cbn.
  assert (G : forall P : shadow -> Prop, (forall sh, s_shadow st !! fst b = Some sh -> P sh) -> P shadow0 -> P (get_shadow st (fst b))).
  { intros P H1 H0. unfold get_shadow. destruct (s_shadow st !! fst b) eqn:Es; [apply H1; reflexivity| exact H0]. }
  split; [| split].
  - apply (G (fun sh => forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= s_tick st)%N)); [intros sh Hsh; exact (proj1 (TK _ _ Hsh))| intros o w t Ho; cbn in Ho; rewrite lookup_empty in Ho; discriminate].
  - intros u hl ch. destruct (Z.eq_dec u (snd b / 16)) as [->|NEu].
    + rewrite lookup_insert_eq. intros E2. inversion E2. subst hl. unfold hav_add. cbn. intros [<-|Hin]; [cbn; lia|].
      apply (proj2 (list_elem_of_In _ _)) in Hin. apply list_elem_of_filter in Hin as [_ Hin]. apply (proj1 (list_elem_of_In _ _)) in Hin.
      revert Hin. apply (G (fun sh => In ch (default [] (r_hav sh !! (snd b / 16))) -> (snd ch <= s_tick st)%N)).
      * intros sh Hsh Hin. destruct (r_hav sh !! (snd b / 16)) as [hl0|] eqn:Eh; cbn in Hin; [| destruct Hin]. exact (proj1 (proj2 (TK _ _ Hsh)) _ hl0 ch Eh Hin).
      * cbn. rewrite lookup_empty. cbn. tauto.
    + rewrite lookup_insert_ne by congruence.
      apply (G (fun sh => r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)); [intros sh Hsh; exact (proj1 (proj2 (TK _ _ Hsh)) u hl ch)|].
      cbn. rewrite lookup_empty. discriminate.
  - apply (G (fun sh => forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N)); [intros sh Hsh; exact (proj2 (proj2 (TK _ _ Hsh)))|].
    intros pg t Hp. cbn in Hp. rewrite lookup_empty in Hp. discriminate.
Qed.

Lemma DOMS_wr8 st0 st q v : DOMS st0 st -> (exists r, s_regions st0 !! fst q = Some r /\ r_kind r = RKGroup) -> DOMS st0 (wr8 q v st).
Proof. intros D Hq. unfold DOMS. apply (wr8_dom st q v (fun rid => exists r, s_regions st0 !! rid = Some r /\ r_kind r = RKGroup) D Hq). Qed.
Lemma DOMS_hdr_havoc st0 st b : DOMS st0 st -> (exists r, s_regions st0 !! fst b = Some r /\ r_kind r = RKGroup) -> DOMS st0 (hdr_havoc b st).
Proof.
  intros D Hb rid sh. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst b)) as [->|NE]; [intros _; exact Hb|].
  rewrite lookup_insert_ne by congruence. apply D.
Qed.
Lemma TKS_wr8 st q v T : (s_tick st <= T)%N -> TKS st T -> TKS (wr8 q v st) T.
Proof. intros LE TK. exact (wr8_tks st q v T LE TK). Qed.

(* [comment removed for export] *)
Lemma sh_ticks_of st rid : TKS st (s_tick st) -> sh_ticks (get_shadow st rid) (s_tick st).
Proof.
  intros TK. unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn.
  - destruct (TK _ _ E) as (_ & A & B). split; [exact A| exact B].
  - split; [intros u hl ch H; rewrite lookup_empty in H; discriminate| intros pg t H; rewrite lookup_empty in H; discriminate].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint wrs (l : list (aptr * Z)) (st : mstate) : mstate :=
  match l with [] => st | (q, v) :: l' => wrs l' (wr8 q v st) end.

Lemma wrs_app l1 l2 st : wrs (l1 ++ l2) st = wrs l2 (wrs l1 st).
Proof. revert st. induction l1 as [|[q v] l1 IH]; intros st; cbn; [reflexivity| apply IH]. Qed.

Section WRS.

Lemma wrs_ctrl l st : ctrl_eq st (wrs l st) /\ s_tick (wrs l st) = s_tick st.
Proof.
  revert st. induction l as [|[q v] l IH]; intros st; cbn; [split; [apply ctrl_eq_refl| reflexivity]|].
  destruct (IH (wr8 q v st)) as [C T]. split; [eapply ctrl_eq_trans; [apply ctrl_eq_wr8| exact C]| rewrite T; reflexivity].
Qed.

Lemma wrs_read_other l st q : ~ In q (map fst l) ->
  cell_read (get_shadow (wrs l st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  revert st. induction l as [|[q' v] l IH]; intros st Hn; cbn; [reflexivity|].
  rewrite IH by (cbn in Hn; tauto). apply cell_read_wr8_other. cbn in Hn. intros ->. apply Hn. left. reflexivity.
Qed.

Lemma wrs_TKS l st T : (s_tick st <= T)%N -> TKS st T -> TKS (wrs l st) T.
Proof.
  revert st. induction l as [|[q v] l IH]; intros st LE TK; cbn; [exact TK|].
  apply IH; [cbn; exact LE|]. apply TKS_wr8; assumption.
Qed.

Lemma wrs_DOMS l st0 st : DOMS st0 st -> (forall q, In q (map fst l) -> exists r, s_regions st0 !! fst q = Some r /\ r_kind r = RKGroup) -> DOMS st0 (wrs l st).
Proof.
  revert st. induction l as [|[q v] l IH]; intros st D H; cbn; [exact D|].
  apply IH; [apply DOMS_wr8; [exact D| apply H; left; reflexivity]| intros q' Hq'; apply H; right; exact Hq'].
Qed.

Lemma wrs_TF l st : TF st -> (forall q, In q (map fst l) -> 12 <= snd q mod 16) -> TF (wrs l st).
Proof.
  revert st. induction l as [|[q v] l IH]; intros st H Hl; cbn; [exact H|].
  apply IH; [apply TF_wr8; [exact H| apply Hl; left; reflexivity]| intros q' Hq'; apply Hl; right; exact Hq'].
Qed.

(* [comment removed for export] *)
Lemma wrs_read_last l1 q v l2 st :
  ~ In q (map fst l2) -> TKS st (s_tick st) ->
  cell_read (get_shadow (wrs (l1 ++ (q, v) :: l2) st) (fst q)) (snd q) = Known (Z.land v 255).
Proof.
  intros Hn TK. rewrite wrs_app. cbn. rewrite wrs_read_other by exact Hn.
  destruct (wrs_ctrl l1 st) as [C T].
  apply cell_read_wr8_same. apply sh_ticks_of. rewrite T. apply wrs_TKS; [lia| exact TK].
Qed.
End WRS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint zlist (p : aptr) (size : Z) (i : Z) (n : nat) : list (aptr * Z) :=
  match n with O => [] | S n' => (aadd p (UNIT + i * size - 4), 0) :: zlist p size (i + 1) n' end.

Lemma zero_hdrs_wrs p size i n st : zero_hdrs p size i n st = wrs (zlist p size i n) st.
Proof. revert i st. induction n as [|n IH]; intros; cbn; [reflexivity| apply IH]. Qed.

Lemma in_zlist p size q : forall n i, In q (map fst (zlist p size i n)) <-> exists k, i <= k < i + Z.of_nat n /\ q = aadd p (UNIT + k * size - 4).
Proof.
  induction n as [|n IH]; intros i; cbn.
  - split; [tauto| intros (k & Hk & _); lia].
  - rewrite IH. split.
    + intros [<-|(k & Hk & ->)]; [exists i; split; [lia| reflexivity]| exists k; split; [lia| reflexivity]].
    + intros (k & Hk & ->). destruct (Z.eq_dec k i) as [->|NE]; [left; reflexivity| right; exists k; split; [lia| reflexivity]].
Qed.

Lemma zlist_split p size i n k : i <= k < i + Z.of_nat n ->
  exists l1 l2, zlist p size i n = l1 ++ (aadd p (UNIT + k * size - 4), 0) :: l2
    /\ (forall q, In q (map fst l2) -> exists k', k < k' < i + Z.of_nat n /\ q = aadd p (UNIT + k' * size - 4)).
Proof.
  revert i. induction n as [|n IH]; intros i Hk; [cbn in Hk; lia|].
  cbn. destruct (Z.eq_dec k i) as [->|NE].
  - exists [], (zlist p size (i + 1) n). split; [reflexivity|]. intros q Hq. apply in_zlist in Hq as (k' & Hk' & ->). exists k'. split; [lia| reflexivity].
  - destruct (IH (i + 1) ltac:(lia)) as (l1 & l2 & E & H). exists ((aadd p (UNIT + i * size - 4), 0) :: l1), l2.
    rewrite E. split; [reflexivity|]. intros q Hq. destruct (H q Hq) as (k' & Hk' & ->). exists k'. split; [lia| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section NL.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bg : aptr) (aig idx j size cnt : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! bg = Some (mkGhdr (Some g) aig).
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Let p : aptr := (fst bg, sstart (MR st g) idx).
Hypothesis HP : x_pend X = Some p.
Hypothesis STR : get_stride (MR st g) = UNIT * size_class j.
Hypothesis SZ16 : size mod 16 = 0.
Hypothesis SZ0 : 16 <= size.
Hypothesis CNT : 1 <= cnt.
Hypothesis FIT : UNIT + cnt * size <= get_stride (MR st g).
Hypothesis HTF : TF st.
Let q : Z := (snd p - (snd bg + UNIT)) / UNIT.
Let st' := nest_layout st g idx j size cnt.

(* [comment removed for export] *)
Definition nl_list : list (aptr * Z) :=
  [(aadd p (-2), q); (aadd (aadd p (-2)) 1, Z.shiftr q 8); (aadd p (-3), idx); (aadd p (-3), Z.land idx 31 + Z.shiftl 0 5);
   (aadd p (-3), Z.lor (Z.land idx 31) 192)] ++ zlist p size 0 (Z.to_nat (cnt + 1)).

Lemma g_hosts : hosts st bg g.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WGroup ()) ["NL"] "h02aip;1p;4p;6p;2p;3g00RLj1:Tg02Bjj49Tg02CHj62Tg00>Sj41Tg007\j48Tg02Cij14Tg00T`j63Tg00U4j20Tg02Dbj25Tg00UVj36Tg016lj47Tg00j_R0g02EYR1#:g003XR2P1P2g00l4R3g010hR4P0g00k=R5C9R6P3P4g011AP0P5g00kVE2R5P1C1P2P6P5P1C8p,2bgp,2st#4E3p,1g,02f0'5,0136X00p,3aigp,2HgC7o"). Qed.
Lemma p_eq : slot_start' (MR st g) idx = p.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WGroup ()) ["NL"] "p;3p;2p;1p;8g00Gnj3=Tg00G6j2<Tg00Ecj33Tg00D2j32Tg00Djj2;Tg00F[j20Tg00Hfj15Tg00I^j34Tg00JVj31Tg01Ggj36Tg02FPj87Tg02GPj28Tg02HCj29Tg00UVj3:Tp,1XR0p,2stR1p,2LSR2A=012R31<12A3012p,2BLR292011;12'0'0'0R2%51R41032R2p,1L94011042p,3INV313136p,1gR2p,2bgp,3idxR4g02I?G7g003X1812/94p,1p3:eo"). Qed.
Lemma bg_gbase : gbase (MR st g) = bg.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WGroup ()) ["NL"] "p;3p;2p;1p;7g00Gnj3:Tg00G6j29Tg00Ecj33Tg00D2j32Tg00Djj28Tg00F[j20Tg00Hfj15Tg00I^j34Tg00JVj31Tg01Ggj36Tg02J:j77Tp,1XR0p,2stR1p,2LSR2A:012R31912A3012p,2BLR292011812'0'0'0R2%51R41032R2p,1L94011042p,3INV313136p,2bgp,1gg02I?F7o"). Qed.

Lemma nl_eq : st' = wrs nl_list st.
Proof.
  unfold st', nest_layout, enframe_at. fold (MR st g). cbn [negb Z.eqb].
  change (aadd (default (0%N, 0) (m_mem (MR st g))) (UNIT + get_stride (MR st g) * idx)) with (slot_start' (MR st g) idx).
  rewrite p_eq. unfold set_size.
  replace (snd (aadd p (get_stride (MR st g) - IB)) - snd p - (UNIT * size_class j - IB)) with 0
    by (unfold aadd; cbn [fst snd]; rewrite STR; unfold UNIT, IB; lia).
  change (5 <=? 0) with false. change (0 =? 0) with true. cbn [negb].
  unfold nl_list. rewrite wrs_app. cbn [wrs app]. rewrite zero_hdrs_wrs. unfold wr16.
  unfold q. fold (gbase (MR st g)). rewrite bg_gbase. reflexivity.
Qed.

Lemma p_mod16 : snd p mod 16 = 0.
Proof.
  unfold p. cbn. unfold sstart. rewrite bg_gbase.
  pose proof (g_align _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hg)) as [_ A].
  pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ g_hosts) as [_ SM].
  pose proof (Z.div_mod (snd bg) 16 ltac:(lia)) as D1. pose proof (Z.div_mod (get_stride (MR st g)) 16 ltac:(lia)) as D2.
  unfold UNIT in *. rewrite A in D1. rewrite SM in D2.
  replace (snd bg + 16 + get_stride (MR st g) * idx) with ((snd bg / 16 + 1 + get_stride (MR st g) / 16 * idx) * 16) by nia.
  apply Z_mod_mult.
Qed.

Lemma res16 a d : a mod 16 = 0 -> (a + d) mod 16 = d mod 16.
Proof. intros H. rewrite Z.add_mod, H, Z.add_0_l, Z.mod_mod by lia. reflexivity. Qed.

Lemma nl_residues r : In r (map fst nl_list) -> 12 <= snd r mod 16.
Proof.
  pose proof p_mod16 as PM. clearbody p. unfold nl_list. rewrite map_app, in_app_iff. unfold aadd. cbn [map fst snd In]. intros [H|H].
  - destruct H as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [snd]; rewrite <- ?Z.add_assoc, (res16 _ _ PM); cbn; lia.
  - apply in_zlist in H as (k & Hk & ->). cbn [snd]. rewrite (res16 _ _ PM). unfold UNIT.
    replace (16 + k * size - 4) with (k * size + 12) by lia. rewrite res16; [cbn; lia|].
    rewrite Z.mul_mod, SZ16, Z.mul_0_r by lia. reflexivity.
Qed.

Lemma nl_in_T r : In r (map fst nl_list) ->
  inT (fst bg) (sstart (MR st g) idx - 3) (sstart (MR st g) (idx + 1) - 4) r \/ r = (fst bg, sstart (MR st g) (idx + 1) - 4).
Proof.
  unfold nl_list. rewrite map_app, in_app_iff. rewrite sstart_succ. unfold inT, p, aadd. cbn [map fst snd In]. intros [H|H].
  - left. pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ g_hosts) as [SG _].
    destruct H as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold UNIT in *; lia.
  - apply in_zlist in H as (k & Hk & ->). cbn [fst snd]. unfold UNIT in *. rewrite Z2Nat.id in Hk by lia.
    destruct (Z.eq_dec (16 + k * size) (get_stride (MR st g))) as [E|NE].
    + right. unfold aadd. cbn [fst snd]. f_equal. lia.
    + left. unfold aadd. cbn [fst snd]. split; [reflexivity|]. assert (k * size <= cnt * size) by nia. lia.
Qed.
Lemma nl_regions r : In r (map fst nl_list) -> fst r = fst bg.
Proof. intros H. destruct (nl_in_T r H) as [[E _]| ->]; [exact E| reflexivity]. Qed.

Theorem nest_layout_ok :
  INVL X st' L BL LS /\ TF st' /\ ctrl_eq st st' /\ s_tick st' = s_tick st
  /\ known st' (aadd p (-3)) (Z.land (Z.lor (Z.land idx 31) 192) 255)
  /\ known st' (aadd p (-2)) (Z.land q 255) /\ known st' (aadd (aadd p (-2)) 1) (Z.land (Z.shiftr q 8) 255)
  /\ (forall k, 0 <= k <= cnt -> known st' (aadd p (UNIT + k * size - 4)) 0)
  /\ (forall r, ~ inT (fst bg) (sstart (MR st g) idx - 3) (sstart (MR st g) (idx + 1) - 4) r ->
        cell_read (get_shadow st' (fst r)) (snd r) = cell_read (get_shadow st (fst r)) (snd r)).
Proof.
  rewrite nl_eq. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (wrs_ctrl nl_list st) as [CE TK].
  pose proof (TKS_of _ _ _ _ _ INV) as TK0. pose proof (DOMS_of _ _ _ _ _ INV) as DM0.
  assert (RD : forall r, ~ inT (fst bg) (sstart (MR st g) idx - 3) (sstart (MR st g) (idx + 1) - 4) r ->
        cell_read (get_shadow (wrs nl_list st) (fst r)) (snd r) = cell_read (get_shadow st (fst r)) (snd r)).
  { intros r Hr. destruct (in_dec aptr_eq_dec r (map fst nl_list)) as [Hin|Hn]; [| apply wrs_read_other; exact Hn].
    destruct (nl_in_T r Hin) as [HT| ->]; [exfalso; exact (Hr HT)|].
    (* [comment removed for export] *)
    pose proof (ish_hdr0 _ _ ISH bg g (idx + 1) g_hosts ltac:(unfold cnt_of; lia)) as K0. unfold known, SHd, IB in K0. cbn [fst snd] in K0 |- *. rewrite K0.
    assert (E : (fst bg, sstart (MR st g) (idx + 1) - 4) = aadd p (UNIT + cnt * size - 4) /\ UNIT + cnt * size = get_stride (MR st g)).
    { unfold nl_list in Hin. rewrite map_app in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      - exfalso. cbn [map fst In] in Hin. pose proof (stride_ge _ _ _ IG _ _ g_hosts) as [SG _].
        destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; apply (f_equal snd) in E; unfold p, aadd in E; cbn [fst snd] in E; rewrite sstart_succ in E; unfold UNIT in *; lia.
      - apply in_zlist in Hin as (k & Hk & Ek). rewrite Z2Nat.id in Hk by lia. apply (f_equal snd) in Ek. unfold p, aadd in Ek. cbn [fst snd] in Ek.
        rewrite sstart_succ in Ek. destruct (Z.eq_dec k cnt) as [->|NEk].
        + split; [unfold p, aadd; cbn [fst snd]; rewrite sstart_succ; f_equal; unfold UNIT in *; lia| unfold UNIT in *; lia].
        + exfalso. assert (k * size <= (cnt - 1) * size) by nia. unfold UNIT in *. lia. }
    destruct E as [E1 E2]. apply (f_equal snd) in E1. cbn [snd] in E1. rewrite E1.
    destruct (zlist_split p size 0 (Z.to_nat (cnt + 1)) cnt ltac:(rewrite Z2Nat.id by lia; lia)) as (l1 & l2 & EZ & Hl2).
    change (cell_read (get_shadow (wrs nl_list st) (fst (aadd p (UNIT + cnt * size - 4)))) (snd (aadd p (UNIT + cnt * size - 4))) = Known (Z.land 0 255)).
    unfold nl_list. rewrite EZ.
    rewrite (app_assoc _ l1) || rewrite app_assoc.
    apply wrs_read_last; [| exact TK0].
    intros Hin2. destruct (Hl2 _ Hin2) as (k' & Hk' & _). rewrite Z2Nat.id in Hk' by lia. lia. }
  pose proof (is_part _ _ _ IS _ _ _ idx Hg Hidx) as P5. cbn zeta in P5. rewrite p_eq, HP in P5. unfold one5 in P5.
  assert (NH : s_groups st !! p = None).
  { destruct (s_groups st !! p) eqn:E; [| reflexivity]. exfalso. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity]. }
  assert (NB : forall k, In k BL -> bslot k <> p).
  { intros k Hk E. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). apply nCE. split; [| reflexivity]. rewrite <- E. apply in_map. exact Hk. }
  assert (REG : exists r, s_regions st !! fst bg = Some r /\ r_kind r = RKGroup) by exact (ig_region _ _ _ IG _ _ Hg).
  split; [| split; [| split; [exact CE| split; [exact TK|]]]].
  - split; [apply (inv_R_ctrl X st _ L CE); exact IR|]. split; [apply (inv_A_ctrl st _ CE); exact IA|].
    split; [apply (inv_M_ctrl X st _ LS CE); exact IM|]. split; [apply (inv_L_ctrl st _ LS CE); exact IL|].
    split; [apply (inv_G_ctrl X st _ LS CE); exact IG|]. split; [apply (inv_S_ctrl X st _ BL CE); exact IS|].
    apply (inv_SH_write_T X st (wrs nl_list st) BL LS IM IG IS ISH g bg idx g_hosts Hidx NH NB CE TK RD).
    + apply wrs_DOMS; [exact DM0|]. intros r Hr. rewrite (nl_regions r Hr). exact REG.
    + apply wrs_TKS; [lia| exact TK0].
  - apply wrs_TF; [exact HTF| apply nl_residues].
  - (* [comment removed for export] *)
    assert (KN : forall l1 r v l2, nl_list = l1 ++ (r, v) :: l2 -> ~ In r (map fst l2) -> known (wrs nl_list st) r (Z.land v 255)).
    { intros l1 r v l2 E Hn. unfold known, SHd. rewrite E. apply wrs_read_last; [exact Hn| exact TK0]. }
    pose proof (stride_ge _ _ _ IG _ _ g_hosts) as [SG _].
    assert (ZL : forall r, In r (map fst (zlist p size 0 (Z.to_nat (cnt + 1)))) -> snd p + 12 <= snd r).
    { intros r Hr. apply in_zlist in Hr as (k & Hk & ->). cbn. unfold UNIT. nia. }
    split; [| split; [| split; [| split; [| exact RD]]]].
    + apply (KN [(aadd p (-2), q); (aadd (aadd p (-2)) 1, Z.shiftr q 8); (aadd p (-3), idx); (aadd p (-3), Z.land idx 31 + Z.shiftl 0 5)] (aadd p (-3)) _ (zlist p size 0 (Z.to_nat (cnt + 1))) eq_refl).
      intros Hin. pose proof (ZL _ Hin) as Z1. cbn in Z1. lia.
    + rewrite <- (Z.land_assoc q 255 255 : Z.land (Z.land q 255) 255 = Z.land q (Z.land 255 255)) || idtac.
      replace (Z.land q 255) with (Z.land (Z.land q 255) 255) by (rewrite <- Z.land_assoc; reflexivity).
      replace (Z.land (Z.land q 255) 255) with (Z.land q 255) by (rewrite <- Z.land_assoc; reflexivity).
      apply (KN [] (aadd p (-2)) q _ eq_refl).
      cbn [map fst app]. intros [E|[E|[E|[E|Hin]]]]; try (unfold aadd in E; cbn in E; apply (f_equal snd) in E; cbn in E; lia). pose proof (ZL _ Hin) as Z1. cbn in Z1. lia.
    + apply (KN [(aadd p (-2), q)] (aadd (aadd p (-2)) 1) (Z.shiftr q 8) _ eq_refl).
      cbn [map fst app]. intros [E|[E|[E|Hin]]]; try (unfold aadd in E; cbn in E; apply (f_equal snd) in E; cbn in E; lia). pose proof (ZL _ Hin) as Z1. cbn in Z1. lia.
    + intros k Hk. destruct (zlist_split p size 0 (Z.to_nat (cnt + 1)) k ltac:(rewrite Z2Nat.id by lia; lia)) as (l1 & l2 & E & Hl2).
      change (known (wrs nl_list st) (aadd p (UNIT + k * size - 4)) (Z.land 0 255)).
      apply (KN ([(aadd p (-2), q); (aadd (aadd p (-2)) 1, Z.shiftr q 8); (aadd p (-3), idx); (aadd p (-3), Z.land idx 31 + Z.shiftl 0 5); (aadd p (-3), Z.lor (Z.land idx 31) 192)] ++ l1) _ 0 l2).
      * unfold nl_list. rewrite E. rewrite <- app_assoc. reflexivity.
      * intros Hin. destruct (Hl2 _ Hin) as (k' & Hk' & E'). unfold aadd in E'. apply (f_equal snd) in E'. cbn in E'. unfold UNIT in E'. nia.
Qed.
End NL.
