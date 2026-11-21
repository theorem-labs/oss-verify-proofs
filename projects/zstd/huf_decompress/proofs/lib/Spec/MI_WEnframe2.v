(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (24 recorded proofs replaced by written proofs (havoc_le0, ef_c, ef_stride and 21 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Read MI_WFree2 MI_WGroup MI_Cnt MI_TF2 MI_WEnframe.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_WEnframe2 () := "C47Corelib7Program6Basics4flipC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsCeq_rewrite_relationC59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsKrespectful_per_obligation_1C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3appC35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec6Malloc3rd8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4rd16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<enframe_fullC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionI35stdpp4gmap4gmap00C35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z8leb_specC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes8BoolSpec00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes3sndK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;havoc_unitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;havoc_pagesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_shadowC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib4Spec6Malloc5havocC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom;hosts_gbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib4Spec<MI_WEnframe28ef_gbaseC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6MI_Inv8is_totalC1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countablec59OSSVerify5KrLib4Spec<MI_WEnframe27ef_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9stride_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec7MI_Tree5ftreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Read9rd8_ftreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Read:rd16_ftreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF2:sstart_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega5Psatz06I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6MI_Inv7is_partC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notI47Corelib4Init5Logic2or00C47Corelib4Init5Logic9False_indI59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C46Stdlib5Lists4List6in_mapC59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8g_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_scC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_liC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4ZdivBZ_div_exact_full_2C56Stdlib6ZArith6BinInt1Z9mul_assocC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz07C56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z7mul_0_rC56Stdlib6ZArith6BinInt1Z7div_mulc59OSSVerify5KrLib4Spec<MI_WEnframe29ef_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6shiftlc59OSSVerify5KrLib4Spec<MI_WEnframe22ppC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe22qvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe24resvC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec;MI_WEnframe5p0_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WEnframe7ef_listC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe22ELC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbc59OSSVerify5KrLib4Spec<MI_WEnframe22eeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe24ef_cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup3wrsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe25EL_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:enframe_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WEnframe=enframe_at_eqC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib4Spec9MI_WGroup6TKS_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup7wrs_TKSC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat3N2Z6inj_leI59OSSVerify5KrLib4Spec6MI_Ext7ctrl_eq00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup8wrs_ctrlC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z7add_modc59OSSVerify5KrLib4Spec<MI_WEnframe26ef_c16C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe23stwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe27stw_TKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup3TKSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe28stw_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup;sh_ticks_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_Shadow8hl_ticksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WEnframe:havoc_ctrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe23stfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe28stw_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext=ctrl_eq_transC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe29havoc_le0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe24pp16C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe27stw_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_ShadowCcell_read_havoc_outC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00K46Stdlib9micromega7EnvRing5PExpr06K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec;MI_WEnframe5lastwC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WEnframe9wrs_lastwC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indc59OSSVerify5KrLib4Spec<MI_WEnframe2<stf_read_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5knownC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe28EL_addrsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe29EL_not_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF2?wrs_cells_otherC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib4Spec7MI_Geom;sstart_succC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF2@TF2_interior_oldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_ShadowBcell_read_havoc_inC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec6MI_Inv7unknownC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe25ef_NHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres2=blk_shadow_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe28stf_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext8ce_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext6MR_extC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe26res_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe2:ef_q_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7byte_ofC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC56Stdlib6ZArith6BinInt1Z:eqb_compatC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit<aptr_eqb_neqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8ish_hdr0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe2=stf_known_oldC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib4Spec<MI_WEnframe2;stf_known_wC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z5min_rC56Stdlib6ZArith6BinInt1Z5min_lC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z:shiftr_0_rC56Stdlib6ZArith6BinInt1Z7mul_1_rC56Stdlib6ZArith6BinInt1Z6leb_leK46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula01c59OSSVerify5KrLib4Spec<MI_WEnframe2;stf_unknownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4Spec6MI_Kit;aptr_eqb_eqC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega5Tauto4kind02I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres23inTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup>wrs_read_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9ig_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup4DOMSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup7DOMS_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup8wrs_DOMSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WEnframe:DOMS_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WEnframe9TKS_havocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe26blk_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres2>INVL_add_blockC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe28ef_slotsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WEnframe;known_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WEnframe;fold_off_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8fold_offC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z3lorc59OSSVerify5KrLib4Spec<MI_WEnframe27ef_INVLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<MI_WEnframe2=enframe_at_ELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;MI_WEnframe=land255_rangeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma havoc_le0 p n st : n <= 0 -> havoc p n st = st.
Proof. intros H. unfold havoc. destruct (Z.leb_spec n 0); [reflexivity| lia]. Qed.

Section ENFRAME.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bg : aptr) (idx n : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Let c : aptr := (fst bg, sstart (MR st g) idx).
Hypothesis HP : x_pend X = Some c.
Hypothesis Hn : 0 <= n.
Hypothesis Hfit : n + IB <= get_stride (MR st g).
Hypothesis TF : TF2 st.
Hypothesis Hres : get_stride (MR st g) - IB - n < 2 ^ 32.
Let X' := xpend X None.
Let stride := get_stride (MR st g).
Let slack := (stride - IB - n) / UNIT.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma ef_gbase : gbase (MR st g) = bg.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WEnframe2 ()) ["ENFRAME"] "p;7p100d6p4p70R0p1001Cp4p710p8P0p1001Zp4p710p8P0p100=Rp4p710p8g00djj70Tp,1Xp,2stp,2LSp,2IMp,2bgp,1gp,2HgF0o"). Qed.
Lemma ef_c : aadd (default (0%N, 0) (m_mem (get_meta_rec st g))) (UNIT + get_stride (get_meta_rec st g) * idx) = c.
Proof. fold (MR st g). change (default (0%N, 0) (m_mem (MR st g))) with (gbase (MR st g)). rewrite ef_gbase. unfold c, sstart, aadd. rewrite ef_gbase. f_equal. lia. Qed.
Lemma ef_slot : slot_start' (MR st g) idx = c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WEnframe2 ()) ["ENFRAME"] "p;8g014kj80Tp,1Xp,2stp,2LSp,2IMp,1gp,2bgp,3idxp,2HgG0o"). Qed.
Lemma ef_slots : s_slots st !! c = Some (g, idx).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WEnframe2 ()) ["ENFRAME"] "h01cp;2p;1p;4p;6p;3p;9g00egj2>Tg015kj2=Tg00Cej20Tg016gj11Tg017Ij4<Tg017gj62Tg00?oj43Tg00:Sj44Tg018Hj15Tg019@j66Tg00LUj47Tg019Tj28Tg00Oaj39Tg01:6l9;Tg003Ej6:Tg000NR0p,2stR1p,1gR2'>p,3idxR3'=g00\TR4,00R5#1P0P5P0g00^iR6g01:oR7P4g00`@R8C<R9P6P7g01;HP4P8g00`YE2R8P5C3P0P9P8P5C4f0%51E6P0P4P2P3C7,8539X00p,1XP1p,2BLp,2ISp,2bgP2P3p,2Hgp,4HidxM9;p,1cg01;fE:o"). Qed.
Lemma ef_stride : 16 <= stride /\ stride mod 16 = 0.
Proof. pose proof (stride_ge _ _ _ IG _ _ Hg) as [A B]. unfold UNIT in *. split; assumption. Qed.
Lemma ef_c16 : snd c mod 16 = 0.
Proof.
  pose proof (sstart_res X st L BL LS INV bg g idx Hg) as R. unfold c. cbn [snd]. unfold IB in R.
  pose proof (Z.div_mod (sstart (MR st g) idx - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st g) idx) 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound (sstart (MR st g) idx) 16 ltac:(lia)). lia.
Qed.
Lemma ef_NH : s_groups st !! c = None.
Proof.
  destruct Hg as [ai Hb]. pose proof (is_part _ _ _ IS _ _ _ idx Hb Hidx) as P5. cbn zeta in P5. rewrite ef_slot, HP in P5.
  destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity].
Qed.
Lemma ef_NB k : In k BL -> bslot k <> c.
Proof.
  destruct Hg as [ai Hb]. pose proof (is_part _ _ _ IS _ _ _ idx Hb Hidx) as P5. cbn zeta in P5. rewrite ef_slot, HP in P5.
  intros Hk E. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). apply nCE. split; [| reflexivity]. rewrite <- E. apply in_map. exact Hk.
Qed.
Lemma ef_q_range off : 0 <= off <= 255 -> UNIT * off + n <= stride - IB -> 0 <= (snd c + UNIT * off - (snd bg + UNIT)) / UNIT < 2 ^ 16.
Proof.
  intros Ho Hf. destruct Hg as [ai Hb]. pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO.
  pose proof (g_stride _ _ _ _ _ _ GO) as GS. pose proof (g_sc _ _ _ _ _ _ GO) as SC. pose proof (g_li _ _ _ _ _ _ GO) as LI.
  unfold c. cbn [snd]. unfold sstart. rewrite ef_gbase. fold stride. pose proof ef_stride as [S16 SM].
  replace (snd bg + UNIT + stride * idx + UNIT * off - (snd bg + UNIT)) with ((stride / 16 * idx + off) * 16)
    by (unfold UNIT; pose proof (Z.div_mod stride 16 ltac:(lia)); nia).
  unfold UNIT. rewrite Z.div_mul by lia.
  assert (0 <= stride / 16 * idx) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
  split; [lia|].
  destruct SC as [[SC1 _]|(SC63 & L0 & _)].
  - destruct (GS ltac:(lia)) as (_ & _ & LT). unfold cnt_of in LT. fold stride in LT.
    assert (stride * idx <= stride * (m_last_idx (MR st g))) by (apply Z.mul_le_mono_nonneg_l; lia).
    pose proof (Z.div_mod stride 16 ltac:(lia)). unfold IB, UNIT in Hf. nia.
  - rewrite L0 in Hidx. assert (idx = 0) by lia. subst idx. rewrite Z.mul_0_r. lia.
Qed.

(* [comment removed for export] *)
Definition pp (off : Z) : aptr := aadd c (UNIT * off).
Definition ee : aptr := aadd c (stride - IB).
Definition resv (off : Z) : Z := snd ee - snd (pp off) - n.
Definition qv (off : Z) : Z := (snd (pp off) - (snd bg + UNIT)) / UNIT.
Definition EL (off : Z) : list (aptr * Z) :=
  (if negb (off =? 0) then [(aadd c (-2), off); (aadd (aadd c (-2)) 1, Z.shiftr off 8); (aadd c (-3), 224); (aadd (pp off) (-4), 0)] else [])
  ++ [(aadd (pp off) (-2), qv off); (aadd (aadd (pp off) (-2)) 1, Z.shiftr (qv off) 8); (aadd (pp off) (-3), idx)]
  ++ (if negb (resv off =? 0) then [(aadd ee (- resv off), 0)] else [])
  ++ (if 5 <=? resv off then [(aadd ee (-4), resv off); (aadd (aadd ee (-4)) 1, Z.shiftr (resv off) 8); (aadd (aadd ee (-4)) 2, Z.shiftr (resv off) 16); (aadd (aadd ee (-4)) 3, Z.shiftr (resv off) 24); (aadd ee (-5), 0)] else [])
  ++ [(aadd (pp off) (-3), Z.land idx 31 + Z.shiftl (if 5 <=? resv off then 5 else resv off) 5)].

Lemma EL_eq off : ef_list st g idx n off = EL off.
Proof.
  unfold ef_list, EL. rewrite (p0_eq st g idx n off). rewrite ef_c. fold (MR st g). fold stride.
  change (default (0%N, 0) (m_mem (MR st g))) with (gbase (MR st g)). rewrite ef_gbase. reflexivity.
Qed.

Lemma enframe_at_EL off : enframe_at st g idx n off = (wrs (EL off) st, pp off).
Proof. rewrite (enframe_at_eq st g idx n off), EL_eq, (p0_eq st g idx n off), ef_c. reflexivity. Qed.

Definition stw (off : Z) : mstate := wrs (EL off) st.
Definition stf (off : Z) : mstate := havoc (pp off) n (stw off).

Lemma stw_TKS off : TKS (stw off) (s_tick st).
Proof. apply wrs_TKS; [lia| exact (TKS_of _ _ _ _ _ INV)]. Qed.
Lemma stw_tick off : s_tick (stw off) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WEnframe2 ()) ["ENFRAME"] "h03offp;1p;2p;3g021Xj16Tg024bj25Tg02=Uj21Tg00H9j10Tg00Oaj34Tg02>Oj22Tg02?Kj33Tg00\TR0p,2stR1f0R2#6R3/51R4'1g00^i%04%0134123133X00P2O1W0o"). Qed.
Lemma stw_ctrl off : ctrl_eq st (stw off).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WEnframe2 ()) ["ENFRAME"] "h03offp;1p;2p;3g021Xj16Tg024bj25Tg02=Uj21Tg00H9j10Tg00Oaj34Tg02>Oj22Tg02?fj33Tg00\TR0p,2stR1f0R2#6R3/51R4'1g00^i%04%0134123133X00P2O1W0o"). Qed.
Lemma pp16 off : snd (pp off) mod 16 = 0.
Proof. unfold pp, aadd. cbn [snd]. unfold UNIT. rewrite Z.add_mod, ef_c16, Z.mul_comm, Z_mod_mult by lia. reflexivity. Qed.
Lemma stw_hav off u hl : r_hav (get_shadow (stw off) (fst (pp off))) !! u = Some hl -> hl_ticks hl (s_tick (stw off)).
Proof. intros Hu ch Hch. rewrite stw_tick. pose proof (stw_TKS off) as TK. rewrite <- (stw_tick off) in TK. rewrite <- (stw_tick off). exact (proj1 (sh_ticks_of _ _ TK) u hl ch Hu Hch). Qed.

Lemma stf_ctrl off : ctrl_eq st (stf off) /\ s_tick (stf off) = s_tick st.
Proof.
  destruct (havoc_ctrl (pp off) n (stw off)) as [C T]. split; [exact (ctrl_eq_trans _ _ _ (stw_ctrl off) C)| rewrite T; apply stw_tick].
Qed.

Lemma stf_read_out off r : ~ (fst r = fst bg /\ snd (pp off) <= snd r < snd (pp off) + n) ->
  cell_read (get_shadow (stf off) (fst r)) (snd r) = cell_read (get_shadow (stw off) (fst r)) (snd r).
Proof.
  intros Hr. unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
  apply (cell_read_havoc_out (pp off) n (stw off) (pp16 off) ltac:(lia) (stw_hav off)). exact Hr.
Qed.

(* [comment removed for export] *)
Lemma EL_addrs off a : 0 <= off -> UNIT * off + n <= stride - IB -> In a (map fst (EL off)) ->
  fst a = fst bg /\ snd c - 3 <= snd a < snd c + stride - 4 /\ ~ (snd (pp off) <= snd a < snd (pp off) + n).
Proof.
  intros Ho Hf Hin. pose proof ef_stride as [S16 _].
  assert (R : 0 <= resv off) by (unfold resv, ee, pp, aadd; cbn [fst snd]; unfold IB, UNIT in *; lia).
  unfold EL in Hin.
  destruct (Z.eqb_spec off 0) as [O0|O0]; destruct (Z.eqb_spec (resv off) 0) as [R0|R0]; destruct (Z.leb_spec 5 (resv off)) as [R5|R5];
    cbn [negb app map fst In] in Hin; unfold resv, ee, pp, aadd in *; cbn [fst snd] in *; unfold IB, UNIT in *;
    repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; unfold c; cbn [fst snd]; (split; [reflexivity| lia]).
Qed.

(* [comment removed for export] *)
Lemma stf_known_w off x w : 0 <= off -> UNIT * off + n <= stride - IB ->
  ~ (snd (pp off) <= x < snd (pp off) + n) ->
  lastw (EL off) (fst bg, x) None = Some w -> known (stf off) (fst bg, x) (Z.land w 255).
Proof.
  intros Ho Hf Hx HL. unfold known, SHd. cbn [fst snd].
  rewrite (stf_read_out off (fst bg, x)) by (cbn [fst snd]; tauto).
  unfold stw. rewrite (wrs_lastw (EL off) st (fst bg, x) (TKS_of _ _ _ _ _ INV)). rewrite HL. reflexivity.
Qed.

Lemma stf_known_old off x v : 0 <= off -> UNIT * off + n <= stride - IB ->
  ~ (snd (pp off) <= x < snd (pp off) + n) ->
  lastw (EL off) (fst bg, x) None = None -> known st (fst bg, x) v -> known (stf off) (fst bg, x) v.
Proof.
  intros Ho Hf Hx HL K. unfold known, SHd in *. cbn [fst snd] in *.
  rewrite (stf_read_out off (fst bg, x)) by (cbn [fst snd]; tauto).
  unfold stw. rewrite (wrs_lastw (EL off) st (fst bg, x) (TKS_of _ _ _ _ _ INV)). rewrite HL. exact K.
Qed.

Lemma EL_not_in off a : 0 <= off -> UNIT * off + n <= stride - IB ->
  snd (pp off) <= a < snd (pp off) + n -> ~ In (fst bg, a) (map fst (EL off)).
Proof. intros Ho Hf Ha Hin. destruct (EL_addrs off _ Ho Hf Hin) as (_ & _ & NR). apply NR. exact Ha. Qed.

Lemma stf_unknown off a : 0 <= off -> UNIT * off + n <= stride - IB ->
  snd (pp off) <= a < snd (pp off) + n -> unknown (stf off) (fst bg, a).
Proof.
  intros Ho Hf Ha. unfold unknown, SHd, stf. cbn [fst snd].
  destruct (cell_read_havoc_in (pp off) n (stw off) (pp16 off) ltac:(lia) (stw_hav off) (fst bg, a) eq_refl Ha) as [h Hh]; [| exists h; exact Hh].
  cbn [snd]. intros v tk Hc. unfold stw in Hc. rewrite wrs_cells_other in Hc by (apply EL_not_in; assumption).
  rewrite stw_tick. change (fst (pp off)) with (fst bg) in Hc.
  apply (TF2_interior_old X st L BL LS INV g bg idx Hg Hidx ef_NH TF a v tk Hc).
  unfold pp, aadd, c in Ha. cbn [fst snd] in Ha. rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia.
Qed.

(* [comment removed for export] *)
Ltac aeq :=
  match goal with
  | |- context [aptr_eqb ?a ?b] =>
      first [ rewrite (aptr_eqb_neq a b) by (unfold pp, ee, aadd, c; cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq a b)) by (unfold pp, ee, aadd, c; cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
  end.
Ltac lastw_eval :=
  unfold EL; cbn [lastw app negb]; repeat aeq; reflexivity.

Lemma res_eq off : resv off = stride - IB - UNIT * off - n.
Proof. unfold resv, ee, pp, aadd. cbn [snd]. lia. Qed.
Lemma qv_eq off : qv off = (snd c + UNIT * off - (snd bg + UNIT)) / UNIT.
Proof. reflexivity. Qed.

Lemma blk_ok off : 0 <= off <= 255 -> UNIT * off + n <= stride - IB ->
  blk_shadow_ok (stf off) ((c, off), n) g idx.
Proof.
  intros Ho Hf. pose proof ef_stride as [S16 SM].
  destruct (stf_ctrl off) as [CE TK].
  assert (MRE : MR (stf off) g = MR st g) by (apply MR_ext; exact (ce_metas _ _ CE)).
  pose proof (res_eq off) as RE.
  destruct Hg as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as LI.
  unfold blk_shadow_ok. cbn [bslot boff bsize fst snd]. rewrite MRE, ef_gbase. fold stride.
  replace (snd c + stride - IB - (snd c + UNIT * off) - n) with (resv off) by (rewrite RE; lia).
  replace ((snd c + UNIT * off - snd bg - UNIT) / UNIT) with (qv off) by (unfold qv, pp, aadd; cbn [snd]; f_equal; lia).
  pose proof (ef_q_range off Ho Hf) as QR.
  replace ((snd c + UNIT * off - (snd bg + UNIT)) / UNIT) with (qv off) in QR by (unfold qv, pp, aadd; cbn [snd]; f_equal; lia).
  assert (R0 : 0 <= resv off) by (rewrite RE; unfold IB, UNIT in *; lia).
  assert (NP : forall x, x < snd (pp off) \/ snd (pp off) + n <= x -> ~ (snd (pp off) <= x < snd (pp off) + n)) by (intros; lia).
  assert (PP : snd (pp off) = snd c + UNIT * off) by reflexivity.
  split; [| split; [| split; [| split; [| split; [exact QR| split; [| split]]]]]].
  - (* [comment removed for export] *) destruct (Z.eqb_spec off 0) as [O0|O0].
    + apply (stf_known_old off); [lia| exact Hf| apply NP; lia| |].
      * unfold EL. rewrite O0 at 1. cbn [Z.eqb negb app lastw].
        destruct (negb (resv off =? 0)); destruct (5 <=? resv off); cbn [lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
      * subst off. pose proof (ish_hdr0 _ _ ISH bg g idx (ex_intro _ ai Hb) ltac:(unfold cnt_of; lia)) as K.
        unfold c. cbn [snd]. replace (sstart (MR st g) idx + UNIT * 0 - 4) with (sstart (MR st g) idx - IB) by (unfold IB, UNIT; lia). exact K.
    + apply (stf_known_w off _ 0); [lia| exact Hf| apply NP; lia|].
      unfold EL. replace (off =? 0) with false by (symmetry; apply Z.eqb_neq; exact O0). cbn [negb app lastw].
      destruct (negb (resv off =? 0)); destruct (5 <=? resv off); cbn [lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *)
    replace (idx + 32 * Z.min (resv off) 5) with (Z.land (Z.land idx 31 + Z.shiftl (if 5 <=? resv off then 5 else resv off) 5) 255).
    2:{ replace (Z.land idx 31) with idx by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia). rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
        destruct (Z.leb_spec 5 (resv off)).
        - rewrite Z.min_r by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia.
        - rewrite Z.min_l by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia. }
    apply (stf_known_w off); [lia| exact Hf| apply NP; lia|].
    unfold EL. destruct (off =? 0); destruct (negb (resv off =? 0)); destruct (5 <=? resv off); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r.
    apply (stf_known_w off); [lia| exact Hf| apply NP; lia|].
    unfold EL. destruct (off =? 0); destruct (Z.eqb_spec (resv off) 0); destruct (Z.leb_spec 5 (resv off)); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) unfold byte_of. rewrite Z.mul_1_r.
    apply (stf_known_w off); [lia| exact Hf| apply NP; lia|].
    unfold EL. destruct (off =? 0); destruct (Z.eqb_spec (resv off) 0); destruct (Z.leb_spec 5 (resv off)); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
    assert (RS : resv off < 2 ^ 32).
    { rewrite RE. fold stride in Hres. unfold UNIT. lia. }
    assert (E5 : (5 <=? resv off) = true) by (apply Z.leb_le; exact R5).
    assert (EZ : (resv off =? 0) = false) by (apply Z.eqb_neq; lia).
    split; [| split; [| split; [| split; [| split; [| exact RS]]]]].
    1-4: apply (stf_known_w off); [lia| exact Hf| apply NP; rewrite ?RE; unfold IB, UNIT in *; lia|];
         unfold EL; rewrite E5, EZ; destruct (off =? 0); cbn [negb lastw app]; repeat aeq; try reflexivity.
    all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
    apply (stf_known_w off _ 0); [lia| exact Hf| apply NP; rewrite ?RE; unfold IB, UNIT in *; lia|].
    unfold EL; rewrite E5, EZ; destruct (off =? 0); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros RP.
    replace (snd c + stride - IB - resv off) with (snd (pp off) + n) by (rewrite RE, PP; lia).
    apply (stf_known_w off _ 0); [lia| exact Hf| apply NP; lia|].
    assert (EZ : (resv off =? 0) = false) by (apply Z.eqb_neq; lia).
    unfold EL; rewrite EZ. destruct (off =? 0); destruct (Z.leb_spec 5 (resv off)); cbn [negb lastw app];
      try (destruct (Z.eq_dec (resv off) 5)); try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros a Ha. apply (stf_unknown off); [lia| exact Hf|]. rewrite PP. exact Ha.
Qed.


(* [comment removed for export] *)
Lemma ef_INVL off : 0 <= off <= 255 -> UNIT * off + n <= stride - IB ->
  INVL X' (stf off) L (((c, off), n) :: BL) LS.
Proof.
  intros Ho Hf. destruct (stf_ctrl off) as [CE TK]. pose proof ef_stride as [S16 _].
  destruct Hg as [ai Hb] eqn:EHg.
  apply (INVL_add_block X st (stf off) L BL LS c off n INV HP CE TK).
  - intros m i Hs q Hq. rewrite ef_slots in Hs. inversion Hs. subst m i.
    assert (NQ : ~ (fst q = fst bg /\ snd (pp off) <= snd q < snd (pp off) + n)).
    { intros [F R]. apply Hq. unfold inT, c. cbn [fst snd]. split; [exact F|]. unfold pp, aadd, c in R. cbn [snd] in R. rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia. }
    rewrite (stf_read_out off q NQ). unfold stw. apply wrs_read_other.
    intros Hin. destruct (EL_addrs off q ltac:(lia) Hf Hin) as (F & R & _). apply Hq. unfold inT, c. cbn [fst snd]. split; [exact F|].
    rewrite sstart_succ. fold stride. unfold c in R. cbn [snd] in R. unfold IB in *. lia.
  - intros rid sh Hsh. assert (REG' : exists r, s_regions st !! fst bg = Some r /\ r_kind r = RKGroup) by exact (ig_region _ _ _ IG _ _ Hb).
    revert rid sh Hsh. change (DOMS st (stf off)). unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV)|]. intros q Hin. destruct (EL_addrs off q ltac:(lia) Hf Hin) as (F & _). rewrite F. exact REG'.
    + apply DOMS_havoc; [lia| | exact REG']. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV)|]. intros q Hin. destruct (EL_addrs off q ltac:(lia) Hf Hin) as (F & _). rewrite F. exact REG'.
  - change (TKS (stf off) (s_tick st)). unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. apply stw_TKS.
    + rewrite <- (stw_tick off). apply TKS_havoc; [apply pp16| lia| rewrite stw_tick; apply stw_TKS].
  - intros m i Hs. rewrite ef_slots in Hs. inversion Hs. subst m i. split; [exact Ho|]. split; [exact Hn|]. split; [exact Hf|].
    apply blk_ok; assumption.
Qed.

Theorem enframe_ft ctr (Post : mled -> mstate * optr -> Prop) :
  (forall off st' , 0 <= off <= 255 -> UNIT * off + n <= stride - IB ->
     INVL X' st' L (((c, off), n) :: BL) LS -> ctrl_eq st st' -> s_tick st' = s_tick st ->
     Post L (st', Some (aadd c (UNIT * off)))) ->
  ftree L (enframe_full st g idx n ctr (fun st2 p => ret (havoc p n st2, Some p))) Post.
Proof.
  intros HPost. pose proof ef_stride as [S16 SM].
  assert (KR : forall q v, cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256) by (intros q v; apply (known_range _ _ _ _ _ q v INV)).
  assert (SL : 0 <= slack) by (unfold slack; apply Z.div_pos; unfold IB, UNIT in *; lia).
  assert (SL16 : UNIT * slack <= stride - IB - n).
  { unfold slack, UNIT, IB in *. pose proof (Z.div_mod (stride - 4 - n) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (stride - 4 - n) 16 ltac:(lia)). lia. }
  assert (GO : forall v, 0 <= v < 256 ->
    ftree L (let '(st1, p) := enframe_at st g idx n (fold_off v slack) in ret (havoc p n st1, Some p)) Post).
  { intros v Hv. pose proof (fold_off_le v slack Hv SL) as FO.
    assert (F255 : fold_off v slack <= 255).
    { unfold fold_off in *. destruct (Z.ltb_spec slack v); [| lia]. cbn zeta in FO. unfold fold_off in FO. lia. }
    rewrite enframe_at_EL. cbn [ftree ret]. apply HPost.
    - lia.
    - unfold UNIT, IB in *. lia.
    - apply ef_INVL; [lia|]. unfold UNIT, IB in *. lia.
    - exact (proj1 (stf_ctrl _)).
    - exact (proj2 (stf_ctrl _)). }
  unfold enframe_full, enframe_read_off. fold (MR st g). fold stride. rewrite ef_slot.
  change ((stride - IB - n) / UNIT) with slack.
  apply rd8_ftree; [intros v; apply KR|]. intros b3 Hb3.
  destruct (b3 =? 0); cbn [negb].
  - apply GO. apply land255_range.
  - apply rd16_ftree; [intros q v; apply KR|]. intros o16 Ho16. apply GO. apply land255_range.
Qed.
End ENFRAME.
