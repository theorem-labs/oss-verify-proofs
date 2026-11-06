(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Kit () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3sndC35stdpp4base6LookupC46Stdlib6ZArith5Zmisc=iter_nat_of_ZC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith9BinIntDef1Z4iterC35stdpp8fin_maps:map_insertI35stdpp8fin_maps6FinMap00C35stdpp4base;RelDecisionC35stdpp8fin_maps:map_deleteC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6InsertC35stdpp4base6DeleteC35stdpp8fin_maps@lookup_delete_eqC35stdpp8fin_maps@lookup_delete_neC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes:option_mapC35stdpp8fin_maps7MapFoldC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z8eqb_reflC47Corelib4Init9Datatypes3fstC56Stdlib6NArith6BinNat1N3eqbC56Stdlib6NArith6BinNat1N8eqb_reflC59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums1Z00C47Corelib4Init5Logic3iffI47Corelib4Init5Logic3and00C47Corelib7Classes9Morphisms?eq_proper_proxyC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6NArith6BinNat1N6eqb_eqC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z6eqb_eqK47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes4prod01C47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib4Init9Datatypes4prod00C47Corelib7Classes?RelationClasses=iff_ReflexiveI47Corelib4Init9Datatypes7reflect00c59OSSVerify5KrLib4Spec6MI_Kit;aptr_eqb_eqC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes7reflect01c59OSSVerify5KrLib4Spec6MI_Kit=aptr_eqb_reflC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notK47Corelib4Init9Datatypes7reflect02K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib4Spec6MI_Kit=aptr_eqb_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02c59OSSVerify5KrLib4Spec6MI_Kit=optr_eqb_specC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec6Malloc9set_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC35stdpp4base6lookupC35stdpp6option;from_optionI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countablec59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Kit@get_meta_rec_putC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Kit<aptr_eqb_neqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Kit@get_meta_rec_updC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Kit@lookup_metas_putC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9get_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z4landK59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_group_active_idxC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc:get_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_regionC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;havoc_unitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;havoc_pagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5havocC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC59OSSVerify5KrLib4Spec6MallocAset_unmap_seq_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7set_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?sc_in_seq_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc:record_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?set_bounces_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>account_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=decay_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_headC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4wr32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib4Spec6Malloc8set_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl?strip_zero_hdrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9zero_hdrsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indK47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl@strip_enframe_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:enframe_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4wr16C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrlAstrip_nest_layoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;nest_layoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3lorc59OSSVerify5KrLib4Spec6MI_KitAs_tick_enframe_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Kit@s_tick_zero_hdrsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succC35stdpp4base6deleteC59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specC59OSSVerify5KrLib4Spec6Malloc>set_active_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=set_usage_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_bounceC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_KitAactive_set_activeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N8eqb_specC59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_KitDs_regions_new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;drop_regionC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_KitEs_regions_drop_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_KitBs_groups_put_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9del_groupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_KitBs_groups_del_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@group_active_idxC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib4Init9Datatypes8nat_rectC56Stdlib6ZArith6BinInt1Z4iterC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z7abs_natC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7add_1_rC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat8Zabs2Nat>abs_nat_nonnegC47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses>impl_ReflexiveI46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega6VarMap1t01C46Stdlib4Bool4Bool<andb_false_rK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z8leb_specK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z7div_modK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz04C57Corelib7BinNums6IntDef1Z3mulC57Corelib7BinNums6IntDef1Z3addc59OSSVerify5KrLib4Spec6MI_Kit:Z_iter_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9add_slotsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec6Malloc9del_slotsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5staleC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_KitEget_shadow_upd_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8stale_pgC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbI59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Kit8sh_ticksC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC56Stdlib6NArith6BinNat1N2leC46Stdlib4Bool4Bool=orb_false_iffC56Stdlib6NArith6BinNat1N3ltbC56Stdlib6NArith6BinNat1N6ltb_geC46Stdlib4Bool4BoolBnot_true_iff_falseC46Stdlib5Lists4List7existsbC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsBsubrelation_properC46Stdlib5Lists4List>existsb_existsC56Stdlib6NArith6BinNat1N2ltC56Stdlib6NArith6BinNat1N6ltb_ltC56Stdlib6ZArith4Znat3N2Z6inj_leC56Stdlib6ZArith4Znat3N2Z6inj_ltC47Corelib7Classes>Morphisms_Prop@not_iff_morphismC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationc59OSSVerify5KrLib4Spec6MI_Kit=not_stale_curC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MI_Kit=cell_read_wr8C1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma aptr_eqb_refl (a : aptr) : aptr_eqb a a = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ah11bp;3p;2p;1p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p7210p9P0p1002Qp4p710p9P0p10038p4p710p9P0p10040p4p710p8P0g004GR1p4p710R2p8P0P1p4p7210R3p8P0p1004dR4p4p710R5p8P0P4p4p7210R0p8p10058p4p7210g005\R6p4p710R7p8g006:R8p4p70R9g006oR:p4p710p8P9p1007Ip4p710R;p8P9p1007ep4p710R<p8P9p1008Cp4p7210R=p8P9p1008`p4p710R>p8P9p1009>p4p7210p8P9P7p8P9p1009[p4p7210p8P9p100:<R?p4p710R@p8P9P?p4p7210RAp8P9P?p4p73110R?p8P9p100:XRBp4p7511100RCp8P9PBp4p771111100RDp8P9P2p8P9P3p8P9p100;2R3p4p710REp8P9P3p4p7210R3p8P9p100;KRFp4p710p8P9PFp4p7210RGp8P9PFp4p73110RFp8P9p100;gRHp4p710p8P9PHp4p741110RHp8P9p100<@RIp4p710p8P9p100<XRJp4p710p8P9PJp4p741110RJp8P9p100=8p4p710p8P9p100=Op4p710p8P9p100=fp4p710p8P9p100>>RKp4p710p8P9p100>URLp4p710p8P9p100?1p4p710p8P9p100?Jp4p73110RMp8P9P5p8P9P0p8P9P4p4p73110R4p8P9p100?\RNp4p710ROp8P9PNp4p7210RPp8P9PNp4p73110RNp8P9p100@0RQp4p710p8P9PQp4p7210RQp8P9p100@Dp4p7<111111111110RRp8P9p100@fp4p7<111111111110RSp8P9p100AHp4p7<111111111110RTp8P9p100Ajp4p7<111111111110R9p8p100BLp4p70RUP;p8PUP<p8PUP=p8PUp100CAR=p4p710p8PUP=p4p7210p8PUP7p8PUPAp8PUP?p8PUPCp8PUPDp8PUP2p8PUPGp8PUPFp8PUPHp8PUPJp8PUP0p8PUP4p8PUPPp8PUPNp8PUPQp8PUPRp8PUPSp8PUPTp8PUP9p8P>PEp8P>P3p8PBp4p73101RUp100CeRQp4p73110p8PUP?p8PUp100D>p4p710p8PUp100DQR?p4p7201p8PUp100Dcp4p7201p8PUP4p8PUPNp8PUp100E5RNp4p73110p8PUp100EOp4p7201p8PBp4p710RUPQp4p710p8PUP@p8PUPEp8PUP3p8PUP5p8PUPOp8PUPNp4p710p8p100EbRNp4p710RUP>p8PUPEp8PUP3p8PUPMp8PNp4p741110RNPLp4p73101p8PRP7p8PSP7p8PTP7p8P9P7p8PHPCp8PCPHp8PIp4p741110RIPBp4p76111100RHp8PHPIp8PJPDp8PDPJp8PKp4p741110RKPBp4p7:1111111100RBp8PBPKp8P?p4p7200R?PNp8PNP?p8P1j33Tg00F6j24Tg00FSj22Tg00G1j2;Tg00GKj1:TP6j61Tg00Gmj38Tg00HJj27Tg00Hgj16Tg00IIj25TP:j39Tg00JBR:f0R6g00JbR139p=0P:P1g00KBR?g00K`RNf133RK/4K,26#0X1:P:P11216#0X1:1;:1A3?N6R1/41%:1E1A8?N6RN/7N%6NE11566#0eX08P6O1X08o"). Qed.

Lemma aptr_eqb_eq (a b : aptr) : aptr_eqb a b = true <-> a = b.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01Hh12H0h22H1h31ai001ah45lemmah52H2h61bh71eh81oh91rh:1Bh;2H3h<1ni011nh=2o'h>2r'h?1zi021zi031pp;2p;3p;4p;6p;;p;9g00HJj2:Tg00F6j28Tg00FSj2;Tg00L>R0j26Tg00LWR1j25Tg00M2j2ETg00M^j2CTg00N?j3OTg00O5j4BTg00OhR2j6NTg00PZj2MTg00Q:j4LTg00Qal;KTg00R\j2ITg00G1j2=Tg005\j6<Tg008Cj6ATg00S<j4@Tg00IIj2HTg00Gmj3GTg004Gj3FTg006oR3j3>Tg00SWj4JTg00T7l9DTg00KBR4g00K`R5f0R63Gp=9AF456p=7g00JBg00Jb7>6p=3g006:R7f1R8;>6p=2P4P5P8P6CJp=0p-0R9P0g00U1f5R:f4R;f3R<f2R=P8P6M9Dp=?A>486p=4A>586p=1g00UbR>P4P5%96R?%98':%76R@%78'8';#31268'6P8P>P4P510=8RA#9/:?%7A/8@';#312A6'6P;1::8R@18;6R?';#3%3@RB%3?RC'5'6f6RD/:=RE18:8RF';#3%3ERE%3FRF'5RGP610D:RH/2ARIPI1E9IRJE?W41C@?14:8R?,6BPG14D=RG/5FRBPEPGP6PFPFP9P0g00VB9O90REPFCBENPIPIPJE?W41M:811;6R@,6CPB11:8RB,5GRCP9P9^:9P0P9P9P0P0CLP1P2PGP9P0PEPGCBPFPBP6M;KPIPIPJE?W41I;615?@R@PI[10:;R?1086RJ'2RFPC[P1PGPBf7RB/0DRG10<=R='2R1P6f8RC/4;REP4P:f9R0/1:f:R9,08/2G[X9411C;R2P5P:10B6/2GX851=7HP0P6E<W0P0P6E<W0P8P6O2n2001000000120000000X0@P3P7PH10;<R;,28140:R:/52[P6P7P5P>P4P5P5P6P6n2001103000120101102X7710CBP;P6EA11B<R<P7P4P>P4P5P4P6P8n2001103000120101102X77100CP?P8EAP:149DP6f;RD/4BP4PCf<R:/1CRC1489f=R>/10'5[X<411DBP6PCP5P014DD1169'5X?5149911001=491=50C@P>P6E<b;W5P:P6E<b5W2P6O1b2P6O1b2X11P6O1X1In2002100000000100126=15E<[X37PAO1P61=7=O1b1X0FC@O2O2O2%9?%9J':%7?%7J'8';#3/6FeX=5X>4P8P6O2n2001103000121101102X85X94P8P6O2n20011030001211011021H86#31286'6eX67X37P8P6O2X67X37o"). Qed.

Lemma aptr_eqb_spec (a b : aptr) : reflect (a = b) (aptr_eqb a b).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01Eh11ah21bi001bh31Hh42b0h51ep;2p;3p;1p;6p;7g00IIj21Tg00G1j2=Tg006oj30Tg00W2j25Tg00WUj2;Tg00XQj2:Tg00Y4j16Tg007Ij64Tg00Z2j27Tg005\j78Tg00ZQj19Tg00Zjj2<Tg00JBR0f0R1g00JbR230p=3g00[MR39001p=2g006:R4f1R5/11R6P01=01f2R7/15R8=001P0f4R9f3R:'1=001f5R;=049/55]0P511:7R<#3A049:R=g00LW%36A0475[R6A0451%38R8[A04:7\81;51P5n2001000000120000000X24X14P6^24^14P1P;P9P5O3b3':W0%2<P4P9111;#2g00[mR<]0X141199#2P011;;%21X20P1P2%6;E4A0023P0P2P0p-0P1g00\JP<n0110000020000X50g00\fP3P1E4P<17<1b3b0W0P;P1P5F8X3=%9=e,<=W0n0110000020000P1O1b0b4X24X14P5P1O2X24W1o"). Qed.

Lemma aptr_eqb_neq (a b : aptr) : a <> b -> aptr_eqb a b = false.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ah11bi001bh21Hh32b0h41ei011eh51ni021nh61ri031rp;3p;1p;2g006oj30Tg00ZQj12Tg00]Bj23Tg00IIj21Tg00W2R0j26Tg00Z2j25Tg00G1j24Tg006:R1f1R2f0R3501#2f2R4/32A01421142'6f3R5/14g00JBR4P0f4R0=015g00[MR59042P2f5=010R6g00Jb=045P0P3O1'5W4P3O1%261445W5P3O1n10210010300021010110102b3b6W2X11X01P2P3O2X11W0o"). Qed.

Lemma optr_eqb_spec (a b : optr) : reflect (a = b) (optr_eqb a b).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ai001ah11bi011bh21Hh33Heqh41ei021eh52H0h62b0h71fh81ni031nh91ri041rh:1ti051op;2p;3p;1p;6g00^@j23Tg00W2R0j20Tg00]Bj2BTg006oj32Tg00IIj2:Tg00_9R1j1?Tg00_[j1>j2@Tg00G1j29Tg008Cj66Tg007ej6=Tg00XQj28Tg00ZQj15Tg00Z2j2<Tg00Zjj27Tg00`=j1ATg007Ij6;Tg00BLR2f1R3f0R432p=1g006:R5/@4p=4P1P511431343'0P3P1P5%43R6/141364'0f2R71B74A25741:74'0f3R8/:3g00JBP0f4R0=257f6R9#4R:%40R;'1R</03P3f5R==258R8%?5R>P:P:P;P>^05R;P>P4f7R:O1X7;%>5R?P?19;?E6P5P>P?P9P0P4E6E=,8<W4P4O1%58P>P5P1P5P5P4P4f8n10110500021000000X:>%4:%4=P4E6A25:=g00[mR:P7P4O1'<b3X2<%5<e,7<W8P4O1n10210110400021010210103b6b9%47R7%44R<'1137<'0eX15P4O1%A5R=,1<R8P4A2>6=P>P7P1P5p-0R0P4g00\JR9P:n10110500021000000X4>g00\fR?P=P4E;P:1<:4R;b5b3X28%58e'713<=,08en10110500021010000X05P4O1P1P511=413=4'0P411=<R8P4A2>=6P>P=P1P5P0P4P:P9n10110500021000000X4>P?P7P4E;P:P;b5b3X28%58e'713=<,08eX15P4O111==R519>='813==,05en10110500021010000n10110500021110000X12X02P3P4O2X12X02o"). Qed.

Lemma optr_eqb_refl (a : optr) : optr_eqb a a = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ah11bi001bh21ei011eh31ni021nh41ri031rp;2p;3p;1g00`_j26Tg006oj30Tg00^@j21Tg00W2R0j23Tg00G1j22Tg00ZQj15Tg00Z2j24Tg00BLR1f0R2/62A01221122'3f1R3/13g00JBR4P0f2R0=010g00JbR09043P3f3R3=013R31240W2P2O1%53g00[M=040P2f4,21O1'4W3P2O1n10210010300021010110102b1b4X01P2O1W0o"). Qed.

(* [comment removed for export] *)
Ltac case_ptr x y := destruct (aptr_eqb_spec x y) as [?EQp|?NEp]; [first [subst x | subst y | idtac]|].

#[export] Instance aptr_eq_dec : EqDecision aptr := _.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma get_meta_rec_put st m r x :
  get_meta_rec (put_meta m r st) x = if aptr_eqb x m then r else get_meta_rec st x.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01xh11mh21oh31ri001rh42sth51Hh63Heqh72NEh81bi011bh91ei021eh:2r0i031np;2p;3p;1p;4p;6p;?p;Ap;7p;5g00]Bj2WTg006oj33Tg00IIj27Tg00W2R0j2>Tg00a]j1VTg00b9j4UTg00bWj6OTg00Ebj4Bj3NTg00;gj4@j3ITg00<Xj4?j3CTg00:<j4=Tg00c8j14Tg00_9j1TTg00_[j2QTg00G1j29Tg00=8j3JTg00<@j3ATg00=Oj3DTg00=fj3ETg00>>j3FTg00?1j3GTg00AHl?HTg005\j65Tg00ZQj18Tg00d0j4KTg00Z2j2LTg00AjlAMTg00dLj2<Tg00eFj3PTg00f?j2:Tg00g<j7;Tg00gPj6RTg00gdj5STg006:R1g00h?R2f4R3f3R4f2R5f1R6f0R7F;p=6P1P2P4P5P6P7ERp=0P2P2P6g00i6P7DSp=1A3267p=2g00ilR81W75A31751775R9'>1764g00JBR:P0A3153%V2R0P1g00KBR;g00jeR<g00K`R=g00k>R>CUR?P;P<g00kWP=P>g00l5EOR>P2CBR=P1P?P>P2C@R<P3P=P1P2P=P1P?P>P2C?C=R;f6R@f5RAf7RB#4RCD6RDC0RE'1P:P2P6PAP=P<P3PCC0RF,10RGn0100000020000'2P6A314ARHP1P@P=P<P7P=P;PBP@f8#4RID6C0,10/2@X01%T2RJ1Q2A1107RK/2@X2J192AP=P<P@PDC0P1AN1?>RDAJ1?>RLAI1?>RMAA1?>RNAC1?>ROAD1?>RPAE1?>RQAF1?>R?g00lSRRAG1R>R>P2PCP@PAM?HE5P3P7E5W9P7O1%8HPJPFP=P<PAPIC0,10,2KX2J192GPEP1PDPLPMPNPOPPPQP?PRP>P2PCP@P3PAA31@3R@P1PBPAP7CKA31ABg00[mP5P7O1'Lb6W5%8@eMAME5W7P7O1n10210110000021110211103b8b:P=P<P7P=P;P5P6%44R;D6/<4#4C0,10P:P2P9P6P=P<P7P;C0,10n0100000020000'2eAP564/:7P:P2P9P61:47n0100000020000'2eX01X32X11X48P4P5P6P7O4X01X32X11W4o"). Qed.

Lemma get_meta_rec_upd st m f x :
  get_meta_rec (upd_meta m f st) x = if aptr_eqb x m then f (get_meta_rec st m) else get_meta_rec st x.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh11mh22sth31xp;2p;4p;3g00f?j20Tg00mOj44Tg00nPj32Tg00IIj21Tg006oj33Tg00ilR0g006:R1g00h?R2P2[R3f3R4f2R5f1R61045O1R7f0R8C4A2564/08g00JBP21185P71048n0100000020000532eX31X03X11X20P4P5P6P8O4X31W0W1W2o"). Qed.

Lemma get_meta_rec_put_same st m r : get_meta_rec (put_meta m r st) m = r.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11rh22sth31bp;2p;3p;1p;6p;4g00IIj27Tg00f?j20Tg006oj31Tg00G1j23Tg00Y4j16Tg005\j62Tg00eFj35Tg00mOj44Tg00ilR0g006:R1g00h?R2P2g00JBR3P2f1R4/74R5f0R6f2R7/04n0100000020000A1264X02P3g00JbP3P2P6P4f3/07n0100000020000=124X331326P5%64E2A5467/04P7P4P6P4C4E2X12X01X20P7P4P6O3W1W0W2o"). Qed.
Lemma get_meta_rec_put_other st m r x : x <> m -> get_meta_rec (put_meta m r st) x = get_meta_rec st x.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11rh22sth31xh41Hh51bp;3p;1p;2p;6p;4g006oj30Tg00ZQj18Tg00IIj23Tg00f?j21Tg00G1j27Tg00oIj36Tg005\j62Tg00eFj34Tg00mOj45Tg00ilR0g006:R1g00h?R2f0R3f2R4501#8P2g00JBR5P2f1R6f3R7'3R8P4f4R9/16R:n0100000020000f5/14R;9023X02P5g00[MP5P2P3P7P;n0100000020000=02;X55172:P8A6673E2A4749/16P9P7P4P6C5E2W4X31X12X01X20P7P4P6P3O4X31W1W0W2o"). Qed.
Lemma get_meta_rec_upd_same st m f : get_meta_rec (upd_meta m f st) m = f (get_meta_rec st m).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11fh22sth31bp;2p;3p;1p;6p;4g00IIj27Tg00f?j20Tg006oj31Tg00G1j23Tg00Y4j16Tg005\j62Tg00nPj35Tg010Fj44Tg00ilR0g006:R1g00h?R2P2[R3P2g00JBR4P2f1R5/75R6f0R7f2R8/05R9O1R:P9n0100000020000P5f3/08R9O1R;9127X02P4g00JbP4P2P7P;P9n0100000020000=12;X34132:P6%65E2A5578/05P8P5P7P5C4E2X13X01X20P8P5P7O3W1W0W2o"). Qed.
Lemma get_meta_rec_upd_other st m f x : x <> m -> get_meta_rec (upd_meta m f st) x = get_meta_rec st x.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11fh22sth31xh41Hh51bp;3p;1p;2p;6p;4g006oj31Tg00ZQj18Tg00IIj23Tg00f?j20Tg00G1j27Tg00oIj36Tg005\j62Tg00nPj34Tg010Fj45Tg00ilR0g006:R1g00h?R2P2[R3f0R4f2R5511#8P2g00JBR6P2f1R7f3R8'3R9P5f4R:/08O110:7R;n0100000020000f5R</05R=9124X02P6g00[MP6P2P4P810<:O1P=n0100000020000=12=X56172;P9A6784E2A485:/07P:P8P5P7C5E2W4X31X13X01X20P8P5P7P4O4X31W1W0W2o"). Qed.

Lemma s_metas_put_meta m r st : s_metas (put_meta m r st) = <[m := r]> (s_metas st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11rh22stp;4p;6p;1p;7p;2g00b9j47Tg00bWj66Tg00Ebj40Tg00<Xj41Tg00:<j45Tg00c8j12Tg00g<j73Tg00G1j24Tg006:R0g00h?R1g00ilR2P0g00KBR3g00jeR4g00K`R5g00k>R6C7R7P3P4g00kWP5P6g00l5E6R6P1C0R5P0P1P5P0P1P5P0P7P6P1C1C5f2R6f1R7f0R5#2F3'4X22X11X00P6P7P5O3W2W1W0o"). Qed.
Lemma s_metas_upd_meta m f st : s_metas (upd_meta m f st) = <[m := f (get_meta_rec st m)]> (s_metas st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh11mh22stp;4p;6p;2p;1p;7g00b9j48Tg00bWj67Tg00Ebj40Tg00<Xj41Tg00:<j46Tg00f?j22Tg00c8j13Tg00g<j74Tg00G1j25Tg006:R0g00h?R1P1[R2g00ilR3P0g00KBR4g00jeR5g00K`R6g00k>R7C8R8P4P5g00kWP6P7g00l5E7R7P1C0R6P0P1P6P0P1P6P0P8P7P1C1C6f2R1f1R7f0R8/21O1%38F4'5X23X02X10P1P7P8O3W2W0W1o"). Qed.

Lemma lookup_metas_put st m r x :
  s_metas (put_meta m r st) !! x = if aptr_eqb x m then Some r else s_metas st !! x.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01xh11mh21oh31ri001rh42sth51Hh63Heqh72NEh81bi011bh91ei021eh:2r0i031np;2p;3p;1p;4p;6p;7p;?p;Ag00]Bj2PTg006oj30Tg00IIj27Tg00W2R0j2:Tg00_9j1OTg00b9j4NTg00bWj6?Tg00Ebj4>j3MTg00;gj4<j3FTg00<Xj4;j3ATg00:<j49Tg00c8j12Tg00g<j75Tg00_[j24Tg00G1j28Tg00=8j3GTg00<@j3@Tg00=Oj3BTg00=fj3=Tg00>>j3CTg00?1j3DTg00AHl?ETg005\j63Tg00ZQj16Tg00d0j4HTg00Z2j2ITg00AjlAJTg00eFj3KTg00gPj6LTg006:R1g00h?R2f3R3f2R4f1R5f0R6ELp=1g00ilR71P64A01641764R8':1753g00JBR9P0f4R09014%O2R:P1g00KBR;g00jeR<g00K`R=g00k>R>CNR?P;P<g00kWP=P>g00l5E?R>P2C>R=P1P?P>P2C<R<P0P1P2P=P1P2P=P1P?P>P2C;C9R;f6R@f5RAf7RB#2RCF5RDC1REP9P:P5142ARFP=P<P0PCC1RGn010000002000030P5A013ARHP1P@P=P<P6P1P2P=P;PBP@f8#2R;F5C1142@RI50:X01P:PFA0:6IX2:18:FP=P<P@PDC1P1AM1?>RDAG1?>RFAF1?>RIA@1?>RJAA1?>RKAB1?>RLA=1?>RMAC1?>R?g00lSRNAD1N>R>P2PCP@PAM?EE3P0P6E3W9P6O1%6HP:PGP=P<PAP;C190:6X2:18:GPEP1PDPFPIPJPKPLPMP?PNP>P2PCP@P0PAA01@0R@P1PBPAP6CHA01ABg00[mP4P6O1'Ib6W5%6@eMAJE3W7P6O1n10210110000021110211103b8b:P=P<P6AK453#2C1P9P:P81425P=P<P6%23C1n010000002000050:eX01X32X11X47P3P4P5P6O4X01X32X11W4o"). Qed.
Lemma lookup_metas_upd st m f x :
  s_metas (upd_meta m f st) !! x = if aptr_eqb x m then Some (f (get_meta_rec st m)) else s_metas st !! x.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh11mh22sth31xp;2p;4p;1p;6p;3g00f?j2<Tg011Gj4;Tg00_9j13Tg00b9j42Tg00bWj6:Tg00Ebj46Tg00;gj45Tg00nPj34Tg00c8j10Tg00gPj61Tg00IIj27Tg00_[j28Tg006oj39Tg00ilR0g006:R1g00h?R2P2[R3f3R4f2R5f1R61<45O1R7f0R8C;%32R9P1P2P1g00KBR:g00jeR;g00K`R<g00k>R=C2R>P:P;g00kWP<P=g00l5E:R=P2C6R<P1P>P=P2C5R=P8A4564#0E1g00JBP917851827P1P2P<P=P8%04E1n010000002000039eX31X03X11X20P4P5P6P8O4X31W0W1W2o"). Qed.

(* [comment removed for export] *)
Lemma get_meta_rec_ext st st' x : s_metas st' = s_metas st -> get_meta_rec st' x = get_meta_rec st x.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth13st'h21xh31Hh41gp;4p;6p;1p;3p;2p;5g00b9j4=Tg00bWj6<Tg00Ebj46Tg00c8j10Tg006oj33Tg00a]j1:Tg00;gj48Tg00G1j27Tg005\j65Tg00f?j24Tg00gPj69Tg00gdj5;Tg006:R0g00h?R1f3R2f2R3f1R4f0R5E9p=1P1P1P4g00i6P5D;p=2g00ilR6P0g00KBR7g00jeR8g00K`R9g00k>R:C=R;P7P8g00kWP9P:g00l5E<R:P1C6R9%04%03R833P9%02R7%:1R<P9P0P;P:P1C8R:P3P5C1'2P9P:P3f4#0C1,2<531X49P9P:P4P7C1,2<,71P8P5E514341424531eW3X20X16X06P3P4P5O3X20X16W0o"). Qed.

(* [comment removed for export] *)
Ltac msimp := cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
                   m_set_prev m_set_next m_set_mem m_set_avail m_set_freed m_set_last_idx m_set_freeable m_set_sizeclass m_set_maplen
                   meta0] in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma s_ctx_upd_ctx f st : s_ctx (upd_ctx f st) = f (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh12stp;1p;2g012Hj11Tg00G1j20Tg013>R0P0[R1g00ilR2f1R3f0R4#1O1,00X12X01P3P4O2W1W0o"). Qed.
Lemma s_regions_upd_ctx f st : s_regions (upd_ctx f st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh12stp;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg013>R0P0[R0g00ilR1g00KBg00jeg00kWg014oC2f0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_shadow_upd_ctx f st : s_shadow (upd_ctx f st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh12stp;4p;1p;2g00Ebj42Tg015hj11Tg00G1j20Tg013>R0P0[R0g00ilR1g00KBg00jeg00kWg016aC2f0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_next_rid_upd_ctx f st : s_next_rid (upd_ctx f st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh12stp;1p;2g017Zj11Tg00G1j20Tg013>R0P0[R0g00ilR1g00KBf0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_metas_upd_ctx f st : s_metas (upd_ctx f st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh12stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg013>R0P0[R0g00ilR1g006:g00KBR2g00jeR3g00K`R4g00k>R5C4P2P3g00kWP4P5g00l5E3g00h?C0f0R5#1'2X11X00f1P5O2W1W0o"). Qed.
Lemma s_areas_upd_ctx f st : s_areas (upd_ctx f st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh12stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg013>R0P0[R0g00ilR1g006:g00KBR2g00jeR3g00K`R4g00k>R5C4P2P3g00kWP4P5g00l5E3g019MC0f0R5#1'2X11X00f1P5O2W1W0o"). Qed.
Lemma s_groups_upd_ctx f st : s_groups (upd_ctx f st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh12stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg013>R0P0[R0g00ilR1g006:g00KBR2g00jeR3g00K`R4g00k>R5C4P2P3g00kWP4P5g00l5E3g01;=C0f0R5#1'2X11X00f1P5O2W1W0o"). Qed.
Lemma s_slots_upd_ctx f st : s_slots (upd_ctx f st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh12stp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<4j13Tg00G1j22Tg013>R0P0[R0g00ilR1g006:R2g00KBR3g00jeR4g00K`R5g00k>R6C5P3P4g00kWP5P6g00l5E41025C1f0R5#3'2X11X00f1P5O2W1W0o"). Qed.
Lemma s_tick_upd_ctx f st : s_tick (upd_ctx f st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh12stp;1p;2g01<lj11Tg00G1j20Tg013>R0P0[R0g00ilR1g00KBf0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_secret_upd_ctx f st : s_secret (upd_ctx f st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh12stp;1p;2g01=cj11Tg00G1j20Tg013>R0P0[R0g00ilR1g00K`f0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_reserved_upd_ctx f st : s_reserved (upd_ctx f st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh12stp;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg013>R0P0[R0g00ilR1g00K`R2/32#2f0R2#0'1X11X00f1P2O2W1W0o"). Qed.
Lemma s_atop_upd_ctx f st : s_atop (upd_ctx f st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh12stp;1p;2g01@7j11Tg00G1j20Tg013>R0P0[R0g00ilR1g00K`f0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_ctx_set_regions v st : s_ctx (set_regions v st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;1p;2g00Ebj42Tg012Hj11Tg00G1j20Tg00KBg00jeg00kWg014oC2R0g00ilR1g013>f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma s_regions_set_regions v st : s_regions (set_regions v st) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;2g00Ebj41Tg00G1j20Tg00KBg00jeg00kWg014oC1R0g00ilR1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma s_shadow_set_regions v st : s_shadow (set_regions v st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;1p;2g00Ebj40Tg015hj12Tg00G1j21Tg00KBR0g00jeR1g00kWR2g014oC0R3g00ilR4P0P1P2g016aC0f0R2#2'1X04X13f1P2O2W0W1o"). Qed.
Lemma s_next_rid_set_regions v st : s_next_rid (set_regions v st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;1p;2g00Ebj42Tg017Zj11Tg00G1j20Tg00KBR0g00jeg00kWg014oC2R1g00ilR2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma s_metas_set_regions v st : s_metas (set_regions v st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00Ebj40Tg00b9j44Tg00bWj62Tg00c8j11Tg00G1j23Tg00KBR0g00jeR1g00kWR2g014oC0R3g00ilR4g006:P0P1g00K`R5g00k>R6C4P0P1P2P5P6g00l5E2g00h?C0f0R6#1'3X04X13f1P6O2W0W1o"). Qed.
Lemma s_areas_set_regions v st : s_areas (set_regions v st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00Ebj40Tg00b9j44Tg00bWj62Tg018Uj11Tg00G1j23Tg00KBR0g00jeR1g00kWR2g014oC0R3g00ilR4g006:P0P1g00K`R5g00k>R6C4P0P1P2P5P6g00l5E2g019MC0f0R6#1'3X04X13f1P6O2W0W1o"). Qed.
Lemma s_groups_set_regions v st : s_groups (set_regions v st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00Ebj40Tg00b9j44Tg00bWj62Tg01:Dj11Tg00G1j23Tg00KBR0g00jeR1g00kWR2g014oC0R3g00ilR4g006:P0P1g00K`R5g00k>R6C4P0P1P2P5P6g00l5E2g01;=C0f0R6#1'3X04X13f1P6O2W0W1o"). Qed.
Lemma s_slots_set_regions v st : s_slots (set_regions v st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00Ebj40Tg00b9j45Tg00bWj62Tg00Ubj21Tg01<4j14Tg00G1j23Tg00KBR0g00jeR1g00kWR2g014oC0R3g00ilR4g006:R5P0P1g00K`R6g00k>R7C5P0P1P2P6P7g00l5E21156C0f0R6#4'3X04X13f1P6O2W0W1o"). Qed.
Lemma s_tick_set_regions v st : s_tick (set_regions v st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;1p;2g00Ebj42Tg01<lj11Tg00G1j20Tg00KBR0g00jeg00kWg014oC2R1g00ilR2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma s_secret_set_regions v st : s_secret (set_regions v st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;1p;2g00Ebj42Tg01=cj11Tg00G1j20Tg00KBg00jeg00kWg014oC2R0g00ilR1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma s_reserved_set_regions v st : s_reserved (set_regions v st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;2p;1g00Ebj44Tg00Ubj23Tg01>\j10Tg01?<j11Tg00G1j22Tg00KBg00jeg00kWg014oC4R0g00ilR1g00K`R2/32#0f0R2#1'2X01X10f1P2O2W0W1o"). Qed.
Lemma s_atop_set_regions v st : s_atop (set_regions v st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;1p;2g00Ebj42Tg01@7j11Tg00G1j20Tg00KBg00jeg00kWg014oC2R0g00ilR1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma s_ctx_set_shadow v st : s_ctx (set_shadow v st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;1p;2g00Ebj42Tg012Hj11Tg00G1j20Tg00KBg00jeg00kWg016aC2R0g00ilR1g013>f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma s_regions_set_shadow v st : s_regions (set_shadow v st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;1p;2g00Ebj40Tg0145j12Tg00G1j21Tg00KBR0g00jeR1g00kWR2g016aC0R3g00ilR4P0P1P2g014oC0f0R2#2'1X04X13f1P2O2W0W1o"). Qed.
Lemma s_shadow_set_shadow v st : s_shadow (set_shadow v st) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;2g00Ebj41Tg00G1j20Tg00KBg00jeg00kWg016aC1R0g00ilR1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma s_next_rid_set_shadow v st : s_next_rid (set_shadow v st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;1p;2g00Ebj42Tg017Zj11Tg00G1j20Tg00KBR0g00jeg00kWg016aC2R1g00ilR2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma s_metas_set_shadow v st : s_metas (set_shadow v st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00Ebj40Tg00b9j44Tg00bWj62Tg00c8j11Tg00G1j23Tg00KBR0g00jeR1g00kWR2g016aC0R3g00ilR4g006:P0P1g00K`R5g00k>R6C4P0P1P2P5P6g00l5E2g00h?C0f0R6#1'3X04X13f1P6O2W0W1o"). Qed.
Lemma s_areas_set_shadow v st : s_areas (set_shadow v st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00Ebj40Tg00b9j44Tg00bWj62Tg018Uj11Tg00G1j23Tg00KBR0g00jeR1g00kWR2g016aC0R3g00ilR4g006:P0P1g00K`R5g00k>R6C4P0P1P2P5P6g00l5E2g019MC0f0R6#1'3X04X13f1P6O2W0W1o"). Qed.
Lemma s_groups_set_shadow v st : s_groups (set_shadow v st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00Ebj40Tg00b9j44Tg00bWj62Tg01:Dj11Tg00G1j23Tg00KBR0g00jeR1g00kWR2g016aC0R3g00ilR4g006:P0P1g00K`R5g00k>R6C4P0P1P2P5P6g00l5E2g01;=C0f0R6#1'3X04X13f1P6O2W0W1o"). Qed.
Lemma s_slots_set_shadow v st : s_slots (set_shadow v st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00Ebj40Tg00b9j45Tg00bWj62Tg00Ubj21Tg01<4j14Tg00G1j23Tg00KBR0g00jeR1g00kWR2g016aC0R3g00ilR4g006:R5P0P1g00K`R6g00k>R7C5P0P1P2P6P7g00l5E21156C0f0R6#4'3X04X13f1P6O2W0W1o"). Qed.
Lemma s_tick_set_shadow v st : s_tick (set_shadow v st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;1p;2g00Ebj42Tg01<lj11Tg00G1j20Tg00KBR0g00jeg00kWg016aC2R1g00ilR2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma s_secret_set_shadow v st : s_secret (set_shadow v st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;1p;2g00Ebj42Tg01=cj11Tg00G1j20Tg00KBg00jeg00kWg016aC2R0g00ilR1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma s_reserved_set_shadow v st : s_reserved (set_shadow v st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;2p;1g00Ebj44Tg00Ubj23Tg01>\j10Tg01?<j11Tg00G1j22Tg00KBg00jeg00kWg016aC4R0g00ilR1g00K`R2/32#0f0R2#1'2X01X10f1P2O2W0W1o"). Qed.
Lemma s_atop_set_shadow v st : s_atop (set_shadow v st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;1p;2g00Ebj42Tg01@7j11Tg00G1j20Tg00KBg00jeg00kWg016aC2R0g00ilR1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma s_ctx_set_next_rid v st : s_ctx (set_next_rid v st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;1p;2g012Hj11Tg00G1j20Tg00KBR0g00ilR1g013>f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma s_regions_set_next_rid v st : s_regions (set_next_rid v st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg00KBR0g00ilR1P0g00jeg00kWg014oC2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma s_shadow_set_next_rid v st : s_shadow (set_next_rid v st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;1p;2g00Ebj42Tg015hj11Tg00G1j20Tg00KBR0g00ilR1P0g00jeg00kWg016aC2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma s_next_rid_set_next_rid v st : s_next_rid (set_next_rid v st) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;2g00G1j20Tg00KBR0g00ilR1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma s_metas_set_next_rid v st : s_metas (set_next_rid v st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg00KBR0g00ilR1g006:P0g00jeR2g00K`R3g00k>R4C4P0P2g00kWP3P4g00l5E3g00h?C0f0R4#1'2X01X10f1P4O2W0W1o"). Qed.
Lemma s_areas_set_next_rid v st : s_areas (set_next_rid v st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg00KBR0g00ilR1g006:P0g00jeR2g00K`R3g00k>R4C4P0P2g00kWP3P4g00l5E3g019MC0f0R4#1'2X01X10f1P4O2W0W1o"). Qed.
Lemma s_groups_set_next_rid v st : s_groups (set_next_rid v st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg00KBR0g00ilR1g006:P0g00jeR2g00K`R3g00k>R4C4P0P2g00kWP3P4g00l5E3g01;=C0f0R4#1'2X01X10f1P4O2W0W1o"). Qed.
Lemma s_slots_set_next_rid v st : s_slots (set_next_rid v st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<4j13Tg00G1j22Tg00KBR0g00ilR1g006:R2P0g00jeR3g00K`R4g00k>R5C5P0P3g00kWP4P5g00l5E41024C1f0R4#3'2X01X10f1P4O2W0W1o"). Qed.
Lemma s_tick_set_next_rid v st : s_tick (set_next_rid v st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;1p;2g01<lj11Tg00G1j20Tg00KBR0g00ilR1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma s_secret_set_next_rid v st : s_secret (set_next_rid v st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;1p;2g01=cj11Tg00G1j20Tg00KBR0g00ilR1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma s_reserved_set_next_rid v st : s_reserved (set_next_rid v st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg00KBR0g00ilR1g00K`R2/32#2f0R2#0'1X01X10f1P2O2W0W1o"). Qed.
Lemma s_atop_set_next_rid v st : s_atop (set_next_rid v st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;1p;2g01@7j11Tg00G1j20Tg00KBR0g00ilR1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma s_ctx_set_metas v st : s_ctx (set_metas v st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg012Hj11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWP2P3g00l5E3g00h?C0R3g00ilR2g013>f0R1#1'2X02X13f1P1O2W0W1o"). Qed.
Lemma s_regions_set_metas v st : s_regions (set_metas v st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg0145j11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWR4P2P3g00l5E3g00h?C0R3g00ilR2P0P1P4g014oC0f0R4#1'2X02X13f1P4O2W0W1o"). Qed.
Lemma s_shadow_set_metas v st : s_shadow (set_metas v st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg015hj11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWR4P2P3g00l5E3g00h?C0R3g00ilR2P0P1P4g016aC0f0R4#1'2X02X13f1P4O2W0W1o"). Qed.
Lemma s_next_rid_set_metas v st : s_next_rid (set_metas v st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg017Zj11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWP2P3g00l5E3g00h?C0R3g00ilR2f0R1#1,20X02X13f1P1O2W0W1o"). Qed.
Lemma s_metas_set_metas v st : s_metas (set_metas v st) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2g00b9j43Tg00bWj62Tg00Ebj40Tg00G1j21Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C3P0P1g00kWP2P3g00l5E2g00h?C0R3g00ilR2f1R1,13X02X13P1f0O2W0W1o"). Qed.
Lemma s_areas_set_metas v st : s_areas (set_metas v st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C4R5P1P2g00kWP3P4g00l5E3R4g00h?C0R3g00ilR2P0P5P4g019MC0f0R4#1'2X02X13f1P4O2W0W1o"). Qed.
Lemma s_groups_set_metas v st : s_groups (set_metas v st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C4R5P1P2g00kWP3P4g00l5E3R4g00h?C0R3g00ilR2P0P5P4g01;=C0f0R4#1'2X02X13f1P4O2W0W1o"). Qed.
Lemma s_slots_set_metas v st : s_slots (set_metas v st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ebj40Tg00Ubj21Tg01<4j13Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C5R5P1P2g00kWP3P4g00l5E4R4g00h?C0R2g00ilR1P0P5P41103C0f0R3#3'2X01X12f1P3O2W0W1o"). Qed.
Lemma s_tick_set_metas v st : s_tick (set_metas v st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01<lj11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWP2P3g00l5E3g00h?C0R3g00ilR2f0R1#1,20X02X13f1P1O2W0W1o"). Qed.
Lemma s_secret_set_metas v st : s_secret (set_metas v st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01=cj11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWP2P3g00l5E3g00h?C0R3g00ilR1f0R0#1,22X01X13f1P0O2W0W1o"). Qed.
Lemma s_reserved_set_metas v st : s_reserved (set_metas v st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j46Tg00bWj65Tg00Ebj40Tg00Ubj21Tg01>\j14Tg01?<j12Tg00G1j23Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C6P0P1g00kWP2P3g00l5E5g00h?C0R3g00ilR11122#4f0R2#2'3X01X13f1P2O2W0W1o"). Qed.
Lemma s_atop_set_metas v st : s_atop (set_metas v st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01@7j11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWP2P3g00l5E3g00h?C0R3g00ilR1f0R0#1,22X01X13f1P0O2W0W1o"). Qed.
Lemma s_ctx_set_areas v st : s_ctx (set_areas v st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg012Hj11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWP2P3g00l5E3g019MC0R3g00ilR2g013>f0R1#1'2X02X13f1P1O2W0W1o"). Qed.
Lemma s_regions_set_areas v st : s_regions (set_areas v st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg0145j11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWR4P2P3g00l5E3g019MC0R3g00ilR2P0P1P4g014oC0f0R4#1'2X02X13f1P4O2W0W1o"). Qed.
Lemma s_shadow_set_areas v st : s_shadow (set_areas v st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg015hj11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWR4P2P3g00l5E3g019MC0R3g00ilR2P0P1P4g016aC0f0R4#1'2X02X13f1P4O2W0W1o"). Qed.
Lemma s_next_rid_set_areas v st : s_next_rid (set_areas v st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg017Zj11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWP2P3g00l5E3g019MC0R3g00ilR2f0R1#1,20X02X13f1P1O2W0W1o"). Qed.
Lemma s_metas_set_areas v st : s_metas (set_areas v st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C4R5P1P2g00kWP3P4g00l5E3R4g019MC0R3g00ilR2P0P5P4g00h?C0f0R4#1'2X02X13f1P4O2W0W1o"). Qed.
Lemma s_areas_set_areas v st : s_areas (set_areas v st) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2g00b9j43Tg00bWj62Tg00Ebj40Tg00G1j21Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C3P0P1g00kWP2P3g00l5E2g019MC0R3g00ilR2f1R1,13X02X13P1f0O2W0W1o"). Qed.
Lemma s_groups_set_areas v st : s_groups (set_areas v st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C4R5P1P2g00kWP3P4g00l5E3R4g019MC0R3g00ilR2P0P5P4g01;=C0f0R4#1'2X02X13f1P4O2W0W1o"). Qed.
Lemma s_slots_set_areas v st : s_slots (set_areas v st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ebj40Tg00Ubj21Tg01<4j13Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C5R5P1P2g00kWP3P4g00l5E4R4g019MC0R2g00ilR1P0P5P41103C0f0R3#3'2X01X12f1P3O2W0W1o"). Qed.
Lemma s_tick_set_areas v st : s_tick (set_areas v st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01<lj11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWP2P3g00l5E3g019MC0R3g00ilR2f0R1#1,20X02X13f1P1O2W0W1o"). Qed.
Lemma s_secret_set_areas v st : s_secret (set_areas v st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01=cj11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWP2P3g00l5E3g019MC0R3g00ilR1f0R0#1,22X01X13f1P0O2W0W1o"). Qed.
Lemma s_reserved_set_areas v st : s_reserved (set_areas v st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j46Tg00bWj65Tg00Ebj40Tg00Ubj21Tg01>\j14Tg01?<j12Tg00G1j23Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C6P0P1g00kWP2P3g00l5E5g019MC0R3g00ilR11122#4f0R2#2'3X01X13f1P2O2W0W1o"). Qed.
Lemma s_atop_set_areas v st : s_atop (set_areas v st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01@7j11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWP2P3g00l5E3g019MC0R3g00ilR1f0R0#1,22X01X13f1P0O2W0W1o"). Qed.
Lemma s_ctx_set_groups v st : s_ctx (set_groups v st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg012Hj11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWP2P3g00l5E3g01;=C0R3g00ilR2g013>f0R1#1'2X02X13f1P1O2W0W1o"). Qed.
Lemma s_regions_set_groups v st : s_regions (set_groups v st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg0145j11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWR4P2P3g00l5E3g01;=C0R3g00ilR2P0P1P4g014oC0f0R4#1'2X02X13f1P4O2W0W1o"). Qed.
Lemma s_shadow_set_groups v st : s_shadow (set_groups v st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg015hj11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWR4P2P3g00l5E3g01;=C0R3g00ilR2P0P1P4g016aC0f0R4#1'2X02X13f1P4O2W0W1o"). Qed.
Lemma s_next_rid_set_groups v st : s_next_rid (set_groups v st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg017Zj11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWP2P3g00l5E3g01;=C0R3g00ilR2f0R1#1,20X02X13f1P1O2W0W1o"). Qed.
Lemma s_metas_set_groups v st : s_metas (set_groups v st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C4R5P1P2g00kWP3P4g00l5E3R4g01;=C0R3g00ilR2P0P5P4g00h?C0f0R4#1'2X02X13f1P4O2W0W1o"). Qed.
Lemma s_areas_set_groups v st : s_areas (set_groups v st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C4R5P1P2g00kWP3P4g00l5E3R4g01;=C0R3g00ilR2P0P5P4g019MC0f0R4#1'2X02X13f1P4O2W0W1o"). Qed.
Lemma s_groups_set_groups v st : s_groups (set_groups v st) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2g00b9j43Tg00bWj62Tg00Ebj40Tg00G1j21Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C3P0P1g00kWP2P3g00l5E2g01;=C0R3g00ilR2f1R1,13X02X13P1f0O2W0W1o"). Qed.
Lemma s_slots_set_groups v st : s_slots (set_groups v st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ebj40Tg00Ubj21Tg01<4j13Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C5R5P1P2g00kWP3P4g00l5E4R4g01;=C0R2g00ilR1P0P5P41103C0f0R3#3'2X01X12f1P3O2W0W1o"). Qed.
Lemma s_tick_set_groups v st : s_tick (set_groups v st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01<lj11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWP2P3g00l5E3g01;=C0R3g00ilR2f0R1#1,20X02X13f1P1O2W0W1o"). Qed.
Lemma s_secret_set_groups v st : s_secret (set_groups v st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01=cj11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWP2P3g00l5E3g01;=C0R3g00ilR1f0R0#1,22X01X13f1P0O2W0W1o"). Qed.
Lemma s_reserved_set_groups v st : s_reserved (set_groups v st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j46Tg00bWj65Tg00Ebj40Tg00Ubj21Tg01>\j14Tg01?<j12Tg00G1j23Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C6P0P1g00kWP2P3g00l5E5g01;=C0R3g00ilR11122#4f0R2#2'3X01X13f1P2O2W0W1o"). Qed.
Lemma s_atop_set_groups v st : s_atop (set_groups v st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01@7j11Tg00G1j22Tg006:g00KBR0g00jeR1g00K`R2g00k>R3C4P0P1g00kWP2P3g00l5E3g01;=C0R3g00ilR1f0R0#1,22X01X13f1P0O2W0W1o"). Qed.
Lemma s_ctx_set_slots v st : s_ctx (set_slots v st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg012Hj13Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C5P1P2g00kWP3P4g00l5E41003C1R3g00ilR0g013>f0R4#3'2X00X13f1P4O2W0W1o"). Qed.
Lemma s_regions_set_slots v st : s_regions (set_slots v st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj21Tg00Ebj40Tg0145j13Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C5P1P2g00kWR5P3P4g00l5E41103C0R3g00ilR0P1P2P5g014oC0f0R5#3'2X00X13f1P5O2W0W1o"). Qed.
Lemma s_shadow_set_slots v st : s_shadow (set_slots v st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj21Tg00Ebj40Tg015hj13Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C5P1P2g00kWR5P3P4g00l5E41103C0R3g00ilR0P1P2P5g016aC0f0R5#3'2X00X13f1P5O2W0W1o"). Qed.
Lemma s_next_rid_set_slots v st : s_next_rid (set_slots v st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg017Zj13Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C5P1P2g00kWP3P4g00l5E41003C1R3g00ilR0f0R4#3,21X00X13f1P4O2W0W1o"). Qed.
Lemma s_metas_set_slots v st : s_metas (set_slots v st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj21Tg00Ebj40Tg00c8j13Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C5R5P1P2g00kWP3P4g00l5E4R41103C0R3g00ilR2P0P5P4g00h?C0f0R4#3'2X02X13f1P4O2W0W1o"). Qed.
Lemma s_areas_set_slots v st : s_areas (set_slots v st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj21Tg00Ebj40Tg018Uj13Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C5R5P1P2g00kWP3P4g00l5E4R41103C0R3g00ilR2P0P5P4g019MC0f0R4#3'2X02X13f1P4O2W0W1o"). Qed.
Lemma s_groups_set_slots v st : s_groups (set_slots v st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj21Tg00Ebj40Tg01:Dj13Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C5R5P1P2g00kWP3P4g00l5E4R41103C0R3g00ilR2P0P5P4g01;=C0f0R4#3'2X02X13f1P4O2W0W1o"). Qed.
Lemma s_slots_set_slots v st : s_slots (set_slots v st) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2g00b9j44Tg00bWj63Tg00Ubj20Tg00Ebj41Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C4P1P2g00kWP3P4g00l5E31003C1R3g00ilR0f1R4,23X00X13P4f0O2W0W1o"). Qed.
Lemma s_tick_set_slots v st : s_tick (set_slots v st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<lj13Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C5P1P2g00kWP3P4g00l5E41003C1R3g00ilR0f0R4#3,21X00X13f1P4O2W0W1o"). Qed.
Lemma s_secret_set_slots v st : s_secret (set_slots v st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01=cj13Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C5P1P2g00kWP3P4g00l5E41003C1R0g00ilR4f0R2#3,23X04X10f1P2O2W0W1o"). Qed.
Lemma s_reserved_set_slots v st : s_reserved (set_slots v st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j46Tg00bWj65Tg00Ubj20Tg00Ebj41Tg01>\j14Tg01?<j12Tg00G1j23Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C6P1P2g00kWP3P4g00l5E51003C1R0g00ilR41033#4f0R3#2'3X04X10f1P3O2W0W1o"). Qed.
Lemma s_atop_set_slots v st : s_atop (set_slots v st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01@7j13Tg00G1j22Tg006:R0g00KBR1g00jeR2g00K`R3g00k>R4C5P1P2g00kWP3P4g00l5E41003C1R0g00ilR4f0R2#3,23X04X10f1P2O2W0W1o"). Qed.
Lemma s_ctx_set_tick v st : s_ctx (set_tick v st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;1p;2g012Hj11Tg00G1j20Tg00KBR0g00ilR1g013>f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma s_regions_set_tick v st : s_regions (set_tick v st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg00KBR0g00ilR1P0g00jeg00kWg014oC2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma s_shadow_set_tick v st : s_shadow (set_tick v st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;1p;2g00Ebj42Tg015hj11Tg00G1j20Tg00KBR0g00ilR1P0g00jeg00kWg016aC2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma s_next_rid_set_tick v st : s_next_rid (set_tick v st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;1p;2g017Zj11Tg00G1j20Tg00KBR0g00ilR1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma s_metas_set_tick v st : s_metas (set_tick v st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg00KBR0g00ilR1g006:P0g00jeR2g00K`R3g00k>R4C4P0P2g00kWP3P4g00l5E3g00h?C0f0R4#1'2X01X10f1P4O2W0W1o"). Qed.
Lemma s_areas_set_tick v st : s_areas (set_tick v st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg00KBR0g00ilR1g006:P0g00jeR2g00K`R3g00k>R4C4P0P2g00kWP3P4g00l5E3g019MC0f0R4#1'2X01X10f1P4O2W0W1o"). Qed.
Lemma s_groups_set_tick v st : s_groups (set_tick v st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg00KBR0g00ilR1g006:P0g00jeR2g00K`R3g00k>R4C4P0P2g00kWP3P4g00l5E3g01;=C0f0R4#1'2X01X10f1P4O2W0W1o"). Qed.
Lemma s_slots_set_tick v st : s_slots (set_tick v st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<4j13Tg00G1j22Tg00KBR0g00ilR1g006:R2P0g00jeR3g00K`R4g00k>R5C5P0P3g00kWP4P5g00l5E41024C1f0R4#3'2X01X10f1P4O2W0W1o"). Qed.
Lemma s_tick_set_tick v st : s_tick (set_tick v st) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;2g00G1j20Tg00KBR0g00ilR1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma s_secret_set_tick v st : s_secret (set_tick v st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;1p;2g01=cj11Tg00G1j20Tg00KBR0g00ilR1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma s_reserved_set_tick v st : s_reserved (set_tick v st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg00KBR0g00ilR1g00K`R2/32#2f0R2#0'1X01X10f1P2O2W0W1o"). Qed.
Lemma s_atop_set_tick v st : s_atop (set_tick v st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sth11vp;1p;2g01@7j11Tg00G1j20Tg00KBR0g00ilR1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_secret v c : c_secret (set_secret v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;2g00G1j20Tg00K`R0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma c_init_done_set_secret v c : c_init_done (set_secret v c) = c_init_done c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01@nj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_mmap_counter_set_secret v c : c_mmap_counter (set_secret v c) = c_mmap_counter c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ajj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_free_meta_head_set_secret v c : c_free_meta_head (set_secret v c) = c_free_meta_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Bij11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_set_secret v c : c_avail_meta (set_secret v c) = c_avail_meta c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Cjj11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_secret v c : c_avail_meta_count (set_secret v c) = c_avail_meta_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Dgj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_secret v c : c_avail_meta_area_count (set_secret v c) = c_avail_meta_area_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ejj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_secret v c : c_meta_alloc_shift (set_secret v c) = c_meta_alloc_shift c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01G2j11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_head_set_secret v c : c_meta_area_head (set_secret v c) = c_meta_area_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01H5j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_secret v c : c_meta_area_tail (set_secret v c) = c_meta_area_tail c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01I6j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_secret v c : c_avail_meta_areas (set_secret v c) = c_avail_meta_areas c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01J7j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_active_set_secret v c : c_active (set_secret v c) = c_active c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01K:j11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5g006:C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_usage_set_secret v c : c_usage (set_secret v c) = c_usage c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01L3j11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_unmap_seq_set_secret v c : c_unmap_seq (set_secret v c) = c_unmap_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Lkj11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_bounces_set_secret v c : c_bounces (set_secret v c) = c_bounces c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Mgj11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_seq_set_secret v c : c_seq (set_secret v c) = c_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Naj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_brk_set_secret v c : c_brk (set_secret v c) = c_brk c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01OWj11Tg00G1j20Tg00K`R0g013>R1g01PMf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_init_done v c : c_secret (set_init_done v c) = c_secret c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01QHj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_init_done_set_init_done v c : c_init_done (set_init_done v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;2g00G1j20Tg00K`R0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma c_mmap_counter_set_init_done v c : c_mmap_counter (set_init_done v c) = c_mmap_counter c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ajj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_free_meta_head_set_init_done v c : c_free_meta_head (set_init_done v c) = c_free_meta_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Bij11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_set_init_done v c : c_avail_meta (set_init_done v c) = c_avail_meta c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Cjj11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_init_done v c : c_avail_meta_count (set_init_done v c) = c_avail_meta_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Dgj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_init_done v c : c_avail_meta_area_count (set_init_done v c) = c_avail_meta_area_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ejj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_init_done v c : c_meta_alloc_shift (set_init_done v c) = c_meta_alloc_shift c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01G2j11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_head_set_init_done v c : c_meta_area_head (set_init_done v c) = c_meta_area_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01H5j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_init_done v c : c_meta_area_tail (set_init_done v c) = c_meta_area_tail c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01I6j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_init_done v c : c_avail_meta_areas (set_init_done v c) = c_avail_meta_areas c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01J7j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_active_set_init_done v c : c_active (set_init_done v c) = c_active c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01K:j11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5g006:C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_usage_set_init_done v c : c_usage (set_init_done v c) = c_usage c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01L3j11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_unmap_seq_set_init_done v c : c_unmap_seq (set_init_done v c) = c_unmap_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Lkj11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_bounces_set_init_done v c : c_bounces (set_init_done v c) = c_bounces c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Mgj11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_seq_set_init_done v c : c_seq (set_init_done v c) = c_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Naj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_brk_set_init_done v c : c_brk (set_init_done v c) = c_brk c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01OWj11Tg00G1j20Tg00K`R0g013>R1g01PMf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_mmap_counter v c : c_secret (set_mmap_counter v c) = c_secret c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01QHj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_init_done_set_mmap_counter v c : c_init_done (set_mmap_counter v c) = c_init_done c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01@nj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_mmap_counter_set_mmap_counter v c : c_mmap_counter (set_mmap_counter v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;2g00G1j20Tg00K`R0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma c_free_meta_head_set_mmap_counter v c : c_free_meta_head (set_mmap_counter v c) = c_free_meta_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Bij11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_set_mmap_counter v c : c_avail_meta (set_mmap_counter v c) = c_avail_meta c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Cjj11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_mmap_counter v c : c_avail_meta_count (set_mmap_counter v c) = c_avail_meta_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Dgj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_mmap_counter v c : c_avail_meta_area_count (set_mmap_counter v c) = c_avail_meta_area_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ejj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_mmap_counter v c : c_meta_alloc_shift (set_mmap_counter v c) = c_meta_alloc_shift c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01G2j11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_head_set_mmap_counter v c : c_meta_area_head (set_mmap_counter v c) = c_meta_area_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01H5j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_mmap_counter v c : c_meta_area_tail (set_mmap_counter v c) = c_meta_area_tail c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01I6j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_mmap_counter v c : c_avail_meta_areas (set_mmap_counter v c) = c_avail_meta_areas c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01J7j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_active_set_mmap_counter v c : c_active (set_mmap_counter v c) = c_active c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01K:j11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5g006:C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_usage_set_mmap_counter v c : c_usage (set_mmap_counter v c) = c_usage c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01L3j11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_unmap_seq_set_mmap_counter v c : c_unmap_seq (set_mmap_counter v c) = c_unmap_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Lkj11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_bounces_set_mmap_counter v c : c_bounces (set_mmap_counter v c) = c_bounces c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Mgj11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_seq_set_mmap_counter v c : c_seq (set_mmap_counter v c) = c_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Naj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_brk_set_mmap_counter v c : c_brk (set_mmap_counter v c) = c_brk c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01OWj11Tg00G1j20Tg00K`R0g013>R1g01PMf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_free_meta_head v c : c_secret (set_free_meta_head v c) = c_secret c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01QHj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_init_done_set_free_meta_head v c : c_init_done (set_free_meta_head v c) = c_init_done c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01@nj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_mmap_counter_set_free_meta_head v c : c_mmap_counter (set_free_meta_head v c) = c_mmap_counter c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ajj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_free_meta_head_set_free_meta_head v c : c_free_meta_head (set_free_meta_head v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;2g00G1j20Tg00BLR0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma c_avail_meta_set_free_meta_head v c : c_avail_meta (set_free_meta_head v c) = c_avail_meta c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Cjj11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_free_meta_head v c : c_avail_meta_count (set_free_meta_head v c) = c_avail_meta_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Dgj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_free_meta_head v c : c_avail_meta_area_count (set_free_meta_head v c) = c_avail_meta_area_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ejj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_free_meta_head v c : c_meta_alloc_shift (set_free_meta_head v c) = c_meta_alloc_shift c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01G2j11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_head_set_free_meta_head v c : c_meta_area_head (set_free_meta_head v c) = c_meta_area_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01H5j11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_free_meta_head v c : c_meta_area_tail (set_free_meta_head v c) = c_meta_area_tail c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01I6j11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_free_meta_head v c : c_avail_meta_areas (set_free_meta_head v c) = c_avail_meta_areas c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01J7j11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_active_set_free_meta_head v c : c_active (set_free_meta_head v c) = c_active c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01K:j11Tg00G1j20Tg00BLR0g013>R1g00K`g00k>g00l5g006:C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_usage_set_free_meta_head v c : c_usage (set_free_meta_head v c) = c_usage c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01L3j11Tg00G1j20Tg00BLR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_unmap_seq_set_free_meta_head v c : c_unmap_seq (set_free_meta_head v c) = c_unmap_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Lkj11Tg00G1j20Tg00BLR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_bounces_set_free_meta_head v c : c_bounces (set_free_meta_head v c) = c_bounces c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Mgj11Tg00G1j20Tg00BLR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_seq_set_free_meta_head v c : c_seq (set_free_meta_head v c) = c_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Naj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_brk_set_free_meta_head v c : c_brk (set_free_meta_head v c) = c_brk c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01OWj11Tg00G1j20Tg00BLR0g013>R1g01PMf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_avail_meta v c : c_secret (set_avail_meta v c) = c_secret c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01QHj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_init_done_set_avail_meta v c : c_init_done (set_avail_meta v c) = c_init_done c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01@nj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_mmap_counter_set_avail_meta v c : c_mmap_counter (set_avail_meta v c) = c_mmap_counter c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ajj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_free_meta_head_set_avail_meta v c : c_free_meta_head (set_avail_meta v c) = c_free_meta_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Bij11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_set_avail_meta v c : c_avail_meta (set_avail_meta v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;2g00G1j20Tg00BLR0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_avail_meta v c : c_avail_meta_count (set_avail_meta v c) = c_avail_meta_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Dgj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_avail_meta v c : c_avail_meta_area_count (set_avail_meta v c) = c_avail_meta_area_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ejj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_avail_meta v c : c_meta_alloc_shift (set_avail_meta v c) = c_meta_alloc_shift c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01G2j11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_head_set_avail_meta v c : c_meta_area_head (set_avail_meta v c) = c_meta_area_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01H5j11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_avail_meta v c : c_meta_area_tail (set_avail_meta v c) = c_meta_area_tail c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01I6j11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_avail_meta v c : c_avail_meta_areas (set_avail_meta v c) = c_avail_meta_areas c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01J7j11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_active_set_avail_meta v c : c_active (set_avail_meta v c) = c_active c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01K:j11Tg00G1j20Tg00BLR0g013>R1g00K`g00k>g00l5g006:C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_usage_set_avail_meta v c : c_usage (set_avail_meta v c) = c_usage c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01L3j11Tg00G1j20Tg00BLR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_unmap_seq_set_avail_meta v c : c_unmap_seq (set_avail_meta v c) = c_unmap_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Lkj11Tg00G1j20Tg00BLR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_bounces_set_avail_meta v c : c_bounces (set_avail_meta v c) = c_bounces c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Mgj11Tg00G1j20Tg00BLR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_seq_set_avail_meta v c : c_seq (set_avail_meta v c) = c_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Naj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_brk_set_avail_meta v c : c_brk (set_avail_meta v c) = c_brk c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01OWj11Tg00G1j20Tg00BLR0g013>R1g01PMf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_avail_meta_count v c : c_secret (set_avail_meta_count v c) = c_secret c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01QHj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_init_done_set_avail_meta_count v c : c_init_done (set_avail_meta_count v c) = c_init_done c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01@nj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_mmap_counter_set_avail_meta_count v c : c_mmap_counter (set_avail_meta_count v c) = c_mmap_counter c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ajj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_free_meta_head_set_avail_meta_count v c : c_free_meta_head (set_avail_meta_count v c) = c_free_meta_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Bij11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_set_avail_meta_count v c : c_avail_meta (set_avail_meta_count v c) = c_avail_meta c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Cjj11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_avail_meta_count v c : c_avail_meta_count (set_avail_meta_count v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;2g00G1j20Tg00K`R0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_avail_meta_count v c : c_avail_meta_area_count (set_avail_meta_count v c) = c_avail_meta_area_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ejj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_avail_meta_count v c : c_meta_alloc_shift (set_avail_meta_count v c) = c_meta_alloc_shift c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01G2j11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_head_set_avail_meta_count v c : c_meta_area_head (set_avail_meta_count v c) = c_meta_area_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01H5j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_avail_meta_count v c : c_meta_area_tail (set_avail_meta_count v c) = c_meta_area_tail c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01I6j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_avail_meta_count v c : c_avail_meta_areas (set_avail_meta_count v c) = c_avail_meta_areas c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01J7j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_active_set_avail_meta_count v c : c_active (set_avail_meta_count v c) = c_active c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01K:j11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5g006:C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_usage_set_avail_meta_count v c : c_usage (set_avail_meta_count v c) = c_usage c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01L3j11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_unmap_seq_set_avail_meta_count v c : c_unmap_seq (set_avail_meta_count v c) = c_unmap_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Lkj11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_bounces_set_avail_meta_count v c : c_bounces (set_avail_meta_count v c) = c_bounces c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Mgj11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_seq_set_avail_meta_count v c : c_seq (set_avail_meta_count v c) = c_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Naj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_brk_set_avail_meta_count v c : c_brk (set_avail_meta_count v c) = c_brk c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01OWj11Tg00G1j20Tg00K`R0g013>R1g01PMf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_avail_meta_area_count v c : c_secret (set_avail_meta_area_count v c) = c_secret c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01QHj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_init_done_set_avail_meta_area_count v c : c_init_done (set_avail_meta_area_count v c) = c_init_done c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01@nj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_mmap_counter_set_avail_meta_area_count v c : c_mmap_counter (set_avail_meta_area_count v c) = c_mmap_counter c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ajj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_free_meta_head_set_avail_meta_area_count v c : c_free_meta_head (set_avail_meta_area_count v c) = c_free_meta_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Bij11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_set_avail_meta_area_count v c : c_avail_meta (set_avail_meta_area_count v c) = c_avail_meta c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Cjj11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_avail_meta_area_count v c : c_avail_meta_count (set_avail_meta_area_count v c) = c_avail_meta_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Dgj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_avail_meta_area_count v c : c_avail_meta_area_count (set_avail_meta_area_count v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;2g00G1j20Tg00K`R0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_avail_meta_area_count v c : c_meta_alloc_shift (set_avail_meta_area_count v c) = c_meta_alloc_shift c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01G2j11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_head_set_avail_meta_area_count v c : c_meta_area_head (set_avail_meta_area_count v c) = c_meta_area_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01H5j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_avail_meta_area_count v c : c_meta_area_tail (set_avail_meta_area_count v c) = c_meta_area_tail c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01I6j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_avail_meta_area_count v c : c_avail_meta_areas (set_avail_meta_area_count v c) = c_avail_meta_areas c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01J7j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_active_set_avail_meta_area_count v c : c_active (set_avail_meta_area_count v c) = c_active c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01K:j11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5g006:C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_usage_set_avail_meta_area_count v c : c_usage (set_avail_meta_area_count v c) = c_usage c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01L3j11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_unmap_seq_set_avail_meta_area_count v c : c_unmap_seq (set_avail_meta_area_count v c) = c_unmap_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Lkj11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_bounces_set_avail_meta_area_count v c : c_bounces (set_avail_meta_area_count v c) = c_bounces c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Mgj11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_seq_set_avail_meta_area_count v c : c_seq (set_avail_meta_area_count v c) = c_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Naj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_brk_set_avail_meta_area_count v c : c_brk (set_avail_meta_area_count v c) = c_brk c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01OWj11Tg00G1j20Tg00K`R0g013>R1g01PMf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_meta_alloc_shift v c : c_secret (set_meta_alloc_shift v c) = c_secret c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01QHj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_init_done_set_meta_alloc_shift v c : c_init_done (set_meta_alloc_shift v c) = c_init_done c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01@nj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_mmap_counter_set_meta_alloc_shift v c : c_mmap_counter (set_meta_alloc_shift v c) = c_mmap_counter c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ajj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_free_meta_head_set_meta_alloc_shift v c : c_free_meta_head (set_meta_alloc_shift v c) = c_free_meta_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Bij11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_set_meta_alloc_shift v c : c_avail_meta (set_meta_alloc_shift v c) = c_avail_meta c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Cjj11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_meta_alloc_shift v c : c_avail_meta_count (set_meta_alloc_shift v c) = c_avail_meta_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Dgj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_meta_alloc_shift v c : c_avail_meta_area_count (set_meta_alloc_shift v c) = c_avail_meta_area_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ejj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_meta_alloc_shift v c : c_meta_alloc_shift (set_meta_alloc_shift v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;2g00G1j20Tg00K`R0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma c_meta_area_head_set_meta_alloc_shift v c : c_meta_area_head (set_meta_alloc_shift v c) = c_meta_area_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01H5j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_meta_alloc_shift v c : c_meta_area_tail (set_meta_alloc_shift v c) = c_meta_area_tail c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01I6j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_meta_alloc_shift v c : c_avail_meta_areas (set_meta_alloc_shift v c) = c_avail_meta_areas c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01J7j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_active_set_meta_alloc_shift v c : c_active (set_meta_alloc_shift v c) = c_active c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01K:j11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5g006:C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_usage_set_meta_alloc_shift v c : c_usage (set_meta_alloc_shift v c) = c_usage c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01L3j11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_unmap_seq_set_meta_alloc_shift v c : c_unmap_seq (set_meta_alloc_shift v c) = c_unmap_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Lkj11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_bounces_set_meta_alloc_shift v c : c_bounces (set_meta_alloc_shift v c) = c_bounces c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Mgj11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_seq_set_meta_alloc_shift v c : c_seq (set_meta_alloc_shift v c) = c_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Naj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_brk_set_meta_alloc_shift v c : c_brk (set_meta_alloc_shift v c) = c_brk c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01OWj11Tg00G1j20Tg00K`R0g013>R1g01PMf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_meta_area_head v c : c_secret (set_meta_area_head v c) = c_secret c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01QHj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_init_done_set_meta_area_head v c : c_init_done (set_meta_area_head v c) = c_init_done c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01@nj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_mmap_counter_set_meta_area_head v c : c_mmap_counter (set_meta_area_head v c) = c_mmap_counter c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ajj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_free_meta_head_set_meta_area_head v c : c_free_meta_head (set_meta_area_head v c) = c_free_meta_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Bij11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_set_meta_area_head v c : c_avail_meta (set_meta_area_head v c) = c_avail_meta c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Cjj11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_meta_area_head v c : c_avail_meta_count (set_meta_area_head v c) = c_avail_meta_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Dgj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_meta_area_head v c : c_avail_meta_area_count (set_meta_area_head v c) = c_avail_meta_area_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ejj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_meta_area_head v c : c_meta_alloc_shift (set_meta_area_head v c) = c_meta_alloc_shift c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01G2j11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_head_set_meta_area_head v c : c_meta_area_head (set_meta_area_head v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;2g00G1j20Tg00BLR0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_meta_area_head v c : c_meta_area_tail (set_meta_area_head v c) = c_meta_area_tail c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01I6j11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_meta_area_head v c : c_avail_meta_areas (set_meta_area_head v c) = c_avail_meta_areas c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01J7j11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_active_set_meta_area_head v c : c_active (set_meta_area_head v c) = c_active c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01K:j11Tg00G1j20Tg00BLR0g013>R1g00K`g00k>g00l5g006:C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_usage_set_meta_area_head v c : c_usage (set_meta_area_head v c) = c_usage c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01L3j11Tg00G1j20Tg00BLR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_unmap_seq_set_meta_area_head v c : c_unmap_seq (set_meta_area_head v c) = c_unmap_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Lkj11Tg00G1j20Tg00BLR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_bounces_set_meta_area_head v c : c_bounces (set_meta_area_head v c) = c_bounces c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Mgj11Tg00G1j20Tg00BLR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_seq_set_meta_area_head v c : c_seq (set_meta_area_head v c) = c_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Naj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_brk_set_meta_area_head v c : c_brk (set_meta_area_head v c) = c_brk c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01OWj11Tg00G1j20Tg00BLR0g013>R1g01PMf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_meta_area_tail v c : c_secret (set_meta_area_tail v c) = c_secret c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01QHj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_init_done_set_meta_area_tail v c : c_init_done (set_meta_area_tail v c) = c_init_done c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01@nj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_mmap_counter_set_meta_area_tail v c : c_mmap_counter (set_meta_area_tail v c) = c_mmap_counter c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ajj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_free_meta_head_set_meta_area_tail v c : c_free_meta_head (set_meta_area_tail v c) = c_free_meta_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Bij11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_set_meta_area_tail v c : c_avail_meta (set_meta_area_tail v c) = c_avail_meta c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Cjj11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_meta_area_tail v c : c_avail_meta_count (set_meta_area_tail v c) = c_avail_meta_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Dgj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_meta_area_tail v c : c_avail_meta_area_count (set_meta_area_tail v c) = c_avail_meta_area_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ejj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_meta_area_tail v c : c_meta_alloc_shift (set_meta_area_tail v c) = c_meta_alloc_shift c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01G2j11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_head_set_meta_area_tail v c : c_meta_area_head (set_meta_area_tail v c) = c_meta_area_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01H5j11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_meta_area_tail v c : c_meta_area_tail (set_meta_area_tail v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;2g00G1j20Tg00BLR0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_meta_area_tail v c : c_avail_meta_areas (set_meta_area_tail v c) = c_avail_meta_areas c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01J7j11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_active_set_meta_area_tail v c : c_active (set_meta_area_tail v c) = c_active c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01K:j11Tg00G1j20Tg00BLR0g013>R1g00K`g00k>g00l5g006:C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_usage_set_meta_area_tail v c : c_usage (set_meta_area_tail v c) = c_usage c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01L3j11Tg00G1j20Tg00BLR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_unmap_seq_set_meta_area_tail v c : c_unmap_seq (set_meta_area_tail v c) = c_unmap_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Lkj11Tg00G1j20Tg00BLR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_bounces_set_meta_area_tail v c : c_bounces (set_meta_area_tail v c) = c_bounces c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Mgj11Tg00G1j20Tg00BLR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_seq_set_meta_area_tail v c : c_seq (set_meta_area_tail v c) = c_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Naj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_brk_set_meta_area_tail v c : c_brk (set_meta_area_tail v c) = c_brk c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01OWj11Tg00G1j20Tg00BLR0g013>R1g01PMf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_avail_meta_areas v c : c_secret (set_avail_meta_areas v c) = c_secret c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01QHj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_init_done_set_avail_meta_areas v c : c_init_done (set_avail_meta_areas v c) = c_init_done c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01@nj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_mmap_counter_set_avail_meta_areas v c : c_mmap_counter (set_avail_meta_areas v c) = c_mmap_counter c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ajj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_free_meta_head_set_avail_meta_areas v c : c_free_meta_head (set_avail_meta_areas v c) = c_free_meta_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Bij11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_set_avail_meta_areas v c : c_avail_meta (set_avail_meta_areas v c) = c_avail_meta c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Cjj11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_avail_meta_areas v c : c_avail_meta_count (set_avail_meta_areas v c) = c_avail_meta_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Dgj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_avail_meta_areas v c : c_avail_meta_area_count (set_avail_meta_areas v c) = c_avail_meta_area_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ejj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_avail_meta_areas v c : c_meta_alloc_shift (set_avail_meta_areas v c) = c_meta_alloc_shift c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01G2j11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_head_set_avail_meta_areas v c : c_meta_area_head (set_avail_meta_areas v c) = c_meta_area_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01H5j11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_avail_meta_areas v c : c_meta_area_tail (set_avail_meta_areas v c) = c_meta_area_tail c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01I6j11Tg00G1j20Tg00BLR0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_avail_meta_areas v c : c_avail_meta_areas (set_avail_meta_areas v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;2g00G1j20Tg00BLR0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma c_active_set_avail_meta_areas v c : c_active (set_avail_meta_areas v c) = c_active c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01K:j11Tg00G1j20Tg00BLR0g013>R1g00K`g00k>g00l5g006:C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_usage_set_avail_meta_areas v c : c_usage (set_avail_meta_areas v c) = c_usage c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01L3j11Tg00G1j20Tg00BLR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_unmap_seq_set_avail_meta_areas v c : c_unmap_seq (set_avail_meta_areas v c) = c_unmap_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Lkj11Tg00G1j20Tg00BLR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_bounces_set_avail_meta_areas v c : c_bounces (set_avail_meta_areas v c) = c_bounces c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Mgj11Tg00G1j20Tg00BLR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_seq_set_avail_meta_areas v c : c_seq (set_avail_meta_areas v c) = c_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Naj11Tg00G1j20Tg00BLR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_brk_set_avail_meta_areas v c : c_brk (set_avail_meta_areas v c) = c_brk c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01OWj11Tg00G1j20Tg00BLR0g013>R1g01PMf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_active_map v c : c_secret (set_active_map v c) = c_secret c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01QHj11Tg00G1j20Tg00K`R0g00k>g00l5g006:C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_init_done_set_active_map v c : c_init_done (set_active_map v c) = c_init_done c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01@nj11Tg00G1j20Tg00K`R0g00k>g00l5g006:C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_mmap_counter_set_active_map v c : c_mmap_counter (set_active_map v c) = c_mmap_counter c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Ajj11Tg00G1j20Tg00K`R0g00k>g00l5g006:C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_free_meta_head_set_active_map v c : c_free_meta_head (set_active_map v c) = c_free_meta_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Bij11Tg00G1j20Tg00K`g00k>g00l5g006:C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_set_active_map v c : c_avail_meta (set_active_map v c) = c_avail_meta c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Cjj11Tg00G1j20Tg00K`g00k>g00l5g006:C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_active_map v c : c_avail_meta_count (set_active_map v c) = c_avail_meta_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Dgj11Tg00G1j20Tg00K`R0g00k>g00l5g006:C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_active_map v c : c_avail_meta_area_count (set_active_map v c) = c_avail_meta_area_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Ejj11Tg00G1j20Tg00K`R0g00k>g00l5g006:C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_active_map v c : c_meta_alloc_shift (set_active_map v c) = c_meta_alloc_shift c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01G2j11Tg00G1j20Tg00K`R0g00k>g00l5g006:C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_meta_area_head_set_active_map v c : c_meta_area_head (set_active_map v c) = c_meta_area_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01H5j11Tg00G1j20Tg00K`g00k>g00l5g006:C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_active_map v c : c_meta_area_tail (set_active_map v c) = c_meta_area_tail c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01I6j11Tg00G1j20Tg00K`g00k>g00l5g006:C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_active_map v c : c_avail_meta_areas (set_active_map v c) = c_avail_meta_areas c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01J7j11Tg00G1j20Tg00K`g00k>g00l5g006:C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_active_set_active_map v c : c_active (set_active_map v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;2g00Ebj41Tg00G1j20Tg00K`g00k>g00l5g006:C1R0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma c_usage_set_active_map v c : c_usage (set_active_map v c) = c_usage c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj40Tg01L3j12Tg00G1j21Tg00K`R0g00k>R1g00l5R2g006:C0R3g013>R4P0P1P2P0C0f0R0#2'1X04X13f1P0O2W0W1o"). Qed.
Lemma c_unmap_seq_set_active_map v c : c_unmap_seq (set_active_map v c) = c_unmap_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj40Tg01Lkj12Tg00G1j21Tg00K`R0g00k>R1g00l5R2g006:C0R3g013>R4P0P1P2P0C0f0R0#2'1X04X13f1P0O2W0W1o"). Qed.
Lemma c_bounces_set_active_map v c : c_bounces (set_active_map v c) = c_bounces c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj40Tg01Mgj12Tg00G1j21Tg00K`R0g00k>R1g00l5R2g006:C0R3g013>R4P0P1P2P0C0f0R0#2'1X04X13f1P0O2W0W1o"). Qed.
Lemma c_seq_set_active_map v c : c_seq (set_active_map v c) = c_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Naj11Tg00G1j20Tg00K`R0g00k>g00l5g006:C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_brk_set_active_map v c : c_brk (set_active_map v c) = c_brk c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01OWj11Tg00G1j20Tg00K`g00k>g00l5g006:C2R0g013>R1g01PMf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_usage_map v c : c_secret (set_usage_map v c) = c_secret c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01QHj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_init_done_set_usage_map v c : c_init_done (set_usage_map v c) = c_init_done c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01@nj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_mmap_counter_set_usage_map v c : c_mmap_counter (set_usage_map v c) = c_mmap_counter c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Ajj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_free_meta_head_set_usage_map v c : c_free_meta_head (set_usage_map v c) = c_free_meta_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Bij11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_set_usage_map v c : c_avail_meta (set_usage_map v c) = c_avail_meta c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Cjj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_usage_map v c : c_avail_meta_count (set_usage_map v c) = c_avail_meta_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Dgj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_usage_map v c : c_avail_meta_area_count (set_usage_map v c) = c_avail_meta_area_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Ejj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_usage_map v c : c_meta_alloc_shift (set_usage_map v c) = c_meta_alloc_shift c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01G2j11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_meta_area_head_set_usage_map v c : c_meta_area_head (set_usage_map v c) = c_meta_area_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01H5j11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_usage_map v c : c_meta_area_tail (set_usage_map v c) = c_meta_area_tail c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01I6j11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_usage_map v c : c_avail_meta_areas (set_usage_map v c) = c_avail_meta_areas c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01J7j11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_active_set_usage_map v c : c_active (set_usage_map v c) = c_active c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj40Tg01K:j12Tg00G1j21Tg00K`R0g00k>R1g00l5R2P0C0R3g013>R4P0P1P2g006:C0f0R2#2'1X04X13f1P2O2W0W1o"). Qed.
Lemma c_usage_set_usage_map v c : c_usage (set_usage_map v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;2g00Ebj41Tg00G1j20Tg00K`R0g00k>g00l5P0C1R0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma c_unmap_seq_set_usage_map v c : c_unmap_seq (set_usage_map v c) = c_unmap_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Lkj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_bounces_set_usage_map v c : c_bounces (set_usage_map v c) = c_bounces c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Mgj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_seq_set_usage_map v c : c_seq (set_usage_map v c) = c_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Naj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_brk_set_usage_map v c : c_brk (set_usage_map v c) = c_brk c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01OWj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g01PMf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_unmap_seq_map v c : c_secret (set_unmap_seq_map v c) = c_secret c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01QHj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_init_done_set_unmap_seq_map v c : c_init_done (set_unmap_seq_map v c) = c_init_done c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01@nj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_mmap_counter_set_unmap_seq_map v c : c_mmap_counter (set_unmap_seq_map v c) = c_mmap_counter c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Ajj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_free_meta_head_set_unmap_seq_map v c : c_free_meta_head (set_unmap_seq_map v c) = c_free_meta_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Bij11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_set_unmap_seq_map v c : c_avail_meta (set_unmap_seq_map v c) = c_avail_meta c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Cjj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_unmap_seq_map v c : c_avail_meta_count (set_unmap_seq_map v c) = c_avail_meta_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Dgj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_unmap_seq_map v c : c_avail_meta_area_count (set_unmap_seq_map v c) = c_avail_meta_area_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Ejj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_unmap_seq_map v c : c_meta_alloc_shift (set_unmap_seq_map v c) = c_meta_alloc_shift c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01G2j11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_meta_area_head_set_unmap_seq_map v c : c_meta_area_head (set_unmap_seq_map v c) = c_meta_area_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01H5j11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_unmap_seq_map v c : c_meta_area_tail (set_unmap_seq_map v c) = c_meta_area_tail c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01I6j11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_unmap_seq_map v c : c_avail_meta_areas (set_unmap_seq_map v c) = c_avail_meta_areas c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01J7j11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_active_set_unmap_seq_map v c : c_active (set_unmap_seq_map v c) = c_active c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj40Tg01K:j12Tg00G1j21Tg00K`R0g00k>R1g00l5R2P0C0R3g013>R4P0P1P2g006:C0f0R2#2'1X04X13f1P2O2W0W1o"). Qed.
Lemma c_usage_set_unmap_seq_map v c : c_usage (set_unmap_seq_map v c) = c_usage c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01L3j11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_unmap_seq_set_unmap_seq_map v c : c_unmap_seq (set_unmap_seq_map v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;2g00Ebj41Tg00G1j20Tg00K`R0g00k>g00l5P0C1R0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma c_bounces_set_unmap_seq_map v c : c_bounces (set_unmap_seq_map v c) = c_bounces c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Mgj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_seq_set_unmap_seq_map v c : c_seq (set_unmap_seq_map v c) = c_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Naj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_brk_set_unmap_seq_map v c : c_brk (set_unmap_seq_map v c) = c_brk c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01OWj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g01PMf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_bounces_map v c : c_secret (set_bounces_map v c) = c_secret c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01QHj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_init_done_set_bounces_map v c : c_init_done (set_bounces_map v c) = c_init_done c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01@nj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_mmap_counter_set_bounces_map v c : c_mmap_counter (set_bounces_map v c) = c_mmap_counter c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Ajj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_free_meta_head_set_bounces_map v c : c_free_meta_head (set_bounces_map v c) = c_free_meta_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Bij11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_set_bounces_map v c : c_avail_meta (set_bounces_map v c) = c_avail_meta c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Cjj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_bounces_map v c : c_avail_meta_count (set_bounces_map v c) = c_avail_meta_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Dgj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_bounces_map v c : c_avail_meta_area_count (set_bounces_map v c) = c_avail_meta_area_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Ejj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_bounces_map v c : c_meta_alloc_shift (set_bounces_map v c) = c_meta_alloc_shift c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01G2j11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_meta_area_head_set_bounces_map v c : c_meta_area_head (set_bounces_map v c) = c_meta_area_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01H5j11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_bounces_map v c : c_meta_area_tail (set_bounces_map v c) = c_meta_area_tail c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01I6j11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_bounces_map v c : c_avail_meta_areas (set_bounces_map v c) = c_avail_meta_areas c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01J7j11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_active_set_bounces_map v c : c_active (set_bounces_map v c) = c_active c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj40Tg01K:j12Tg00G1j21Tg00K`R0g00k>R1g00l5R2P0C0R3g013>R4P0P1P2g006:C0f0R2#2'1X04X13f1P2O2W0W1o"). Qed.
Lemma c_usage_set_bounces_map v c : c_usage (set_bounces_map v c) = c_usage c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01L3j11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_unmap_seq_set_bounces_map v c : c_unmap_seq (set_bounces_map v c) = c_unmap_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Lkj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_bounces_set_bounces_map v c : c_bounces (set_bounces_map v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;2g00Ebj41Tg00G1j20Tg00K`R0g00k>g00l5P0C1R0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma c_seq_set_bounces_map v c : c_seq (set_bounces_map v c) = c_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Naj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R1g013>R2f0R3#1,00X02X11f1P3O2W0W1o"). Qed.
Lemma c_brk_set_bounces_map v c : c_brk (set_bounces_map v c) = c_brk c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01OWj11Tg00G1j20Tg00K`R0g00k>g00l5P0C2R0g013>R1g01PMf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_seq v c : c_secret (set_seq v c) = c_secret c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01QHj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_init_done_set_seq v c : c_init_done (set_seq v c) = c_init_done c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01@nj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_mmap_counter_set_seq v c : c_mmap_counter (set_seq v c) = c_mmap_counter c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ajj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_free_meta_head_set_seq v c : c_free_meta_head (set_seq v c) = c_free_meta_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Bij11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_set_seq v c : c_avail_meta (set_seq v c) = c_avail_meta c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Cjj11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_seq v c : c_avail_meta_count (set_seq v c) = c_avail_meta_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Dgj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_seq v c : c_avail_meta_area_count (set_seq v c) = c_avail_meta_area_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ejj11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_seq v c : c_meta_alloc_shift (set_seq v c) = c_meta_alloc_shift c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01G2j11Tg00G1j20Tg00K`R0g013>R1f0R2#1,00X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_head_set_seq v c : c_meta_area_head (set_seq v c) = c_meta_area_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01H5j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_seq v c : c_meta_area_tail (set_seq v c) = c_meta_area_tail c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01I6j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_seq v c : c_avail_meta_areas (set_seq v c) = c_avail_meta_areas c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01J7j11Tg00G1j20Tg00K`R0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_active_set_seq v c : c_active (set_seq v c) = c_active c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01K:j11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5g006:C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_usage_set_seq v c : c_usage (set_seq v c) = c_usage c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01L3j11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_unmap_seq_set_seq v c : c_unmap_seq (set_seq v c) = c_unmap_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Lkj11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_bounces_set_seq v c : c_bounces (set_seq v c) = c_bounces c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Mgj11Tg00G1j20Tg00K`R0g013>R1P0g00k>g00l5P0C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_seq_set_seq v c : c_seq (set_seq v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;2g00G1j20Tg00K`R0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
Lemma c_brk_set_seq v c : c_brk (set_seq v c) = c_brk c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01OWj11Tg00G1j20Tg00K`R0g013>R1g01PMf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_secret_set_brk v c : c_secret (set_brk v c) = c_secret c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01QHj11Tg00G1j20Tg01PMR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_init_done_set_brk v c : c_init_done (set_brk v c) = c_init_done c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01@nj11Tg00G1j20Tg01PMR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_mmap_counter_set_brk v c : c_mmap_counter (set_brk v c) = c_mmap_counter c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ajj11Tg00G1j20Tg01PMR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_free_meta_head_set_brk v c : c_free_meta_head (set_brk v c) = c_free_meta_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Bij11Tg00G1j20Tg01PMR0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_set_brk v c : c_avail_meta (set_brk v c) = c_avail_meta c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Cjj11Tg00G1j20Tg01PMR0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_count_set_brk v c : c_avail_meta_count (set_brk v c) = c_avail_meta_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Dgj11Tg00G1j20Tg01PMR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_area_count_set_brk v c : c_avail_meta_area_count (set_brk v c) = c_avail_meta_area_count c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Ejj11Tg00G1j20Tg01PMR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_alloc_shift_set_brk v c : c_meta_alloc_shift (set_brk v c) = c_meta_alloc_shift c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01G2j11Tg00G1j20Tg01PMR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_head_set_brk v c : c_meta_area_head (set_brk v c) = c_meta_area_head c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01H5j11Tg00G1j20Tg01PMR0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_meta_area_tail_set_brk v c : c_meta_area_tail (set_brk v c) = c_meta_area_tail c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01I6j11Tg00G1j20Tg01PMR0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_avail_meta_areas_set_brk v c : c_avail_meta_areas (set_brk v c) = c_avail_meta_areas c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01J7j11Tg00G1j20Tg01PMR0g013>R1g00BLf0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_active_set_brk v c : c_active (set_brk v c) = c_active c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01K:j11Tg00G1j20Tg01PMR0g013>R1g00K`g00k>g00l5g006:C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_usage_set_brk v c : c_usage (set_brk v c) = c_usage c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01L3j11Tg00G1j20Tg01PMR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_unmap_seq_set_brk v c : c_unmap_seq (set_brk v c) = c_unmap_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Lkj11Tg00G1j20Tg01PMR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_bounces_set_brk v c : c_bounces (set_brk v c) = c_bounces c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;4p;1p;2g00Ebj42Tg01Mgj11Tg00G1j20Tg01PMR0g013>R1g00K`R2g00k>g00l5P2C2f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_seq_set_brk v c : c_seq (set_brk v c) = c_seq c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;1p;2g01Naj11Tg00G1j20Tg01PMR0g013>R1g00K`f0R2#1'0X01X10f1P2O2W0W1o"). Qed.
Lemma c_brk_set_brk v c : c_brk (set_brk v c) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ch11vp;2g00G1j20Tg01PMR0g013>R1f1R2,00X01X10P2f0O2W0W1o"). Qed.
#[export] Hint Rewrite s_ctx_upd_ctx s_regions_upd_ctx s_shadow_upd_ctx s_next_rid_upd_ctx s_metas_upd_ctx s_areas_upd_ctx s_groups_upd_ctx s_slots_upd_ctx s_tick_upd_ctx s_secret_upd_ctx s_reserved_upd_ctx s_atop_upd_ctx s_ctx_set_regions s_regions_set_regions s_shadow_set_regions s_next_rid_set_regions s_metas_set_regions s_areas_set_regions s_groups_set_regions s_slots_set_regions s_tick_set_regions s_secret_set_regions s_reserved_set_regions s_atop_set_regions s_ctx_set_shadow s_regions_set_shadow s_shadow_set_shadow s_next_rid_set_shadow s_metas_set_shadow s_areas_set_shadow s_groups_set_shadow s_slots_set_shadow s_tick_set_shadow s_secret_set_shadow s_reserved_set_shadow s_atop_set_shadow s_ctx_set_next_rid s_regions_set_next_rid s_shadow_set_next_rid s_next_rid_set_next_rid s_metas_set_next_rid s_areas_set_next_rid s_groups_set_next_rid s_slots_set_next_rid s_tick_set_next_rid s_secret_set_next_rid s_reserved_set_next_rid s_atop_set_next_rid s_ctx_set_metas s_regions_set_metas s_shadow_set_metas s_next_rid_set_metas s_metas_set_metas s_areas_set_metas s_groups_set_metas s_slots_set_metas s_tick_set_metas s_secret_set_metas s_reserved_set_metas s_atop_set_metas s_ctx_set_areas s_regions_set_areas s_shadow_set_areas s_next_rid_set_areas s_metas_set_areas s_areas_set_areas s_groups_set_areas s_slots_set_areas s_tick_set_areas s_secret_set_areas s_reserved_set_areas s_atop_set_areas s_ctx_set_groups s_regions_set_groups s_shadow_set_groups s_next_rid_set_groups s_metas_set_groups s_areas_set_groups s_groups_set_groups s_slots_set_groups s_tick_set_groups s_secret_set_groups s_reserved_set_groups s_atop_set_groups s_ctx_set_slots s_regions_set_slots s_shadow_set_slots s_next_rid_set_slots s_metas_set_slots s_areas_set_slots s_groups_set_slots s_slots_set_slots s_tick_set_slots s_secret_set_slots s_reserved_set_slots s_atop_set_slots s_ctx_set_tick s_regions_set_tick s_shadow_set_tick s_next_rid_set_tick s_metas_set_tick s_areas_set_tick s_groups_set_tick s_slots_set_tick s_tick_set_tick s_secret_set_tick s_reserved_set_tick s_atop_set_tick c_secret_set_secret c_init_done_set_secret c_mmap_counter_set_secret c_free_meta_head_set_secret c_avail_meta_set_secret c_avail_meta_count_set_secret c_avail_meta_area_count_set_secret c_meta_alloc_shift_set_secret c_meta_area_head_set_secret c_meta_area_tail_set_secret c_avail_meta_areas_set_secret c_active_set_secret c_usage_set_secret c_unmap_seq_set_secret c_bounces_set_secret c_seq_set_secret c_brk_set_secret c_secret_set_init_done c_init_done_set_init_done c_mmap_counter_set_init_done c_free_meta_head_set_init_done c_avail_meta_set_init_done c_avail_meta_count_set_init_done c_avail_meta_area_count_set_init_done c_meta_alloc_shift_set_init_done c_meta_area_head_set_init_done c_meta_area_tail_set_init_done c_avail_meta_areas_set_init_done c_active_set_init_done c_usage_set_init_done c_unmap_seq_set_init_done c_bounces_set_init_done c_seq_set_init_done c_brk_set_init_done c_secret_set_mmap_counter c_init_done_set_mmap_counter c_mmap_counter_set_mmap_counter c_free_meta_head_set_mmap_counter c_avail_meta_set_mmap_counter c_avail_meta_count_set_mmap_counter c_avail_meta_area_count_set_mmap_counter c_meta_alloc_shift_set_mmap_counter c_meta_area_head_set_mmap_counter c_meta_area_tail_set_mmap_counter c_avail_meta_areas_set_mmap_counter c_active_set_mmap_counter c_usage_set_mmap_counter c_unmap_seq_set_mmap_counter c_bounces_set_mmap_counter c_seq_set_mmap_counter c_brk_set_mmap_counter c_secret_set_free_meta_head c_init_done_set_free_meta_head c_mmap_counter_set_free_meta_head c_free_meta_head_set_free_meta_head c_avail_meta_set_free_meta_head c_avail_meta_count_set_free_meta_head c_avail_meta_area_count_set_free_meta_head c_meta_alloc_shift_set_free_meta_head c_meta_area_head_set_free_meta_head c_meta_area_tail_set_free_meta_head c_avail_meta_areas_set_free_meta_head c_active_set_free_meta_head c_usage_set_free_meta_head c_unmap_seq_set_free_meta_head c_bounces_set_free_meta_head c_seq_set_free_meta_head c_brk_set_free_meta_head c_secret_set_avail_meta c_init_done_set_avail_meta c_mmap_counter_set_avail_meta c_free_meta_head_set_avail_meta c_avail_meta_set_avail_meta c_avail_meta_count_set_avail_meta c_avail_meta_area_count_set_avail_meta c_meta_alloc_shift_set_avail_meta c_meta_area_head_set_avail_meta c_meta_area_tail_set_avail_meta c_avail_meta_areas_set_avail_meta c_active_set_avail_meta c_usage_set_avail_meta c_unmap_seq_set_avail_meta c_bounces_set_avail_meta c_seq_set_avail_meta c_brk_set_avail_meta c_secret_set_avail_meta_count c_init_done_set_avail_meta_count c_mmap_counter_set_avail_meta_count c_free_meta_head_set_avail_meta_count c_avail_meta_set_avail_meta_count c_avail_meta_count_set_avail_meta_count c_avail_meta_area_count_set_avail_meta_count c_meta_alloc_shift_set_avail_meta_count c_meta_area_head_set_avail_meta_count c_meta_area_tail_set_avail_meta_count c_avail_meta_areas_set_avail_meta_count c_active_set_avail_meta_count c_usage_set_avail_meta_count c_unmap_seq_set_avail_meta_count c_bounces_set_avail_meta_count c_seq_set_avail_meta_count c_brk_set_avail_meta_count c_secret_set_avail_meta_area_count c_init_done_set_avail_meta_area_count c_mmap_counter_set_avail_meta_area_count c_free_meta_head_set_avail_meta_area_count c_avail_meta_set_avail_meta_area_count c_avail_meta_count_set_avail_meta_area_count c_avail_meta_area_count_set_avail_meta_area_count c_meta_alloc_shift_set_avail_meta_area_count c_meta_area_head_set_avail_meta_area_count c_meta_area_tail_set_avail_meta_area_count c_avail_meta_areas_set_avail_meta_area_count c_active_set_avail_meta_area_count c_usage_set_avail_meta_area_count c_unmap_seq_set_avail_meta_area_count c_bounces_set_avail_meta_area_count c_seq_set_avail_meta_area_count c_brk_set_avail_meta_area_count c_secret_set_meta_alloc_shift c_init_done_set_meta_alloc_shift c_mmap_counter_set_meta_alloc_shift c_free_meta_head_set_meta_alloc_shift c_avail_meta_set_meta_alloc_shift c_avail_meta_count_set_meta_alloc_shift c_avail_meta_area_count_set_meta_alloc_shift c_meta_alloc_shift_set_meta_alloc_shift c_meta_area_head_set_meta_alloc_shift c_meta_area_tail_set_meta_alloc_shift c_avail_meta_areas_set_meta_alloc_shift c_active_set_meta_alloc_shift c_usage_set_meta_alloc_shift c_unmap_seq_set_meta_alloc_shift c_bounces_set_meta_alloc_shift c_seq_set_meta_alloc_shift c_brk_set_meta_alloc_shift c_secret_set_meta_area_head c_init_done_set_meta_area_head c_mmap_counter_set_meta_area_head c_free_meta_head_set_meta_area_head c_avail_meta_set_meta_area_head c_avail_meta_count_set_meta_area_head c_avail_meta_area_count_set_meta_area_head c_meta_alloc_shift_set_meta_area_head c_meta_area_head_set_meta_area_head c_meta_area_tail_set_meta_area_head c_avail_meta_areas_set_meta_area_head c_active_set_meta_area_head c_usage_set_meta_area_head c_unmap_seq_set_meta_area_head c_bounces_set_meta_area_head c_seq_set_meta_area_head c_brk_set_meta_area_head c_secret_set_meta_area_tail c_init_done_set_meta_area_tail c_mmap_counter_set_meta_area_tail c_free_meta_head_set_meta_area_tail c_avail_meta_set_meta_area_tail c_avail_meta_count_set_meta_area_tail c_avail_meta_area_count_set_meta_area_tail c_meta_alloc_shift_set_meta_area_tail c_meta_area_head_set_meta_area_tail c_meta_area_tail_set_meta_area_tail c_avail_meta_areas_set_meta_area_tail c_active_set_meta_area_tail c_usage_set_meta_area_tail c_unmap_seq_set_meta_area_tail c_bounces_set_meta_area_tail c_seq_set_meta_area_tail c_brk_set_meta_area_tail c_secret_set_avail_meta_areas c_init_done_set_avail_meta_areas c_mmap_counter_set_avail_meta_areas c_free_meta_head_set_avail_meta_areas c_avail_meta_set_avail_meta_areas c_avail_meta_count_set_avail_meta_areas c_avail_meta_area_count_set_avail_meta_areas c_meta_alloc_shift_set_avail_meta_areas c_meta_area_head_set_avail_meta_areas c_meta_area_tail_set_avail_meta_areas c_avail_meta_areas_set_avail_meta_areas c_active_set_avail_meta_areas c_usage_set_avail_meta_areas c_unmap_seq_set_avail_meta_areas c_bounces_set_avail_meta_areas c_seq_set_avail_meta_areas c_brk_set_avail_meta_areas c_secret_set_active_map c_init_done_set_active_map c_mmap_counter_set_active_map c_free_meta_head_set_active_map c_avail_meta_set_active_map c_avail_meta_count_set_active_map c_avail_meta_area_count_set_active_map c_meta_alloc_shift_set_active_map c_meta_area_head_set_active_map c_meta_area_tail_set_active_map c_avail_meta_areas_set_active_map c_active_set_active_map c_usage_set_active_map c_unmap_seq_set_active_map c_bounces_set_active_map c_seq_set_active_map c_brk_set_active_map c_secret_set_usage_map c_init_done_set_usage_map c_mmap_counter_set_usage_map c_free_meta_head_set_usage_map c_avail_meta_set_usage_map c_avail_meta_count_set_usage_map c_avail_meta_area_count_set_usage_map c_meta_alloc_shift_set_usage_map c_meta_area_head_set_usage_map c_meta_area_tail_set_usage_map c_avail_meta_areas_set_usage_map c_active_set_usage_map c_usage_set_usage_map c_unmap_seq_set_usage_map c_bounces_set_usage_map c_seq_set_usage_map c_brk_set_usage_map c_secret_set_unmap_seq_map c_init_done_set_unmap_seq_map c_mmap_counter_set_unmap_seq_map c_free_meta_head_set_unmap_seq_map c_avail_meta_set_unmap_seq_map c_avail_meta_count_set_unmap_seq_map c_avail_meta_area_count_set_unmap_seq_map c_meta_alloc_shift_set_unmap_seq_map c_meta_area_head_set_unmap_seq_map c_meta_area_tail_set_unmap_seq_map c_avail_meta_areas_set_unmap_seq_map c_active_set_unmap_seq_map c_usage_set_unmap_seq_map c_unmap_seq_set_unmap_seq_map c_bounces_set_unmap_seq_map c_seq_set_unmap_seq_map c_brk_set_unmap_seq_map c_secret_set_bounces_map c_init_done_set_bounces_map c_mmap_counter_set_bounces_map c_free_meta_head_set_bounces_map c_avail_meta_set_bounces_map c_avail_meta_count_set_bounces_map c_avail_meta_area_count_set_bounces_map c_meta_alloc_shift_set_bounces_map c_meta_area_head_set_bounces_map c_meta_area_tail_set_bounces_map c_avail_meta_areas_set_bounces_map c_active_set_bounces_map c_usage_set_bounces_map c_unmap_seq_set_bounces_map c_bounces_set_bounces_map c_seq_set_bounces_map c_brk_set_bounces_map c_secret_set_seq c_init_done_set_seq c_mmap_counter_set_seq c_free_meta_head_set_seq c_avail_meta_set_seq c_avail_meta_count_set_seq c_avail_meta_area_count_set_seq c_meta_alloc_shift_set_seq c_meta_area_head_set_seq c_meta_area_tail_set_seq c_avail_meta_areas_set_seq c_active_set_seq c_usage_set_seq c_unmap_seq_set_seq c_bounces_set_seq c_seq_set_seq c_brk_set_seq c_secret_set_brk c_init_done_set_brk c_mmap_counter_set_brk c_free_meta_head_set_brk c_avail_meta_set_brk c_avail_meta_count_set_brk c_avail_meta_area_count_set_brk c_meta_alloc_shift_set_brk c_meta_area_head_set_brk c_meta_area_tail_set_brk c_avail_meta_areas_set_brk c_active_set_brk c_usage_set_brk c_unmap_seq_set_brk c_bounces_set_brk c_seq_set_brk c_brk_set_brk : mst.
Lemma s_regions_set_active sc v st : s_regions (set_active sc v st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg00K`R0g00BLR1g00ilR2g00KBg00jeg00kWg014oC2f0R3#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_shadow_set_active sc v st : s_shadow (set_active sc v st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;1p;2g00Ebj42Tg015hj11Tg00G1j20Tg00K`R0g00BLR1g00ilR2g00KBg00jeg00kWg016aC2f0R3#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_next_rid_set_active sc v st : s_next_rid (set_active sc v st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g017Zj11Tg00G1j20Tg00K`R0g00BLR1g00ilR2g00KBf0R3#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_metas_set_active sc v st : s_metas (set_active sc v st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg00K`R0g00BLR1g00ilR2g006:g00KBR3g00jeR4P0g00k>R5C4P3P4g00kWP0P5g00l5E3g00h?C0f0R5#1'2X12X21X00f2f1P5O3W1W2W0o"). Qed.
Lemma s_areas_set_active sc v st : s_areas (set_active sc v st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg00K`R0g00BLR1g00ilR2g006:g00KBR3g00jeR4P0g00k>R5C4P3P4g00kWP0P5g00l5E3g019MC0f0R5#1'2X12X21X00f2f1P5O3W1W2W0o"). Qed.
Lemma s_groups_set_active sc v st : s_groups (set_active sc v st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg00K`R0g00BLR1g00ilR2g006:g00KBR3g00jeR4P0g00k>R5C4P3P4g00kWP0P5g00l5E3g01;=C0f0R5#1'2X12X21X00f2f1P5O3W1W2W0o"). Qed.
Lemma s_slots_set_active sc v st : s_slots (set_active sc v st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<4j13Tg00G1j22Tg00K`R0g00BLR1g00ilR2g006:R3g00KBR4g00jeR5P0g00k>R6C5P4P5g00kWP0P6g00l5E41030C1f0R3#3'2X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_tick_set_active sc v st : s_tick (set_active sc v st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g01<lj11Tg00G1j20Tg00K`R0g00BLR1g00ilR2g00KBf0R3#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_secret_set_active sc v st : s_secret (set_active sc v st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g01=cj11Tg00G1j20Tg00K`R0g00BLR1g00ilR2f0R3#1,00X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_reserved_set_active sc v st : s_reserved (set_active sc v st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg00K`R0g00BLR1g00ilR21300#2f0R3#0'1X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_atop_set_active sc v st : s_atop (set_active sc v st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g01@7j11Tg00G1j20Tg00K`R0g00BLR1g00ilR2f0R3#1,00X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_regions_set_usage sc v st : s_regions (set_usage sc v st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg00K`R0g00ilR1g00KBg00jeg00kWg014oC2f0R2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma s_shadow_set_usage sc v st : s_shadow (set_usage sc v st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;1p;2g00Ebj42Tg015hj11Tg00G1j20Tg00K`R0g00ilR1g00KBg00jeg00kWg016aC2f0R2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma s_next_rid_set_usage sc v st : s_next_rid (set_usage sc v st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g017Zj11Tg00G1j20Tg00K`R0g00ilR1g00KBf0R2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma s_metas_set_usage sc v st : s_metas (set_usage sc v st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg00K`R0g00ilR1g006:g00KBR2g00jeR3P0g00k>R4C4P2P3g00kWP0P4g00l5E3g00h?C0f0R4#1'2X11X20X00f2f1P4O3W1X20W0o"). Qed.
Lemma s_areas_set_usage sc v st : s_areas (set_usage sc v st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg00K`R0g00ilR1g006:g00KBR2g00jeR3P0g00k>R4C4P2P3g00kWP0P4g00l5E3g019MC0f0R4#1'2X11X20X00f2f1P4O3W1X20W0o"). Qed.
Lemma s_groups_set_usage sc v st : s_groups (set_usage sc v st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg00K`R0g00ilR1g006:g00KBR2g00jeR3P0g00k>R4C4P2P3g00kWP0P4g00l5E3g01;=C0f0R4#1'2X11X20X00f2f1P4O3W1X20W0o"). Qed.
Lemma s_slots_set_usage sc v st : s_slots (set_usage sc v st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<4j13Tg00G1j22Tg00K`R0g00ilR1g006:R2g00KBR3g00jeR4P0g00k>R5C5P3P4g00kWP0P5g00l5E41020C1f0R2#3'2X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma s_tick_set_usage sc v st : s_tick (set_usage sc v st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g01<lj11Tg00G1j20Tg00K`R0g00ilR1g00KBf0R2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma s_secret_set_usage sc v st : s_secret (set_usage sc v st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g01=cj11Tg00G1j20Tg00K`R0g00ilR1f0R2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma s_reserved_set_usage sc v st : s_reserved (set_usage sc v st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg00K`R0g00ilR11300#2f0R2#0'1X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma s_atop_set_usage sc v st : s_atop (set_usage sc v st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g01@7j11Tg00G1j20Tg00K`R0g00ilR1f0R2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma s_regions_set_bounce i v st : s_regions (set_bounce i v st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg00K`R0g00ilR1g00KBg00jeg00kWg014oC2f0R2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma s_shadow_set_bounce i v st : s_shadow (set_bounce i v st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;4p;1p;2g00Ebj42Tg015hj11Tg00G1j20Tg00K`R0g00ilR1g00KBg00jeg00kWg016aC2f0R2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma s_next_rid_set_bounce i v st : s_next_rid (set_bounce i v st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g017Zj11Tg00G1j20Tg00K`R0g00ilR1g00KBf0R2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma s_metas_set_bounce i v st : s_metas (set_bounce i v st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg00K`R0g00ilR1g006:g00KBR2g00jeR3P0g00k>R4C4P2P3g00kWP0P4g00l5E3g00h?C0f0R4#1'2X11X20X00f2f1P4O3W1X20W0o"). Qed.
Lemma s_areas_set_bounce i v st : s_areas (set_bounce i v st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg00K`R0g00ilR1g006:g00KBR2g00jeR3P0g00k>R4C4P2P3g00kWP0P4g00l5E3g019MC0f0R4#1'2X11X20X00f2f1P4O3W1X20W0o"). Qed.
Lemma s_groups_set_bounce i v st : s_groups (set_bounce i v st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg00K`R0g00ilR1g006:g00KBR2g00jeR3P0g00k>R4C4P2P3g00kWP0P4g00l5E3g01;=C0f0R4#1'2X11X20X00f2f1P4O3W1X20W0o"). Qed.
Lemma s_slots_set_bounce i v st : s_slots (set_bounce i v st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<4j13Tg00G1j22Tg00K`R0g00ilR1g006:R2g00KBR3g00jeR4P0g00k>R5C5P3P4g00kWP0P5g00l5E41020C1f0R2#3'2X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma s_tick_set_bounce i v st : s_tick (set_bounce i v st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g01<lj11Tg00G1j20Tg00K`R0g00ilR1g00KBf0R2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma s_secret_set_bounce i v st : s_secret (set_bounce i v st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g01=cj11Tg00G1j20Tg00K`R0g00ilR1f0R2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma s_reserved_set_bounce i v st : s_reserved (set_bounce i v st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg00K`R0g00ilR11300#2f0R2#0'1X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma s_atop_set_bounce i v st : s_atop (set_bounce i v st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g01@7j11Tg00G1j20Tg00K`R0g00ilR1f0R2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma s_ctx_put_meta m r st : s_ctx (put_meta m r st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11rh22stp;1p;2g012Hj11Tg00G1j20Tg006:R0g00h?R1g00ilR2g013>f0R3#1'0X22X11X00f2f1P3O3W2W1W0o"). Qed.
Lemma s_regions_put_meta m r st : s_regions (put_meta m r st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11rh22stp;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg006:R0g00h?R1g00ilR2g00KBg00jeg00kWg014oC2f0R3#1'0X22X11X00f2f1P3O3W2W1W0o"). Qed.
Lemma s_shadow_put_meta m r st : s_shadow (put_meta m r st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11rh22stp;4p;1p;2g00Ebj42Tg015hj11Tg00G1j20Tg006:R0g00h?R1g00ilR2g00KBg00jeg00kWg016aC2f0R3#1'0X22X11X00f2f1P3O3W2W1W0o"). Qed.
Lemma s_next_rid_put_meta m r st : s_next_rid (put_meta m r st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11rh22stp;1p;2g017Zj11Tg00G1j20Tg006:R0g00h?R1g00ilR2g00KBf0R3#1'0X22X11X00f2f1P3O3W2W1W0o"). Qed.
Lemma s_areas_put_meta m r st : s_areas (put_meta m r st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11rh22stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg006:R0g00h?R1g00ilR2P0g00KBR3g00jeR4g00K`R5g00k>R6C4P3P4g00kWP5P6g00l5E3g019MC0f0R6#1'2X22X11X00f2f1P6O3W2W1W0o"). Qed.
Lemma s_groups_put_meta m r st : s_groups (put_meta m r st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11rh22stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg006:R0g00h?R1g00ilR2P0g00KBR3g00jeR4g00K`R5g00k>R6C4P3P4g00kWP5P6g00l5E3g01;=C0f0R6#1'2X22X11X00f2f1P6O3W2W1W0o"). Qed.
Lemma s_slots_put_meta m r st : s_slots (put_meta m r st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11rh22stp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<4j13Tg00G1j22Tg006:R0g00h?R1g00ilR2P0g00KBR3g00jeR4g00K`R5g00k>R6C5P3P4g00kWP5P6g00l5E41005C1f0R5#3'2X22X11X00f2f1P5O3W2W1W0o"). Qed.
Lemma s_tick_put_meta m r st : s_tick (put_meta m r st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11rh22stp;1p;2g01<lj11Tg00G1j20Tg006:R0g00h?R1g00ilR2g00KBf0R3#1'0X22X11X00f2f1P3O3W2W1W0o"). Qed.
Lemma s_secret_put_meta m r st : s_secret (put_meta m r st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11rh22stp;1p;2g01=cj11Tg00G1j20Tg006:R0g00h?R1g00ilR2g00K`f0R3#1'0X22X11X00f2f1P3O3W2W1W0o"). Qed.
Lemma s_reserved_put_meta m r st : s_reserved (put_meta m r st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11rh22stp;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg006:R0g00h?R1g00ilR2g00K`R3/33#2f0R3#0'1X22X11X00f2f1P3O3W2W1W0o"). Qed.
Lemma s_atop_put_meta m r st : s_atop (put_meta m r st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11rh22stp;1p;2g01@7j11Tg00G1j20Tg006:R0g00h?R1g00ilR2g00K`f0R3#1'0X22X11X00f2f1P3O3W2W1W0o"). Qed.
Lemma s_ctx_upd_meta m f st : s_ctx (upd_meta m f st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh11mh22stp;1p;2g012Hj11Tg00G1j20Tg006:R0g00h?R1P1[R1g00ilR2g013>f0R3#1'0X22X01X10f2f1P3O3W2W0W1o"). Qed.
Lemma s_regions_upd_meta m f st : s_regions (upd_meta m f st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh11mh22stp;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg006:R0g00h?R1P1[R1g00ilR2g00KBg00jeg00kWg014oC2f0R3#1'0X22X01X10f2f1P3O3W2W0W1o"). Qed.
Lemma s_shadow_upd_meta m f st : s_shadow (upd_meta m f st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh11mh22stp;4p;1p;2g00Ebj42Tg015hj11Tg00G1j20Tg006:R0g00h?R1P1[R1g00ilR2g00KBg00jeg00kWg016aC2f0R3#1'0X22X01X10f2f1P3O3W2W0W1o"). Qed.
Lemma s_next_rid_upd_meta m f st : s_next_rid (upd_meta m f st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh11mh22stp;1p;2g017Zj11Tg00G1j20Tg006:R0g00h?R1P1[R1g00ilR2g00KBf0R3#1'0X22X01X10f2f1P3O3W2W0W1o"). Qed.
Lemma s_areas_upd_meta m f st : s_areas (upd_meta m f st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh11mh22stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg006:R0g00h?R1P1[R1g00ilR2P0g00KBR3g00jeR4g00K`R5g00k>R6C4P3P4g00kWP5P6g00l5E3g019MC0f0R6#1'2X22X01X10f2f1P6O3W2W0W1o"). Qed.
Lemma s_groups_upd_meta m f st : s_groups (upd_meta m f st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh11mh22stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg006:R0g00h?R1P1[R1g00ilR2P0g00KBR3g00jeR4g00K`R5g00k>R6C4P3P4g00kWP5P6g00l5E3g01;=C0f0R6#1'2X22X01X10f2f1P6O3W2W0W1o"). Qed.
Lemma s_slots_upd_meta m f st : s_slots (upd_meta m f st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh11mh22stp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<4j13Tg00G1j22Tg006:R0g00h?R1P1[R1g00ilR2P0g00KBR3g00jeR4g00K`R5g00k>R6C5P3P4g00kWP5P6g00l5E41005C1f0R5#3'2X22X01X10f2f1P5O3W2W0W1o"). Qed.
Lemma s_tick_upd_meta m f st : s_tick (upd_meta m f st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh11mh22stp;1p;2g01<lj11Tg00G1j20Tg006:R0g00h?R1P1[R1g00ilR2g00KBf0R3#1'0X22X01X10f2f1P3O3W2W0W1o"). Qed.
Lemma s_secret_upd_meta m f st : s_secret (upd_meta m f st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh11mh22stp;1p;2g01=cj11Tg00G1j20Tg006:R0g00h?R1P1[R1g00ilR2g00K`f0R3#1'0X22X01X10f2f1P3O3W2W0W1o"). Qed.
Lemma s_reserved_upd_meta m f st : s_reserved (upd_meta m f st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh11mh22stp;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg006:R0g00h?R1P1[R1g00ilR2g00K`R3/33#2f0R3#0'1X22X01X10f2f1P3O3W2W0W1o"). Qed.
Lemma s_atop_upd_meta m f st : s_atop (upd_meta m f st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh11mh22stp;1p;2g01@7j11Tg00G1j20Tg006:R0g00h?R1P1[R1g00ilR2g00K`f0R3#1'0X22X01X10f2f1P3O3W2W0W1o"). Qed.
Lemma s_ctx_put_group g mo ai st : s_ctx (put_group g mo ai st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02aih11gh22moh32stp;1p;2g012Hj11Tg00G1j20Tg006:R0g00BLR1g00K`R2g00ilR3g013>f0R4#1'0X33X02X21X10f3f2f1P4O4W3W0W2W1o"). Qed.
Lemma s_regions_put_group g mo ai st : s_regions (put_group g mo ai st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02aih11gh22moh32stp;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg006:R0g00BLR1g00K`R2g00ilR3g00KBg00jeg00kWg014oC2f0R4#1'0X33X02X21X10f3f2f1P4O4W3W0W2W1o"). Qed.
Lemma s_shadow_put_group g mo ai st : s_shadow (put_group g mo ai st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02aih11gh22moh32stp;4p;1p;2g00Ebj42Tg015hj11Tg00G1j20Tg006:R0g00BLR1g00K`R2g00ilR3g00KBg00jeg00kWg016aC2f0R4#1'0X33X02X21X10f3f2f1P4O4W3W0W2W1o"). Qed.
Lemma s_next_rid_put_group g mo ai st : s_next_rid (put_group g mo ai st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02aih11gh22moh32stp;1p;2g017Zj11Tg00G1j20Tg006:R0g00BLR1g00K`R2g00ilR3g00KBf0R4#1'0X33X02X21X10f3f2f1P4O4W3W0W2W1o"). Qed.
Lemma s_metas_put_group g mo ai st : s_metas (put_group g mo ai st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02aih11gh22moh32stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg006:R0g00BLR1g00K`R2g00ilR3P0g00KBR4g00jeR5P2g00k>R6C4P4P5g00kWP2P6g00l5E3g00h?C0f0R6#1'2X33X02X21X10f3f2f1P6O4W3W0W2W1o"). Qed.
Lemma s_areas_put_group g mo ai st : s_areas (put_group g mo ai st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02aih11gh22moh32stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg006:R0g00BLR1g00K`R2g00ilR3P0g00KBR4g00jeR5P2g00k>R6C4P4P5g00kWP2P6g00l5E3g019MC0f0R6#1'2X33X02X21X10f3f2f1P6O4W3W0W2W1o"). Qed.
Lemma s_slots_put_group g mo ai st : s_slots (put_group g mo ai st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02aih11gh22moh32stp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<4j13Tg00G1j22Tg006:R0g00BLR1g00K`R2g00ilR3P0g00KBR4g00jeR5P2g00k>R6C5P4P5g00kWP2P6g00l5E41002C1f0R6#3'2X33X02X21X10f3f2f1P6O4W3W0W2W1o"). Qed.
Lemma s_tick_put_group g mo ai st : s_tick (put_group g mo ai st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02aih11gh22moh32stp;1p;2g01<lj11Tg00G1j20Tg006:R0g00BLR1g00K`R2g00ilR3g00KBf0R4#1'0X33X02X21X10f3f2f1P4O4W3W0W2W1o"). Qed.
Lemma s_secret_put_group g mo ai st : s_secret (put_group g mo ai st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02aih11gh22moh32stp;1p;2g01=cj11Tg00G1j20Tg006:R0g00BLR1g00K`R2g00ilR3f0R4#1,02X33X02X21X10f3f2f1P4O4W3W0W2W1o"). Qed.
Lemma s_reserved_put_group g mo ai st : s_reserved (put_group g mo ai st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02aih11gh22moh32stp;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg006:R0g00BLR1g00K`R2g00ilR31322#2f0R4#0'1X33X02X21X10f3f2f1P4O4W3W0W2W1o"). Qed.
Lemma s_atop_put_group g mo ai st : s_atop (put_group g mo ai st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02aih11gh22moh32stp;1p;2g01@7j11Tg00G1j20Tg006:R0g00BLR1g00K`R2g00ilR3f0R4#1,02X33X02X21X10f3f2f1P4O4W3W0W2W1o"). Qed.
Lemma s_ctx_del_group g st : s_ctx (del_group g st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01gh12stp;1p;2g012Hj11Tg00G1j20Tg006:R0g00ilR1g013>f0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_regions_del_group g st : s_regions (del_group g st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01gh12stp;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg006:R0g00ilR1g00KBg00jeg00kWg014oC2f0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_shadow_del_group g st : s_shadow (del_group g st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01gh12stp;4p;1p;2g00Ebj42Tg015hj11Tg00G1j20Tg006:R0g00ilR1g00KBg00jeg00kWg016aC2f0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_next_rid_del_group g st : s_next_rid (del_group g st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01gh12stp;1p;2g017Zj11Tg00G1j20Tg006:R0g00ilR1g00KBf0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_metas_del_group g st : s_metas (del_group g st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01gh12stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg006:R0g00ilR1P0g00KBR2g00jeR3g00K`R4g00k>R5C4P2P3g00kWP4P5g00l5E3g00h?C0f0R5#1'2X11X00f1P5O2W1W0o"). Qed.
Lemma s_areas_del_group g st : s_areas (del_group g st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01gh12stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg006:R0g00ilR1P0g00KBR2g00jeR3g00K`R4g00k>R5C4P2P3g00kWP4P5g00l5E3g019MC0f0R5#1'2X11X00f1P5O2W1W0o"). Qed.
Lemma s_slots_del_group g st : s_slots (del_group g st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01gh12stp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<4j13Tg00G1j22Tg006:R0g00ilR1P0g00KBR2g00jeR3g00K`R4g00k>R5C5P2P3g00kWP4P5g00l5E41004C1f0R4#3'2X11X00f1P4O2W1W0o"). Qed.
Lemma s_tick_del_group g st : s_tick (del_group g st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01gh12stp;1p;2g01<lj11Tg00G1j20Tg006:R0g00ilR1g00KBf0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_secret_del_group g st : s_secret (del_group g st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01gh12stp;1p;2g01=cj11Tg00G1j20Tg006:R0g00ilR1g00K`f0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_reserved_del_group g st : s_reserved (del_group g st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01gh12stp;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg006:R0g00ilR1g00K`R2/32#2f0R2#0'1X11X00f1P2O2W1W0o"). Qed.
Lemma s_atop_del_group g st : s_atop (del_group g st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01gh12stp;1p;2g01@7j11Tg00G1j20Tg006:R0g00ilR1g00K`f0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_ctx_set_group_active_idx g ai st : s_ctx (set_group_active_idx g ai st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02aih11gi001gh22sth32g0h41oi011oi021hi031xp;2p;1p;4p;6p;7p;3g01RAj2BTg00_9R0j1ATg00b9j46Tg00bWj64Tg00Ebj4@Tg00<Xj4<Tg00:<j4;Tg01S;j15Tg01T2j11Tg01TWj17Tg01U5j28Tg01USj29Tg01:Dj1:Tg00g<j7?Tg01VJj2=Tg012Hj10Tg006oj32Tg00G1j23Tg01WEj3>Tg006:R1g00K`R2g00ilR3f0R4f2R5'Bg01;=R6#AP0P6g013>R7P0P6P3P4P1P6P1g00KBR0g00jeR8P2g00k>R9C6R:P0P8g00kWP2P9g00l5E4R9P6C@R8P1P6P8P1P:P9P6C<C;f5%54f4g01XJ#1#1#1#1#7'8'9f3R9#:F?/=9P5n10110300021010200#0%0532P4%09,37X36P4O1f1R6#0,37n10110100021010000b4A>564#0%04527eX23X02X11P5P6P4O3W2W0W1o"). Qed.
Lemma s_regions_set_group_active_idx g ai st : s_regions (set_group_active_idx g ai st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02aih11gi001gh22sth32g0h41oi011oi021hi031xp;2p;1p;4p;6p;7p;3g01RAj2BTg00_9R0j1ATg00Ebj42Tg00b9j45Tg00bWj6@Tg00<Xj4<Tg00:<j4;Tg01S;j16Tg01T2j11Tg01TWj17Tg01U5j28Tg01USj29Tg01:Dj1:Tg00g<j7?Tg01VJj2=Tg0145j10Tg006oj33Tg00G1j24Tg01WEj3>Tg006:R1g00K`R2g00ilR3f0R4f2R5'Bg01;=R6#AP0P6g00KBR7g00jeR8g00kWR9g014oC2R:P0P6P3P4P1P6P1P7P8P2g00k>R0C5R;P7P8P9P2P0g00l5E@R0P6C2R9P1P6P9P1P;P0P6C<C;f5%64f4g01XJ#1#1#1#1#7'8'9f3R0#:F?/=0P5n10110300021010200#0%0533P4%00,4:X36P4O1f1R6#0,4:n10110100021010000b4A>564#0%0453:eX23X02X11P5P6P4O3W2W0W1o"). Qed.
Lemma s_shadow_set_group_active_idx g ai st : s_shadow (set_group_active_idx g ai st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02aih11gi001gh22sth32g0h41oi011oi021hi031xp;2p;1p;4p;6p;7p;3g01RAj2BTg00_9R0j1ATg00Ebj42Tg00b9j45Tg00bWj6@Tg00<Xj4<Tg00:<j4;Tg01S;j16Tg01T2j11Tg01TWj17Tg01U5j28Tg01USj29Tg01:Dj1:Tg00g<j7?Tg01VJj2=Tg015hj10Tg006oj33Tg00G1j24Tg01WEj3>Tg006:R1g00K`R2g00ilR3f0R4f2R5'Bg01;=R6#AP0P6g00KBR7g00jeR8g00kWR9g016aC2R:P0P6P3P4P1P6P1P7P8P2g00k>R0C5R;P7P8P9P2P0g00l5E@R0P6C2R9P1P6P9P1P;P0P6C<C;f5%64f4g01XJ#1#1#1#1#7'8'9f3R0#:F?/=0P5n10110300021010200#0%0533P4%00,4:X36P4O1f1R6#0,4:n10110100021010000b4A>564#0%0453:eX23X02X11P5P6P4O3W2W0W1o"). Qed.
Lemma s_next_rid_set_group_active_idx g ai st : s_next_rid (set_group_active_idx g ai st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02aih11gi001gh22sth32g0h41oi011oi021hi031xp;2p;1p;4p;6p;7p;3g01RAj2BTg00_9R0j1ATg00b9j46Tg00bWj64Tg00Ebj4@Tg00<Xj4<Tg00:<j4;Tg01S;j15Tg01T2j11Tg01TWj17Tg01U5j28Tg01USj29Tg01:Dj1:Tg00g<j7?Tg01VJj2=Tg017Zj10Tg006oj32Tg00G1j23Tg01WEj3>Tg006:R1g00K`R2g00ilR3f0R4f2R5'Bg01;=R6#AP0P6g00KBR7P0P6P3P4P1P6P1P7g00jeR0P2g00k>R8C6R9P7P0g00kWP2P8g00l5E4R8P6C@R0P1P6P0P1P9P8P6C<C;f5%54f4g01XJ#1#1#1#1#7'8'9f3R8#:F?/=8P5n10110300021010200#0%0532P4%08,37X36P4O1f1R6#0,37n10110100021010000b4A>564#0%04527eX23X02X11P5P6P4O3W2W0W1o"). Qed.
Lemma s_metas_set_group_active_idx g ai st : s_metas (set_group_active_idx g ai st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02aih11gi001gh22sth32g0h41oi011oi021hi031xp;2p;1p;4p;6p;7p;3g01RAj2BTg00_9R0j1ATg00b9j4;Tg00bWj65Tg00Ebj44Tg00<Xj4=Tg00:<j4<Tg01S;j1:Tg01T2j11Tg01TWj16Tg01U5j27Tg01USj28Tg01:Dj19Tg00g<j7@Tg01VJj2?Tg00c8j10Tg006oj33Tg00G1j22Tg01WEj3>Tg006:R1g00K`R2g00ilR3f0R4f2R5'Bg01;=R6#AP0P6P1g00KBR7g00jeR8P2g00k>R9C;R:P7P8g00kWP2P9g00l5E5R9g00h?C4R8P0P6P3P4P1P6P1P:P9P6C4R0P1P6P0P1P:P9P6C=C<f5%:4f4g01XJ#1#1#1#1#6'7'8f3R9#9F@/?9P5n10110300021010200#0%0533P4%09,28X36P4O1f1R6#0,28n10110100021010000b4A>564#0%04538eX23X02X11P5P6P4O3W2W0W1o"). Qed.
Lemma s_areas_set_group_active_idx g ai st : s_areas (set_group_active_idx g ai st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02aih11gi001gh22sth32g0h41oi011oi021hi031xp;2p;1p;4p;6p;7p;3g01RAj2BTg00_9R0j1ATg00b9j4;Tg00bWj65Tg00Ebj44Tg00<Xj4=Tg00:<j4<Tg01S;j1:Tg01T2j11Tg01TWj16Tg01U5j27Tg01USj28Tg01:Dj19Tg00g<j7@Tg01VJj2?Tg018Uj10Tg006oj33Tg00G1j22Tg01WEj3>Tg006:R1g00K`R2g00ilR3f0R4f2R5'Bg01;=R6#AP0P6P1g00KBR7g00jeR8P2g00k>R9C;R:P7P8g00kWP2P9g00l5E5R9g019MC4R8P0P6P3P4P1P6P1P:P9P6C4R0P1P6P0P1P:P9P6C=C<f5%:4f4g01XJ#1#1#1#1#6'7'8f3R9#9F@/?9P5n10110300021010200#0%0533P4%09,28X36P4O1f1R6#0,28n10110100021010000b4A>564#0%04538eX23X02X11P5P6P4O3W2W0W1o"). Qed.
Lemma s_slots_set_group_active_idx g ai st : s_slots (set_group_active_idx g ai st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02aih11gi001gh22sth32g0h41oi011oi021hi031xp;2p;1p;4p;6p;7p;3g01RAj2CTg00_9R0j1BTg00b9j4;Tg00bWj65Tg00Ubj2ATg00Ebj43Tg00<Xj4<Tg00:<j4:Tg01S;j16Tg01T2j11Tg01TWj17Tg01U5j28Tg01USj29Tg01:Dj1@Tg00g<j7>Tg01VJj2=Tg01<4j10Tg006oj32Tg00G1j24Tg01WEj3?Tg006:R1g00K`R2g00ilR3f0R4f2R5'Cg01;=R6#BP0P6P1g00KBR7g00jeR8P2g00k>R9C;R:P7P8g00kWP2P9g00l5E5R91A12C3R8P0P6P3P4P1P6P1P:P9P6C3R0P1P6P0P1P:P9P6C<C:f5%64f4g01XJ#1#1#1#1#7'8'9f3R9#@F>/=9P5n10110300021010200#0%0532P4%09,48X36P4O1f1R6#0,48n10110100021010000b4A?564#0%04528eX23X02X11P5P6P4O3W2W0W1o"). Qed.
Lemma s_tick_set_group_active_idx g ai st : s_tick (set_group_active_idx g ai st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02aih11gi001gh22sth32g0h41oi011oi021hi031xp;2p;1p;4p;6p;7p;3g01RAj2BTg00_9R0j1ATg00b9j46Tg00bWj64Tg00Ebj4@Tg00<Xj4<Tg00:<j4;Tg01S;j15Tg01T2j11Tg01TWj17Tg01U5j28Tg01USj29Tg01:Dj1:Tg00g<j7?Tg01VJj2=Tg01<lj10Tg006oj32Tg00G1j23Tg01WEj3>Tg006:R1g00K`R2g00ilR3f0R4f2R5'Bg01;=R6#AP0P6g00KBR7P0P6P3P4P1P6P1P7g00jeR0P2g00k>R8C6R9P7P0g00kWP2P8g00l5E4R8P6C@R0P1P6P0P1P9P8P6C<C;f5%54f4g01XJ#1#1#1#1#7'8'9f3R8#:F?/=8P5n10110300021010200#0%0532P4%08,37X36P4O1f1R6#0,37n10110100021010000b4A>564#0%04527eX23X02X11P5P6P4O3W2W0W1o"). Qed.
Lemma s_secret_set_group_active_idx g ai st : s_secret (set_group_active_idx g ai st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02aih11gi001gh22sth32g0h41oi011oi021hi031xp;2p;1p;4p;6p;7p;3g01RAj2BTg00_9R0j1ATg00b9j46Tg00bWj64Tg00Ebj4@Tg00<Xj4<Tg00:<j4;Tg01S;j15Tg01T2j11Tg01TWj17Tg01U5j28Tg01USj29Tg01:Dj1:Tg00g<j7?Tg01VJj2=Tg01=cj10Tg006oj32Tg00G1j23Tg01WEj3>Tg006:R1g00K`R2g00ilR3f0R4f2R5'Bg01;=R6#AP0P6P0P6P3P4P1P6P1g00KBR0g00jeR7P2g00k>R8C6R9P0P7g00kWP2P8g00l5E4R8P6C@R7P1P6P7P1P9P8P6C<C;f5%54f4g01XJ#1#1#1#1#7'8'9f3R8#:F?/=8P5n10110300021010200#0%05522P4%08,32X36P4O1f1R6#0,32n10110100021010000b4A>564#0%04522eX23X02X11P5P6P4O3W2W0W1o"). Qed.
Lemma s_reserved_set_group_active_idx g ai st : s_reserved (set_group_active_idx g ai st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02aih11gi001gh22sth32g0h41oi011oi021hi031xp;2p;1p;4p;6p;7p;3g01RAj2DTg00_9R0j1CTg00Ubj28Tg01>\j14Tg00b9j4BTg00bWj6<Tg00Ebj4;Tg00<Xj47Tg00:<j45Tg01S;j16Tg01T2j11Tg01TWj19Tg01U5j2:Tg01USj2ATg01:Dj1?Tg00g<j7>Tg01VJj2=Tg01?<j10Tg006oj32Tg00G1j23Tg01WEj3@Tg006:R1g00K`R2g00ilR3f0R4f2R5'Dg01;=R6#CP0P61822#4R7P0P6P3P4P1P6P1g00KBR0g00jeR8P2g00k>R9CBR:P0P8g00kWP2P9g00l5E<R9P6C;R8P1P6P8P1P:P9P6C7C5f5%64f4g01XJ#1#1#1#1#9':'Af3R9#?F>/=9P5n10110300021010200#0%0532P4%09,37X36P4O1f1R6#0,37n10110100021010000b4A@564#0%04527eX23X02X11P5P6P4O3W2W0W1o"). Qed.
Lemma s_atop_set_group_active_idx g ai st : s_atop (set_group_active_idx g ai st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02aih11gi001gh22sth32g0h41oi011oi021hi031xp;2p;1p;4p;6p;7p;3g01RAj2BTg00_9R0j1ATg00b9j46Tg00bWj64Tg00Ebj4@Tg00<Xj4<Tg00:<j4;Tg01S;j15Tg01T2j11Tg01TWj17Tg01U5j28Tg01USj29Tg01:Dj1:Tg00g<j7?Tg01VJj2=Tg01@7j10Tg006oj32Tg00G1j23Tg01WEj3>Tg006:R1g00K`R2g00ilR3f0R4f2R5'Bg01;=R6#AP0P6P0P6P3P4P1P6P1g00KBR0g00jeR7P2g00k>R8C6R9P0P7g00kWP2P8g00l5E4R8P6C@R7P1P6P7P1P9P8P6C<C;f5%54f4g01XJ#1#1#1#1#7'8'9f3R8#:F?/=8P5n10110300021010200#0%05522P4%08,32X36P4O1f1R6#0,32n10110100021010000b4A>564#0%04522eX23X02X11P5P6P4O3W2W0W1o"). Qed.
Lemma s_ctx_drop_region rid st : s_ctx (drop_region rid st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03ridh12stp;1p;2g012Hj11Tg00G1j20Tg00KBR0g00ilR1g013>f0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_next_rid_drop_region rid st : s_next_rid (drop_region rid st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03ridh12stp;1p;2g017Zj11Tg00G1j20Tg00KBR0g00ilR1f0R2#1,00X11X00f1P2O2W1W0o"). Qed.
Lemma s_metas_drop_region rid st : s_metas (drop_region rid st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03ridh12stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg00KBR0g00ilR1g006:P0g00jeR2g00K`R3g00k>R4C4P0P2g00kWP3P4g00l5E3g00h?C0f0R4#1'2X11X00f1P4O2W1W0o"). Qed.
Lemma s_areas_drop_region rid st : s_areas (drop_region rid st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03ridh12stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg00KBR0g00ilR1g006:P0g00jeR2g00K`R3g00k>R4C4P0P2g00kWP3P4g00l5E3g019MC0f0R4#1'2X11X00f1P4O2W1W0o"). Qed.
Lemma s_groups_drop_region rid st : s_groups (drop_region rid st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03ridh12stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg00KBR0g00ilR1g006:P0g00jeR2g00K`R3g00k>R4C4P0P2g00kWP3P4g00l5E3g01;=C0f0R4#1'2X11X00f1P4O2W1W0o"). Qed.
Lemma s_slots_drop_region rid st : s_slots (drop_region rid st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03ridh12stp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<4j13Tg00G1j22Tg00KBR0g00ilR1g006:R2P0g00jeR3g00K`R4g00k>R5C5P0P3g00kWP4P5g00l5E41024C1f0R4#3'2X11X00f1P4O2W1W0o"). Qed.
Lemma s_tick_drop_region rid st : s_tick (drop_region rid st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03ridh12stp;1p;2g01<lj11Tg00G1j20Tg00KBR0g00ilR1f0R2#1,00X11X00f1P2O2W1W0o"). Qed.
Lemma s_secret_drop_region rid st : s_secret (drop_region rid st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03ridh12stp;1p;2g01=cj11Tg00G1j20Tg00KBR0g00ilR1g00K`f0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_reserved_drop_region rid st : s_reserved (drop_region rid st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03ridh12stp;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg00KBR0g00ilR1g00K`R2/32#2f0R2#0'1X11X00f1P2O2W1W0o"). Qed.
Lemma s_atop_drop_region rid st : s_atop (drop_region rid st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03ridh12stp;1p;2g01@7j11Tg00G1j20Tg00KBR0g00ilR1g00K`f0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_ctx_upd_region rid f st : s_ctx (upd_region rid f st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01fh13ridh22sth31oi001oh41ri011ri021xp;2p;1p;4p;7p;3g01Xoj2;Tg00_9R0j1:Tg00Ebj44Tg00<Xj43Tg00:<j49Tg0145j17Tg00g<j76Tg01Yjj25Tg012Hj10Tg006oj31Tg00G1j22Tg01Zfj38Tg00KBR1g014oR2P2[R3g00ilR4f0R5f2R6';%:2P0P2g013>R7P0P2P4P5P1P2P1g00jeR0g00kWR8P2C4R9P1P2P9P1P0P8P2C3C9f5f4P5O1f3R8#7F6/58P6n10110200021010100#0%0631P5%08,27X42P5O1f1R2#0,27n10110000021010100b3A8625#0%05517eX24X03X11P6P2P5O3W2W0W1o"). Qed.
Lemma s_shadow_upd_region rid f st : s_shadow (upd_region rid f st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01fh13ridh22sth31oi001oh41ri011ri021xp;2p;1p;4p;7p;3g01Xoj2;Tg00_9R0j1:Tg00Ebj42Tg00<Xj44Tg00:<j49Tg0145j17Tg00g<j76Tg01Yjj25Tg015hj10Tg006oj31Tg00G1j23Tg01Zfj38Tg00KBR1g014oR2P2[R3g00ilR4f0R5f2R6';%:2P0P2P1g00jeR7g00kWR8g016aC2R9P0P2P4P5P1P2P1P7P8P2C2R0P1P2P0P1P7P8P2C4C9f5f4P5O1f3R8#7F6/58P6n10110200021010100#0%0631P5%08,39X42P5O1f1R2#0,39n10110000021010100b3A8625#0%05519eX24X03X11P6P2P5O3W2W0W1o"). Qed.
Lemma s_next_rid_upd_region rid f st : s_next_rid (upd_region rid f st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01fh13ridh22sth31oi001oh41ri011ri021xp;2p;1p;4p;7p;3g01Xoj2;Tg00_9R0j1:Tg00Ebj44Tg00<Xj43Tg00:<j49Tg0145j17Tg00g<j76Tg01Yjj25Tg017Zj10Tg006oj31Tg00G1j22Tg01Zfj38Tg00KBR1g014oR2P2[R3g00ilR4f0R5f2R6';%:2P0P2P0P2P4P5P1P2P1g00jeR0g00kWR7P2C4R8P1P2P8P1P0P7P2C3C9f5f4P5O1f3R7#7F6/57P6n10110200021010100#0%06511P5%07,21X42P5O1f1R2#0,21n10110000021010100b3A8625#0%05511eX24X03X11P6P2P5O3W2W0W1o"). Qed.
Lemma s_metas_upd_region rid f st : s_metas (upd_region rid f st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01fh13ridh22sth31oi001oh41ri011ri021xp;2p;1p;4p;6p;7p;3g01Xoj2=Tg00_9R0j1<Tg00b9j48Tg00bWj64Tg00Ebj43Tg00<Xj4:Tg00:<j49Tg0145j17Tg00g<j75Tg01Yjj26Tg00c8j10Tg006oj32Tg00G1j21Tg01Zfj3;Tg00KBR1g014oR2P2[R3g00ilR4f0R5f2R6'=%<2P0P2g006:P1g00jeR7g00K`R8g00k>R9C8P1P7g00kWR:P8P9g00l5E4g00h?C3R9P0P2P4P5P1P2P1P7P:P2C3R0P1P2P0P1P7P:P2C:C9f5f4P5O1f3R:#7F5/6:P6n10110200021010100#0%0632P5%0:,19X42P5O1f1R2#0,19n10110000021010100b3A;625#0%05529eX24X03X11P6P2P5O3W2W0W1o"). Qed.
Lemma s_areas_upd_region rid f st : s_areas (upd_region rid f st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01fh13ridh22sth31oi001oh41ri011ri021xp;2p;1p;4p;6p;7p;3g01Xoj2=Tg00_9R0j1<Tg00b9j48Tg00bWj64Tg00Ebj43Tg00<Xj4:Tg00:<j49Tg0145j17Tg00g<j75Tg01Yjj26Tg018Uj10Tg006oj32Tg00G1j21Tg01Zfj3;Tg00KBR1g014oR2P2[R3g00ilR4f0R5f2R6'=%<2P0P2g006:P1g00jeR7g00K`R8g00k>R9C8P1P7g00kWR:P8P9g00l5E4g019MC3R9P0P2P4P5P1P2P1P7P:P2C3R0P1P2P0P1P7P:P2C:C9f5f4P5O1f3R:#7F5/6:P6n10110200021010100#0%0632P5%0:,19X42P5O1f1R2#0,19n10110000021010100b3A;625#0%05529eX24X03X11P6P2P5O3W2W0W1o"). Qed.
Lemma s_groups_upd_region rid f st : s_groups (upd_region rid f st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01fh13ridh22sth31oi001oh41ri011ri021xp;2p;1p;4p;6p;7p;3g01Xoj2=Tg00_9R0j1<Tg00b9j48Tg00bWj64Tg00Ebj43Tg00<Xj4:Tg00:<j49Tg0145j17Tg00g<j75Tg01Yjj26Tg01:Dj10Tg006oj32Tg00G1j21Tg01Zfj3;Tg00KBR1g014oR2P2[R3g00ilR4f0R5f2R6'=%<2P0P2g006:P1g00jeR7g00K`R8g00k>R9C8P1P7g00kWR:P8P9g00l5E4g01;=C3R9P0P2P4P5P1P2P1P7P:P2C3R0P1P2P0P1P7P:P2C:C9f5f4P5O1f3R:#7F5/6:P6n10110200021010100#0%0632P5%0:,19X42P5O1f1R2#0,19n10110000021010100b3A;625#0%05529eX24X03X11P6P2P5O3W2W0W1o"). Qed.
Lemma s_slots_upd_region rid f st : s_slots (upd_region rid f st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01fh13ridh22sth31oi001oh41ri011ri021xp;2p;1p;4p;6p;7p;3g01Xoj2>Tg00_9R0j1=Tg00b9j49Tg00bWj64Tg00Ubj2<Tg00Ebj41Tg00<Xj4:Tg00:<j48Tg0145j15Tg00g<j76Tg01Yjj27Tg01<4j10Tg006oj32Tg00G1j23Tg01Zfj3;Tg00KBR1g014oR2P2[R3g00ilR4f0R5f2R6'>%=2P0P2g006:R7P1g00jeR8g00K`R9g00k>R:C9P1P8g00kWR;P9P:g00l5E41<79C1R9P0P2P4P5P1P2P1P8P;P2C1R0P1P2P0P1P8P;P2C:C8f5f4P5O1f3R;#5F6/7;P6n10110200021010100#0%0632P5%0;,39X42P5O1f1R2#0,39n10110000021010100b3A;625#0%05529eX24X03X11P6P2P5O3W2W0W1o"). Qed.
Lemma s_tick_upd_region rid f st : s_tick (upd_region rid f st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01fh13ridh22sth31oi001oh41ri011ri021xp;2p;1p;4p;7p;3g01Xoj2;Tg00_9R0j1:Tg00Ebj44Tg00<Xj43Tg00:<j49Tg0145j17Tg00g<j76Tg01Yjj25Tg01<lj10Tg006oj31Tg00G1j22Tg01Zfj38Tg00KBR1g014oR2P2[R3g00ilR4f0R5f2R6';%:2P0P2P0P2P4P5P1P2P1g00jeR0g00kWR7P2C4R8P1P2P8P1P0P7P2C3C9f5f4P5O1f3R7#7F6/57P6n10110200021010100#0%06511P5%07,21X42P5O1f1R2#0,21n10110000021010100b3A8625#0%05511eX24X03X11P6P2P5O3W2W0W1o"). Qed.
Lemma s_secret_upd_region rid f st : s_secret (upd_region rid f st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01fh13ridh22sth31oi001oh41ri011ri021xp;2p;1p;4p;7p;3g01Xoj2;Tg00_9R0j1:Tg00Ebj44Tg00<Xj43Tg00:<j49Tg0145j17Tg00g<j76Tg01Yjj25Tg01=cj10Tg006oj31Tg00G1j22Tg01Zfj38Tg00KBR1g014oR2P2[R3g00ilR4f0R5f2R6';%:2P0P2g00K`R7P0P2P4P5P1P2P1g00jeR0g00kWR8P2C4R9P1P2P9P1P0P8P2C3C9f5f4P5O1f3R8#7F6/58P6n10110200021010100#0%0631P5%08,27X42P5O1f1R2#0,27n10110000021010100b3A8625#0%05517eX24X03X11P6P2P5O3W2W0W1o"). Qed.
Lemma s_reserved_upd_region rid f st : s_reserved (upd_region rid f st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01fh13ridh22sth31oi001oh41ri011ri021xp;2p;1p;4p;7p;3g01Xoj2=Tg00_9R0j1<Tg00Ubj24Tg01>\j13Tg00Ebj4;Tg00<Xj49Tg00:<j48Tg0145j15Tg00g<j76Tg01Yjj27Tg01?<j10Tg006oj31Tg00G1j22Tg01Zfj3:Tg00KBR1g014oR2P2[R3g00ilR4f0R5f2R6'=%<2P0P2g00K`R7/47#3R7P0P2P4P5P1P2P1g00jeR0g00kWR8P2C;R9P1P2P9P1P0P8P2C9C8f5f4P5O1f3R8#5F6/78P6n10110200021010100#0%0631P5%08,27X42P5O1f1R2#0,27n10110000021010100b3A:625#0%05517eX24X03X11P6P2P5O3W2W0W1o"). Qed.
Lemma s_atop_upd_region rid f st : s_atop (upd_region rid f st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01fh13ridh22sth31oi001oh41ri011ri021xp;2p;1p;4p;7p;3g01Xoj2;Tg00_9R0j1:Tg00Ebj44Tg00<Xj43Tg00:<j49Tg0145j17Tg00g<j76Tg01Yjj25Tg01@7j10Tg006oj31Tg00G1j22Tg01Zfj38Tg00KBR1g014oR2P2[R3g00ilR4f0R5f2R6';%:2P0P2g00K`R7P0P2P4P5P1P2P1g00jeR0g00kWR8P2C4R9P1P2P9P1P0P8P2C3C9f5f4P5O1f3R8#7F6/58P6n10110200021010100#0%0631P5%08,27X42P5O1f1R2#0,27n10110000021010100b3A8625#0%05517eX24X03X11P6P2P5O3W2W0W1o"). Qed.
Lemma s_ctx_add_slots m p stride cnt st : s_ctx (add_slots m p stride cnt st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11mh21ph32sth46stridep;1p;2g012Hj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g013>f0R3#1'0X32X01X41X20X10f4f3f2f1P3O5W3X01W4X20W1o"). Qed.
Lemma s_regions_add_slots m p stride cnt st : s_regions (add_slots m p stride cnt st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11mh21ph32sth46stridep;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBg00jeg00kWg014oC2f0R3#1'0X32X01X41X20X10f4f3f2f1P3O5W3X01W4X20W1o"). Qed.
Lemma s_shadow_add_slots m p stride cnt st : s_shadow (add_slots m p stride cnt st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11mh21ph32sth46stridep;4p;1p;2g00Ebj42Tg015hj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBg00jeg00kWg016aC2f0R3#1'0X32X01X41X20X10f4f3f2f1P3O5W3X01W4X20W1o"). Qed.
Lemma s_next_rid_add_slots m p stride cnt st : s_next_rid (add_slots m p stride cnt st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11mh21ph32sth46stridep;1p;2g017Zj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBf0R3#1'0X32X01X41X20X10f4f3f2f1P3O5W3X01W4X20W1o"). Qed.
Lemma s_metas_add_slots m p stride cnt st : s_metas (add_slots m p stride cnt st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11mh21ph32sth46stridep;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C4P3P4g00kWP1P5g00l5E3g00h?C0f0R5#1'2X32X01X41X20X10f4f3f2f1P5O5W3X01W4X20W1o"). Qed.
Lemma s_areas_add_slots m p stride cnt st : s_areas (add_slots m p stride cnt st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11mh21ph32sth46stridep;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C4P3P4g00kWP1P5g00l5E3g019MC0f0R5#1'2X32X01X41X20X10f4f3f2f1P5O5W3X01W4X20W1o"). Qed.
Lemma s_groups_add_slots m p stride cnt st : s_groups (add_slots m p stride cnt st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11mh21ph32sth46stridep;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C4P3P4g00kWP1P5g00l5E3g01;=C0f0R5#1'2X32X01X41X20X10f4f3f2f1P5O5W3X01W4X20W1o"). Qed.
Lemma s_tick_add_slots m p stride cnt st : s_tick (add_slots m p stride cnt st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11mh21ph32sth46stridep;1p;2g01<lj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBf0R3#1'0X32X01X41X20X10f4f3f2f1P3O5W3X01W4X20W1o"). Qed.
Lemma s_secret_add_slots m p stride cnt st : s_secret (add_slots m p stride cnt st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11mh21ph32sth46stridep;1p;2g01=cj11Tg00G1j20Tg006:R0g00K`R1g00ilR2f0R3#1,01X32X01X41X20X10f4f3f2f1P3O5W3X01W4X20W1o"). Qed.
Lemma s_reserved_add_slots m p stride cnt st : s_reserved (add_slots m p stride cnt st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11mh21ph32sth46stridep;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg006:R0g00K`R1g00ilR21311#2f0R3#0'1X32X01X41X20X10f4f3f2f1P3O5W3X01W4X20W1o"). Qed.
Lemma s_atop_add_slots m p stride cnt st : s_atop (add_slots m p stride cnt st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11mh21ph32sth46stridep;1p;2g01@7j11Tg00G1j20Tg006:R0g00K`R1g00ilR2f0R3#1,01X32X01X41X20X10f4f3f2f1P3O5W3X01W4X20W1o"). Qed.
Lemma s_ctx_del_slots p stride cnt st : s_ctx (del_slots p stride cnt st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11ph22sth36stridep;1p;2g012Hj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g013>f0R3#1'0X22X01X31X10f3f2f1P3O4W2X01W3W1o"). Qed.
Lemma s_regions_del_slots p stride cnt st : s_regions (del_slots p stride cnt st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11ph22sth36stridep;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBg00jeg00kWg014oC2f0R3#1'0X22X01X31X10f3f2f1P3O4W2X01W3W1o"). Qed.
Lemma s_shadow_del_slots p stride cnt st : s_shadow (del_slots p stride cnt st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11ph22sth36stridep;4p;1p;2g00Ebj42Tg015hj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBg00jeg00kWg016aC2f0R3#1'0X22X01X31X10f3f2f1P3O4W2X01W3W1o"). Qed.
Lemma s_next_rid_del_slots p stride cnt st : s_next_rid (del_slots p stride cnt st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11ph22sth36stridep;1p;2g017Zj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBf0R3#1'0X22X01X31X10f3f2f1P3O4W2X01W3W1o"). Qed.
Lemma s_metas_del_slots p stride cnt st : s_metas (del_slots p stride cnt st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11ph22sth36stridep;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C4P3P4g00kWP1P5g00l5E3g00h?C0f0R5#1'2X22X01X31X10f3f2f1P5O4W2X01W3W1o"). Qed.
Lemma s_areas_del_slots p stride cnt st : s_areas (del_slots p stride cnt st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11ph22sth36stridep;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C4P3P4g00kWP1P5g00l5E3g019MC0f0R5#1'2X22X01X31X10f3f2f1P5O4W2X01W3W1o"). Qed.
Lemma s_groups_del_slots p stride cnt st : s_groups (del_slots p stride cnt st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11ph22sth36stridep;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C4P3P4g00kWP1P5g00l5E3g01;=C0f0R5#1'2X22X01X31X10f3f2f1P5O4W2X01W3W1o"). Qed.
Lemma s_tick_del_slots p stride cnt st : s_tick (del_slots p stride cnt st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11ph22sth36stridep;1p;2g01<lj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBf0R3#1'0X22X01X31X10f3f2f1P3O4W2X01W3W1o"). Qed.
Lemma s_secret_del_slots p stride cnt st : s_secret (del_slots p stride cnt st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11ph22sth36stridep;1p;2g01=cj11Tg00G1j20Tg006:R0g00K`R1g00ilR2f0R3#1,01X22X01X31X10f3f2f1P3O4W2X01W3W1o"). Qed.
Lemma s_reserved_del_slots p stride cnt st : s_reserved (del_slots p stride cnt st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11ph22sth36stridep;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg006:R0g00K`R1g00ilR21311#2f0R3#0'1X22X01X31X10f3f2f1P3O4W2X01W3W1o"). Qed.
Lemma s_atop_del_slots p stride cnt st : s_atop (del_slots p stride cnt st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03cnth11ph22sth36stridep;1p;2g01@7j11Tg00G1j20Tg006:R0g00K`R1g00ilR2f0R3#1,01X22X01X31X10f3f2f1P3O4W2X01W3W1o"). Qed.
Lemma s_ctx_upd_shadow rid f st : s_ctx (upd_shadow rid f st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh13ridh22stp;1p;2g012Hj11Tg00G1j20Tg00KBR0g016aR1P1[R1g00ilR2g013>f0R3#1'0X22X01X10f2f1P3O3W2W0W1o"). Qed.
Lemma s_regions_upd_shadow rid f st : s_regions (upd_shadow rid f st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh13ridh22stp;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg00KBR0g016aR1P1[R1g00ilR2P0g00jeg00kWg014oC2f0R3#1'0X22X01X10f2f1P3O3W2W0W1o"). Qed.
Lemma s_next_rid_upd_shadow rid f st : s_next_rid (upd_shadow rid f st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh13ridh22stp;1p;2g017Zj11Tg00G1j20Tg00KBR0g016aR1P1[R1g00ilR2f0R3#1,00X22X01X10f2f1P3O3W2W0W1o"). Qed.
Lemma s_metas_upd_shadow rid f st : s_metas (upd_shadow rid f st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh13ridh22stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg00KBR0g016aR1P1[R1g00ilR2g006:P0g00jeR3g00K`R4g00k>R5C4P0P3g00kWP4P5g00l5E3g00h?C0f0R5#1'2X22X01X10f2f1P5O3W2W0W1o"). Qed.
Lemma s_areas_upd_shadow rid f st : s_areas (upd_shadow rid f st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh13ridh22stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg00KBR0g016aR1P1[R1g00ilR2g006:P0g00jeR3g00K`R4g00k>R5C4P0P3g00kWP4P5g00l5E3g019MC0f0R5#1'2X22X01X10f2f1P5O3W2W0W1o"). Qed.
Lemma s_groups_upd_shadow rid f st : s_groups (upd_shadow rid f st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh13ridh22stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg00KBR0g016aR1P1[R1g00ilR2g006:P0g00jeR3g00K`R4g00k>R5C4P0P3g00kWP4P5g00l5E3g01;=C0f0R5#1'2X22X01X10f2f1P5O3W2W0W1o"). Qed.
Lemma s_slots_upd_shadow rid f st : s_slots (upd_shadow rid f st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh13ridh22stp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<4j13Tg00G1j22Tg00KBR0g016aR1P1[R1g00ilR2g006:R3P0g00jeR4g00K`R5g00k>R6C5P0P4g00kWP5P6g00l5E41035C1f0R5#3'2X22X01X10f2f1P5O3W2W0W1o"). Qed.
Lemma s_tick_upd_shadow rid f st : s_tick (upd_shadow rid f st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh13ridh22stp;1p;2g01<lj11Tg00G1j20Tg00KBR0g016aR1P1[R1g00ilR2f0R3#1,00X22X01X10f2f1P3O3W2W0W1o"). Qed.
Lemma s_secret_upd_shadow rid f st : s_secret (upd_shadow rid f st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh13ridh22stp;1p;2g01=cj11Tg00G1j20Tg00KBR0g016aR1P1[R1g00ilR2g00K`f0R3#1'0X22X01X10f2f1P3O3W2W0W1o"). Qed.
Lemma s_reserved_upd_shadow rid f st : s_reserved (upd_shadow rid f st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh13ridh22stp;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg00KBR0g016aR1P1[R1g00ilR2g00K`R3/33#2f0R3#0'1X22X01X10f2f1P3O3W2W0W1o"). Qed.
Lemma s_atop_upd_shadow rid f st : s_atop (upd_shadow rid f st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh13ridh22stp;1p;2g01@7j11Tg00G1j20Tg00KBR0g016aR1P1[R1g00ilR2g00K`f0R3#1'0X22X01X10f2f1P3O3W2W0W1o"). Qed.
Lemma s_ctx_wr8 p v st : s_ctx (wr8 p v st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;1p;2g012Hj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g013>f0R3#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_regions_wr8 p v st : s_regions (wr8 p v st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBg00jeg00kWg014oC2f0R3#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_next_rid_wr8 p v st : s_next_rid (wr8 p v st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;1p;2g017Zj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBf0R3#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_metas_wr8 p v st : s_metas (wr8 p v st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C4P3P4g00kWP1P5g00l5E3g00h?C0f0R5#1'2X12X21X00f2f1P5O3W1W2W0o"). Qed.
Lemma s_areas_wr8 p v st : s_areas (wr8 p v st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C4P3P4g00kWP1P5g00l5E3g019MC0f0R5#1'2X12X21X00f2f1P5O3W1W2W0o"). Qed.
Lemma s_groups_wr8 p v st : s_groups (wr8 p v st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C4P3P4g00kWP1P5g00l5E3g01;=C0f0R5#1'2X12X21X00f2f1P5O3W1W2W0o"). Qed.
Lemma s_slots_wr8 p v st : s_slots (wr8 p v st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<4j13Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C5P3P4g00kWP1P5g00l5E41001C1f0R5#3'2X12X21X00f2f1P5O3W1W2W0o"). Qed.
Lemma s_tick_wr8 p v st : s_tick (wr8 p v st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;1p;2g01<lj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBf0R3#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_secret_wr8 p v st : s_secret (wr8 p v st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;1p;2g01=cj11Tg00G1j20Tg006:R0g00K`R1g00ilR2f0R3#1,01X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_reserved_wr8 p v st : s_reserved (wr8 p v st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg006:R0g00K`R1g00ilR21311#2f0R3#0'1X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_atop_wr8 p v st : s_atop (wr8 p v st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;1p;2g01@7j11Tg00G1j20Tg006:R0g00K`R1g00ilR2f0R3#1,01X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_ctx_wr16 p v st : s_ctx (wr16 p v st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;1p;2g012Hj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g013>f0R3#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_regions_wr16 p v st : s_regions (wr16 p v st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBg00jeg00kWg014oC2f0R3#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_next_rid_wr16 p v st : s_next_rid (wr16 p v st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;1p;2g017Zj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBf0R3#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_metas_wr16 p v st : s_metas (wr16 p v st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C4P3P4g00kWP1P5g00l5E3g00h?C0f0R5#1'2X12X21X00f2f1P5O3W1W2W0o"). Qed.
Lemma s_areas_wr16 p v st : s_areas (wr16 p v st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C4P3P4g00kWP1P5g00l5E3g019MC0f0R5#1'2X12X21X00f2f1P5O3W1W2W0o"). Qed.
Lemma s_groups_wr16 p v st : s_groups (wr16 p v st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C4P3P4g00kWP1P5g00l5E3g01;=C0f0R5#1'2X12X21X00f2f1P5O3W1W2W0o"). Qed.
Lemma s_slots_wr16 p v st : s_slots (wr16 p v st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<4j13Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C5P3P4g00kWP1P5g00l5E41001C1f0R5#3'2X12X21X00f2f1P5O3W1W2W0o"). Qed.
Lemma s_tick_wr16 p v st : s_tick (wr16 p v st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;1p;2g01<lj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBf0R3#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_secret_wr16 p v st : s_secret (wr16 p v st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;1p;2g01=cj11Tg00G1j20Tg006:R0g00K`R1g00ilR2f0R3#1,01X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_reserved_wr16 p v st : s_reserved (wr16 p v st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg006:R0g00K`R1g00ilR21311#2f0R3#0'1X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_atop_wr16 p v st : s_atop (wr16 p v st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;1p;2g01@7j11Tg00G1j20Tg006:R0g00K`R1g00ilR2f0R3#1,01X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_ctx_wr32 p v st : s_ctx (wr32 p v st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;1p;2g012Hj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g013>f0R3#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_regions_wr32 p v st : s_regions (wr32 p v st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBg00jeg00kWg014oC2f0R3#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_next_rid_wr32 p v st : s_next_rid (wr32 p v st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;1p;2g017Zj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBf0R3#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_metas_wr32 p v st : s_metas (wr32 p v st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C4P3P4g00kWP1P5g00l5E3g00h?C0f0R5#1'2X12X21X00f2f1P5O3W1W2W0o"). Qed.
Lemma s_areas_wr32 p v st : s_areas (wr32 p v st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C4P3P4g00kWP1P5g00l5E3g019MC0f0R5#1'2X12X21X00f2f1P5O3W1W2W0o"). Qed.
Lemma s_groups_wr32 p v st : s_groups (wr32 p v st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C4P3P4g00kWP1P5g00l5E3g01;=C0f0R5#1'2X12X21X00f2f1P5O3W1W2W0o"). Qed.
Lemma s_slots_wr32 p v st : s_slots (wr32 p v st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<4j13Tg00G1j22Tg006:R0g00K`R1g00ilR2P0g00KBR3g00jeR4P1g00k>R5C5P3P4g00kWP1P5g00l5E41001C1f0R5#3'2X12X21X00f2f1P5O3W1W2W0o"). Qed.
Lemma s_tick_wr32 p v st : s_tick (wr32 p v st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;1p;2g01<lj11Tg00G1j20Tg006:R0g00K`R1g00ilR2g00KBf0R3#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_secret_wr32 p v st : s_secret (wr32 p v st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;1p;2g01=cj11Tg00G1j20Tg006:R0g00K`R1g00ilR2f0R3#1,01X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_reserved_wr32 p v st : s_reserved (wr32 p v st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg006:R0g00K`R1g00ilR21311#2f0R3#0'1X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_atop_wr32 p v st : s_atop (wr32 p v st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ph12sth21vp;1p;2g01@7j11Tg00G1j20Tg006:R0g00K`R1g00ilR2f0R3#1,01X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma s_ctx_havoc p n st : s_ctx (havoc p n st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01nh11ph22sth31bi001bh41ri013havi024havpi031xp;2p;3p;1p;4g01[aj2KTg00Gmj3JTg00UbR0j28Tg01>\j1?Tg00Ebj4<Tg004Gj3FTg01T2j15Tg01TWj1=Tg01\>j27Tg01\[j26Tg01]8j24Tg01]Uj2>Tg01<lj1ITg01^2j1HTg01^hj43Tg01_dj1ETg01`[j4DTg00SWj49Tg01aWj1CTg01bOj3BTg01cHj3ATg012Hj11Tg006oj3:Tg00G1j2@Tg01dCj3GTg01e9j1;Tf0R1#5#5p=2%;1#;p=0g006:R2g00K`R3g00ilR4f1R5g01e^'Kg00JBR6P6g013>R7P6P4P1f2R8g00KBR9f4R:7J3g016aR;P0P3g00k>R0g00l5R<1839#?C<R=P3P0P<P9C<R<P;P618=<f59F93R9g01XJR;#5#2#2#2#2#2#='7%0;#0#0#0#0#0#=R;'6R0179:R:/6;R>'4P=P<P6P=1>>;R?/4:P?P:f3#IR?P6P=1>0;R;,49P9P;P?%H1R;C3P;n0100000020000R6C3P6n0100000020000P0P>P?%E1R>CDC9P=P<P9P:P?P;C3P>C9n0100000020100%C8?B51n2001103000120101102W4;A8n0100000020001#1%183:P1%15,@7R>P>n0110001020000b3AG851#1%115:7eX24X03X12P8P5P1O3W2W0W1o"). Qed.
Lemma s_regions_havoc p n st : s_regions (havoc p n st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01nh11ph22sth31bi001bh41ri013havi024havpi031xp;2p;4p;3p;1g01[aj2KTg00Ebj45Tg00Gmj3ATg00UbR0j27Tg01>\j1JTg004Gj3FTg01T2j16Tg01TWj1=Tg01\>j28Tg01\[j29Tg01]8j24Tg01]Uj2>Tg01<lj1ITg01^2j1HTg01^hj43Tg01_dj1ETg01`[j4DTg00SWj4:Tg01aWj1CTg01bOj3BTg01cHj3@Tg0145j12Tg006oj3;Tg00G1j2?Tg01dCj3GTg01e9j1<Tf0R1#6#6p=1%<1#<p=0g006:R2g00K`R3g00ilR4f1R5g01e^'Kg00JBR6P6g00KBR7g00jeg00kWg014oC5R8P6P4P1f2R9f4R:9A73g016aR;P0P3g00k>R0g00l5R<1737#JC5R=P3P0P<P7C5R<P;P617=<f59F73R7g01XJR;#6#1#1#1#1#1#='8%0;#0#0#0#0#0#=R;'9R0187:R:/9;R>'4P=P<P6P=1>>;R?/4:P?P:f3#IR?P6P=1>0;R;,47P7P;P?%H1R;C3P;n0100000020000R6C3P6n0100000020000P0P>P?%E1R>CDC:P=P<P7P:P?P;C3P>C:n0100000020100%C9?B51n2001103000120101102W4;@9n0100000020001#2%293;P1%25,?8R>P>n0110001020000b3AG951#2%215;8eX24X03X12P9P5P1O3W2W0W1o"). Qed.
Lemma s_next_rid_havoc p n st : s_next_rid (havoc p n st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01nh11ph22sth31bi001bh41ri013havi024havpi031xp;2p;3p;1p;4g01[aj2KTg00Gmj3JTg00UbR0j28Tg01>\j1?Tg00Ebj4<Tg004Gj3FTg01T2j15Tg01TWj1=Tg01\>j27Tg01\[j26Tg01]8j24Tg01]Uj2>Tg01<lj1ITg01^2j1HTg01^hj43Tg01_dj1ETg01`[j4DTg00SWj49Tg01aWj1CTg01bOj3BTg01cHj3ATg017Zj11Tg006oj3:Tg00G1j2@Tg01dCj3GTg01e9j1;Tf0R1#5#5p=2%;1#;p=0g006:R2g00K`R3g00ilR4f1R5g01e^'Kg00JBR6P6g00KBR7P6P4P1f2R8f4R99J73g016aR:P0P3g00k>R0g00l5R;1837#?C<R<P3P0P;P7C<R;P:P618<;f59F73R:g01XJR0#5#2#2#2#2#2#='7%00#0#0#0#0#0#=R0'6R=17:9R9/60R>'4P<P;P6P<1>>0R?/49P?P9f3#IR?P6P<1>=0R0,4:P:P0P?%H1R0C3P0n0100000020000R6C3P6n0100000020000P=P>P?%E1R>CDC9P<P;P:P9P?P0C3P>C9n0100000020100%C8?B51n2001103000120101102W4;A8n0100000020001#1%183:P1%15,@7R>P>n0110001020000b3AG851#1%115:7eX24X03X12P8P5P1O3W2W0W1o"). Qed.
Lemma s_metas_havoc p n st : s_metas (havoc p n st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01nh11ph22sth31bi001bh41ri013havi024havpi031xp;2p;4p;6p;3p;1g01[aj2MTg00b9j4LTg00bWj6BTg00Ebj45Tg00Gmj3KTg00UbR0j2;Tg01>\j1HTg004Gj3ATg01T2j14Tg01TWj17Tg01\>j29Tg01\[j2>Tg01]8j26Tg01]Uj2<Tg01<lj1JTg01^2j1ITg01^hj43Tg01_dj1GTg01`[j4FTg00SWj48Tg01aWj1CTg01bOj3DTg01cHj3ETg00c8j11Tg006oj3:Tg00G1j2@Tg01dCj3?Tg01e9j1=Tf0R1#4#4p=2%=1#=p=0g006:R2g00K`R3g00ilR4f1R5g01e^'Mg00JBR6P6P2g00KBR7g00jeR8P3g00k>R9CLP7P8g00kWP3P9g00l5R8EBg00h?C5R:P6P4P1f2R;f4R<9K73g016aR=P0P3P9P81;37#HC5R0P3P9P8P7C5R8P=P61;08f59A73R7g01XJR=#4#2#2#2#2#2#7'9%0=#0#0#0#0#0#7R='>R9197<R</>=R>'6P0P8P6P01<>=R?/6<P?P<f3#JR?P6P01<9=R=,67P7P=P?%I1R=C3P=n0100000020000R6C3P6n0100000020000P9P>P?%G1R>CFC8P0P8P7P<P?P=C3P>C8n0100000020100%C;?D51n2001103000120101102W4;E;n0100000020001#1%1;3:P1%15,@:R>P>n0110001020000b3A?;51#1%115::eX24X03X12P;P5P1O3W2W0W1o"). Qed.
Lemma s_areas_havoc p n st : s_areas (havoc p n st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01nh11ph22sth31bi001bh41ri013havi024havpi031xp;2p;4p;6p;3p;1g01[aj2MTg00b9j4LTg00bWj6BTg00Ebj45Tg00Gmj3KTg00UbR0j2;Tg01>\j1HTg004Gj3ATg01T2j14Tg01TWj17Tg01\>j29Tg01\[j2>Tg01]8j26Tg01]Uj2<Tg01<lj1JTg01^2j1ITg01^hj43Tg01_dj1GTg01`[j4FTg00SWj48Tg01aWj1CTg01bOj3DTg01cHj3ETg018Uj11Tg006oj3:Tg00G1j2@Tg01dCj3?Tg01e9j1=Tf0R1#4#4p=2%=1#=p=0g006:R2g00K`R3g00ilR4f1R5g01e^'Mg00JBR6P6P2g00KBR7g00jeR8P3g00k>R9CLP7P8g00kWP3P9g00l5R8EBg019MC5R:P6P4P1f2R;f4R<9K73g016aR=P0P3P9P81;37#HC5R0P3P9P8P7C5R8P=P61;08f59A73R7g01XJR=#4#2#2#2#2#2#7'9%0=#0#0#0#0#0#7R='>R9197<R</>=R>'6P0P8P6P01<>=R?/6<P?P<f3#JR?P6P01<9=R=,67P7P=P?%I1R=C3P=n0100000020000R6C3P6n0100000020000P9P>P?%G1R>CFC8P0P8P7P<P?P=C3P>C8n0100000020100%C;?D51n2001103000120101102W4;E;n0100000020001#1%1;3:P1%15,@:R>P>n0110001020000b3A?;51#1%115::eX24X03X12P;P5P1O3W2W0W1o"). Qed.
Lemma s_groups_havoc p n st : s_groups (havoc p n st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01nh11ph22sth31bi001bh41ri013havi024havpi031xp;2p;4p;6p;3p;1g01[aj2MTg00b9j4LTg00bWj6BTg00Ebj45Tg00Gmj3KTg00UbR0j2;Tg01>\j1HTg004Gj3ATg01T2j14Tg01TWj17Tg01\>j29Tg01\[j2>Tg01]8j26Tg01]Uj2<Tg01<lj1JTg01^2j1ITg01^hj43Tg01_dj1GTg01`[j4FTg00SWj48Tg01aWj1CTg01bOj3DTg01cHj3ETg01:Dj11Tg006oj3:Tg00G1j2@Tg01dCj3?Tg01e9j1=Tf0R1#4#4p=2%=1#=p=0g006:R2g00K`R3g00ilR4f1R5g01e^'Mg00JBR6P6P2g00KBR7g00jeR8P3g00k>R9CLP7P8g00kWP3P9g00l5R8EBg01;=C5R:P6P4P1f2R;f4R<9K73g016aR=P0P3P9P81;37#HC5R0P3P9P8P7C5R8P=P61;08f59A73R7g01XJR=#4#2#2#2#2#2#7'9%0=#0#0#0#0#0#7R='>R9197<R</>=R>'6P0P8P6P01<>=R?/6<P?P<f3#JR?P6P01<9=R=,67P7P=P?%I1R=C3P=n0100000020000R6C3P6n0100000020000P9P>P?%G1R>CFC8P0P8P7P<P?P=C3P>C8n0100000020100%C;?D51n2001103000120101102W4;E;n0100000020001#1%1;3:P1%15,@:R>P>n0110001020000b3A?;51#1%115::eX24X03X12P;P5P1O3W2W0W1o"). Qed.
Lemma s_slots_havoc p n st : s_slots (havoc p n st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01nh11ph22sth31bi001bh41ri013havi024havpi031xp;2p;4p;6p;3p;1g01[aj2MTg00b9j4LTg00bWj6BTg00UbR0j24Tg00Ebj47Tg00Gmj3KTg01>\j1HTg004Gj3ATg01T2j13Tg01TWj18Tg01\>j29Tg01\[j2>Tg01]8j26Tg01]Uj2=Tg01<lj1JTg01^2j1ITg01^hj45Tg01_dj1GTg01`[j4FTg00SWj4:Tg01aWj1CTg01bOj3DTg01cHj3ETg01<4j12Tg006oj3;Tg00G1j2@Tg01dCj3?Tg01e9j1<Tf0R1#3#3p=1%<1#<p=0g006:R2g00K`R3g00ilR4f1R5g01e^'Mg00JBR6P6P2g00KBR7g00jeR8P3g00k>R9CLP7P8g00kWP3P9g00l5R8EB1423C7R:P6P4P1f2R;f4R<9K73g016aR=P0P3P9P81437#HC7R0P3P9P8P7C7R8P=P61408f59A73R7g01XJR=#3#1#1#1#1#1#8'9%0=#0#0#0#0#0#8R='>R9197<R</>=R>'6P0P8P6P01=>=R?/6<P?P<f3#JR?P6P01=9=R=,67P7P=P?%I1R=C5P=n0100000020000R6C5P6n0100000020000P9P>P?%G1R>CFC:P0P8P7P<P?P=C5P>C:n0100000020100%C;?D51n2001103000120101102W4;E;n0100000020001#2%2;3;P1%25,@:R>P>n0110001020000b3A?;51#2%215;:eX24X03X12P;P5P1O3W2W0W1o"). Qed.
Lemma s_tick_havoc p n st : s_tick (havoc p n st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01nh11ph22sth31bi001bh41ri013havi024havpi031xp;2p;3p;1p;4g01[aj2JTg00Gmj3ITg00UbR0j29Tg01>\j1?Tg00Ebj4<Tg004Gj3GTg01T2j15Tg01TWj1;Tg01\>j27Tg01\[j26Tg01]8j23Tg01]Uj2>Tg01<lj11Tg01^2j1HTg01^hj44Tg01_dj1FTg01`[j4ETg00SWj4:Tg01aWj1DTg01bOj3CTg01cHj3BTg006oj38Tg00G1j2ATg01dCj3@Tg01e9j1=Tf0R1#5#5p=2%=1#=p=0g006:R2g00K`R3g00ilR4f1R5g01e^'Jg00JBR6P6g00KBR7P6P4P1f2R8f4R99I73g016aR:P0P3g00k>R0g00l5R;1937#?C<R<P3P0P;P7C<R;P:P619<;f59G73R:g01XJR0#5#2#2#2#2#2#;'7%00#0#0#0#0#0#;R0'6R=17:9R9/60R>'3P<P;P6P<1>>0R?/39P?P9f3#1R?P6P<1>=0R0,3:P:P0P?%H1R0C4P0n0100000020000R6C4P6n0100000020000P=P>P?%F1R>CEC:P<P;P:P9P?P0C4P>C:n0100000020100%D8?C51n2001103000120101102W4;B8n0100000020001#1%1838P1%15,A7R>P>n0110001020000b3A@851#1%11587eX24X03X12P8P5P1O3W2W0W1o"). Qed.
Lemma s_secret_havoc p n st : s_secret (havoc p n st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01nh11ph22sth31bi001bh41ri013havi024havpi031xp;2p;3p;1p;4g01[aj2KTg00Gmj3JTg00UbR0j28Tg01>\j1?Tg00Ebj4<Tg004Gj3FTg01T2j15Tg01TWj1=Tg01\>j27Tg01\[j26Tg01]8j24Tg01]Uj2>Tg01<lj1ITg01^2j1HTg01^hj43Tg01_dj1ETg01`[j4DTg00SWj49Tg01aWj1CTg01bOj3BTg01cHj3ATg01=cj11Tg006oj3:Tg00G1j2@Tg01dCj3GTg01e9j1;Tf0R1#5#5p=2%;1#;p=0g006:R2g00K`R3g00ilR4f1R5g01e^'Kg00JBR6P6P6P4P1f2R7g00KBR8f4R97J3g016aR:P0P3g00k>R0g00l5R;1838#?C<R<P3P0P;P8C<R;P:P618<;f59F83R8g01XJR:#5#2#2#2#2#2#='7%0:#0#0#0#0#0#=R:'6R01789R9/6:R='4P<P;P6P<1>=:R>/49P>P9f3#IR>P6P<1>0:R:,48P8P:P>%H1R:C3P:n0100000020000R6C3P6n0100000020000P0P=P>%E1R=CDC9P<P;P8P9P>P:C3P=C9n0100000020100%C7?B51n2001103000120101102W4;A7n0100000020001#1%175:3P1%15,@3R=P=n0110001020000b3AG751#1%115:3eX24X03X12P7P5P1O3W2W0W1o"). Qed.
Lemma s_reserved_havoc p n st : s_reserved (havoc p n st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01nh11ph22sth31bi001bh41ri013havi024havpi031xp;2p;1p;3p;4g01[aj2KTg00UbR0j23Tg01>\j1:Tg00Gmj3@Tg00Ebj4=Tg004Gj3HTg01T2j16Tg01TWj1<Tg01\>j28Tg01\[j27Tg01]8j25Tg01]Uj2?Tg01<lj1JTg01^2j1ITg01^hj44Tg01_dj1GTg01`[j4ETg00SWj4;Tg01aWj1DTg01bOj3CTg01cHj3BTg01?<j12Tg006oj39Tg00G1j2ATg01dCj3FTg01e9j1>Tf0R1#6#6p=1%>1#>p=0g006:R2g00K`R3g00ilR4f1R5g01e^'Kg00JBR6P61333#:R7P6P4P1f2R8g00KBR9f4R:7@3g016aR;P0P3g00k>R0g00l5R<1339#:C=R=P3P0P<P9C=R<P;P613=<f59H93R9g01XJR;#6#1#1#1#1#1#<'8%0;#0#0#0#0#0#<R;'7R0189:R:/7;R>'5P=P<P6P=1?>;R?/5:P?P:f3#JR?P6P=1?0;R;,59P9P;P?%I1R;C4P;n0100000020000R6C4P6n0100000020000P0P>P?%G1R>CEC;P=P<P9P:P?P;C4P>C;n0100000020100%D8?C51n2001103000120101102W4;B8n0100000020001#2%2839P1%25,A7R>P>n0110001020000b3AF851#2%21597eX24X03X12P8P5P1O3W2W0W1o"). Qed.
Lemma s_atop_havoc p n st : s_atop (havoc p n st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01nh11ph22sth31bi001bh41ri013havi024havpi031xp;2p;3p;1p;4g01[aj2KTg00Gmj3JTg00UbR0j28Tg01>\j1?Tg00Ebj4<Tg004Gj3FTg01T2j15Tg01TWj1=Tg01\>j27Tg01\[j26Tg01]8j24Tg01]Uj2>Tg01<lj1ITg01^2j1HTg01^hj43Tg01_dj1ETg01`[j4DTg00SWj49Tg01aWj1CTg01bOj3BTg01cHj3ATg01@7j11Tg006oj3:Tg00G1j2@Tg01dCj3GTg01e9j1;Tf0R1#5#5p=2%;1#;p=0g006:R2g00K`R3g00ilR4f1R5g01e^'Kg00JBR6P6P6P4P1f2R7g00KBR8f4R97J3g016aR:P0P3g00k>R0g00l5R;1838#?C<R<P3P0P;P8C<R;P:P618<;f59F83R8g01XJR:#5#2#2#2#2#2#='7%0:#0#0#0#0#0#=R:'6R01789R9/6:R='4P<P;P6P<1>=:R>/49P>P9f3#IR>P6P<1>0:R:,48P8P:P>%H1R:C3P:n0100000020000R6C3P6n0100000020000P0P=P>%E1R=CDC9P<P;P8P9P>P:C3P=C9n0100000020100%C7?B51n2001103000120101102W4;A7n0100000020001#1%175:3P1%15,@3R=P=n0110001020000b3AG751#1%115:3eX24X03X12P7P5P1O3W2W0W1o"). Qed.
Lemma s_ctx_hdr_havoc b st : s_ctx (hdr_havoc b st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01bh12stp;1p;2g012Hj11Tg00G1j20Tg006:R0g00ilR1g013>f0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_regions_hdr_havoc b st : s_regions (hdr_havoc b st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01bh12stp;4p;1p;2g00Ebj42Tg0145j11Tg00G1j20Tg006:R0g00ilR1g00KBg00jeg00kWg014oC2f0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_next_rid_hdr_havoc b st : s_next_rid (hdr_havoc b st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01bh12stp;1p;2g017Zj11Tg00G1j20Tg006:R0g00ilR1g00KBf0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_metas_hdr_havoc b st : s_metas (hdr_havoc b st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01bh12stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg00c8j11Tg00G1j22Tg006:R0g00ilR1P0g00KBR2g00jeR3g00K`R4g00k>R5C4P2P3g00kWP4P5g00l5E3g00h?C0f0R5#1'2X11X00f1P5O2W1W0o"). Qed.
Lemma s_areas_hdr_havoc b st : s_areas (hdr_havoc b st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01bh12stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg018Uj11Tg00G1j22Tg006:R0g00ilR1P0g00KBR2g00jeR3g00K`R4g00k>R5C4P2P3g00kWP4P5g00l5E3g019MC0f0R5#1'2X11X00f1P5O2W1W0o"). Qed.
Lemma s_groups_hdr_havoc b st : s_groups (hdr_havoc b st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01bh12stp;4p;6p;1p;2g00b9j44Tg00bWj63Tg00Ebj40Tg01:Dj11Tg00G1j22Tg006:R0g00ilR1P0g00KBR2g00jeR3g00K`R4g00k>R5C4P2P3g00kWP4P5g00l5E3g01;=C0f0R5#1'2X11X00f1P5O2W1W0o"). Qed.
Lemma s_slots_hdr_havoc b st : s_slots (hdr_havoc b st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01bh12stp;4p;6p;2p;1g00b9j45Tg00bWj64Tg00Ubj20Tg00Ebj41Tg01<4j13Tg00G1j22Tg006:R0g00ilR1P0g00KBR2g00jeR3g00K`R4g00k>R5C5P2P3g00kWP4P5g00l5E41004C1f0R4#3'2X11X00f1P4O2W1W0o"). Qed.
Lemma s_tick_hdr_havoc b st : s_tick (hdr_havoc b st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01bh12stp;1p;2g01<lj11Tg00G1j20Tg006:R0g00ilR1g00KBf0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_secret_hdr_havoc b st : s_secret (hdr_havoc b st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01bh12stp;1p;2g01=cj11Tg00G1j20Tg006:R0g00ilR1g00K`f0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_reserved_hdr_havoc b st : s_reserved (hdr_havoc b st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01bh12stp;2p;1g00Ubj23Tg01>\j12Tg01?<j10Tg00G1j21Tg006:R0g00ilR1g00K`R2/32#2f0R2#0'1X11X00f1P2O2W1W0o"). Qed.
Lemma s_atop_hdr_havoc b st : s_atop (hdr_havoc b st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01bh12stp;1p;2g01@7j11Tg00G1j20Tg006:R0g00ilR1g00K`f0R2#1'0X11X00f1P2O2W1W0o"). Qed.
Lemma s_regions_step_seq  st : s_regions (step_seq st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1?Tg01Naj14Tg01T2j10Tg01TWj13Tg00F6j2>Tg00Ebj46Tg00<@j4;Tg01g0j2:Tg01gCj29Tg01hEj22Tg01i=j25Tg01\>j28Tg0145j11Tg006oj37Tg00G1j2=Tg01j5j1<Tg00ilR0f0R1#?#4g01XJR2#0#0#0#0#0#0#0#3'>g00JBR3P3g00KBg00jeg00kWg014oC6R4P3P0P1g013>R3%32R2g00K`R5g00k>R6g00l5R7P5C6P5P6P7P5C;':/91'2W0f2R5'5%41/82/21X03/55n0100000020000#1%1537P1f1#1,=4R5P5n0110000020000b2%<1#1%11574eX10P1O1W1o"). Qed.
Lemma s_shadow_step_seq  st : s_shadow (step_seq st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1?Tg01Naj14Tg01T2j10Tg01TWj13Tg00F6j2>Tg00Ebj46Tg00<@j4;Tg01g0j2:Tg01gCj29Tg01hEj22Tg01i=j25Tg01\>j28Tg015hj11Tg006oj37Tg00G1j2=Tg01j5j1<Tg00ilR0f0R1#?#4g01XJR2#0#0#0#0#0#0#0#3'>g00JBR3P3g00KBg00jeg00kWg016aC6R4P3P0P1g013>R3%32R2g00K`R5g00k>R6g00l5R7P5C6P5P6P7P5C;':/91'2W0f2R5'5%41/82/21X03/55n0100000020000#1%1537P1f1#1,=4R5P5n0110000020000b2%<1#1%11574eX10P1O1W1o"). Qed.
Lemma s_next_rid_step_seq  st : s_next_rid (step_seq st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1?Tg01Naj14Tg01T2j10Tg01TWj15Tg00F6j2>Tg00Ebj4;Tg00<@j4:Tg01g0j29Tg01gCj28Tg01hEj22Tg01i=j23Tg01\>j27Tg017Zj11Tg006oj36Tg00G1j2=Tg01j5j1<Tg00ilR0f0R1#?#4g01XJR2#0#0#0#0#0#0#0#5'>g00JBR3P3g00KBR4P3P0P1g013>R3%52R2g00K`R5g00k>R6g00l5R7P5C;P5P6P7P5C:'9/81'2W0f2R5'3%41/72/21X03/35n0100000020000#1%1536P1f1#1,=4R5P5n0110000020000b2%<1#1%11564eX10P1O1W1o"). Qed.
Lemma s_metas_step_seq  st : s_metas (step_seq st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;6p;3g01f<j1ATg01Naj17Tg01T2j10Tg01TWj14Tg00F6j2@Tg00b9j4<Tg00bWj6;Tg00Ebj43Tg00<@j4:Tg01g0j29Tg01gCj28Tg01hEj22Tg01i=j26Tg01\>j2?Tg00c8j11Tg006oj35Tg00G1j2=Tg01j5j1>Tg00ilR0f0R1#A#7g01XJR2#0#0#0#0#0#0#0#4'@g00JBR3P3g006:g00KBR4g00jeR5g00K`R6g00k>R7C<P4P5g00kWP6P7g00l5R5E;g00h?C3R4P3P0P1g013>R3%42R2P6P7P5P6C3P6P7P5P6C:'9/81'2W0f2R6'6%71/?2/21X03/66n0100000020000#1%1635P1f1#1,=4R6P6n0110000020000b2%>1#1%11554eX10P1O1W1o"). Qed.
Lemma s_areas_step_seq  st : s_areas (step_seq st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;6p;3g01f<j1ATg01Naj17Tg01T2j10Tg01TWj14Tg00F6j2@Tg00b9j4<Tg00bWj6;Tg00Ebj43Tg00<@j4:Tg01g0j29Tg01gCj28Tg01hEj22Tg01i=j26Tg01\>j2?Tg018Uj11Tg006oj35Tg00G1j2=Tg01j5j1>Tg00ilR0f0R1#A#7g01XJR2#0#0#0#0#0#0#0#4'@g00JBR3P3g006:g00KBR4g00jeR5g00K`R6g00k>R7C<P4P5g00kWP6P7g00l5R5E;g019MC3R4P3P0P1g013>R3%42R2P6P7P5P6C3P6P7P5P6C:'9/81'2W0f2R6'6%71/?2/21X03/66n0100000020000#1%1635P1f1#1,=4R6P6n0110000020000b2%>1#1%11554eX10P1O1W1o"). Qed.
Lemma s_groups_step_seq  st : s_groups (step_seq st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;6p;3g01f<j1ATg01Naj17Tg01T2j10Tg01TWj14Tg00F6j2@Tg00b9j4<Tg00bWj6;Tg00Ebj43Tg00<@j4:Tg01g0j29Tg01gCj28Tg01hEj22Tg01i=j26Tg01\>j2?Tg01:Dj11Tg006oj35Tg00G1j2=Tg01j5j1>Tg00ilR0f0R1#A#7g01XJR2#0#0#0#0#0#0#0#4'@g00JBR3P3g006:g00KBR4g00jeR5g00K`R6g00k>R7C<P4P5g00kWP6P7g00l5R5E;g01;=C3R4P3P0P1g013>R3%42R2P6P7P5P6C3P6P7P5P6C:'9/81'2W0f2R6'6%71/?2/21X03/66n0100000020000#1%1635P1f1#1,=4R6P6n0110000020000b2%>1#1%11554eX10P1O1W1o"). Qed.
Lemma s_slots_step_seq  st : s_slots (step_seq st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;6p;3g01f<j1BTg01Naj14Tg01T2j10Tg01TWj15Tg00F6j2ATg00b9j4=Tg00bWj6<Tg00Ubj2;Tg00Ebj43Tg00<@j4:Tg01g0j28Tg01gCj29Tg01hEj22Tg01i=j27Tg01\>j2@Tg01<4j11Tg006oj36Tg00G1j2>Tg01j5j1?Tg00ilR0f0R1#B#4g01XJR2#0#0#0#0#0#0#0#5'Ag00JBR3P3g006:R4g00KBR5g00jeR6g00K`R7g00k>R8C=P5P6g00kWP7P8g00l5R6E<1;47C3R4P3P0P1g013>R3%52R2P7P8P6P7C3P7P8P6P7C:'8/91'2W0f2R7'7%41/@2/21X03/77n0100000020000#1%1736P1f1#1,>4R7P7n0110000020000b2%?1#1%11564eX10P1O1W1o"). Qed.
Lemma s_tick_step_seq  st : s_tick (step_seq st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1?Tg01Naj14Tg01T2j10Tg01TWj15Tg00F6j2>Tg00Ebj4;Tg00<@j4:Tg01g0j29Tg01gCj28Tg01hEj22Tg01i=j23Tg01\>j27Tg01<lj11Tg006oj36Tg00G1j2=Tg01j5j1<Tg00ilR0f0R1#?#4g01XJR2#0#0#0#0#0#0#0#5'>g00JBR3P3g00KBR4P3P0P1g013>R3%52R2g00K`R5g00k>R6g00l5R7P5C;P5P6P7P5C:'9/81'2W0f2R5'3%41/72/21X03/35n0100000020000#1%1536P1f1#1,=4R5P5n0110000020000b2%<1#1%11564eX10P1O1W1o"). Qed.
Lemma s_secret_step_seq  st : s_secret (step_seq st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1?Tg01Naj14Tg01T2j10Tg01TWj15Tg00F6j2>Tg00Ebj4;Tg00<@j4:Tg01g0j29Tg01gCj28Tg01hEj22Tg01i=j23Tg01\>j27Tg01=cj11Tg006oj36Tg00G1j2=Tg01j5j1<Tg00ilR0f0R1#?#4g01XJR2#0#0#0#0#0#0#0#5'>g00JBR3P3g00K`R4P3P0P1g013>R3%52R2P4g00k>R5g00l5R6P4C;P4P5P6P4C:'9/81'2W0f2R6'3%41/72/21X03/36n0100000020000#1%1636P1f1#1,=4R6P6n0110000020000b2%<1#1%11564eX10P1O1W1o"). Qed.
Lemma s_reserved_step_seq  st : s_reserved (step_seq st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1ATg01Naj16Tg01T2j10Tg01TWj12Tg00F6j2@Tg00Ubj2<Tg01>\j1;Tg00Ebj4:Tg00<@j49Tg01g0j28Tg01gCj27Tg01hEj23Tg01i=j25Tg01\>j2?Tg01?<j11Tg006oj34Tg00G1j2=Tg01j5j1>Tg00ilR0f0R1#A#6g01XJR2#0#0#0#0#0#0#0#2'@g00JBR3P3g00K`R4/<4#;R5P3P0P1g013>R3%22R2P4g00k>R6g00l5R7P4C:P4P6P7P4C9'8/71'3W0f2R4'5%61/?2/31X03/54n0100000020000#1%1434P1f1#1,=5R4P4n0110000020000b2%>1#1%11545eX10P1O1W1o"). Qed.
Lemma s_atop_step_seq  st : s_atop (step_seq st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1?Tg01Naj14Tg01T2j10Tg01TWj15Tg00F6j2>Tg00Ebj4;Tg00<@j4:Tg01g0j29Tg01gCj28Tg01hEj22Tg01i=j23Tg01\>j27Tg01@7j11Tg006oj36Tg00G1j2=Tg01j5j1<Tg00ilR0f0R1#?#4g01XJR2#0#0#0#0#0#0#0#5'>g00JBR3P3g00K`R4P3P0P1g013>R3%52R2P4g00k>R5g00l5R6P4C;P4P5P6P4C:'9/81'2W0f2R6'3%41/72/21X03/36n0100000020000#1%1636P1f1#1,=4R6P6n0110000020000b2%<1#1%11564eX10P1O1W1o"). Qed.
Lemma s_regions_record_seq sc st : s_regions (record_seq sc st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1?Tg00Ebj42Tg00<Xj4:Tg00:<j44Tg01T2j11Tg01TWj1<Tg01knj2;Tg01Naj19Tg01Lkj15Tg00g<j76Tg01gCj27Tg01i=j28Tg0145j10Tg006oj33Tg00G1j2>Tg01lKj2=Tg00K`R0g00ilR1f1R2#?g00JBR3P3g00KBg00jeg00kWg014oC2R4P3P1f0R3g013>P0P0P0g00k>R5g00l5R6P0C2R7P0P0P7P0P5P6P0C:C4f4g01XJ#1#1#<';%93%53F6/73W3f2R6'8P6n0100000020000#0%0633P3%02,>4R6P6n0110000020000b21=23#0%03534eX11X00P2P3O2W1W0o"). Qed.
Lemma s_shadow_record_seq sc st : s_shadow (record_seq sc st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1?Tg00Ebj42Tg00<Xj4:Tg00:<j44Tg01T2j11Tg01TWj1<Tg01knj2;Tg01Naj19Tg01Lkj15Tg00g<j76Tg01gCj27Tg01i=j28Tg015hj10Tg006oj33Tg00G1j2>Tg01lKj2=Tg00K`R0g00ilR1f1R2#?g00JBR3P3g00KBg00jeg00kWg016aC2R4P3P1f0R3g013>P0P0P0g00k>R5g00l5R6P0C2R7P0P0P7P0P5P6P0C:C4f4g01XJ#1#1#<';%93%53F6/73W3f2R6'8P6n0100000020000#0%0633P3%02,>4R6P6n0110000020000b21=23#0%03534eX11X00P2P3O2W1W0o"). Qed.
Lemma s_next_rid_record_seq sc st : s_next_rid (record_seq sc st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1?Tg00Ebj4>Tg00<Xj44Tg00:<j43Tg01T2j11Tg01TWj1;Tg01knj2:Tg01Naj15Tg01Lkj16Tg00g<j77Tg01gCj28Tg01i=j29Tg017Zj10Tg006oj32Tg00G1j2=Tg01lKj2<Tg00K`R0g00ilR1f1R2#?g00JBR3P3g00KBR4P3P1f0R3g013>P0P0P0g00k>R5g00l5R6P0C>R7P0P0P7P0P5P6P0C4C3f4g01XJ#1#1#;':%53%63F7/83W3f2R6'9P6n0100000020000#0%0632P3%02,=4R6P6n0110000020000b21<23#0%03524eX11X00P2P3O2W1W0o"). Qed.
Lemma s_metas_record_seq sc st : s_metas (record_seq sc st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;6p;2p;7p;3g01jnj1ATg00b9j4@Tg00bWj68Tg00Ebj42Tg00<Xj4?Tg00:<j4;Tg01T2j11Tg01TWj17Tg01knj25Tg01Naj16Tg01Lkj14Tg00g<j79Tg01gCj2:Tg01i=j2>Tg00c8j10Tg006oj33Tg00G1j2<Tg01lKj2=Tg00K`R0g00ilR1f1R2#Ag00JBR3P3g006:g00KBR4g00jeR5P0g00k>R6C@P4P5g00kWP0P6g00l5R5E8g00h?C2R4P3P1f0R3g013>P0P0P0P6P5P0C2R7P0P0P7P0P6P5P0C?C;f4g01XJ#1#1#7'5%63%43F9/:3W3f2R5'>P5n0100000020000#0%0533P3%02,<4R5P5n0110000020000b21=23#0%03534eX11X00P2P3O2W1W0o"). Qed.
Lemma s_areas_record_seq sc st : s_areas (record_seq sc st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;6p;2p;7p;3g01jnj1ATg00b9j4@Tg00bWj68Tg00Ebj42Tg00<Xj4?Tg00:<j4;Tg01T2j11Tg01TWj17Tg01knj25Tg01Naj16Tg01Lkj14Tg00g<j79Tg01gCj2:Tg01i=j2>Tg018Uj10Tg006oj33Tg00G1j2<Tg01lKj2=Tg00K`R0g00ilR1f1R2#Ag00JBR3P3g006:g00KBR4g00jeR5P0g00k>R6C@P4P5g00kWP0P6g00l5R5E8g019MC2R4P3P1f0R3g013>P0P0P0P6P5P0C2R7P0P0P7P0P6P5P0C?C;f4g01XJ#1#1#7'5%63%43F9/:3W3f2R5'>P5n0100000020000#0%0533P3%02,<4R5P5n0110000020000b21=23#0%03534eX11X00P2P3O2W1W0o"). Qed.
Lemma s_groups_record_seq sc st : s_groups (record_seq sc st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;6p;2p;7p;3g01jnj1ATg00b9j4@Tg00bWj68Tg00Ebj42Tg00<Xj4?Tg00:<j4;Tg01T2j11Tg01TWj17Tg01knj25Tg01Naj16Tg01Lkj14Tg00g<j79Tg01gCj2:Tg01i=j2>Tg01:Dj10Tg006oj33Tg00G1j2<Tg01lKj2=Tg00K`R0g00ilR1f1R2#Ag00JBR3P3g006:g00KBR4g00jeR5P0g00k>R6C@P4P5g00kWP0P6g00l5R5E8g01;=C2R4P3P1f0R3g013>P0P0P0P6P5P0C2R7P0P0P7P0P6P5P0C?C;f4g01XJ#1#1#7'5%63%43F9/:3W3f2R5'>P5n0100000020000#0%0533P3%02,<4R5P5n0110000020000b21=23#0%03534eX11X00P2P3O2W1W0o"). Qed.
Lemma s_slots_record_seq sc st : s_slots (record_seq sc st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;6p;2p;7p;3g01jnj1BTg00b9j4ATg00bWj65Tg00Ubj24Tg00Ebj43Tg00<Xj4<Tg00:<j4;Tg01T2j12Tg01TWj16Tg01knj27Tg01Naj18Tg01Lkj19Tg00g<j7:Tg01gCj2@Tg01i=j2?Tg01<4j10Tg006oj31Tg00G1j2=Tg01lKj2>Tg00K`R0g00ilR1f1R2#Bg00JBR3P3g006:R4g00KBR5g00jeR6P0g00k>R7CAP5P6g00kWP0P7g00l5R6E51440C3R4P3P1f0R3g013>P0P0P0P7P6P0C3R5P0P0P5P0P7P6P0C<C;f4g01XJ#2#2#6'7%83%93F:/@3W3f2R6'?P6n0100000020000#0%0631P3%02,=4R6P6n0110000020000b21>23#0%03514eX11X00P2P3O2W1W0o"). Qed.
Lemma s_tick_record_seq sc st : s_tick (record_seq sc st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1?Tg00Ebj4>Tg00<Xj44Tg00:<j43Tg01T2j11Tg01TWj1;Tg01knj2:Tg01Naj15Tg01Lkj16Tg00g<j77Tg01gCj28Tg01i=j29Tg01<lj10Tg006oj32Tg00G1j2=Tg01lKj2<Tg00K`R0g00ilR1f1R2#?g00JBR3P3g00KBR4P3P1f0R3g013>P0P0P0g00k>R5g00l5R6P0C>R7P0P0P7P0P5P6P0C4C3f4g01XJ#1#1#;':%53%63F7/83W3f2R6'9P6n0100000020000#0%0632P3%02,=4R6P6n0110000020000b21<23#0%03524eX11X00P2P3O2W1W0o"). Qed.
Lemma s_secret_record_seq sc st : s_secret (record_seq sc st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1?Tg00Ebj4>Tg00<Xj44Tg00:<j43Tg01T2j11Tg01TWj1;Tg01knj2:Tg01Naj15Tg01Lkj16Tg00g<j77Tg01gCj28Tg01i=j29Tg01=cj10Tg006oj32Tg00G1j2=Tg01lKj2<Tg00K`R0g00ilR1f1R2#?g00JBR3P3P3P1f0R3g013>P0P0P0g00k>R4g00l5R5P0C>R6P0P0P6P0P4P5P0C4C3f4g01XJ#1#1#;':%53%63F7/83W3f2R5'9P5n0100000020000#0%05520P3%02,=0R5P5n0110000020000b21<23#0%03520eX11X00P2P3O2W1W0o"). Qed.
Lemma s_reserved_record_seq sc st : s_reserved (record_seq sc st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1ATg00Ubj2@Tg01>\j14Tg00Ebj43Tg00<Xj4?Tg00:<j4;Tg01T2j11Tg01TWj15Tg01knj26Tg01Naj17Tg01Lkj18Tg00g<j79Tg01gCj2:Tg01i=j2>Tg01?<j10Tg006oj32Tg00G1j2<Tg01lKj2=Tg00K`R0g00ilR1f1R2#Ag00JBR3P31@00#4R4P3P1f0R3g013>P0P0P0g00k>R5g00l5R6P0C3R7P0P0P7P0P5P6P0C?C;f4g01XJ#1#1#5'6%73%83F9/:3W3f2R6'>P6n0100000020000#0%0632P3%02,<4R6P6n0110000020000b21=23#0%03524eX11X00P2P3O2W1W0o"). Qed.
Lemma s_atop_record_seq sc st : s_atop (record_seq sc st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1?Tg00Ebj4>Tg00<Xj44Tg00:<j43Tg01T2j11Tg01TWj1;Tg01knj2:Tg01Naj15Tg01Lkj16Tg00g<j77Tg01gCj28Tg01i=j29Tg01@7j10Tg006oj32Tg00G1j2=Tg01lKj2<Tg00K`R0g00ilR1f1R2#?g00JBR3P3P3P1f0R3g013>P0P0P0g00k>R4g00l5R5P0C>R6P0P0P6P0P4P5P0C4C3f4g01XJ#1#1#;':%53%63F7/83W3f2R5'9P5n0100000020000#0%05520P3%02,=0R5P5n0110000020000b21<23#0%03520eX11X00P2P3O2W1W0o"). Qed.
Lemma s_regions_account_bounce sc st : s_regions (account_bounce sc st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;4p;2p;3p;7g01jnj1ITg00Ebj4CTg01T2j12Tg01TWj17Tg01knj23Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1ATg01Naj1>Tg01e9j11Tg01]8j28Tg00FSj2=Tg01n^j2;Tg01\>j29Tg00<Xj4HTg00:<j4GTg01Mgj1FTg01oVj26Tg01i=j25Tg0145j10Tg006oj3:Tg00G1j2<Tg020Vj2ETg00g<j7DTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FDp=4g00ilR6%I4g00JBR7P7g00KBg00jeg00kWg014oCCR8P7P6P5P7P6g01XJR9#2R:#2#7R;,32R<,B3R=g01e^R>'@#?%A3#>/3=%19R=#2#1#7R?'8'=P7P61;3<%79R9'9%1:#1#2#1#1#7R:'8R<g013>R@P0g00k>RAg00l5RBP0CCRCP0P0PCP0PAPBP0CHCGRB131;RA1;2A/99RD%F5RED4/65W0/53PCPBPA%1=#2#1#2#2#1#7R=PED4/65X0@/53n0100000020000P3n0100000020000P3n0100000020000#0%03RA3:P5133;,B4R3/@>#?%A4#>/33/8?'=P7P7P7P6P5P7P618D:PCPBf5RD/3;R:1;1:/99PED4/65X0@/52PCPBP:P=PED4/65X0@/52n0100000020000P2n0100000020000#0%02R25:8P5P<P7P7P7P6P5PCPBf6/3;R;1;D;/99PED4/65X0@/51PCPBP;P=PED4/65X0@/51n0100000020000#0%015:8P51<82R2P2n0110000020000b11<8An0110000020000b1%04,<8n0110000020100b11E45#0%055:8eX36X20P4P5O2W3X20o"). Qed.
Lemma s_shadow_account_bounce sc st : s_shadow (account_bounce sc st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;4p;2p;3p;7g01jnj1ITg00Ebj4CTg01T2j12Tg01TWj17Tg01knj23Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1ATg01Naj1>Tg01e9j11Tg01]8j28Tg00FSj2=Tg01n^j2;Tg01\>j29Tg00<Xj4HTg00:<j4GTg01Mgj1FTg01oVj26Tg01i=j25Tg015hj10Tg006oj3:Tg00G1j2<Tg020Vj2ETg00g<j7DTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FDp=4g00ilR6%I4g00JBR7P7g00KBg00jeg00kWg016aCCR8P7P6P5P7P6g01XJR9#2R:#2#7R;,32R<,B3R=g01e^R>'@#?%A3#>/3=%19R=#2#1#7R?'8'=P7P61;3<%79R9'9%1:#1#2#1#1#7R:'8R<g013>R@P0g00k>RAg00l5RBP0CCRCP0P0PCP0PAPBP0CHCGRB131;RA1;2A/99RD%F5RED4/65W0/53PCPBPA%1=#2#1#2#2#1#7R=PED4/65X0@/53n0100000020000P3n0100000020000P3n0100000020000#0%03RA3:P5133;,B4R3/@>#?%A4#>/33/8?'=P7P7P7P6P5P7P618D:PCPBf5RD/3;R:1;1:/99PED4/65X0@/52PCPBP:P=PED4/65X0@/52n0100000020000P2n0100000020000#0%02R25:8P5P<P7P7P7P6P5PCPBf6/3;R;1;D;/99PED4/65X0@/51PCPBP;P=PED4/65X0@/51n0100000020000#0%015:8P51<82R2P2n0110000020000b11<8An0110000020000b1%04,<8n0110000020100b11E45#0%055:8eX36X20P4P5O2W3X20o"). Qed.
Lemma s_next_rid_account_bounce sc st : s_next_rid (account_bounce sc st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1ITg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1>Tg01Naj1ATg01e9j10Tg01]8j29Tg00FSj2=Tg01n^j2:Tg01\>j2;Tg00Ebj4HTg00<Xj4GTg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg017Zj11Tg006oj38Tg00G1j2<Tg020Vj2DTg00g<j7CTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5g00ilR6%I4g00JBR7P7g00KBR8P7P6P5P7P6g01XJR9#3R:#3#7R;,22R<,B3R=g01e^R>'@#?%>3#A/2=%09R=#3#0#7R?'9'=P7P61:3<%79R9';%0:#0#3#0#0#7R:'9R<g013>R@P0g00k>RAg00l5RBP0CHRCP0P0PCP0PAPBP0CGCFRB121;RA1:2A/;9RD%E5RED5/65W0/43PCPBPA%0=#3#0#3#3#0#7R=PED5/65X0@/43n0100000020000P3n0100000020000P3n0100000020000#1%13RA38P5123;,B4R3/@>#?%>4#A/23/9?'=P7P7P7P6P5P7P619D:PCPBf5RD/2;R:1:1:/;9PED5/65X0@/42PCPBP:P=PED5/65X0@/42n0100000020000P2n0100000020000#1%12R2588P5P<P7P7P7P6P5PCPBf6/2;R;1:D;/;9PED5/65X0@/41PCPBP;P=PED5/65X0@/41n0100000020000#1%11588P51<82R2P2n0110000020000b11<8An0110000020000b1%14,<8n0110000020100b11D45#1%15588eX36X20P4P5O2W3X20o"). Qed.
Lemma s_metas_account_bounce sc st : s_metas (account_bounce sc st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;4p;6p;2p;3p;7g01jnj1KTg00b9j4JTg00bWj6ETg00Ebj4?Tg01T2j13Tg01TWj17Tg01knj22Tg01mFj2ATg00F6j2BTg01n@j1@Tg01f<j1>Tg01Naj1=Tg01e9j10Tg01]8j2;Tg00FSj2CTg01n^j28Tg01\>j2:Tg00<Xj4ITg00:<j4HTg01Mgj1FTg01oVj26Tg01i=j25Tg00c8j11Tg006oj39Tg00G1j2<Tg020Vj2DTg00g<j7GTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FGp=4g00ilR6%K4g00JBR7P7g006:g00KBR8g00jeR9P0g00k>R:CJP8P9g00kWP0P:g00l5R9EEg00h?C?R8P7P6P5P7P6g01XJR;#3R<#3#7R=,22R>,A3R?g01e^R@'B#@%>3#=/2?%0;R?#3#0#7RA';'CP7P6183>%7;R;':%0<#0#3#0#0#7R<';R>g013>RBP0P:P9P0C?RCP0P0PCP0P:P9P0CICHR9121=R:182:/:;RD%F5RED4/65W0/53PCP9P:%0?#3#0#3#3#0#7R?PED4/65X0B/53n0100000020000P3n0100000020000P3n0100000020000#1%13R:39P5123=,A4R3/B@#@%>4#=/23/;A'CP7P7P7P6P5P7P61;D<PCP9f5RD/2=R<181</:;PED4/65X0B/52PCP9P<P?PED4/65X0B/52n0100000020000P2n0100000020000#1%12R2598P5P>P7P7P7P6P5PCP9f6/2=R=18D=/:;PED4/65X0B/51PCP9P=P?PED4/65X0B/51n0100000020000#1%11598P51<82R2P2n0110000020000b11<8:n0110000020000b1%14,<8n0110000020100b11D45#1%15598eX36X20P4P5O2W3X20o"). Qed.
Lemma s_areas_account_bounce sc st : s_areas (account_bounce sc st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;4p;6p;2p;3p;7g01jnj1KTg00b9j4JTg00bWj6ETg00Ebj4?Tg01T2j13Tg01TWj17Tg01knj22Tg01mFj2ATg00F6j2BTg01n@j1@Tg01f<j1>Tg01Naj1=Tg01e9j10Tg01]8j2;Tg00FSj2CTg01n^j28Tg01\>j2:Tg00<Xj4ITg00:<j4HTg01Mgj1FTg01oVj26Tg01i=j25Tg018Uj11Tg006oj39Tg00G1j2<Tg020Vj2DTg00g<j7GTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FGp=4g00ilR6%K4g00JBR7P7g006:g00KBR8g00jeR9P0g00k>R:CJP8P9g00kWP0P:g00l5R9EEg019MC?R8P7P6P5P7P6g01XJR;#3R<#3#7R=,22R>,A3R?g01e^R@'B#@%>3#=/2?%0;R?#3#0#7RA';'CP7P6183>%7;R;':%0<#0#3#0#0#7R<';R>g013>RBP0P:P9P0C?RCP0P0PCP0P:P9P0CICHR9121=R:182:/:;RD%F5RED4/65W0/53PCP9P:%0?#3#0#3#3#0#7R?PED4/65X0B/53n0100000020000P3n0100000020000P3n0100000020000#1%13R:39P5123=,A4R3/B@#@%>4#=/23/;A'CP7P7P7P6P5P7P61;D<PCP9f5RD/2=R<181</:;PED4/65X0B/52PCP9P<P?PED4/65X0B/52n0100000020000P2n0100000020000#1%12R2598P5P>P7P7P7P6P5PCP9f6/2=R=18D=/:;PED4/65X0B/51PCP9P=P?PED4/65X0B/51n0100000020000#1%11598P51<82R2P2n0110000020000b11<8:n0110000020000b1%14,<8n0110000020100b11D45#1%15598eX36X20P4P5O2W3X20o"). Qed.
Lemma s_groups_account_bounce sc st : s_groups (account_bounce sc st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;4p;6p;2p;3p;7g01jnj1KTg00b9j4JTg00bWj6ETg00Ebj4?Tg01T2j13Tg01TWj17Tg01knj22Tg01mFj2ATg00F6j2BTg01n@j1@Tg01f<j1>Tg01Naj1=Tg01e9j10Tg01]8j2;Tg00FSj2CTg01n^j28Tg01\>j2:Tg00<Xj4ITg00:<j4HTg01Mgj1FTg01oVj26Tg01i=j25Tg01:Dj11Tg006oj39Tg00G1j2<Tg020Vj2DTg00g<j7GTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FGp=4g00ilR6%K4g00JBR7P7g006:g00KBR8g00jeR9P0g00k>R:CJP8P9g00kWP0P:g00l5R9EEg01;=C?R8P7P6P5P7P6g01XJR;#3R<#3#7R=,22R>,A3R?g01e^R@'B#@%>3#=/2?%0;R?#3#0#7RA';'CP7P6183>%7;R;':%0<#0#3#0#0#7R<';R>g013>RBP0P:P9P0C?RCP0P0PCP0P:P9P0CICHR9121=R:182:/:;RD%F5RED4/65W0/53PCP9P:%0?#3#0#3#3#0#7R?PED4/65X0B/53n0100000020000P3n0100000020000P3n0100000020000#1%13R:39P5123=,A4R3/B@#@%>4#=/23/;A'CP7P7P7P6P5P7P61;D<PCP9f5RD/2=R<181</:;PED4/65X0B/52PCP9P<P?PED4/65X0B/52n0100000020000P2n0100000020000#1%12R2598P5P>P7P7P7P6P5PCP9f6/2=R=18D=/:;PED4/65X0B/51PCP9P=P?PED4/65X0B/51n0100000020000#1%11598P51<82R2P2n0110000020000b11<8:n0110000020000b1%14,<8n0110000020100b11D45#1%15598eX36X20P4P5O2W3X20o"). Qed.
Lemma s_slots_account_bounce sc st : s_slots (account_bounce sc st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;4p;6p;2p;3p;7g01jnj1LTg00b9j4KTg00bWj6GTg00Ubj2DTg00Ebj4CTg01T2j13Tg01TWj17Tg01knj22Tg01mFj2@Tg00F6j2ATg01n@j1?Tg01f<j1>Tg01Naj1=Tg01e9j11Tg01]8j2;Tg00FSj2BTg01n^j2:Tg01\>j29Tg00<Xj4JTg00:<j4ITg01Mgj1HTg01oVj25Tg01i=j24Tg01<4j10Tg006oj38Tg00G1j2<Tg020Vj2FTg00g<j7ETg00K`R0P0f4R1f3R2f2R3f1R4f0R5FEp=6g00ilR6%L4g00JBR7P7g006:R8g00KBR9g00jeR:P0g00k>R;CKP9P:g00kWP0P;g00l5R:EG1D80CCR8P7P6P5P7P6g01XJR9#3R<#3#7R=,22R>,@3R?g01e^R@'A#?%>3#=/2?%19R?#3#1#7RA';'BP7P61:3>%79R9'9%1<#1#3#1#1#7R<';R>g013>RBP0P;P:P0CCRCP0P0PCP0P;P:P0CJCIR:121=R;1:2;/99RD%H5RED6/55W0/43PCP:P;%1?#3#1#3#3#1#7R?PED6/55X0B/43n0100000020000P3n0100000020000P3n0100000020000#0%03R;38P5123=,@4R3/A@#?%>4#=/23/;A'BP7P7P7P6P5P7P61;D<PCP:f5RD/2=R<1:1</99PED6/55X0B/42PCP:P<P?PED6/55X0B/42n0100000020000P2n0100000020000#0%02R2588P5P>P7P7P7P6P5PCP:f6/2=R=1:D=/99PED6/55X0B/41PCP:P=P?PED6/55X0B/41n0100000020000#0%01588P51<82R2P2n0110000020000b11<8;n0110000020000b1%04,<8n0110000020100b11F45#0%05588eX36X20P4P5O2W3X20o"). Qed.
Lemma s_tick_account_bounce sc st : s_tick (account_bounce sc st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1ITg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1>Tg01Naj1ATg01e9j10Tg01]8j29Tg00FSj2=Tg01n^j2:Tg01\>j2;Tg00Ebj4HTg00<Xj4GTg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg01<lj11Tg006oj38Tg00G1j2<Tg020Vj2DTg00g<j7CTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5g00ilR6%I4g00JBR7P7g00KBR8P7P6P5P7P6g01XJR9#3R:#3#7R;,22R<,B3R=g01e^R>'@#?%>3#A/2=%09R=#3#0#7R?'9'=P7P61:3<%79R9';%0:#0#3#0#0#7R:'9R<g013>R@P0g00k>RAg00l5RBP0CHRCP0P0PCP0PAPBP0CGCFRB121;RA1:2A/;9RD%E5RED5/65W0/43PCPBPA%0=#3#0#3#3#0#7R=PED5/65X0@/43n0100000020000P3n0100000020000P3n0100000020000#1%13RA38P5123;,B4R3/@>#?%>4#A/23/9?'=P7P7P7P6P5P7P619D:PCPBf5RD/2;R:1:1:/;9PED5/65X0@/42PCPBP:P=PED5/65X0@/42n0100000020000P2n0100000020000#1%12R2588P5P<P7P7P7P6P5PCPBf6/2;R;1:D;/;9PED5/65X0@/41PCPBP;P=PED5/65X0@/41n0100000020000#1%11588P51<82R2P2n0110000020000b11<8An0110000020000b1%14,<8n0110000020100b11D45#1%15588eX36X20P4P5O2W3X20o"). Qed.
Lemma s_secret_account_bounce sc st : s_secret (account_bounce sc st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1ITg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1>Tg01Naj1ATg01e9j10Tg01]8j29Tg00FSj2=Tg01n^j2:Tg01\>j2;Tg00Ebj4HTg00<Xj4GTg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg01=cj11Tg006oj38Tg00G1j2<Tg020Vj2DTg00g<j7CTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5g00ilR6%I4g00JBR7P7P7P6P5P7P6g01XJR8#3R9#3#7R:,22R;,B3R<g01e^R='@#?%>3#A/2<%08R<#3#0#7R>'9'=P7P61:3;%78R8';%09#0#3#0#0#7R9'9R;g013>R?P0g00k>R@g00l5RAP0CHRBP0P0PBP0P@PAP0CGCFRA121:R@1:2@/;8RC%E5RDD5/65W0/43PBPAP@%0<#3#0#3#3#0#7R<PDD5/65X0?/43n0100000020000P3n0100000020000P3n0100000020000#1%13R@580P5123:,B4R3/@=#?%>4#A/23/9>'=P7P7P7P6P5P7P619C9PBPAf5RC/2:R91:19/;8PDD5/65X0?/42PBPAP9P<PDD5/65X0?/42n0100000020000P2n0100000020000#1%12R2580P5P;P7P7P7P6P5PBPAf6/2:R:1:C:/;8PDD5/65X0?/41PBPAP:P<PDD5/65X0?/41n0100000020000#1%11580P51<02R2P2n0110000020000b11<0@n0110000020000b1%14,<0n0110000020100b11D45#1%15580eX36X20P4P5O2W3X20o"). Qed.
Lemma s_reserved_account_bounce sc st : s_reserved (account_bounce sc st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1KTg00Ubj2JTg01>\j1DTg01T2j13Tg01TWj17Tg01knj22Tg01mFj2@Tg00F6j2?Tg01n@j1ATg01f<j1>Tg01Naj1=Tg01e9j11Tg01]8j28Tg00FSj2BTg01n^j2;Tg01\>j29Tg00Ebj4ITg00<Xj4HTg00:<j4FTg01Mgj1ETg01oVj25Tg01i=j26Tg01?<j10Tg006oj3:Tg00G1j2<Tg020Vj2CTg00g<j7GTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FGp=4g00ilR6%K4g00JBR7P71J00#DR8P7P6P5P7P6g01XJR9#3R:#3#7R;,22R<,@3R=g01e^R>'?#A%>3#=/2=%19R=#3#1#7R?'8'BP7P61;3<%79R9'9%1:#1#3#1#1#7R:'8R<g013>R@P0g00k>RAg00l5RBP0CIRCP0P0PCP0PAPBP0CHCFRB121;RA1;2A/99RD%E5RED4/55W0/63PCPBPA%1=#3#1#3#3#1#7R=PED4/55X0@/63n0100000020000P3n0100000020000P3n0100000020000#0%03RA3:P5123;,@4R3/?>#A%>4#=/23/8?'BP7P7P7P6P5P7P618D:PCPBf5RD/2;R:1;1:/99PED4/55X0@/62PCPBP:P=PED4/55X0@/62n0100000020000P2n0100000020000#0%02R25:8P5P<P7P7P7P6P5PCPBf6/2;R;1;D;/99PED4/55X0@/61PCPBP;P=PED4/55X0@/61n0100000020000#0%015:8P51<82R2P2n0110000020000b11<8An0110000020000b1%04,<8n0110000020100b11C45#0%055:8eX36X20P4P5O2W3X20o"). Qed.
Lemma s_atop_account_bounce sc st : s_atop (account_bounce sc st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1ITg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1>Tg01Naj1ATg01e9j10Tg01]8j29Tg00FSj2=Tg01n^j2:Tg01\>j2;Tg00Ebj4HTg00<Xj4GTg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg01@7j11Tg006oj38Tg00G1j2<Tg020Vj2DTg00g<j7CTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5g00ilR6%I4g00JBR7P7P7P6P5P7P6g01XJR8#3R9#3#7R:,22R;,B3R<g01e^R='@#?%>3#A/2<%08R<#3#0#7R>'9'=P7P61:3;%78R8';%09#0#3#0#0#7R9'9R;g013>R?P0g00k>R@g00l5RAP0CHRBP0P0PBP0P@PAP0CGCFRA121:R@1:2@/;8RC%E5RDD5/65W0/43PBPAP@%0<#3#0#3#3#0#7R<PDD5/65X0?/43n0100000020000P3n0100000020000P3n0100000020000#1%13R@580P5123:,B4R3/@=#?%>4#A/23/9>'=P7P7P7P6P5P7P619C9PBPAf5RC/2:R91:19/;8PDD5/65X0?/42PBPAP9P<PDD5/65X0?/42n0100000020000P2n0100000020000#1%12R2580P5P;P7P7P7P6P5PBPAf6/2:R:1:C:/;8PDD5/65X0?/41PBPAP:P<PDD5/65X0?/41n0100000020000#1%11580P51<02R2P2n0110000020000b11<0@n0110000020000b1%14,<0n0110000020100b11D45#1%15580eX36X20P4P5O2W3X20o"). Qed.
Lemma s_regions_decay_bounces sc st : s_regions (decay_bounces sc st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1BTg01T2j14Tg01TWj13Tg01knj21Tg01n^j26Tg00F6j2=Tg01n@j1<Tg00FSj2;Tg00Ebj42Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2ATg01i=j2@Tg0145j10Tg006oj35Tg00G1j2>Tg021Uj2?Tg00K`R0g00ilR1f1R2#Bf0R3g01XJR4#4#4#3R5,12'6g01e^'=#<';g00JBR6P6g00KBg00jeg00kWg014oC2R7P6P1P3g013>P0P0P0g00k>R6g00l5R8P0C2R9P0P0P9P0P6P8P0C:C7f4/15R5f3/65%34'1%83F9/A3W3f2R4'@P4n0100000020000#0%0435P3%02,>7R4P4n0110000020000b21?23#0%03557eX11X00P2P3O2W1W0o"). Qed.
Lemma s_shadow_decay_bounces sc st : s_shadow (decay_bounces sc st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1BTg01T2j14Tg01TWj13Tg01knj21Tg01n^j26Tg00F6j2=Tg01n@j1<Tg00FSj2;Tg00Ebj42Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2ATg01i=j2@Tg015hj10Tg006oj35Tg00G1j2>Tg021Uj2?Tg00K`R0g00ilR1f1R2#Bf0R3g01XJR4#4#4#3R5,12'6g01e^'=#<';g00JBR6P6g00KBg00jeg00kWg016aC2R7P6P1P3g013>P0P0P0g00k>R6g00l5R8P0C2R9P0P0P9P0P6P8P0C:C7f4/15R5f3/65%34'1%83F9/A3W3f2R4'@P4n0100000020000#0%0435P3%02,>7R4P4n0110000020000b21?23#0%03557eX11X00P2P3O2W1W0o"). Qed.
Lemma s_next_rid_decay_bounces sc st : s_next_rid (decay_bounces sc st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1BTg01T2j13Tg01TWj12Tg01knj21Tg01n^j25Tg00F6j2=Tg01n@j1<Tg00FSj2;Tg00Ebj4:Tg00<Xj47Tg00:<j46Tg01Mgj18Tg00g<j79Tg01oVj2ATg01i=j2@Tg017Zj10Tg006oj34Tg00G1j2>Tg021Uj2?Tg00K`R0g00ilR1f1R2#Bf0R3g01XJR4#3#3#2R5,12'5g01e^'=#<';g00JBR6P6g00KBR7P6P1P3g013>P0P0P0g00k>R6g00l5R8P0C:R9P0P0P9P0P6P8P0C7C6f4/15R5f3/55%24'1%83F9/A3W3f2R4'@P4n0100000020000#0%0434P3%02,>7R4P4n0110000020000b21?23#0%03547eX11X00P2P3O2W1W0o"). Qed.
Lemma s_metas_decay_bounces sc st : s_metas (decay_bounces sc st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;6p;7p;3g01jnj1DTg01T2j13Tg01TWj12Tg01knj21Tg01n^j26Tg00F6j2>Tg01n@j1<Tg00FSj2;Tg00b9j4:Tg00bWj68Tg00Ebj44Tg00<Xj47Tg00:<j49Tg01Mgj1CTg00g<j7BTg01oVj2ATg01i=j2=Tg00c8j10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Df0R3g01XJR4#3#3#2R5,12'6g01e^'>#<';g00JBR6P6g006:g00KBR7g00jeR8P0g00k>R9C:P7P8g00kWP0P9g00l5R8E8g00h?C4R7P6P1P3g013>P0P0P0P9P8P0C4R6P0P0P6P0P9P8P0C7C9f4/15R5f3/65%24'1%C3FB/A3W3f2R4'=P4n0100000020000#0%0435P3%02,?7R4P4n0110000020000b21@23#0%03557eX11X00P2P3O2W1W0o"). Qed.
Lemma s_areas_decay_bounces sc st : s_areas (decay_bounces sc st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;6p;7p;3g01jnj1DTg01T2j13Tg01TWj12Tg01knj21Tg01n^j26Tg00F6j2>Tg01n@j1<Tg00FSj2;Tg00b9j4:Tg00bWj68Tg00Ebj44Tg00<Xj47Tg00:<j49Tg01Mgj1CTg00g<j7BTg01oVj2ATg01i=j2=Tg018Uj10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Df0R3g01XJR4#3#3#2R5,12'6g01e^'>#<';g00JBR6P6g006:g00KBR7g00jeR8P0g00k>R9C:P7P8g00kWP0P9g00l5R8E8g019MC4R7P6P1P3g013>P0P0P0P9P8P0C4R6P0P0P6P0P9P8P0C7C9f4/15R5f3/65%24'1%C3FB/A3W3f2R4'=P4n0100000020000#0%0435P3%02,?7R4P4n0110000020000b21@23#0%03557eX11X00P2P3O2W1W0o"). Qed.
Lemma s_groups_decay_bounces sc st : s_groups (decay_bounces sc st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;6p;7p;3g01jnj1DTg01T2j13Tg01TWj12Tg01knj21Tg01n^j26Tg00F6j2>Tg01n@j1<Tg00FSj2;Tg00b9j4:Tg00bWj68Tg00Ebj44Tg00<Xj47Tg00:<j49Tg01Mgj1CTg00g<j7BTg01oVj2ATg01i=j2=Tg01:Dj10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Df0R3g01XJR4#3#3#2R5,12'6g01e^'>#<';g00JBR6P6g006:g00KBR7g00jeR8P0g00k>R9C:P7P8g00kWP0P9g00l5R8E8g01;=C4R7P6P1P3g013>P0P0P0P9P8P0C4R6P0P0P6P0P9P8P0C7C9f4/15R5f3/65%24'1%C3FB/A3W3f2R4'=P4n0100000020000#0%0435P3%02,?7R4P4n0110000020000b21@23#0%03557eX11X00P2P3O2W1W0o"). Qed.
Lemma s_slots_decay_bounces sc st : s_slots (decay_bounces sc st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;6p;7p;3g01jnj1ETg01T2j14Tg01TWj13Tg01knj21Tg01n^j26Tg00F6j2?Tg01n@j1<Tg00FSj2;Tg00b9j4:Tg00bWj68Tg00Ubj27Tg00Ebj42Tg00<Xj49Tg00:<j4DTg01Mgj1CTg00g<j7BTg01oVj2>Tg01i=j2=Tg01<4j10Tg006oj35Tg00G1j2@Tg021Uj2ATg00K`R0g00ilR1f1R2#Ef0R3g01XJR4#4#4#3R5,12'6g01e^'?#<';g00JBR6P6g006:R7g00KBR8g00jeR9P0g00k>R:C:P8P9g00kWP0P:g00l5R9E81770C2R7P6P1P3g013>P0P0P0P:P9P0C2R6P0P0P6P0P:P9P0C9CDf4/15R5f3/65%34'1%C3FB/>3W3f2R4'=P4n0100000020000#0%0435P3%02,@7R4P4n0110000020000b21A23#0%03557eX11X00P2P3O2W1W0o"). Qed.
Lemma s_tick_decay_bounces sc st : s_tick (decay_bounces sc st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1BTg01T2j13Tg01TWj12Tg01knj21Tg01n^j25Tg00F6j2=Tg01n@j1<Tg00FSj2;Tg00Ebj4:Tg00<Xj47Tg00:<j46Tg01Mgj18Tg00g<j79Tg01oVj2ATg01i=j2@Tg01<lj10Tg006oj34Tg00G1j2>Tg021Uj2?Tg00K`R0g00ilR1f1R2#Bf0R3g01XJR4#3#3#2R5,12'5g01e^'=#<';g00JBR6P6g00KBR7P6P1P3g013>P0P0P0g00k>R6g00l5R8P0C:R9P0P0P9P0P6P8P0C7C6f4/15R5f3/55%24'1%83F9/A3W3f2R4'@P4n0100000020000#0%0434P3%02,>7R4P4n0110000020000b21?23#0%03547eX11X00P2P3O2W1W0o"). Qed.
Lemma s_secret_decay_bounces sc st : s_secret (decay_bounces sc st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1BTg01T2j13Tg01TWj12Tg01knj21Tg01n^j25Tg00F6j2=Tg01n@j1<Tg00FSj2;Tg00Ebj4:Tg00<Xj47Tg00:<j46Tg01Mgj18Tg00g<j79Tg01oVj2ATg01i=j2@Tg01=cj10Tg006oj34Tg00G1j2>Tg021Uj2?Tg00K`R0g00ilR1f1R2#Bf0R3g01XJR4#3#3#2R5,12'5g01e^'=#<';g00JBR6P6P6P1P3g013>P0P0P0g00k>R6g00l5R7P0C:R8P0P0P8P0P6P7P0C7C6f4/15R5f3/55%24'1%83F9/A3W3f2R4'@P4n0100000020000#0%04540P3%02,>0R4P4n0110000020000b21?23#0%03540eX11X00P2P3O2W1W0o"). Qed.
Lemma s_reserved_decay_bounces sc st : s_reserved (decay_bounces sc st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1DTg01T2j13Tg01TWj12Tg01knj21Tg01n^j25Tg00F6j2>Tg01n@j1<Tg00FSj2;Tg00Ubj2:Tg01>\j17Tg00Ebj46Tg00<Xj48Tg00:<j49Tg01Mgj1CTg00g<j7BTg01oVj2ATg01i=j2=Tg01?<j10Tg006oj34Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Df0R3g01XJR4#3#3#2R5,12'5g01e^'>#<';g00JBR6P61:00#7R7P6P1P3g013>P0P0P0g00k>R6g00l5R8P0C6R9P0P0P9P0P6P8P0C8C9f4/15R5f3/55%24'1%C3FB/A3W3f2R4'=P4n0100000020000#0%0434P3%02,?7R4P4n0110000020000b21@23#0%03547eX11X00P2P3O2W1W0o"). Qed.
Lemma s_atop_decay_bounces sc st : s_atop (decay_bounces sc st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1BTg01T2j13Tg01TWj12Tg01knj21Tg01n^j25Tg00F6j2=Tg01n@j1<Tg00FSj2;Tg00Ebj4:Tg00<Xj47Tg00:<j46Tg01Mgj18Tg00g<j79Tg01oVj2ATg01i=j2@Tg01@7j10Tg006oj34Tg00G1j2>Tg021Uj2?Tg00K`R0g00ilR1f1R2#Bf0R3g01XJR4#3#3#2R5,12'5g01e^'=#<';g00JBR6P6P6P1P3g013>P0P0P0g00k>R6g00l5R7P0C:R8P0P0P8P0P6P7P0C7C6f4/15R5f3/55%24'1%83F9/A3W3f2R4'@P4n0100000020000#0%04540P3%02,>0R4P4n0110000020000b21?23#0%03540eX11X00P2P3O2W1W0o"). Qed.
Lemma s_regions_set_head h v st : s_regions (set_head h v st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01hh12sth21vh32sci002sci011lp;4p;3p;1p;2g00Ebj44Tg022Sj33Tg0145j10Tg006oj32Tg00G1j21Tg023LR0g00BLR1g00ilR2P0g00KBg00jeg00kWg014oC4R3f0R4f2R5f1R633#0%0632P5g00K`%05,13W3P4O1%04,13n0110100021010000X12X21X00P5P6P4O3W1W2W0o"). Qed.
Lemma s_shadow_set_head h v st : s_shadow (set_head h v st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01hh12sth21vh32sci002sci011lp;4p;3p;1p;2g00Ebj44Tg022Sj33Tg015hj10Tg006oj32Tg00G1j21Tg023LR0g00BLR1g00ilR2P0g00KBg00jeg00kWg016aC4R3f0R4f2R5f1R633#0%0632P5g00K`%05,13W3P4O1%04,13n0110100021010000X12X21X00P5P6P4O3W1W2W0o"). Qed.
Lemma s_next_rid_set_head h v st : s_next_rid (set_head h v st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01hh12sth21vh32sci002sci011lp;3p;1p;2g022Sj33Tg017Zj10Tg006oj32Tg00G1j21Tg023LR0g00BLR1g00ilR2P0g00KBR3f0R4f2R5f1R633#0%0632P5g00K`%05,13W3P4O1%04,13n0110100021010000X12X21X00P5P6P4O3W1W2W0o"). Qed.
Lemma s_metas_set_head h v st : s_metas (set_head h v st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01hh12sth21vh32sci002sci011lp;4p;6p;3p;1p;2g00b9j46Tg00bWj65Tg00Ebj43Tg022Sj32Tg00c8j10Tg006oj34Tg00G1j21Tg023LR0g00BLR1g00ilR2P0g006:g00KBR3g00jeR4g00K`R5g00k>R6C6P3P4g00kWP5P6g00l5E5g00h?C3R6f0R4f2R3f1R732#0%0734P3%03,16X35P4O1%04,16n0110100021010000X12X21X00P3P7P4O3W1W2W0o"). Qed.
Lemma s_areas_set_head h v st : s_areas (set_head h v st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01hh12sth21vh32sci002sci011lp;4p;6p;3p;1p;2g00b9j46Tg00bWj65Tg00Ebj43Tg022Sj32Tg018Uj10Tg006oj34Tg00G1j21Tg023LR0g00BLR1g00ilR2P0g006:g00KBR3g00jeR4g00K`R5g00k>R6C6P3P4g00kWP5P6g00l5E5g019MC3R6f0R4f2R3f1R732#0%0734P3%03,16X35P4O1%04,16n0110100021010000X12X21X00P3P7P4O3W1W2W0o"). Qed.
Lemma s_groups_set_head h v st : s_groups (set_head h v st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01hh12sth21vh32sci002sci011lp;4p;6p;3p;1p;2g00b9j46Tg00bWj65Tg00Ebj43Tg022Sj32Tg01:Dj10Tg006oj34Tg00G1j21Tg023LR0g00BLR1g00ilR2P0g006:g00KBR3g00jeR4g00K`R5g00k>R6C6P3P4g00kWP5P6g00l5E5g01;=C3R6f0R4f2R3f1R732#0%0734P3%03,16X35P4O1%04,16n0110100021010000X12X21X00P3P7P4O3W1W2W0o"). Qed.
Lemma s_slots_set_head h v st : s_slots (set_head h v st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01hh12sth21vh32sci002sci011lp;4p;6p;2p;3p;1g00b9j47Tg00bWj66Tg00Ubj23Tg00Ebj42Tg022Sj35Tg01<4j10Tg006oj34Tg00G1j21Tg023LR0g00BLR1g00ilR2P0g006:R3g00KBR4g00jeR5g00K`R6g00k>R7C7P4P5g00kWP6P7g00l5E61336C2R3f0R7f2R5f1R435#0%0434P5%05,13X36P7O1%07,13n0110100021010000X12X21X00P5P4P7O3W1W2W0o"). Qed.
Lemma s_tick_set_head h v st : s_tick (set_head h v st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01hh12sth21vh32sci002sci011lp;3p;1p;2g022Sj33Tg01<lj10Tg006oj32Tg00G1j21Tg023LR0g00BLR1g00ilR2P0g00KBR3f0R4f2R5f1R633#0%0632P5g00K`%05,13W3P4O1%04,13n0110100021010000X12X21X00P5P6P4O3W1W2W0o"). Qed.
Lemma s_secret_set_head h v st : s_secret (set_head h v st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01hh12sth21vh32sci002sci011lp;3p;1p;2g022Sj33Tg01=cj10Tg006oj32Tg00G1j21Tg023LR0g00BLR1g00ilR2P0g00K`R3f0R4f2R5f1R633#0%0632P5%05,13X33P4O1%04,13n0110100021010000X12X21X00P5P6P4O3W1W2W0o"). Qed.
Lemma s_reserved_set_head h v st : s_reserved (set_head h v st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01hh12sth21vh32sci002sci011lp;2p;1p;3g00Ubj25Tg01>\j14Tg022Sj32Tg01?<j10Tg006oj33Tg00G1j21Tg023LR0g00BLR1g00ilR2P0g00K`R3/53#4R4f0R5f2R6f1R732#0%0733P6%06,14X33P5O1%05,14n0110100021010000X12X21X00P6P7P5O3W1W2W0o"). Qed.
Lemma s_atop_set_head h v st : s_atop (set_head h v st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01hh12sth21vh32sci002sci011lp;3p;1p;2g022Sj33Tg01@7j10Tg006oj32Tg00G1j21Tg023LR0g00BLR1g00ilR2P0g00K`R3f0R4f2R5f1R633#0%0632P5%05,13X33P4O1%04,13n0110100021010000X12X21X00P5P6P4O3W1W2W0o"). Qed.
Lemma s_regions_dequeue h m st : s_regions (dequeue h m st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;4p;3g00f?j27Tg024Dj1:Tg00^@j2<Tg01n@j1FTg00Ebj4ETg00`=j1CTg025;j2?j15Tg0266j2>j19Tg0271j1;Tg00nPj31Tg022Sj32Tg0145j13Tg00G1j28Tg027hj3DTg00_[j2@Tg028`j2ATg006oj3=Tg006:R0f0R1'@p=4f2R2f1R3'A/<1p=6f4R4f3R5?123#3;=1p=0%33==21p=Bg023LR6g00ilR71713#:%43'<#Fg00JBR8P8g00KBg00jeg00kWg014oCER9P5g00h?%C0R:1?:1'>W8R;P8P7P1P8P7g00_9R<P0P71725R=#:R>1754R?#;R@#9P<P0P7P@f5R@,74#:RA#5=114RBP5n10110700021010600511P<P0P7%;=%:?R?#5=115P2n10110700021010600n10110700021010500R=%45RC764A24>=P=n0100000020000A24:2n0100000020000%32R=D0P11732#;g00BLRDP<P0P9P4P;P8P7P<P0P7P?%93P<P0P7P3f6RE,7@#:#5=11@P4n10110700021010600511P<P0P7P1PBP5n10110700021010600n10110700021010500RB%44RF76@A2@?BPBn0100000020000%35RBD0P1PAPDP<P0P9f7RAP;P8P7P<P0P7P1%9CRC%53=15A511%51=12En10110700021010500R?f8RG%4A36A2G1?P?n0100000020000%3ER?D0P1%41#5=15A911Cf9RC%4G36P8P8P9f:RHP;P8P7P1f;%42RI%4@RJ#9%5I=1@C512RK32PKn0100000020000%3CRLD0P1P6P9PHP;A21IKPLD0PHg00K`RM%3H,89W1P1O1RN%3G,89ROn0110400021010100P6P9PHP;PKPLD0PHPNPOn0110400021010100n0110000020000b0X70P1O1%5:RN=13@%4ERH76AP8P8P9PGP;P8P7P1A15NARN92C:PNn0100000020000%3ARLD0P1P6P9PGP;A21:NPLD0PGPOX1MP1O1RO189?R?n0110400021010100P6P9PGP;PNPLD0PGPOP?n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P>PDP<P0P9P@P;P8P7P<P0P7P1%9:R<=11@RDP4n10110700021010500R>?6EJA2E1>P>n0100000020000%34R4D0P1A6DAHP8P8P9PGP;P8P7P1A12<AR<92CIP<n0100000020000PLD0P1P6P9PGP;A21I<PLD0PGPOP?n0110400021010100P6P9PGP;P<PLD0PGPOP?n0110400021010100n0110000020000b0X30P1O1A65@FP8P8P9PEP;P8P7P1A2A:@P@n0100000020000%3@RAD0P1P6P9PEP;A21:@PAD0PEP?X1MP1O1R?1894R4n0110400021010100P6P9PEP;P@PAD0PEP?P4n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P9P5P;A21:2P=D0P5189BX1MP1O1%33,89n0110400021010100n0110000020100b0AD231%315B9eX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma s_shadow_dequeue h m st : s_shadow (dequeue h m st) = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;4p;3g00f?j27Tg024Dj1:Tg00^@j2<Tg01n@j1FTg00Ebj4ETg00`=j1CTg025;j2?j15Tg0266j2>j19Tg0271j1;Tg00nPj31Tg022Sj32Tg015hj13Tg00G1j28Tg027hj3DTg00_[j2@Tg028`j2ATg006oj3=Tg006:R0f0R1'@p=4f2R2f1R3'A/<1p=6f4R4f3R5?123#3;=1p=0%33==21p=Bg023LR6g00ilR71713#:%43'<#Fg00JBR8P8g00KBg00jeg00kWg016aCER9P5g00h?%C0R:1?:1'>W8R;P8P7P1P8P7g00_9R<P0P71725R=#:R>1754R?#;R@#9P<P0P7P@f5R@,74#:RA#5=114RBP5n10110700021010600511P<P0P7%;=%:?R?#5=115P2n10110700021010600n10110700021010500R=%45RC764A24>=P=n0100000020000A24:2n0100000020000%32R=D0P11732#;g00BLRDP<P0P9P4P;P8P7P<P0P7P?%93P<P0P7P3f6RE,7@#:#5=11@P4n10110700021010600511P<P0P7P1PBP5n10110700021010600n10110700021010500RB%44RF76@A2@?BPBn0100000020000%35RBD0P1PAPDP<P0P9f7RAP;P8P7P<P0P7P1%9CRC%53=15A511%51=12En10110700021010500R?f8RG%4A36A2G1?P?n0100000020000%3ER?D0P1%41#5=15A911Cf9RC%4G36P8P8P9f:RHP;P8P7P1f;%42RI%4@RJ#9%5I=1@C512RK32PKn0100000020000%3CRLD0P1P6P9PHP;A21IKPLD0PHg00K`RM%3H,89W1P1O1RN%3G,89ROn0110400021010100P6P9PHP;PKPLD0PHPNPOn0110400021010100n0110000020000b0X70P1O1%5:RN=13@%4ERH76AP8P8P9PGP;P8P7P1A15NARN92C:PNn0100000020000%3ARLD0P1P6P9PGP;A21:NPLD0PGPOX1MP1O1RO189?R?n0110400021010100P6P9PGP;PNPLD0PGPOP?n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P>PDP<P0P9P@P;P8P7P<P0P7P1%9:R<=11@RDP4n10110700021010500R>?6EJA2E1>P>n0100000020000%34R4D0P1A6DAHP8P8P9PGP;P8P7P1A12<AR<92CIP<n0100000020000PLD0P1P6P9PGP;A21I<PLD0PGPOP?n0110400021010100P6P9PGP;P<PLD0PGPOP?n0110400021010100n0110000020000b0X30P1O1A65@FP8P8P9PEP;P8P7P1A2A:@P@n0100000020000%3@RAD0P1P6P9PEP;A21:@PAD0PEP?X1MP1O1R?1894R4n0110400021010100P6P9PEP;P@PAD0PEP?P4n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P9P5P;A21:2P=D0P5189BX1MP1O1%33,89n0110400021010100n0110000020100b0AD231%315B9eX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma s_next_rid_dequeue h m st : s_next_rid (dequeue h m st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j27Tg024Dj1:Tg00^@j2<Tg01n@j1FTg00`=j1ETg025;j2Bj15Tg0266j2?j19Tg0271j1;Tg00nPj31Tg022Sj32Tg017Zj13Tg027hj3DTg00_[j2ATg028`j2@Tg006oj3=Tg00G1j2>Tg006:R0f0R1'Ap=4f2R2f1R3'@/<1p=6g00KBR4f3R5?123#3;=1p=01>41p=8%33==41p=Cg023LR4g00ilR61713#:%43'<#Fg00JBR7P7P5g00h?%E0R81B81'?W8R9P7P6P1P7P6g00_9R:P0P61725R;#:R<f4R=,75R>#;R?#9P:P0P6P?f5R?,7=#:R@#5=11=RAP5n10110700021010600511P:P0P6%;;%:>R>#5=115P2n10110700021010600n10110700021010500R;%45RB76=A2=<;P;n0100000020000A2=82n0100000020000%32R;C0P11732#;g00BLRCP:P0P=P9P7P6P:P0P6P>%93P:P0P6P3f6RD,7?#:#5=11?P=n10110700021010600511P:P0P6P1PAP5n10110700021010600n10110700021010500RA%4=RE76?A2?>APAn0100000020000%35RAC0P1P@PCP:P0f7R@P9P7P6P:P0P6P1%9BRB%53=15@511%51=12Dn10110700021010500R>f8RF%4@36A2F1>P>n0100000020000%3DR>C0P1%41#5=15@911Bf9RB%4F36P7P7f:RGP9P7P6P1f;%42RH%4?RI#9%5H=1?B512RJ32PJn0100000020000%3BRKC0P1P4PGP9A21HJPKC0PGg00K`RL%3G#8W1P1O1RM%3F#8RNn0110400021010100P4PGP9PJPKC0PGPMPNn0110400021010100n0110000020000b0X70P1O1%58RM=13?%4DRG76@P7P7PFP9P7P6P1A15M@RM92B8PMn0100000020000%3@RKC0P1P4PFP9A218MPKC0PFPNX1LP1O1RN%8>R>n0110400021010100P4PFP9PMPKC0PFPNP>n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P<PCP:P0P?P9P7P6P:P0P6P1%98R:=11?RCP=n10110700021010500R<?6DIA2D1<P<n0100000020000%3=R=C0P1A6C@GP7P7PFP9P7P6P1A12:@R:92BHP:n0100000020000PKC0P1P4PFP9A21H:PKC0PFPNP>n0110400021010100P4PFP9P:PKC0PFPNP>n0110400021010100n0110000020000b0X30P1O1A65?EP7P7PDP9P7P6P1A2@8?P?n0100000020000%3?R@C0P1P4PDP9A218?P@C0PDP>X1LP1O1R>%8=R=n0110400021010100P4PDP9P?P@C0PDP>P=n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P4P5P9A2182P;C0P5%8AX1LP1O1%33#8n0110400021010100n0110000020100b0AD231%31'CeX66X50X44P2P3P1O3W6X50W4o"). Qed.
Lemma s_areas_dequeue h m st : s_areas (dequeue h m st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;4p;6p;3g00f?j28Tg024Dj1:Tg00^@j2<Tg01n@j1HTg00b9j4GTg00bWj6FTg00Ebj4BTg00`=j1@Tg025;j2?j16Tg0266j2>j19Tg0271j1;Tg00nPj30Tg022Sj32Tg018Uj13Tg00G1j27Tg027hj3ETg00_[j2ATg028`j2CTg006oj3=Tg006:R0f0R1'Ap=4f2R2f1R3'C/<1p=5f4R4f3R5?023#3;=1p=1%33==21p=Dg023LR6g00ilR71813#:%43'<#Hg00JBR8P8P0g00KBR9g00jeR:g00K`R;g00k>R<CGP9P:g00kWP;P<g00l5EFg019MCBR<P5g00h?%@0R:1?:1'>W8R9P8P7P1P8P7g00_9R=P0P71825R>#:R?1854R@#;RA#9P=P0P7PAf5RA,84#:RB#6=014RCP5n10110700021010600501P=P0P7%;>%:@R@#6=015P2n10110700021010600n10110700021010500R>%45RD754A24?>P>n0100000020000A24:2n0100000020000%32R>D1P11832#;g00BLREP=P0P<P4P9P8P7P=P0P7P@%93P=P0P7P3f6RF,8A#:#6=01AP4n10110700021010600501P=P0P7P1PCP5n10110700021010600n10110700021010500RC%44RG75AA2A@CPCn0100000020000%35RCD1P1PBPEP=P0P<f7RBP9P8P7P=P0P7P1%9DRD%63=05B501%61=02Fn10110700021010500R@f8RH%4B35A2H1@P@n0100000020000%3FR@D1P1%41#6=05B901Df9RD%4H35P8P8P<f:RIP9P8P7P1f;%42RJ%4ARK#9%6J=0AD502RL32PLn0100000020000%3DRMD1P1P6P<PIP9A21JLPMD1PI%3I,7<X1;P1O1RN%3H,7<ROn0110400021010100P6P<PIP9PLPMD1PIPNPOn0110400021010100n0110000020000b0X70P1O1%6:RN=03A%4FRI75BP8P8P<PHP9P8P7P1A05NBRN92D:PNn0100000020000%3BRMD1P1P6P<PHP9A21:NPMD1PHPOX1;P1O1RO17<@R@n0110400021010100P6P<PHP9PNPMD1PHPOP@n0110400021010100n0110000020000b0n10110200021110300b2X30P1O1P?PEP=P0P<PAP9P8P7P=P0P7P1%9:R==01AREP4n10110700021010500R??5FKA2F1?P?n0100000020000%34R4D1P1A5EBIP8P8P<PHP9P8P7P1A02=BR=92DJP=n0100000020000PMD1P1P6P<PHP9A21J=PMD1PHPOP@n0110400021010100P6P<PHP9P=PMD1PHPOP@n0110400021010100n0110000020000b0X30P1O1A55AGP8P8P<PFP9P8P7P1A2B:APAn0100000020000%3ARBD1P1P6P<PFP9A21:APBD1PFP@X1;P1O1R@17<4R4n0110400021010100P6P<PFP9PAPBD1PFP@P4n0110400021010100n0110000020000b0n10110200021110300b2n10110200021110301b2P6P<P5P9A21:2P>D1P517<CX1;P1O1%33,7<n0110400021010100n0110000020100b0AE231%315D<eX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma s_groups_dequeue h m st : s_groups (dequeue h m st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;4p;6p;3g00f?j28Tg024Dj1:Tg00^@j2<Tg01n@j1HTg00b9j4GTg00bWj6FTg00Ebj4BTg00`=j1@Tg025;j2?j16Tg0266j2>j19Tg0271j1;Tg00nPj30Tg022Sj32Tg01:Dj13Tg00G1j27Tg027hj3ETg00_[j2ATg028`j2CTg006oj3=Tg006:R0f0R1'Ap=4f2R2f1R3'C/<1p=5f4R4f3R5?023#3;=1p=1%33==21p=Dg023LR6g00ilR71813#:%43'<#Hg00JBR8P8P0g00KBR9g00jeR:g00K`R;g00k>R<CGP9P:g00kWP;P<g00l5EFg01;=CBR<P5g00h?%@0R:1?:1'>W8R9P8P7P1P8P7g00_9R=P0P71825R>#:R?1854R@#;RA#9P=P0P7PAf5RA,84#:RB#6=014RCP5n10110700021010600501P=P0P7%;>%:@R@#6=015P2n10110700021010600n10110700021010500R>%45RD754A24?>P>n0100000020000A24:2n0100000020000%32R>D1P11832#;g00BLREP=P0P<P4P9P8P7P=P0P7P@%93P=P0P7P3f6RF,8A#:#6=01AP4n10110700021010600501P=P0P7P1PCP5n10110700021010600n10110700021010500RC%44RG75AA2A@CPCn0100000020000%35RCD1P1PBPEP=P0P<f7RBP9P8P7P=P0P7P1%9DRD%63=05B501%61=02Fn10110700021010500R@f8RH%4B35A2H1@P@n0100000020000%3FR@D1P1%41#6=05B901Df9RD%4H35P8P8P<f:RIP9P8P7P1f;%42RJ%4ARK#9%6J=0AD502RL32PLn0100000020000%3DRMD1P1P6P<PIP9A21JLPMD1PI%3I,7<X1;P1O1RN%3H,7<ROn0110400021010100P6P<PIP9PLPMD1PIPNPOn0110400021010100n0110000020000b0X70P1O1%6:RN=03A%4FRI75BP8P8P<PHP9P8P7P1A05NBRN92D:PNn0100000020000%3BRMD1P1P6P<PHP9A21:NPMD1PHPOX1;P1O1RO17<@R@n0110400021010100P6P<PHP9PNPMD1PHPOP@n0110400021010100n0110000020000b0n10110200021110300b2X30P1O1P?PEP=P0P<PAP9P8P7P=P0P7P1%9:R==01AREP4n10110700021010500R??5FKA2F1?P?n0100000020000%34R4D1P1A5EBIP8P8P<PHP9P8P7P1A02=BR=92DJP=n0100000020000PMD1P1P6P<PHP9A21J=PMD1PHPOP@n0110400021010100P6P<PHP9P=PMD1PHPOP@n0110400021010100n0110000020000b0X30P1O1A55AGP8P8P<PFP9P8P7P1A2B:APAn0100000020000%3ARBD1P1P6P<PFP9A21:APBD1PFP@X1;P1O1R@17<4R4n0110400021010100P6P<PFP9PAPBD1PFP@P4n0110400021010100n0110000020000b0n10110200021110300b2n10110200021110301b2P6P<P5P9A21:2P>D1P517<CX1;P1O1%33,7<n0110400021010100n0110000020100b0AE231%315D<eX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma s_slots_dequeue h m st : s_slots (dequeue h m st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;4p;6p;3g00f?j28Tg024Dj1:Tg00^@j2<Tg01n@j1ITg00b9j4HTg00bWj6GTg00Ubj2CTg00Ebj4ATg00`=j1@Tg025;j2?j16Tg0266j2>j19Tg0271j1;Tg00nPj30Tg022Sj32Tg01<4j13Tg00G1j27Tg027hj3FTg00_[j2DTg028`j2ETg006oj3=Tg006:R0f0R1'Dp=4f2R2f1R3'E/<1p=5f4R4f3R5?023#3;=1p=1%33==21p=Bg023LR6g00ilR71813#:%43'<#Ig00JBR8P8P0g00KBR9g00jeR:g00K`R;g00k>R<CHP9P:g00kWP;P<g00l5EG1C0;CAR<P5g00h?%@0R:1?:1'>W8R9P8P7P1P8P7g00_9R=P0P71825R>#:R?1854R@#;RA#9P=P0P7PAf5RA,84#:RB#6=014RCP5n10110700021010600501P=P0P7%;>%:@R@#6=015P2n10110700021010600n10110700021010500R>%45RD754A24?>P>n0100000020000A24:2n0100000020000%32R>D1P11832#;g00BLREP=P0P<P4P9P8P7P=P0P7P@%93P=P0P7P3f6RF,8A#:#6=01AP4n10110700021010600501P=P0P7P1PCP5n10110700021010600n10110700021010500RC%44RG75AA2A@CPCn0100000020000%35RCD1P1PBPEP=P0P<f7RBP9P8P7P=P0P7P1%9DRD%63=05B501%61=02Fn10110700021010500R@f8RH%4B35A2H1@P@n0100000020000%3FR@D1P1%41#6=05B901Df9RD%4H35P8P8P<f:RIP9P8P7P1f;%42RJ%4ARK#9%6J=0AD502RL32PLn0100000020000%3DRMD1P1P6P<PIP9A21JLPMD1PI%3I,7<X1;P1O1RN%3H,7<ROn0110400021010100P6P<PIP9PLPMD1PIPNPOn0110400021010100n0110000020000b0X70P1O1%6:RN=03A%4FRI75BP8P8P<PHP9P8P7P1A05NBRN92D:PNn0100000020000%3BRMD1P1P6P<PHP9A21:NPMD1PHPOX1;P1O1RO17<@R@n0110400021010100P6P<PHP9PNPMD1PHPOP@n0110400021010100n0110000020000b0n10110200021110301b2X30P1O1P?PEP=P0P<PAP9P8P7P=P0P7P1%9:R==01AREP4n10110700021010500R??5FKA2F1?P?n0100000020000%34R4D1P1A5EBIP8P8P<PHP9P8P7P1A02=BR=92DJP=n0100000020000PMD1P1P6P<PHP9A21J=PMD1PHPOP@n0110400021010100P6P<PHP9P=PMD1PHPOP@n0110400021010100n0110000020000b0X30P1O1A55AGP8P8P<PFP9P8P7P1A2B:APAn0100000020000%3ARBD1P1P6P<PFP9A21:APBD1PFP@X1;P1O1R@17<4R4n0110400021010100P6P<PFP9PAPBD1PFP@P4n0110400021010100n0110000020000b0n10110200021110300b2n10110200021110301b2P6P<P5P9A21:2P>D1P517<CX1;P1O1%33,7<n0110400021010100n0110000020100b0AF231%315B<eX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma s_tick_dequeue h m st : s_tick (dequeue h m st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j27Tg024Dj1:Tg00^@j2<Tg01n@j1FTg00`=j1ETg025;j2Bj15Tg0266j2?j19Tg0271j1;Tg00nPj31Tg022Sj32Tg01<lj13Tg027hj3DTg00_[j2ATg028`j2@Tg006oj3=Tg00G1j2>Tg006:R0f0R1'Ap=4f2R2f1R3'@/<1p=6g00KBR4f3R5?123#3;=1p=01>41p=8%33==41p=Cg023LR4g00ilR61713#:%43'<#Fg00JBR7P7P5g00h?%E0R81B81'?W8R9P7P6P1P7P6g00_9R:P0P61725R;#:R<f4R=,75R>#;R?#9P:P0P6P?f5R?,7=#:R@#5=11=RAP5n10110700021010600511P:P0P6%;;%:>R>#5=115P2n10110700021010600n10110700021010500R;%45RB76=A2=<;P;n0100000020000A2=82n0100000020000%32R;C0P11732#;g00BLRCP:P0P=P9P7P6P:P0P6P>%93P:P0P6P3f6RD,7?#:#5=11?P=n10110700021010600511P:P0P6P1PAP5n10110700021010600n10110700021010500RA%4=RE76?A2?>APAn0100000020000%35RAC0P1P@PCP:P0f7R@P9P7P6P:P0P6P1%9BRB%53=15@511%51=12Dn10110700021010500R>f8RF%4@36A2F1>P>n0100000020000%3DR>C0P1%41#5=15@911Bf9RB%4F36P7P7f:RGP9P7P6P1f;%42RH%4?RI#9%5H=1?B512RJ32PJn0100000020000%3BRKC0P1P4PGP9A21HJPKC0PGg00K`RL%3G#8W1P1O1RM%3F#8RNn0110400021010100P4PGP9PJPKC0PGPMPNn0110400021010100n0110000020000b0X70P1O1%58RM=13?%4DRG76@P7P7PFP9P7P6P1A15M@RM92B8PMn0100000020000%3@RKC0P1P4PFP9A218MPKC0PFPNX1LP1O1RN%8>R>n0110400021010100P4PFP9PMPKC0PFPNP>n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P<PCP:P0P?P9P7P6P:P0P6P1%98R:=11?RCP=n10110700021010500R<?6DIA2D1<P<n0100000020000%3=R=C0P1A6C@GP7P7PFP9P7P6P1A12:@R:92BHP:n0100000020000PKC0P1P4PFP9A21H:PKC0PFPNP>n0110400021010100P4PFP9P:PKC0PFPNP>n0110400021010100n0110000020000b0X30P1O1A65?EP7P7PDP9P7P6P1A2@8?P?n0100000020000%3?R@C0P1P4PDP9A218?P@C0PDP>X1LP1O1R>%8=R=n0110400021010100P4PDP9P?P@C0PDP>P=n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P4P5P9A2182P;C0P5%8AX1LP1O1%33#8n0110400021010100n0110000020100b0AD231%31'CeX66X50X44P2P3P1O3W6X50W4o"). Qed.
Lemma s_secret_dequeue h m st : s_secret (dequeue h m st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j27Tg024Dj1:Tg00^@j2<Tg01n@j1FTg00`=j1ETg025;j2Bj15Tg0266j2?j19Tg0271j1;Tg00nPj31Tg022Sj32Tg01=cj13Tg027hj3DTg00_[j2ATg028`j2@Tg006oj3=Tg00G1j2>Tg006:R0f0R1'Ap=4f2R2f1R3'@/<1p=6g00K`R4f3R5?123#3;=1p=01>41p=8%33==41p=Cg023LR6g00ilR71713#:%43'<#Fg00JBR8P8P5g00h?%E0R91B91'?W8R:P8P7P1P8P7g00_9R;P0P71725R<#:R=f4R>,75R?#;R@#9P;P0P7P@f5R@,7>#:RA#5=11>RBP5n10110700021010600511P;P0P7%;<%:?R?#5=115P2n10110700021010600n10110700021010500R<%45RC76>A2>=<P<n0100000020000A2>92n0100000020000%32R<C0P11732#;g00BLRDP;P0P>P:P8P7P;P0P7P?%93P;P0P7P3f6RE,7@#:#5=11@P>n10110700021010600511P;P0P7P1PBP5n10110700021010600n10110700021010500RB%4>RF76@A2@?BPBn0100000020000%35RBC0P1PAPDP;P0f7RAP:P8P7P;P0P7P1%9CRC%53=15A511%51=12En10110700021010500R?f8RG%4A36A2G1?P?n0100000020000%3ER?C0P1%41#5=15A911Cf9RC%4G36P8P8f:RHP:P8P7P1f;%42RI%4@RJ#9%5I=1@C512RK32PKn0100000020000%3CRLC0P1P6PHP:A21IKPLC0PH%3H#8X14P1O1RM%3G#8RNn0110400021010100P6PHP:PKPLC0PHPMPNn0110400021010100n0110000020000b0X70P1O1%59RM=13@%4ERH76AP8P8PGP:P8P7P1A15MARM92C9PMn0100000020000%3ARLC0P1P6PGP:A219MPLC0PGPNX14P1O1RN%8?R?n0110400021010100P6PGP:PMPLC0PGPNP?n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P=PDP;P0P@P:P8P7P;P0P7P1%99R;=11@RDP>n10110700021010500R=?6EJA2E1=P=n0100000020000%3>R>C0P1A6DAHP8P8PGP:P8P7P1A12;AR;92CIP;n0100000020000PLC0P1P6PGP:A21I;PLC0PGPNP?n0110400021010100P6PGP:P;PLC0PGPNP?n0110400021010100n0110000020000b0X30P1O1A65@FP8P8PEP:P8P7P1A2A9@P@n0100000020000%3@RAC0P1P6PEP:A219@PAC0PEP?X14P1O1R?%8>R>n0110400021010100P6PEP:P@PAC0PEP?P>n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P5P:A2192P<C0P5%8BX14P1O1%33#8n0110400021010100n0110000020100b0AD231%31'CeX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma s_reserved_dequeue h m st : s_reserved (dequeue h m st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j28Tg024Dj1:Tg00^@j2<Tg01n@j1GTg00Ubj2FTg01>\j1ETg00`=j1ATg025;j2?j15Tg0266j2>j19Tg0271j1;Tg00nPj30Tg022Sj32Tg01?<j13Tg00G1j27Tg027hj3DTg00_[j2BTg028`j2@Tg006oj3=Tg006:R0f0R1'Bp=4f2R2f1R3'@/<1p=6f4R4f3R5?023#3;=1p=1%33==21p=Cg023LR6g00ilR71813#:%43'<#Gg00JBR8P8g00K`R9/F9#ER:P5g00h?%A0R;1?;1'>W8R<P8P7P1P8P7g00_9R=P0P71825R>#:R?1854R@#;RA#9P=P0P7PAf5RA,84#:RB#5=014RCP5n10110700021010600501P=P0P7%;>%:@R@#5=015P2n10110700021010600n10110700021010500R>%45RD764A24?>P>n0100000020000A24;2n0100000020000%32R>D1P11832#;g00BLREP=P0P:P4P<P8P7P=P0P7P@%93P=P0P7P3f6RF,8A#:#5=01AP4n10110700021010600501P=P0P7P1PCP5n10110700021010600n10110700021010500RC%44RG76AA2A@CPCn0100000020000%35RCD1P1PBPEP=P0P:f7RBP<P8P7P=P0P7P1%9DRD%53=05B501%51=02Fn10110700021010500R@f8RH%4B36A2H1@P@n0100000020000%3FR@D1P1%41#5=05B901Df9RD%4H36P8P8P:f:RIP<P8P7P1f;%42RJ%4ARK#9%5J=0AD502RL32PLn0100000020000%3DRMD1P1P6P:PIP<A21JLPMD1PI%3I,7:X19P1O1RN%3H,7:ROn0110400021010100P6P:PIP<PLPMD1PIPNPOn0110400021010100n0110000020000b0X70P1O1%5;RN=03A%4FRI76BP8P8P:PHP<P8P7P1A05NBRN92D;PNn0100000020000%3BRMD1P1P6P:PHP<A21;NPMD1PHPOX19P1O1RO17:@R@n0110400021010100P6P:PHP<PNPMD1PHPOP@n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P?PEP=P0P:PAP<P8P7P=P0P7P1%9;R==01AREP4n10110700021010500R??6FKA2F1?P?n0100000020000%34R4D1P1A6EBIP8P8P:PHP<P8P7P1A02=BR=92DJP=n0100000020000PMD1P1P6P:PHP<A21J=PMD1PHPOP@n0110400021010100P6P:PHP<P=PMD1PHPOP@n0110400021010100n0110000020000b0X30P1O1A65AGP8P8P:PFP<P8P7P1A2B;APAn0100000020000%3ARBD1P1P6P:PFP<A21;APBD1PFP@X19P1O1R@17:4R4n0110400021010100P6P:PFP<PAPBD1PFP@P4n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P:P5P<A21;2P>D1P517:CX19P1O1%33,7:n0110400021010100n0110000020100b0AD231%315C:eX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma s_atop_dequeue h m st : s_atop (dequeue h m st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j27Tg024Dj1:Tg00^@j2<Tg01n@j1FTg00`=j1ETg025;j2Bj15Tg0266j2?j19Tg0271j1;Tg00nPj31Tg022Sj32Tg01@7j13Tg027hj3DTg00_[j2ATg028`j2@Tg006oj3=Tg00G1j2>Tg006:R0f0R1'Ap=4f2R2f1R3'@/<1p=6g00K`R4f3R5?123#3;=1p=01>41p=8%33==41p=Cg023LR6g00ilR71713#:%43'<#Fg00JBR8P8P5g00h?%E0R91B91'?W8R:P8P7P1P8P7g00_9R;P0P71725R<#:R=f4R>,75R?#;R@#9P;P0P7P@f5R@,7>#:RA#5=11>RBP5n10110700021010600511P;P0P7%;<%:?R?#5=115P2n10110700021010600n10110700021010500R<%45RC76>A2>=<P<n0100000020000A2>92n0100000020000%32R<C0P11732#;g00BLRDP;P0P>P:P8P7P;P0P7P?%93P;P0P7P3f6RE,7@#:#5=11@P>n10110700021010600511P;P0P7P1PBP5n10110700021010600n10110700021010500RB%4>RF76@A2@?BPBn0100000020000%35RBC0P1PAPDP;P0f7RAP:P8P7P;P0P7P1%9CRC%53=15A511%51=12En10110700021010500R?f8RG%4A36A2G1?P?n0100000020000%3ER?C0P1%41#5=15A911Cf9RC%4G36P8P8f:RHP:P8P7P1f;%42RI%4@RJ#9%5I=1@C512RK32PKn0100000020000%3CRLC0P1P6PHP:A21IKPLC0PH%3H#8X14P1O1RM%3G#8RNn0110400021010100P6PHP:PKPLC0PHPMPNn0110400021010100n0110000020000b0X70P1O1%59RM=13@%4ERH76AP8P8PGP:P8P7P1A15MARM92C9PMn0100000020000%3ARLC0P1P6PGP:A219MPLC0PGPNX14P1O1RN%8?R?n0110400021010100P6PGP:PMPLC0PGPNP?n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P=PDP;P0P@P:P8P7P;P0P7P1%99R;=11@RDP>n10110700021010500R=?6EJA2E1=P=n0100000020000%3>R>C0P1A6DAHP8P8PGP:P8P7P1A12;AR;92CIP;n0100000020000PLC0P1P6PGP:A21I;PLC0PGPNP?n0110400021010100P6PGP:P;PLC0PGPNP?n0110400021010100n0110000020000b0X30P1O1A65@FP8P8PEP:P8P7P1A2A9@P@n0100000020000%3@RAC0P1P6PEP:A219@PAC0PEP?X14P1O1R?%8>R>n0110400021010100P6PEP:P@PAC0PEP?P>n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P5P:A2192P<C0P5%8BX14P1O1%33#8n0110400021010100n0110000020100b0AD231%31'CeX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma s_ctx_set_size p e n b3 st : s_ctx (set_size p e n b3 st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12b3h21eh31nh41ph52sti018reservedi023st2i031xp;1p;2p;3p;4p;5g01e9j1>Tg01T2j15Tg01TWj1=Tg01knj20Tg01[aj2FTg00UbR0j2ETg029Yj19Tg02:7j21Tg00F6j2<Tg01n@j1;Tg02:lj1:Tg02;Ij33Tg02<=j3ATg00SWj4@Tg01U5j2?Tg02=2j27Tg01\>j28Tg012Hj12Tg006oj36Tg00G1j2DTg02=Rj5CTg004Gj3BTg00KBg00K`R1f0R23Bp=4g006:R3g00ilR4g01XJR5#>R6#5R7#=R8f3R9#4f4R:#4R;'0f2R<'0'Fg00JBR=P=g013>R>P0P4P1P4P=1E41P2P4P1f5R0%97R7'1g01e^R?%>6#9R6,10%40R@f6RA#4RB'0/0:RCP=P41<C?#;%:C,10?3?<P<n0100000020000RD3A33P8C@P4P1PDPCC@n0100000020000f8%55R5#9RC'1%55#5#5#=R5,?01728'8f1RD33n2001103000120102101#2%2<RE36P210;@/09/<?#;R@P=P=f7R;/1CRC1?:5R51788'811A711A6%4;,0B/00R0P=P4P2%:0,1A?3?9P9n0100000020000RA3A73?33#2%29R?56>P21D>EREPEn0110000020000b0P@P=P=1708,85=3CA#2=6>?P2PEPEn0110000020000b0n0110000020000b0P:P9P<PDP2DC#2%2256>eX54X11X31X23X43P:P9P<PDP2O5W5X11X31X23W4o"). Qed.
Lemma s_regions_set_size p e n b3 st : s_regions (set_size p e n b3 st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12b3h21eh31nh41ph52sti018reservedi023st2i031xp;1p;2p;4p;3p;5g01e9j1=Tg01T2j15Tg01TWj1?Tg01knj21Tg01[aj2GTg00Ebj4FTg00UbR0j2CTg029Yj17Tg02:7j20Tg00F6j2<Tg01n@j1;Tg02:lj1:Tg02;Ij33Tg02<=j3ATg00SWj4@Tg01U5j2>Tg02=2j28Tg01\>j29Tg0145j12Tg006oj36Tg00G1j2ETg02=Rj5BTg004Gj3DTg00KBR1g00K`R2f0R33Dp=4g006:R4g00ilR5g01XJR6#=R7#5R8#?R9f3R:#4f4R;#4R<'1f2R='1'Gg00JBR>P>P1g00jeg00kWg014oCFR1P0P5P2P5P>1C52P3P5P2f5R0%78R8'0g01e^R?%=7#7R7,00%40R@f6RA#4RB'1/1;RCP>P51<C?#;%:C,00?3?=P=n0100000020000RD3A33P9C@P5P2PDPCC@n0100000020000f8%56R6#7RC'0%56#5#5#?R6,>01839'9f1RD33n2001103000120102101#2%2=RE36P311<@/1:/<?#;R@P>P>f7R</0CRC1>;6R61899'910A810A7%4<,1B/10R0P>P5P3%:0,0A?3?:P:n0100000020000RA3A73?33#2%2:R?561P31E1EREPEn0110000020000b0P@P>P>1809,96=3CA#2=61?P3PEPEn0110000020000b0n0110000020000b0P;P:P=PDP3DB#2%23561eX55X12X32X24X44P;P:P=PDP3O5W5X12X32X24W4o"). Qed.
Lemma s_next_rid_set_size p e n b3 st : s_next_rid (set_size p e n b3 st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12b3h21eh31nh41ph52sti018reservedi023st2i031xp;1p;2p;3p;4p;5g01e9j1>Tg01T2j15Tg01TWj1=Tg01knj20Tg01[aj2FTg00UbR0j2ETg029Yj19Tg02:7j21Tg00F6j2<Tg01n@j1;Tg02:lj1:Tg02;Ij33Tg02<=j3ATg00SWj4@Tg01U5j2?Tg02=2j27Tg01\>j28Tg017Zj12Tg006oj36Tg00G1j2DTg02=Rj5CTg004Gj3BTg00KBR1g00K`R2f0R33Bp=4g006:R4g00ilR5g01XJR6#>R7#5R8#=R9f3R:#4f4R;#4R<'0f2R='0'Fg00JBR>P>P0P5P2P5P>1E52P3P5P2f5R0%98R8'1g01e^R?%>7#9R7,10%40R@f6RA#4RB'0/0;RCP>P51<C?#;%:C,10?3?=P=n0100000020000RD3A33P9C@P5P2PDPCC@n0100000020000f8%56R6#9RC'1%56#5#5#=R6,?01739'8f1RD33n2001103000120102101#2%2=RE561P310<@/0:/<?#;R@P>P>f7R</1CRC1?;6R61799'811A811A7%4<,0B/00R0P>P5P3%:0,1A?3?:P:n0100000020000RA3A73?33#2%2:R?561P31D1EREPEn0110000020000b0P@P>P>1709,86=3CA#2=61?P3PEPEn0110000020000b0n0110000020000b0P;P:P=PDP3DC#2%23561eX55X12X32X24X44P;P:P=PDP3O5W5X12X32X24W4o"). Qed.
Lemma s_metas_set_size p e n b3 st : s_metas (set_size p e n b3 st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12b3h21eh31nh41ph52sti018reservedi023st2i031xp;1p;2p;4p;6p;3p;5g01e9j1;Tg01T2j15Tg01TWj1?Tg01knj21Tg01[aj2ITg00b9j4HTg00bWj6ETg00Ebj4CTg00UbR0j2BTg029Yj17Tg02:7j20Tg00F6j2:Tg01n@j1ATg02:lj1@Tg02;Ij33Tg02<=j3<Tg00SWj4=Tg01U5j2>Tg02=2j28Tg01\>j29Tg00c8j12Tg006oj36Tg00G1j2DTg02=Rj5FTg004Gj3GTg00KBR1g00K`R2f0R33Gp=4g006:R4g00ilR5g01XJR6#;R7#5R8#?R9f3R:#4f4R;#4R<'1f2R='1'Ig00JBR>P>P4P1g00jeR?P2g00k>R@CHP1P?g00kWP2P@g00l5EEg00h?CCR@P0P5P2P5P>1B52P3P5P2f5R0%78R8'0g01e^R?%;7#7R7,00%40R1f6RA#4RB'1/1;RCP>P51:C?#A%@C,00?3?=P=n0100000020000RD3<33P9C=P5P2PDPCC=n0100000020000f8%56R6#7RC'0%56#5#5#?R6,>01839'9f1RD33n2001103000120102101#2%2=RE36P311<1/1:/:?#AR1P>P>f7R</0CRC1>;6R61899'910A810A7%4<,1B/10R0P>P5P3%@0,0A?3?:P:n0100000020000RA3<73?33#2%2:R?56@P31D@EREPEn0110000020000b0P1P>P>1809,96=3CA#2=6@?P3PEPEn0110000020000b0n0110000020000b0P;P:P=PDP3DF#2%2356@eX55X12X32X24X44P;P:P=PDP3O5W5X12X32X24W4o"). Qed.
Lemma s_areas_set_size p e n b3 st : s_areas (set_size p e n b3 st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12b3h21eh31nh41ph52sti018reservedi023st2i031xp;1p;2p;4p;6p;3p;5g01e9j1;Tg01T2j15Tg01TWj1?Tg01knj21Tg01[aj2ITg00b9j4HTg00bWj6ETg00Ebj4CTg00UbR0j2BTg029Yj17Tg02:7j20Tg00F6j2:Tg01n@j1ATg02:lj1@Tg02;Ij33Tg02<=j3<Tg00SWj4=Tg01U5j2>Tg02=2j28Tg01\>j29Tg018Uj12Tg006oj36Tg00G1j2DTg02=Rj5FTg004Gj3GTg00KBR1g00K`R2f0R33Gp=4g006:R4g00ilR5g01XJR6#;R7#5R8#?R9f3R:#4f4R;#4R<'1f2R='1'Ig00JBR>P>P4P1g00jeR?P2g00k>R@CHP1P?g00kWP2P@g00l5EEg019MCCR@P0P5P2P5P>1B52P3P5P2f5R0%78R8'0g01e^R?%;7#7R7,00%40R1f6RA#4RB'1/1;RCP>P51:C?#A%@C,00?3?=P=n0100000020000RD3<33P9C=P5P2PDPCC=n0100000020000f8%56R6#7RC'0%56#5#5#?R6,>01839'9f1RD33n2001103000120102101#2%2=RE36P311<1/1:/:?#AR1P>P>f7R</0CRC1>;6R61899'910A810A7%4<,1B/10R0P>P5P3%@0,0A?3?:P:n0100000020000RA3<73?33#2%2:R?56@P31D@EREPEn0110000020000b0P1P>P>1809,96=3CA#2=6@?P3PEPEn0110000020000b0n0110000020000b0P;P:P=PDP3DF#2%2356@eX55X12X32X24X44P;P:P=PDP3O5W5X12X32X24W4o"). Qed.
Lemma s_groups_set_size p e n b3 st : s_groups (set_size p e n b3 st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12b3h21eh31nh41ph52sti018reservedi023st2i031xp;1p;2p;4p;6p;3p;5g01e9j1;Tg01T2j15Tg01TWj1?Tg01knj21Tg01[aj2ITg00b9j4HTg00bWj6ETg00Ebj4CTg00UbR0j2BTg029Yj17Tg02:7j20Tg00F6j2:Tg01n@j1ATg02:lj1@Tg02;Ij33Tg02<=j3<Tg00SWj4=Tg01U5j2>Tg02=2j28Tg01\>j29Tg01:Dj12Tg006oj36Tg00G1j2DTg02=Rj5FTg004Gj3GTg00KBR1g00K`R2f0R33Gp=4g006:R4g00ilR5g01XJR6#;R7#5R8#?R9f3R:#4f4R;#4R<'1f2R='1'Ig00JBR>P>P4P1g00jeR?P2g00k>R@CHP1P?g00kWP2P@g00l5EEg01;=CCR@P0P5P2P5P>1B52P3P5P2f5R0%78R8'0g01e^R?%;7#7R7,00%40R1f6RA#4RB'1/1;RCP>P51:C?#A%@C,00?3?=P=n0100000020000RD3<33P9C=P5P2PDPCC=n0100000020000f8%56R6#7RC'0%56#5#5#?R6,>01839'9f1RD33n2001103000120102101#2%2=RE36P311<1/1:/:?#AR1P>P>f7R</0CRC1>;6R61899'910A810A7%4<,1B/10R0P>P5P3%@0,0A?3?:P:n0100000020000RA3<73?33#2%2:R?56@P31D@EREPEn0110000020000b0P1P>P>1809,96=3CA#2=6@?P3PEPEn0110000020000b0n0110000020000b0P;P:P=PDP3DF#2%2356@eX55X12X32X24X44P;P:P=PDP3O5W5X12X32X24W4o"). Qed.
Lemma s_slots_set_size p e n b3 st : s_slots (set_size p e n b3 st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12b3h21eh31nh41ph52sti018reservedi023st2i031xp;1p;2p;4p;6p;3p;5g01e9j1<Tg01T2j15Tg01TWj1;Tg01knj21Tg01[aj2ITg00b9j4HTg00bWj6GTg00UbR0j2@Tg00Ebj4CTg029Yj17Tg02:7j20Tg00F6j2:Tg01n@j1BTg02:lj1ATg02;Ij33Tg02<=j3=Tg00SWj4>Tg01U5j2?Tg02=2j29Tg01\>j28Tg01<4j12Tg006oj36Tg00G1j2FTg02=Rj5ETg004Gj3DTg00KBR1g00K`R2f0R33Dp=4g006:R4g00ilR5g01XJR6#<R7#5R8#;R9f3R:#4f4R;#4R<'1f2R='1'Ig00JBR>P>P4P1g00jeR?P2g00k>R@CHP1P?g00kWP2P@g00l5EG1@42CCR@P0P5P2P5P>1@52P3P5P2f5R0%78R8'0g01e^R?%<7#7R7,00%40R1f6RA#4RB'1/1;RCP>P51:C?#B%AC,00?3?=P=n0100000020000RD3=33P9C>P5P2PDPCC>n0100000020000f8%56R6#7RC'0%56#5#5#;R6,?01939'8f1RD33n2001103000120102101#2%2=RE36P311<1/1:/:?#BR1P>P>f7R</0CRC1?;6R61999'810A810A7%4<,1B/10R0P>P5P3%A0,0A?3?:P:n0100000020000RA3=73?33#2%2:R?56@P31F@EREPEn0110000020000b0P1P>P>1909,86=3CA#2=6@?P3PEPEn0110000020000b0n0110000020000b0P;P:P=PDP3DE#2%2356@eX55X12X32X24X44P;P:P=PDP3O5W5X12X32X24W4o"). Qed.
Lemma s_tick_set_size p e n b3 st : s_tick (set_size p e n b3 st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12b3h21eh31nh41ph52sti018reservedi023st2i031xp;1p;2p;3p;4p;5g01e9j1>Tg01T2j15Tg01TWj1=Tg01knj20Tg01[aj2FTg00UbR0j2ETg029Yj19Tg02:7j21Tg00F6j2<Tg01n@j1;Tg02:lj1:Tg02;Ij33Tg02<=j3ATg00SWj4@Tg01U5j2?Tg02=2j27Tg01\>j28Tg01<lj12Tg006oj36Tg00G1j2DTg02=Rj5CTg004Gj3BTg00KBR1g00K`R2f0R33Bp=4g006:R4g00ilR5g01XJR6#>R7#5R8#=R9f3R:#4f4R;#4R<'0f2R='0'Fg00JBR>P>P0P5P2P5P>1E52P3P5P2f5R0%98R8'1g01e^R?%>7#9R7,10%40R@f6RA#4RB'0/0;RCP>P51<C?#;%:C,10?3?=P=n0100000020000RD3A33P9C@P5P2PDPCC@n0100000020000f8%56R6#9RC'1%56#5#5#=R6,?01739'8f1RD33n2001103000120102101#2%2=RE561P310<@/0:/<?#;R@P>P>f7R</1CRC1?;6R61799'811A811A7%4<,0B/00R0P>P5P3%:0,1A?3?:P:n0100000020000RA3A73?33#2%2:R?561P31D1EREPEn0110000020000b0P@P>P>1709,86=3CA#2=61?P3PEPEn0110000020000b0n0110000020000b0P;P:P=PDP3DC#2%23561eX55X12X32X24X44P;P:P=PDP3O5W5X12X32X24W4o"). Qed.
Lemma s_secret_set_size p e n b3 st : s_secret (set_size p e n b3 st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12b3h21eh31nh41ph52sti018reservedi023st2i031xp;1p;2p;3p;4p;5g01e9j1>Tg01T2j15Tg01TWj1=Tg01knj20Tg01[aj2FTg00UbR0j2ETg029Yj19Tg02:7j21Tg00F6j2<Tg01n@j1;Tg02:lj1:Tg02;Ij33Tg02<=j3ATg00SWj4@Tg01U5j2?Tg02=2j27Tg01\>j28Tg01=cj12Tg006oj36Tg00G1j2DTg02=Rj5CTg004Gj3BTg00KBg00K`R1f0R23Bp=4g006:R3g00ilR4g01XJR5#>R6#5R7#=R8f3R9#4f4R:#4R;'0f2R<'0'Fg00JBR=P=P0P4P1P4P=1E41P2P4P1f5R0%97R7'1g01e^R>%>6#9R6,10%40R?f6R@#4RA'0/0:RBP=P41<B>#;%:B,10?3><P<n0100000020000RC3A33P8C@P4P1PCPBC@n0100000020000f8%55R5#9RB'1%55#5#5#=R5,?01728'8f1RC33n2001103000120102101#2%2<RD561P210;?/09/<>#;R?P=P=f7R;/1BRB1?:5R51788'811@711@6%4;,0A/00R0P=P4P2%:0,1@?3>9P9n0100000020000R@3A73>33#2%29R>561P21D1DRDPDn0110000020000b0P?P=P=1708,85=3B@#2=61>P2PDPDn0110000020000b0n0110000020000b0P:P9P<PCP2DC#2%22561eX54X11X31X23X43P:P9P<PCP2O5W5X11X31X23W4o"). Qed.
Lemma s_reserved_set_size p e n b3 st : s_reserved (set_size p e n b3 st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12b3h21eh31nh41ph52sti018reservedi023st2i031xp;1p;2p;3p;4p;5g01e9j1>Tg01T2j15Tg01TWj1@Tg01knj20Tg01[aj2GTg00UbR0j2=Tg01>\j1DTg029Yj17Tg02:7j21Tg00F6j2<Tg01n@j1;Tg02:lj1:Tg02;Ij33Tg02<=j3BTg00SWj4ATg01U5j2?Tg02=2j28Tg01\>j29Tg01?<j12Tg006oj36Tg00G1j2FTg02=Rj5CTg004Gj3ETg00KBg00K`R1f0R23Ep=4g006:R3g00ilR4g01XJR5#>R6#5R7#@R8f3R9#4f4R:#4R;'0f2R<'0'Gg00JBR=P=1=11#DR>P0P4P1P4P=1=41P2P4P1f5R0%77R7'1g01e^R?%>6#7R6,10%40R@f6RA#4RB'0/0:RCP=P41<C?#;%:C,10?3?<P<n0100000020000RD3B33P8CAP4P1PDPCCAn0100000020000f8%55R5#7RC'1%55#5#5#@R5,?01828'9f1RD33n2001103000120102101#2%2<RE36P210;@/09/<?#;R@P=P=f7R;/1CRC1?:5R51888'911A711A6%4;,0B/00R0P=P4P2%:0,1A?3?9P9n0100000020000RA3B73?33#2%29R?56>P21F>EREPEn0110000020000b0P@P=P=1808,95=3CA#2=6>?P2PEPEn0110000020000b0n0110000020000b0P:P9P<PDP2DC#2%2256>eX54X11X31X23X43P:P9P<PDP2O5W5X11X31X23W4o"). Qed.
Lemma s_atop_set_size p e n b3 st : s_atop (set_size p e n b3 st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12b3h21eh31nh41ph52sti018reservedi023st2i031xp;1p;2p;3p;4p;5g01e9j1>Tg01T2j15Tg01TWj1=Tg01knj20Tg01[aj2FTg00UbR0j2ETg029Yj19Tg02:7j21Tg00F6j2<Tg01n@j1;Tg02:lj1:Tg02;Ij33Tg02<=j3ATg00SWj4@Tg01U5j2?Tg02=2j27Tg01\>j28Tg01@7j12Tg006oj36Tg00G1j2DTg02=Rj5CTg004Gj3BTg00KBg00K`R1f0R23Bp=4g006:R3g00ilR4g01XJR5#>R6#5R7#=R8f3R9#4f4R:#4R;'0f2R<'0'Fg00JBR=P=P0P4P1P4P=1E41P2P4P1f5R0%97R7'1g01e^R>%>6#9R6,10%40R?f6R@#4RA'0/0:RBP=P41<B>#;%:B,10?3><P<n0100000020000RC3A33P8C@P4P1PCPBC@n0100000020000f8%55R5#9RB'1%55#5#5#=R5,?01728'8f1RC33n2001103000120102101#2%2<RD561P210;?/09/<>#;R?P=P=f7R;/1BRB1?:5R51788'811@711@6%4;,0A/00R0P=P4P2%:0,1@?3>9P9n0100000020000R@3A73>33#2%29R>561P21D1DRDPDn0110000020000b0P?P=P=1708,85=3B@#2=61>P2PDPDn0110000020000b0n0110000020000b0P:P9P<PCP2DC#2%22561eX54X11X31X23X43P:P9P<PCP2O5W5X11X31X23W4o"). Qed.
Lemma c_secret_set_active sc v st : c_secret (s_ctx (set_active sc v st)) = c_secret (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01QHj11Tg00G1j20Tg00K`R0g00BLR1g00ilR2f0R3#2#1,00X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma c_init_done_set_active sc v st : c_init_done (s_ctx (set_active sc v st)) = c_init_done (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01@nj11Tg00G1j20Tg00K`R0g00BLR1g00ilR2f0R3#2#1,00X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma c_mmap_counter_set_active sc v st : c_mmap_counter (s_ctx (set_active sc v st)) = c_mmap_counter (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01Ajj11Tg00G1j20Tg00K`R0g00BLR1g00ilR2f0R3#2#1,00X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma c_free_meta_head_set_active sc v st : c_free_meta_head (s_ctx (set_active sc v st)) = c_free_meta_head (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01Bij11Tg00G1j20Tg00K`R0g00BLR1g00ilR2f0R3#2#1,01X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma c_avail_meta_set_active sc v st : c_avail_meta (s_ctx (set_active sc v st)) = c_avail_meta (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01Cjj11Tg00G1j20Tg00K`R0g00BLR1g00ilR2f0R3#2#1,01X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma c_avail_meta_count_set_active sc v st : c_avail_meta_count (s_ctx (set_active sc v st)) = c_avail_meta_count (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01Dgj11Tg00G1j20Tg00K`R0g00BLR1g00ilR2f0R3#2#1,00X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma c_avail_meta_area_count_set_active sc v st : c_avail_meta_area_count (s_ctx (set_active sc v st)) = c_avail_meta_area_count (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01Ejj11Tg00G1j20Tg00K`R0g00BLR1g00ilR2f0R3#2#1,00X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma c_meta_alloc_shift_set_active sc v st : c_meta_alloc_shift (s_ctx (set_active sc v st)) = c_meta_alloc_shift (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01G2j11Tg00G1j20Tg00K`R0g00BLR1g00ilR2f0R3#2#1,00X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma c_meta_area_head_set_active sc v st : c_meta_area_head (s_ctx (set_active sc v st)) = c_meta_area_head (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01H5j11Tg00G1j20Tg00K`R0g00BLR1g00ilR2f0R3#2#1,01X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma c_meta_area_tail_set_active sc v st : c_meta_area_tail (s_ctx (set_active sc v st)) = c_meta_area_tail (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01I6j11Tg00G1j20Tg00K`R0g00BLR1g00ilR2f0R3#2#1,01X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma c_avail_meta_areas_set_active sc v st : c_avail_meta_areas (s_ctx (set_active sc v st)) = c_avail_meta_areas (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01J7j11Tg00G1j20Tg00K`R0g00BLR1g00ilR2f0R3#2#1,01X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma c_usage_set_active sc v st : c_usage (s_ctx (set_active sc v st)) = c_usage (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;1p;2g00Ebj43Tg012Hj12Tg01L3j10Tg00G1j21Tg00K`R0g00BLR1g00ilR2P0g00k>g00l5P0C3f0R3#2#0'1X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma c_unmap_seq_set_active sc v st : c_unmap_seq (s_ctx (set_active sc v st)) = c_unmap_seq (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;1p;2g00Ebj43Tg012Hj12Tg01Lkj10Tg00G1j21Tg00K`R0g00BLR1g00ilR2P0g00k>g00l5P0C3f0R3#2#0'1X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma c_bounces_set_active sc v st : c_bounces (s_ctx (set_active sc v st)) = c_bounces (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;1p;2g00Ebj43Tg012Hj12Tg01Mgj10Tg00G1j21Tg00K`R0g00BLR1g00ilR2P0g00k>g00l5P0C3f0R3#2#0'1X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma c_seq_set_active sc v st : c_seq (s_ctx (set_active sc v st)) = c_seq (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01Naj11Tg00G1j20Tg00K`R0g00BLR1g00ilR2f0R3#2#1,00X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma c_brk_set_active sc v st : c_brk (s_ctx (set_active sc v st)) = c_brk (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01OWj11Tg00G1j20Tg00K`R0g00BLR1g00ilR2g01PMf0R3#2#1'0X12X21X00f2f1P3O3W1W2W0o"). Qed.
Lemma c_secret_set_usage sc v st : c_secret (s_ctx (set_usage sc v st)) = c_secret (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01QHj11Tg00G1j20Tg00K`R0g00ilR1f0R2#2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_init_done_set_usage sc v st : c_init_done (s_ctx (set_usage sc v st)) = c_init_done (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01@nj11Tg00G1j20Tg00K`R0g00ilR1f0R2#2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_mmap_counter_set_usage sc v st : c_mmap_counter (s_ctx (set_usage sc v st)) = c_mmap_counter (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01Ajj11Tg00G1j20Tg00K`R0g00ilR1f0R2#2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_free_meta_head_set_usage sc v st : c_free_meta_head (s_ctx (set_usage sc v st)) = c_free_meta_head (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01Bij11Tg00G1j20Tg00K`R0g00ilR1g00BLf0R2#2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_avail_meta_set_usage sc v st : c_avail_meta (s_ctx (set_usage sc v st)) = c_avail_meta (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01Cjj11Tg00G1j20Tg00K`R0g00ilR1g00BLf0R2#2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_avail_meta_count_set_usage sc v st : c_avail_meta_count (s_ctx (set_usage sc v st)) = c_avail_meta_count (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01Dgj11Tg00G1j20Tg00K`R0g00ilR1f0R2#2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_avail_meta_area_count_set_usage sc v st : c_avail_meta_area_count (s_ctx (set_usage sc v st)) = c_avail_meta_area_count (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01Ejj11Tg00G1j20Tg00K`R0g00ilR1f0R2#2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_meta_alloc_shift_set_usage sc v st : c_meta_alloc_shift (s_ctx (set_usage sc v st)) = c_meta_alloc_shift (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01G2j11Tg00G1j20Tg00K`R0g00ilR1f0R2#2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_meta_area_head_set_usage sc v st : c_meta_area_head (s_ctx (set_usage sc v st)) = c_meta_area_head (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01H5j11Tg00G1j20Tg00K`R0g00ilR1g00BLf0R2#2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_meta_area_tail_set_usage sc v st : c_meta_area_tail (s_ctx (set_usage sc v st)) = c_meta_area_tail (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01I6j11Tg00G1j20Tg00K`R0g00ilR1g00BLf0R2#2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_avail_meta_areas_set_usage sc v st : c_avail_meta_areas (s_ctx (set_usage sc v st)) = c_avail_meta_areas (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01J7j11Tg00G1j20Tg00K`R0g00ilR1g00BLf0R2#2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_active_set_usage sc v st : c_active (s_ctx (set_usage sc v st)) = c_active (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;1p;2g00Ebj43Tg012Hj12Tg01K:j10Tg00G1j21Tg00K`R0g00ilR1P0g00k>g00l5g006:C3f0R2#2#0'1X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_unmap_seq_set_usage sc v st : c_unmap_seq (s_ctx (set_usage sc v st)) = c_unmap_seq (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;1p;2g00Ebj43Tg012Hj12Tg01Lkj10Tg00G1j21Tg00K`R0g00ilR1P0g00k>g00l5P0C3f0R2#2#0'1X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_bounces_set_usage sc v st : c_bounces (s_ctx (set_usage sc v st)) = c_bounces (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;4p;1p;2g00Ebj43Tg012Hj12Tg01Mgj10Tg00G1j21Tg00K`R0g00ilR1P0g00k>g00l5P0C3f0R2#2#0'1X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_seq_set_usage sc v st : c_seq (s_ctx (set_usage sc v st)) = c_seq (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01Naj11Tg00G1j20Tg00K`R0g00ilR1f0R2#2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_brk_set_usage sc v st : c_brk (s_ctx (set_usage sc v st)) = c_brk (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02sch12sth21vp;1p;2g012Hj12Tg01OWj11Tg00G1j20Tg00K`R0g00ilR1g01PMf0R2#2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_secret_set_bounce i v st : c_secret (s_ctx (set_bounce i v st)) = c_secret (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g012Hj12Tg01QHj11Tg00G1j20Tg00K`R0g00ilR1f0R2#2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_init_done_set_bounce i v st : c_init_done (s_ctx (set_bounce i v st)) = c_init_done (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g012Hj12Tg01@nj11Tg00G1j20Tg00K`R0g00ilR1f0R2#2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_mmap_counter_set_bounce i v st : c_mmap_counter (s_ctx (set_bounce i v st)) = c_mmap_counter (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g012Hj12Tg01Ajj11Tg00G1j20Tg00K`R0g00ilR1f0R2#2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_free_meta_head_set_bounce i v st : c_free_meta_head (s_ctx (set_bounce i v st)) = c_free_meta_head (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g012Hj12Tg01Bij11Tg00G1j20Tg00K`R0g00ilR1g00BLf0R2#2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_avail_meta_set_bounce i v st : c_avail_meta (s_ctx (set_bounce i v st)) = c_avail_meta (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g012Hj12Tg01Cjj11Tg00G1j20Tg00K`R0g00ilR1g00BLf0R2#2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_avail_meta_count_set_bounce i v st : c_avail_meta_count (s_ctx (set_bounce i v st)) = c_avail_meta_count (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g012Hj12Tg01Dgj11Tg00G1j20Tg00K`R0g00ilR1f0R2#2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_avail_meta_area_count_set_bounce i v st : c_avail_meta_area_count (s_ctx (set_bounce i v st)) = c_avail_meta_area_count (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g012Hj12Tg01Ejj11Tg00G1j20Tg00K`R0g00ilR1f0R2#2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_meta_alloc_shift_set_bounce i v st : c_meta_alloc_shift (s_ctx (set_bounce i v st)) = c_meta_alloc_shift (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g012Hj12Tg01G2j11Tg00G1j20Tg00K`R0g00ilR1f0R2#2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_meta_area_head_set_bounce i v st : c_meta_area_head (s_ctx (set_bounce i v st)) = c_meta_area_head (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g012Hj12Tg01H5j11Tg00G1j20Tg00K`R0g00ilR1g00BLf0R2#2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_meta_area_tail_set_bounce i v st : c_meta_area_tail (s_ctx (set_bounce i v st)) = c_meta_area_tail (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g012Hj12Tg01I6j11Tg00G1j20Tg00K`R0g00ilR1g00BLf0R2#2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_avail_meta_areas_set_bounce i v st : c_avail_meta_areas (s_ctx (set_bounce i v st)) = c_avail_meta_areas (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g012Hj12Tg01J7j11Tg00G1j20Tg00K`R0g00ilR1g00BLf0R2#2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_active_set_bounce i v st : c_active (s_ctx (set_bounce i v st)) = c_active (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;4p;1p;2g00Ebj43Tg012Hj12Tg01K:j10Tg00G1j21Tg00K`R0g00ilR1P0g00k>g00l5g006:C3f0R2#2#0'1X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_usage_set_bounce i v st : c_usage (s_ctx (set_bounce i v st)) = c_usage (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;4p;1p;2g00Ebj43Tg012Hj12Tg01L3j10Tg00G1j21Tg00K`R0g00ilR1P0g00k>g00l5P0C3f0R2#2#0'1X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_unmap_seq_set_bounce i v st : c_unmap_seq (s_ctx (set_bounce i v st)) = c_unmap_seq (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;4p;1p;2g00Ebj43Tg012Hj12Tg01Lkj10Tg00G1j21Tg00K`R0g00ilR1P0g00k>g00l5P0C3f0R2#2#0'1X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_seq_set_bounce i v st : c_seq (s_ctx (set_bounce i v st)) = c_seq (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g012Hj12Tg01Naj11Tg00G1j20Tg00K`R0g00ilR1f0R2#2#1,00X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_brk_set_bounce i v st : c_brk (s_ctx (set_bounce i v st)) = c_brk (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01ih12sth21vp;1p;2g012Hj12Tg01OWj11Tg00G1j20Tg00K`R0g00ilR1g01PMf0R2#2#1'0X11X20X00f2f1P2O3W1X20W0o"). Qed.
Lemma c_secret_step_seq  st : c_secret (s_ctx (step_seq st)) = c_secret (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1@Tg01Naj16Tg01T2j10Tg01TWj14Tg00F6j2?Tg00Ebj4<Tg00<@j4;Tg01g0j2:Tg01gCj29Tg01hEj23Tg01i=j25Tg01\>j28Tg012Hj12Tg01QHj11Tg006oj37Tg00G1j2>Tg01j5j1=Tg00ilR0f0R1#@#6g01XJR2#0#0#0#0#0#0#0#4'?g00JBR3P3g00K`R4P3P0P1g013>R3%42R2P4g00k>R5g00l5R6P4C<P4P5P6P4C;':/91'3W0f2R6'5%61/82/31X03/56n0100000020000#2#1%26#137P1f1#2#1,>4R6P6n0110000020000b2%=1#2#1%21#1574eX10P1O1W1o"). Qed.
Lemma c_init_done_step_seq  st : c_init_done (s_ctx (step_seq st)) = c_init_done (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1@Tg01Naj16Tg01T2j10Tg01TWj14Tg00F6j2?Tg00Ebj4<Tg00<@j4;Tg01g0j2:Tg01gCj29Tg01hEj23Tg01i=j25Tg01\>j28Tg012Hj12Tg01@nj11Tg006oj37Tg00G1j2>Tg01j5j1=Tg00ilR0f0R1#@#6g01XJR2#0#0#0#0#0#0#0#4'?g00JBR3P3g00K`R4P3P0P1g013>R3%42R2P4g00k>R5g00l5R6P4C<P4P5P6P4C;':/91'3W0f2R6'5%61/82/31X03/56n0100000020000#2#1%26#137P1f1#2#1,>4R6P6n0110000020000b2%=1#2#1%21#1574eX10P1O1W1o"). Qed.
Lemma c_mmap_counter_step_seq  st : c_mmap_counter (s_ctx (step_seq st)) = c_mmap_counter (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1@Tg01Naj16Tg01T2j10Tg01TWj14Tg00F6j2?Tg00Ebj4<Tg00<@j4;Tg01g0j2:Tg01gCj29Tg01hEj23Tg01i=j25Tg01\>j28Tg012Hj12Tg01Ajj11Tg006oj37Tg00G1j2>Tg01j5j1=Tg00ilR0f0R1#@#6g01XJR2#0#0#0#0#0#0#0#4'?g00JBR3P3g00K`R4P3P0P1g013>R3%42R2P4g00k>R5g00l5R6P4C<P4P5P6P4C;':/91'3W0f2R6'5%61/82/31X03/56n0100000020000#2#1%26#137P1f1#2#1,>4R6P6n0110000020000b2%=1#2#1%21#1574eX10P1O1W1o"). Qed.
Lemma c_free_meta_head_step_seq  st : c_free_meta_head (s_ctx (step_seq st)) = c_free_meta_head (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1@Tg01Naj16Tg01T2j10Tg01TWj14Tg00F6j2?Tg00Ebj4<Tg00<@j4;Tg01g0j2:Tg01gCj29Tg01hEj23Tg01i=j25Tg01\>j28Tg012Hj12Tg01Bij11Tg006oj37Tg00G1j2>Tg01j5j1=Tg00ilR0f0R1#@#6g01XJR2#0#0#0#0#0#0#0#4'?g00JBR3P3g00BLR4P3P0P1g013>R3%42R2g00K`R5g00k>R6g00l5R7P5C<P5P6P7P5C;':/91'3W0f2R5'5%61/82/31X03/55n0100000020000#2#1%25#137P1f1#2#1,>4R5P5n0110000020000b2%=1#2#1%21#1574eX10P1O1W1o"). Qed.
Lemma c_avail_meta_step_seq  st : c_avail_meta (s_ctx (step_seq st)) = c_avail_meta (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1@Tg01Naj16Tg01T2j10Tg01TWj14Tg00F6j2?Tg00Ebj4<Tg00<@j4;Tg01g0j2:Tg01gCj29Tg01hEj23Tg01i=j25Tg01\>j28Tg012Hj12Tg01Cjj11Tg006oj37Tg00G1j2>Tg01j5j1=Tg00ilR0f0R1#@#6g01XJR2#0#0#0#0#0#0#0#4'?g00JBR3P3g00BLR4P3P0P1g013>R3%42R2g00K`R5g00k>R6g00l5R7P5C<P5P6P7P5C;':/91'3W0f2R5'5%61/82/31X03/55n0100000020000#2#1%25#137P1f1#2#1,>4R5P5n0110000020000b2%=1#2#1%21#1574eX10P1O1W1o"). Qed.
Lemma c_avail_meta_count_step_seq  st : c_avail_meta_count (s_ctx (step_seq st)) = c_avail_meta_count (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1@Tg01Naj16Tg01T2j10Tg01TWj14Tg00F6j2?Tg00Ebj4<Tg00<@j4;Tg01g0j2:Tg01gCj29Tg01hEj23Tg01i=j25Tg01\>j28Tg012Hj12Tg01Dgj11Tg006oj37Tg00G1j2>Tg01j5j1=Tg00ilR0f0R1#@#6g01XJR2#0#0#0#0#0#0#0#4'?g00JBR3P3g00K`R4P3P0P1g013>R3%42R2P4g00k>R5g00l5R6P4C<P4P5P6P4C;':/91'3W0f2R6'5%61/82/31X03/56n0100000020000#2#1%26#137P1f1#2#1,>4R6P6n0110000020000b2%=1#2#1%21#1574eX10P1O1W1o"). Qed.
Lemma c_avail_meta_area_count_step_seq  st : c_avail_meta_area_count (s_ctx (step_seq st)) = c_avail_meta_area_count (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1@Tg01Naj16Tg01T2j10Tg01TWj14Tg00F6j2?Tg00Ebj4<Tg00<@j4;Tg01g0j2:Tg01gCj29Tg01hEj23Tg01i=j25Tg01\>j28Tg012Hj12Tg01Ejj11Tg006oj37Tg00G1j2>Tg01j5j1=Tg00ilR0f0R1#@#6g01XJR2#0#0#0#0#0#0#0#4'?g00JBR3P3g00K`R4P3P0P1g013>R3%42R2P4g00k>R5g00l5R6P4C<P4P5P6P4C;':/91'3W0f2R6'5%61/82/31X03/56n0100000020000#2#1%26#137P1f1#2#1,>4R6P6n0110000020000b2%=1#2#1%21#1574eX10P1O1W1o"). Qed.
Lemma c_meta_alloc_shift_step_seq  st : c_meta_alloc_shift (s_ctx (step_seq st)) = c_meta_alloc_shift (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1@Tg01Naj16Tg01T2j10Tg01TWj14Tg00F6j2?Tg00Ebj4<Tg00<@j4;Tg01g0j2:Tg01gCj29Tg01hEj23Tg01i=j25Tg01\>j28Tg012Hj12Tg01G2j11Tg006oj37Tg00G1j2>Tg01j5j1=Tg00ilR0f0R1#@#6g01XJR2#0#0#0#0#0#0#0#4'?g00JBR3P3g00K`R4P3P0P1g013>R3%42R2P4g00k>R5g00l5R6P4C<P4P5P6P4C;':/91'3W0f2R6'5%61/82/31X03/56n0100000020000#2#1%26#137P1f1#2#1,>4R6P6n0110000020000b2%=1#2#1%21#1574eX10P1O1W1o"). Qed.
Lemma c_meta_area_head_step_seq  st : c_meta_area_head (s_ctx (step_seq st)) = c_meta_area_head (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1@Tg01Naj16Tg01T2j10Tg01TWj14Tg00F6j2?Tg00Ebj4<Tg00<@j4;Tg01g0j2:Tg01gCj29Tg01hEj23Tg01i=j25Tg01\>j28Tg012Hj12Tg01H5j11Tg006oj37Tg00G1j2>Tg01j5j1=Tg00ilR0f0R1#@#6g01XJR2#0#0#0#0#0#0#0#4'?g00JBR3P3g00BLR4P3P0P1g013>R3%42R2g00K`R5g00k>R6g00l5R7P5C<P5P6P7P5C;':/91'3W0f2R5'5%61/82/31X03/55n0100000020000#2#1%25#137P1f1#2#1,>4R5P5n0110000020000b2%=1#2#1%21#1574eX10P1O1W1o"). Qed.
Lemma c_meta_area_tail_step_seq  st : c_meta_area_tail (s_ctx (step_seq st)) = c_meta_area_tail (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1@Tg01Naj16Tg01T2j10Tg01TWj14Tg00F6j2?Tg00Ebj4<Tg00<@j4;Tg01g0j2:Tg01gCj29Tg01hEj23Tg01i=j25Tg01\>j28Tg012Hj12Tg01I6j11Tg006oj37Tg00G1j2>Tg01j5j1=Tg00ilR0f0R1#@#6g01XJR2#0#0#0#0#0#0#0#4'?g00JBR3P3g00BLR4P3P0P1g013>R3%42R2g00K`R5g00k>R6g00l5R7P5C<P5P6P7P5C;':/91'3W0f2R5'5%61/82/31X03/55n0100000020000#2#1%25#137P1f1#2#1,>4R5P5n0110000020000b2%=1#2#1%21#1574eX10P1O1W1o"). Qed.
Lemma c_avail_meta_areas_step_seq  st : c_avail_meta_areas (s_ctx (step_seq st)) = c_avail_meta_areas (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1@Tg01Naj16Tg01T2j10Tg01TWj14Tg00F6j2?Tg00Ebj4<Tg00<@j4;Tg01g0j2:Tg01gCj29Tg01hEj23Tg01i=j25Tg01\>j28Tg012Hj12Tg01J7j11Tg006oj37Tg00G1j2>Tg01j5j1=Tg00ilR0f0R1#@#6g01XJR2#0#0#0#0#0#0#0#4'?g00JBR3P3g00BLR4P3P0P1g013>R3%42R2g00K`R5g00k>R6g00l5R7P5C<P5P6P7P5C;':/91'3W0f2R5'5%61/82/31X03/55n0100000020000#2#1%25#137P1f1#2#1,>4R5P5n0110000020000b2%=1#2#1%21#1574eX10P1O1W1o"). Qed.
Lemma c_active_step_seq  st : c_active (s_ctx (step_seq st)) = c_active (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1@Tg01Naj17Tg01T2j10Tg01TWj16Tg00F6j2?Tg00Ebj45Tg00<@j4<Tg01g0j2;Tg01gCj2:Tg01hEj24Tg01i=j23Tg01\>j29Tg012Hj11Tg01K:j12Tg006oj38Tg00G1j2>Tg01j5j1=Tg00ilR0f0R1#@#7g01XJR2#0#0#0#0#0#0#0#6'?g00JBR3P3g00K`R4g00k>R5g00l5R6g006:C5R7P3P0P1g013>R3%62R2P4P5P6P4C5P4P5P6P4C<';/:1'4W0f2R4'3%71/92/41X03/34n0100000020000#1#2%14#238P1f1#1#2,>7R4P4n0110000020000b2%=1#1#2%11#2587eX10P1O1W1o"). Qed.
Lemma c_usage_step_seq  st : c_usage (s_ctx (step_seq st)) = c_usage (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1@Tg01Naj16Tg01T2j10Tg01TWj14Tg00F6j2?Tg00Ebj4<Tg00<@j4;Tg01g0j2:Tg01gCj29Tg01hEj23Tg01i=j25Tg01\>j28Tg012Hj12Tg01L3j11Tg006oj37Tg00G1j2>Tg01j5j1=Tg00ilR0f0R1#@#6g01XJR2#0#0#0#0#0#0#0#4'?g00JBR3P3g00K`R4g00k>R5g00l5R6P4C<R7P3P0P1g013>R3%42R2P4P5P6P4C;,:7/91'3W0f2R4'5%61/82/31X03/54n0100000020000#2#1%24#137P1f1#2#1,>7R4P4n0110000020000b2%=1#2#1%21#1577eX10P1O1W1o"). Qed.
Lemma c_bounces_step_seq  st : c_bounces (s_ctx (step_seq st)) = c_bounces (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1@Tg01Naj16Tg01T2j10Tg01TWj14Tg00F6j2?Tg00Ebj4<Tg00<@j4;Tg01g0j2:Tg01gCj29Tg01hEj23Tg01i=j25Tg01\>j28Tg012Hj12Tg01Mgj11Tg006oj37Tg00G1j2>Tg01j5j1=Tg00ilR0f0R1#@#6g01XJR2#0#0#0#0#0#0#0#4'?g00JBR3P3g00K`R4g00k>R5g00l5R6P4C<R7P3P0P1g013>R3%42R2P4P5P6P4C;,:7/91'3W0f2R4'5%61/82/31X03/54n0100000020000#2#1%24#137P1f1#2#1,>7R4P4n0110000020000b2%=1#2#1%21#1577eX10P1O1W1o"). Qed.
Lemma c_brk_step_seq  st : c_brk (s_ctx (step_seq st)) = c_brk (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch12sth21bi001bp;1p;2p;4p;3g01f<j1@Tg01Naj16Tg01T2j10Tg01TWj14Tg00F6j2?Tg00Ebj4<Tg00<@j4;Tg01g0j2:Tg01gCj29Tg01hEj23Tg01i=j25Tg01\>j28Tg012Hj12Tg01OWj11Tg006oj37Tg00G1j2>Tg01j5j1=Tg00ilR0f0R1#@#6g01XJR2#0#0#0#0#0#0#0#4'?g00JBR3P3g01PMR4P3P0P1g013>R3%42R2g00K`R5g00k>R6g00l5R7P5C<P5P6P7P5C;':/91'3W0f2R5'5%61/82/31X03/55n0100000020000#2#1%25#137P1f1#2#1,>4R5P5n0110000020000b2%=1#2#1%21#1574eX10P1O1W1o"). Qed.
Lemma c_secret_record_seq sc st : c_secret (s_ctx (record_seq sc st)) = c_secret (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1@Tg00Ebj4?Tg00<Xj4:Tg00:<j44Tg01T2j12Tg01TWj1<Tg01knj2;Tg01Naj19Tg01Lkj15Tg00g<j76Tg01gCj27Tg01i=j28Tg012Hj11Tg01QHj10Tg006oj33Tg00G1j2>Tg01lKj2=Tg00K`R0g00ilR1f1R2#@g00JBR3P3P3P1f0R3g013>P0P0P0g00k>R4g00l5R5P0C?R6P0P0P6P0P4P5P0C:C4f4g01XJ#2#2#<';%93%53F6/73W3f2R5'8P5n0100000020000#1#0%15#0530P3%12#0,>0R5P5n0110000020000b21=23#1#0%13#0530eX11X00P2P3O2W1W0o"). Qed.
Lemma c_init_done_record_seq sc st : c_init_done (s_ctx (record_seq sc st)) = c_init_done (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1@Tg00Ebj4?Tg00<Xj4:Tg00:<j44Tg01T2j12Tg01TWj1<Tg01knj2;Tg01Naj19Tg01Lkj15Tg00g<j76Tg01gCj27Tg01i=j28Tg012Hj11Tg01@nj10Tg006oj33Tg00G1j2>Tg01lKj2=Tg00K`R0g00ilR1f1R2#@g00JBR3P3P3P1f0R3g013>P0P0P0g00k>R4g00l5R5P0C?R6P0P0P6P0P4P5P0C:C4f4g01XJ#2#2#<';%93%53F6/73W3f2R5'8P5n0100000020000#1#0%15#0530P3%12#0,>0R5P5n0110000020000b21=23#1#0%13#0530eX11X00P2P3O2W1W0o"). Qed.
Lemma c_mmap_counter_record_seq sc st : c_mmap_counter (s_ctx (record_seq sc st)) = c_mmap_counter (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1@Tg00Ebj4?Tg00<Xj4:Tg00:<j44Tg01T2j12Tg01TWj1<Tg01knj2;Tg01Naj19Tg01Lkj15Tg00g<j76Tg01gCj27Tg01i=j28Tg012Hj11Tg01Ajj10Tg006oj33Tg00G1j2>Tg01lKj2=Tg00K`R0g00ilR1f1R2#@g00JBR3P3P3P1f0R3g013>P0P0P0g00k>R4g00l5R5P0C?R6P0P0P6P0P4P5P0C:C4f4g01XJ#2#2#<';%93%53F6/73W3f2R5'8P5n0100000020000#1#0%15#0530P3%12#0,>0R5P5n0110000020000b21=23#1#0%13#0530eX11X00P2P3O2W1W0o"). Qed.
Lemma c_free_meta_head_record_seq sc st : c_free_meta_head (s_ctx (record_seq sc st)) = c_free_meta_head (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1@Tg00Ebj4?Tg00<Xj4:Tg00:<j44Tg01T2j12Tg01TWj1<Tg01knj2;Tg01Naj19Tg01Lkj15Tg00g<j76Tg01gCj27Tg01i=j28Tg012Hj11Tg01Bij10Tg006oj33Tg00G1j2>Tg01lKj2=Tg00K`R0g00ilR1f1R2#@g00JBR3P3g00BLR4P3P1f0R3g013>P0P0P0g00k>R5g00l5R6P0C?R7P0P0P7P0P5P6P0C:C4f4g01XJ#2#2#<';%93%53F6/73W3f2R6'8P6n0100000020000#1#0%16#033P3%12#0,>4R6P6n0110000020000b21=23#1#0%13#0534eX11X00P2P3O2W1W0o"). Qed.
Lemma c_avail_meta_record_seq sc st : c_avail_meta (s_ctx (record_seq sc st)) = c_avail_meta (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1@Tg00Ebj4?Tg00<Xj4:Tg00:<j44Tg01T2j12Tg01TWj1<Tg01knj2;Tg01Naj19Tg01Lkj15Tg00g<j76Tg01gCj27Tg01i=j28Tg012Hj11Tg01Cjj10Tg006oj33Tg00G1j2>Tg01lKj2=Tg00K`R0g00ilR1f1R2#@g00JBR3P3g00BLR4P3P1f0R3g013>P0P0P0g00k>R5g00l5R6P0C?R7P0P0P7P0P5P6P0C:C4f4g01XJ#2#2#<';%93%53F6/73W3f2R6'8P6n0100000020000#1#0%16#033P3%12#0,>4R6P6n0110000020000b21=23#1#0%13#0534eX11X00P2P3O2W1W0o"). Qed.
Lemma c_avail_meta_count_record_seq sc st : c_avail_meta_count (s_ctx (record_seq sc st)) = c_avail_meta_count (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1@Tg00Ebj4?Tg00<Xj4:Tg00:<j44Tg01T2j12Tg01TWj1<Tg01knj2;Tg01Naj19Tg01Lkj15Tg00g<j76Tg01gCj27Tg01i=j28Tg012Hj11Tg01Dgj10Tg006oj33Tg00G1j2>Tg01lKj2=Tg00K`R0g00ilR1f1R2#@g00JBR3P3P3P1f0R3g013>P0P0P0g00k>R4g00l5R5P0C?R6P0P0P6P0P4P5P0C:C4f4g01XJ#2#2#<';%93%53F6/73W3f2R5'8P5n0100000020000#1#0%15#0530P3%12#0,>0R5P5n0110000020000b21=23#1#0%13#0530eX11X00P2P3O2W1W0o"). Qed.
Lemma c_avail_meta_area_count_record_seq sc st : c_avail_meta_area_count (s_ctx (record_seq sc st)) = c_avail_meta_area_count (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1@Tg00Ebj4?Tg00<Xj4:Tg00:<j44Tg01T2j12Tg01TWj1<Tg01knj2;Tg01Naj19Tg01Lkj15Tg00g<j76Tg01gCj27Tg01i=j28Tg012Hj11Tg01Ejj10Tg006oj33Tg00G1j2>Tg01lKj2=Tg00K`R0g00ilR1f1R2#@g00JBR3P3P3P1f0R3g013>P0P0P0g00k>R4g00l5R5P0C?R6P0P0P6P0P4P5P0C:C4f4g01XJ#2#2#<';%93%53F6/73W3f2R5'8P5n0100000020000#1#0%15#0530P3%12#0,>0R5P5n0110000020000b21=23#1#0%13#0530eX11X00P2P3O2W1W0o"). Qed.
Lemma c_meta_alloc_shift_record_seq sc st : c_meta_alloc_shift (s_ctx (record_seq sc st)) = c_meta_alloc_shift (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1@Tg00Ebj4?Tg00<Xj4:Tg00:<j44Tg01T2j12Tg01TWj1<Tg01knj2;Tg01Naj19Tg01Lkj15Tg00g<j76Tg01gCj27Tg01i=j28Tg012Hj11Tg01G2j10Tg006oj33Tg00G1j2>Tg01lKj2=Tg00K`R0g00ilR1f1R2#@g00JBR3P3P3P1f0R3g013>P0P0P0g00k>R4g00l5R5P0C?R6P0P0P6P0P4P5P0C:C4f4g01XJ#2#2#<';%93%53F6/73W3f2R5'8P5n0100000020000#1#0%15#0530P3%12#0,>0R5P5n0110000020000b21=23#1#0%13#0530eX11X00P2P3O2W1W0o"). Qed.
Lemma c_meta_area_head_record_seq sc st : c_meta_area_head (s_ctx (record_seq sc st)) = c_meta_area_head (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1@Tg00Ebj4?Tg00<Xj4:Tg00:<j44Tg01T2j12Tg01TWj1<Tg01knj2;Tg01Naj19Tg01Lkj15Tg00g<j76Tg01gCj27Tg01i=j28Tg012Hj11Tg01H5j10Tg006oj33Tg00G1j2>Tg01lKj2=Tg00K`R0g00ilR1f1R2#@g00JBR3P3g00BLR4P3P1f0R3g013>P0P0P0g00k>R5g00l5R6P0C?R7P0P0P7P0P5P6P0C:C4f4g01XJ#2#2#<';%93%53F6/73W3f2R6'8P6n0100000020000#1#0%16#033P3%12#0,>4R6P6n0110000020000b21=23#1#0%13#0534eX11X00P2P3O2W1W0o"). Qed.
Lemma c_meta_area_tail_record_seq sc st : c_meta_area_tail (s_ctx (record_seq sc st)) = c_meta_area_tail (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1@Tg00Ebj4?Tg00<Xj4:Tg00:<j44Tg01T2j12Tg01TWj1<Tg01knj2;Tg01Naj19Tg01Lkj15Tg00g<j76Tg01gCj27Tg01i=j28Tg012Hj11Tg01I6j10Tg006oj33Tg00G1j2>Tg01lKj2=Tg00K`R0g00ilR1f1R2#@g00JBR3P3g00BLR4P3P1f0R3g013>P0P0P0g00k>R5g00l5R6P0C?R7P0P0P7P0P5P6P0C:C4f4g01XJ#2#2#<';%93%53F6/73W3f2R6'8P6n0100000020000#1#0%16#033P3%12#0,>4R6P6n0110000020000b21=23#1#0%13#0534eX11X00P2P3O2W1W0o"). Qed.
Lemma c_avail_meta_areas_record_seq sc st : c_avail_meta_areas (s_ctx (record_seq sc st)) = c_avail_meta_areas (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1@Tg00Ebj4?Tg00<Xj4:Tg00:<j44Tg01T2j12Tg01TWj1<Tg01knj2;Tg01Naj19Tg01Lkj15Tg00g<j76Tg01gCj27Tg01i=j28Tg012Hj11Tg01J7j10Tg006oj33Tg00G1j2>Tg01lKj2=Tg00K`R0g00ilR1f1R2#@g00JBR3P3g00BLR4P3P1f0R3g013>P0P0P0g00k>R5g00l5R6P0C?R7P0P0P7P0P5P6P0C:C4f4g01XJ#2#2#<';%93%53F6/73W3f2R6'8P6n0100000020000#1#0%16#033P3%12#0,>4R6P6n0110000020000b21=23#1#0%13#0534eX11X00P2P3O2W1W0o"). Qed.
Lemma c_active_record_seq sc st : c_active (s_ctx (record_seq sc st)) = c_active (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1@Tg00Ebj44Tg00<Xj4;Tg00:<j45Tg01T2j13Tg01TWj1>Tg01knj2<Tg01Naj1:Tg01Lkj19Tg00g<j76Tg01gCj27Tg01i=j28Tg012Hj10Tg01K:j11Tg006oj32Tg00G1j2?Tg01lKj2=Tg00K`R0g00ilR1f1R2#@g00JBR3P3P0g00k>R4g00l5R5g006:C4R6P3P1f0R3g013>P0P0P0P4P5P0C4R7P0P0P7P0P4P5P0C;C5f4g01XJ#3#3#>'<%:3%93F6/73W3f2R5'8P5n0100000020000#0#1%05#132P3%02#1,?6R5P5n0110000020000b21=23#0#1%03#1526eX11X00P2P3O2W1W0o"). Qed.
Lemma c_usage_record_seq sc st : c_usage (s_ctx (record_seq sc st)) = c_usage (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1@Tg00Ebj4?Tg00<Xj4:Tg00:<j44Tg01T2j12Tg01TWj1<Tg01knj2;Tg01Naj19Tg01Lkj15Tg00g<j76Tg01gCj27Tg01i=j28Tg012Hj11Tg01L3j10Tg006oj33Tg00G1j2>Tg01lKj2=Tg00K`R0g00ilR1f1R2#@g00JBR3P3P0g00k>R4g00l5R5P0C?R6P3P1f0R3g013>P0P0P6P0P0P6P0P4P5P0C:C4f4g01XJ#2#2#<';%93%53F6/73W3f2R5'8P5n0100000020000#1#0%15#033P3%12#0,>6R5P5n0110000020000b21=23#1#0%13#0536eX11X00P2P3O2W1W0o"). Qed.
Lemma c_bounces_record_seq sc st : c_bounces (s_ctx (record_seq sc st)) = c_bounces (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1@Tg00Ebj4?Tg00<Xj4:Tg00:<j44Tg01T2j12Tg01TWj1<Tg01knj2;Tg01Naj19Tg01Lkj15Tg00g<j76Tg01gCj27Tg01i=j28Tg012Hj11Tg01Mgj10Tg006oj33Tg00G1j2>Tg01lKj2=Tg00K`R0g00ilR1f1R2#@g00JBR3P3P0g00k>R4g00l5R5P0C?R6P3P1f0R3g013>P0P0P6P0P0P6P0P4P5P0C:C4f4g01XJ#2#2#<';%93%53F6/73W3f2R5'8P5n0100000020000#1#0%15#033P3%12#0,>6R5P5n0110000020000b21=23#1#0%13#0536eX11X00P2P3O2W1W0o"). Qed.
Lemma c_seq_record_seq sc st : c_seq (s_ctx (record_seq sc st)) = c_seq (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1?Tg00Ebj4>Tg00<Xj45Tg00:<j44Tg01T2j12Tg01TWj1;Tg01knj2:Tg01Naj10Tg01Lkj16Tg00g<j77Tg01gCj28Tg01i=j29Tg012Hj11Tg006oj33Tg00G1j2=Tg01lKj2<Tg00K`R0g00ilR1f1R2#?g00JBR3P3P3P1f0R3g013>P0P0P0g00k>R4g00l5R5P0C>R6P0P0P6P0P4P5P0C5C4f4g01XJ#2#2#;':%03%63F7/83W3f2R5'9P5n0100000020000#1#0%15#0530P3%12#0,=0R5P5n0110000020000b21<23#1#0%13#0530eX11X00P2P3O2W1W0o"). Qed.
Lemma c_brk_record_seq sc st : c_brk (s_ctx (record_seq sc st)) = c_brk (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;4p;2p;7p;3g01jnj1@Tg00Ebj4?Tg00<Xj4:Tg00:<j44Tg01T2j12Tg01TWj1<Tg01knj2;Tg01Naj19Tg01Lkj15Tg00g<j76Tg01gCj27Tg01i=j28Tg012Hj11Tg01OWj10Tg006oj33Tg00G1j2>Tg01lKj2=Tg00K`R0g00ilR1f1R2#@g00JBR3P3g01PMR4P3P1f0R3g013>P0P0P0g00k>R5g00l5R6P0C?R7P0P0P7P0P5P6P0C:C4f4g01XJ#2#2#<';%93%53F6/73W3f2R6'8P6n0100000020000#1#0%16#033P3%12#0,>4R6P6n0110000020000b21=23#1#0%13#0534eX11X00P2P3O2W1W0o"). Qed.
Lemma c_secret_account_bounce sc st : c_secret (s_ctx (account_bounce sc st)) = c_secret (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1KTg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1>Tg01Naj1ATg01e9j10Tg01]8j29Tg00FSj2=Tg01n^j2:Tg01\>j2;Tg00Ebj4JTg00<Xj4ITg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg006oj38Tg00G1j2<Tg020Vj2DTg00g<j7CTg012Hj1GTg01QHj1HTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5%G5#Hp=1g00ilR6%K4g00JBR7P7P7P6P5P7P6g01XJR8#3R9#3#7R:,22R;,B3R<g01e^R='@#?%>3#A/2<%08R<#3#0#7R>'9'=P7P61:3;%78R8';%09#0#3#0#0#7R9'9R;g013>R?P0g00k>R@g00l5RAP0CJRBP0P0PBP0P@PAP0CICFRA121:R@1:2@/;8RC%E5RDD5/65W0/43PBPAP@%0<#3#0#3#3#0#7R<PDD5/65X0?/43n0100000020000P3n0100000020000P3n0100000020000#1%13R@580P5123:,B4R3/@=#?%>4#A/23/9>'=P7P7P7P6P5P7P619C9PBPAf5RC/2:R91:19/;8PDD5/65X0?/42PBPAP9P<PDD5/65X0?/42n0100000020000P2n0100000020000#1%12R2580P5P;P7P7P7P6P5PBPAf6/2:R:1:C:/;8PDD5/65X0?/41PBPAP:P<PDD5/65X0?/41n0100000020000#1%11580P51<02R2P2n0110000020000b11<0@n0110000020000b1%14,<0n0110000020100b11D45#1%15580eX36X20P4P5O2W3X20o"). Qed.
Lemma c_init_done_account_bounce sc st : c_init_done (s_ctx (account_bounce sc st)) = c_init_done (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1KTg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1>Tg01Naj1ATg01e9j10Tg01]8j29Tg00FSj2=Tg01n^j2:Tg01\>j2;Tg00Ebj4JTg00<Xj4ITg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg006oj38Tg00G1j2<Tg020Vj2DTg00g<j7CTg012Hj1GTg01@nj1HTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5%G5#Hp=1g00ilR6%K4g00JBR7P7P7P6P5P7P6g01XJR8#3R9#3#7R:,22R;,B3R<g01e^R='@#?%>3#A/2<%08R<#3#0#7R>'9'=P7P61:3;%78R8';%09#0#3#0#0#7R9'9R;g013>R?P0g00k>R@g00l5RAP0CJRBP0P0PBP0P@PAP0CICFRA121:R@1:2@/;8RC%E5RDD5/65W0/43PBPAP@%0<#3#0#3#3#0#7R<PDD5/65X0?/43n0100000020000P3n0100000020000P3n0100000020000#1%13R@580P5123:,B4R3/@=#?%>4#A/23/9>'=P7P7P7P6P5P7P619C9PBPAf5RC/2:R91:19/;8PDD5/65X0?/42PBPAP9P<PDD5/65X0?/42n0100000020000P2n0100000020000#1%12R2580P5P;P7P7P7P6P5PBPAf6/2:R:1:C:/;8PDD5/65X0?/41PBPAP:P<PDD5/65X0?/41n0100000020000#1%11580P51<02R2P2n0110000020000b11<0@n0110000020000b1%14,<0n0110000020100b11D45#1%15580eX36X20P4P5O2W3X20o"). Qed.
Lemma c_mmap_counter_account_bounce sc st : c_mmap_counter (s_ctx (account_bounce sc st)) = c_mmap_counter (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1KTg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1>Tg01Naj1ATg01e9j10Tg01]8j29Tg00FSj2=Tg01n^j2:Tg01\>j2;Tg00Ebj4JTg00<Xj4ITg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg006oj38Tg00G1j2<Tg020Vj2DTg00g<j7CTg012Hj1GTg01Ajj1HTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5%G5#Hp=1g00ilR6%K4g00JBR7P7P7P6P5P7P6g01XJR8#3R9#3#7R:,22R;,B3R<g01e^R='@#?%>3#A/2<%08R<#3#0#7R>'9'=P7P61:3;%78R8';%09#0#3#0#0#7R9'9R;g013>R?P0g00k>R@g00l5RAP0CJRBP0P0PBP0P@PAP0CICFRA121:R@1:2@/;8RC%E5RDD5/65W0/43PBPAP@%0<#3#0#3#3#0#7R<PDD5/65X0?/43n0100000020000P3n0100000020000P3n0100000020000#1%13R@580P5123:,B4R3/@=#?%>4#A/23/9>'=P7P7P7P6P5P7P619C9PBPAf5RC/2:R91:19/;8PDD5/65X0?/42PBPAP9P<PDD5/65X0?/42n0100000020000P2n0100000020000#1%12R2580P5P;P7P7P7P6P5PBPAf6/2:R:1:C:/;8PDD5/65X0?/41PBPAP:P<PDD5/65X0?/41n0100000020000#1%11580P51<02R2P2n0110000020000b11<0@n0110000020000b1%14,<0n0110000020100b11D45#1%15580eX36X20P4P5O2W3X20o"). Qed.
Lemma c_free_meta_head_account_bounce sc st : c_free_meta_head (s_ctx (account_bounce sc st)) = c_free_meta_head (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1KTg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1>Tg01Naj1ATg01e9j10Tg01]8j29Tg00FSj2=Tg01n^j2:Tg01\>j2;Tg00Ebj4JTg00<Xj4ITg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg006oj38Tg00G1j2<Tg020Vj2DTg00g<j7CTg012Hj1GTg01Bij1HTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5%G5#Hp=1g00ilR6%K4g00JBR7P7g00BLR8P7P6P5P7P6g01XJR9#3R:#3#7R;,22R<,B3R=g01e^R>'@#?%>3#A/2=%09R=#3#0#7R?'9'=P7P61:3<%79R9';%0:#0#3#0#0#7R:'9R<g013>R@P0g00k>RAg00l5RBP0CJRCP0P0PCP0PAPBP0CICFRB121;RA1:2A/;9RD%E5RED5/65W0/43PCPBPA%0=#3#0#3#3#0#7R=PED5/65X0@/43n0100000020000P3n0100000020000P3n0100000020000#1%13RA38P5123;,B4R3/@>#?%>4#A/23/9?'=P7P7P7P6P5P7P619D:PCPBf5RD/2;R:1:1:/;9PED5/65X0@/42PCPBP:P=PED5/65X0@/42n0100000020000P2n0100000020000#1%12R2588P5P<P7P7P7P6P5PCPBf6/2;R;1:D;/;9PED5/65X0@/41PCPBP;P=PED5/65X0@/41n0100000020000#1%11588P51<82R2P2n0110000020000b11<8An0110000020000b1%14,<8n0110000020100b11D45#1%15588eX36X20P4P5O2W3X20o"). Qed.
Lemma c_avail_meta_account_bounce sc st : c_avail_meta (s_ctx (account_bounce sc st)) = c_avail_meta (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1KTg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1>Tg01Naj1ATg01e9j10Tg01]8j29Tg00FSj2=Tg01n^j2:Tg01\>j2;Tg00Ebj4JTg00<Xj4ITg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg006oj38Tg00G1j2<Tg020Vj2DTg00g<j7CTg012Hj1GTg01Cjj1HTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5%G5#Hp=1g00ilR6%K4g00JBR7P7g00BLR8P7P6P5P7P6g01XJR9#3R:#3#7R;,22R<,B3R=g01e^R>'@#?%>3#A/2=%09R=#3#0#7R?'9'=P7P61:3<%79R9';%0:#0#3#0#0#7R:'9R<g013>R@P0g00k>RAg00l5RBP0CJRCP0P0PCP0PAPBP0CICFRB121;RA1:2A/;9RD%E5RED5/65W0/43PCPBPA%0=#3#0#3#3#0#7R=PED5/65X0@/43n0100000020000P3n0100000020000P3n0100000020000#1%13RA38P5123;,B4R3/@>#?%>4#A/23/9?'=P7P7P7P6P5P7P619D:PCPBf5RD/2;R:1:1:/;9PED5/65X0@/42PCPBP:P=PED5/65X0@/42n0100000020000P2n0100000020000#1%12R2588P5P<P7P7P7P6P5PCPBf6/2;R;1:D;/;9PED5/65X0@/41PCPBP;P=PED5/65X0@/41n0100000020000#1%11588P51<82R2P2n0110000020000b11<8An0110000020000b1%14,<8n0110000020100b11D45#1%15588eX36X20P4P5O2W3X20o"). Qed.
Lemma c_avail_meta_count_account_bounce sc st : c_avail_meta_count (s_ctx (account_bounce sc st)) = c_avail_meta_count (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1KTg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1>Tg01Naj1ATg01e9j10Tg01]8j29Tg00FSj2=Tg01n^j2:Tg01\>j2;Tg00Ebj4JTg00<Xj4ITg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg006oj38Tg00G1j2<Tg020Vj2DTg00g<j7CTg012Hj1GTg01Dgj1HTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5%G5#Hp=1g00ilR6%K4g00JBR7P7P7P6P5P7P6g01XJR8#3R9#3#7R:,22R;,B3R<g01e^R='@#?%>3#A/2<%08R<#3#0#7R>'9'=P7P61:3;%78R8';%09#0#3#0#0#7R9'9R;g013>R?P0g00k>R@g00l5RAP0CJRBP0P0PBP0P@PAP0CICFRA121:R@1:2@/;8RC%E5RDD5/65W0/43PBPAP@%0<#3#0#3#3#0#7R<PDD5/65X0?/43n0100000020000P3n0100000020000P3n0100000020000#1%13R@580P5123:,B4R3/@=#?%>4#A/23/9>'=P7P7P7P6P5P7P619C9PBPAf5RC/2:R91:19/;8PDD5/65X0?/42PBPAP9P<PDD5/65X0?/42n0100000020000P2n0100000020000#1%12R2580P5P;P7P7P7P6P5PBPAf6/2:R:1:C:/;8PDD5/65X0?/41PBPAP:P<PDD5/65X0?/41n0100000020000#1%11580P51<02R2P2n0110000020000b11<0@n0110000020000b1%14,<0n0110000020100b11D45#1%15580eX36X20P4P5O2W3X20o"). Qed.
Lemma c_avail_meta_area_count_account_bounce sc st : c_avail_meta_area_count (s_ctx (account_bounce sc st)) = c_avail_meta_area_count (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1KTg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1>Tg01Naj1ATg01e9j10Tg01]8j29Tg00FSj2=Tg01n^j2:Tg01\>j2;Tg00Ebj4JTg00<Xj4ITg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg006oj38Tg00G1j2<Tg020Vj2DTg00g<j7CTg012Hj1GTg01Ejj1HTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5%G5#Hp=1g00ilR6%K4g00JBR7P7P7P6P5P7P6g01XJR8#3R9#3#7R:,22R;,B3R<g01e^R='@#?%>3#A/2<%08R<#3#0#7R>'9'=P7P61:3;%78R8';%09#0#3#0#0#7R9'9R;g013>R?P0g00k>R@g00l5RAP0CJRBP0P0PBP0P@PAP0CICFRA121:R@1:2@/;8RC%E5RDD5/65W0/43PBPAP@%0<#3#0#3#3#0#7R<PDD5/65X0?/43n0100000020000P3n0100000020000P3n0100000020000#1%13R@580P5123:,B4R3/@=#?%>4#A/23/9>'=P7P7P7P6P5P7P619C9PBPAf5RC/2:R91:19/;8PDD5/65X0?/42PBPAP9P<PDD5/65X0?/42n0100000020000P2n0100000020000#1%12R2580P5P;P7P7P7P6P5PBPAf6/2:R:1:C:/;8PDD5/65X0?/41PBPAP:P<PDD5/65X0?/41n0100000020000#1%11580P51<02R2P2n0110000020000b11<0@n0110000020000b1%14,<0n0110000020100b11D45#1%15580eX36X20P4P5O2W3X20o"). Qed.
Lemma c_meta_alloc_shift_account_bounce sc st : c_meta_alloc_shift (s_ctx (account_bounce sc st)) = c_meta_alloc_shift (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1KTg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1>Tg01Naj1ATg01e9j10Tg01]8j29Tg00FSj2=Tg01n^j2:Tg01\>j2;Tg00Ebj4JTg00<Xj4ITg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg006oj38Tg00G1j2<Tg020Vj2DTg00g<j7CTg012Hj1GTg01G2j1HTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5%G5#Hp=1g00ilR6%K4g00JBR7P7P7P6P5P7P6g01XJR8#3R9#3#7R:,22R;,B3R<g01e^R='@#?%>3#A/2<%08R<#3#0#7R>'9'=P7P61:3;%78R8';%09#0#3#0#0#7R9'9R;g013>R?P0g00k>R@g00l5RAP0CJRBP0P0PBP0P@PAP0CICFRA121:R@1:2@/;8RC%E5RDD5/65W0/43PBPAP@%0<#3#0#3#3#0#7R<PDD5/65X0?/43n0100000020000P3n0100000020000P3n0100000020000#1%13R@580P5123:,B4R3/@=#?%>4#A/23/9>'=P7P7P7P6P5P7P619C9PBPAf5RC/2:R91:19/;8PDD5/65X0?/42PBPAP9P<PDD5/65X0?/42n0100000020000P2n0100000020000#1%12R2580P5P;P7P7P7P6P5PBPAf6/2:R:1:C:/;8PDD5/65X0?/41PBPAP:P<PDD5/65X0?/41n0100000020000#1%11580P51<02R2P2n0110000020000b11<0@n0110000020000b1%14,<0n0110000020100b11D45#1%15580eX36X20P4P5O2W3X20o"). Qed.
Lemma c_meta_area_head_account_bounce sc st : c_meta_area_head (s_ctx (account_bounce sc st)) = c_meta_area_head (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1KTg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1>Tg01Naj1ATg01e9j10Tg01]8j29Tg00FSj2=Tg01n^j2:Tg01\>j2;Tg00Ebj4JTg00<Xj4ITg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg006oj38Tg00G1j2<Tg020Vj2DTg00g<j7CTg012Hj1GTg01H5j1HTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5%G5#Hp=1g00ilR6%K4g00JBR7P7g00BLR8P7P6P5P7P6g01XJR9#3R:#3#7R;,22R<,B3R=g01e^R>'@#?%>3#A/2=%09R=#3#0#7R?'9'=P7P61:3<%79R9';%0:#0#3#0#0#7R:'9R<g013>R@P0g00k>RAg00l5RBP0CJRCP0P0PCP0PAPBP0CICFRB121;RA1:2A/;9RD%E5RED5/65W0/43PCPBPA%0=#3#0#3#3#0#7R=PED5/65X0@/43n0100000020000P3n0100000020000P3n0100000020000#1%13RA38P5123;,B4R3/@>#?%>4#A/23/9?'=P7P7P7P6P5P7P619D:PCPBf5RD/2;R:1:1:/;9PED5/65X0@/42PCPBP:P=PED5/65X0@/42n0100000020000P2n0100000020000#1%12R2588P5P<P7P7P7P6P5PCPBf6/2;R;1:D;/;9PED5/65X0@/41PCPBP;P=PED5/65X0@/41n0100000020000#1%11588P51<82R2P2n0110000020000b11<8An0110000020000b1%14,<8n0110000020100b11D45#1%15588eX36X20P4P5O2W3X20o"). Qed.
Lemma c_meta_area_tail_account_bounce sc st : c_meta_area_tail (s_ctx (account_bounce sc st)) = c_meta_area_tail (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1KTg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1>Tg01Naj1ATg01e9j10Tg01]8j29Tg00FSj2=Tg01n^j2:Tg01\>j2;Tg00Ebj4JTg00<Xj4ITg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg006oj38Tg00G1j2<Tg020Vj2DTg00g<j7CTg012Hj1GTg01I6j1HTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5%G5#Hp=1g00ilR6%K4g00JBR7P7g00BLR8P7P6P5P7P6g01XJR9#3R:#3#7R;,22R<,B3R=g01e^R>'@#?%>3#A/2=%09R=#3#0#7R?'9'=P7P61:3<%79R9';%0:#0#3#0#0#7R:'9R<g013>R@P0g00k>RAg00l5RBP0CJRCP0P0PCP0PAPBP0CICFRB121;RA1:2A/;9RD%E5RED5/65W0/43PCPBPA%0=#3#0#3#3#0#7R=PED5/65X0@/43n0100000020000P3n0100000020000P3n0100000020000#1%13RA38P5123;,B4R3/@>#?%>4#A/23/9?'=P7P7P7P6P5P7P619D:PCPBf5RD/2;R:1:1:/;9PED5/65X0@/42PCPBP:P=PED5/65X0@/42n0100000020000P2n0100000020000#1%12R2588P5P<P7P7P7P6P5PCPBf6/2;R;1:D;/;9PED5/65X0@/41PCPBP;P=PED5/65X0@/41n0100000020000#1%11588P51<82R2P2n0110000020000b11<8An0110000020000b1%14,<8n0110000020100b11D45#1%15588eX36X20P4P5O2W3X20o"). Qed.
Lemma c_avail_meta_areas_account_bounce sc st : c_avail_meta_areas (s_ctx (account_bounce sc st)) = c_avail_meta_areas (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1KTg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1>Tg01Naj1ATg01e9j10Tg01]8j29Tg00FSj2=Tg01n^j2:Tg01\>j2;Tg00Ebj4JTg00<Xj4ITg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg006oj38Tg00G1j2<Tg020Vj2DTg00g<j7CTg012Hj1GTg01J7j1HTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5%G5#Hp=1g00ilR6%K4g00JBR7P7g00BLR8P7P6P5P7P6g01XJR9#3R:#3#7R;,22R<,B3R=g01e^R>'@#?%>3#A/2=%09R=#3#0#7R?'9'=P7P61:3<%79R9';%0:#0#3#0#0#7R:'9R<g013>R@P0g00k>RAg00l5RBP0CJRCP0P0PCP0PAPBP0CICFRB121;RA1:2A/;9RD%E5RED5/65W0/43PCPBPA%0=#3#0#3#3#0#7R=PED5/65X0@/43n0100000020000P3n0100000020000P3n0100000020000#1%13RA38P5123;,B4R3/@>#?%>4#A/23/9?'=P7P7P7P6P5P7P619D:PCPBf5RD/2;R:1:1:/;9PED5/65X0@/42PCPBP:P=PED5/65X0@/42n0100000020000P2n0100000020000#1%12R2588P5P<P7P7P7P6P5PCPBf6/2;R;1:D;/;9PED5/65X0@/41PCPBP;P=PED5/65X0@/41n0100000020000#1%11588P51<82R2P2n0110000020000b11<8An0110000020000b1%14,<8n0110000020100b11D45#1%15588eX36X20P4P5O2W3X20o"). Qed.
Lemma c_active_account_bounce sc st : c_active (s_ctx (account_bounce sc st)) = c_active (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;4p;2p;3p;7g01jnj1KTg00Ebj4CTg01T2j12Tg01TWj17Tg01knj23Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1ATg01Naj1>Tg01e9j11Tg01]8j28Tg00FSj2=Tg01n^j2;Tg01\>j29Tg00<Xj4JTg00:<j4ITg01Mgj1HTg01oVj26Tg01i=j25Tg006oj3:Tg00G1j2<Tg020Vj2ETg00g<j7DTg012Hj1FTg01K:j1GTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FDp=4%F5#Gp=0g00ilR6%K4g00JBR7P7P0g00k>R8g00l5R9g006:CCR:P7P6P5P7P6g01XJR;#2R<#2#7R=,32R>,B3R?g01e^R@'@#?%A3#>/3?%1;R?#2#1#7RA'8'=P7P61;3>%7;R;'9%1<#1#2#1#1#7R<'8R>g013>RBP0P8P9P0CCRCP0P0PCP0P8P9P0CJCIR9131=R81;28/9;RD%H5RED4/65W0/53PCP9P8%1?#2#1#2#2#1#7R?PED4/65X0B/53n0100000020000P3n0100000020000P3n0100000020000#0%03R83:P5133=,B4R3/@@#?%A4#>/33/8A'=P7P7P7P6P5P7P618D<PCP9f5RD/3=R<1;1</9;PED4/65X0B/52PCP9P<P?PED4/65X0B/52n0100000020000P2n0100000020000#0%02R25::P5P>P7P7P7P6P5PCP9f6/3=R=1;D=/9;PED4/65X0B/51PCP9P=P?PED4/65X0B/51n0100000020000#0%015::P51<:2R2P2n0110000020000b11<:8n0110000020000b1%04,<:n0110000020100b11E45#0%055::eX36X20P4P5O2W3X20o"). Qed.
Lemma c_usage_account_bounce sc st : c_usage (s_ctx (account_bounce sc st)) = c_usage (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;4p;2p;3p;7g01jnj1KTg00Ebj4JTg01T2j12Tg01TWj17Tg01knj23Tg01mFj2ATg00F6j2@Tg01n@j1?Tg01f<j1BTg01Naj1>Tg01e9j11Tg01]8j28Tg00FSj2=Tg01n^j2;Tg01\>j29Tg00<Xj4ITg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg006oj3:Tg00G1j2<Tg020Vj2DTg00g<j7CTg012Hj1GTg01L3j1HTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5%G5#Hp=0g00ilR6%K4g00JBR7P7P0g00k>R8g00l5R9P0CJR:P7P6P5P7P6g01XJR;#2R<#2#7R=,32R>,A3R?g01e^R@'@#?%B3#>/3?%1;R?#2#1#7RA'8'=P7P61;3>%7;R;'9%1<#1#2#1#1#7R<'8R>g013>RBP:P0P0P:P0P8P9P0CICFR9131=R81;28/9;RC%E5RDD5/65W0/43P:P9P8%1?#2#1#2#2#1#7R?PDD5/65X0B/43n0100000020000P3n0100000020000P3n0100000020000#0%03R83:P5133=,A4R3/@@#?%B4#>/33/8A'=P7P7P7P6P5P7P618C<P:P9f5RC/3=R<1;1</9;PDD5/65X0B/42P:P9P<P?PDD5/65X0B/42n0100000020000P2n0100000020000#0%02R25::P5P>P7P7P7P6P5P:P9f6/3=R=1;C=/9;PDD5/65X0B/41P:P9P=P?PDD5/65X0B/41n0100000020000#0%015::P51<:2R2P2n0110000020000b11<:8n0110000020000b1%04,<:n0110000020100b11D45#0%055::eX36X20P4P5O2W3X20o"). Qed.
Lemma c_unmap_seq_account_bounce sc st : c_unmap_seq (s_ctx (account_bounce sc st)) = c_unmap_seq (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;4p;2p;3p;7g01jnj1KTg00Ebj4JTg01T2j12Tg01TWj17Tg01knj23Tg01mFj2ATg00F6j2@Tg01n@j1?Tg01f<j1BTg01Naj1>Tg01e9j11Tg01]8j28Tg00FSj2=Tg01n^j2;Tg01\>j29Tg00<Xj4ITg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg006oj3:Tg00G1j2<Tg020Vj2DTg00g<j7CTg012Hj1GTg01Lkj1HTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5%G5#Hp=0g00ilR6%K4g00JBR7P7P0g00k>R8g00l5R9P0CJR:P7P6P5P7P6g01XJR;#2R<#2#7R=,32R>,A3R?g01e^R@'@#?%B3#>/3?%1;R?#2#1#7RA'8'=P7P61;3>%7;R;'9%1<#1#2#1#1#7R<'8R>g013>RBP:P0P0P:P0P8P9P0CICFR9131=R81;28/9;RC%E5RDD5/65W0/43P:P9P8%1?#2#1#2#2#1#7R?PDD5/65X0B/43n0100000020000P3n0100000020000P3n0100000020000#0%03R83:P5133=,A4R3/@@#?%B4#>/33/8A'=P7P7P7P6P5P7P618C<P:P9f5RC/3=R<1;1</9;PDD5/65X0B/42P:P9P<P?PDD5/65X0B/42n0100000020000P2n0100000020000#0%02R25::P5P>P7P7P7P6P5P:P9f6/3=R=1;C=/9;PDD5/65X0B/41P:P9P=P?PDD5/65X0B/41n0100000020000#0%015::P51<:2R2P2n0110000020000b11<:8n0110000020000b1%04,<:n0110000020100b11D45#0%055::eX36X20P4P5O2W3X20o"). Qed.
Lemma c_seq_account_bounce sc st : c_seq (s_ctx (account_bounce sc st)) = c_seq (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1JTg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2ATg01n@j1@Tg01f<j1?Tg01Naj1=Tg01e9j10Tg01]8j28Tg00FSj2>Tg01n^j29Tg01\>j2;Tg00Ebj4ITg00<Xj4HTg00:<j4FTg01Mgj1ETg01oVj25Tg01i=j24Tg006oj3:Tg00G1j2<Tg020Vj2DTg00g<j7CTg012Hj1GTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=6%G5#=p=1g00ilR6%J4g00JBR7P7P7P6P5P7P6g01XJR8#3R9#3#7R:,22R;,B3R<g01e^R='A#@%?3#=/2<%08R<#3#0#7R>'8'>P7P6193;%78R8';%09#0#3#0#0#7R9'8R;g013>R?P0g00k>R@g00l5RAP0CIRBP0P0PBP0P@PAP0CHCFRA121:R@192@/;8RC%E5RDD6/55W0/43PBPAP@%0<#3#0#3#3#0#7R<PDD6/55X0?/43n0100000020000P3n0100000020000P3n0100000020000#1%13R@5:0P5123:,B4R3/A=#@%?4#=/23/8>'>P7P7P7P6P5P7P618C9PBPAf5RC/2:R91919/;8PDD6/55X0?/42PBPAP9P<PDD6/55X0?/42n0100000020000P2n0100000020000#1%12R25:0P5P;P7P7P7P6P5PBPAf6/2:R:19C:/;8PDD6/55X0?/41PBPAP:P<PDD6/55X0?/41n0100000020000#1%115:0P51<02R2P2n0110000020000b11<0@n0110000020000b1%14,<0n0110000020100b11D45#1%155:0eX36X20P4P5O2W3X20o"). Qed.
Lemma c_brk_account_bounce sc st : c_brk (s_ctx (account_bounce sc st)) = c_brk (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ch11bi001bh22sch32stp;1p;2p;4p;3p;7g01jnj1KTg01T2j13Tg01TWj17Tg01knj22Tg01mFj2BTg00F6j2@Tg01n@j1?Tg01f<j1>Tg01Naj1ATg01e9j10Tg01]8j29Tg00FSj2=Tg01n^j2:Tg01\>j2;Tg00Ebj4JTg00<Xj4ITg00:<j4FTg01Mgj1ETg01oVj26Tg01i=j24Tg006oj38Tg00G1j2<Tg020Vj2DTg00g<j7CTg012Hj1GTg01OWj1HTg00K`R0P0f4R1f3R2f2R3f1R4f0R5FCp=5%G5#Hp=1g00ilR6%K4g00JBR7P7g01PMR8P7P6P5P7P6g01XJR9#3R:#3#7R;,22R<,B3R=g01e^R>'@#?%>3#A/2=%09R=#3#0#7R?'9'=P7P61:3<%79R9';%0:#0#3#0#0#7R:'9R<g013>R@P0g00k>RAg00l5RBP0CJRCP0P0PCP0PAPBP0CICFRB121;RA1:2A/;9RD%E5RED5/65W0/43PCPBPA%0=#3#0#3#3#0#7R=PED5/65X0@/43n0100000020000P3n0100000020000P3n0100000020000#1%13RA38P5123;,B4R3/@>#?%>4#A/23/9?'=P7P7P7P6P5P7P619D:PCPBf5RD/2;R:1:1:/;9PED5/65X0@/42PCPBP:P=PED5/65X0@/42n0100000020000P2n0100000020000#1%12R2588P5P<P7P7P7P6P5PCPBf6/2;R;1:D;/;9PED5/65X0@/41PCPBP;P=PED5/65X0@/41n0100000020000#1%11588P51<82R2P2n0110000020000b11<8An0110000020000b1%14,<8n0110000020100b11D45#1%15588eX36X20P4P5O2W3X20o"). Qed.
Lemma c_secret_decay_bounces sc st : c_secret (s_ctx (decay_bounces sc st)) = c_secret (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1CTg01T2j13Tg01TWj14Tg01knj22Tg01n^j26Tg00F6j2>Tg01n@j1=Tg00FSj2<Tg00Ebj4;Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2BTg01i=j2ATg012Hj11Tg01QHj10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Cf0R3g01XJR4#3#3#4R5,22'6g01e^'>#='<g00JBR6P6P6P1P3g013>P0P0P0g00k>R6g00l5R7P0C;R8P0P0P8P0P6P7P0C:C7f4/25R5f3/65%44'2%83F9/B3W3f2R4'AP4n0100000020000#1#0%14#0550P3%12#0,?0R4P4n0110000020000b21@23#1#0%13#0550eX11X00P2P3O2W1W0o"). Qed.
Lemma c_init_done_decay_bounces sc st : c_init_done (s_ctx (decay_bounces sc st)) = c_init_done (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1CTg01T2j13Tg01TWj14Tg01knj22Tg01n^j26Tg00F6j2>Tg01n@j1=Tg00FSj2<Tg00Ebj4;Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2BTg01i=j2ATg012Hj11Tg01@nj10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Cf0R3g01XJR4#3#3#4R5,22'6g01e^'>#='<g00JBR6P6P6P1P3g013>P0P0P0g00k>R6g00l5R7P0C;R8P0P0P8P0P6P7P0C:C7f4/25R5f3/65%44'2%83F9/B3W3f2R4'AP4n0100000020000#1#0%14#0550P3%12#0,?0R4P4n0110000020000b21@23#1#0%13#0550eX11X00P2P3O2W1W0o"). Qed.
Lemma c_mmap_counter_decay_bounces sc st : c_mmap_counter (s_ctx (decay_bounces sc st)) = c_mmap_counter (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1CTg01T2j13Tg01TWj14Tg01knj22Tg01n^j26Tg00F6j2>Tg01n@j1=Tg00FSj2<Tg00Ebj4;Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2BTg01i=j2ATg012Hj11Tg01Ajj10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Cf0R3g01XJR4#3#3#4R5,22'6g01e^'>#='<g00JBR6P6P6P1P3g013>P0P0P0g00k>R6g00l5R7P0C;R8P0P0P8P0P6P7P0C:C7f4/25R5f3/65%44'2%83F9/B3W3f2R4'AP4n0100000020000#1#0%14#0550P3%12#0,?0R4P4n0110000020000b21@23#1#0%13#0550eX11X00P2P3O2W1W0o"). Qed.
Lemma c_free_meta_head_decay_bounces sc st : c_free_meta_head (s_ctx (decay_bounces sc st)) = c_free_meta_head (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1CTg01T2j13Tg01TWj14Tg01knj22Tg01n^j26Tg00F6j2>Tg01n@j1=Tg00FSj2<Tg00Ebj4;Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2BTg01i=j2ATg012Hj11Tg01Bij10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Cf0R3g01XJR4#3#3#4R5,22'6g01e^'>#='<g00JBR6P6g00BLR7P6P1P3g013>P0P0P0g00k>R6g00l5R8P0C;R9P0P0P9P0P6P8P0C:C7f4/25R5f3/65%44'2%83F9/B3W3f2R4'AP4n0100000020000#1#0%14#035P3%12#0,?7R4P4n0110000020000b21@23#1#0%13#0557eX11X00P2P3O2W1W0o"). Qed.
Lemma c_avail_meta_decay_bounces sc st : c_avail_meta (s_ctx (decay_bounces sc st)) = c_avail_meta (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1CTg01T2j13Tg01TWj14Tg01knj22Tg01n^j26Tg00F6j2>Tg01n@j1=Tg00FSj2<Tg00Ebj4;Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2BTg01i=j2ATg012Hj11Tg01Cjj10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Cf0R3g01XJR4#3#3#4R5,22'6g01e^'>#='<g00JBR6P6g00BLR7P6P1P3g013>P0P0P0g00k>R6g00l5R8P0C;R9P0P0P9P0P6P8P0C:C7f4/25R5f3/65%44'2%83F9/B3W3f2R4'AP4n0100000020000#1#0%14#035P3%12#0,?7R4P4n0110000020000b21@23#1#0%13#0557eX11X00P2P3O2W1W0o"). Qed.
Lemma c_avail_meta_count_decay_bounces sc st : c_avail_meta_count (s_ctx (decay_bounces sc st)) = c_avail_meta_count (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1CTg01T2j13Tg01TWj14Tg01knj22Tg01n^j26Tg00F6j2>Tg01n@j1=Tg00FSj2<Tg00Ebj4;Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2BTg01i=j2ATg012Hj11Tg01Dgj10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Cf0R3g01XJR4#3#3#4R5,22'6g01e^'>#='<g00JBR6P6P6P1P3g013>P0P0P0g00k>R6g00l5R7P0C;R8P0P0P8P0P6P7P0C:C7f4/25R5f3/65%44'2%83F9/B3W3f2R4'AP4n0100000020000#1#0%14#0550P3%12#0,?0R4P4n0110000020000b21@23#1#0%13#0550eX11X00P2P3O2W1W0o"). Qed.
Lemma c_avail_meta_area_count_decay_bounces sc st : c_avail_meta_area_count (s_ctx (decay_bounces sc st)) = c_avail_meta_area_count (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1CTg01T2j13Tg01TWj14Tg01knj22Tg01n^j26Tg00F6j2>Tg01n@j1=Tg00FSj2<Tg00Ebj4;Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2BTg01i=j2ATg012Hj11Tg01Ejj10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Cf0R3g01XJR4#3#3#4R5,22'6g01e^'>#='<g00JBR6P6P6P1P3g013>P0P0P0g00k>R6g00l5R7P0C;R8P0P0P8P0P6P7P0C:C7f4/25R5f3/65%44'2%83F9/B3W3f2R4'AP4n0100000020000#1#0%14#0550P3%12#0,?0R4P4n0110000020000b21@23#1#0%13#0550eX11X00P2P3O2W1W0o"). Qed.
Lemma c_meta_alloc_shift_decay_bounces sc st : c_meta_alloc_shift (s_ctx (decay_bounces sc st)) = c_meta_alloc_shift (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1CTg01T2j13Tg01TWj14Tg01knj22Tg01n^j26Tg00F6j2>Tg01n@j1=Tg00FSj2<Tg00Ebj4;Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2BTg01i=j2ATg012Hj11Tg01G2j10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Cf0R3g01XJR4#3#3#4R5,22'6g01e^'>#='<g00JBR6P6P6P1P3g013>P0P0P0g00k>R6g00l5R7P0C;R8P0P0P8P0P6P7P0C:C7f4/25R5f3/65%44'2%83F9/B3W3f2R4'AP4n0100000020000#1#0%14#0550P3%12#0,?0R4P4n0110000020000b21@23#1#0%13#0550eX11X00P2P3O2W1W0o"). Qed.
Lemma c_meta_area_head_decay_bounces sc st : c_meta_area_head (s_ctx (decay_bounces sc st)) = c_meta_area_head (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1CTg01T2j13Tg01TWj14Tg01knj22Tg01n^j26Tg00F6j2>Tg01n@j1=Tg00FSj2<Tg00Ebj4;Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2BTg01i=j2ATg012Hj11Tg01H5j10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Cf0R3g01XJR4#3#3#4R5,22'6g01e^'>#='<g00JBR6P6g00BLR7P6P1P3g013>P0P0P0g00k>R6g00l5R8P0C;R9P0P0P9P0P6P8P0C:C7f4/25R5f3/65%44'2%83F9/B3W3f2R4'AP4n0100000020000#1#0%14#035P3%12#0,?7R4P4n0110000020000b21@23#1#0%13#0557eX11X00P2P3O2W1W0o"). Qed.
Lemma c_meta_area_tail_decay_bounces sc st : c_meta_area_tail (s_ctx (decay_bounces sc st)) = c_meta_area_tail (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1CTg01T2j13Tg01TWj14Tg01knj22Tg01n^j26Tg00F6j2>Tg01n@j1=Tg00FSj2<Tg00Ebj4;Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2BTg01i=j2ATg012Hj11Tg01I6j10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Cf0R3g01XJR4#3#3#4R5,22'6g01e^'>#='<g00JBR6P6g00BLR7P6P1P3g013>P0P0P0g00k>R6g00l5R8P0C;R9P0P0P9P0P6P8P0C:C7f4/25R5f3/65%44'2%83F9/B3W3f2R4'AP4n0100000020000#1#0%14#035P3%12#0,?7R4P4n0110000020000b21@23#1#0%13#0557eX11X00P2P3O2W1W0o"). Qed.
Lemma c_avail_meta_areas_decay_bounces sc st : c_avail_meta_areas (s_ctx (decay_bounces sc st)) = c_avail_meta_areas (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1CTg01T2j13Tg01TWj14Tg01knj22Tg01n^j26Tg00F6j2>Tg01n@j1=Tg00FSj2<Tg00Ebj4;Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2BTg01i=j2ATg012Hj11Tg01J7j10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Cf0R3g01XJR4#3#3#4R5,22'6g01e^'>#='<g00JBR6P6g00BLR7P6P1P3g013>P0P0P0g00k>R6g00l5R8P0C;R9P0P0P9P0P6P8P0C:C7f4/25R5f3/65%44'2%83F9/B3W3f2R4'AP4n0100000020000#1#0%14#035P3%12#0,?7R4P4n0110000020000b21@23#1#0%13#0557eX11X00P2P3O2W1W0o"). Qed.
Lemma c_active_decay_bounces sc st : c_active (s_ctx (decay_bounces sc st)) = c_active (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1CTg01T2j13Tg01TWj14Tg01knj22Tg01n^j27Tg00F6j2>Tg01n@j1=Tg00FSj2<Tg00Ebj45Tg00<Xj4;Tg00:<j48Tg01Mgj19Tg00g<j7:Tg01oVj2BTg01i=j2ATg012Hj11Tg01K:j10Tg006oj36Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Cf0R3g01XJR4#3#3#4R5,22'7g01e^'>#='<g00JBR6P6P0g00k>R7g00l5R8g006:C5R9P6P1P3g013>P0P0P0P7P8P0C5R6P0P0P6P0P7P8P0C;C8f4/25R5f3/75%44'2%93F:/B3W3f2R4'AP4n0100000020000#1#0%14#036P3%12#0,?9R4P4n0110000020000b21@23#1#0%13#0569eX11X00P2P3O2W1W0o"). Qed.
Lemma c_usage_decay_bounces sc st : c_usage (s_ctx (decay_bounces sc st)) = c_usage (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1CTg01T2j13Tg01TWj14Tg01knj22Tg01n^j26Tg00F6j2>Tg01n@j1=Tg00FSj2<Tg00Ebj4;Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2BTg01i=j2ATg012Hj11Tg01L3j10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Cf0R3g01XJR4#3#3#4R5,22'6g01e^'>#='<g00JBR6P6P0g00k>R7g00l5R8P0C;R9P6P1P3g013>P0P0P9P0P0P9P0P7P8P0C:C7f4/25R5f3/65%44'2%83F9/B3W3f2R4'AP4n0100000020000#1#0%14#035P3%12#0,?9R4P4n0110000020000b21@23#1#0%13#0559eX11X00P2P3O2W1W0o"). Qed.
Lemma c_unmap_seq_decay_bounces sc st : c_unmap_seq (s_ctx (decay_bounces sc st)) = c_unmap_seq (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1CTg01T2j13Tg01TWj14Tg01knj22Tg01n^j26Tg00F6j2>Tg01n@j1=Tg00FSj2<Tg00Ebj4;Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2BTg01i=j2ATg012Hj11Tg01Lkj10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Cf0R3g01XJR4#3#3#4R5,22'6g01e^'>#='<g00JBR6P6P0g00k>R7g00l5R8P0C;R9P6P1P3g013>P0P0P9P0P0P9P0P7P8P0C:C7f4/25R5f3/65%44'2%83F9/B3W3f2R4'AP4n0100000020000#1#0%14#035P3%12#0,?9R4P4n0110000020000b21@23#1#0%13#0559eX11X00P2P3O2W1W0o"). Qed.
Lemma c_seq_decay_bounces sc st : c_seq (s_ctx (decay_bounces sc st)) = c_seq (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1CTg01T2j13Tg01TWj14Tg01knj22Tg01n^j26Tg00F6j2>Tg01n@j1=Tg00FSj2<Tg00Ebj4;Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2BTg01i=j2ATg012Hj11Tg01Naj10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Cf0R3g01XJR4#3#3#4R5,22'6g01e^'>#='<g00JBR6P6P6P1P3g013>P0P0P0g00k>R6g00l5R7P0C;R8P0P0P8P0P6P7P0C:C7f4/25R5f3/65%44'2%83F9/B3W3f2R4'AP4n0100000020000#1#0%14#0550P3%12#0,?0R4P4n0110000020000b21@23#1#0%13#0550eX11X00P2P3O2W1W0o"). Qed.
Lemma c_brk_decay_bounces sc st : c_brk (s_ctx (decay_bounces sc st)) = c_brk (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02sch12sth21bi001bh31cp;1p;2p;4p;7p;3g01jnj1CTg01T2j13Tg01TWj14Tg01knj22Tg01n^j26Tg00F6j2>Tg01n@j1=Tg00FSj2<Tg00Ebj4;Tg00<Xj4:Tg00:<j47Tg01Mgj18Tg00g<j79Tg01oVj2BTg01i=j2ATg012Hj11Tg01OWj10Tg006oj35Tg00G1j2?Tg021Uj2@Tg00K`R0g00ilR1f1R2#Cf0R3g01XJR4#3#3#4R5,22'6g01e^'>#='<g00JBR6P6g01PMR7P6P1P3g013>P0P0P0g00k>R6g00l5R8P0C;R9P0P0P9P0P6P8P0C:C7f4/25R5f3/65%44'2%83F9/B3W3f2R4'AP4n0100000020000#1#0%14#035P3%12#0,?7R4P4n0110000020000b21@23#1#0%13#0557eX11X00P2P3O2W1W0o"). Qed.
Lemma c_secret_dequeue h m st : c_secret (s_ctx (dequeue h m st)) = c_secret (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j27Tg024Dj1:Tg00^@j2>Tg01n@j1HTg00`=j1GTg025;j2Ej15Tg0266j2Aj19Tg0271j1;Tg00nPj30Tg022Sj32Tg027hj3FTg012Hj1=Tg00_[j2CTg028`j2BTg01QHj1<Tg006oj3?Tg00G1j2@Tg006:R0f0R1'Cp=4f2R2f1R3'B/>1p=6%=1#<p=3g00K`R4f3R5?023#=#<;?1p=11@41p=8%<3=?41p=Dg023LR6g00ilR71713#:%43'>#Hg00JBR8P8P5g00h?%G0R91E91'AW8R:P8P7P1P8P7g00_9R;P0P71725R<#:R=f4R>,75R?#;R@#9P;P0P7P@f5R@,7>#:RA#5=01>RBP5n10110700021010600501P;P0P7%;<%:?R?#5=015P2n10110700021010600n10110700021010500R<%45RC76>A2>=<P<n0100000020000A2>92n0100000020000%32R<C1P11732#;g00BLRDP;P0P>P:P8P7P;P0P7P?%93P;P0P7P3f6RE,7@#:#5=01@P>n10110700021010600501P;P0P7P1PBP5n10110700021010600n10110700021010500RB%4>RF76@A2@?BPBn0100000020000%35RBC1P1PAPDP;P0f7RAP:P8P7P;P0P7P1%9CRC%53=05A501%51=02En10110700021010500R?f8RG%4A36A2G1?P?n0100000020000%3ER?C1P1%41#5=05A901Cf9RC%4G36P8P8f:RHP:P8P7P1f;%42RI%4@RJ#9%5I=0@C502RK32PKn0100000020000%3CRLC1P1P6PHP:A21IKPLC1PH%3H#8X14P1O1RM%3G#8RNn0110400021010100P6PHP:PKPLC1PHPMPNn0110400021010100n0110000020000b0X70P1O1%59RM=03@%4ERH76AP8P8PGP:P8P7P1A05MARM92C9PMn0100000020000%3ARLC1P1P6PGP:A219MPLC1PGPNX14P1O1RN%8?R?n0110400021010100P6PGP:PMPLC1PGPNP?n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P=PDP;P0P@P:P8P7P;P0P7P1%99R;=01@RDP>n10110700021010500R=?6EJA2E1=P=n0100000020000%3>R>C1P1A6DAHP8P8PGP:P8P7P1A02;AR;92CIP;n0100000020000PLC1P1P6PGP:A21I;PLC1PGPNP?n0110400021010100P6PGP:P;PLC1PGPNP?n0110400021010100n0110000020000b0X30P1O1A65@FP8P8PEP:P8P7P1A2A9@P@n0100000020000%3@RAC1P1P6PEP:A219@PAC1PEP?X14P1O1R?%8>R>n0110400021010100P6PEP:P@PAC1PEP?P>n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P5P:A2192P<C1P5%8BX14P1O1%33#8n0110400021010100n0110000020100b0AF231#=%31'DeX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma c_init_done_dequeue h m st : c_init_done (s_ctx (dequeue h m st)) = c_init_done (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j27Tg024Dj1:Tg00^@j2>Tg01n@j1HTg00`=j1GTg025;j2Ej15Tg0266j2Aj19Tg0271j1;Tg00nPj30Tg022Sj32Tg027hj3FTg012Hj1=Tg00_[j2CTg028`j2BTg01@nj1<Tg006oj3?Tg00G1j2@Tg006:R0f0R1'Cp=4f2R2f1R3'B/>1p=6%=1#<p=3g00K`R4f3R5?023#=#<;?1p=11@41p=8%<3=?41p=Dg023LR6g00ilR71713#:%43'>#Hg00JBR8P8P5g00h?%G0R91E91'AW8R:P8P7P1P8P7g00_9R;P0P71725R<#:R=f4R>,75R?#;R@#9P;P0P7P@f5R@,7>#:RA#5=01>RBP5n10110700021010600501P;P0P7%;<%:?R?#5=015P2n10110700021010600n10110700021010500R<%45RC76>A2>=<P<n0100000020000A2>92n0100000020000%32R<C1P11732#;g00BLRDP;P0P>P:P8P7P;P0P7P?%93P;P0P7P3f6RE,7@#:#5=01@P>n10110700021010600501P;P0P7P1PBP5n10110700021010600n10110700021010500RB%4>RF76@A2@?BPBn0100000020000%35RBC1P1PAPDP;P0f7RAP:P8P7P;P0P7P1%9CRC%53=05A501%51=02En10110700021010500R?f8RG%4A36A2G1?P?n0100000020000%3ER?C1P1%41#5=05A901Cf9RC%4G36P8P8f:RHP:P8P7P1f;%42RI%4@RJ#9%5I=0@C502RK32PKn0100000020000%3CRLC1P1P6PHP:A21IKPLC1PH%3H#8X14P1O1RM%3G#8RNn0110400021010100P6PHP:PKPLC1PHPMPNn0110400021010100n0110000020000b0X70P1O1%59RM=03@%4ERH76AP8P8PGP:P8P7P1A05MARM92C9PMn0100000020000%3ARLC1P1P6PGP:A219MPLC1PGPNX14P1O1RN%8?R?n0110400021010100P6PGP:PMPLC1PGPNP?n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P=PDP;P0P@P:P8P7P;P0P7P1%99R;=01@RDP>n10110700021010500R=?6EJA2E1=P=n0100000020000%3>R>C1P1A6DAHP8P8PGP:P8P7P1A02;AR;92CIP;n0100000020000PLC1P1P6PGP:A21I;PLC1PGPNP?n0110400021010100P6PGP:P;PLC1PGPNP?n0110400021010100n0110000020000b0X30P1O1A65@FP8P8PEP:P8P7P1A2A9@P@n0100000020000%3@RAC1P1P6PEP:A219@PAC1PEP?X14P1O1R?%8>R>n0110400021010100P6PEP:P@PAC1PEP?P>n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P5P:A2192P<C1P5%8BX14P1O1%33#8n0110400021010100n0110000020100b0AF231#=%31'DeX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma c_mmap_counter_dequeue h m st : c_mmap_counter (s_ctx (dequeue h m st)) = c_mmap_counter (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j27Tg024Dj1:Tg00^@j2>Tg01n@j1HTg00`=j1GTg025;j2Ej15Tg0266j2Aj19Tg0271j1;Tg00nPj30Tg022Sj32Tg027hj3FTg012Hj1=Tg00_[j2CTg028`j2BTg01Ajj1<Tg006oj3?Tg00G1j2@Tg006:R0f0R1'Cp=4f2R2f1R3'B/>1p=6%=1#<p=3g00K`R4f3R5?023#=#<;?1p=11@41p=8%<3=?41p=Dg023LR6g00ilR71713#:%43'>#Hg00JBR8P8P5g00h?%G0R91E91'AW8R:P8P7P1P8P7g00_9R;P0P71725R<#:R=f4R>,75R?#;R@#9P;P0P7P@f5R@,7>#:RA#5=01>RBP5n10110700021010600501P;P0P7%;<%:?R?#5=015P2n10110700021010600n10110700021010500R<%45RC76>A2>=<P<n0100000020000A2>92n0100000020000%32R<C1P11732#;g00BLRDP;P0P>P:P8P7P;P0P7P?%93P;P0P7P3f6RE,7@#:#5=01@P>n10110700021010600501P;P0P7P1PBP5n10110700021010600n10110700021010500RB%4>RF76@A2@?BPBn0100000020000%35RBC1P1PAPDP;P0f7RAP:P8P7P;P0P7P1%9CRC%53=05A501%51=02En10110700021010500R?f8RG%4A36A2G1?P?n0100000020000%3ER?C1P1%41#5=05A901Cf9RC%4G36P8P8f:RHP:P8P7P1f;%42RI%4@RJ#9%5I=0@C502RK32PKn0100000020000%3CRLC1P1P6PHP:A21IKPLC1PH%3H#8X14P1O1RM%3G#8RNn0110400021010100P6PHP:PKPLC1PHPMPNn0110400021010100n0110000020000b0X70P1O1%59RM=03@%4ERH76AP8P8PGP:P8P7P1A05MARM92C9PMn0100000020000%3ARLC1P1P6PGP:A219MPLC1PGPNX14P1O1RN%8?R?n0110400021010100P6PGP:PMPLC1PGPNP?n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P=PDP;P0P@P:P8P7P;P0P7P1%99R;=01@RDP>n10110700021010500R=?6EJA2E1=P=n0100000020000%3>R>C1P1A6DAHP8P8PGP:P8P7P1A02;AR;92CIP;n0100000020000PLC1P1P6PGP:A21I;PLC1PGPNP?n0110400021010100P6PGP:P;PLC1PGPNP?n0110400021010100n0110000020000b0X30P1O1A65@FP8P8PEP:P8P7P1A2A9@P@n0100000020000%3@RAC1P1P6PEP:A219@PAC1PEP?X14P1O1R?%8>R>n0110400021010100P6PEP:P@PAC1PEP?P>n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P5P:A2192P<C1P5%8BX14P1O1%33#8n0110400021010100n0110000020100b0AF231#=%31'DeX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma c_avail_meta_dequeue h m st : c_avail_meta (s_ctx (dequeue h m st)) = c_avail_meta (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j27Tg024Dj1:Tg00^@j2>Tg01n@j1HTg00`=j1GTg025;j2Ej15Tg0266j2Aj19Tg0271j1;Tg00nPj30Tg022Sj32Tg027hj3FTg012Hj1=Tg00_[j2CTg028`j2BTg01Cjj1<Tg006oj3?Tg00G1j2@Tg006:R0f0R1'Cp=4f2R2f1R3'B/>1p=6%=1#<p=3g00BLR4f3R5?023#=#<;?1p=11@41p=8%<3=?41p=Dg023LR6g00ilR71713#:%43'>#Hg00JBR8P8P5g00h?%G0R91E91'AW8R:P8P7P1P8P7g00_9R;P0P71725R<#:R=f4R>,75R?#;R@#9P;P0P7P@f5R@,7>#:RA#5=01>RBP5n10110700021010600501P;P0P7%;<%:?R?#5=015P2n10110700021010600n10110700021010500R<%45RC76>A2>=<P<n0100000020000A2>92n0100000020000%32R<C1P11732#;P4P;P0P>P:P8P7P;P0P7P?%93P;P0P7P3f6RD,7@#:#5=01@P>n10110700021010600501P;P0P7P1PBP5n10110700021010600n10110700021010500RB%4>RE76@A2@?BPBn0100000020000%35RBC1P1PAP4P;P0f7RAP:P8P7P;P0P7P1%9CRC%53=05A501%51=02Dn10110700021010500R?f8RF%4A36A2F1?P?n0100000020000%3DR?C1P1%41#5=05A901Cf9RC%4F36P8P8f:RGP:P8P7P1f;%42RH%4@RI#9%5H=0@C502RJ32PJn0100000020000%3CRKC1P1P6PGP:A21HJPKC1PGg00K`RL%3G#8W1P1O1RM%3F#8RNn0110400021010100P6PGP:PJPKC1PGPMPNn0110400021010100n0110000020000b0X70P1O1%59RM=03@%4DRG76AP8P8PFP:P8P7P1A05MARM92C9PMn0100000020000%3ARKC1P1P6PFP:A219MPKC1PFPNX1LP1O1RN%8?R?n0110400021010100P6PFP:PMPKC1PFPNP?n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P=P4P;P0P@P:P8P7P;P0P7P1%99R;=01@R4P>n10110700021010500R=?6DIA2D1=P=n0100000020000%3>R>C1P1A64AGP8P8PFP:P8P7P1A02;AR;92CHP;n0100000020000PKC1P1P6PFP:A21H;PKC1PFPNP?n0110400021010100P6PFP:P;PKC1PFPNP?n0110400021010100n0110000020000b0X30P1O1A65@EP8P8PDP:P8P7P1A2A9@P@n0100000020000%3@RAC1P1P6PDP:A219@PAC1PDP?X1LP1O1R?%8>R>n0110400021010100P6PDP:P@PAC1PDP?P>n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P5P:A2192P<C1P5%8BX1LP1O1%33#8n0110400021010100n0110000020100b0AF231#=%31'DeX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma c_avail_meta_count_dequeue h m st : c_avail_meta_count (s_ctx (dequeue h m st)) = c_avail_meta_count (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j27Tg024Dj1:Tg00^@j2>Tg01n@j1HTg00`=j1GTg025;j2Ej15Tg0266j2Aj19Tg0271j1;Tg00nPj30Tg022Sj32Tg027hj3FTg012Hj1=Tg00_[j2CTg028`j2BTg01Dgj1<Tg006oj3?Tg00G1j2@Tg006:R0f0R1'Cp=4f2R2f1R3'B/>1p=6%=1#<p=3g00K`R4f3R5?023#=#<;?1p=11@41p=8%<3=?41p=Dg023LR6g00ilR71713#:%43'>#Hg00JBR8P8P5g00h?%G0R91E91'AW8R:P8P7P1P8P7g00_9R;P0P71725R<#:R=f4R>,75R?#;R@#9P;P0P7P@f5R@,7>#:RA#5=01>RBP5n10110700021010600501P;P0P7%;<%:?R?#5=015P2n10110700021010600n10110700021010500R<%45RC76>A2>=<P<n0100000020000A2>92n0100000020000%32R<C1P11732#;g00BLRDP;P0P>P:P8P7P;P0P7P?%93P;P0P7P3f6RE,7@#:#5=01@P>n10110700021010600501P;P0P7P1PBP5n10110700021010600n10110700021010500RB%4>RF76@A2@?BPBn0100000020000%35RBC1P1PAPDP;P0f7RAP:P8P7P;P0P7P1%9CRC%53=05A501%51=02En10110700021010500R?f8RG%4A36A2G1?P?n0100000020000%3ER?C1P1%41#5=05A901Cf9RC%4G36P8P8f:RHP:P8P7P1f;%42RI%4@RJ#9%5I=0@C502RK32PKn0100000020000%3CRLC1P1P6PHP:A21IKPLC1PH%3H#8X14P1O1RM%3G#8RNn0110400021010100P6PHP:PKPLC1PHPMPNn0110400021010100n0110000020000b0X70P1O1%59RM=03@%4ERH76AP8P8PGP:P8P7P1A05MARM92C9PMn0100000020000%3ARLC1P1P6PGP:A219MPLC1PGPNX14P1O1RN%8?R?n0110400021010100P6PGP:PMPLC1PGPNP?n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P=PDP;P0P@P:P8P7P;P0P7P1%99R;=01@RDP>n10110700021010500R=?6EJA2E1=P=n0100000020000%3>R>C1P1A6DAHP8P8PGP:P8P7P1A02;AR;92CIP;n0100000020000PLC1P1P6PGP:A21I;PLC1PGPNP?n0110400021010100P6PGP:P;PLC1PGPNP?n0110400021010100n0110000020000b0X30P1O1A65@FP8P8PEP:P8P7P1A2A9@P@n0100000020000%3@RAC1P1P6PEP:A219@PAC1PEP?X14P1O1R?%8>R>n0110400021010100P6PEP:P@PAC1PEP?P>n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P5P:A2192P<C1P5%8BX14P1O1%33#8n0110400021010100n0110000020100b0AF231#=%31'DeX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma c_avail_meta_area_count_dequeue h m st : c_avail_meta_area_count (s_ctx (dequeue h m st)) = c_avail_meta_area_count (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j27Tg024Dj1:Tg00^@j2>Tg01n@j1HTg00`=j1GTg025;j2Ej15Tg0266j2Aj19Tg0271j1;Tg00nPj30Tg022Sj32Tg027hj3FTg012Hj1=Tg00_[j2CTg028`j2BTg01Ejj1<Tg006oj3?Tg00G1j2@Tg006:R0f0R1'Cp=4f2R2f1R3'B/>1p=6%=1#<p=3g00K`R4f3R5?023#=#<;?1p=11@41p=8%<3=?41p=Dg023LR6g00ilR71713#:%43'>#Hg00JBR8P8P5g00h?%G0R91E91'AW8R:P8P7P1P8P7g00_9R;P0P71725R<#:R=f4R>,75R?#;R@#9P;P0P7P@f5R@,7>#:RA#5=01>RBP5n10110700021010600501P;P0P7%;<%:?R?#5=015P2n10110700021010600n10110700021010500R<%45RC76>A2>=<P<n0100000020000A2>92n0100000020000%32R<C1P11732#;g00BLRDP;P0P>P:P8P7P;P0P7P?%93P;P0P7P3f6RE,7@#:#5=01@P>n10110700021010600501P;P0P7P1PBP5n10110700021010600n10110700021010500RB%4>RF76@A2@?BPBn0100000020000%35RBC1P1PAPDP;P0f7RAP:P8P7P;P0P7P1%9CRC%53=05A501%51=02En10110700021010500R?f8RG%4A36A2G1?P?n0100000020000%3ER?C1P1%41#5=05A901Cf9RC%4G36P8P8f:RHP:P8P7P1f;%42RI%4@RJ#9%5I=0@C502RK32PKn0100000020000%3CRLC1P1P6PHP:A21IKPLC1PH%3H#8X14P1O1RM%3G#8RNn0110400021010100P6PHP:PKPLC1PHPMPNn0110400021010100n0110000020000b0X70P1O1%59RM=03@%4ERH76AP8P8PGP:P8P7P1A05MARM92C9PMn0100000020000%3ARLC1P1P6PGP:A219MPLC1PGPNX14P1O1RN%8?R?n0110400021010100P6PGP:PMPLC1PGPNP?n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P=PDP;P0P@P:P8P7P;P0P7P1%99R;=01@RDP>n10110700021010500R=?6EJA2E1=P=n0100000020000%3>R>C1P1A6DAHP8P8PGP:P8P7P1A02;AR;92CIP;n0100000020000PLC1P1P6PGP:A21I;PLC1PGPNP?n0110400021010100P6PGP:P;PLC1PGPNP?n0110400021010100n0110000020000b0X30P1O1A65@FP8P8PEP:P8P7P1A2A9@P@n0100000020000%3@RAC1P1P6PEP:A219@PAC1PEP?X14P1O1R?%8>R>n0110400021010100P6PEP:P@PAC1PEP?P>n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P5P:A2192P<C1P5%8BX14P1O1%33#8n0110400021010100n0110000020100b0AF231#=%31'DeX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma c_meta_alloc_shift_dequeue h m st : c_meta_alloc_shift (s_ctx (dequeue h m st)) = c_meta_alloc_shift (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j27Tg024Dj1:Tg00^@j2>Tg01n@j1HTg00`=j1GTg025;j2Ej15Tg0266j2Aj19Tg0271j1;Tg00nPj30Tg022Sj32Tg027hj3FTg012Hj1=Tg00_[j2CTg028`j2BTg01G2j1<Tg006oj3?Tg00G1j2@Tg006:R0f0R1'Cp=4f2R2f1R3'B/>1p=6%=1#<p=3g00K`R4f3R5?023#=#<;?1p=11@41p=8%<3=?41p=Dg023LR6g00ilR71713#:%43'>#Hg00JBR8P8P5g00h?%G0R91E91'AW8R:P8P7P1P8P7g00_9R;P0P71725R<#:R=f4R>,75R?#;R@#9P;P0P7P@f5R@,7>#:RA#5=01>RBP5n10110700021010600501P;P0P7%;<%:?R?#5=015P2n10110700021010600n10110700021010500R<%45RC76>A2>=<P<n0100000020000A2>92n0100000020000%32R<C1P11732#;g00BLRDP;P0P>P:P8P7P;P0P7P?%93P;P0P7P3f6RE,7@#:#5=01@P>n10110700021010600501P;P0P7P1PBP5n10110700021010600n10110700021010500RB%4>RF76@A2@?BPBn0100000020000%35RBC1P1PAPDP;P0f7RAP:P8P7P;P0P7P1%9CRC%53=05A501%51=02En10110700021010500R?f8RG%4A36A2G1?P?n0100000020000%3ER?C1P1%41#5=05A901Cf9RC%4G36P8P8f:RHP:P8P7P1f;%42RI%4@RJ#9%5I=0@C502RK32PKn0100000020000%3CRLC1P1P6PHP:A21IKPLC1PH%3H#8X14P1O1RM%3G#8RNn0110400021010100P6PHP:PKPLC1PHPMPNn0110400021010100n0110000020000b0X70P1O1%59RM=03@%4ERH76AP8P8PGP:P8P7P1A05MARM92C9PMn0100000020000%3ARLC1P1P6PGP:A219MPLC1PGPNX14P1O1RN%8?R?n0110400021010100P6PGP:PMPLC1PGPNP?n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P=PDP;P0P@P:P8P7P;P0P7P1%99R;=01@RDP>n10110700021010500R=?6EJA2E1=P=n0100000020000%3>R>C1P1A6DAHP8P8PGP:P8P7P1A02;AR;92CIP;n0100000020000PLC1P1P6PGP:A21I;PLC1PGPNP?n0110400021010100P6PGP:P;PLC1PGPNP?n0110400021010100n0110000020000b0X30P1O1A65@FP8P8PEP:P8P7P1A2A9@P@n0100000020000%3@RAC1P1P6PEP:A219@PAC1PEP?X14P1O1R?%8>R>n0110400021010100P6PEP:P@PAC1PEP?P>n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P5P:A2192P<C1P5%8BX14P1O1%33#8n0110400021010100n0110000020100b0AF231#=%31'DeX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma c_meta_area_head_dequeue h m st : c_meta_area_head (s_ctx (dequeue h m st)) = c_meta_area_head (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j27Tg024Dj1:Tg00^@j2>Tg01n@j1HTg00`=j1GTg025;j2Ej15Tg0266j2Aj19Tg0271j1;Tg00nPj30Tg022Sj32Tg027hj3FTg012Hj1=Tg00_[j2CTg028`j2BTg01H5j1<Tg006oj3?Tg00G1j2@Tg006:R0f0R1'Cp=4f2R2f1R3'B/>1p=6%=1#<p=3g00BLR4f3R5?023#=#<;?1p=11@41p=8%<3=?41p=Dg023LR6g00ilR71713#:%43'>#Hg00JBR8P8P5g00h?%G0R91E91'AW8R:P8P7P1P8P7g00_9R;P0P71725R<#:R=f4R>,75R?#;R@#9P;P0P7P@f5R@,7>#:RA#5=01>RBP5n10110700021010600501P;P0P7%;<%:?R?#5=015P2n10110700021010600n10110700021010500R<%45RC76>A2>=<P<n0100000020000A2>92n0100000020000%32R<C1P11732#;P4P;P0P>P:P8P7P;P0P7P?%93P;P0P7P3f6RD,7@#:#5=01@P>n10110700021010600501P;P0P7P1PBP5n10110700021010600n10110700021010500RB%4>RE76@A2@?BPBn0100000020000%35RBC1P1PAP4P;P0f7RAP:P8P7P;P0P7P1%9CRC%53=05A501%51=02Dn10110700021010500R?f8RF%4A36A2F1?P?n0100000020000%3DR?C1P1%41#5=05A901Cf9RC%4F36P8P8f:RGP:P8P7P1f;%42RH%4@RI#9%5H=0@C502RJ32PJn0100000020000%3CRKC1P1P6PGP:A21HJPKC1PGg00K`RL%3G#8W1P1O1RM%3F#8RNn0110400021010100P6PGP:PJPKC1PGPMPNn0110400021010100n0110000020000b0X70P1O1%59RM=03@%4DRG76AP8P8PFP:P8P7P1A05MARM92C9PMn0100000020000%3ARKC1P1P6PFP:A219MPKC1PFPNX1LP1O1RN%8?R?n0110400021010100P6PFP:PMPKC1PFPNP?n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P=P4P;P0P@P:P8P7P;P0P7P1%99R;=01@R4P>n10110700021010500R=?6DIA2D1=P=n0100000020000%3>R>C1P1A64AGP8P8PFP:P8P7P1A02;AR;92CHP;n0100000020000PKC1P1P6PFP:A21H;PKC1PFPNP?n0110400021010100P6PFP:P;PKC1PFPNP?n0110400021010100n0110000020000b0X30P1O1A65@EP8P8PDP:P8P7P1A2A9@P@n0100000020000%3@RAC1P1P6PDP:A219@PAC1PDP?X1LP1O1R?%8>R>n0110400021010100P6PDP:P@PAC1PDP?P>n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P5P:A2192P<C1P5%8BX1LP1O1%33#8n0110400021010100n0110000020100b0AF231#=%31'DeX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma c_meta_area_tail_dequeue h m st : c_meta_area_tail (s_ctx (dequeue h m st)) = c_meta_area_tail (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j27Tg024Dj1:Tg00^@j2>Tg01n@j1HTg00`=j1GTg025;j2Ej15Tg0266j2Aj19Tg0271j1;Tg00nPj30Tg022Sj32Tg027hj3FTg012Hj1=Tg00_[j2CTg028`j2BTg01I6j1<Tg006oj3?Tg00G1j2@Tg006:R0f0R1'Cp=4f2R2f1R3'B/>1p=6%=1#<p=3g00BLR4f3R5?023#=#<;?1p=11@41p=8%<3=?41p=Dg023LR6g00ilR71713#:%43'>#Hg00JBR8P8P5g00h?%G0R91E91'AW8R:P8P7P1P8P7g00_9R;P0P71725R<#:R=f4R>,75R?#;R@#9P;P0P7P@f5R@,7>#:RA#5=01>RBP5n10110700021010600501P;P0P7%;<%:?R?#5=015P2n10110700021010600n10110700021010500R<%45RC76>A2>=<P<n0100000020000A2>92n0100000020000%32R<C1P11732#;P4P;P0P>P:P8P7P;P0P7P?%93P;P0P7P3f6RD,7@#:#5=01@P>n10110700021010600501P;P0P7P1PBP5n10110700021010600n10110700021010500RB%4>RE76@A2@?BPBn0100000020000%35RBC1P1PAP4P;P0f7RAP:P8P7P;P0P7P1%9CRC%53=05A501%51=02Dn10110700021010500R?f8RF%4A36A2F1?P?n0100000020000%3DR?C1P1%41#5=05A901Cf9RC%4F36P8P8f:RGP:P8P7P1f;%42RH%4@RI#9%5H=0@C502RJ32PJn0100000020000%3CRKC1P1P6PGP:A21HJPKC1PGg00K`RL%3G#8W1P1O1RM%3F#8RNn0110400021010100P6PGP:PJPKC1PGPMPNn0110400021010100n0110000020000b0X70P1O1%59RM=03@%4DRG76AP8P8PFP:P8P7P1A05MARM92C9PMn0100000020000%3ARKC1P1P6PFP:A219MPKC1PFPNX1LP1O1RN%8?R?n0110400021010100P6PFP:PMPKC1PFPNP?n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P=P4P;P0P@P:P8P7P;P0P7P1%99R;=01@R4P>n10110700021010500R=?6DIA2D1=P=n0100000020000%3>R>C1P1A64AGP8P8PFP:P8P7P1A02;AR;92CHP;n0100000020000PKC1P1P6PFP:A21H;PKC1PFPNP?n0110400021010100P6PFP:P;PKC1PFPNP?n0110400021010100n0110000020000b0X30P1O1A65@EP8P8PDP:P8P7P1A2A9@P@n0100000020000%3@RAC1P1P6PDP:A219@PAC1PDP?X1LP1O1R?%8>R>n0110400021010100P6PDP:P@PAC1PDP?P>n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P5P:A2192P<C1P5%8BX1LP1O1%33#8n0110400021010100n0110000020100b0AF231#=%31'DeX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma c_avail_meta_areas_dequeue h m st : c_avail_meta_areas (s_ctx (dequeue h m st)) = c_avail_meta_areas (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j27Tg024Dj1:Tg00^@j2>Tg01n@j1HTg00`=j1GTg025;j2Ej15Tg0266j2Aj19Tg0271j1;Tg00nPj30Tg022Sj32Tg027hj3FTg012Hj1=Tg00_[j2CTg028`j2BTg01J7j1<Tg006oj3?Tg00G1j2@Tg006:R0f0R1'Cp=4f2R2f1R3'B/>1p=6%=1#<p=3g00BLR4f3R5?023#=#<;?1p=11@41p=8%<3=?41p=Dg023LR6g00ilR71713#:%43'>#Hg00JBR8P8P5g00h?%G0R91E91'AW8R:P8P7P1P8P7g00_9R;P0P71725R<#:R=f4R>,75R?#;R@#9P;P0P7P@f5R@,7>#:RA#5=01>RBP5n10110700021010600501P;P0P7%;<%:?R?#5=015P2n10110700021010600n10110700021010500R<%45RC76>A2>=<P<n0100000020000A2>92n0100000020000%32R<C1P11732#;P4P;P0P>P:P8P7P;P0P7P?%93P;P0P7P3f6RD,7@#:#5=01@P>n10110700021010600501P;P0P7P1PBP5n10110700021010600n10110700021010500RB%4>RE76@A2@?BPBn0100000020000%35RBC1P1PAP4P;P0f7RAP:P8P7P;P0P7P1%9CRC%53=05A501%51=02Dn10110700021010500R?f8RF%4A36A2F1?P?n0100000020000%3DR?C1P1%41#5=05A901Cf9RC%4F36P8P8f:RGP:P8P7P1f;%42RH%4@RI#9%5H=0@C502RJ32PJn0100000020000%3CRKC1P1P6PGP:A21HJPKC1PGg00K`RL%3G#8W1P1O1RM%3F#8RNn0110400021010100P6PGP:PJPKC1PGPMPNn0110400021010100n0110000020000b0X70P1O1%59RM=03@%4DRG76AP8P8PFP:P8P7P1A05MARM92C9PMn0100000020000%3ARKC1P1P6PFP:A219MPKC1PFPNX1LP1O1RN%8?R?n0110400021010100P6PFP:PMPKC1PFPNP?n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P=P4P;P0P@P:P8P7P;P0P7P1%99R;=01@R4P>n10110700021010500R=?6DIA2D1=P=n0100000020000%3>R>C1P1A64AGP8P8PFP:P8P7P1A02;AR;92CHP;n0100000020000PKC1P1P6PFP:A21H;PKC1PFPNP?n0110400021010100P6PFP:P;PKC1PFPNP?n0110400021010100n0110000020000b0X30P1O1A65@EP8P8PDP:P8P7P1A2A9@P@n0100000020000%3@RAC1P1P6PDP:A219@PAC1PDP?X1LP1O1R?%8>R>n0110400021010100P6PDP:P@PAC1PDP?P>n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P5P:A2192P<C1P5%8BX1LP1O1%33#8n0110400021010100n0110000020100b0AF231#=%31'DeX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma c_usage_dequeue h m st : c_usage (s_ctx (dequeue h m st)) = c_usage (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;4p;3g00f?j28Tg024Dj1:Tg00^@j2>Tg01n@j1HTg00Ebj4GTg00`=j1ETg025;j2Bj15Tg0266j2@j19Tg0271j1;Tg00nPj31Tg022Sj32Tg00G1j27Tg027hj3FTg012Hj1<Tg00_[j2CTg028`j2ATg01L3j1=Tg006oj3?Tg006:R0f0R1'Cp=4f2R2f1R3'A/>1p=6%<1#=p=3f4R4f3R5?123#<#=;?1p=0%=3=?21p=Dg023LR6g00ilR71813#:%43'>#Hg00JBR8P8g00K`R9g00k>g00l5P9CGR:P5g00h?%E0R;1B;1'@W8R<P8P7P1P8P7g00_9R=P0P71825R>#:R?1854R@#;RA#9P=P0P7PAf5RA,84#:RB#5=114RCP5n10110700021010600511P=P0P7%;>%:@R@#5=115P2n10110700021010600n10110700021010500R>%45RD764A24?>P>n0100000020000A24;2n0100000020000%32R>D0P11832#;g00BLREP=P0P:P4P<P8P7P=P0P7P@%93P=P0P7P3f6RF,8A#:#5=11AP4n10110700021010600511P=P0P7P1PCP5n10110700021010600n10110700021010500RC%44RG76AA2A@CPCn0100000020000%35RCD0P1PBPEP=P0P:f7RBP<P8P7P=P0P7P1%9DRD%53=15B511%51=12Fn10110700021010500R@f8RH%4B36A2H1@P@n0100000020000%3FR@D0P1%41#5=15B911Df9RD%4H36P8P8P:f:RIP<P8P7P1f;%42RJ%4ARK#9%5J=1AD512RL32PLn0100000020000%3DRMD0P1P6P:PIP<A21JLPMD0PI%3I,7:X19P1O1RN%3H,7:ROn0110400021010100P6P:PIP<PLPMD0PIPNPOn0110400021010100n0110000020000b0X70P1O1%5;RN=13A%4FRI76BP8P8P:PHP<P8P7P1A15NBRN92D;PNn0100000020000%3BRMD0P1P6P:PHP<A21;NPMD0PHPOX19P1O1RO17:@R@n0110400021010100P6P:PHP<PNPMD0PHPOP@n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P?PEP=P0P:PAP<P8P7P=P0P7P1%9;R==11AREP4n10110700021010500R??6FKA2F1?P?n0100000020000%34R4D0P1A6EBIP8P8P:PHP<P8P7P1A12=BR=92DJP=n0100000020000PMD0P1P6P:PHP<A21J=PMD0PHPOP@n0110400021010100P6P:PHP<P=PMD0PHPOP@n0110400021010100n0110000020000b0X30P1O1A65AGP8P8P:PFP<P8P7P1A2B;APAn0100000020000%3ARBD0P1P6P:PFP<A21;APBD0PFP@X19P1O1R@17:4R4n0110400021010100P6P:PFP<PAPBD0PFP@P4n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P:P5P<A21;2P>D0P517:CX19P1O1%33,7:n0110400021010100n0110000020100b0AF231#<%315D:eX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma c_unmap_seq_dequeue h m st : c_unmap_seq (s_ctx (dequeue h m st)) = c_unmap_seq (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;4p;3g00f?j28Tg024Dj1:Tg00^@j2>Tg01n@j1HTg00Ebj4GTg00`=j1ETg025;j2Bj15Tg0266j2@j19Tg0271j1;Tg00nPj31Tg022Sj32Tg00G1j27Tg027hj3FTg012Hj1<Tg00_[j2CTg028`j2ATg01Lkj1=Tg006oj3?Tg006:R0f0R1'Cp=4f2R2f1R3'A/>1p=6%<1#=p=3f4R4f3R5?123#<#=;?1p=0%=3=?21p=Dg023LR6g00ilR71813#:%43'>#Hg00JBR8P8g00K`R9g00k>g00l5P9CGR:P5g00h?%E0R;1B;1'@W8R<P8P7P1P8P7g00_9R=P0P71825R>#:R?1854R@#;RA#9P=P0P7PAf5RA,84#:RB#5=114RCP5n10110700021010600511P=P0P7%;>%:@R@#5=115P2n10110700021010600n10110700021010500R>%45RD764A24?>P>n0100000020000A24;2n0100000020000%32R>D0P11832#;g00BLREP=P0P:P4P<P8P7P=P0P7P@%93P=P0P7P3f6RF,8A#:#5=11AP4n10110700021010600511P=P0P7P1PCP5n10110700021010600n10110700021010500RC%44RG76AA2A@CPCn0100000020000%35RCD0P1PBPEP=P0P:f7RBP<P8P7P=P0P7P1%9DRD%53=15B511%51=12Fn10110700021010500R@f8RH%4B36A2H1@P@n0100000020000%3FR@D0P1%41#5=15B911Df9RD%4H36P8P8P:f:RIP<P8P7P1f;%42RJ%4ARK#9%5J=1AD512RL32PLn0100000020000%3DRMD0P1P6P:PIP<A21JLPMD0PI%3I,7:X19P1O1RN%3H,7:ROn0110400021010100P6P:PIP<PLPMD0PIPNPOn0110400021010100n0110000020000b0X70P1O1%5;RN=13A%4FRI76BP8P8P:PHP<P8P7P1A15NBRN92D;PNn0100000020000%3BRMD0P1P6P:PHP<A21;NPMD0PHPOX19P1O1RO17:@R@n0110400021010100P6P:PHP<PNPMD0PHPOP@n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P?PEP=P0P:PAP<P8P7P=P0P7P1%9;R==11AREP4n10110700021010500R??6FKA2F1?P?n0100000020000%34R4D0P1A6EBIP8P8P:PHP<P8P7P1A12=BR=92DJP=n0100000020000PMD0P1P6P:PHP<A21J=PMD0PHPOP@n0110400021010100P6P:PHP<P=PMD0PHPOP@n0110400021010100n0110000020000b0X30P1O1A65AGP8P8P:PFP<P8P7P1A2B;APAn0100000020000%3ARBD0P1P6P:PFP<A21;APBD0PFP@X19P1O1R@17:4R4n0110400021010100P6P:PFP<PAPBD0PFP@P4n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P:P5P<A21;2P>D0P517:CX19P1O1%33,7:n0110400021010100n0110000020100b0AF231#<%315D:eX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma c_bounces_dequeue h m st : c_bounces (s_ctx (dequeue h m st)) = c_bounces (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;4p;3g00f?j28Tg024Dj1:Tg00^@j2>Tg01n@j1HTg00Ebj4GTg00`=j1ETg025;j2Bj15Tg0266j2@j19Tg0271j1;Tg00nPj31Tg022Sj32Tg00G1j27Tg027hj3FTg012Hj1<Tg00_[j2CTg028`j2ATg01Mgj1=Tg006oj3?Tg006:R0f0R1'Cp=4f2R2f1R3'A/>1p=6%<1#=p=3f4R4f3R5?123#<#=;?1p=0%=3=?21p=Dg023LR6g00ilR71813#:%43'>#Hg00JBR8P8g00K`R9g00k>g00l5P9CGR:P5g00h?%E0R;1B;1'@W8R<P8P7P1P8P7g00_9R=P0P71825R>#:R?1854R@#;RA#9P=P0P7PAf5RA,84#:RB#5=114RCP5n10110700021010600511P=P0P7%;>%:@R@#5=115P2n10110700021010600n10110700021010500R>%45RD764A24?>P>n0100000020000A24;2n0100000020000%32R>D0P11832#;g00BLREP=P0P:P4P<P8P7P=P0P7P@%93P=P0P7P3f6RF,8A#:#5=11AP4n10110700021010600511P=P0P7P1PCP5n10110700021010600n10110700021010500RC%44RG76AA2A@CPCn0100000020000%35RCD0P1PBPEP=P0P:f7RBP<P8P7P=P0P7P1%9DRD%53=15B511%51=12Fn10110700021010500R@f8RH%4B36A2H1@P@n0100000020000%3FR@D0P1%41#5=15B911Df9RD%4H36P8P8P:f:RIP<P8P7P1f;%42RJ%4ARK#9%5J=1AD512RL32PLn0100000020000%3DRMD0P1P6P:PIP<A21JLPMD0PI%3I,7:X19P1O1RN%3H,7:ROn0110400021010100P6P:PIP<PLPMD0PIPNPOn0110400021010100n0110000020000b0X70P1O1%5;RN=13A%4FRI76BP8P8P:PHP<P8P7P1A15NBRN92D;PNn0100000020000%3BRMD0P1P6P:PHP<A21;NPMD0PHPOX19P1O1RO17:@R@n0110400021010100P6P:PHP<PNPMD0PHPOP@n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P?PEP=P0P:PAP<P8P7P=P0P7P1%9;R==11AREP4n10110700021010500R??6FKA2F1?P?n0100000020000%34R4D0P1A6EBIP8P8P:PHP<P8P7P1A12=BR=92DJP=n0100000020000PMD0P1P6P:PHP<A21J=PMD0PHPOP@n0110400021010100P6P:PHP<P=PMD0PHPOP@n0110400021010100n0110000020000b0X30P1O1A65AGP8P8P:PFP<P8P7P1A2B;APAn0100000020000%3ARBD0P1P6P:PFP<A21;APBD0PFP@X19P1O1R@17:4R4n0110400021010100P6P:PFP<PAPBD0PFP@P4n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P:P5P<A21;2P>D0P517:CX19P1O1%33,7:n0110400021010100n0110000020100b0AF231#<%315D:eX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma c_seq_dequeue h m st : c_seq (s_ctx (dequeue h m st)) = c_seq (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j27Tg024Dj1:Tg00^@j2>Tg01n@j1HTg00`=j1GTg025;j2Ej15Tg0266j2Aj19Tg0271j1;Tg00nPj30Tg022Sj32Tg027hj3FTg012Hj1=Tg00_[j2CTg028`j2BTg01Naj1<Tg006oj3?Tg00G1j2@Tg006:R0f0R1'Cp=4f2R2f1R3'B/>1p=6%=1#<p=3g00K`R4f3R5?023#=#<;?1p=11@41p=8%<3=?41p=Dg023LR6g00ilR71713#:%43'>#Hg00JBR8P8P5g00h?%G0R91E91'AW8R:P8P7P1P8P7g00_9R;P0P71725R<#:R=f4R>,75R?#;R@#9P;P0P7P@f5R@,7>#:RA#5=01>RBP5n10110700021010600501P;P0P7%;<%:?R?#5=015P2n10110700021010600n10110700021010500R<%45RC76>A2>=<P<n0100000020000A2>92n0100000020000%32R<C1P11732#;g00BLRDP;P0P>P:P8P7P;P0P7P?%93P;P0P7P3f6RE,7@#:#5=01@P>n10110700021010600501P;P0P7P1PBP5n10110700021010600n10110700021010500RB%4>RF76@A2@?BPBn0100000020000%35RBC1P1PAPDP;P0f7RAP:P8P7P;P0P7P1%9CRC%53=05A501%51=02En10110700021010500R?f8RG%4A36A2G1?P?n0100000020000%3ER?C1P1%41#5=05A901Cf9RC%4G36P8P8f:RHP:P8P7P1f;%42RI%4@RJ#9%5I=0@C502RK32PKn0100000020000%3CRLC1P1P6PHP:A21IKPLC1PH%3H#8X14P1O1RM%3G#8RNn0110400021010100P6PHP:PKPLC1PHPMPNn0110400021010100n0110000020000b0X70P1O1%59RM=03@%4ERH76AP8P8PGP:P8P7P1A05MARM92C9PMn0100000020000%3ARLC1P1P6PGP:A219MPLC1PGPNX14P1O1RN%8?R?n0110400021010100P6PGP:PMPLC1PGPNP?n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P=PDP;P0P@P:P8P7P;P0P7P1%99R;=01@RDP>n10110700021010500R=?6EJA2E1=P=n0100000020000%3>R>C1P1A6DAHP8P8PGP:P8P7P1A02;AR;92CIP;n0100000020000PLC1P1P6PGP:A21I;PLC1PGPNP?n0110400021010100P6PGP:P;PLC1PGPNP?n0110400021010100n0110000020000b0X30P1O1A65@FP8P8PEP:P8P7P1A2A9@P@n0100000020000%3@RAC1P1P6PEP:A219@PAC1PEP?X14P1O1R?%8>R>n0110400021010100P6PEP:P@PAC1PEP?P>n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P6P5P:A2192P<C1P5%8BX14P1O1%33#8n0110400021010100n0110000020100b0AF231#=%31'DeX67X50X46P2P3P1O3W6X50W4o"). Qed.
Lemma c_brk_dequeue h m st : c_brk (s_ctx (dequeue h m st)) = c_brk (s_ctx st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh12sci012sch21oi021oh31ai031ah41hh51mh62sth72a0h81ri041li052nxi062pvi071xp;2p;1p;3g00f?j27Tg024Dj1:Tg00^@j2>Tg01n@j1HTg00`=j1GTg025;j2Ej15Tg0266j2Aj19Tg0271j1;Tg00nPj30Tg022Sj32Tg027hj3FTg012Hj1=Tg00_[j2CTg028`j2BTg01OWj1<Tg006oj3?Tg00G1j2@Tg006:R0f0R1'Cp=4f2R2f1R3'B/>1p=6%=1#<p=3g01PMR4f3R5?023#=#<;?1p=11@41p=8%<3=?41p=Dg023LR4g00ilR61713#:%43'>#Hg00JBR7P7P5g00h?%G0R81E81'AW8R9P7P6P1P7P6g00_9R:P0P61725R;#:R<f4R=,75R>#;R?#9P:P0P6P?f5R?,7=#:R@#5=01=RAP5n10110700021010600501P:P0P6%;;%:>R>#5=015P2n10110700021010600n10110700021010500R;%45RB76=A2=<;P;n0100000020000A2=82n0100000020000%32R;C1P11732#;g00BLRCP:P0P=P9P7P6P:P0P6P>%93P:P0P6P3f6RD,7?#:#5=01?P=n10110700021010600501P:P0P6P1PAP5n10110700021010600n10110700021010500RA%4=RE76?A2?>APAn0100000020000%35RAC1P1P@PCP:P0f7R@P9P7P6P:P0P6P1%9BRB%53=05@501%51=02Dn10110700021010500R>f8RF%4@36A2F1>P>n0100000020000%3DR>C1P1%41#5=05@901Bf9RB%4F36P7P7f:RGP9P7P6P1f;%42RH%4?RI#9%5H=0?B502RJ32PJn0100000020000%3BRKC1P1P4PGP9A21HJPKC1PGg00K`RL%3G#8W1P1O1RM%3F#8RNn0110400021010100P4PGP9PJPKC1PGPMPNn0110400021010100n0110000020000b0X70P1O1%58RM=03?%4DRG76@P7P7PFP9P7P6P1A05M@RM92B8PMn0100000020000%3@RKC1P1P4PFP9A218MPKC1PFPNX1LP1O1RN%8>R>n0110400021010100P4PFP9PMPKC1PFPNP>n0110400021010100n0110000020000b0n10110200021010300b2X30P1O1P<PCP:P0P?P9P7P6P:P0P6P1%98R:=01?RCP=n10110700021010500R<?6DIA2D1<P<n0100000020000%3=R=C1P1A6C@GP7P7PFP9P7P6P1A02:@R:92BHP:n0100000020000PKC1P1P4PFP9A21H:PKC1PFPNP>n0110400021010100P4PFP9P:PKC1PFPNP>n0110400021010100n0110000020000b0X30P1O1A65?EP7P7PDP9P7P6P1A2@8?P?n0100000020000%3?R@C1P1P4PDP9A218?P@C1PDP>X1LP1O1R>%8=R=n0110400021010100P4PDP9P?P@C1PDP>P=n0110400021010100n0110000020000b0n10110200021010300b2n10110200021110301b2P4P5P9A2182P;C1P5%8AX1LP1O1%33#8n0110400021010100n0110000020100b0AF231#=%31'DeX66X50X44P2P3P1O3W6X50W4o"). Qed.
#[export] Hint Rewrite s_regions_set_active s_shadow_set_active s_next_rid_set_active s_metas_set_active s_areas_set_active s_groups_set_active s_slots_set_active s_tick_set_active s_secret_set_active s_reserved_set_active s_atop_set_active s_regions_set_usage s_shadow_set_usage s_next_rid_set_usage s_metas_set_usage s_areas_set_usage s_groups_set_usage s_slots_set_usage s_tick_set_usage s_secret_set_usage s_reserved_set_usage s_atop_set_usage s_regions_set_bounce s_shadow_set_bounce s_next_rid_set_bounce s_metas_set_bounce s_areas_set_bounce s_groups_set_bounce s_slots_set_bounce s_tick_set_bounce s_secret_set_bounce s_reserved_set_bounce s_atop_set_bounce s_ctx_put_meta s_regions_put_meta s_shadow_put_meta s_next_rid_put_meta s_areas_put_meta s_groups_put_meta s_slots_put_meta s_tick_put_meta s_secret_put_meta s_reserved_put_meta s_atop_put_meta s_ctx_upd_meta s_regions_upd_meta s_shadow_upd_meta s_next_rid_upd_meta s_areas_upd_meta s_groups_upd_meta s_slots_upd_meta s_tick_upd_meta s_secret_upd_meta s_reserved_upd_meta s_atop_upd_meta s_ctx_put_group s_regions_put_group s_shadow_put_group s_next_rid_put_group s_metas_put_group s_areas_put_group s_slots_put_group s_tick_put_group s_secret_put_group s_reserved_put_group s_atop_put_group s_ctx_del_group s_regions_del_group s_shadow_del_group s_next_rid_del_group s_metas_del_group s_areas_del_group s_slots_del_group s_tick_del_group s_secret_del_group s_reserved_del_group s_atop_del_group s_ctx_set_group_active_idx s_regions_set_group_active_idx s_shadow_set_group_active_idx s_next_rid_set_group_active_idx s_metas_set_group_active_idx s_areas_set_group_active_idx s_slots_set_group_active_idx s_tick_set_group_active_idx s_secret_set_group_active_idx s_reserved_set_group_active_idx s_atop_set_group_active_idx s_ctx_drop_region s_next_rid_drop_region s_metas_drop_region s_areas_drop_region s_groups_drop_region s_slots_drop_region s_tick_drop_region s_secret_drop_region s_reserved_drop_region s_atop_drop_region s_ctx_upd_region s_shadow_upd_region s_next_rid_upd_region s_metas_upd_region s_areas_upd_region s_groups_upd_region s_slots_upd_region s_tick_upd_region s_secret_upd_region s_reserved_upd_region s_atop_upd_region s_ctx_add_slots s_regions_add_slots s_shadow_add_slots s_next_rid_add_slots s_metas_add_slots s_areas_add_slots s_groups_add_slots s_tick_add_slots s_secret_add_slots s_reserved_add_slots s_atop_add_slots s_ctx_del_slots s_regions_del_slots s_shadow_del_slots s_next_rid_del_slots s_metas_del_slots s_areas_del_slots s_groups_del_slots s_tick_del_slots s_secret_del_slots s_reserved_del_slots s_atop_del_slots s_ctx_upd_shadow s_regions_upd_shadow s_next_rid_upd_shadow s_metas_upd_shadow s_areas_upd_shadow s_groups_upd_shadow s_slots_upd_shadow s_tick_upd_shadow s_secret_upd_shadow s_reserved_upd_shadow s_atop_upd_shadow s_ctx_wr8 s_regions_wr8 s_next_rid_wr8 s_metas_wr8 s_areas_wr8 s_groups_wr8 s_slots_wr8 s_tick_wr8 s_secret_wr8 s_reserved_wr8 s_atop_wr8 s_ctx_wr16 s_regions_wr16 s_next_rid_wr16 s_metas_wr16 s_areas_wr16 s_groups_wr16 s_slots_wr16 s_tick_wr16 s_secret_wr16 s_reserved_wr16 s_atop_wr16 s_ctx_wr32 s_regions_wr32 s_next_rid_wr32 s_metas_wr32 s_areas_wr32 s_groups_wr32 s_slots_wr32 s_tick_wr32 s_secret_wr32 s_reserved_wr32 s_atop_wr32 s_ctx_havoc s_regions_havoc s_next_rid_havoc s_metas_havoc s_areas_havoc s_groups_havoc s_slots_havoc s_tick_havoc s_secret_havoc s_reserved_havoc s_atop_havoc s_ctx_hdr_havoc s_regions_hdr_havoc s_next_rid_hdr_havoc s_metas_hdr_havoc s_areas_hdr_havoc s_groups_hdr_havoc s_slots_hdr_havoc s_tick_hdr_havoc s_secret_hdr_havoc s_reserved_hdr_havoc s_atop_hdr_havoc s_regions_step_seq s_shadow_step_seq s_next_rid_step_seq s_metas_step_seq s_areas_step_seq s_groups_step_seq s_slots_step_seq s_tick_step_seq s_secret_step_seq s_reserved_step_seq s_atop_step_seq s_regions_record_seq s_shadow_record_seq s_next_rid_record_seq s_metas_record_seq s_areas_record_seq s_groups_record_seq s_slots_record_seq s_tick_record_seq s_secret_record_seq s_reserved_record_seq s_atop_record_seq s_regions_account_bounce s_shadow_account_bounce s_next_rid_account_bounce s_metas_account_bounce s_areas_account_bounce s_groups_account_bounce s_slots_account_bounce s_tick_account_bounce s_secret_account_bounce s_reserved_account_bounce s_atop_account_bounce s_regions_decay_bounces s_shadow_decay_bounces s_next_rid_decay_bounces s_metas_decay_bounces s_areas_decay_bounces s_groups_decay_bounces s_slots_decay_bounces s_tick_decay_bounces s_secret_decay_bounces s_reserved_decay_bounces s_atop_decay_bounces s_regions_set_head s_shadow_set_head s_next_rid_set_head s_metas_set_head s_areas_set_head s_groups_set_head s_slots_set_head s_tick_set_head s_secret_set_head s_reserved_set_head s_atop_set_head s_regions_dequeue s_shadow_dequeue s_next_rid_dequeue s_areas_dequeue s_groups_dequeue s_slots_dequeue s_tick_dequeue s_secret_dequeue s_reserved_dequeue s_atop_dequeue s_ctx_set_size s_regions_set_size s_next_rid_set_size s_metas_set_size s_areas_set_size s_groups_set_size s_slots_set_size s_tick_set_size s_secret_set_size s_reserved_set_size s_atop_set_size c_secret_set_active c_init_done_set_active c_mmap_counter_set_active c_free_meta_head_set_active c_avail_meta_set_active c_avail_meta_count_set_active c_avail_meta_area_count_set_active c_meta_alloc_shift_set_active c_meta_area_head_set_active c_meta_area_tail_set_active c_avail_meta_areas_set_active c_usage_set_active c_unmap_seq_set_active c_bounces_set_active c_seq_set_active c_brk_set_active c_secret_set_usage c_init_done_set_usage c_mmap_counter_set_usage c_free_meta_head_set_usage c_avail_meta_set_usage c_avail_meta_count_set_usage c_avail_meta_area_count_set_usage c_meta_alloc_shift_set_usage c_meta_area_head_set_usage c_meta_area_tail_set_usage c_avail_meta_areas_set_usage c_active_set_usage c_unmap_seq_set_usage c_bounces_set_usage c_seq_set_usage c_brk_set_usage c_secret_set_bounce c_init_done_set_bounce c_mmap_counter_set_bounce c_free_meta_head_set_bounce c_avail_meta_set_bounce c_avail_meta_count_set_bounce c_avail_meta_area_count_set_bounce c_meta_alloc_shift_set_bounce c_meta_area_head_set_bounce c_meta_area_tail_set_bounce c_avail_meta_areas_set_bounce c_active_set_bounce c_usage_set_bounce c_unmap_seq_set_bounce c_seq_set_bounce c_brk_set_bounce c_secret_step_seq c_init_done_step_seq c_mmap_counter_step_seq c_free_meta_head_step_seq c_avail_meta_step_seq c_avail_meta_count_step_seq c_avail_meta_area_count_step_seq c_meta_alloc_shift_step_seq c_meta_area_head_step_seq c_meta_area_tail_step_seq c_avail_meta_areas_step_seq c_active_step_seq c_usage_step_seq c_bounces_step_seq c_brk_step_seq c_secret_record_seq c_init_done_record_seq c_mmap_counter_record_seq c_free_meta_head_record_seq c_avail_meta_record_seq c_avail_meta_count_record_seq c_avail_meta_area_count_record_seq c_meta_alloc_shift_record_seq c_meta_area_head_record_seq c_meta_area_tail_record_seq c_avail_meta_areas_record_seq c_active_record_seq c_usage_record_seq c_bounces_record_seq c_seq_record_seq c_brk_record_seq c_secret_account_bounce c_init_done_account_bounce c_mmap_counter_account_bounce c_free_meta_head_account_bounce c_avail_meta_account_bounce c_avail_meta_count_account_bounce c_avail_meta_area_count_account_bounce c_meta_alloc_shift_account_bounce c_meta_area_head_account_bounce c_meta_area_tail_account_bounce c_avail_meta_areas_account_bounce c_active_account_bounce c_usage_account_bounce c_unmap_seq_account_bounce c_seq_account_bounce c_brk_account_bounce c_secret_decay_bounces c_init_done_decay_bounces c_mmap_counter_decay_bounces c_free_meta_head_decay_bounces c_avail_meta_decay_bounces c_avail_meta_count_decay_bounces c_avail_meta_area_count_decay_bounces c_meta_alloc_shift_decay_bounces c_meta_area_head_decay_bounces c_meta_area_tail_decay_bounces c_avail_meta_areas_decay_bounces c_active_decay_bounces c_usage_decay_bounces c_unmap_seq_decay_bounces c_seq_decay_bounces c_brk_decay_bounces c_secret_dequeue c_init_done_dequeue c_mmap_counter_dequeue c_avail_meta_dequeue c_avail_meta_count_dequeue c_avail_meta_area_count_dequeue c_meta_alloc_shift_dequeue c_meta_area_head_dequeue c_meta_area_tail_dequeue c_avail_meta_areas_dequeue c_usage_dequeue c_unmap_seq_dequeue c_bounces_dequeue c_seq_dequeue c_brk_dequeue : mst.

(* [comment removed for export] *)
Lemma strip_fields st :
  s_ctx (strip st) = s_ctx st /\ s_regions (strip st) = s_regions st /\ s_next_rid (strip st) = s_next_rid st
  /\ s_metas (strip st) = s_metas st /\ s_areas (strip st) = s_areas st /\ s_groups (strip st) = s_groups st
  /\ s_slots (strip st) = s_slots st /\ s_secret (strip st) = s_secret st /\ s_reserved (strip st) = s_reserved st
  /\ s_atop (strip st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02stp;1p;3p;4p;6p;2g02>Kj1DTg012Hj1?Tg006oj30Tg00Ebj43Tg0145j1:Tg017Zj17Tg00b9j4BTg00bWj6@Tg00c8j15Tg018Uj16Tg01:Dj14Tg00Ubj28Tg01<4j19Tg01=cj1>Tg01>\j1CTg01?<j1;Tg01@7j1<Tg00LWj22Tg00G1j2=Tg00S<j4ATf4f3f2f1'=f0R0CAp=1g00ilR1g013>R2%D0R3#?%?0R430g00KBR5g00jeR6g00kWR7g014oC3R8%:3%:0R930R:%73%70R;505R<g006:R=P5P6g00K`R>g00k>R?CBR@P5P6P7P>P?g00l5E@R?g00h?C3R7%53%50R630RAP=P@P?g019MC3RB%63%60RC30RDP=P@P?g01;=C3RE%43%40RF30RGP=P@P?18=>C3R=%93%90R?30R@%>3%>0RH50>RI18>>#CRJ%;3%;0RK30RL%<3%<0R350>RM'2RN'2RO'2RP'2RQ'2RR'2RS'2RT'2P2P4P:PTP8P9P<PSP5P;PAPRP7P6PDPQPBPCPGPPPEPFP@POP=P?PIPNP>PHPLPMPJPK1=>3D1D1D1D1D1D1D1D1D1X01P0O1W0o"). Qed.

(* [comment removed for export] *)
Ltac by_strip H :=
  first [ apply (f_equal s_ctx) in H | apply (f_equal s_regions) in H | apply (f_equal s_next_rid) in H
        | apply (f_equal s_metas) in H | apply (f_equal s_areas) in H | apply (f_equal s_groups) in H
        | apply (f_equal s_slots) in H | apply (f_equal s_secret) in H | apply (f_equal s_reserved) in H
        | apply (f_equal s_atop) in H ]; exact H.

Section LAYOUT_FIELDS.
  Ltac lay lem := intros; pose proof lem as H; cbn [strip] in H;
    match goal with |- ?F _ = _ => apply (f_equal F) in H; cbn in H; exact H end.
  Lemma s_ctx_zero_hdrs p size i cnt st : s_ctx (zero_hdrs p size i cnt st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21ih31ph44sizeh52stp;5p;1p;3p;6g02?Aj55Tg02@Ej53Tg02>Kj10Tg006oj31Tg008Cj64Tg012HR0j12Tg006:R1g00K`R2g02A?R3g00ilR4f4R5f3R6f2R7f1R8f0R9D5P5P6P7P8P9D3#0%09514P4g013>R:P0f5P5P6P7P8D3#0R0%08R;P9E4%20%2;51:P9b0b0X54X13X22X42X31P5P6P7P8P9O5W5W1X22W4W3o"). Qed.
  Lemma s_regions_zero_hdrs p size i cnt st : s_regions (zero_hdrs p size i cnt st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21ih31ph44sizeh52stp;5p;1p;3p;4p;6g02?Aj56Tg02@Ej53Tg02>Kj10Tg006oj31Tg00Ebj45Tg008Cj64Tg0145R0j12Tg006:R1g00K`R2g02A?R3g00ilR4f4R5f3R6f2R7f1R8f0R9D6P5P6P7P8P9D3#0%09514P4g00KBg00jeg00kWg014oC5R:P0f5P5P6P7P8D3#0R0%08R;P9E4%20%2;51:P9b0b0X54X13X22X42X31P5P6P7P8P9O5W5W1X22W4W3o"). Qed.
  Lemma s_next_rid_zero_hdrs p size i cnt st : s_next_rid (zero_hdrs p size i cnt st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21ih31ph44sizeh52stp;5p;1p;3p;6g02?Aj55Tg02@Ej53Tg02>Kj10Tg006oj31Tg008Cj64Tg017ZR0j12Tg006:R1g00K`R2g02A?R3g00ilR4f4R5f3R6f2R7f1R8f0R9D5P5P6P7P8P9D3#0%09514P4g00KBR:P0f5P5P6P7P8D3#0R0%08R;P9E4%20%2;51:P9b0b0X54X13X22X42X31P5P6P7P8P9O5W5W1X22W4W3o"). Qed.
  Lemma s_metas_zero_hdrs p size i cnt st : s_metas (zero_hdrs p size i cnt st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21ih31ph44sizeh52stp;5p;1p;3p;4p;6g02?Aj58Tg02@Ej53Tg02>Kj10Tg006oj31Tg00b9j47Tg00bWj66Tg00Ebj45Tg008Cj64Tg00c8R0j12Tg006:R1g00K`R2g02A?R3g00ilR4f4R5f3R6f2R7f1R8f0R9D8P5P6P7P8P9D3#0%09514P4P1g00KBR:g00jeR;P2g00k>R<C7P:P;g00kWP2P<g00l5E6g00h?C5R<P0f5P5P6P7P8D3#0R0%08R;P9E4%20%2;51<P9b0b0X54X13X22X42X31P5P6P7P8P9O5W5W1X22W4W3o"). Qed.
  Lemma s_areas_zero_hdrs p size i cnt st : s_areas (zero_hdrs p size i cnt st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21ih31ph44sizeh52stp;5p;1p;3p;4p;6g02?Aj58Tg02@Ej53Tg02>Kj10Tg006oj31Tg00b9j47Tg00bWj66Tg00Ebj45Tg008Cj64Tg018UR0j12Tg006:R1g00K`R2g02A?R3g00ilR4f4R5f3R6f2R7f1R8f0R9D8P5P6P7P8P9D3#0%09514P4P1g00KBR:g00jeR;P2g00k>R<C7P:P;g00kWP2P<g00l5E6g019MC5R<P0f5P5P6P7P8D3#0R0%08R;P9E4%20%2;51<P9b0b0X54X13X22X42X31P5P6P7P8P9O5W5W1X22W4W3o"). Qed.
  Lemma s_groups_zero_hdrs p size i cnt st : s_groups (zero_hdrs p size i cnt st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21ih31ph44sizeh52stp;5p;1p;3p;4p;6g02?Aj58Tg02@Ej53Tg02>Kj10Tg006oj31Tg00b9j47Tg00bWj66Tg00Ebj45Tg008Cj64Tg01:DR0j12Tg006:R1g00K`R2g02A?R3g00ilR4f4R5f3R6f2R7f1R8f0R9D8P5P6P7P8P9D3#0%09514P4P1g00KBR:g00jeR;P2g00k>R<C7P:P;g00kWP2P<g00l5E6g01;=C5R<P0f5P5P6P7P8D3#0R0%08R;P9E4%20%2;51<P9b0b0X54X13X22X42X31P5P6P7P8P9O5W5W1X22W4W3o"). Qed.
  Lemma s_slots_zero_hdrs p size i cnt st : s_slots (zero_hdrs p size i cnt st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21ih31ph44sizeh52stp;5p;1p;3p;4p;6p;2g02?Aj59Tg02@Ej53Tg02>Kj10Tg006oj31Tg00b9j48Tg00bWj67Tg00Ubj26Tg00Ebj44Tg008Cj65Tg01<4R0j12Tg006:R1g00K`R2g02A?R3g00ilR4f4R5f3R6f2R7f1R8f0R9D9P5P6P7P8P9D3#0%09514P4P1g00KBR:g00jeR;P2g00k>R<C8P:P;g00kWP2P<g00l5E71612C4R<P0f5P5P6P7P8D3#0R0%08R;P9E5%20%2;51<P9b0b0X54X13X22X42X31P5P6P7P8P9O5W5W1X22W4W3o"). Qed.
  Lemma s_secret_zero_hdrs p size i cnt st : s_secret (zero_hdrs p size i cnt st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21ih31ph44sizeh52stp;5p;1p;3p;6g02?Aj55Tg02@Ej53Tg02>Kj10Tg006oj31Tg008Cj64Tg01=cR0j12Tg006:R1g00K`R2g02A?R3g00ilR4f4R5f3R6f2R7f1R8f0R9D5P5P6P7P8P9D3#0%09514P4P2P0f5P5P6P7P8D3#0R0%08R:P9E4%20%2:512P9b0b0X54X13X22X42X31P5P6P7P8P9O5W5W1X22W4W3o"). Qed.
  Lemma s_reserved_zero_hdrs p size i cnt st : s_reserved (zero_hdrs p size i cnt st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21ih31ph44sizeh52stp;5p;1p;3p;2p;6g02?Aj57Tg02@Ej53Tg02>Kj10Tg006oj31Tg00Ubj26Tg01>\j15Tg008Cj64Tg01?<R0j12Tg006:R1g00K`R2g02A?R3g00ilR4f4R5f3R6f2R7f1R8f0R9D7P5P6P7P8P9D3#0%09514P41622#5R:P0f5P5P6P7P8D3#0R0%08R;P9E4%20%2;51:P9b0b0X54X13X22X42X31P5P6P7P8P9O5W5W1X22W4W3o"). Qed.
  Lemma s_atop_zero_hdrs p size i cnt st : s_atop (zero_hdrs p size i cnt st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21ih31ph44sizeh52stp;5p;1p;3p;6g02?Aj55Tg02@Ej53Tg02>Kj10Tg006oj31Tg008Cj64Tg01@7R0j12Tg006:R1g00K`R2g02A?R3g00ilR4f4R5f3R6f2R7f1R8f0R9D5P5P6P7P8P9D3#0%09514P4P2P0f5P5P6P7P8D3#0R0%08R:P9E4%20%2:512P9b0b0X54X13X22X42X31P5P6P7P8P9O5W5W1X22W4W3o"). Qed.
  Lemma s_tick_zero_hdrs p size i cnt st : s_tick (zero_hdrs p size i cnt st) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01ih12sth23cnth31ph44sizeh55IHcnth61np;5p;1p;3p;2p;6g02@Ej52Tg01<lj10Tg006oj31Tg00G1j26Tg01]Uj2=Tg01\>j25Tg01e9j14Tg01TWj13Tg01knj2;Tg02:7j2:Tg02;Ij37Tg005\j68Tg02A^j19Tg02B=j6<Tg006:R0g00K`R1g02A?R2g00ilR3g00KBR4f7R5f6R6f1R7f2R8f0R9D2#0%09R:31^13^01R;X22164:R<P6f5P7g02B^P9D2#0=14:eX13X01P4f8R6g02C=1=75'5g01XJR=#4#4#3';':g01e^;79R>#0%079149X64P<P6P5%3=,57R=f3R<P>D2#0P8P=P>O2E8P6P5P7%9<P9D2#0=14:eX13X01X5;X22P7P8P9E<X13X22X01X41X30f4P<P8P7P9O5W1W2X01W4W3o"). Qed.

  Lemma s_ctx_enframe_at st g idx n off : s_ctx (fst (enframe_at st g idx n off)) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh11gh23idxh31nh43offh52stp;5p;3p;1p;6g02D2j56Tg02E7j52Tg00Gmj31Tg02>Kj10Tg006oj34Tg008Cj65Tg012HR0j13Tg00ilR1g006:R2g00K`R3f4R4f3R5f2R6f1R7f0R8D6P4P5P6P7P8D29112#0%04541P1g013>R9P0f5R0P4P5P6P7D29112#0R:%00R0P8E5%3:%30549P8b0b0X43X33X23X12X51P4P5P6P7P8O5X43X33W2W1W5o"). Qed.
  Lemma s_regions_enframe_at st g idx n off : s_regions (fst (enframe_at st g idx n off)) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh11gh23idxh31nh43offh52stp;5p;3p;1p;4p;6g02D2j57Tg02E7j52Tg00Gmj31Tg02>Kj10Tg006oj34Tg00Ebj46Tg008Cj65Tg0145R0j13Tg00ilR1g006:R2g00K`R3f4R4f3R5f2R6f1R7f0R8D7P4P5P6P7P8D29112#0%04541P1g00KBg00jeg00kWg014oC6R9P0f5R0P4P5P6P7D29112#0R:%00R0P8E5%3:%30549P8b0b0X43X33X23X12X51P4P5P6P7P8O5X43X33W2W1W5o"). Qed.
  Lemma s_next_rid_enframe_at st g idx n off : s_next_rid (fst (enframe_at st g idx n off)) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh11gh23idxh31nh43offh52stp;5p;3p;1p;6g02D2j56Tg02E7j52Tg00Gmj31Tg02>Kj10Tg006oj34Tg008Cj65Tg017ZR0j13Tg00ilR1g006:R2g00K`R3f4R4f3R5f2R6f1R7f0R8D6P4P5P6P7P8D29112#0%04541P1g00KBR9P0f5R0P4P5P6P7D29112#0R:%00R0P8E5%3:%30549P8b0b0X43X33X23X12X51P4P5P6P7P8O5X43X33W2W1W5o"). Qed.
  Lemma s_metas_enframe_at st g idx n off : s_metas (fst (enframe_at st g idx n off)) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh11gh23idxh31nh43offh52stp;5p;3p;1p;4p;6g02D2j59Tg02E7j52Tg00Gmj33Tg02>Kj10Tg006oj34Tg00b9j48Tg00bWj67Tg00Ebj45Tg008Cj66Tg00c8R0j11Tg00ilR1g006:R2g00K`R3f4R4f3R5f2R6f1R7f0R8D9P4P5P6P7P8D29312#0%04541P1P2g00KBR9g00jeR:P3g00k>R;C8P9P:g00kWP3P;g00l5E7g00h?C5R;P0f5R0P4P5P6P7D29312#0R:%00R0P8E6%1:%1054;P8b0b0X43X33X23X12X51P4P5P6P7P8O5X43X33W2W1W5o"). Qed.
  Lemma s_areas_enframe_at st g idx n off : s_areas (fst (enframe_at st g idx n off)) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh11gh23idxh31nh43offh52stp;5p;3p;1p;4p;6g02D2j59Tg02E7j52Tg00Gmj33Tg02>Kj10Tg006oj34Tg00b9j48Tg00bWj67Tg00Ebj45Tg008Cj66Tg018UR0j11Tg00ilR1g006:R2g00K`R3f4R4f3R5f2R6f1R7f0R8D9P4P5P6P7P8D29312#0%04541P1P2g00KBR9g00jeR:P3g00k>R;C8P9P:g00kWP3P;g00l5E7g019MC5R;P0f5R0P4P5P6P7D29312#0R:%00R0P8E6%1:%1054;P8b0b0X43X33X23X12X51P4P5P6P7P8O5X43X33W2W1W5o"). Qed.
  Lemma s_groups_enframe_at st g idx n off : s_groups (fst (enframe_at st g idx n off)) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh11gh23idxh31nh43offh52stp;5p;3p;1p;4p;6g02D2j59Tg02E7j52Tg00Gmj33Tg02>Kj10Tg006oj34Tg00b9j48Tg00bWj67Tg00Ebj45Tg008Cj66Tg01:DR0j11Tg00ilR1g006:R2g00K`R3f4R4f3R5f2R6f1R7f0R8D9P4P5P6P7P8D29312#0%04541P1P2g00KBR9g00jeR:P3g00k>R;C8P9P:g00kWP3P;g00l5E7g01;=C5R;P0f5R0P4P5P6P7D29312#0R:%00R0P8E6%1:%1054;P8b0b0X43X33X23X12X51P4P5P6P7P8O5X43X33W2W1W5o"). Qed.
  Lemma s_slots_enframe_at st g idx n off : s_slots (fst (enframe_at st g idx n off)) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh11gh23idxh31nh43offh52stp;5p;3p;1p;4p;6p;2g02D2j5:Tg02E7j52Tg00Gmj33Tg02>Kj10Tg006oj34Tg00b9j49Tg00bWj68Tg00Ubj25Tg00Ebj46Tg008Cj67Tg01<4R0j11Tg00ilR1g006:R2g00K`R3f4R4f3R5f2R6f1R7f0R8D:P4P5P6P7P8D29312#0%04541P1P2g00KBR9g00jeR:P3g00k>R;C9P9P:g00kWP3P;g00l5E81523C6R;P0f5R0P4P5P6P7D29312#0R:%00R0P8E7%1:%1054;P8b0b0X43X33X23X12X51P4P5P6P7P8O5X43X33W2W1W5o"). Qed.
  Lemma s_secret_enframe_at st g idx n off : s_secret (fst (enframe_at st g idx n off)) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh11gh23idxh31nh43offh52stp;5p;3p;1p;6g02D2j56Tg02E7j52Tg00Gmj31Tg02>Kj10Tg006oj34Tg008Cj65Tg01=cR0j13Tg00ilR1g006:R2g00K`R3f4R4f3R5f2R6f1R7f0R8D6P4P5P6P7P8D29112#0%04541P1P3P0f5R0P4P5P6P7D29112#0R9%00R0P8E5%39%30543P8b0b0X43X33X23X12X51P4P5P6P7P8O5X43X33W2W1W5o"). Qed.
  Lemma s_reserved_enframe_at st g idx n off : s_reserved (fst (enframe_at st g idx n off)) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh11gh23idxh31nh43offh52stp;5p;3p;1p;2p;6g02D2j58Tg02E7j52Tg00Gmj33Tg02>Kj10Tg006oj34Tg00Ubj27Tg01>\j16Tg008Cj65Tg01?<R0j11Tg00ilR1g006:R2g00K`R3f4R4f3R5f2R6f1R7f0R8D8P4P5P6P7P8D29312#0%04541P11733#6R9P0f5R0P4P5P6P7D29312#0R:%00R0P8E5%1:%10549P8b0b0X43X33X23X12X51P4P5P6P7P8O5X43X33W2W1W5o"). Qed.
  Lemma s_atop_enframe_at st g idx n off : s_atop (fst (enframe_at st g idx n off)) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh11gh23idxh31nh43offh52stp;5p;3p;1p;6g02D2j56Tg02E7j52Tg00Gmj31Tg02>Kj10Tg006oj34Tg008Cj65Tg01@7R0j13Tg00ilR1g006:R2g00K`R3f4R4f3R5f2R6f1R7f0R8D6P4P5P6P7P8D29112#0%04541P1P3P0f5R0P4P5P6P7D29112#0R9%00R0P8E5%39%30543P8b0b0X43X33X23X12X51P4P5P6P7P8O5X43X33W2W1W5o"). Qed.
  Lemma s_tick_enframe_at st g idx n off : s_tick (fst (enframe_at st g idx n off)) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "p'0h01bi001bh11gh23idxh31nh43offh52sti011pi028reservedi033st1i043st2i051xp;2p;1p;4p;5p;3g00F6j2<Tg01n@j1CTg00UbR0j2MTg00a]j1WTg00SWj4OTg00f?j2BTg02F2j1@Tg00gdj5>Tg02Fhj1=Tg01]Uj24Tg01\>j21Tg02:7j20Tg01e9j1:Tg029Yj1LTg01T2j1DTg01TWj1NTg01knj29Tg02=Rj5?Tg01<lj1;Tg01[aj2RTg02:lj1GTg02<=j3JTg01U5j2QTg02=2j2ETg02;Ij35Tg00G1j2VTg02E7j5UTg02Gcj3PTg004Gj3STg01\[j2TTg00Gmj3YTg006oj3XTf4R1f3R2f2R3f1R4f0R53P35p=K1034g01e^R6;55p=8g00ilR7g006:R8P4P5COp=Ag00KBR9g00K`R:;S5p=2f5R;1934g02C=R<'T=P25751p=6AY785p=I%;4=X95p=31934/95p=7A5465p=HP7P:P4P5COp=F1<56#Cg00JBR=P=P0P7P81M78R>P=P>P51M9:R>P>%W>R?P9P:g02HXP6COR@f6RA/B;RB#@D>%=BRB/41,1<'0RC14<3'0RDg01XJRE#:RF#:#LRG%DERE#LRH,0C%DERE#:#:#:#:#:#NRI%LFRJ,0CP3PADK38/AD1AACn0100000020000P5P>P>P?P@f8RKf7RL'BRM#@D>RN%=MRM/4A,1<RO'0RPg02I6RQ,9M'0RMP;PA105HPA105J%25%2NRN/1<RRP4E6D?/A5n2001105000120103101#I%;A'3P5%DFRF#NRSP>P>P?P@1B;1RT#@D>RU%=TRT/42,1<RV'0RW19TQ'0RT#2RX14<4RY,0WRZ#2R[;73'RP=P=P0P7P:P7P=1M7:R\P5P>P>P?P@1BLAR]#@D>R^%=]R]/4;,1<R_'0R`19]Q'0R]%LFRF'0Ra10]GRb%2]Rc14<2Rd,0`Re#2;71RfP=P71<f6#C%Gf10eHP;10eJ%2^R^/1_R_/1d11^<R^10`HRdPI10`JRgP2PLDK98eGE6Re58]Pen0100000020101Re3J'H/FS1Fefn0100000020101P>P>P?P@f9/BKR@#@D>%=@/4L,1<'0R@14<;'0/0H%DE#D#NRE,QL1E5S'1R?;54n2001105000120104102%;LR>'3P519BQ,0C#2RQ%2D;72/<6#CRDP=P=14<1RB,0PRe/0HRf1QAERE1ESS'1Rh10MFRF10MGRi%2MRj%2e;7;RkP=P7P5%GkPfPA10eJ11NORN/1BPR10PHRBPI10PJROP1PKDK98eGE6Re58MPen0100000020101Re3J'H35%;KRl'3P51V9>R9P9n0110001020000b0PDP=P=1EkS,1E=5fe/3lP5P9P9n0110001020000b0n0110001020101b0PZPTP3P210ZHReP210ZJRf%2URU/1VRV/1Y11U<RU10WHR<PI10WJRJP4P;DK98ZGRGE6D?%;;RI'3ePZPTP3P2PeP2PfP[PUPGE6D?/AZ#I/3Ie%2WRZ=7X3,RSP=P=P0P7P:P7P=P\P5%2`=7c1RcP=P71<c6#C%GcPdP;PgP_P^PLE6RL58]PLn0100000020100RL5Jb,Ha/FS1FLcn010000002010110@H?5?4n2001105000120104102/3>P5%2C=7Q2/<6#CR6P=P=%2P=7j;RjP=P7P5%GjPBPAPOPNPRPKE6RK58MPKn0100000020100RK5Ji,HF95Bh/3lP5P9P9n0110001020000b0P6P=P=1EjS,1E=5BK/3lP5P9P9n0110001020000b0n0110001020101b0PWPTP3P2P<P2PJPVPUP;E6D?/3IePWPTP3P2P<P2PJPZPUP;E6D?/AW#I/3Ien0110001020101b0P1P2P3P4P5DU#I%;1'3eX4:X3:X2:X18X57P1P2P3P4P5O5X4:X3:X2:X18X57o"). Qed.

  Lemma s_ctx_nest_layout st g idx j size cnt : s_ctx (nest_layout st g idx j size cnt) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21gh33idxh41jh54sizeh62stp;6p;1p;3g02Iij65Tg02Joj63Tg02>Kj10Tg006oj31Tg008Cj64Tg012HR0j12Tg00ilR1g006:R2g00K`R3f5R4f4R5f3R6f2R7f1R8f0R9E5P4P5P6P7P8P9E3#0%04511P1g013>R:P0f6R0P4P5P6P7P8E3#0R;%00R0P9E4%2;%2051:P9b0b0X13X53X43X33X22X61P4P5P6P7P8P9O6X13X53X43W3W2W6o"). Qed.
  Lemma s_regions_nest_layout st g idx j size cnt : s_regions (nest_layout st g idx j size cnt) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21gh33idxh41jh54sizeh62stp;6p;1p;3p;4g02Iij66Tg02Joj63Tg02>Kj10Tg006oj31Tg00Ebj45Tg008Cj64Tg0145R0j12Tg00ilR1g006:R2g00K`R3f5R4f4R5f3R6f2R7f1R8f0R9E6P4P5P6P7P8P9E3#0%04511P1g00KBg00jeg00kWg014oC5R:P0f6R0P4P5P6P7P8E3#0R;%00R0P9E4%2;%2051:P9b0b0X13X53X43X33X22X61P4P5P6P7P8P9O6X13X53X43W3W2W6o"). Qed.
  Lemma s_next_rid_nest_layout st g idx j size cnt : s_next_rid (nest_layout st g idx j size cnt) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21gh33idxh41jh54sizeh62stp;6p;1p;3g02Iij65Tg02Joj63Tg02>Kj10Tg006oj31Tg008Cj64Tg017ZR0j12Tg00ilR1g006:R2g00K`R3f5R4f4R5f3R6f2R7f1R8f0R9E5P4P5P6P7P8P9E3#0%04511P1g00KBR:P0f6R0P4P5P6P7P8E3#0R;%00R0P9E4%2;%2051:P9b0b0X13X53X43X33X22X61P4P5P6P7P8P9O6X13X53X43W3W2W6o"). Qed.
  Lemma s_metas_nest_layout st g idx j size cnt : s_metas (nest_layout st g idx j size cnt) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21gh33idxh41jh54sizeh62stp;6p;1p;3p;4g02Iij68Tg02Joj63Tg02>Kj10Tg006oj31Tg00b9j47Tg00bWj66Tg00Ebj45Tg008Cj64Tg00c8R0j12Tg00ilR1g006:R2g00K`R3f5R4f4R5f3R6f2R7f1R8f0R9E8P4P5P6P7P8P9E3#0%04511P1P2g00KBR:g00jeR;P3g00k>R<C7P:P;g00kWP3P<g00l5E6g00h?C5R<P0f6R0P4P5P6P7P8E3#0R;%00R0P9E4%2;%2051<P9b0b0X13X53X43X33X22X61P4P5P6P7P8P9O6X13X53X43W3W2W6o"). Qed.
  Lemma s_areas_nest_layout st g idx j size cnt : s_areas (nest_layout st g idx j size cnt) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21gh33idxh41jh54sizeh62stp;6p;1p;3p;4g02Iij68Tg02Joj63Tg02>Kj10Tg006oj31Tg00b9j47Tg00bWj66Tg00Ebj45Tg008Cj64Tg018UR0j12Tg00ilR1g006:R2g00K`R3f5R4f4R5f3R6f2R7f1R8f0R9E8P4P5P6P7P8P9E3#0%04511P1P2g00KBR:g00jeR;P3g00k>R<C7P:P;g00kWP3P<g00l5E6g019MC5R<P0f6R0P4P5P6P7P8E3#0R;%00R0P9E4%2;%2051<P9b0b0X13X53X43X33X22X61P4P5P6P7P8P9O6X13X53X43W3W2W6o"). Qed.
  Lemma s_groups_nest_layout st g idx j size cnt : s_groups (nest_layout st g idx j size cnt) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21gh33idxh41jh54sizeh62stp;6p;1p;3p;4g02Iij68Tg02Joj63Tg02>Kj10Tg006oj31Tg00b9j47Tg00bWj66Tg00Ebj45Tg008Cj64Tg01:DR0j12Tg00ilR1g006:R2g00K`R3f5R4f4R5f3R6f2R7f1R8f0R9E8P4P5P6P7P8P9E3#0%04511P1P2g00KBR:g00jeR;P3g00k>R<C7P:P;g00kWP3P<g00l5E6g01;=C5R<P0f6R0P4P5P6P7P8E3#0R;%00R0P9E4%2;%2051<P9b0b0X13X53X43X33X22X61P4P5P6P7P8P9O6X13X53X43W3W2W6o"). Qed.
  Lemma s_slots_nest_layout st g idx j size cnt : s_slots (nest_layout st g idx j size cnt) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21gh33idxh41jh54sizeh62stp;6p;1p;3p;4p;2g02Iij69Tg02Joj63Tg02>Kj10Tg006oj31Tg00b9j48Tg00bWj67Tg00Ubj26Tg00Ebj44Tg008Cj65Tg01<4R0j12Tg00ilR1g006:R2g00K`R3f5R4f4R5f3R6f2R7f1R8f0R9E9P4P5P6P7P8P9E3#0%04511P1P2g00KBR:g00jeR;P3g00k>R<C8P:P;g00kWP3P<g00l5E71623C4R<P0f6R0P4P5P6P7P8E3#0R;%00R0P9E5%2;%2051<P9b0b0X13X53X43X33X22X61P4P5P6P7P8P9O6X13X53X43W3W2W6o"). Qed.
  Lemma s_secret_nest_layout st g idx j size cnt : s_secret (nest_layout st g idx j size cnt) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21gh33idxh41jh54sizeh62stp;6p;1p;3g02Iij65Tg02Joj63Tg02>Kj10Tg006oj31Tg008Cj64Tg01=cR0j12Tg00ilR1g006:R2g00K`R3f5R4f4R5f3R6f2R7f1R8f0R9E5P4P5P6P7P8P9E3#0%04511P1P3P0f6R0P4P5P6P7P8E3#0R:%00R0P9E4%2:%20513P9b0b0X13X53X43X33X22X61P4P5P6P7P8P9O6X13X53X43W3W2W6o"). Qed.
  Lemma s_reserved_nest_layout st g idx j size cnt : s_reserved (nest_layout st g idx j size cnt) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21gh33idxh41jh54sizeh62stp;6p;1p;3p;2g02Iij67Tg02Joj63Tg02>Kj10Tg006oj31Tg00Ubj26Tg01>\j15Tg008Cj64Tg01?<R0j12Tg00ilR1g006:R2g00K`R3f5R4f4R5f3R6f2R7f1R8f0R9E7P4P5P6P7P8P9E3#0%04511P11633#5R:P0f6R0P4P5P6P7P8E3#0R;%00R0P9E4%2;%2051:P9b0b0X13X53X43X33X22X61P4P5P6P7P8P9O6X13X53X43W3W2W6o"). Qed.
  Lemma s_atop_nest_layout st g idx j size cnt : s_atop (nest_layout st g idx j size cnt) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "h01Hh13cnth21gh33idxh41jh54sizeh62stp;6p;1p;3g02Iij65Tg02Joj63Tg02>Kj10Tg006oj31Tg008Cj64Tg01@7R0j12Tg00ilR1g006:R2g00K`R3f5R4f4R5f3R6f2R7f1R8f0R9E5P4P5P6P7P8P9E3#0%04511P1P3P0f6R0P4P5P6P7P8E3#0R:%00R0P9E4%2:%20513P9b0b0X13X53X43X33X22X61P4P5P6P7P8P9O6X13X53X43W3W2W6o"). Qed.
  Lemma s_tick_nest_layout st g idx j size cnt : s_tick (nest_layout st g idx j size cnt) = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) ["LAYOUT_FIELDS"] "p'0h01Eh11pi001ph21Hh33cnth41gh53idxh61jh74sizeh82sth91nh:3st1i013st1i021ai031mi041xp;1p;2p;3p;5p;4p;6g02Kkj14Tg00UbR0j2NTg00G1j2MTg006oj38Tg01TWj19Tg01\>j2@Tg02Lfj1;Tg01T2j17Tg029Yj1CTg02:7j2<Tg01U5j2BTg01e9j15Tg02MFj2ATg02;Ij3?Tg02@Ej5>Tg01<lj10Tg00SWj4=Tg02Mcj5LTg007Ij6GTg02Nej5FTg005\j6ETg02Joj6HTg01]Uj2ITg01knj2DTg02E7j5JTg00Gmj3KTg02C=f0R1'Ip=6g02I6,D1p=2f3R2f2R3f1R4P1g01e^R5DJp=3g00KBR6?841p=1g00ilR7g006:R8;K1p=:g00K`R9f5R:f4R;P2%43#6#2C31N78R<1M<1f6R=P:P;%42#6#2C3=8<1P0P7P8f8R>f7R?P=%4:#6#2C3=8<1P0P7P8P7P4P1P?P5g01XJR0#9R@,@=#;%70R0#CR=,<1f9RA%70#7#7#9RB'B%50#5#5#5#5#5#9R0'A;?4D>n2001104000120101100#0%0A'1]0P4f;RCf:RDPA%4>#6#2C3P7P8P4P1C=58<P61<4=1BDB/A0;?3R0#0RBf=R=#0RE,11X96f<R6PCPD%4A#6#2RAP5DLP6PCPDPAC3#:#0%06RA'1P<P=P6PC%4D#6#2C3%:1#0f>#0'1X1<P1P7P8P2P3C=R<P4EG%:<#0/1EP1b2b211BAeP4P>P51@?@#;R@P0D>#0P4P>P5P@P0DFEEW0X18X:7P4P1O2n2001100000121103102P1O1b0b1P:P;P2P3P4P1EH#0%0:'1eX39X79X69X59X48X87P:P;P2P3P4P1O6X39X79X69W5X48X87o"). Qed.
End LAYOUT_FIELDS.
#[export] Hint Rewrite s_ctx_zero_hdrs s_regions_zero_hdrs s_next_rid_zero_hdrs s_metas_zero_hdrs s_areas_zero_hdrs s_groups_zero_hdrs s_slots_zero_hdrs s_secret_zero_hdrs s_reserved_zero_hdrs s_atop_zero_hdrs s_tick_zero_hdrs
  s_ctx_enframe_at s_regions_enframe_at s_next_rid_enframe_at s_metas_enframe_at s_areas_enframe_at s_groups_enframe_at s_slots_enframe_at s_secret_enframe_at s_reserved_enframe_at s_atop_enframe_at s_tick_enframe_at
  s_ctx_nest_layout s_regions_nest_layout s_next_rid_nest_layout s_metas_nest_layout s_areas_nest_layout s_groups_nest_layout s_slots_nest_layout s_secret_nest_layout s_reserved_nest_layout s_atop_nest_layout s_tick_nest_layout : mst.

(* [comment removed for export] *)
Lemma s_regions_new_region k b l st : s_regions (fst (new_region k b l st)) = <[s_next_rid st := mkRegion k b l]> (s_regions st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01bh11kh21lh32stp;4p;1p;3p;7p;2g00Ebj47Tg00<Xj46Tg00:<j40Tg017Zj11Tg02Ofj35Tg0145j12Tg00g<j73Tg00G1j24Tg02P_R0g00K`R1g00ilR2g00KBR3g00jeR4g00kWR5g014oR6C7R7P3P6P7P3P6P7P3P4P5P6C6C0f0R6#1f3R5f2R4f1R335%26F3'4X32X21X01X10P5P4P3P6O4W3X21W0W1o"). Qed.
Lemma s_next_rid_new_region k b l st : s_next_rid (fst (new_region k b l st)) = N.succ (s_next_rid st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01bh11kh21lh32stp;1p;2g017Zj12Tg02QWj11Tg00G1j20Tg02P_R0g00K`R1g00ilR2g00KBf0R3#2#1'0X32X21X01X10f3f2f1P3O4W3X21W0W1o"). Qed.
Lemma snd_new_region k b l st : snd (new_region k b l st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01bh11kh21lh32stp;1p;2g017Zj11Tg00G1j20Tg02P_R0g00K`R1g00ilR2g00KBf0R3#1'0X32X21X01X10f3f2f1P3O4W3X21W0W1o"). Qed.
Lemma s_regions_drop_region rid st : s_regions (drop_region rid st) = delete rid (s_regions st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03ridh12stp;4p;1p;5p;2g00Ebj45Tg00<Xj44Tg00;Kj40Tg0145j11Tg02R5j53Tg00G1j22Tg00KBR0g00ilR1P0g00jeR2g00kWR3g014oR4C5R5P0P5P0P4P5P0P2P3P4C4C0f1R4f0R3#1D3'2X11X00P4P3O2W1W0o"). Qed.
Lemma s_shadow_drop_region rid st : s_shadow (drop_region rid st) = delete rid (s_shadow st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03ridh12stp;4p;1p;5p;2g00Ebj45Tg00<Xj44Tg00;Kj40Tg015hj11Tg02R5j53Tg00G1j22Tg00KBR0g00ilR1P0g00jeR2g00kWR3g016aR4C5R5P0P5P0P4P5P0P2P3P4C4C0f1R4f0R3#1D3'2X11X00P4P3O2W1W0o"). Qed.
Lemma s_groups_put_group g mo ai st : s_groups (put_group g mo ai st) = <[g := mkGhdr mo (Z.land ai 31)]> (s_groups st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02aih11gh22moh32stp;4p;6p;1p;2p;7g00b9j4;Tg00bWj6:Tg00Ebj42Tg00<Xj41Tg00:<j49Tg01T2j10Tg01TWj13Tg01U5j24Tg01USj25Tg01:Dj16Tg00g<j77Tg00G1j28Tg006:R0g00BLR1g00K`R2g00ilR3P0g00KBR4g00jeR5P2g00k>R6C;R7P4P5g00kWP2P6g00l5E:R6g01;=R5C2R4P0P5P4P0P5P4P0P7P6P5C1C9f3R5f2R6f1R7g01XJ#0#0#0#0#3'4'5f0R4#6F7'8X33X02X21X10P5P6P7P4O4W3W0W2W1o"). Qed.
Lemma s_groups_del_group g st : s_groups (del_group g st) = delete g (s_groups st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01gh12stp;4p;6p;1p;5p;2g00b9j47Tg00bWj66Tg00Ebj40Tg00<Xj41Tg00;Kj45Tg01:Dj12Tg02R5j53Tg00G1j24Tg006:R0g00ilR1P0g00KBR2g00jeR3g00K`R4g00k>R5C7R6P2P3g00kWP4P5g00l5E6R5g01;=R4C0R3P0P3P0P4P3P0P6P5P4C1C5f1R4f0R5#2D3'4X11X00P4P5O2W1W0o"). Qed.
Lemma s_shadow_upd_shadow rid f st : s_shadow (upd_shadow rid f st) = <[rid := f (get_shadow st rid)]> (s_shadow st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh13ridh22stp;4p;2p;1p;7g00Ebj46Tg00<Xj45Tg00:<j40Tg02RIj21Tg015hj14Tg00g<j72Tg00G1j23Tg00KBR0g016aR1P1[R2g00ilR3P0g00jeR4g00kWR5P1C6R6P0P1P6P0P1P6P0P4P5P1C5C0f2R1f1R5f0R4/11O1%44F2'3X23X02X10P1P5P4O3W2W0W1o"). Qed.
#[export] Hint Rewrite s_regions_new_region s_next_rid_new_region snd_new_region s_regions_drop_region s_shadow_drop_region
  s_groups_put_group s_groups_del_group s_shadow_upd_shadow : mst.

(* [comment removed for export] *)
Lemma active_set_active st sc v sc' : active (set_active sc v st) sc' = if sc' =? sc then v else active st sc'.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01oi001oh13sc'h21Hh33Heqh41ai011ah52sch62sth71vi021vh82NEh91bi031bh:1ch;1ei041eh<1ri051ri061ni071pp;2p;4p;1p;5p;3p;?p;6p;>p;Ap;@p;7g02SDj2ZTg00F6j2<Tg00W2R0j2BTg00Ebj4Yj3TTg00;gj4Uj3MTg00<Xj4Rj3ITg00:<j4JTg012Hj14Tg01K:j12Tg00;Kj4ATg02R5j59Tg00_9R1j1VTg00_[j2>Tg00G1j26Tg00=8j3QTg00<@j3LTg00=Oj3HTg00=fj3ETg00>>j3DTg00?1j3FTg00AHl?GTg005\j65Tg00`=j1CTg00@Dl>KTg00ZQj17Tg00d0j4;Tg00Z2j2=Tg00AjlANTg00@fl@OTg02Sfj2PTg01i=j2@Tg02Tej3STg02U`j2:Tg006oj3?Tg00g<j7XTg00gPj6WTg00K`R2f1R3f0R43?p=3P2g006:R5f4R6f3R7f2R8P3P4FXp=8P2P5P7P8P3P4EWp=0g00BLR9??34p=1g00ilR:1Z4813481<48R;'B1<37g00JBR<P01386P2g00k>R0g00l5R=P5CYR>P2P0P=P5CUR?P6P1P5P>f5R@P>P2P5P>P2P0P=P5CRRACJRBf7RCP4f8RD#4#2RED8P2P>P2P5P>PACARAf6RF%4C#2RGD9RHn10110200021010700C0P<P9P3P@P>P?P6PGC0RIn0100000020000'1P3137@RJP2PFP>P?P4P1P5P>PFP>PBPDP4f9RK#4#2RLD8RMP2P>PAPCPED9RNn10110200021010700C0/1FX12P1P5P>P?PCP1P5P>P4PMPNn10110200021010700RNC0/14P@%V5RO1>54RP1>53,14X0O169PP>P?PDPMC0P2AT20=RPAQ20=RQAM20=RRAL20=RSAI20=RTAH20=RUAE20=RVAD20=RWP0AF20=R=P5PLPDP4M?GE5X45P4O1PO%C5RX114XX0O169XP>P?PFPHC0P2PPPQPRPSPTPUPVPWP0P=P5PGPFM>KE5n10110000021010100P6P4E5W;P4O1%7JP1P5P>P?P@PNC0P>P?P@PEC0RE'1P@POP>P?PFPLC0RNP>P?PCf:#4#2C0,14X0O169NP>P?PFPMC0P2PPPQPRPSPTPUPVPWP0P=P5PLPDPFP413DFRDP2PKPCP4C;13CKg00[mRKP6P4O1'=b3W2%7DeMANE5X45P4O1POPI114EX0O169IP>P?P6PHC0P2PPPQPRPSPTPUPVPWP0P=P5PGPFP613F6RFP2PCP@P4C;13@CP8P4O1,=Kb3W2%7FeM@OE5n10110000021010100W8P4O1n10210310500021110411106b9b<P>P?P4g013>P1P5P>P8P>PBP6P4%23D8P2P>PAP7%24D9n10110200021010700/P4W:/@7#4#2C0P<P9P;P3P>P?P4%47#2C0n0100000020000'1eAS837/:4P<P9P;P31:74n0100000020000'1eX12X79X52X6:P7P8P3P4O4X12X79X52W6o"). Qed.
Lemma usage_set_usage st sc v sc' : usage (set_usage sc v st) sc' = if sc' =? sc then v else usage st sc'.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h03sc'h11oh22sch32sth41vh51Hh63Heqh72NEh81bi001bh91ch:1ei011eh;1ri021ri031np;2p;1p;4p;3p;?p;6p;Ap;7p;5g02SDj2WTg00F6j27Tg00W2R0j2>Tg00a]j1VTg00Ebj4Pj3OTg00;gj4Jj3ITg00<Xj4Bj3GTg00:<j4@Tg012Hj14Tg01L3j13Tg00_9j1UTg00_[j2TTg00G1j29Tg00=8j3NTg00<@j3HTg00=Oj3ATg00=fj3CTg00>>j3DTg00?1j3ETg00AHl?FTg005\j66Tg00ZQj18Tg00d0j4?Tg00Z2j2KTg00AjlA=Tg02VWj2LTg01i=j2MTg02WUj3<Tg02XOj2:Tg006oj3QTg00g<j7;Tg00gPj6RTg00gdj5STg00K`R1f1R2f0R33Qp=0P1P1f4R4f3R5f2R6P2P3F;p=5P1P1P5P6P2P3ERp=1P1P1P2g01e^P3DSp=2g00ilR71W3610361736R8'>1725g00JBR9P01064%V1R0P1g00k>R:g00l5R;P1CPR<P1P:P;P1CJR=P4P<P1P1P<P1P:P;P1CBC@R>f6R?f5R@f7RA#4#3RBD5RCC1RD'2P9P1P2P@P<P=P4PBC1RE,20RFn0100000020000'0P2105@RGP1P?P<P=P3P<P>PAP?f8#4#3RHD5C1,20/0?X01%U1RI1T1@1203RJ/0?X1I191@P<P=P?PCC1P1AO1:;RCAN1:;RKAI1:;RLAH1:;RMAG1:;RNAA1:;ROAC1:;RPAD1:;RQP:AE1:;R;P1PBP?P@M?FE6P4P3E6W:P3O1%8GPIPEP<P=P@PHC1,20,0JX1I191FPDP1PCPKPLPMPNPOPPPQP:P;P1PBP?P4P@10?4R?P1PAP@P3C?10@Ag00[mP6P3O1'Kb6W5%8?eMA=E6W7P3O1n10210010200021010110103b8b;P<P=P3g013>P<P>P5P6%33D5/L3W9/M5#4#3C1,20P9P1P8P2P<P=P3%45#3C1,20n0100000020000'0eA<625/:3P9P1P8P21:53n0100000020000'0eX01X41X21X37P5P6P2P3O4X01X41X21W3o"). Qed.
Lemma bounces_set_bounce st i v i' : bounces (set_bounce i v st) i' = if i' =? i then v else bounces st i'.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02i'h11ih21oh32sth41vh51Hh63Heqh72NEh81bi001bh91ch:1ei011eh;1ri021ri031np;2p;1p;4p;3p;?p;6p;Ap;7p;5g02SDj2WTg00F6j27Tg00W2R0j2>Tg00a]j1VTg00Ebj4Pj3OTg00;gj4Jj3ITg00<Xj4Bj3GTg00:<j4@Tg012Hj14Tg01Mgj13Tg00_9j1UTg00_[j2TTg00G1j29Tg00=8j3NTg00<@j3HTg00=Oj3ATg00=fj3CTg00>>j3DTg00?1j3ETg00AHl?FTg005\j66Tg00ZQj18Tg00d0j4?Tg00Z2j2KTg00AjlA=Tg01oVj2LTg01i=j2MTg02YEj3<Tg01n^j2:Tg006oj3QTg00g<j7;Tg00gPj6RTg00gdj5STg00K`R1f1R2f0R33Qp=0P1P1f4R4f3R5f2R6P2P3F;p=5P1P1P5P6P2P3ERp=1P1P1P2g01e^P3DSp=2g00ilR71W3610361736R8'>1725g00JBR9P01064%V1R0P1g00k>R:g00l5R;P1CPR<P1P:P;P1CJR=P4P<P1P1P<P1P:P;P1CBC@R>f6R?f5R@f7RA#4#3RBD5RCC1RD'2P9P1P2P@P<P=P4PBC1RE,20RFn0100000020000'0P2105@RGP1P?P<P=P3P<P>PAP?f8#4#3RHD5C1,20/0?X01%U1RI1T1@1203RJ/0?X2I191@P<P=P?PCC1P1AO1:;RCAN1:;RKAI1:;RLAH1:;RMAG1:;RNAA1:;ROAC1:;RPAD1:;RQP:AE1:;R;P1PBP?P@M?FE6P4P3E6W:P3O1%8GPIPEP<P=P@PHC1,20,0JX2I191FPDP1PCPKPLPMPNPOPPPQP:P;P1PBP?P4P@10?4R?P1PAP@P3C?10@Ag00[mP6P3O1'Kb6W5%8?eMA=E6W7P3O1n10210010200021010110103b8b;P<P=P3g013>P<P>P5P6%33D5/L3W9/M5#4#3C1,20P9P1P8P2P<P=P3%45#3C1,20n0100000020000'0eA<625/:3P9P1P8P21:53n0100000020000'0eX01X41X11X37P5P6P2P3O4X01X41X11W3o"). Qed.
Lemma get_head_set_head st h v : get_head (set_head h v st) h = v.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01hh12sth21vh31bh41oh52sci002sci011lp;3p;2p;1p;6p;4g022Sj31Tg028`j22Tg006oj30Tg00F6j26Tg02U`j23Tg00G1j25Tg00GKj1:Tg005\j64Tg02Tej39Tg02Z@j48Tg02[Bj17Tg00ilR0g023LR1g00BLR2P1f0R3f1R4f3R531/23=024P4g00K`P2g00JBR6P21633R7f2R8f4R9/33n0100000020000A0235X42P6g00JbP6P2P3P5f5/34n0100000020000=025X361528P7%:3E4A9389/33P9P3P8P3C8E4%73R7?189/27=028eW5P3O11523g02\:R7?138/27=023en0110100021010000X22X01X10P8P4P3O3W2W0W1o"). Qed.
Lemma get_head_set_head_other st h h' v : h' <> h -> get_head (set_head h v st) h' = get_head st h'.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02NEh13Heqh21hh32h'h42sci002sch53sc'h62sth71vh81bi011bh91ei021eh:1fh;1ni031nh<1oh=1ri041ri051lp;1p;3p;2p;6p;4g00ZQj11Tg022Sj34Tg028`j20Tg02[BR0j15Tg00F6j2;Tg02U`j26Tg02SDj2@Tg006oj33Tg00W2R1j2?Tg00G1j28Tg008Cj6:Tg007ej6DTg00Z2j2>Tg02Tej3CTg02Z@j4BTg005\j6ATg01f<j1<Tg01Bij1=Tg023LR2f1R3f0R433p=7g00BLR5?334p=2g02\:R69324p=9g00ilR7f2R8,73#1P2f3R9/74#1f6R:9439f4R;'010:;'2]0P9g00K`R<%54R=,7;#1P2%58R>,74#1%59R?f9R@74:/0310@3'2]0f5R@17=?#1P5g00JBR?P51;3;RAf7RBf:RC/63n0100000020000f;RD/68,24X<51@3;A3<3;/?A1;8@P?P1A3<9:P?P5P3PDf>/6@RDn0100000020000/2DP3A3<;BR?P2%5@R1P1f8RA#5REP2^4<RFP2P4P:O1X:FP0P018F0E:P<P2P0P@PAP4E:ED171Ef<f?/6:'2P@P4O1'>b1W9P4O1%1?185DW;P4O1n10210110400021010210103b8b=AC;BC/63PCP;PBP3CBEA%5;?4BC%53RD'010CD'2eW0X5<P4O1A326D#1%<A#=,85A4>@A/0610A6'2eW0n0110500021010000P4O1W0W4P4O1%98#1P2%94#1A46;B/0310B3'2]0P9%9=#116A3,85A46@A/0D10AD'2eW0X5<P4O1A3266R<#11826P<%<B#=,2;P3P4O1'>b1A469:/0610:6'2eW0n0110500021010000P4O1W0n0110500021010000P4O1W0X75X32X22X67P9P8P3P4O4X75X32X22W6o"). Qed.
Lemma active_upd_meta st m f sc : active (upd_meta m f st) sc = active st sc.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh11mh22sch32stp;2g02U`j21Tg00G1j20Tg00ilR0g006:R1g00h?R2P2[R2g00K`R3g00BLf3R4f0R5'1'0X23X02X11X30P4f2f1P5O4W2W0W1W3o"). Qed.
Lemma active_put_meta st m r sc : active (put_meta m r st) sc = active st sc.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01mh11rh22sch32stp;2g02U`j21Tg00G1j20Tg00ilR0g006:R1g00h?R2g00K`R3g00BLf3R4f0R5'1'0X23X12X01X30P4f2f1P5O4W2W1W0W3o"). Qed.
Lemma usage_upd_meta st m f sc : usage (upd_meta m f st) sc = usage st sc.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh11mh22sch32stp;2g02XOj21Tg00G1j20Tg00ilR0g006:R1g00h?R2P2[R2g00K`R3f3R4f0R5'1,03X23X02X11X30P4f2f1P5O4W2W0W1W3o"). Qed.
Lemma get_head_upd_meta st m f h : get_head (upd_meta m f st) h = get_head st h.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01fh11hh21mh32sth42sci002sci011lp;3p;2p;1g00nPj34Tg028`j20Tg006oj33Tg02[Bj12Tg00G1j21Tg00ilR0g006:R1g00h?R2P2[R2g023LR3P3g00BLR4f3R5f2R6f4R734f0R8'0107833P8g00K`f5%28'0,14W4P8O1g02\:,05,14n0110100021010000X13X02X21X30P5P6f1P8O4W1W0W2W3o"). Qed.
Lemma get_head_put_meta st m r h : get_head (put_meta m r st) h = get_head st h.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01hh11mh21rh32sth42sci002sci011lp;3p;2p;1g00eFj34Tg028`j20Tg006oj33Tg02[Bj12Tg00G1j21Tg00ilR0g006:R1g00h?R2g023LR3P3g00BLR4f3R5f2R6f4R734f0R8'0107833P8g00K`f5%28'0,14W4P8O1g02\:,05,14n0110100021010000X03X22X11X30P5P6f1P8O4W0W2W1W3o"). Qed.
Lemma get_meta_rec_set_head st h v x : get_meta_rec (set_head h v st) x = get_meta_rec st x.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01hh12sth21vh31xh42sci002sci011lp;3p;2g022Sj33Tg00f?j20Tg006oj32Tg00G1j21Tg00ilR0g023LR1g00BLR2g006:R3P1g00h?R4f0R5f2R6f4R733f1R8'0107832P6g00K`f5/06,14W4P5O1f3R7/05,14n0110100021010000X33X22X01X10P7P6P8P5O4W3W2W0W1o"). Qed.
Lemma get_meta_rec_upd_ctx st f x : get_meta_rec (upd_ctx f st) x = get_meta_rec st x.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01fh12sth21xp;2g00f?j21Tg00G1j20Tg00ilR0g013>R1P1[R1g006:R2g00h?f2R3f0R4'1'0X22X01X10P3f1P4O3W2W0W1o"). Qed.
#[export] Hint Rewrite active_set_active usage_set_usage bounces_set_bounce get_head_set_head
  active_upd_meta active_put_meta usage_upd_meta get_head_upd_meta get_head_put_meta get_meta_rec_set_head get_meta_rec_upd_ctx : mst.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lookup_new_region k b l st rid :
  s_regions (fst (new_region k b l st)) !! rid = if (rid =? s_next_rid st)%N then Some (mkRegion k b l) else s_regions st !! rid.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h03ridh11bi001bh21kh31lh41oh52sth61Hh73Heqh82NEh92b0h:1ei011eh;1gh<1ri021ri031np;4p;1p;3p;2p;?p;6p;Ap;7g00Ebj4Sj3MTg00<Xj4Rj3GTg00:<j4ATg017Zj12Tg02Ofj35Tg0145j13Tg00_9j1@Tg00;gj4?j3KTg00HJj29Tg00_[j27Tg006oj30Tg02]2j2QTg00W2R0j2PTg00G1j2:Tg00=8j3LTg00<@j3HTg00=Oj3FTg00=fj3BTg00>>j3CTg00?1j3DTg00AHl?ETg005\j64Tg00ZQj18Tg00d0j4>Tg00Z2j2ITg00AjlAJTg02]Tj4=Tg00Gmj3<Tg02^Oj4NTg00g<j7;Tg00gPj6OTg00KBR1g014oR2f4R3f3R4f2R5f1R6f0R7F;p=6P1P2P4P5P6P7EOp=1g02P_R8g00K`R9g00ilR:P1g00jeR;g00kWR<P2CSR=P=P1P2P=P1P;P<P2CRCAR>%26R?A5345%36D6%@2R@P=P1P;P<P2C?RAP6P7C1g00JBRBP@%25,96RCf5RD?534,72P=PAP6%35C1n010000002000030X;=1Q7?A017?197?'PPCPBP0%249015P=PAP3P=P>%2DR0f8RCf7R?f6RE35RF%3DRGD6RHC1RIPBP@P6172FRBP=PAP3PGC1RJn010000002000050@P6%239014RKP1P0P=PAP7P=P>%2ER>f9?5C?R?%3ERED6C1172?R?50@X01P@PBA0@7?X4@1:@BP=PAP0PHC1P1AM1;<RHAL1;<RBAK1;<R?AH1;<RCAG1;<RLAF1;<RMAB1;<RNAC1;<ROP;AD1;<R<P2PGP0PFM?EE4P3P7E4W:P7O1%8KP@PJP=PAPDPEC190@7X4@1:@JPIP1PHPBP?PCPLPMPNPOP;P<P2PGP0P3PFA0103R0P1P>PDP7C>A01D>g00[mP5P7O1'Ib7W6%80eMAJE4W8P7O1n10210010200021010110103b9b<P3P4P5P6C=9<:1#3P3P4P5P6CNE4X01X5:X39X19X28P3P4P5P6P7O5X01W5X39W1W2o"). Qed.
Lemma lookup_drop_region rid st rid' :
  s_regions (drop_region rid st) !! rid' = if (rid' =? rid)%N then None else s_regions st !! rid'.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h04rid'h11oh23ridh32sth41Hh53Heqh62NEh71bi001bh81ei011eh91gh:1ri021ri031np;4p;1p;5p;2p;3p;>p;6p;@g00Ebj4Oj3MTg00<Xj4Nj3DTg00;Kj4>Tg0145j12Tg02R5j54Tg00_9j1GTg00;gj4?j3FTg00HJj26Tg00`=j1;Tg006oj30Tg02]2j29Tg00W2R0j2:Tg00G1j27Tg00=8j3LTg00<@j3ETg00=Oj3@Tg00=fj3ATg00>>j3BTg00?1j3=Tg00@Dl>CTg005\j63Tg00ZQj15Tg00d0j4<Tg00Z2j2HTg00@fl@ITg02_Tj2JTg02`Pj2KTg00gPj68Tg00KBR1g014oR2f3R3f2R4f1R5f0R6E8p=1g00ilR7P1g00jeR8g00kWR9P2COR:P1P:P1P2P:P1P8P9P2CNC>R;P4%25D4%G2R<P:P1P8P9P2C?R=P5P6C1g00JBR>P<1653R?%;2R@P:P=P5%24C1n010000002000030X9:1964A01641664':P?P>P0f4R09014P:P=P0P1P:P;f6R?f5RA#2RBD4RCC1RDP>P<P5P@P:P=P0PBC1R>n010000002000050<P5A013AR3P1P?P:P=P6P1P:P;f7R;%2?RED4C1=0<@X01P<P@A0<6@X1<17<@P:P=P?PCC1P1AM189RCAL189R@AF189RFAE189RGAD189RHA@189RIAA189RJAB189RKP8A=189R9P2PBP?M>CE3P0P6E3W8P6O1%53P<P>P:P=PAPEC190<6X1<17<>PDP1PCP@PFPGPHPIPJPKP8P9P2PBP?P0A01?0R?P1P;PAP6C<A01A;g00[mP4P6O1'Hb5W4%5?eM@IE3W6P6O1n10210010200021010110103b7b:1J45#21K45E3X01X37X21P4P5P6O3X01W3X21o"). Qed.
Lemma lookup_upd_region rid f st rid' :
  s_regions (upd_region rid f st) !! rid' =
  if (rid' =? rid)%N then option_map f (s_regions st !! rid) else s_regions st !! rid'.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01Eh11oi001oh24rid'h32NEh41bi011bh51ei021eh61fh71ri031rh83ridh92sth:1Hh;3Heqh<2r0i041ni051xp;4p;1p;2p;3p;?p;6p;Ap;7g00Ebj4Uj3RTg00;gj4Tj3OTg0145j10Tg00_9R0j1STg00G1j26Tg00<Xj4Lj3KTg00:<j4ETg01Yjj2<Tg00HJj25Tg00_[j2:Tg02]2j2?Tg00W2R1j2>Tg006oj33Tg00=8j3PTg00<@j3NTg00=Oj3JTg00=fj3ITg00>>j3FTg00?1j3GTg00AHl?HTg005\j67Tg00ZQj1;Tg00d0j4DTg00Z2j2CTg00AjlABTg00`=j1MTg01Zfj3ATg00gPj6=Tg00g<j7QTg00CAj4@Tg00KBR2g014oR3f3R4f2R5f1R6f0R7E=p=1f5R8P2P3f4R9P4P5P6E=;37p=2P2P3P9P4P5P6P7FQp=9P3P3P6P7C@p=8A3267p=4P3\3R:g00ilR;P2g00jeR<g00kWR=P3CUR>P2P<P=P3CTR?P4%06R@C1RA%S3RB16B7PBP>P?P9%05P7E2P0P3PBP>P?f6RC%09RDP7E2PBP>P?P9P0P3P;P6P>P2P3P>P2P<P=P3CLCER0f8REf7RFP7O1%0CRGD9/<CP8n10110500021010300#0g00JBRHPB159FRI18C6P>P?P9%08RJC1n0100000020000E2]0P6PBP>P?PFPJ1:37E21?8E148ERJ158ERK'>f9RL,5CPHP1f:RM,4FP>P?PLP>P0f<RNf;ROP8O1RP%0MRQD9RRC1RSPHPBP61:3PRTP>P?PLPQC1RUn010000002000053BP614EORVP2PNPBP>P?P7P>P0f=RWPNPCO1RX%0OROD91:3XRXE2X22PBPTA3B7XX1B16BTP>P?PNPRC1P2AR2<=RRAP2<=RTAO2<=RXAN2<=RYAK2<=RZAJ2<=R[AI2<=R\AF2<=R]P<AG2<=R=P3PQPNPPM?HE7PLP7E7W5P7O1%;VPBPUP>P?PMPOC193B7X1B16BUPSP2PRPTPXPYPZP[P\P]P<P=P3PQPNPLPP14NLRNP2PWPMP7CD14MWg00[mP5P7O1'Cb;W:%;NeMABE7W3P7O1n10210110300021010210104b4b<PBP>P?P8P>P0PEPFP6O1PGD9/<C#0PHPBPK1:36,8FP>P?P8PGC1n0100000020000E2eW0X73P7O1PBP>P?P8%04%M3R3E21?4C144C154CRG'>PIPHP1PJP>P?PF%0EREC1RJPHPBP6P3PJn010000002000053BP614CLRCP2PMPBP>P?P7%0LP3E2X22PBP3A3B73X1B16B3P>P?PMPEC1P9E7PFP7E7W5P7O1%;C16BJW3P7O1n10210110300021010210104b4b7P>P?P4PDC1RDPHPBPG1883PDn010000002000053BeW0n10110000021110301P7O1b0b1PBP>P?P7AA456#0PHPB1574185AP>P?P7P@C1n0100000020000E2eX22X9;X6:X82P4P5P6P7O4X22W9W6X82o"). Qed.
Lemma conc_eq st p r : s_regions st !! (fst p) = Some r -> conc st p = r_base r + snd p.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01ph11ri001rh22sth31Hh41oi011xp;2p;1p;4p;3p;6g00Ubj2?Tg00_9R0j1>Tg00Ebj49Tg00;gj48Tg00Gmj37Tg0145j16Tg00gPj65Tg00_[j24Tg006oj30Tg02aVj11Tg01\>j23Tg00G1j2:Tg005\j6=Tg02bMj2<Tg004Gj3;Tg00KBR1g00K`R2f0R33;p=2g00ilR41?12R5g014oR6%>6R7P1P6P1g00jeR8g00kWR9P6C9R:P1P8P9P6C8R9f1R89712f2R;#6E5146330P71468P0P6P2P3%13f4#2'3g01e^n10110100021010000%1;f3R0#2'3502X47%18%2;'3R7,:2P1P6P:P9A712;%60E5P3E=1<0;=027eW3X16X05X24P;P8P3O3W1W0W2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lookup_put_group g mo ai st b :
  s_groups (put_group g mo ai st) !! b = if aptr_eqb b g then Some (mkGhdr mo (Z.land ai 31)) else s_groups st !! b.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh11gh22aih32moh41oh52sth61Hh73Heqh82NEh92b0h:1ei011eh;1ri021ri031np;4p;6p;1p;2p;3p;?p;Ap;7g00b9j4VTg00bWj6UTg00Ebj4Cj3JTg00<Xj4?j3ETg00:<j4TTg01T2j13Tg01TWj1KTg01U5j24Tg01USj26Tg01:Dj12Tg00_9j1=Tg00;gj4<j3BTg00IIj2;Tg00_[j27Tg006oj30Tg00]Bj2MTg00W2R0j2LTg00G1j29Tg00=8j3HTg00<@j3DTg00=Oj3ATg00=fj3FTg00>>j3GTg00?1j3@Tg00AHl?ITg005\j65Tg00ZQj1:Tg00d0j4>Tg00Z2j2NTg00AjlAOTg02cBj4PTg02d<j4QTg00g<j7RTg00gPj6STg006:R1g01;=R2f4R3f3R4f2R5f1R6f0R7FRp=8P1P2P4P5P6P7ESp=1g00BLR8g00K`R9g00ilR:P1g00KBR;g00jeR<P9g00k>R=CVR>P;P<g00kWP9P=g00l5EUR=P2CCR<P<P1P2P<P1P>P=P2C?CTR;P3g01XJ#3#3#3#3#KR?,45,64%26D8%=2R@P<P1P>P=P2C<RAP6P7C1g00JBRBP@f5RC,;6RD144?,63,72P<PAP6%25C1n010000002000030X1<1M73A01731;73'LPDPBP0f6R09015P<PAP3P<P;f8RDf7RE140?'6RF%2CRGD8RHC1RIPBP@P6172FRBP<PAP3PGC1RJn010000002000050@P6A014ERKP1PDP<PAP7P<P;f9R;14E?,6DRE%20R0D8C1172ERE50@X01P@PBA0@7EX4@19@BP<PAPDPHC1P1AJ1>=RHAH1>=RBAB1>=READ1>=R?AE1>=RLAA1>=RMAF1>=RNAG1>=R>g00lSROA@1O=R=P2PGPDPFM?IE5P3P7E5W:P7O1%:KP@PJP<PAPCP0C190@7X4@19@JPIP1PHPBPEP?PLPMPNP>POP=P2PGPDP3PFA01D3RDP1P;PCP7C>A01C;g00[mP5P7O1'Nb7W6%:DeMAOE5W8P7O1n10210010200021110111103b9b;P3P4P5P6CP#2P3P4P5P6CQE5X01X5:X29X38X11P3P4P5P6P7O5X01W5W2W3X11o"). Qed.
Lemma lookup_del_group g st b :
  s_groups (del_group g st) !! b = if aptr_eqb b g then None else s_groups st !! b.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01bi001bh11gh21oh32sth41Hh53Heqh62NEh72b0h81ei011eh91ri021ri031np;4p;6p;1p;5p;2p;3p;>p;@g00b9j4QTg00bWj6PTg00Ebj4>j3HTg00<Xj4:j3@Tg00;Kj4OTg01:Dj12Tg02R5j54Tg00_9j1=Tg00;gj4<j3FTg00IIj27Tg00`=j18Tg006oj30Tg00]Bj2NTg00W2R0j2KTg00G1j25Tg00=8j3GTg00<@j3?Tg00=Oj3ATg00=fj3BTg00>>j3CTg00?1j3DTg00@Dl>ETg005\j63Tg00ZQj16Tg00d0j4;Tg00Z2j2ITg00@fl@JTg02e?j29Tg02f9j2LTg00gPj6MTg006:R1g01;=R2f3R3f2R4f1R5f0R6EMp=1g00ilR7P1g00KBR8g00jeR9g00K`R:g00k>R;CQR<P8P9g00kWP:P;g00l5EPR;P2C>R:P1P:P1P2P:P1P<P;P2C:COR9P4%25D4%=2R8P:P1P<P;P2C<R=P5P6C1g00JBR>P81753R?%82R@P:P=P5%24C1n010000002000030X1:1N64A01641764'KP?P>P0f4R09014P:P=P0P1P:P9f6R?f5RA#2RBD4RCC1RDP>P8P5P@P:P=P0PBC1R>n0100000020000508P5A013AR3P1P?P:P=P6P1P:P9f7R9%2?RED4C1=08@X01P8P@A086@X28158@P:P=P?PCC1P1AH1<;RCAG1<;R@AF1<;RFA?1<;RGA@1<;RHAA1<;RIAB1<;RJAC1<;R<g00lSRKAD1K;R;P2PBP?M>EE3P0P6E3W8P6O1%63P8P>P:P=PAPEC19086X28158>PDP1PCP@PFPGPHPIPJP<PKP;P2PBP?P0A01?0R?P1P9PAP6C;A01A9g00[mP4P6O1'Ib5W4%6?eM@JE3W6P6O1n10210010200021110111103b7b91945#21L45E3X01X37X11P4P5P6O3X01W3X11o"). Qed.
Lemma lookup_set_group_active_idx g ai st b :
  s_groups (set_group_active_idx g ai st) !! b =
  if aptr_eqb b g then option_map (fun h => mkGhdr (g_meta h) (Z.land ai 31)) (s_groups st !! g) else s_groups st !! b.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01hi001hh11Eh21bi011bh31oi021oh42NEh52aih62b0h71ei031eh81gi041gh91ri051rh:2sth;1Hh<3Heqi061ni071xp;4p;6p;1p;2p;3p;?p;Ap;7g00b9j4\Tg00bWj6[Tg00Ebj4Rj3QTg00;gj4Gj3OTg01:Dj10Tg00_9R0j1UTg00G1j28Tg00<Xj4Hj3JTg00:<j4FTg01S;j1;Tg01T2j1:Tg01TWj1ZTg01U5j26Tg01USj25Tg01VJj2BTg00IIj29Tg00_[j2=Tg00]Bj2ATg00W2R1j2@Tg006oj33Tg00=8j3PTg00<@j3ITg00=Oj3KTg00=fj3LTg00>>j3MTg00?1j3NTg00AHl?ETg005\j67Tg00ZQj1?Tg00d0j4DTg00Z2j2STg00AjlATTg00`=j1YTg01WEj3XTg00gPj6CTg00g<j7VTg00CAj4WTg006:R2g01;=R3f3R4f2R5f1R6f0R7ECp=1f5R8P2P3f4R9P4P5P6EC;37p=2P2P3P9P4P5P6P7FVp=>P3P3P6P7CWp=<A3267p=4g00K`R:g00ilR;P2g00KBR<g00jeR=P:g00k>R>C\R?P<P=g00kWP:P>g00l5E[R>P3CRR=P2P?P>P3CGR<P4%06R@C1RA%U3RB18B7PBP=P<P9%05P7E2P0P3PBP=P<f6RC%09RDP7E2PBP=P<P9P0P3P;P6P=P2P3P=P2P?P>P3CHCFR0f8RE%;7RFf7RGg01XJ#:#:#:#:#ZRH'6RI'5RJ%0CRKD>/BCP8n10110700021010000#0g00JBRLPB199GRMPJX03/<6P=P<P9%08RJC1n0100000020000E2]1P6PBP=P<PGPJ1=37E21A8E148ERJ198ERN'@f9RO,9CPLP1f:RP,4GP=P<POP=P0f<RQ%;8f;RR/6H'5RS%0PRTD>RUC1RVPLPBP61=3SRWP=P<POPTC1RXn010000002000053BP614ERRYP2PQPBP=P<P7P=P0f=RZ%;C16QH'5R[%0RRRD>1=3[R[E2X22PBPWA3B7[X3B18BWP=P<PQPUC1P2AQ2?>RUAP2?>RWAO2?>R[AI2?>R\AJ2?>R]AK2?>R^AL2?>R_AM2?>R?g00lSR`AN2`>R>P3PTPQPSM?EE7POP7E7W7P7O1%?YPBPXP=P<PPPRC193B7X3B18BXPVP2PUPWP[P\P]P^P_P?P`P>P3PTPQPOPS14QORQP2PZPPP7CD14PZg00[mP5P7O1'Sb<W;%?QeMATE7W4P7O1n10210110500021110311106b6b9PBP=P<P8P=P0PE%;6/5IPKD>/BC#0PLPBPN16EH,5FX031=36'<P=P<P8PKC1n0100000020000E2eW1X03P7O1PBP=P<P8%04%Y3R8E21A4C144C194CRK'@PMPLP1PJP=P<PG%0EREC1RJPLPBP6P8PJn010000002000053BP614COR1P2PPPBP=P<P7%0OP8E2X22PBP8A3B78X3B18B8P=P<PPPEC1P9E7PGP7E7W7P7O1%?118BJW4P7O1n10210110500021010310106b6b9P=P<P4PDC1RDPLPBPK16CH,5FX03/<8PDn010000002000053BeW1n10110200021110401P7O1b1b3PBP=P<P7AX456#0PLPB1974164H,5FX03/<AP=P<P7P@C1n0100000020000E2eX22X:;X5:X82P4P5P6P7O4X22W:W5X82o"). Qed.
Lemma group_active_idx_eq st g m ai : s_groups st !! g = Some (mkGhdr m ai) -> group_active_idx st g = Z.land ai 31.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02aih11gh21mh32sth41Hh51oi001hi011xp;1p;4p;6p;2p;3g00_9R0j1@Tg00b9j4?Tg00bWj69Tg00Ebj47Tg00;gj4>Tg01:Dj16Tg00gPj65Tg01USj24Tg00_[j23Tg006oj31Tg02g<j18Tg01T2j10Tg01TWj1:Tg01U5j22Tg00G1j2=Tg005\j6<Tg02h9j2;Tg00ilR1g006:R2g00BLR3g00K`R4g01;=R5#@R6P2P5P2g00KBR7g00jeR8P4g00k>R9C?R:P7P8g00kWP4P9g00l5E9R9P5C7R8P2P:P9P5C>R9f2R:f3R7#6E5f1R;f0R<'4,3531P614:;,35P0P5P4P<%8<g01XJ#0#0#0#0#:R0'2g01e^n1011010002101000012:0514X5612;0R0,=4P2P5P8P9P7f4R9#6E5P<E<1;97=140eW4X04X23X12X31P7P:P;P<O4W0W2W1W3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_iter_ind {A} (f : A -> A) (P : Z -> A -> Prop) x :
  P 0 x -> (forall n a, 0 <= n -> P n a -> P (n + 1) (f a)) -> forall n, 0 <= n -> P n (Z.iter n f x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01nh11Ah21Ph34__x1h41ah51fh62n0h71xh82H0h92HSh:2Hnh;2IHh<7__arithh=4__ffh>8__varmaph?5__with@4cstrhA1khB5lemmahC1zp;2p;1p;4p;3p;6p;:p;7p;8p;5p1006:p4p70p200R0p8P0g02i:R1p4p710p8P0g02igR2p4p710p8P0g0058R3p4p7210p8P0g02jXR4p4p7201p8P0p1001]R5p4p7210p8P0P5p4p710p8P0g02k:R5p4p7210p8P0g02kXR6p4p710p8g02lOj22Tg01TWj1]Tg01\>j27Tg02lkj16TP4j40Tg02Lfj19Tg02mLj11Tg006oj34j18Tg001?j4@Tg00Q:j43TP2j3=TP6j45Tg00N?j3\Tg02mlj1VTg02n[j6UTg00M2j2STP1l:RTg02oFj2QTg02odj1LTg030Bj1KTg030gj1ETg01>\j1CTg031Gj2BTg031ej1DTg032Cj1ATg032nj2FTg033Qj2GTg0344j4HTg034_j7ITg00`=j1JTg035Cj8?Tg035gj2>Tg00G1j2MTg036Ij2NTg0375j3OTg037Tj4PTg038Fj1<Tg007Ij6:Tg02A^j1TTg038gj1[Tg005\j6;Tg02B=j4ZTg039Kj2WTP5j4XTP3j5YTf0R3f1R5[R1g00K`R6f2R2p-0R4[[R7P5g01e^R8P3O2f5R91285R:P9P2P5O2f6R;f3R<g01XJR=#]R>'7f7R?P2O1O2[[]4^061283R@P?g02A?RAf8RBW0RCf4RDP?X0A%65REC0P;P2P3O2X4?%95RF#1=465f9RGP4[\6RHP6P4\BRI%86RJPBP4%8BP4P4P4g03:8RKC@RLC3RMC3RNP6PIPMPBP4PLg03:V9=4KC5C59\HNP;P2%92#1RNP6PJ%V6PNP2P3EUPGX0ARNP9PC%62C0RCPC1SBCM:RWB1Q53PAPEP;%13RJPCO2X0APEPAP?PJf:RJX0AREP;PNP3C0O2RNX6APDP6%15RC#LRHPGP3PJf<X0APBf;X0ARJP2C0O1O2XC6RGP617C>PGP9PCPJP?PEP5C0%K5128Cg03;GR9#E%C91B65%D6%A6R9g03<3RGg03<RR>P>g03=2RKP9PGP>P>PKP61F68g03=R1G6=CHg03>9FIR=%J>P=G?1>9KP3P2g00JBRKg00JbR9'M1N32=4K9dAO685CPb=b>b?X36P:\@^36P3%1<P5O2b<b@P3O4PH%<CE:%T5RC#1RH%[5E;PBPHPJP?PEPCC0O2eX;NXAAP3CZb6PF1W53E:O2P5P?P;PDCXP5P?P;PDP3DYE;W:X06W9W8X72X27X51X10P<P2P5P3O4X72W2W5X10o"). Qed.

(* [comment removed for export] *)
Lemma lookup_add_slots m p stride cnt st s : 0 <= cnt -> 0 < stride ->
  s_slots (add_slots m p stride cnt st) !! s =
  if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? cnt)
  then Some (m, (snd s - snd p - UNIT) / stride) else s_slots st !! s.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02IHh14__x1h21bi001bh31Hh42H0h54__x2h61Eh72E1h87__arithh92H1h:4__ffh;4__p1h<8__varmaph=5__with>2NEh?2b0h@1ni011nhA1ei021ehB1mhC4__x3hD4__x4hE3acci033acchF1ri041rhG1FhH2_HhI1shJ1zi051zhK2H2hL4__x5hM4__x6hN4__x7hO1ahP2b1hQ2b2hR3cnthS1ii061ihT1ohU1pi071phV2srhW2sthX6stridehY1GhZ3GENh[2H3h\2Hch]3Heqh^2Hih_2Hkh`2Hnha2Hshb1khc2n0hd2pohe2prhf2sohg2tbi082tbi091gp%0p%1p&0p&1p;2p;4p;6p;1p;3p;7p;?p;8p;Ap;5g00UbS00k20>Tg03>Yj2@Tg00b9k40RTg00bWk61>Tg00Ebk40lk319Tg01TWk10`Tg01\>j25Tg00<Xk40Wk311Tg00:<k40FTg01]Uj2>Tg00_9k10kTg00;gk40hk315Tg01\[j26Tg01<4j1KTg00gPj6=Tg006oj30Tg00G1j2MTg00HJj2ITg01]8j2;Tg00FSj22Tg03?5j2}Tg03?WS01j3nTg00LWS02j2^Tg00M^k20qTg01[aj2fTg02lOj2?Tg03@;k20gTg03@[k40fTg030gk10eTg01>\k10dTg03A<k10bTg031ek10_Tg032Ck10^Tg032nk20ITg01T2j1~Tg00`=k10]Tg035gk20\Tg036Ik20[Tg0375k30ZTg037Tk40YTg00Z2k20:Tg03AZk10XTg005\j6\k70Mk80uTg00S<k40GTg00]Bk20STg00IIk20ETg00W2S03k20DTg02:7j2jTg00_[k206Tg033Qk20BTg01e9k104Tg03B:j3sTg03B]j3{Tg01knj2JTg00F6j2wTg03C@k20@Tg03Cbk205Tg03DCk20PTg02A^k103Tg03Dlj2zTg03EUk30?Tg03F>k208Tg03Fjk309Tg00GKk10OTg03GJk60UTg03Gnk31=Tg03HOj2LTg03Hok21<Tg007Ik61;Tg00Hgk11:Tg00g<k70=Tg00=8k318Tg00<@k312Tg00=Ok310Tg00=fk30~Tg00>>k30}Tg00?1k30zTg00AHm?0sTg00ZQj1XTg02SDk20rTg00PZk20pTg00SWk30nj4eTg03IOk30oTg03J0k40JTg03JQk30LTg03K2k301Tg029Yk10jTg009>k80tTg03K[k20iTg03L:k20vTg00d0k40wTg00AjmA0xTg03LYk80yTg02k:j4gTg03MTk20{Tg03NNk50|Tg00Gmj3yTg004Gj3dTg031Gk213Tg03OHk40cTg0344k40<Tg03Ofk614Tg034_k70NTg035Ck816Tg03PJk317Tg03Pmk30aTg01e^R0f0R1'?p=Af1R2g02C=R3/51'jp=ig006:R4g00K`R5P2P1Cep=`P4f5R6f4R7f3R8f2R9P2P1K0=p=pP5P9P2P1Cep=EAy521p>0KAd521p=Fg00KBR:?y51p=4Ay:52/I1p>00Ad:51p=11J21/J3p=71f01p=D1L21/w0p=H1292/21p=C1;21,29p=NP4P5P2P1Ce-069p=3f7R;f6R<P6P7P8P9P2E=;01p=8A0592/^1p>0CP5P2P0P1Cep=lP6P7P8P9P2%K1E=p=9g00JBR=g00JbR>701p=<1@10p=Q12>1p=WAd:52,J9/J3/61p=U1I921f01'2p>0;Ad:52/J1/J3p=O21351p=oP5P9P2P1H0cp=B20B51p=cP5P2g03=RP1H0<p=uP5P2g03QVP1H0<p=mP2g03<3S04g03<RR?P?g03=2S05P1J14p>0HP7Q04P?P?Q05P8Q04P?P?Q05P9g03>9R@K0NP2P1L16p=Gg00[MRA/21p=kA0510p=TP<P6P7P8P9Ad521E=p=tA0921,^8p>0V1I<61f07'21L89/w0'21;21'2p=RAy589=052/^1p=]Ay592=051p=|12891;21'2p=hP5P9P2P1Ce9d58p=S1L92/w0,28/21p=r1I671f08'2/291;21'2p>0TA0521p=VA0421p=q1>21,53,j99048p=_1>21,53p>071f01,22p>0QP:P5P2P1Cep=:B17521p=bP5P2g03R=P1H0<p=aP2Q04P?P?Q05P1P@K0Np>02P:P5P81>21,53,59Cep=Y1w10p>0AB0a521p=[1J92/J3/61p=PA0:21p=ZAd:52/J1p=x1J23/61p=v1j219049p>0mg00ilS0620>:5R@Q06%A9S071@07P4P:g00jeRBP5g00k>RCH0RRDP:PBg00kWP5PCg00l5J1>RC20>45RBH0lRE-0>5RFQ00P5PEPFP1g01XJRG$0`RH,52S08PBPEP4PBPEP4PDPCPBH0WS09H0FS0:f9RIf8RJ/>2'if:RK/`2P1Ep5EEn2001103000120106108WES0;PF^EFS0<%A1S0=PFP920KE1S0>&0kBRLP@PBPEP4PDPCPBH0hRMP;1FE1S0?P=PLf;RN#4-00;%1;S0@%1NRO'7RP#D1HPK3CRQ16PKRP;N2f<RR=3BPP@PBPEPMP;%KJS0AE=n0100000020000G880C2XFFX@5%K<RP,lES0BA0500P@PBPEPMP6PPE=S0CP=PL%4IS0D-006%16S0E%1IRP'7RS#D1HSJ3CS0F16SJS0G;N0Q0G93BKS0HQ0Cn0100000020000S0I50L1M50Q0FP=1M=1S0J%4<S0K%4KS0L'I%1<S0M%1KRS'7S0N#DQ0N/HI3CS0O=0=1P=%4JS0P%4RS0Q'I%1JS0R%1RRT'7RU#D1HUN3CS0S=0=1P@PBPEPMPIPKE9S0TP=PLf=RV#1RW,7PS0U/6RRP/;0RX,22f>RY=3BPS0VQ0Tn010000002000050L]6P2%<Q16UNRU/}0%QU%AU1;U0S0W3nPXP=Q01%1YRX,7SS0X/6VRS#Q%ASP@PBPEPMPRPVE9RZP=PL%W2S0YfAR[f@R\#1R],7TS0Zf?RT'6S0[53BS0\PZn010000002000050LP2AUOTYS0]#QP=PL12>>ROQ0\PZn010000002000090LZQ021221#<%<9R^%<2R_'^[R`%<1,^_1292#<R_[%<8/^^\_20q21P2n2001000000120000000XQ=XP=R_P`^Q=^P=R`P1%4VS0^%4[S0_%1[R^,7WRW40;Ra1HW\RbP6O3%<a%<b'^Q02%4YS0`fBRc#4S0a%1cS0b,7XRX40;S0c#<1HX[S0d#<g00[mS0eP1%4\S0ffDRd#4Re%1dRf,7]R]40;S0g#<fERg#1,7^S0h/HdS0i#<P_P`P1fCR`fGR_#4S0j+00R^%1_Rh,O`Ri#DRjP9O3%<^%<j'^Q02fHRk#4S0k,Ie#<%1k,7f#D#<Q0eP1fFRf#4S0lfJRe#4S0m'IS0n#<fKRl#1Rm,7hS0o#DS0p#<Q021f21#<1?92S0q[Rh1?211f92#<Rn[1?89\n20g21P2n2001000000120000000XB5X@5Ph^B5^@5P1P0fIRhfMRn#1S0r'ORoP2O3%Ao%1eRpfNRq#1S0s'7RrPnP1PkH0f16rnS0t#Ap-0Rsg03;GRt$0eRu&0dtRv&0b5Rw%o2S0u9Bw27B2&0_5S0v&0^5RxPx20I50Ry%~GS0w#~#cRz'u&0]?R{PxPx1mzyP{20Hx8S0xDGDGQ05-0\xS0yP1P91M=>20[19#<dB0Z502H0YS0zb:b<b=X15W;Q0=%Q2P8[[^15^;sP1Q0efLRz#1R|fPR}#1S0{'7S0|fOR~'6P2P\O4b8b4b6b4W6WHP2P1O2n2001000000121000000b6b4WHW6P2P1O2n2001000000121000000b6b4+0:W3P1O1Q0]#AP=PAP@PBPEPMPVPYE9S0]P=PLP116W\RW93BcS0}Q0]n010000002000050LX2=1MLZ12>AS0~&0X>E\W3P1O1n200210000000021100010000b?b2W6A0=QAP=PLQ0W#kA3BVUS0WP@PBPEPMPJ%KIS10E=S11n0100000020000,MLW6n0110000020100P1O1b6b2H0GQ0B-0KE#TPLP@PBPEPMP6PEQ0BFtQ0IH0VeQ00P5PEQ07PEP2P8PLP@PBPEPMPI1FE2P=PLQ0DQ0^Q0UQ0UPRPPP8FRQ0VQ0Tn0100000020000G8C]PEP;P9O1RP157HRQPLP@PBPEPMPK1FEPP=PLQ0LQ0`Q0XQ0XPVPSPQFRA3BTSP@PBPEPMPKPNE9n0100000020000G8C][[P1%A6PEAEE92RSP<PLP@PBPEPMPR1FESP=PLQ0QQ0fQ0ZQ0ZPTQ0[P<FRQ0\PZn0100000020000G8C]Q02AEE89RZ=|E;PLP@PBPEPMPV1FEZP=PLPaPbPWP;ChQ0}Q0]n0100000020000G8PEPNAEE78O1RW15JHRbPLP@PBPEPMPY1FEWP=PLQ0cQ0d16X[RXPbChA3B`XP@PBPEPMPYPTE9n0100000020000G8C]P1AEE67=|EIPLP@PBPEPMP\PEPEP<P6CSP=PLQ0gP]P`16]`R]/;KCrA3Bg]P@PBPEPMP\P[E9n0100000020000G8P5PNPLP@PBPEPMPcPEPEP1P;CSP=PLQ0aQ0l'IQ0b%1fR]'7RX#D1HXg3CRb16XgRX;NRA3B_XRWP@PBPEPMPcP`E9Ran0100000020000G8PEP\AEE2JO1RZ15VHRSPLP@PBPEPMP`1FEZP=PL12^jPiPf16ifRi/;SCrA3BkiP@PBPEPMP`PdE9n0100000020000G8C]]0XS5PLP@PBPEPMP[PEPEPNP<CSP=PLQ0_%4gQ0hQ0iQ0h/6dRiPNJ0TA3BfiP@PBPEPMP[PcE9n0100000020000G815RHRi/ViPLP@PBPEPMPcPBPEQ0:1>gR,ifRS1`_RP;EpS0hP=PLANbXiPWPan0100000020000S0iG81M5i20ScS1qcS20EcS+0D1>fV,i_-0E`P=Q03PdPkP_PYC_PLP@PBPEPMPfPBPEQ0:1>h\,ieRS1`l\S0_PNEpP=PLQ0n17]pR]#D1H]h3CS0b16]hS0l15\H3NQ0l93BlS0aP@PBPEPMPf%K_R]E=S0gn0100000020000G8P2PgPhPkPTC_S0dP4PSPLP@PBPEPMP1PEPEP[PRCSP=PL%41S0c%4lRa1O1mRWPWPe16WeRWP[FRA3BzWP@PBPEPMP1%KkS0]E=n0100000020000G8PLP@PBPEPMP2PBPEQ0:207lcRW,jzRX1`ncRbPVEpP=PL%42S0}%4zS0\%12S0[/7|RjPjPl16jlRj15cHS0ZFRA3BnjP@PBPEPMP2%KhRjE=n0100000020000G8]0XI4PLP@PBPEPMPSPEPEP\PNCSS0fP=PL%4SQ0m1OSpRpPpPh16phRpP\FRA3BlpP@PBPEPMPSP]E=n0100000020000G8PL1`z[S0m-06BS0QP=PL%4XQ0\1OX|R]P]Pl16]lR]Q0ZFRA3Bn]P@PBPEPMPXPjE=n010000002000090L1XTLP=P>206BbS0XP=PL15|WRW/7|S0`-0Q1Q0`PlQ0`/6lRbQ0Z';CrA3BnbP@PBPEPMQ0\/:WPjE=S0Ln010000002000050LX2=PuPv%o7?B9w%o87B2Q0v20B5GRj&04GS0T#cRW5s5Q0w#cS0VQ0T$04S0U#cRbAs5Wj'b'bQ0V5{5={5b'a-02xQ0yQ0zb:b<b=X15X55XC5XD51>121>21S0^,58,59/J9/J8'V^15^55^C5^D5P1P3P|PlPcO4b81>[e207e[S0D,5mS0I/7m'VP51>clR|A3Bq`RXP=PL%D1#WP1Pz161zR]15`HRp';CrA3Bq]P@PBPEPM%4nS12Q0rPzP`CY%KeS13E=R]n010000002000050LXJ5P5P0P=PL1>`zR^#DRZ#WRQ&0A116^zR^PpChA3Bq^P]n010000002000090LXXJ5P5PcP=PLPQ1w00S14P1PpChA3Bq1P]n010000002000090LXXJ5P=P>P=PLPQP1P`PpChPXP]n010000002000090LXX2=20@0|%A|%Q|%D|S153nPZP=Q011>dnRZ#A%QZfQRZ=3BfRXP=PL15fHR],;fRp9C2>PXP@PBPEPM%4}Q0{P~PfCYPnE9n010000002000050LP21>gqS16#A1}f]1@f]1?]f;np15_H,;_S17P=Q0115kHRp,@k1?pkfURp=3BeR]P=PL12O2S18P]P@PBPEPMfTRX#4%1XS19fSRQPeCYPZE9R^n010000002000050LP215hHS1:,@hP=PL12O>RPP]P^n0100000020000,MLW4P1O1Q1:/?hPuPvQ0u?B2w?B2wQ0vPxPx20I5HS1;,bbS1</ubP{Q0xDGQ0yQ0zb:b<b=X15X;s151HS0x/?1P9[^15^;sP1fVR^=3BlR]P=PL12OAS1=P]P@PBPEPM%4p%1pS1>PXPlCYfRR]E9n010000002000050LPlP2O3b8W4P1O1n200210000000021000010000b?b2W3P1O1Q16#Q2055HS16-0P5g02B^S1?$03S1@$03S1A,z5S1B60?5Q1?,z5S1?Q1@,z5S1@60?5Q1@'['[g03RdS1C+08>09tuPv%o9S1D?B2wS1E?B9wQ0vPxPxAs5bW/myP{PxPx1uybP{PxPx1myWP{20Hx7S1FDGDGDGQ0yQ0zb:b<b=X15X55X;sQ0^#QQ071@09P6[[[^15^55^;sP1A3B]_S07P=PLQ179CA>Q07P@PBPEPM%4Z%1ZS07P}P_CYPqE9n010000002000050LP_P}P2P[PlO6b8W3P1O1n200210000000021100011000b?b2Q0XP=PLQ15#WP>PcQ0ZChQ0XQ0Ln010000002000050LeQ14&0O0E\16|lPuPvQ0uQ0vPxPx1myjP{PxQ04P?P?Q051ajy-02xJ0UDGQ0yQ0zb:b<b=X15S051@01%T2Q0e[[^15S04P1PzP_O2b8:1=clE\1L|l21<clE\Q0`P1J1;b31Iaa&1:aE\Q0QP=PLQ0I,:aR|#4Pa1O|mR?P?Pe16?eR?15[HS0IFRA3Bz?P@PBPEPMP|Q0]E=n010000002000050LeQ0QP=PLQ0D,jlR|#4Pa1O|mR?P?Pe16?eR?Q0IFRA3Bz?P@PBPEPMP|Q0]E=n010000002000050LeP@PBPEPMP|P@PBPEP@PBPEQ09H0FS09P|Q0mPRK0=E=P@B194DCS0QB184DCS0DB154DCS0`B124DCS14B114DCS0XB104DCS0LB0~4DCS0ZB0}4DCS15g00lSS17Q17>0z4CS0^PBPRP|Q0mN?0sE\W0PfP1P7K0MWAP1O1Q0d#XPLP@PBPEPMPfPNE=P=PLQ0j/IaRaQ0p'2Q0oPeQ0o/6eR|Q0I';CrA3Bz|P@PBPEPMP_Q0]E=n010000002000090L1XTLR|PLP=PLQ0bQ0l;N\Q0aQ0gn0100000020000P|Q0nP=Q0JA0=a1P=Q12-00h=0=1PLP@PBPEPMPePEPEPdPTCSP=PL%DrRa,221HrnS12Q0t/;dS0J3CQ0t93B~S0nP@PBPEPMPePlE9R|n0100000020000G8P=PL%1~RC,7mRm#DS0g1Hmq5C9RD16mqRm;NgA3B}mS0aP@PBPEPMPlPzE9R?n0100000020000P=PL15gH9NDmQ0aP?n010000002000050L]0]7P2Q0kQ0\'IS0\#<P@PBPEPMPhPEAEE`YFtS0kP=PL%DoS0a#W1HozS0l16ozRz/;`S0b3CA3BqzS0]P@PBPEPMPhQ13E=S13n010000002000050L20@0r%Ar%Qr;naQ0gP=Q01Q0|#AQ0|#QP@PBPEPMPqPEAEEk`FtS0|P=PLQ0YQ0s%1]S0g'7Rr/HZS0s16rZRr/;kS0I3CA3BQrS0YP@PBPEPMPqP~E9S0on010000002000050LP=PL%1QRr,7CRC/L]Rz$0ARo,29R?16C]RC/;hS0p'2A3BXCS0jP@PBPEPMP~P}E9Rmn0100000020000P=PLQ1:,;CS1:,2?Q0jPmn010000002000050L]0P2Q0rQ07'7S0r#AQ0|P=PLQ0sQ0I5COQ0YQ0on010000002000050L20rz0%Tz00DoQ0{Q19'7/HQP=Q03Q07Q1>'7/LX#TP@PBPEPMPQPEAEEnkFtS07P=PLQ18fWRz#1S03=Pr^Rr/;nS0{'2fXRO=3BrS18P@PBPEPMPQPXE9S0dn010000002000050LP=PLQ19%1OS0m;PzRz/;qRr,29fYR?=3BzRCP@PBPEPMPXPpE9RDn0100000020000P=PL15qH,;zS19,29PCPDn010000002000050L]0P2Q0g%1^S1G'7/Lp#TS0gQ07P=PLQ0{,2PQ18Q0dn010000002000050L1}zq1@zq1?qz;nrQ1>%1?Rz;PO/;~P=Q01Q1GfZR~#1S1>;P?Rq/@}1?}qP@PBPEPMPOPEAEE]nFtR]P=PL12P2f]RnQ0mf\S1G#1S1Hf[Rq3P53BS0mP@PBPEPMPOP?E9S1In010000002000050LP=PLP9f^R}%1nS1JQ1G5PzRz53BS1KP@PBPEPMP?P~E9S1Ln0100000020000P=PL15QHRQ,;zS1MQ1KQ1Ln010000002000050L]0P2Q03%1qS1L;P~S03/@ZP=PL12P>Q0mQ1In010000002000090L]1}zQS1K1@zQ1?QzQ1M3nS1MQ1>%1}S1N;Pn15XH';S1>P=Q01Q1Lf_RX;U}RQ15pHRp'@S1L1?pQS1OfbRpQ1JfaRQf`Rz3U53BR>P=PLP2P>P@PBPEPMPnP}E9Rnn0100000020000S1J50LP2Q1H?UzXS1H15^HR~'@S1P1ML>W9P1O1Q1H,?~S1HPuPvQ0u?B9wQ1D?B9w?B9w7B9Q0vPxPxQ1<Q0U#~#cR~'uP{PxPx1m~bP{Q1FDGDGQ0yQ0zb:b<b=X15X55X;sQ0x/?21@92P7[[^15^55^;sP1fcS0xQ1N?UpQRs53BP@PBPEPMP}PXE950LPsPOP2P<O5b8W9P1O1n200210000000021000011000b?b2W0W4P1O1Q03,?ZP=PL12PARPQ0mQ1In010000002000090L]Q1KQ1MQ1>P=Q01Q1LQ1OQ1J90LnP2Q1PA0Ln>P_Q021I21#<1Z92[R>1Z211I92#<R][1Z89\]20p21P2n2001000000120000000XB:X@:P>^B:^@:P1%4}R>%4pR]PgO31Z>]Q00P:P5Q0cfdR]#4'ZPLP@PBPEPMP2PEPEPqP^CSP=PLPPffR^Q0[feS0c;U]53BP@PBPEPMP2PpE9n0100000020000G8P9P^Q0cQ1GC_#XfgR^#1,O8#A%17R]fhRq#1R>'7/L^#TQ0EfiRZ;Uq,?XQ0MfjRO#1S1G;PZ15zH'@fkRz#4%1zRsPOPQCY,q;]9]4]A]3]>]0]7PX1:21#4%4^'ZPLP@PBPEPM1:92RQPEPEP}P?CSP=PLPP1xQ>/v^93BZP@PBPEPMPQQ0cE9n0100000020000G81:89S0[PZPqPXC_#X1:78S1JQ1G'O#A1:67#1S1G/7s/LO#T1:<6#1S1OflRs;Uz,?p1:;<#1S1LfmS01;UsQ0x/5H'@Q00P:P5Q00P5PEPFP1Q08PBPEQ0:fqS1>/>2,i8fsRZ/`2P1Ep5EEn2001103000120106108XEFQ0<1:KIS1M#4Q0}'ZPLP@PBPEPM1:NKR>PEPEP^PpCSP=PLPPfrR^%19S0},x>fpS1K'v53BP@PBPEPMP>fnR}E9n0100000020000G81:RNP8Q1>PqC_#X1:VRS1I/O]#A1:YVS0m#1S03Q0E'7/LZ#T1:TYS0EQ0M'xftRY'v,?z1:\T#1S1NQ0@fuRq3P15sH'@1:[\S0@Q0PQ0RfvR\Q01CY'q]9]4]A]3]>]0]7bGP}Q00P5PEPFP1Q08PBPEQ0:Q1J1>Y2'i1`\2P1Ep5EEn2001103000120106108XEFQ0<Q1I#4%4Q'ZPLP@PBPEPMQ0mPEPEPOQ0cCSP=PLPPQ03Q0[;UZ93BqP@PBPEPMQ0mQ1>E9n0100000020000G8Q0EQ1JPYPzC_#XQ1NQ1G'7#AQ0@Q1O'O/L\#T1:c[Q1L'xfwR\'v,?}1:`c1:J;#1'xfxR}'vfo/5H'@P:PIPLP@PBPEPM1:1dRYPsP@PBPEPMPYP}E9G81:2gf{RY007^Rs80m>#X1:9fPRPNf|R>PZCY'q]>]0XV:PLP@PBPEPM1:I`RPPzP@PBPEPMPPP\E9G81:KdQ1MfzQ1>C_#XP5P4B0n:5NR\P\Pg15KsP4\5/M\PuPvQ1EQ0vPxPxQ1;,bW,mjP{PxPx1uWjP{1ajW-02xDGDGQ0yQ0zb:b<b=X15X55Q08,@1Q0q1V98[[^15^55P1PZ17fNRZ/6>R\P8P7O4b8APgKY/V^Q05Q04P1f}P}O2b8:0oZ>1>>\1LZ>'5,VZQ1A$03,z5RZQ0wP5Q16PG20550R0H0J60L5Q1B6015Q1@Q1?'['['[Q1C+08&0jG-055R>>015ZQ0wP5P>PGP0H0J60L5Q1B6015Q1@:015>Q1?'['['[Q1C+08>09tu609tPv%o<?B7w?B9w%o;?B6w?B8w7B2Q0vPxPxA{5jWQ0V5{5As5b~Q0U$04#cRw'b'aP{PxPxQ0T#~#cRv,a~P{PxPx1awyP{Q0VAs5bv'b,bW,aj-02xDGDGDGQ0yQ0zb:b<b=X15X55XC5XD5XL5XM5XN51J12/J91>8</56'V1V;6%T;1><;,56,57,V8[[[^15^55^C5^D5^L5^M5^N5P117kVRxf~Rj'61LxjPqPjP3PVPkP2P9P;O:b8b[bKL0tW>W0PdP<P6P7L0u1:d`1:IJR`#4%1`fyQ1KCY'qeW9W4WAW3W>W0W7bGXd5Xe:P2P1O2n2001107010121101105P<P6P7P8P9P2P1O7W9W4WAW3W>W0W7Xf5XV:P2P1O2n2001107010121101105P1P<PhP[PRP;P9O7PXQ0xPpP?C_eb7bKO1+0:W9P1O1Q1H1MLnW9P1O1n200210000000021100010000b?b2W0W4P1O1n200210000001021100011000P9O1b?b2P=PL%WrPCPDn0100000020000P=PLQ19#WPCPDn010000002000050LeW0WAP1O1Q0g#XQ07P=PLQ1=Q0{'2Q18Q0dn010000002000050L1MLDP=PL%krPCPDn0100000020000P=PLQ19#kPCPDn010000002000050LeW0WcP1O1n10210010401021110211101P9O1b2bFP=PL%WoRDQ0p'2Q0jPmn0100000020000P=PLQ1:,2DQ0jPmn010000002000050LeW0W3P1O1Q0r#QQ0|P=PLQ0~Q0sQ0I3CQ0YQ0on010000002000050L1MLmP=PL%koRoQ0p'2Q0jPmn0100000020000P=PLQ1:,2oQ0jPmn010000002000050LeW0W3P1O1n200210000001021100011000P9O1b?b2P=PL%WaQ12'2RmQ0J'2Q0nP|n0100000020000P=PLQ0t15dH';Rd,2mQ0nP|n010000002000050LeW0W7Q0\=0=AQ0kP=PLQ0a#kQ0lQ0b3CQ0]Q13n010000002000050L1ML|P=PL%kaQ12'2RaQ0J'2Q0nP|n0100000020000P=PL12adQ0nP|n010000002000050LeW0W7n0110001020101P1P<O2b7b2P@PBPEPMPfQ0fE=P7E\P@PBPEPMPfP@PBPEQ09PSQ0_PNK0=E=P@Q0QQ0DQ0`Q14Q0XQ0LQ0ZQ15Q17Q0^PBPNPSPfQ0_A0@SfRSP@20ie[-0v3,jlRlP_P1H0wA0@_lQ0eP9P1O1+0:b]W3%XSeNA0xE\W>P1O1n10210010401021110211101b2bFH0GPEQ0h9EEiRSPiPLP@PBPEPMPc1FESQ0iG8C]ePEPTAEER;O1RRPiPLP@PBPEPMPc1FERQ0iG8C]eW0P;P2P1K0MW0W^P2P1O2n2001000010121000000W3W_XgEXS5P2P1O2n2001107010121105109XOFXb5P2P1L0yW`X@5Q0=P2PFP9Q0BCgPFQ0>PLP@PBPEPMP<Q0?P=PLQ0OQ0N/6IRR;N9A3BNRRNP@PBPEPMP<%K;RcE=Rin0100000020000G880C9bF[^@5P1P<P8O2PEP<PFP2%K6RT,lECgRSP<PLP@PBPEPMP71FESP=PL%47Q0PQ0R,7]R]P]P;16];R]P<FRA3BI]P@PBPEPMP7PTE=n0100000020000G8C]Q02P;PFP9Q0BCgRT=|E;PLP@PBPEPMP61FETP=PLQ0FQ0G;N;Q0HQ0Cn0100000020000G8PLP@PBPEPMP<PJPFP81lEcCg,FEP=PLQ0O?NRJPNPin0100000020000G8P1PIPFP7Q0A,lECg=|EIPLP@PBPEPMPJPKPFP6Q10,lECg,FEP=PLQ0S?NUKQ0WQ11n0100000020000G8P1WYWHP2P1O2n2011000010121000000bObZbGPLP@PBPEPMP9P7PFQ0;%K8RF,lECg,FE00{8#KP=PL%49Q0KQ0}Q0M'7R=P=P616=6R=P7FRA3B;=P@PBPEPMP9PFE=n0100000020000RFG8ePLP@PBPEPMP9P;P<P6P7P8I0|#KPFG8eWaW\XI@WWXR5XX5XU4XB4P6P7P8P9P2P1O6WIWWXR5XX5XU4XB4o"). Qed.

Lemma lookup_del_slots p stride cnt st s : 0 <= cnt -> 0 < stride ->
  s_slots (del_slots p stride cnt st) !! s =
  if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? cnt)
  then None else s_slots st !! s.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h02IHh14__x1h21bi001bh31Hh42H0h54__x2h61Eh72E1h87__arithh92H1h:4__ffh;4__p1h<8__varmaph=5__with>2NEh?2b0h@1ni011nhA1ei021ehB4__x3hC4__x4hD3acci033acchE1mhF1ri041rhG1FhH2_HhI1shJ1zi051zhK2H2hL4__x5hM4__x6hN4__x7hO1ahP2b1hQ2b2hR3cnthS1ii061ihT1ohU1pi071phV2srhW2sthX6stridehY1GhZ3GENh[2H3h\2Hch]3Heqh^2Hih_2Hkh`2Hnha2Hshb1khc2n0hd2pohe2prhf2sohg2tbi082tbi091gp%0p%1p&0p&1p;2p;4p;6p;1p;3p;5p;>p;7p;8p;@g00UbS00k20:Tg03>Yj2?Tg00b9k40RTg00bWk61<Tg00Ebk40kk318Tg01TWk10_Tg01\>j24Tg00<Xk40Wk310Tg00;Kk40CTg01]Uj2=Tg00_9k10qTg00;gk40jk315Tg00HJj2DTg01\[j2<Tg00`=k10DTg01<4j1KTg00gPj6:Tg006oj30Tg00G1j2LTg01]8j2;Tg00FSj21Tg03?5j2}Tg03?WS01j3jTg00LWS02j2`Tg00M^k20pTg01[aj2_Tg02lOj2>Tg03@;k20gTg03@[k40fTg030gk10dTg01>\k10cTg03A<k10bTg031ek10^Tg032Ck10]Tg032nk20HTg01T2j1zTg035gk20\Tg036Ik20[Tg0375k30ZTg037Tk40YTg00Z2k207Tg03AZk10XTg005\j6Zk70Kk80hTg00S<k40FTg00]Bk20STg00IIk20BTg00W2S03k20ATg02:7j2fTg033Qk20?Tg01e9k102Tg03B:j3oTg03B]j3wTg01knj2CTg00F6j2lTg03C@k20=Tg03Cbk204Tg03DCk20PTg02A^j1~Tg03Dlj2vTg03EUk30<Tg03F>k200Tg03Fjk305Tg00GKk10OTg03GJk60NTg03Gnk30UTg03HOj2HTg03Hok21;Tg007Ik61:Tg00Hgk119Tg02R5k50;Tg00=8k316Tg00<@k313Tg00=Ok30~Tg00=fk30}Tg00>>k30|Tg00?1k30{Tg00@Dm>0yTg00ZQj1UTg02SDk20sTg00PZk20oTg00SWk30mj4tTg03IOk30lTg03J0k40ITg03JQk30JTg03K2j3|Tg029Yk10iTg009>k80rTg03K[k20tTg03L:k20uTg00d0k40vTg00@fm@0wTg03LYk80xTg02k:j4dTg03MTk20eTg03SPk40zTg00Gmj3uTg004Gj3cTg031Gk211Tg03OHk412Tg0344k409Tg03Ofk60aTg034_k70MTg035Ck814Tg03PJk30`Tg03Pmk317Tg01e^R0f0R1'>p=@f1R2g02C=R3/41'fp=ng006:R4f3R5f2R6P2P1I0;p=gg00K`R7P6P2P1Ctp=FAu721p>0LAc721p=Jg00KBR8?u71p=3Ac871p=21C21/C3p=51_01p=E1H21/l0p=I1162/11p=A1;21,16p=Mf7R9f6R:f5R;f4R<P5P6P2E:;01p=6A0762/`1p>0@P7P2P0P1Ctp=kAu872/D1p>01P;P<P5P6P2%K1E:p=7g00JBR=g00JbR>701p=91?10p=O11>1p=RAc872,C6/C3/<1p=\1D621_01'1p>08Ac872/C1/C3p=N21171p=mP7P6P2P1H12p=B20?71p=bP7P2g03=RP1H09p=sP7P2g03QVP1H09p=iP2g03<3S04g03<RR?P?g03=2S05P1J0ap>0GP<Q04P?P?Q05P5Q04P?P?Q05P6g03>9R@K0MP2P1L14p=Gg00[MRA/11p=hA0710p=QP:P;P<P5P6Ac721E:p=rA0621,`5p>0V1D;<1_05'11H62/l0'1/11p>0EAu756=072/`1p=Y1D9:1_0;'11H<5/l0'11<62/;1'1p=SAu762=071p=x11<51<62/;1'1p>06P7P6P2P1Ct9c75p=^1<62/;1p=P1H62/l0,15/11p=q1D:;1_0<'1/151<62/;1'1p>0TA0721p=VA0421p=p1=21,43,f69045p=X1=21,43p>031_01,12p>0QP8P7P2P1Ctp=8B0`721p=aP7P2g03R=P1H09p=eP2Q04P?P?Q05P1P@K0Mp=yP8P7P51=21,43,46Ctp=W1l10p>0>B17721p=[1C23/<1p=TAc872/C1p={A0821p=]1f219046p>0ng00ilS0620:87R@Q06%@6S071?0<P4P8g00jeRBP7g00k>RCH0RRDP8PBg00kWP7PCg00l5J1<RC20:47RBH0kRE-0:7RFQ00P7PEPFP1g01XJRG$0_RH,42S08PEP4PBPEP4PDPCPBH0WS09H0CS0:f9RIf8RJ/=2'nP1Cg5FEn2001103000120106108WDS0;PF^DFS0<%@1S0=PFP620LE1S0>&0qBRKP@PBPEP4PDPCPBH0jRLP91JE1S0?P=PK%39S0@f;RM#3'D%29S0A%2MRN'5RO#Ef:RP,IO3ARQ1<OP;M2&0DBROP@PBPEPLP9%KJS0BE:n0100000020000G680@2XFFX@7%K:RR,kES0CA0700P@PBPEPLP;PRE:S0DP=PK%3IS0E-01;%2;S0F%2IRR'5RS#E1ISJ3AS0G1<SJS0H;M0POQ0Dn0100000020000S0I50K1L70Q0GP=1L=1S0J%3:S0K%3PS0L'D%2:S0M%2PRS'5S0N#EQ0N/II3AS0O=0=1P=%3JS0Pf<RT#3S0Q'D%2JS0R%2TS0S'5RU#E1IUM3AS0T=0=1P@PBPEPLPIPPE7S0UP=PKf=RV#2RW,5RS0V/<TS0W/;0RR,12POQ0Un010000002000050K]6P2%9Q1<UMRU/}0%OU%@U1;U0S0X3jPRP=Q01f>RR#2RX,5SS0Y/<VRS#O%@SP@PBPEPLPTPVE7RYP=PK%R2S0ZPOPYn010000002000050KP2f?RZ=\NRS0[#OP=PK11>>RNPOPYn010000002000090KYQ021121#9%96R[%92R\'`[R]%91,`\1162#9R\[%95/`[\\20p21P2n2001000000120000000XQ=XP=R\P]^Q=^P=R]P1%3VS0\fAR[#3S0]%2[R^,5WRW408R_f@R`,IWRaP;O3%9_%9a'`Q02%3RS0^fBRb#3S0_%2bS0`,5XRX408S0a#91IX[S0b#9g00[mS0cP1%3`S0dfDRc#3Rd%2`S0e%2cRe'5Rf408S0f#9fERg#2,5^S0g/IcS0h#9P\P]P1fCR]fGR\#3S0i+01R^%2\Rh,N]Ri#ERjP6O3%9^%9j'`Q02fHRk#3S0j,Dd#9%2k,5e#E#9Q0cP1fFRe#3S0kfJRd#3S0l'DS0m#9fKRl#2Rm,5hS0n#ES0o#9Q021_21#91>62S0p[Rh1>211_62#9Rn[1>56\n20g21P2n2001000000120000000XE7X@7Ph^E7^@7P1P0fIRhfMRn#2S0q'NRoP2O3%@o%2dRpfNRq#2S0r'5RrPnP1PkH0f1<rnS0s#@p-0Rsg03;GRt$0dRu&0ctRv&0b7Rw%m2S0t9Bw27B2&0^7S0u&0]7RxPx20H70Ry%zGS0v#z#bRz's&0D?R{PxPx1izyP{20Gx5S0wDGDGQ05-0\xS0xP1P61L=>20[16#9dB0Z702H0YS0yb:b<b=X17W;Q0=%O2P5[[^17^;sP1Q0cfLRz#2R|fPR}#2S0z'5S0{fOR~'<P2P`O4b8b4b6b4W6WHP2P1O2n2001000000121000000b6b4WHW6P2P1O2n2001000000121000000b6b4+07W3P1O1Q0[#@P=PAP@PBPEPLPVPRE7S0[P=PKP1POQ0[n010000002000050KX2=1LKY11>AS0|&0X>EZW3P1O1n200210000000021100010000b?b2W6A0=QAP=PKQ0X#hPOP@PBPEPLPJ%KIS0XE:S0}n0100000020000,LKW6n0110000020100P1O1b6b2H0FQ0C-0LE#QPKP@PBPEPLP;PEQ0CFrQ0IH0VeQ00P7PEQ07PEP2P5PKP@PBPEPLPI1JE2P=PKQ0EQ0\Q0VQ0VPTQ0W/;5J0EPOQ0Un0100000020000G6CYPEP9P6O1RQ14<HS0UPKP@PBPEPLPP1JEQP=PKQ0LQ0^Q0YQ0YPVQ0U,;SJ0EPOP@PBPEPLPPPME7n0100000020000G6CY[[P1%@;PEAFE62RSP:PKP@PBPEPLPT1JESP=PKQ0QQ0dQ0SQ0e'5RSPSPZPSPZP:GSPOPYn0100000020000G6CYQ02AFE56RY=xE9PKP@PBPEPLPV1JEYP=PKP_PaPWP`P9I06POQ0[n0100000020000G6PEPMAFE<5O1RW14JHRaPKP@PBPEPLPR1JEWP=PKQ0aQ0bPXP[PaI06POP@PBPEPLPRPZE7n0100000020000G6CYP1AFE;<=xEIPKP@PBPEPLP`PEPEP:P;C^P=PKQ0fPfP]APf]PCqPOP@PBPEPLP`P[E7n0100000020000G6P7PMPKP@PBPEPLPbPEPEP1P9C^P=PKQ0_Q0k'DQ0`%2eRf'5Ra#E1Iag3ARX1<agRa;MTPOP@PBPEPLPbP]E7RWn0100000020000G6PEP`AFE2JO1R_14VHRYPKP@PBPEPLP]1JE_P=PK11^jPiPeAPieYCqPOP@PBPEPLP]PcE7n0100000020000G6CY]0XS7PKP@PBPEPLP[PEPEPMP:C^P=PKQ0]%3gQ0gQ0hQ0gPcPMK0TPOP@PBPEPLP[PbE7n0100000020000G614THRY/VYPKP@PBPEPLPbPEQ0:1=gT,neRiP9CgS0gP=PKAMXaYPOPWn0100000020000S0hG61L7Y20Sbi1pbi20Bbi+0A1=eV,n\-0B]P=Q03PcPkP\PRCXPKP@PBPEPLPePEQ0:1=h`,ndRiPMCgP=PKQ0m15fpRf#E1Ifh3AS0]1<fhS0`14`H3MPOP@PBPEPLPe%K\RfE:S0kn0100000020000G6P2PgPhPkPZCXS0_P4PiPKP@PBPEPLP1PEPEP[PTC^P=PK%31S0f%3lRW1N1mRaPaPdPaPdP[GSPOP@PBPEPLP1%KkS0bE:n0100000020000G6PKP@PBPEPLP2PEQ0:203lbRa,fzRXPVCgP=PK%32S0a%3zS0[1N2|RjPjPlPjPl14bHS0eGSPOP@PBPEPLP2%KhRjE:n0100000020000G6]0XI4PKP@PBPEPLPiPEPEP`PMC^S0SP=PK%3iQ0l1NipRpPpPhPpPhP`GSPOP@PBPEPLPiPfE:n0100000020000G6PKPOP=PK%3XQ0[1NX|RfPfPlPfPlQ0eGSPOP@PBPEPLPXPjE:n010000002000090K1XTKP=P>P=PK14|aRa/5|S0l-0Q1Q0lPlQ0lQ0e7PlCqPOP@PBPEPLQ0[/8aPjE:S0dn010000002000090KOX2=PuPv%m<?B6w%m57B2Q0u20?7GRj&02GS0Q#bRa5o7Q0v#bS0UQ0Q$02S0Y#bRXAo7aj'a'aQ0U5w7=w7X'e,yxQ0xQ0yb:b<b=X17X57XB7XC71=121=21S0^,45,46/C6/C5'V^17^57^B7^C7P1P3P|PlPbO4b81=[d203d[S0L,4mS0W/5m'VP71=blR|P=PK%E1#RP1Pz14]HRf9P1zCqPOP@PBPEPL%3nS0VQ0qPzP]CW%KdS0\E:Rpn010000002000090KOXJ7P7P0P=PK1=]zR^#ER_#RRS&0>1P^PzPfI06POPpn010000002000090KOXJ7P7PbP=PK1l00S0E1;1f5ASPOPpn010000002000090KOXJ7P=P>P=PK1;]f9AS1POPpn010000002000090KOX2=20=0|%@|%O|%E|S0I3jP_P=Q011=cnR_#@%O_P=PK14eHR_,;eRp9A2>POP@PBPEPL%3}Q0zP~PeCWPnE7n010000002000090KOP21=gqS0~#@1}e_1?e_1>_e;jp14\H,;\S10P=Q0114kHRp,?k1>pkP=PK11N2S11POP@PBPEPLfTRp#3%2pS12fSR_PdCWfQRSE7Rfn010000002000090KOP214hHS13,?hP=PK11N>R^POPfn0100000020000,LKW4P1O1Q13/>hPuPvQ0t?B2w?B2wQ0uPxPx20H7HS14,aXS15/sXP{Q0wDGQ0xQ0yb:b<b=X17X;s141HS0w/>1P6[^17^;sP1P=PK11NAS16POP@PBPEPLfURf#3%2fS17PpPlCWfRRQE7n010000002000090KOPlP2O3b8W4P1O1n200210000000021000010000b?b2W3P1O1Q0~#O2047HS0~-0P7g02B^S18#~S19#~S1:,v7S1;60<7Q18,v7S18Q19,v7S1960<7Q19'['[g03RdS1<+00>05tuPv%m6S1=?B2wS1>?B6wQ0uPxPxAo7Xa/iyP{PxPx1syXP{PxPx1iyaP{20Gx<S1?DGDGDGQ0xQ0yb:b<b=X17X57X;sQ0^#OQ071?06P;[[[^17^57^;sP1P=PKQ109AA>POP@PBPEPL%3S%2SS10P}P\CWPqE7n010000002000090KOP\P}P2P[PlO6b8W3P1O1n200210000000021100011000b?b2P=PKQ0I#RQ0e,;b7A>POQ0dn010000002000090KOeQ0E&0O0EZ1<|lPuPvQ0tQ0uPxPx1iyjP{PxQ04P?P?Q051ejy,yxJ0NDGQ0xQ0yb:b<b=X17S051?01%Q2Q0c[[^17S04P1PzP\O2b8:0UblEZ1H|l21;blEZQ0lP1J1:b31DWW&19WEZP=PKQ0W,8WR|#3PW1N|mR?P?PdP?Pd14[HR?GSPOP@PBPEPLP|Q0bE:n010000002000090KOeP=PKQ0L,flR|#3PW1N|mS0LQ0LPdQ0LPdP?GSPOP@PBPEPLP|Q0bE:n010000002000090KOeP@PBPEPLP|P@PEP@PBPEQ09H0CS09P|PTI0;E:P@B184DCS0LB164DCS0WB154DCS0lB134DCS0EB104DCS0dB0~4DCS0eB0}4DCS0IB0|4DCS07g00lSS0^Q0^>0{4CS1@PBPTP|N>0yEZW0PeP1P<K0KWAP1O1Q0_#UPKP@PBPEPLPePME:P=PKQ0i/DWRWQ0o'1Q0nPdQ0n?Pd?CqPOP@PBPEPLP\Q0bE:n010000002000090K1XTKR?PKP=PKQ0]Q0`;M`POQ0kn0100000020000P?Q0mP=Q0JA0=W1P=Q0V-01h=0=1PKP@PBPEPLPdPEPEPcPZC^P=PK%ErRW,121IrnS0VQ0s/;cS0J3APOP@PBPEPLPdPlE7R?n0100000020000G6P=PK%2~R|,5mRm#ES0m1Imq5A6RC1<mqRm;MgPOP@PBPEPLPlPzE7RDn0100000020000P=PK14gH9MCmPOPDn010000002000050K]0]7P2Q0jQ0['DS0[#9P@PBPEPLPhPEAFE]RFrS0jP=PK%EoS0k#R1IozS0`APoz]S0]3APOP@PBPEPLPhQ0\E:S0\n010000002000050K20=0r%@r%Or;jWQ0mP=Q01Q0{#@Q0{#OP@PBPEPLPqPEAFEk]FrS0{P=PKQ0ZQ0r%2QS0m'5Rr/ISS0rAPrSkS0b3APOP@PBPEPLPqP~E7S0Zn010000002000050KP=PK%2_Rr,5|R|/HQRz$0>Ro,16RD1<|QR|/;hS0n'1POP@PBPEPLP~P}E7Rmn0100000020000P=PKQ13,;|S13,1DPOPmn010000002000050K]0P2Q0qQ10'5S0q#@Q0{P=PKQ0rQ0b5ANPOQ0Zn010000002000050K20sz0%Qz00AoQ0zQ12'5/I_P=Q03Q10Q17'5/Hp#QP@PBPEPLP_PEAFEnkFrS10P=PKQ11fWRk#2S03,5rfVRr;PnRz'1POP@PBPEPLP_PpE7S11n010000002000050KP=PKQ12fXRN;\kRk/;qRD,16POP@PBPEPLPpPfE7R|n0100000020000P=PK14qH,;kRC,16POP|n010000002000050K]0P2Q0m%2rS12'5/Hf#QS0mQ10P=PK11^zPOQ11n010000002000050K1}kq1?kq1>qk;jDQ17fYRk#2S0z'5?PN~P=Q01Q12fZR~#2S17'C/TkRq/?}1>}qP@PBPEPLPNPEAFEQnFrRQP=PK11^2POP@PBPEPLPNPkE7S12n010000002000050KP=PKP6POP@PBPEPLPkP~E7S0on0100000020000P=PKQ0zf]Rnf\Rq3\R}14_HR_';S0zPOQ0on010000002000050K]0P2Q03f[S0o#2S0i'C/T~S03/?SP=PK11^>POQ12n010000002000090KQ1}}_S0_1?}_1>_}Q0z3jS0zQ17f^R_#2R}'514pH7PnS17P=Q01Q0if_Rp;\_R>14fHRf'?S0i1>f>S1AP=PKP2POP@PBPEPLPnP_E7Rnn0100000020000Rf90KOP2f`S1B#2,{q/TpR>14rHR~'?S1C1LKOW9P1O11>~>S1DPuPvQ0t?B6wQ1=?B6w?B6w7B6Q0uPxPxQ15Q0Y#z#bR~'sP{PxPx1i~XP{Q1?DGDGQ0xQ0yb:b<b=X17X57X;sQ0w/>21?62P<[[^17^57^;sP1P@PBPEPLP_PpE790KOfbRsfaR>5\}PNP2P:O5b8W9P1O1n200210000000021000011000b?b2W0W4P1O1Q03,>SP=PK11^AS03POQ12n010000002000090KQQ0_Q0zQ17P=Q01Q0iQ1AA0KnfP2Q1CA0KnOP\Q021D21#91]62[Rf1]211D62#9RQ[1]56\Q20o21P2n2001000000120000000XE8X@8Pf^E8^@8P1%3_Rf%3sRQPgO31]fQQ00P8P7Q0ffd#3']PKP@PBPEPLP2PEPEQ0oPrC^P=PKQ03POP@PBPEPLP2PsE7n0100000020000G6P6fffeS0oPqCX#U%25S0ffgRq#2'5#@%2<RrfhRQ#2'5/Hq#QQ0FfiRf;\Q,>pQ0MfjR^#2RS'C/TfQ1B/4H'?fkRN#3%2NR}P^P>CW,p9]9]4]A]3]>]0]7Pp1821#3%3q']PKP@PBPEPL1862R>PEPEP_PkC^P=PKQ03POP@PBPEPLP>Q0oE7n0100000020000G61856S0oPfPQPpCX#U18<5RQ#2S03/5S#@18;<#2S1B/5}/H^#Q18:;#2S1AflR};\N,>s189:#2S0ifmS01;\}fcS17/4H'?Q00P8P7Q00P7PEPFP1Q08PEQ0:fqRS/=2,n5P1Cg5FEn2001103000120106108XDFQ0<18PIS0z#3Q0a']18MPP6fpS0aPqCX#U18TMQ0f'N#@18VTRq/NrfrS0f'H#Q18RVS0_Q0F'{fsS0F'T,>^18ZR#2RRQ0M'CftRV'T14NH'?18`ZRfQ0@Q0AfuR_P}CW'p]9]4]A]3]>]7bGfnR}Q00P7PEPFP1Q08PEQ0:1=V2,nQP1Cg5FEn2001103000120106108XDFQ0<%3q%3>']Q0_Q0oQ0FP^CX#UQ03,5R#@Q1B,Nf/H_#QQ0118[`Q1A'{fvR_'T'>18b[Q0i'{fwRf'T14}H'?P8PJPKP@PBPEPL181]R}PNP@PBPEPLP}PfE7G6182cQ0zfzR}003SRN40n#U186gPMPPf{RRQ0fCW'p]>]0XV8PKP@PBPEPL18JbR>P^P@PBPEPLP>P_E7G618I]18IJfyQ0aCX#UP7P4B0m87PR_P_Pc14INP4\7/L_PuPvQ1>Q0uPxPxQ14,aa,ijP{PxPx1sajP{1eja,yxDGDGQ0xQ0yb:b<b=X17X57Q08,?1Q0p1V65[[^17^57P1Q0f15gPRg/<RR_P5P<O4b81CcI/T}/VSQ05Q04P1f|PfO2b8:0lgR1=R_1HgR'4,VgQ1:#~,v7RgQ0vP7Q0~PG20470R0H0I60J7Q1;5|7Q19Q18'['['[Q1<+00&0iG-047RR=|7gQ0vP7PRPGP0H0I60J7Q1;5|7Q199|7RQ18'['['[Q1<+00>05tu605tPv%m:?B<w?B6w%m9?B;w?B5w7B2Q0uPxPxAw7jaQ0U5w7Ao7X~Q0Y$02#bRw'a'eP{PxPxQ0Q#z#bRv,e~P{PxPx1ewyP{Q0UAo7Xv'a,aa,ej,yxDGDGDGQ0xQ0yb:b<b=X17X57XB7XC7XL7XM7XN71C12/C61=5:/4;'V1V9;%Q91=:9,4;,4<,V5[[[^17^57^B7^C7^L7^M7^N7P115\TRxf}Rj'<1HxjPVPjP3PTP\P2P6P9O:b8b[bKL0rW>W0P]P;P`P<L0h18]b18J9R]#3%2]fxfoCW'peW9W4WAW3W>W7bGXd7Xe8P2P1O2n2001107010121101105P:P<P5P6P2P1O6W9W4WAW3W>W0W7Xf7XV8P2P1O2n2001107010121101105P1P:PhP[PTP9P6O7PpQ17PsPkCXeb7bKO1+07W9P1O1Q1D1LKnW9P1O1n200210000000021100010000b?b2W0W4P1O1n200210000001021100011000P6O1b?b2P=PK%RDPOP|n0100000020000P=PK%RCPOP|n010000002000050KeW0WAP1O1Q0m#UQ10P=PKQ16/1zPOQ11n010000002000050K1LK|P=PK%hDPOP|n0100000020000P=PK%hCPOP|n010000002000050KeW0WcP1O1n10210010401021110211101P6O1b2bFP=PK%RoR|Q0n'1POPmn0100000020000P=PKQ13,1|POPmn010000002000050KeW0W3P1O1Q0q#OQ0{P=PKQ0|Q0rQ0b3APOQ0Zn010000002000050K1LKmP=PK%hoRoQ0n'1POPmn0100000020000P=PKQ13,1oPOPmn010000002000050KeW0W3P1O1n200210000001021100011000P6O1b?b2P=PK%RWQ0V'1RmQ0J'1POP?n0100000020000P=PKQ0s14cH';Rc,1mPOP?n010000002000050KeW0W7Q0[=0=AQ0jP=PKQ0k#hQ0`Q0]3APOQ0\n010000002000050K1LK?P=PK%hWQ0V'1RWQ0J'1POP?n0100000020000P=PK11WcPOP?n010000002000050KeW0W7n0110001020101P1P:O2b7b2P@PBPEPLPeQ0SE:P<EZP@PBPEPLPeP@PEQ09PiPMI0;E:P@Q0LQ0WQ0lQ0EQ0dQ0eQ0IQ07Q0^Q1@PBPMPiPeA0@ieRiP@20td[-0u3,flRlP\P1H0vA0@\lQ0cP6P1O1+07b]W3%UieN@0wEZW>P1O1n10210010400021110211101b2bFH0FPEQ0g9FEYRiPYPKP@PBPEPLPb1JEiQ0hG6CYePEPZAFET9O1RTPYPKP@PBPEPLPb1JETQ0hG6CYeW0P9P2P1K0KW0W^P2P1O2n2001000010121000000W3W_XgEXS7P2P1O2n2001107010121105109XOFXb7P2P1L0xW`X@7Q0=P2PFP6Q0CCdPFQ0>PKP@PBPEPLP:Q0?P=PKQ0OQ0N/<IRT;M6POP@PBPEPLP:%K9RbE:RYn0100000020000G680@6bF[^@7P1P:P5O2PEP:PFP2%K;RZ,kECdRiP:PKP@PBPEPLP<1JEiP=PK%3<Q0PQ0R,5rRrPrP9PrP9P:GSPOP@PBPEPLP<PZE:n0100000020000G6CYQ02P9PFP6Q0CCdRZ=xE9PKP@PBPEPLP;1JEZP=PKQ0GQ0H;M9POQ0Dn0100000020000G6PKP@PBPEPLP:PJPFP51kEbCd,JEP=PKQ0O?MTJPOPYn0100000020000G6P1PIPFP<Q0B,kECd=xEIPKP@PBPEPLPJPPPFP;Q0X,kECd,JEP=PKQ0T?MUPPOQ0}n0100000020000G6P1WYWHP2P1O2n2001000000121000000bObZbGPKP@PBPEPLP6P<PFQ0;%K5RF,kECd,JE00e5#KP=PK%36Q0KQ0M,N6R=P=P;P=P;P<GSPOP@PBPEPLP6PFE:n0100000020000RFG6ePKP@PBPEPLP6P:P;P<P5H0z#KPFG6eWaW\XI@WWXR7XX7XU4P<P5P6P2P1O5WIWWXR7XX7XU4o"). Qed.

(* [comment removed for export] *)
Lemma slot_key_test p stride cnt s : 0 < stride ->
  ((fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? cnt)) = true
  <-> exists i, 0 <= i < cnt /\ s = aadd p (UNIT + stride * i).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h04__x1h14__x2h21Hh37__arithh44__ffh58__varmaph65__with71ih85lemmah94__x3h:2E1h;2E2h<2E3h=2E4h>4__p1h?4__x4h@1shA1zi001zhB2E0hC4__x5hD4__x6hE3cnthF4cstrhG5cstr0hH1pi011phI2srhJ6stridehK1BhL2HihM2HshN2pohO2prhP2sohQ1xi021xhR1yi031np&0p;2p;3p;6p;4p;1p;<p;8p;9p;;p;7g00UbR0k20UTg03>Yj27Tg00HJj2iTg01[aj2oTg00FSj2STg03HOj2KTg00F6j2lTg01\[j2ETg01]8j2hTg00LWR1j21Tg00L>R2j2JTg03TJR3j2XTg00M2k20GTg00M^j2eTg00N?k30;Tg00OhR4j6BTg00PZk207Tg00Q:k403Tg03@;k202Tg00R\j2~Tg03Tdj2|Tg03UDR5j1QTg006oj1rj3>Tg03Ubj2tTg03VCk30TTg00G1j2TTg03V`m<0STg03WEk40RTg03Wlj1sTg030gk10QTg01>\k10NTg031ek10MTg032Ck10LTg032nk20KTg033Qj2PTg01e9j1fTg03B]j3ZTg01T2j1qTg00`=k10FTg035gk20ETg036Ik20DTg0375k30CTg037Tk40@Tg01knj2;Tg03@[k40=Tg00S<j4OTg01\>j29Tg00SWk30:k40OTg01]Uj2@Tg03GJk608Tg03IOk306Tg029Yk105Tg03Cbk204Tg02A^j1jTg03Dlj2]Tg03K2j3kTg03F>j2\Tg03Fjj3^Tg03A<k101Tg03B:j3`Tg03PJj3UTg009>k800Tg005\j6[Tg03XOj4}Tg02:7j2mTg03EUk30>Tg03Ofk60?Tg03Gnj3{Tg03Hok20ATg007Ik60BTg00Gmj3zTg004Gj3cTg02lOj2pTg00T7l9yTg00O5k40HTg00Qam;0ITg031Gj2xTg03OHk40JTg0344j4gTg034_j7wTg035Cj8vTg03Pmj3uTg03Xik70PTg00KBR6g00K`R7f0R83zp=2Ac678p=0f1R9/;8g02C=R:';p=3g00JBR;g00JbR<7>8p=:g01e^R=/p8p=4f4R>f3R?f2R@1@98,9:'m3>p=A11@9/18p=8p-0RAP2g00U1f5RBP>P?P@P9P8M9yp=HPAP2P9P8H0Hp=NA>698p=6PAf6RCP2PBP1P4P>P?P@P9P8N;0Ip=_A>78=p=W1K98=>7=p==1p=8,19p=I1E@9/78p=<A>798p=G1x78p=RP7P@P9P8H0Jp=FP7P9g03=RP8Cgp=dP9g03<3R4g03<RRDPDg03=2REP8g03>9Fwp=?P?P4PDPDPEP@P9P8Gvp=CP7P9g03QVP8Cgp=a1;9:/E8p=Y1@98,9:p=LP6P7P9P8H0Op=5Ac679/;8/;:p=D19:8p>09P7P9g03R=P8Cgp=VAu798p=MAc679/;8p>0<1798,1@p=bP@P4PDPDPEP9P8K0Pp=n20U67RF17=@RG%29RH%2>RI'iRJ%09RK%0>RL'3RM,o=RN'SRO1KM?RP/l=RQ'SRR1EM?RS/h@RT'S#:%:RRU%:TRV'1'J%2@RW%2BRX'iRY%0@RZ%0BR['3R\,o=R]'SR^1K\>R_/l=R`'SRa1E\>Rb/h?Rc'S#:%:aRa%:cRc'1RdP8%48Re178>PFP?PCPBP8DA38X77Rf,X7RgPg20GAgRhEHW81eRT%:ORT%:QRR'1,JUPd%:^R^%:`R`'1Rd/1cRUPaPdP8PcPcg00VB:0;A2Ra/NcRiEBPgPgPhEHW81eOQ%:JRQ%:NRO'1,JTPU%:YRY%:]R]'1RU/1`RT/1cRjPdPTP^PUP8P`P`1Na`R^EBPcPcPiEBPgPgPhEHW81eJN16HIRN,JQPj16WXRW/1]Rj/1`RQ/1cRJPTPQPUPjPYPWP8P]P]1Na]EBP`P`P^EBPcPcPiEBPgPgPhEHW8207HI%4MRH,JOPJ%4\R\,1WRJ/1`RO/1cRYPQPOPjPJPA^KARjPAPAP2P2H03R2PW1NaWP]P\P8F_P`P`P^EBPcPcPiEBPgPgPhEHW8202=M%WPRM,JRPY%W_R_,1JRY/1cRRPOPYPjP2PJ1NaJP`P_P8F_PcPcPiEBPgPgPhEHW81~P=17S@RP,JVPR17b?Rb,1YRRPjP2PY1NaYPcPbP8F_PgPgPhEHW81|S@11NH?8MPRPPg[178?PFP@PBP>P8DA58eX77,X7RgPR[P1PYPb178BPFP>f7RbPCP8DA58eX77,X7P8%2bRY,6I%0bRR,3LRM#41=MC38P1f8RM#2RH,6X%0MRX,3[R['I1=[b%0CR[f9RN#0RS'3?<Mb178NPFPMf;Rhf:RcP8DA58eX77,X7[P8%2cRa,6Y%0cRY,3RRR'IR2P1%2h,6H%0hRH,3X#4f<RX#0Rj,3S/=hf=RS#0RV,3Y?<Xh178SRYPFPXf?Rif>R_P8DA58eX77,X7[[P8%2SR`,6a%0_Ra,3H#4%0i,3j/=_f@Rj#0,3V?<i_P7178jPFPifBRHfARJP8DA58eX77%0J,3aRO/EjR^%4^R\17^iR]'1PFP_PJPjP^DAR^P\P]POPj%2_RO%2JR]'6%QOR\%Q]RW'GRQP6P7%r6P5%r7%Q9%Q8'G16981t9840TXR6XQ6POP\1T7\P]PW1T7WN<0SP?H0RRWPQ%2HR]#sR\%Q]#4R5%2jRj#sRU%Qj#4Rjg03;GRT$0QRd&0NTRk%R@Rl%R?Rm7F9&0M7Rn&0L7Ro20K7=Rpg01XJRq,P7Rr%fqRs,P7Rt5Z7%qqRu,P7Rv5Z7Rw'd,?oRx&0FDRyPxCC20EoERxP8P@1T;<20D8@#:dB0C7=9H0@R<b4b5b6X07X17X971;89/;@R;#41;9@/;?#4[^07^17^97P8P:fERz#0R{%0HPCO4b3bGbFbBPWPQP\P5PUPjPdPk%R9RjPnPo1apr,?oRUPyPUCCPxP<b4b5b6X0717=8R517=9[^07P8fDR\PJO2b3bGbFbBH0=P8COP0P6P7%28RJ/6]fCR]#0,3K#4%0\,3Z/=]%0?RQ/3{?<\]fFR]#2%0]R\1;L\/Yz,Lz'9'59>F>]=]<];]:P_1598#2R{%2z'615@9#0Rz/3\#415?@#0R\fGRW#0'3/=]15>?#0RHfH#0'3?<W]P0P6P715CB#2/6J15bC/DK#415Mb/DZfKRZ'=15NMRK/DQfL;<Z15cNRZfMR0%0ZRZ/;L/Y0'L,9L,5I5>F]=]<];]:fI%2K/6{13Zz#415hc/D\fNR\'=15Xh/DHfO;<\P6PB158SfQRH1;SB/YH'L,9B,5C5>FXI6P7PFB0:67BRZPZPXfPRz13X>R{/Ez'@RK$09,9>PF\7/TZPdPkPjPnPoPUPyPoP4PDPDPE1Vrp,?oJ08CCPxP<b4b5b6X07RU%W9g00[m[\5^07R5P8PHP\O2b3:06{z1K{z,9K,G{&05q-047Rqg02B^R{#jRK#j,]7R\5k71]7KRK9k7q1]7{R{'M'Mg03RdRq'\1MK{,M\/\q=^Td5^TPk%R>RH%RC7F@%RB&017Rj7F?7F9PnPo%fs,P7RZ%qs,P75`7Rs%fu,P7Ru5U7,Vw,?oPyPo1Vup,?oPyAU7vs9U7t,Vr,?oCCCCPxP<b4b5b6X07X17X97X?7XC7XD71@?>/9B,G;%WC1@BC,9>,9?,G@[[^07^17^97^?7^C7^D7P813_CR;fRRs'K1E;sPsP:PCP_P9P?O8b3b2L00PSP?E[15SXRs15B>R;#2%0;R;20<s;/Yz,Lz'9'55>FeW=W<W;W:XN7XO6P9P8O2n2001101000121103100P?P@P9P8O4W=W<W;W:XP7XI6P9P8O2n2001101000121103100P?P@P9P8O4P^eCOC}W=W<W;W:P9P8O2n2001000000121000000W2P9P8O2n2001000000121000000W2P9P8O2n2001000000121000000X2PP3P7Pf%2?%2C'613Q[RQ'I1=QBA<QB>38P8178CPFPBPMPbP8DA58eP1%49?b9bPFPCPNPMP9DA1=RNA<RNM582P8%4??b?NPFPNPXPhP>DAPF1LXBRN,mSR216JO1D8aRJ'I1=JSA<JSX38X@FPdPkAFH@j?F9mPnA`7rtRmA`7tr9U7Z9U7v=Z7v=Z7Z'V,?oPxP<b4b5b6X07X17X97X?71@891@98,9?,9@/;@/;?'G^07^17^97^?7P8P:PaPSPCO4b31@BX19VNRN/3V'GP71@CSRB%2iRi/6iRi/1e1=8_A<8_S38XA7P7P=1@b_R:,IiRi%W8A<:_S38XA7P7PCA>7==R:=8iYXA716OORi%4BRY'1RZ/1:17CXPZP:PiPY1T6OB0>7\K1M\{'M/\q=^TdPkAFl9jRjPnPo1dpr,?oPoP4PDPDPEP>J0?R>5noPyPo1apt,?oPy1dpm,?oCCCCPxP<b4b5b6X07X17X>A11e@1@@?#4\G[^07^17^>AP817bSP_PbP?PhO5b3CO1T7=COPdPkPjPnPo1art,?oRt9no>PyPtCCPxP<b4b5b6X07X17X>AAb@89179@[^07^17^>AP8%4bPSPbP?O4b3CO1EBSPUP5P8P_PhO2b39{CSE[1KBS20ACSE[1LSC,9a/3aP8J0Bb215`NRN#2/6`1DNVRN'I1=NXA<NXh38e%22/6`1D2VR2'I1=2XA<2Xh38ePcP8E[W2WLP9P8O2n2001000000121000000W2X77P9P8O2n2001000000121102000X2gCOO2O2O2O2O2O2O2WMX@FXE7XJ7XHFP?P@P9P8O4X@FXE7XJ7WHo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma get_shadow_eq st rid : get_shadow st rid = default shadow0 (s_shadow st !! rid).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03ridh12stp;1p;4p;6p;5p;2g00a]j16Tg00Ebj45Tg00;gj40Tg015hj11Tg00gPj64Tg00gdj52Tg00G1j23Tg00ilR0g00KBR1g016aR2P2P2%62g03YMP1P2P1g00jeR3g00kWR4P2C5P1P3P4P2C0f0R2f1R4#1E4D2'3X01X10P4P2O2W0W1o"). Qed.
Lemma get_shadow_ext st st' rid : s_shadow st' = s_shadow st -> get_shadow st' rid = get_shadow st rid.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h03ridh12sth23st'h31Hh41gp;4p;1p;3p;2p;6p;5g00Ebj4;Tg015hj10Tg006oj32Tg00a]j15Tg00;gj4:Tg00G1j27Tg005\j66Tg02RIj24Tg00gPj68Tg00gdj59Tg00KBR0g016aR1f3R2f2R3f1R4f0R5E8p=3P1P1P4g03YMP5D9p=1g00ilR6P0g00jeR7g00kWR8P1C;R9%04%03R:32P9%02R;%51R<P9P0P7P8P1C:R8P3P5C3'1P9P8P3f4#0C3,1<521X49P9P8P4P;C3,1<,71P:P5E614341424521eW3X00X26X16P3P4P5O3X00X26W1o"). Qed.
Lemma get_shadow_upd_shadow rid f st rid' :
  get_shadow (upd_shadow rid f st) rid' = if (rid' =? rid)%N then f (get_shadow st rid) else get_shadow st rid'.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h04rid'h11fh21oh33ridh42sth51Hh63Heqh72NEh81bi001bh91ei011eh:1ri021ri031np;2p;3p;1p;4p;?p;6p;Ap;7p;5g02]2j2UTg006oj32Tg00HJj28Tg00W2R0j2>Tg00a]j1TTg00Ebj4Rj3NTg00;gj4Kj3ITg00<Xj4Bj3ATg00:<j4@Tg02RIj24Tg015hj15Tg00_9j1STg00_[j2QTg00G1j2:Tg00=8j3JTg00<@j3HTg00=Oj3CTg00=fj3DTg00>>j3ETg00?1j3FTg00AHl?GTg005\j66Tg00ZQj19Tg00d0j4?Tg00Z2j2=Tg00AjlALTg03ZEj2MTg01cHj3<Tg00g<j7OTg00gPj6PTg00gdj5;Tg00KBR1g016aR2f4R3f3R4f2R5f1R6f0R7FOp=7P1P2P4P5P6P7EPp=1P2P2P6g03YMP7D;p=0A2267p=3P2\2R8g00ilR91U74A21741874R:'>1863g00JBR;P0f5R09215%T2R<P1g00jeR=g00kWR>P2CRR?P1P=P>P2CKR@P3P?P1P2P?P1P=P>P2CBC@RAf7RBf6RC140BO1RD%50RED7RFC1RG'0P;P2P6PCP?P@PBPEC1,0<O1RHP?P@P3PEC1RI,0<RJn0100000020000'3P6A214CRKP1PBP?P@P7P?PAf8RLPB14CLO1%5CRCD7C1,0<PBP?P@PLPCC1,0<O1RM'3X01%S2RN1Q2D10<7RO/3MX2N1:2HP?P@PBPFC1P1AN1=>RFAJ1=>RHAI1=>RMAH1=>RPAA1=>RQAC1=>RRAD1=>RSAE1=>RTP=AF1=>R>P2PEPBPDM?GE6P3P7E6W9P7O1%9KPNPIP?P@P0PCC1,0<,3OX2N1:2JPGP1PFPHPMPPPQPRPSPTP=P>P2PEPBP3PDA21B3RBP1PLP0P7C?A210Lg00[mP5P7O1'=b6W5%9BeMALE6W7P7O1n10210010200021110110103b8b:P?P@P7P?PAP4P51464O1RA%56RBD7/M6#5C1,0<P;P2P:P5P?P@P4PBC1,0<O1P?P@P7PBC1,0<n0100000020000'3eA<456/47P;P2P:PA1467n0100000020000'3eX01X49X18X31P4P5P6P7O4X01W4W1X31o"). Qed.

(* [comment removed for export] *)
Lemma cell_read_wr8 p v st q :
  cell_read (get_shadow (wr8 p v st) (fst q)) (snd q) =
  if aptr_eqb q p then
    (let r := get_shadow st (fst p) in
     let hl := default [] (r_hav r !! (snd p / 16)) in
     let hp := r_havp r !! (snd p / 4096) in
     if stale_pg hp (Some (s_tick st)) || stale hl (snd p mod 16) (Some (s_tick st)) then Unknown (Z.land v 255) else Known (Z.land v 255))
  else cell_read (get_shadow st (fst q)) (snd q).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01Eh12E2h22NEh31ri001rh41bi011bh51qh61fh71ni021nh81oh91pi031ph:2sth;1vi041vh<3NE2h=1ei051eh>2hlh?2hph@2n0hA1shB1zi061zhC2z0i071ti081xi091yp%0p&0p;2p;4p;1p;3p;5p;?p;6p;Ap;7g00UbR0j2cTg00HJj2RTg00<Xk403j3{Tg00:<k400Tg01T2j1DTg01TWj1VTg01U5j2<Tg01<lj1;Tg02RIj21Tg01aWj17Tg01^2j1@Tg01_dj1=Tg01bOj3HTg00IIj2_Tg00Ebj4^k301Tg00;gj4]j3}Tg01\[j23Tg00_[j2JTg01>\j1jTg00a]j1iTg030gj1gTg03HOj2?Tg03[@j1ITg03\:j1LTg03]4j2OTg00]Bj2fTg00W2R1j2XTg00gdj5WTg03]nj3UTg00_9R2j1eTg00`=k102Tg00G1j2STg00=8j3~Tg00<@j3|Tg00=Oj3zTg00=fj3xTg00>>j3sTg00?1j3rTg00AHl?qTg005\j6MTg00Hgj1pTg00ZQj1FTg02]2j2oTg006oj3>Tg00SWj3\j2nj4`Tg008Cj6TTg007ej6[Tg00d0j4mTg00AjlAlTg01cHj3kTg03^dj4tTg02;Ij3uTg00Gmj3wTg004Gj3hTg00g<j7yTg01e9j1aTg00gPj6QTg03_jj2bTg03`cj2dTg00KBR3g00K`R4f0R53wp=2P4g00k>R6g00l5R7P5C^p=YAh345p=0P4P3f1R8P5C`p=BP4f5R9f4R:f3R;f2R<P8P5Fyp=C%a5#ap=KP4P6P7P5C]p=ZP4P:P;P<P8%@5EQp=9f6R=P9P:P;P<DW?U85p=4P4P3P9P:P;%=<EQ/b8/d5p=8g03a@R>1O<8;>5p=Ag006:R??>85p=:P4P3P;P<P8P5EQp=NP4P:P;P<P8P5EQp=51b<8/d5p=GA>>85p=PA>385p=EP3P4P8P5C`p=6P4P3P;P<P8%=5EQp=vg00ilR@1c34RAg016aRBg00JBRCPB%25RD%2;RE'R1c43RF%YFRGP4PFPGP4P6P7PFH03H00RH%0;g01XJRI#D#D#D#D#D#D#D#VRJ,<<%;8'B118ERK#7EC%@K%=K3H118DRLn0100000020000%08RMPCP>1_8:RNPCP>P4P6P7P3C^ROP4P6P7P3C]RP%0:RQ%KI#KRI#K#K#K#K#VRR'3%2:RS,1<RT%;<RU,J3RV%jFRWPW%iWRX%gFRYPW%YWRZ%ZWR[%VIRI,3QS00PTD91?QIPVF4E81<;JRV#I%LVn0100000020000%28RT,1</OMn01000000200005A5XAB1f5;1:5;1_5;S01'XPNPCP11:<9PCPBf7RN#2RM,RSR\PFPGPH%0NR]1<=JR^%;9R_'BR`119MRa#7RbECRc%@aRd%=aRa3HRe119SRfn0100000020000PCP>P8PCP>POPP13]RS02PaCN1J3_R_PWPWPXPYPWPZP[13]IRaPdD51?]IRdP_F43G%I^%L^n0100000020000R^1OfQn01000000200007AQP81:;=RfP?PNPCPBf8R_#2Rg,RDPFPGPH%0_Rh1<NJRi%;=Rj'B11=gRk#7EC%@kRl%=kRm3HRn11=Dn0100000020000%05RoPCP>POPP13hRRpPmCNRm1J3jRjPWPWPXPYPWPZP[13hIRqPlD5DWRl1?hIRr;Uj3G%Ii%Lin0100000020000Ri3AX5?PCg00JbPCPBP5PnPkn0100000020000?AhiX4C%eFRk1JF`P2PFP>P5P0P4P3P>P5PCP>POPPf;Rn#0Rj/3RRsf9Rt%2nRu'1Rv#=RwCN1J35RxPWPWPXPYPWPZP[13jIRy%@vRzD51?jIR{PxF43G%I8R|%L8R}n0100000020000n2001109000120104107PCP>&023R~AUlr~5Gmg01e^Rm#IRl%LmRmn0100000020000n10110800021010900/PiX8k1S>^PFPG%ZFRiP]PcD5P4B01467S03A~467S04A}467S05A|467S06A{467S07Az467S08Ax467S09As467S0:P6Ar467S0;PFPbP]P`M?qEMP2PFP>PFPGPiP]%7eD5P0P4P3P>P5PCP>POPPf:R`#0Rb/3RPFPGPHPb1<tJ%;_'B%2`R7,1_Rc#7EC%@c%=c3HRcPxPWPWPXPYPWPZP[13bIPcD91?bIPxF4E8P|P}n0100000020000n2001109000121104107PCP>POPPQ02PeP~PWPWPXPYPWPZP[PaPeD9PdP~F4E8PlPmn0100000020000n10110800021110901/P^eAAe]^e1RMM%pMEMP:P5EMW=P5O1%Ff1oSM1ESM/X\%29/RgPCP1%2=%2t'EPCPBP8PFPGPHPj1<`J%;t'BS02%7vRvECS0<?HzwR111tgR\n01000000200001O\hRS7AhP81EM7R7P3PuP2PFP>PFPGPi%0tRMPFPGPHf<Rf#0R^1<nJ%;`'B%2f,1`Re#7S0=ECD5P0P4P3P>P5PCP>POPP13^RR]f=Rdf?Ra#2'1RbPxPWPWPXPYPWPZP[13^IS0>PbD91?^IS0?PxF4E8P|P}n0100000020000n2001109000120104107R^PCP>POPP13MRS0@PeP~PWPWPXPYPWPZP[13MIS0APeD91?MIReP~F4E8PlPmn0100000020000Rbn10110800021010900P2PFP>PFPGPiPM11`5Rc#7D5P0P4P3P>P5PCP>POPPP]11d;R]PxPWPWPXPYPWPZP[Q0>P]D9Q0?PxF4E8P|P}n0100000020000n2001109000120104107PCP>POPPQ0@PcP~PWPWPXPYPWPZP[Q0APcD9PeP~F4E8PlPmn0100000020000n10110800021010900'PX73PkPFPGPiPhPvD5ReP2PFP>P5P^Pbn10110800021010900P2PFP>PFPGPiPMQ0=D5P^Pbn10110800021010900'PX8kP2PFP>PeP0P4P3P>P5PCP>POPPPsf>Re#2Rk,1fRb#=R^CNPWPWPXPYPWPZP[Py%@bRMD5P{PxF47GxP|P}n0100000020000n2001109000120104107PCP>POPPPpPwCNPWPWPXPYPWPZP[PqPzD5PrP~F47G~PlPmn0100000020000n10110800021010900,S>PFPGPiPhQ0<D5P4Q03Q04Q05Q06Q07Q08Q09Q0:P6Q0;PFPvPjPhQ02A>4jhRjP9P0P3P41:5d#F1ETk%0a%0<Ra5>4f@Rk,:;]1]0]2Pt1685Rv/:k#F16<8#2RkfA#2'EfB#016;<#0R65>4P0P3P4169:/:5#F16=9#2/ET16N=#09>4a16_NRN/:;]1]0]2fC1:Nv#F16t_#2/Ek16`t#09>46PA16n`R616:`16:;RtPA\4RkPAP5PnO1X6kA\34nR_A\34:RNPkP_P_PNPk\3R_PkP5PfO1X6_1n34RvPv1S_vETP3PkPvPnP:P8ETE[ETP4PAPNP`P;P4P;P`P5CmETE[1:6teW1W0W2XC4X@3P8P5O2n2001103000120102106P<P8P5O3W1W0W2XB4X73P8P5O2n2001103000121102106P9P8P5O3O1W1%FjeMAlEMPgP5EMP2PFP>PFPGPiPh%71D5P0P4P3P>P5PCP>POPPPsPFPGPH%0e1<dJ%;f'B%7bEC?HM^RMPxPWPWPXPYPWPZP[PyPMD9P{PxF4E8P|P}n0100000020000n2001109000121104107PCP>POPPPpP1P~PWPWPXPYPWPZP[PqP1D9PrP~F4E8PlPmn0100000020000n10110800021110901P2PFP>PFPGPiPh%7\D5P0P4P3P>P5PCP>POPPPs11fuRfPxPWPWPXPYPWPZP[PyPfD9P{PxF4E8P|P}n0100000020000n2001109000120104107PCP>POPPPpP\P~PWPWPXPYPWPZP[PqP\D9PrP~F4E8PlPmn0100000020000n10110800021010900'PeAA1hSeW0P5O1%F71S>SW<P5O1n10210110000021110510102b4b3W2P5O1n10210110001021110511102b4b3PFPGPHPQ1BVU%75EC%@5RV%=53HX3BRU=kE8/1DPEPUP8PDCtEMAu;<8/1DPCP>Q01PKPBPWPWPXPYPWPZP[Q00PVD5DWPWPOPP%09/3RP8Cv%e3PCP>%;:,J3R3%0=/?I=U835G51<9JRJ#I%LJn0100000020000b?b>b31OLon01000000200007AoeX5AX:@X;4X9?P;P<P8P5O4W5W:X;4X9?o"). Qed.

(* [comment removed for export] *)
Definition sh_ticks (r : shadow) (t : N) : Prop :=
  (forall u hl ch, r_hav r !! u = Some hl -> In ch hl -> (snd ch <= t)%N)
  /\ (forall pg t', r_havp r !! pg = Some t' -> (t' <= t)%N).

Lemma not_stale_cur r t b : sh_ticks r t ->
  forall u pg, stale_pg (r_havp r !! pg) (Some t) || stale (default [] (r_hav r !! u)) b (Some t) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01Hh11Eh21xi001xh32chh42Hbh53Hinh61bh72b1h82b2h92pgh:1uh;2hlh<2t'h=1yh>4__p1h?4__x1h@4__x2hA1mhB1ni011nhC1oi021ohD1rhE1thF1AhG2H0hH3Hb0hI2HhhJ2HphK2_HhL7__arithhM4__ffhN8__varmaphO5__withP1chQ4cstrhR5cstr0hS1hhT5lemmai031li041pi051zp&0p;2p;1p;4p;3p;5p;8p;:p;6p;<p;7g03b:k203Tg00UbR0k202Tg01>\j1STg00_9R1j1NTg00Ebj4]Tg00;gj4ZTg01^2j1UTg00_[j2KTg006oj33Tg03c3j3GTg03cJR2j2=Tg03_jj2BTg00a]j1rTg030gj1XTg00gdj5@Tg03]nj3VTg03`cj2ETg00LWR3j25Tg03cfj2eTg00G1j29Tg03dGj24Tg03ddj2aTg00`=j1HTg00ZQR4j1FTg03eDj1`Tg01]8j26Tg00FSj27Tg03ejj3MTg03TJR5j2ITg00L>R6j2_Tg00Q:j4LTg001?j4^Tg03fFk201Tg03:8R7k200Tg03g3j4~Tg03gUj8{Tg03hHl:zTg03i7j3xTg00M^j2wTg03iZR8j2ATg03j6j2qTg03UDR9j1:Tg02lOR:j2CTg03WEj4OTg03>YR;j2WTg03Wlj1PTg031Gj2nTg03A<j1mTg03OHj4lTg031ej1iTg032Cj1jTg01e9j1kTg033Qj2TTg0344j4QTg03Ofj6hTg035gj2gTg036Ij2fTg0375j3sTg037Tj4tTg00Z2j2uTg00S<j4vTg00gPj6JTg004Gj3dTg01_dj1cTg00Gmj3yTg00SWj4bTg03V`l<\Tg034_j7|Tg035Cj8}Tg00K`R<f4R=f3R>f2R?f1R@f0RAEJp=[g00KBRB=d<Ap=?P<PBP>P?P@%cAEJp=;1KBAp=>g00JBRCg00[MRD73Ap=1P<P=P>P?P@%UAEJp=2g00JbRE93CAp=0Ay<BAp=Df6RFf5RGP=P>P?P@PAD@3Gp=<P<PBP@PACbp=8PBP<P2P9P:g03jVPGP=P>P?P@PAM<\p=pPBP<P8P9P;g03k6PGP=P>P?P@PAM<\p=oP@g03<3R;g03<RR9P9g03=2R8PAg03>9R:F|p=RP>P;P9P9P8P?P@PAG}p=Yg016aR2203?@P3202<BRH#SRI%NIRJPIP<g00k>RKg00l5RLPIC]RMP<PKPLPICZRNP?%UFROD[1KI@RP33AGH@?RQ%??RRf7RS'=[[^3H];^:<%NBRTP<PKPLPBC]RUP<PKPLPBCZRLP@PGC;%>ARK331=@G[^<B^9<PUPLPAPFC;%>GRV'BPIPI%rIRW%XHRXPIPMPNP@POD[D@?V=V'E#1^9<^:<PAPIPMPNP?f8RVD2=3JPf9RO,=R\Q[^3H^;I^:<PUPLP@PVC;=3TK1=@V[^<B^9<P31E@A#1%1?RQ%1@RR'5RY[%1ARZ,5R1E?@#1[R[1E>?#1\Y1e@APAn2001000000120000000X8CX7CP[^8C^7CPAPUPLP@f:R[C;RY%>OR\'BR]PIPIPWPXPIPMPNP?P[D2D@?VV\R\%1]%1\R\PYPT19TAPUPLP?f;RYC;=3TAP1PBPUPLP=f=R]C;=3TA%>],B@#1]1P@PUPLPGf>R^C;=3TKP314@ARK#11=@?R_[1=A@14?@R`#1[Ra14>?#1\_1a@APAn2001000000120000000X=BX2BPa^=B^2BPAf?RaP?POPSP?P@O3O3b0%>@%>^'B#1eW1X<BPAO1PUPLP>f<RLC;%HBRU53T19CD%>L,BU#1eW1n10110200021010100PAO1b1bCP3%0ARU#FPR[RR%0@RD#FRT\ZPQ\T%`AP@n2001000000120000000X6CPR^6CPA%DARR,6[%?ART,4Y'7RQX3HRZPIPIPWPXPIPMPNP>PYD2D@RO5MHR_%0_PIPIPWPXPIPMPNP=PLD2D@R_9GHARb16YR14LT'7RcX3HRdPAO1#0'5X2H,IH'_p-0RePe]FPePeP6P6CLP4g03kVPePeP6PePePeP7C^R7CLP:PePeP6P6201e6P6P7PeP6200A@X=eX2eg03lHC~G{AMHd_#0PHPAPIPIPWPXPIPMPNPGP]D2F<Rd16LR14]T'7X3HPAO1#0'5X2H,IHPAM:zWTAxHZO%0Q,5bX2H,IHRbP5PH%0c,5dX2Hg00[mRdPAP0P<PBPHPAPIPIPWPXPIPMPNPVf@R0D2F<16^R14aT'7#0'5Pd[PAPH18@ARTPIPIPWPXPIPMPNPYfCRaD2F<fARR%DT'6fBRc%?T'4'7#0'5P3PH18?@RTPIPIPWPXPIPMPNPLfDR5D2F<%DT,6c%?T,4a'7#0PdPAPH18=>PIPIPWPXPIPMPNP^fFR^D2F<fERT18G=RG#D'6%?G,4^'7#0P317@A#0%0?R^/5D[RG15DU17?@#0RD[%0>/5^\D1w@AP@n2001000000120000000X8CX7CPG^8C^7CPAfGRG/6SRDfHR^/4FRFP@O3%0D%0F'5P316^V#0fIRF/4S#0PdPAfJRS/6[#0fLRD/4[#0P3%0K1A?@[RK1A@A%0`R`[1A>?\`1q@AP@n2001000000120000000XABXBBPK^AB^BBPAfNRKPLP@O31AKLPIPMPNP^fPR^D2PJ19JAPIPMPNPFfQD2=3JAP1PIPIPMPNfKfSD2=3JAPH18cRPIPIPWPXP@F<Pd]5]1P@PIPMPNPDfTD21KIA53JPH18acPIPIPWPXPPF<P^PKP?185aRaP@PAO5%?afU'=fVRa,=5%:5RK%:aR^'CRPP5PK19<KPaP^19<^EpPACOPPfWRP/AT%:PR^%:TRa'WRKPPP^19<^PTPa19<aEoPVCOPKfXRK#Pg01e^RV%:K'C%PG%:G,CVg03;GRG#X%SGP<1n<?P@%m<Cl%i<%j<RGP<g01XJRK#k,T<Rag03QV1T<KRKCQ,RG%H9RTPGP<PKg03=RPaCQ,RGPTPGP;P9P9P8P=EhCYCY1gG8PAP?19CE1fA?#0dAs<V@CtbMbNbOX?<X@<X>e1W@A1C@?P=[[^?<^@<^>ePAPdf[#:%:FP>P=O5bLbRbQbHbGb0W5W1X;IPAO1PIPMPNPSfRD2%HIRS53JPH18R0PIPIPWPXPSF<1udAW5W1n10110200021110300PAPYO2b1bCb4b0W4WKP@PAO2n2001000000121000000b4b0W4W5P@PAO2n2001000000121000000W0XSBXP<P@PAO2n2001104000121105101X2HP@PAO2n2001000000121100000W0%FbeO2O2b0P\eCvO3b0X9<X:<WJWIP@PAO2n2001000000121000000W0X6<XEBXD2P?P@PAO3X6<XEBWDo"). Qed.

Lemma cell_read_wr8_same p v st : sh_ticks (get_shadow st (fst p)) (s_tick st) ->
  cell_read (get_shadow (wr8 p v st) (fst p)) (snd p) = Known (Z.land v 255).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h01bh12hlh22hph31ph41rh52sth61vh72HTh81cp;2p;1p;4p;6p;5p;3g00Ubj2ITg02RIj28Tg01<lj19Tg03b:j2XTg00IIj2WTg01>\j1VTg00a]j1QTg030gj1PTg00Ebj4GTg00;gj4FTg01TWj1ATg01\[j22Tg01^2j1JTg00gPj66Tg00gdj5CTg01_dj1HTg00_9j1UTg00_[j2BTg03_jj2?Tg03HOj2>Tg03]nj3:Tg03`cj2=Tg01T2j10Tg01U5j25Tg03[@j1<Tg03\:j14Tg03]4j2;Tg006oj37Tg00G1j2OTg03m>j6NTg005\j6DTg00Y4j1MTg02;Ij3RTg03n<j4LTg00Gmj3STg004Gj3TTg01e9j1KTg00KBR0g00K`R1f0R23Sp=EAT012p=3%K2#Kp=1P1P0f3R3f2R4f1R5P2E6p=@1I01R6g00ilR7%E4,82%92'Xg03a@R8g00JBR9P81W33R:%E3R;,85R<g016aR=1I10R>#VR?P?%Q?R@%P>R>P1P?P1g00k>RAg00l5RBP?CGRCP1PAPBP?CFRDf4RE#3RFg01XJRG#1#1RH#ARI'2%J2RJE6DCP?P1PAPBP0CGRKP1PAPBP0CFRBf5RA#3RL%1H#1#1#1#ARH'2%H5RMC@%U0RNP9P8%9E,B0RO,?2f6RP#3RQ/>I=:5O'=%0G#0#0#0#0#0#0#ARG,5ARO#<%4On0100000020000b2b1b4RO%33RR,;<n0100000020000153GRS#4RT9782X88P9g00JbP9P8P2%EE,84REP=P?P?P@P>P1P?PCPD12LIPJE6DCP?PKPB12QHPMC@PNP9P8%9A,B0RA,?2f7#3/>I=:5A'=15PGRP#<%4Pn0100000020000b2b1b41;EFn0100000020000=78TX09P9g00[MP9P8P2%<SPTn0100000020000=78TX09154G#4RG,O8PKPB12RHRH%H<C@%95RB,B0R0'?P?P?P@P>P1P?PCPD12RIRD%J<E6DC1>RIRI;:0'=P<PBPIP2PDPHENEDA78OGeP:%M3EDAR345/8;/;RP3P4P5P3CLEDW7X57X61X36P4P5P2O3W5X61W3o"). Qed.
Lemma cell_read_wr8_other p v st q : q <> p ->
  cell_read (get_shadow (wr8 p v st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "h02hlh12hph21ph31qh41rh52sth61vh72NEh81bh91cp;3p;1p;2p;4p;6p;5g006oj39Tg00ZQj1VTg00IIj2NTg02RIj23Tg00Ubj2TTg01>\j1RTg00a]j1MTg030gj1LTg00Ebj4<Tg00;gj4>Tg01TWj18Tg01\[j24Tg01^2j1UTg00gPj66Tg00gdj5GTg01_dj1STg00_9j1QTg01<lj1@Tg00_[j2BTg03_jj2?Tg03HOj2DTg03]nj3ETg03`cj2=Tg01T2j10Tg01U5j2:Tg03[@j1;Tg03\:j1CTg03]4j27Tg00G1j2KTg00oIj3JTg005\j6ATg02;Ij3ITg03n<j4OTg00Gmj3PTg004Gj3HTg01e9j1FTg00KBR0g00K`R1f0R23Pp=5AH012p=1%F2#Fp=2g006:R3g00ilR4f3R59932#Vg03a@R6g00JBR7P6f1R8f4R9'NR:f2R;%59'3g016aR<1T10R=#RR>P>%M>R?%L=R=P1P>P1g00k>R@g00l5RAP>C<RBP1P@PAP>C>RCf5RD#1g01XJRE#2#2RF#8RG'4%U2RHE6DGP>P1P0P1P@PAP0C<RIP1P@PAP0C>RAf6R@#1RJ%2F#2#2#2#8RF'4%S8RKE6%Q0RLP7P6%@D,B0RM,?2f7RN#1RO/DG=E8M'=%0E#0#0#0#0#0#0#8RE,:@RM#;%CMn0100000020000b1b0b4%58RM,3;%18RP'7RQn0100000020000%5;,35%1;'7RR9962X96P7g00[MP7P6P2%5D,35P<P>P>P?P=P1P>PBPC14JGPHE6DGP>P1P0PIPA14OFPKE6PLP7P6%@@,B0R0,?2f8#1/DG=E80'=1:NERE#;%CEn0100000020000b1b0b4PRn0100000020000=96RX871K6QP:AJ892EAAI95;/3M/7PP9P5P;P8COEAW7X33X54X61X23P5P;P8P2O4X33W5X61W2o"). Qed.

Lemma sh_ticks_wr8 p v st rid : sh_ticks (get_shadow st rid) (s_tick st) -> sh_ticks (get_shadow (wr8 p v st) rid) (s_tick st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Kit ()) [] "p'0h01Hh12chh22hlh32pgh43ridh52t'h61uh71ph81ri001rh92sth:1vh;2Hhh<2Hph=2NEh>1bi011bh?1ei021eh@1si031np;2p;1p;4p;3p;6p;7g02RIj20Tg01<lj12Tg03b:j26Tg00HJj2GTg00Ubj2WTg00<Xj4OTg00:<j4MTg01T2j17Tg01TWj1ITg01U5j2:Tg01aWj1=Tg01^2j14Tg01_dj15Tg01bOj3;Tg02]2j2VTg006oj33Tg00W2R0j2UTg01>\j1NTg00_9j1ETg00;gj4DTg00gPj6?Tg00_[j2CTg03c3j3LTg004Gj3BTg03cJj29Tg00Ebj4ATg00S<j4KTg005\j7Jj6HTg00ZQj1PTg01cHj3QTg03^dj4RTg02;Ij3STg00Gmj3TTg00SWj4YTg00g<j7XTg00KBR1g00K`R2f0R33Tp=1P2g00k>R4g00l5R5P3CAp=FAB123p=8P2P1f1R6P3CYp=>P2f5R7f4R8f3R9f2R:P6P3FXp=<P2P1P9P:P6P3E?p=@g006:R;g00ilR<1063%26'6g016aR=g00JBR>P=%18R?,G6R@1W21RA%FARBP2PAPBP2P4P5PACOCMRC%88g01XJ#7#7#7#7#7#7#7#IRD,:9%2:RE'>10:?RF#=E<%4F%5F3;10:6n0100000020000%29RF,63X@=1V6?A316?/U@%17,G:P>P0f6R0#19319P>P=P6PAPBPCf8R>#8f7R@/:D%20RG'>%1>RH,00RI#=E<%4I%5I3;1007n0100000020000/6GP6%1@9318R0P1PH10@3%2@'6PAPBPCf:R@#8f9RH/:D%2>RJ'>%1@,0>R>#=E<%4>%5>3;/6JRJ]0X4116IGg00LW%NARI%EIRGP2PI%FIR>P2P4P5PICDRKP:f<RL#1,0@#4E?1CI6RM33ALA6:RNAB21:RO%2L'9[[^1A]2^62%E1RPP2P4P5P1CARQP2P4P5P1CDR5P6f;#1,0H#5C@1C13RH33%2@,96[^51^32PJP3P2PIP>PKP:f>RJ#1,0LRL#4E?=3GM%2JR@,9O\N[^1A^2I^62PQP5P6%5LC@=3PHf=RL#2R4,96[^51^32P2PIP>PKP:PAPBPCf@RK#8f?R>/:D/>@%1K,0JRR#=E<%4R%5R3;#4E?=3GM%2K,9O\N[^1A^2I^62RIPQP5P6PAPBPC%8>1:JD/>4%1>,0LRL#=E<%4L%5L3;#5C@=3PH196@[^51^32R@P6PIeP3P@eCKW<W;P6P3O2n2001000000121000000W0P7P3P8FJW?P3O1%P0P8W=P3O1n10210110000021110210103b>b8PAPBPC%871:8D/>F%=3E<%43%533;X8=R==Q?:/06P?P=P:P6CREHAS89:/06/6EeW0X41X9<X:2X7;P9P:P6P3O4X41W9X:2W7o"). Qed.
