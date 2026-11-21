(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (54 recorded proofs replaced by written proofs (aptr_eqb_refl, aptr_eqb_eq, aptr_eqb_spec and 51 more)). *)
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
Proof. unfold aptr_eqb. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

Lemma aptr_eqb_eq (a b : aptr) : aptr_eqb a b = true <-> a = b.
Proof.
  unfold aptr_eqb. destruct a as [r o], b as [r' o']; cbn. rewrite Bool.andb_true_iff, N.eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity| intros H; inversion H; auto].
Qed.

Lemma aptr_eqb_spec (a b : aptr) : reflect (a = b) (aptr_eqb a b).
Proof.
  destruct (aptr_eqb a b) eqn:E; constructor.
  - apply aptr_eqb_eq. exact E.
  - intros ->. rewrite aptr_eqb_refl in E. discriminate.
Qed.

Lemma aptr_eqb_neq (a b : aptr) : a <> b -> aptr_eqb a b = false.
Proof. intros H. destruct (aptr_eqb_spec a b); [contradiction| reflexivity]. Qed.

Lemma optr_eqb_spec (a b : optr) : reflect (a = b) (optr_eqb a b).
Proof.
  destruct a as [a|], b as [b|]; cbn; try (constructor; congruence).
  destruct (aptr_eqb_spec a b); constructor; congruence.
Qed.

Lemma optr_eqb_refl (a : optr) : optr_eqb a a = true.
Proof. destruct (optr_eqb_spec a a); [reflexivity| contradiction]. Qed.

(* [comment removed for export] *)
Ltac case_ptr x y := destruct (aptr_eqb_spec x y) as [?EQp|?NEp]; [first [subst x | subst y | idtac]|].

#[export] Instance aptr_eq_dec : EqDecision aptr := _.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma get_meta_rec_put st m r x :
  get_meta_rec (put_meta m r st) x = if aptr_eqb x m then r else get_meta_rec st x.
Proof.
  unfold get_meta_rec, put_meta; cbn. destruct (aptr_eqb_spec x m) as [->|NE].
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma get_meta_rec_upd st m f x :
  get_meta_rec (upd_meta m f st) x = if aptr_eqb x m then f (get_meta_rec st m) else get_meta_rec st x.
Proof. unfold upd_meta. apply get_meta_rec_put. Qed.

Lemma get_meta_rec_put_same st m r : get_meta_rec (put_meta m r st) m = r.
Proof. rewrite get_meta_rec_put, aptr_eqb_refl. reflexivity. Qed.
Lemma get_meta_rec_put_other st m r x : x <> m -> get_meta_rec (put_meta m r st) x = get_meta_rec st x.
Proof. intros H. rewrite get_meta_rec_put, aptr_eqb_neq by exact H. reflexivity. Qed.
Lemma get_meta_rec_upd_same st m f : get_meta_rec (upd_meta m f st) m = f (get_meta_rec st m).
Proof. rewrite get_meta_rec_upd, aptr_eqb_refl. reflexivity. Qed.
Lemma get_meta_rec_upd_other st m f x : x <> m -> get_meta_rec (upd_meta m f st) x = get_meta_rec st x.
Proof. intros H. rewrite get_meta_rec_upd, aptr_eqb_neq by exact H. reflexivity. Qed.

Lemma s_metas_put_meta m r st : s_metas (put_meta m r st) = <[m := r]> (s_metas st).
Proof. reflexivity. Qed.
Lemma s_metas_upd_meta m f st : s_metas (upd_meta m f st) = <[m := f (get_meta_rec st m)]> (s_metas st).
Proof. reflexivity. Qed.

Lemma lookup_metas_put st m r x :
  s_metas (put_meta m r st) !! x = if aptr_eqb x m then Some r else s_metas st !! x.
Proof.
  cbn. destruct (aptr_eqb_spec x m) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma lookup_metas_upd st m f x :
  s_metas (upd_meta m f st) !! x = if aptr_eqb x m then Some (f (get_meta_rec st m)) else s_metas st !! x.
Proof. unfold upd_meta. apply lookup_metas_put. Qed.

(* [comment removed for export] *)
Lemma get_meta_rec_ext st st' x : s_metas st' = s_metas st -> get_meta_rec st' x = get_meta_rec st x.
Proof. intros H. unfold get_meta_rec. rewrite H. reflexivity. Qed.

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
Proof. repeat split; reflexivity. Qed.

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
  Proof. revert i st; induction cnt; intros; cbn [zero_hdrs]; [reflexivity|]. rewrite IHcnt. reflexivity. Qed.

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
  Proof. unfold enframe_at. destruct (negb (off =? 0)); cbn -[set_size wr8 wr16 Z.add Z.sub Z.mul Z.div get_stride];
    unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.

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
  Proof. unfold nest_layout. destruct (enframe_at st g idx _ 0) as [st1 p] eqn:E.
    rewrite s_tick_zero_hdrs. cbn. pose proof (s_tick_enframe_at st g idx (UNIT * size_class j - IB) 0) as H. rewrite E in H. exact H. Qed.
End LAYOUT_FIELDS.
#[export] Hint Rewrite s_ctx_zero_hdrs s_regions_zero_hdrs s_next_rid_zero_hdrs s_metas_zero_hdrs s_areas_zero_hdrs s_groups_zero_hdrs s_slots_zero_hdrs s_secret_zero_hdrs s_reserved_zero_hdrs s_atop_zero_hdrs s_tick_zero_hdrs
  s_ctx_enframe_at s_regions_enframe_at s_next_rid_enframe_at s_metas_enframe_at s_areas_enframe_at s_groups_enframe_at s_slots_enframe_at s_secret_enframe_at s_reserved_enframe_at s_atop_enframe_at s_tick_enframe_at
  s_ctx_nest_layout s_regions_nest_layout s_next_rid_nest_layout s_metas_nest_layout s_areas_nest_layout s_groups_nest_layout s_slots_nest_layout s_secret_nest_layout s_reserved_nest_layout s_atop_nest_layout s_tick_nest_layout : mst.

(* [comment removed for export] *)
Lemma s_regions_new_region k b l st : s_regions (fst (new_region k b l st)) = <[s_next_rid st := mkRegion k b l]> (s_regions st).
Proof. reflexivity. Qed.
Lemma s_next_rid_new_region k b l st : s_next_rid (fst (new_region k b l st)) = N.succ (s_next_rid st).
Proof. reflexivity. Qed.
Lemma snd_new_region k b l st : snd (new_region k b l st) = s_next_rid st.
Proof. reflexivity. Qed.
Lemma s_regions_drop_region rid st : s_regions (drop_region rid st) = delete rid (s_regions st).
Proof. reflexivity. Qed.
Lemma s_shadow_drop_region rid st : s_shadow (drop_region rid st) = delete rid (s_shadow st).
Proof. reflexivity. Qed.
Lemma s_groups_put_group g mo ai st : s_groups (put_group g mo ai st) = <[g := mkGhdr mo (Z.land ai 31)]> (s_groups st).
Proof. reflexivity. Qed.
Lemma s_groups_del_group g st : s_groups (del_group g st) = delete g (s_groups st).
Proof. reflexivity. Qed.
Lemma s_shadow_upd_shadow rid f st : s_shadow (upd_shadow rid f st) = <[rid := f (get_shadow st rid)]> (s_shadow st).
Proof. reflexivity. Qed.
#[export] Hint Rewrite s_regions_new_region s_next_rid_new_region snd_new_region s_regions_drop_region s_shadow_drop_region
  s_groups_put_group s_groups_del_group s_shadow_upd_shadow : mst.

(* [comment removed for export] *)
Lemma active_set_active st sc v sc' : active (set_active sc v st) sc' = if sc' =? sc then v else active st sc'.
Proof.
  unfold active, set_active, ctx; cbn. destruct (Z.eqb_spec sc' sc) as [->|NE].
  - destruct v; [rewrite lookup_insert_eq| rewrite lookup_delete_eq]; reflexivity.
  - destruct v; [rewrite lookup_insert_ne by congruence| rewrite lookup_delete_ne by congruence]; reflexivity.
Qed.
Lemma usage_set_usage st sc v sc' : usage (set_usage sc v st) sc' = if sc' =? sc then v else usage st sc'.
Proof.
  unfold usage, set_usage, ctx; cbn. destruct (Z.eqb_spec sc' sc) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma bounces_set_bounce st i v i' : bounces (set_bounce i v st) i' = if i' =? i then v else bounces st i'.
Proof.
  unfold bounces, set_bounce, ctx; cbn. destruct (Z.eqb_spec i' i) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma get_head_set_head st h v : get_head (set_head h v st) h = v.
Proof. destruct h; cbn; [rewrite active_set_active, Z.eqb_refl|]; reflexivity. Qed.
Lemma get_head_set_head_other st h h' v : h' <> h -> get_head (set_head h v st) h' = get_head st h'.
Proof.
  intros NE. destruct h as [sc|], h' as [sc'|]; cbn; try reflexivity; try congruence.
  rewrite active_set_active. destruct (Z.eqb_spec sc' sc); [congruence| reflexivity].
Qed.
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
  rewrite s_regions_new_region. destruct (N.eqb_spec rid (s_next_rid st)) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma lookup_drop_region rid st rid' :
  s_regions (drop_region rid st) !! rid' = if (rid' =? rid)%N then None else s_regions st !! rid'.
Proof.
  rewrite s_regions_drop_region. destruct (N.eqb_spec rid' rid) as [->|NE];
  [rewrite lookup_delete_eq| rewrite lookup_delete_ne by congruence]; reflexivity.
Qed.
Lemma lookup_upd_region rid f st rid' :
  s_regions (upd_region rid f st) !! rid' =
  if (rid' =? rid)%N then option_map f (s_regions st !! rid) else s_regions st !! rid'.
Proof.
  unfold upd_region, get_region. destruct (s_regions st !! rid) as [r|] eqn:E; cbn.
  - destruct (N.eqb_spec rid' rid) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; [reflexivity|reflexivity].
  - destruct (N.eqb_spec rid' rid) as [->|NE]; [rewrite E|]; reflexivity.
Qed.
Lemma conc_eq st p r : s_regions st !! (fst p) = Some r -> conc st p = r_base r + snd p.
Proof. intros H. unfold conc, get_region. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lookup_put_group g mo ai st b :
  s_groups (put_group g mo ai st) !! b = if aptr_eqb b g then Some (mkGhdr mo (Z.land ai 31)) else s_groups st !! b.
Proof.
  rewrite s_groups_put_group. destruct (aptr_eqb_spec b g) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma lookup_del_group g st b :
  s_groups (del_group g st) !! b = if aptr_eqb b g then None else s_groups st !! b.
Proof.
  rewrite s_groups_del_group. destruct (aptr_eqb_spec b g) as [->|NE];
  [rewrite lookup_delete_eq| rewrite lookup_delete_ne by congruence]; reflexivity.
Qed.
Lemma lookup_set_group_active_idx g ai st b :
  s_groups (set_group_active_idx g ai st) !! b =
  if aptr_eqb b g then option_map (fun h => mkGhdr (g_meta h) (Z.land ai 31)) (s_groups st !! g) else s_groups st !! b.
Proof.
  unfold set_group_active_idx, get_group. destruct (s_groups st !! g) as [h|] eqn:E; cbn.
  - destruct (aptr_eqb_spec b g) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
  - destruct (aptr_eqb_spec b g) as [->|NE]; [rewrite E|]; reflexivity.
Qed.
Lemma group_active_idx_eq st g m ai : s_groups st !! g = Some (mkGhdr m ai) -> group_active_idx st g = Z.land ai 31.
Proof. intros H. unfold group_active_idx, get_group. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_iter_ind {A} (f : A -> A) (P : Z -> A -> Prop) x :
  P 0 x -> (forall n a, 0 <= n -> P n a -> P (n + 1) (f a)) -> forall n, 0 <= n -> P n (Z.iter n f x).
Proof.
  intros H0 HS n Hn. rewrite iter_nat_of_Z by exact Hn.
  rewrite <- (Z2Nat.id n) at 1 by exact Hn. rewrite <- Zabs2Nat.abs_nat_nonneg by exact Hn.
  induction (Z.abs_nat n) as [|k IH]; [exact H0|].
  cbn [nat_rect]. rewrite Nat2Z.inj_succ, <- Z.add_1_r. apply HS; [lia| exact IH].
Qed.

(* [comment removed for export] *)
Lemma lookup_add_slots m p stride cnt st s : 0 <= cnt -> 0 < stride ->
  s_slots (add_slots m p stride cnt st) !! s =
  if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? cnt)
  then Some (m, (snd s - snd p - UNIT) / stride) else s_slots st !! s.
Proof.
  intros Hc Hs. unfold add_slots. cbn -[Z.iter Z.add Z.mul Z.sub Z.div Z.modulo Z.leb Z.ltb Z.eqb lookup insert].
  set (F := fun acc : Z * gmap aptr (aptr * Z) => let (i, tb) := acc in (i + 1, <[aadd p (UNIT + stride * i) := (m, i)]> tb)).
  assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (0, s_slots st) in fst r = n /\
            snd r !! s = if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? n)
                         then Some (m, (snd s - snd p - UNIT) / stride) else s_slots st !! s).
  { intros n Hn. apply (Z_iter_ind F (fun n r => fst r = n /\ snd r !! s = (if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? n) then Some (m, (snd s - snd p - UNIT) / stride) else s_slots st !! s))); [| |exact Hn].
    - cbn. split; [reflexivity|]. destruct ((fst s =? fst p)%N && _ && _) eqn:E; [|reflexivity].
      destruct (Z.ltb_spec ((snd s - snd p - UNIT) / stride) 0); [|rewrite Bool.andb_false_r; reflexivity].
      exfalso. apply Bool.andb_true_iff in E as [E _]. apply Bool.andb_true_iff in E as [_ E]. apply Z.leb_le in E.
      pose proof (Z.div_pos (snd s - snd p - UNIT) stride E Hs). lia.
    - intros k [i tb] Hk [Hi IH]. cbn in Hi; subst i. unfold F. cbn [fst snd]. split; [reflexivity|].
      destruct (aptr_eqb_spec s (aadd p (UNIT + stride * k))) as [->|NE].
      + rewrite lookup_insert_eq. unfold aadd; cbn [fst snd]. rewrite N.eqb_refl.
        replace (snd p + (UNIT + stride * k) - snd p - UNIT) with (k * stride) by lia.
        rewrite Z_mod_mult, Z.div_mul, Z.eqb_refl by lia. cbn.
        destruct (Z.leb_spec 0 (k * stride)); [|nia]. destruct (Z.ltb_spec k (k + 1)); [|lia]. reflexivity.
      + rewrite lookup_insert_ne by congruence. rewrite IH.
        destruct ((fst s =? fst p)%N) eqn:E1; cbn; [|reflexivity].
        destruct (Z.leb_spec 0 (snd s - snd p - UNIT)); cbn; [|reflexivity].
        destruct (Z.eqb_spec ((snd s - snd p - UNIT) mod stride) 0); cbn; [|reflexivity].
        destruct (Z.ltb_spec ((snd s - snd p - UNIT) / stride) k), (Z.ltb_spec ((snd s - snd p - UNIT) / stride) (k + 1)); try reflexivity; try lia.
        exfalso. apply NE. apply N.eqb_eq in E1. unfold aadd. destruct s as [sr so], p as [pr po]; cbn in *. subst sr. f_equal.
        assert ((so - po - UNIT) / stride = k) by lia.
        pose proof (Z.div_mod (so - po - UNIT) stride ltac:(lia)). lia. }
  destruct (GEN cnt Hc) as [_ G]. exact G.
Qed.

Lemma lookup_del_slots p stride cnt st s : 0 <= cnt -> 0 < stride ->
  s_slots (del_slots p stride cnt st) !! s =
  if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? cnt)
  then None else s_slots st !! s.
Proof.
  intros Hc Hs. unfold del_slots. cbn -[Z.iter Z.add Z.mul Z.sub Z.div Z.modulo Z.leb Z.ltb Z.eqb lookup delete].
  set (F := fun acc : Z * gmap aptr (aptr * Z) => let (i, tb) := acc in (i + 1, delete (aadd p (UNIT + stride * i)) tb)).
  assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (0, s_slots st) in fst r = n /\
            snd r !! s = if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? n)
                         then None else s_slots st !! s).
  { intros n Hn. apply (Z_iter_ind F (fun n r => fst r = n /\ snd r !! s = (if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? n) then None else s_slots st !! s))); [| |exact Hn].
    - cbn. split; [reflexivity|]. destruct ((fst s =? fst p)%N && _ && _) eqn:E; [|reflexivity].
      destruct (Z.ltb_spec ((snd s - snd p - UNIT) / stride) 0); [|rewrite Bool.andb_false_r; reflexivity].
      exfalso. apply Bool.andb_true_iff in E as [E _]. apply Bool.andb_true_iff in E as [_ E]. apply Z.leb_le in E.
      pose proof (Z.div_pos (snd s - snd p - UNIT) stride E Hs). lia.
    - intros k [i tb] Hk [Hi IH]. cbn in Hi; subst i. unfold F. cbn [fst snd]. split; [reflexivity|].
      destruct (aptr_eqb_spec s (aadd p (UNIT + stride * k))) as [->|NE].
      + rewrite lookup_delete_eq. unfold aadd; cbn [fst snd]. rewrite N.eqb_refl.
        replace (snd p + (UNIT + stride * k) - snd p - UNIT) with (k * stride) by lia.
        rewrite Z_mod_mult, Z.div_mul, Z.eqb_refl by lia. cbn.
        destruct (Z.leb_spec 0 (k * stride)); [|nia]. destruct (Z.ltb_spec k (k + 1)); [|lia]. reflexivity.
      + rewrite lookup_delete_ne by congruence. rewrite IH.
        destruct ((fst s =? fst p)%N) eqn:E1; cbn; [|reflexivity].
        destruct (Z.leb_spec 0 (snd s - snd p - UNIT)); cbn; [|reflexivity].
        destruct (Z.eqb_spec ((snd s - snd p - UNIT) mod stride) 0); cbn; [|reflexivity].
        destruct (Z.ltb_spec ((snd s - snd p - UNIT) / stride) k), (Z.ltb_spec ((snd s - snd p - UNIT) / stride) (k + 1)); try reflexivity; try lia.
        exfalso. apply NE. apply N.eqb_eq in E1. unfold aadd. destruct s as [sr so], p as [pr po]; cbn in *. subst sr. f_equal.
        assert ((so - po - UNIT) / stride = k) by lia.
        pose proof (Z.div_mod (so - po - UNIT) stride ltac:(lia)). lia. }
  destruct (GEN cnt Hc) as [_ G]. exact G.
Qed.

(* [comment removed for export] *)
Lemma slot_key_test p stride cnt s : 0 < stride ->
  ((fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? cnt)) = true
  <-> exists i, 0 <= i < cnt /\ s = aadd p (UNIT + stride * i).
Proof.
  intros Hs. rewrite !Bool.andb_true_iff, N.eqb_eq, Z.leb_le, Z.eqb_eq, Z.ltb_lt. split.
  - intros [[[E1 E2] E3] E4]. exists ((snd s - snd p - UNIT) / stride). split.
    + split; [apply Z.div_pos; lia| exact E4].
    + unfold aadd. destruct s as [sr so], p as [pr po]; cbn in *. subst sr. f_equal.
      pose proof (Z.div_mod (so - po - UNIT) stride ltac:(lia)). lia.
  - intros (i & Hi & ->). unfold aadd; cbn. replace (snd p + (UNIT + stride * i) - snd p - UNIT) with (i * stride) by lia.
    rewrite Z_mod_mult, Z.div_mul by lia. repeat split; auto; try lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma get_shadow_eq st rid : get_shadow st rid = default shadow0 (s_shadow st !! rid).
Proof. reflexivity. Qed.
Lemma get_shadow_ext st st' rid : s_shadow st' = s_shadow st -> get_shadow st' rid = get_shadow st rid.
Proof. intros H. unfold get_shadow. rewrite H. reflexivity. Qed.
Lemma get_shadow_upd_shadow rid f st rid' :
  get_shadow (upd_shadow rid f st) rid' = if (rid' =? rid)%N then f (get_shadow st rid) else get_shadow st rid'.
Proof.
  unfold get_shadow, upd_shadow; cbn. destruct (N.eqb_spec rid' rid) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.

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
  unfold wr8. rewrite get_shadow_upd_shadow. destruct (aptr_eqb_spec q p) as [->|NE].
  - rewrite N.eqb_refl. unfold cell_read; cbn. rewrite lookup_insert_eq. reflexivity.
  - destruct (N.eqb_spec (fst q) (fst p)) as [E|NE2]; [|reflexivity].
    unfold cell_read; cbn. rewrite E. rewrite lookup_insert_ne; [reflexivity|].
    intros E2. apply NE. destruct q, p; cbn in *; congruence.
Qed.

(* [comment removed for export] *)
Definition sh_ticks (r : shadow) (t : N) : Prop :=
  (forall u hl ch, r_hav r !! u = Some hl -> In ch hl -> (snd ch <= t)%N)
  /\ (forall pg t', r_havp r !! pg = Some t' -> (t' <= t)%N).

Lemma not_stale_cur r t b : sh_ticks r t ->
  forall u pg, stale_pg (r_havp r !! pg) (Some t) || stale (default [] (r_hav r !! u)) b (Some t) = false.
Proof.
  intros [Hh Hp] u pg. apply Bool.orb_false_iff. split.
  - destruct (r_havp r !! pg) as [t'|] eqn:E; cbn; [|reflexivity]. apply N.ltb_ge. eapply Hp; eauto.
  - unfold stale. apply Bool.not_true_iff_false. rewrite existsb_exists. intros ([c h] & Hin & Hb). cbn in Hb.
    apply Bool.andb_true_iff in Hb as [_ Hb]. apply N.ltb_lt in Hb.
    destruct (r_hav r !! u) as [hl|] eqn:E; cbn in Hin; [|contradiction].
    pose proof (Hh u hl (c, h) E Hin). cbn in H. lia.
Qed.

Lemma cell_read_wr8_same p v st : sh_ticks (get_shadow st (fst p)) (s_tick st) ->
  cell_read (get_shadow (wr8 p v st) (fst p)) (snd p) = Known (Z.land v 255).
Proof.
  intros HT. rewrite (cell_read_wr8 p v st p), aptr_eqb_refl. cbn zeta. rewrite (not_stale_cur _ _ _ HT). reflexivity.
Qed.
Lemma cell_read_wr8_other p v st q : q <> p ->
  cell_read (get_shadow (wr8 p v st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof. intros NE. rewrite cell_read_wr8, aptr_eqb_neq by exact NE. reflexivity. Qed.

Lemma sh_ticks_wr8 p v st rid : sh_ticks (get_shadow st rid) (s_tick st) -> sh_ticks (get_shadow (wr8 p v st) rid) (s_tick st).
Proof.
  intros H. unfold wr8. rewrite get_shadow_upd_shadow. destruct (N.eqb_spec rid (fst p)) as [->|NE]; [|exact H].
  destruct H as [Hh Hp]. split; cbn; eauto.
Qed.
