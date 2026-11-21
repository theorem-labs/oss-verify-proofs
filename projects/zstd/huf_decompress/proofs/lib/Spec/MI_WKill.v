(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (35 recorded proofs replaced by written proofs (zsum_perm, round_up_ge_k, gcnt_unfold and 32 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_WFree.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_WKill () := "C47Corelib7Program6Basics4flipC35stdpp4base6LookupI59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C35stdpp7tactics<f_equal_helpC47Corelib7Classes9MorphismsGrewrite_relation_eq_domI35stdpp8fin_maps6FinMap00C47Corelib7Classes9MorphismsKrespectful_per_obligation_1C35stdpp6option8Some_injC47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC35stdpp4base3InjC35stdpp8fin_maps:map_deleteC35stdpp8fin_maps;map_to_listC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC46Stdlib7Sorting;Permutation?Permutation_mapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC46Stdlib5Lists4List8map_consC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6DeleteC46Stdlib5Lists4List7map_extC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2IDC35stdpp4gmapBgmap_dep_ne_lookupC35stdpp4base5EmptyC35stdpp8fin_maps@lookup_delete_eqC35stdpp8fin_maps@lookup_delete_neC35stdpp8fin_mapsBlookup_delete_SomeC35stdpp8fin_mapsBmap_to_list_deleteC59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap8gmap_key00I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps@lookup_insert_neI47Corelib4Init9Datatypes4list00I46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec6MI_Inv4zsumC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z3addC46Stdlib7Sorting;Permutation?Permutation_indK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib5Lists4List:fold_rightK46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3oppK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z;land_nonnegK46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic2or02C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00c59OSSVerify5KrLib4Spec8MI_WKill5gtermC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI47Corelib4Init9Datatypes6option00C35stdpp4base6lookupK47Corelib4Init9Datatypes6option01C35stdpp4base6deleteC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gcntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib4Spec8MI_WKill9zsum_permC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill;gcnt_unfoldC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C35stdpp6option;from_optionI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9stride_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill7g_hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec7MI_Geom;hosts_gbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_InvBslot_start'_sstartC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill7gbase_pC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=set_usage_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9del_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9del_slotsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill7K_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill5K_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8frontierC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_liC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill5gslotC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6NArith6BinNat1N6eqb_eqC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05c59OSSVerify5KrLib4Spec8MI_WKill6slot_gC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N8eqb_reflK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv:Z_div_multC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2or01C59OSSVerify5KrLib4Spec6MI_Kit@lookup_del_slotsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega5Tauto4kind02c59OSSVerify5KrLib4Spec8MI_WKill:stride_posC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill2GOC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01K46Stdlib9micromega=RingMicromega3Op206I47Corelib4Init5Logic4True00c59OSSVerify5KrLib4Spec8MI_WKill7K_slotsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec6MI_Inv7is_partC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~I35stdpp4gmap8gmap_dep00C35stdpp9countable6encodeC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC56Stdlib6ZArith6BinInt1Z8lt_totalC59OSSVerify5KrLib4Spec7MI_Geom9sstart_ltC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00C46Stdlib5Lists4List2Inc59OSSVerify5KrLib4Spec8MI_WKill7none_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c59OSSVerify5KrLib4Spec8MI_WKill;g_slot_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill;gslot_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres1<slot_key_injC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_validC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill@other_slot_not_gC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffc59OSSVerify5KrLib4Spec8MI_WKill8K_groupsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill7hosts_KC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9hosts_injC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9hosts_funC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres49old_listsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List;lists_notinC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC59OSSVerify5KrLib4Spec7MI_Geom7sstart0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom;sstart_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom8hosts_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7g_alignC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6im_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9top_chainC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec7MI_Geom3anc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom:top_uniqueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom<anc_hostslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9anc_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom5childC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill;gcnt_deleteC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv;is_metakindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterC59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec4KInv9ld_brkregC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation@Permutation_reflc59OSSVerify5KrLib4Spec8MI_WKill:K_frontierC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationAPermutation_transc59OSSVerify5KrLib4Spec8MI_WKill3K_cC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_zombC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv6extras01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5g_topC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill@top_region_emptyC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_R01C1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5mslotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill6gcnt_KC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_symc59OSSVerify5KrLib4Spec8MI_WKill7K_usageC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_A01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_M01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill4K_MRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill<g_unlisted_KC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7il_linkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9hosts_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3dllC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00K59OSSVerify5KrLib4Spec6MI_Inv5inv_L01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill:K_get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext=dll_ext_metasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill6live_KC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_G01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill<g_slot_free'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill;entry_not_gC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill=K_slots_otherC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv8group_ok01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_S01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill<K_slots_someC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill=entry_g_gslotC1?~~~~~~~~~~~~~~~C35stdpp4base3injc59OSSVerify5KrLib4Spec8MI_WKill9slots_posC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indC59OSSVerify5KrLib4Spec6MI_Inv6g_nestC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_map_iffC59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7byte_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5knownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7unknownC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv6inv_SH01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minI59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill9K_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill7K_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7atop_hiC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill:K_next_ridC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill6K_atopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill:K_reservedC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill4K_cfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill8K_secretC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill;p_not_gslotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill8K_shadowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill6K_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8ir_shapeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill=round_up_ge_kC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WKill:dec_hdr_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dec_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib4Spec6MI_Inv=ia_usage_keysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_scC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C59OSSVerify5KrLib4Spec6Malloc9set_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit?usage_set_usageC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6mstate01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4mctx01C1?~~~~~~~~~~~~~~~C35stdpp4base6insertI59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zsum_perm l l' : Permutation l l' -> zsum l = zsum l'.
Proof. induction 1; unfold zsum in *; cbn in *; lia. Qed.

Lemma round_up_ge_k x : x <= round_up_pg x.
Proof. unfold round_up_pg. pose proof (proj2 (Z.land_nonneg (-x) (PGSZ - 1)) ltac:(right; unfold PGSZ; lia)). lia. Qed.

Definition gterm (st : mstate) (sc : Z) (bh : aptr * ghdr) : Z :=
  match g_meta (snd bh) with
  | Some m => if m_sizeclass (MR st m) =? sc then cnt_of (MR st m) else 0
  | None => 0
  end.
Lemma gcnt_unfold st sc : gcnt st sc = zsum (map (gterm st sc) (map_to_list (s_groups st))).
Proof. reflexivity. Qed.

Lemma gcnt_delete st st' p h sc :
  s_groups st !! p = Some h -> s_groups st' = delete p (s_groups st) -> s_metas st' = s_metas st ->
  gcnt st sc = gterm st sc (p, h) + gcnt st' sc.
Proof.
  intros Hp HG HM. rewrite !gcnt_unfold, HG.
  rewrite <- (zsum_perm _ _ (Permutation_map (gterm st sc) (map_to_list_delete (s_groups st) p h Hp))). cbn. f_equal.
  f_equal. apply map_ext. intros [b hb]. unfold gterm. cbn. unfold MR, get_meta_rec. rewrite HM. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section KILL.
Variables (X : extras) (st st1 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g p : aptr) (ai i : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! p = Some (mkGhdr (Some g) ai).
Hypothesis HF : x_fresh X = Some g.
Hypothesis NL : m_next (MR st g) = None.
Hypothesis HO : x_orph X = None.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st g).
Hypothesis HP : x_pend X = Some (fst p, sstart (MR st g) i).
Hypothesis ALL : forall j, 0 <= j <= m_last_idx (MR st g) -> j <> i ->
  tbit (m_avail (MR st g)) j = true \/ tbit (m_freed (MR st g)) j = true.
Let sc := m_sizeclass (MR st g).
Let cnt := m_last_idx (MR st g) + 1.
(* [comment removed for export] *)
Hypothesis S1 : exists U, st1 = upd_ctx (fun c => set_usage_map U c) st.
Hypothesis U1 : forall sc', 0 <= sc' < 48 -> usage st1 sc' = if sc' =? sc then usage st sc - cnt else usage st sc'.
Hypothesis U2 : forall sc0 v, c_usage (s_ctx st1) !! sc0 = Some v -> 0 <= sc0 < 48.
Let st' := del_slots p (get_stride (MR st g)) cnt (del_group p st1).
Let nested := m_maplen (MR st g) =? 0.
Let X' := mkX (x_idle X) (g :: x_zomb X) (if nested then Some p else None) (if nested then None else Some (fst p)) None.

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma g_hosts : hosts st p g.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WKill ()) ["KILL"] "h02aip;1p;4p;6p;2p;3g013Hj1:Tg00mTj49Tg00n2j62Tg00I@j41Tg00:ij48Tg00nSj14Tg013jj63Tg014>j20Tg01A2j25Tg002lj36Tg01Aij47Tg00^=R0g010ER1#:g0027R2P1P2g011<R3g011ZR4P0g0123R5C9R6P3P4g012LP0P5g012jE2R5P1C1P2P6P5P1C8p,1pp,2st#4E3p,1g,02f0'5,0136X00p,2aip,2HgC7o"). Qed.
Lemma GO : group_ok X st LS g p ai.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WKill ()) ["KILL"] "p;8g01BCj80Tp,1Xp,2stp,2LSp,2IGp,1gp,1pp,2aip,2HgG0o"). Qed.
Lemma stride_pos : 0 < get_stride (MR st g).
Proof. pose proof (stride_ge _ _ _ IG _ _ g_hosts) as [H _]. unfold UNIT in H. lia. Qed.
Lemma gbase_p : gbase (MR st g) = p.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WKill ()) ["KILL"] "p;7g01IWj70Tp,1Xp,2stp,2LSp,2IMp,1pp,1gg01GAF0o"). Qed.
Lemma slot_g j : slot_start' (MR st g) j = (fst p, snd p + UNIT + get_stride (MR st g) * j).
Proof. rewrite slot_start'_sstart. unfold sstart. rewrite gbase_p. reflexivity. Qed.
Lemma sstart_g j : sstart (MR st g) j = snd p + UNIT + get_stride (MR st g) * j.
Proof. unfold sstart. rewrite gbase_p. reflexivity. Qed.

(* [comment removed for export] *)
Lemma K_metas : s_metas st' = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WKill ()) ["KILL"] "p'0h01ch11Uh22S1h32U1h42U2h53sc'h63sc0h73st'h81vh91Hh:1eh;3st1i001xp;4p;2p;3p;6p;1p;9g00I@j4>Tg01OWj22Tg01PUj21Tg002lj30Tg01QMR0j26Tg00mTj4KTg00n2j6FTg0154j15Tg00iHj29Tg00Y7j1ATg00Woj13Tg00eXj1@Tg01Ejj27Tg01EOj2?Tg01Qgj24Tg0190j2LTg00f6j2JTg013Hj1ITg00:ij4GTg01R]j1<Tg01SSj18Tg013jj6;Tg014>j2DTg01:Dj2CTg01D4j1ETg01TKj2=Tg01UEj4:Tg00P7j2BTg001Yl9HTp,2S1R1g00^=R2g0123R3g012jR4P2C>R5g00oLR6p,3st1R7g01V?R8f1R9f0R:'2W0p,2stR;'1R<30R=X15R>'6P0P5P>g0027g011<R>g011ZR0P2P3CKP>P0g012LP2P3P4EFg01>IC>R0p,3st'#5%5;R>30P:P6f2R?/2:X08/1;A069<X15,65g00aAR@/9:g00cK#A#3#3#3#3#@RA,7:'?RBf3RC/49g00bKP2p,2scRD,L914;Dp,3cntRD'J14;9n0100000020000RE502[^52%I2RFP2P2P5P2P3P4P2CGR4P9f4#<#8E;1D2:R33019@?17?A'?RA[^82^62p,1pR?p,1g,C;#ER@PD1=?CC:P6%5:=00>b7]4]3]2X;612C:X08/1;=06<X15,65f5/2:X08/1;R</49=02E\B^52P2P2P5P4P9f6/2:X08/1;#<#8E;=0F3PA[^82^62P?P@PD1=?<C:P61B0>b7W4W3W2P7P:P1p,2U1p,2U2M9HX9=X15P9P:O2n2001000000121100000b:o"). Qed.
Lemma K_MR x : MR st' x = MR st x.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WKill ()) ["KILL"] "h01xh11gp;4p;6p;1p;3p;2p;5g00mTj4=Tg00n2j6<Tg00I@j46Tg0154j12Tg017Xj1;Tg00:ij48Tg002lj33Tg00P7j27Tg001Yj65Tg01:Dj24Tg013jj69Tg01=nj5:Tg0027R0g01>IR1f3f2f1R2f0R3E9p=1P1P1P2g01?@P3D:p=0P0g011<R4g011ZR5g00^=R6g0123R7C=R8P4P5g012LP6P7g012jE<R7P1C6R6p,2stR5#2R4%;1R9P6P0P8P7P1C8R7P2P3C1'0P6P7P2P4C1,09531X16P6P7P3P4C1,09,71p,3st'R9#2g01W6E514931453531eX00P3O1X00o"). Qed.
Lemma K_regions : s_regions st' = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WKill ()) ["KILL"] "p'0h01ch11Uh22S1h32U1h42U2h53sc'h63sc0h73st'h81vh91Hh:1eh;3st1i001xp;4p;2p;3p;1p;6p;9g00I@j4?Tg01OWj22Tg01PUj21Tg002lj30Tg01QMR0j26Tg01X0j15Tg00iHj2;Tg00Y7j1CTg00Woj14Tg00eXj1@Tg01Ejj27Tg01EOj28Tg01Qgj23Tg0190j2JTg00f6j2ITg013Hj1HTg00:ij4FTg01R]j1=Tg01SSj19Tg013jj6<Tg014>j2ETg01:Dj2DTg01D4j1BTg01TKj2>Tg01UEj4:Tg00P7j2ATg001Yl9GTp,2S1R1g00^=R2g0123R3g012jR4P2C?R5g00oLR6p,3st1R7g01V?R8f1R9f0R:'2W0p,2stR;'1R<30R=X15R>'6P0P5P>g011<g011Zg012Lg01XjC?R>p,3st'#5%5;R030P:P6f2R?/2:X08/1;A069<X15,65g00aAR@/;:g00cK#C#4#4#4#4#@RA,7:'8RBf3RC/39g00bKP2p,2scRD,J913;Dp,3cntRD'I13;9n0100000020000RE502[^52%H2RFP2P2P5P2P3P4P2CFR4P9f4#=#9E<1E2:R3301;@?17?A'8RA[^82^62p,1pR?p,1g,D;#BR@PD1>?CC:P6%5:=0>0b7]4]3]2X;612C:X08/1;=06<X15,65f5/2:X08/1;R</39=02E\B^52P2P2P5P4P9f6/2:X08/1;#=#9E<=0F3PA[^82^62P?P@PD1>?<C:P61A>0b7W4W3W2P7P:P1p,2U1p,2U2M9GX9=X15P9P:O2n2001000000121100000b:o"). Qed.
Lemma K_shadow : s_shadow st' = s_shadow st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WKill ()) ["KILL"] "p'0h01ch11Uh22S1h32U1h42U2h53sc'h63sc0h73st'h81vh91Hh:1eh;3st1i001xp;4p;2p;3p;1p;6p;9g00I@j4?Tg01OWj22Tg01PUj21Tg002lj30Tg01QMR0j26Tg01Ycj15Tg00iHj2;Tg00Y7j1CTg00Woj14Tg00eXj1@Tg01Ejj27Tg01EOj28Tg01Qgj23Tg0190j2JTg00f6j2ITg013Hj1HTg00:ij4FTg01R]j1=Tg01SSj19Tg013jj6<Tg014>j2ETg01:Dj2DTg01D4j1BTg01TKj2>Tg01UEj4:Tg00P7j2ATg001Yl9GTp,2S1R1g00^=R2g0123R3g012jR4P2C?R5g00oLR6p,3st1R7g01V?R8f1R9f0R:'2W0p,2stR;'1R<30R=X15R>'6P0P5P>g011<g011Zg012Lg01Z\C?R>p,3st'#5%5;R030P:P6f2R?/2:X08/1;A069<X15,65g00aAR@/;:g00cK#C#4#4#4#4#@RA,7:'8RBf3RC/39g00bKP2p,2scRD,J913;Dp,3cntRD'I13;9n0100000020000RE502[^52%H2RFP2P2P5P2P3P4P2CFR4P9f4#=#9E<1E2:R3301;@?17?A'8RA[^82^62p,1pR?p,1g,D;#BR@PD1>?CC:P6%5:=0>0b7]4]3]2X;612C:X08/1;=06<X15,65f5/2:X08/1;R</39=02E\B^52P2P2P5P4P9f6/2:X08/1;#=#9E<=0F3PA[^82^62P?P@PD1>?<C:P61A>0b7W4W3W2P7P:P1p,2U1p,2U2M9GX9=X15P9P:O2n2001000000121100000b:o"). Qed.
Lemma K_areas : s_areas st' = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WKill ()) ["KILL"] "p'0h01ch11Uh22S1h32U1h42U2h53sc'h63sc0h73st'h81vh91Hh:1eh;3st1i001xp;4p;2p;3p;6p;1p;9g00I@j4>Tg01OWj22Tg01PUj21Tg002lj30Tg01QMR0j26Tg00mTj4KTg00n2j6FTg01[Uj15Tg00iHj29Tg00Y7j1ATg00Woj13Tg00eXj1@Tg01Ejj27Tg01EOj2?Tg01Qgj24Tg0190j2LTg00f6j2JTg013Hj1ITg00:ij4GTg01R]j1<Tg01SSj18Tg013jj6;Tg014>j2DTg01:Dj2CTg01D4j1ETg01TKj2=Tg01UEj4:Tg00P7j2BTg001Yl9HTp,2S1R1g00^=R2g0123R3g012jR4P2C>R5g00oLR6p,3st1R7g01V?R8f1R9f0R:'2W0p,2stR;'1R<30R=X15R>'6P0P5P>g0027g011<R>g011ZR0P2P3CKP>P0g012LP2P3P4EFg01\MC>R0p,3st'#5%5;R>30P:P6f2R?/2:X08/1;A069<X15,65g00aAR@/9:g00cK#A#3#3#3#3#@RA,7:'?RBf3RC/49g00bKP2p,2scRD,L914;Dp,3cntRD'J14;9n0100000020000RE502[^52%I2RFP2P2P5P2P3P4P2CGR4P9f4#<#8E;1D2:R33019@?17?A'?RA[^82^62p,1pR?p,1g,C;#ER@PD1=?CC:P6%5:=00>b7]4]3]2X;612C:X08/1;=06<X15,65f5/2:X08/1;R</49=02E\B^52P2P2P5P4P9f6/2:X08/1;#<#8E;=0F3PA[^82^62P?P@PD1=?<C:P61B0>b7W4W3W2P7P:P1p,2U1p,2U2M9HX9=X15P9P:O2n2001000000121100000b:o"). Qed.
Lemma K_tick : s_tick st' = s_tick st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WKill ()) ["KILL"] "p'0h01ch11Uh22S1h32U1h42U2h53sc'h63sc0h73st'h81vh91Hh:1eh;3st1i001xp;4p;2p;3p;1p;6p;9g00I@j4JTg01OWj21Tg01PUj22Tg002lj30Tg01QMR0j26Tg01]Dj15Tg00iHj2=Tg00Y7j1BTg00Woj13Tg00eXj1?Tg01Ejj27Tg01EOj28Tg01Qgj24Tg0190j2ITg00f6j2HTg013Hj1GTg00:ij4ETg01R]j1<Tg01SSj1:Tg013jj6;Tg014>j2DTg01:Dj2CTg01D4j1ATg01TKj29Tg01UEj4>Tg00P7j2@Tg001Yl9FTp,2S1R1g00^=R2g0123R3g012jR4P2CJR5g00oLR6p,3st1R7g01V?R8f1R9f0R:'1W0p,2stR;'2R<30R=X15R>'6P0P5P>g011<R>p,3st'#5%5;R030P:P6f2R?/1:X08/2;A069<X15,65g00aAR@/=:g00cK#B#3#3#3#3#?RA,7:'8RBf3RC/49g00bKP2p,2scRD,I914;Dp,3cntRD'H14;9n0100000020000RE502[^52%G2RFP2P2P5P2P3P4P2CER4P9f4#<#:E;1D2:R3301=@?17?A'8RA[^82^62p,1pR?p,1g,C;#AR@PD19?CC>P6%5:=0>0b7]4]3]2X;611C:X08/2;=06<X15,65f5/1:X08/2;R</49=02E\B^52P2P2P5P4P9f6/1:X08/2;#<#:E;=0F3PA[^82^62P?P@PD19?<C>P61@>0b7W4W3W2P7P:P1p,2U1p,2U2M9FX9=X15P9P:O2n2001000000121100000b:o"). Qed.
Lemma K_next_rid : s_next_rid st' = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WKill ()) ["KILL"] "p'0h01ch11Uh22S1h32U1h42U2h53sc'h63sc0h73st'h81vh91Hh:1eh;3st1i001xp;4p;2p;3p;1p;6p;9g00I@j4JTg01OWj21Tg01PUj22Tg002lj30Tg01QMR0j26Tg01^;j15Tg00iHj2=Tg00Y7j1BTg00Woj13Tg00eXj1?Tg01Ejj27Tg01EOj28Tg01Qgj24Tg0190j2ITg00f6j2HTg013Hj1GTg00:ij4ETg01R]j1<Tg01SSj1:Tg013jj6;Tg014>j2DTg01:Dj2CTg01D4j1ATg01TKj29Tg01UEj4>Tg00P7j2@Tg001Yl9FTp,2S1R1g00^=R2g0123R3g012jR4P2CJR5g00oLR6p,3st1R7g01V?R8f1R9f0R:'1W0p,2stR;'2R<30R=X15R>'6P0P5P>g011<R>p,3st'#5%5;R030P:P6f2R?/1:X08/2;A069<X15,65g00aAR@/=:g00cK#B#3#3#3#3#?RA,7:'8RBf3RC/49g00bKP2p,2scRD,I914;Dp,3cntRD'H14;9n0100000020000RE502[^52%G2RFP2P2P5P2P3P4P2CER4P9f4#<#:E;1D2:R3301=@?17?A'8RA[^82^62p,1pR?p,1g,C;#AR@PD19?CC>P6%5:=0>0b7]4]3]2X;611C:X08/2;=06<X15,65f5/1:X08/2;R</49=02E\B^52P2P2P5P4P9f6/1:X08/2;#<#:E;=0F3PA[^82^62P?P@PD19?<C>P61@>0b7W4W3W2P7P:P1p,2U1p,2U2M9FX9=X15P9P:O2n2001000000121100000b:o"). Qed.
Lemma K_secret : s_secret st' = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WKill ()) ["KILL"] "p'0h01ch11Uh22S1h32U1h42U2h53sc'h63sc0h73st'h81vh91Hh:1eh;3st1i001xp;4p;2p;3p;1p;6p;9g00I@j4JTg01OWj21Tg01PUj22Tg002lj30Tg01QMR0j26Tg01_6j15Tg00iHj2=Tg00Y7j1BTg00Woj13Tg00eXj1?Tg01Ejj27Tg01EOj28Tg01Qgj24Tg0190j2ITg00f6j2HTg013Hj1GTg00:ij4ETg01R]j1<Tg01SSj1:Tg013jj6;Tg014>j2DTg01:Dj2CTg01D4j1ATg01TKj29Tg01UEj4>Tg00P7j2@Tg001Yl9FTp,2S1R1g00^=R2g0123R3g012jR4P2CJR5g00oLR6p,3st1R7g01V?R8f1R9f0R:'1W0p,2stR;'2R<30R=X15R>'6P0P5P>p,3st'#5%5;R>502P:P6f2R0/1:X08/2;A069<X15,65g00aAR?/=:g00cK#B#3#3#3#3#?R@,7:'8RAf3RB/49g00bKP2p,2scRC,I914;Cp,3cntRC'H14;9n0100000020000RD502[^52%G2REP2P2P5P2P3P4P2CER4P9f4#<#:E;1D2:R3301=?0170@'8R@[^82^62p,1pR0p,1g,C;#AR?PC190BC>P6%5:=02>b7]4]3]2X;611B:X08/2;=06<X15,65f5/1:X08/2;R</49=02D\A^52P2P2P5P4P9f6/1:X08/2;#<#:E;=0E3P@[^82^62P0P?PC190<C>P61@2>b7W4W3W2P7P:P1p,2U1p,2U2M9FX9=X15P9P:O2n2001000000121100000b:o"). Qed.
Lemma K_reserved : s_reserved st' = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WKill ()) ["KILL"] "p'0h01ch11Uh22S1h32U1h42U2h53sc'h63sc0h73st'h81vh91Hh:1eh;3st1i001xp;4p;2p;3p;1p;6p;9g00I@j4LTg01OWj21Tg01PUj22Tg002lj30Tg01QMR0j26Tg00l<j2JTg00Jkj1DTg01_oj15Tg00iHj2<Tg00Y7j1@Tg00Woj13Tg00eXj1?Tg01Ejj27Tg01EOj2>Tg01Qgj24Tg0190j2KTg00f6j2ITg013Hj1GTg00:ij4FTg01R]j1;Tg01SSj1:Tg013jj6=Tg014>j2CTg01:Dj2BTg01D4j1ETg01TKj28Tg01UEj49Tg00P7j2ATg001Yl9HTp,2S1R1g00^=R2g0123R3g012jR4P2CLR5g00oLR6p,3st1R7g01V?R8f1R9f0R:'1W0p,2stR;'2R<30R=X15R>'6P0P5P>1J22#DR>p,3st'#5%5;R030P:P6f2R?/1:X08/2;A069<X15,65g00aAR@/<:g00cK#@#3#3#3#3#?RA,7:'>RBf3RC/49g00bKP2p,2scRD,K914;Dp,3cntRD'I14;9n0100000020000RE502[^52%G2RFP2P2P5P2P3P4P2CFR4P9f4#;#:E=1C2:R3301<@?17?A'>RA[^82^62p,1pR?p,1g,B;#ER@PD18?CC9P6%5:=0>0b7]4]3]2X;611C:X08/2;=06<X15,65f5/1:X08/2;R</49=02E\B^52P2P2P5P4P9f6/1:X08/2;#;#:E==0F3PA[^82^62P?P@PD18?<C9P61A>0b7W4W3W2P7P:P1p,2U1p,2U2M9HX9=X15P9P:O2n2001000000121100000b:o"). Qed.
Lemma K_atop : s_atop st' = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WKill ()) ["KILL"] "p'0h01ch11Uh22S1h32U1h42U2h53sc'h63sc0h73st'h81vh91Hh:1eh;3st1i001xp;4p;2p;3p;1p;6p;9g00I@j4JTg01OWj21Tg01PUj22Tg002lj30Tg01QMR0j26Tg01`jj15Tg00iHj2=Tg00Y7j1BTg00Woj13Tg00eXj1?Tg01Ejj27Tg01EOj28Tg01Qgj24Tg0190j2ITg00f6j2HTg013Hj1GTg00:ij4ETg01R]j1<Tg01SSj1:Tg013jj6;Tg014>j2DTg01:Dj2CTg01D4j1ATg01TKj29Tg01UEj4>Tg00P7j2@Tg001Yl9FTp,2S1R1g00^=R2g0123R3g012jR4P2CJR5g00oLR6p,3st1R7g01V?R8f1R9f0R:'1W0p,2stR;'2R<30R=X15R>'6P0P5P>p,3st'#5%5;R>502P:P6f2R0/1:X08/2;A069<X15,65g00aAR?/=:g00cK#B#3#3#3#3#?R@,7:'8RAf3RB/49g00bKP2p,2scRC,I914;Cp,3cntRC'H14;9n0100000020000RD502[^52%G2REP2P2P5P2P3P4P2CER4P9f4#<#:E;1D2:R3301=?0170@'8R@[^82^62p,1pR0p,1g,C;#AR?PC190BC>P6%5:=02>b7]4]3]2X;611B:X08/2;=06<X15,65f5/1:X08/2;R</49=02D\A^52P2P2P5P4P9f6/1:X08/2;#<#:E;=0E3P@[^82^62P0P?PC190<C>P61@2>b7W4W3W2P7P:P1p,2U1p,2U2M9FX9=X15P9P:O2n2001000000121100000b:o"). Qed.
Lemma K_groups : s_groups st' = delete p (s_groups st).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WKill ()) ["KILL"] "p'0h01ch11Uh22S1h32U1h42U2h53sc'h63sc0h73st'h81vh91Hh:1eh;3st1i001xp;4p;2p;3p;6p;1p;5p;9g00I@j49Tg01OWj22Tg01PUj21Tg002lj30Tg01QMR0j26Tg00mTj4NTg00n2j6LTg00nSj15Tg00;Zj4ETg00:0j4CTg014`j5BTg00iHj28Tg00Y7j1@Tg00Woj14Tg00eXj1OTg01Ejj2?Tg01EOj2=Tg01Qgj23Tg0190j2MTg00f6j2KTg013Hj1ITg00:ij4HTg01R]j1;Tg01SSj1>Tg013jj67Tg014>j2DTg01:Dj2FTg01D4j1GTg01TKj2:Tg01UEj4<Tg00P7j2JTg001Yl9ATp,2S1R1g00^=R2g0123R3g012jR4P2C9R5g00oLR6p,3st1R7g01V?R8f1R9f0R:'2W0p,2stR;'1R<30R=X15R>'6P0P5P>g0027R>g011<R0g011ZR?P2P3CNR@P0P?g012LP2P3P4ELR?g010ER0C9RAp,3st'#5P>PAP>P0PAP>P@P?P0CECCp,1pR0%5;DBR?30P:P6f2R@/2:X08/1;A069<X15,65g00aAR>/8:g00cK#@#4#4#4#4#ORB,?:'=RCf3RD/39g00bKP2p,2scRE,M913;Ep,3cntRE'K13;9n0100000020000RF502[^52%I2RGP2P2P5P2P3P4P2CHR4P9f4#;#>E71D2:R33018>@1?@B'=RB[^82^62P0p,1g,F;#GR@PE1:0DC<P6%5:=0A?b7]4]3]2X;612D:X08/1;=06<X15,65f5/2:X08/1;R</39=02F\C^52P2P2P5P4P9f6/2:X08/1;#;#>E7=0G3PB[^82^62P0P@PE1:0<C<P61JA?b7W4W3W2P7P:P1p,2U1p,2U2M9AX9=X15P9P:O2n2001000000121100000b:o"). Qed.
Lemma K_ctx : s_ctx st' = s_ctx st1.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WKill ()) ["KILL"] "p;1p;2g01R]j11Tg00P7j20Tg01V?p,3st1#1'0o"). Qed.
(* [comment removed for export] *)
Lemma K_c (P : mctx -> Prop) : (forall c U, P c -> P (set_usage_map U c)) -> P (s_ctx st) -> P (s_ctx st').
Proof. intros HPU H0. rewrite K_ctx. destruct S1 as [U ->]. cbn. apply HPU. exact H0. Qed.
Lemma K_cf :
  c_secret (s_ctx st') = c_secret (s_ctx st) /\ c_init_done (s_ctx st') = c_init_done (s_ctx st)
  /\ c_mmap_counter (s_ctx st') = c_mmap_counter (s_ctx st) /\ c_free_meta_head (s_ctx st') = c_free_meta_head (s_ctx st)
  /\ c_avail_meta (s_ctx st') = c_avail_meta (s_ctx st) /\ c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st)
  /\ c_avail_meta_area_count (s_ctx st') = c_avail_meta_area_count (s_ctx st) /\ c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st)
  /\ c_meta_area_head (s_ctx st') = c_meta_area_head (s_ctx st) /\ c_meta_area_tail (s_ctx st') = c_meta_area_tail (s_ctx st)
  /\ c_avail_meta_areas (s_ctx st') = c_avail_meta_areas (s_ctx st) /\ c_active (s_ctx st') = c_active (s_ctx st)
  /\ c_unmap_seq (s_ctx st') = c_unmap_seq (s_ctx st) /\ c_bounces (s_ctx st') = c_bounces (s_ctx st)
  /\ c_seq (s_ctx st') = c_seq (s_ctx st) /\ c_brk (s_ctx st') = c_brk (s_ctx st) /\ c_usage (s_ctx st') = c_usage (s_ctx st1).
Proof. destruct S1 as [U E]. rewrite K_ctx, E. cbn. repeat split; reflexivity. Qed.
Lemma K_usage sc' : usage st' sc' = usage st1 sc'.
Proof. reflexivity. Qed.

Lemma K_get_head h : get_head st' h = get_head st h.
Proof. destruct S1 as [U ->]. destruct h; reflexivity. Qed.
Lemma K_frontier rid r : frontier st' rid r = frontier st rid r.
Proof. unfold frontier. rewrite K_ctx. destruct S1 as [U ->]. reflexivity. Qed.

(* [comment removed for export] *)
Definition gslot (s : aptr) : Prop := exists j, 0 <= j < cnt /\ s = slot_start' (MR st g) j.
Lemma K_slots s : s_slots st' !! s = s_slots st !! s /\ ~ gslot s \/ s_slots st' !! s = None /\ gslot s.
Proof.
  pose proof stride_pos as SP. pose proof (g_li _ _ _ _ _ _ GO) as LI.
  unfold st'. rewrite lookup_del_slots; [| unfold cnt; lia| exact SP].
  replace (s_slots (del_group p st1)) with (s_slots st) by (destruct S1 as [U ->]; reflexivity).
  set (d := snd s - snd p - UNIT).
  destruct ((fst s =? fst p)%N && (0 <=? d) && (d mod get_stride (MR st g) =? 0) && (d / get_stride (MR st g) <? cnt)) eqn:E.
  - right. split; [reflexivity|]. apply Bool.andb_true_iff in E as [E E4]. apply Bool.andb_true_iff in E as [E E3]. apply Bool.andb_true_iff in E as [E1 E2].
    apply N.eqb_eq in E1. apply Z.leb_le in E2. apply Z.eqb_eq in E3. apply Z.ltb_lt in E4.
    exists (d / get_stride (MR st g)). split; [split; [apply Z.div_pos; lia| exact E4]|].
    rewrite slot_g. pose proof (Z.div_mod d (get_stride (MR st g)) ltac:(lia)) as DM. rewrite E3, Z.add_0_r in DM.
    destruct s as [sr so]. cbn in E1, d |- *. subst sr. f_equal. unfold d in DM. lia.
  - left. split; [reflexivity|]. intros (j & Hj & Es). rewrite slot_g in Es. subst s. cbn in d.
    assert (Ed : d = get_stride (MR st g) * j) by (unfold d; lia).
    rewrite N.eqb_refl in E. cbn in E.
    assert (E2 : (0 <=? d) = true) by (apply Z.leb_le; rewrite Ed; nia). rewrite E2 in E. cbn in E.
    assert (E3 : (d mod get_stride (MR st g) =? 0) = true) by (apply Z.eqb_eq; rewrite Ed, Z.mul_comm; apply Z_mod_mult).
    rewrite E3 in E. cbn in E.
    assert (E4 : (d / get_stride (MR st g) <? cnt) = true) by (apply Z.ltb_lt; rewrite Ed, Z.mul_comm, Z_div_mult by lia; lia).
    rewrite E4 in E. discriminate.
Qed.
Lemma K_slots_other s : ~ gslot s -> s_slots st' !! s = s_slots st !! s.
Proof. intros NG. destruct (K_slots s) as [[E _]|[_ G]]; [exact E| tauto]. Qed.
Lemma K_slots_g s : gslot s -> s_slots st' !! s = None.
Proof. intros G. destruct (K_slots s) as [[_ NG]|[E _]]; [tauto| exact E]. Qed.
Lemma K_slots_some s v : s_slots st' !! s = Some v -> s_slots st !! s = Some v /\ ~ gslot s.
Proof. intros H. destruct (K_slots s) as [[E NG]|[E G]]; [rewrite <- E; auto| congruence]. Qed.

(* [comment removed for export] *)
Lemma none_of {A} (o : option A) : (o <> None -> False) -> o = None.
Proof. destruct o; [intros H; exfalso; apply H; discriminate| reflexivity]. Qed.

Lemma g_slot_free j : 0 <= j <= m_last_idx (MR st g) ->
  ~ In (fst p, sstart (MR st g) j) (map bslot BL) /\ s_groups st !! (fst p, sstart (MR st g) j) = None
  /\ (x_pend X = Some (fst p, sstart (MR st g) j) -> j = i).
Proof.
  intros Hj. pose proof (is_part _ _ _ IS _ _ _ j Hg Hj) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ g_hosts) in P. unfold one5 in P.
  destruct P as (_ & nAB & nAC & nAD & nAE & nBC & nBD & nBE & nCD & nCE & nDE).
  assert (PJ : x_pend X = Some (fst p, sstart (MR st g) j) -> j = i).
  { intros HPj. rewrite HP in HPj. inversion HPj.
    destruct (Z.lt_total j i) as [LT|[E|LT]]; [| exact E|]; exfalso.
    - pose proof (sstart_lt _ _ _ IG _ _ j i g_hosts LT). pose proof stride_pos. lia.
    - pose proof (sstart_lt _ _ _ IG _ _ i j g_hosts LT). pose proof stride_pos. lia. }
  destruct (Z.eq_dec j i) as [->|NE].
  - rewrite HP in *. split; [intros C; apply nCE; auto|]. split; [| auto]. apply none_of. intros Hh. apply nDE. auto.
  - destruct (ALL j Hj NE) as [A|B].
    + split; [intros C; exact (nAC (conj A C))|]. split; [| exact PJ]. apply none_of. intros Hh. exact (nAD (conj A Hh)).
    + split; [intros C; exact (nBC (conj B C))|]. split; [| exact PJ]. apply none_of. intros Hh. exact (nBD (conj B Hh)).
Qed.
Lemma g_slot_free' j : 0 <= j <= m_last_idx (MR st g) ->
  ~ In (slot_start' (MR st g) j) (map bslot BL) /\ s_groups st !! (slot_start' (MR st g) j) = None.
Proof. intros Hj. rewrite (slot_start'_eq _ _ _ IM _ _ _ g_hosts). destruct (g_slot_free j Hj) as (A & B & _). auto. Qed.

Lemma gslot_range s : gslot s -> exists j, 0 <= j <= m_last_idx (MR st g) /\ s = slot_start' (MR st g) j.
Proof. intros (j & Hj & E). exists j. unfold cnt in Hj. split; [lia| exact E]. Qed.

(* [comment removed for export] *)
Lemma other_slot_not_g m b j : hosts st b m -> m <> g -> 0 <= j <= m_last_idx (MR st m) -> ~ gslot (slot_start' (MR st m) j).
Proof.
  intros Hm NE Hj G. destruct (gslot_range _ G) as (j' & Hj' & E).
  destruct (slot_key_inj _ _ _ IS _ _ _ _ _ _ Hm g_hosts Hj Hj' E) as [Em _]. exact (NE Em).
Qed.
Lemma entry_not_g s m j : s_slots st !! s = Some (m, j) -> m <> g -> ~ gslot s.
Proof.
  intros Hs NE. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hj & ->). exact (other_slot_not_g m b j Hb NE Hj).
Qed.
(* [comment removed for export] *)
Lemma entry_g_gslot s j : s_slots st !! s = Some (g, j) -> gslot s.
Proof.
  intros Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & Hj & ->). exists j. unfold cnt. split; [lia| reflexivity].
Qed.

Lemma hosts_K b m : hosts st' b m <-> hosts st b m /\ b <> p.
Proof.
  unfold hosts. rewrite K_groups. split.
  - intros [a H]. apply lookup_delete_Some in H as [NE H]. split; [exists a; exact H| congruence].
  - intros [[a H] NE]. exists a. rewrite lookup_delete_ne by congruence. exact H.
Qed.
Lemma hosts_K_neq b m : hosts st' b m -> m <> g.
Proof. intros H. apply hosts_K in H as [H NE]. intros ->. exact (NE (hosts_inj _ _ _ IM _ _ _ H g_hosts)). Qed.
Lemma live_K m : live_group st m -> m <> g -> live_group st' m.
Proof.
  intros [b Hb] NE. exists b. apply hosts_K. split; [exact Hb|]. intros ->. exact (NE (hosts_fun _ _ _ _ Hb g_hosts)).
Qed.
Lemma g_unlisted_K h : ~ In g (LS h).
Proof. exact (lists_notin st LS (old_lists _ _ _ _ _ INV) g NL h). Qed.

(* [comment removed for export] *)
Lemma p_not_gslot : ~ gslot p.
Proof.
  intros (j & Hj & E). rewrite slot_g in E. pose proof stride_pos.
  assert (snd p = snd p + UNIT + get_stride (MR st g) * j) by (rewrite E at 1; reflexivity). unfold UNIT in *. nia.
Qed.
Lemma slots_pos s m j : s_slots st !! s = Some (m, j) -> 0 < snd s.
Proof.
  intros Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hj & ->). rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb). cbn.
  pose proof (sstart0 _ _ _ IM _ _ Hb). pose proof (sstart_mono _ _ _ IG _ _ 0 j Hb ltac:(lia)).
  destruct (hosts_ok _ _ _ IG _ _ Hb) as (a & _ & GOm). pose proof (g_align _ _ _ _ _ _ GOm) as [A _]. unfold UNIT in *. lia.
Qed.

(* [comment removed for export] *)
Lemma top_region_empty b h : m_maplen (MR st g) <> 0 -> s_groups st !! b = Some h -> fst b = fst p -> b = p.
Proof.
  intros Hml Hb Hf. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Em & Hmem & _).
  assert (Hm : hosts st b m) by (destruct h as [hm ha]; cbn in Em; subst hm; exists ha; exact Hb).
  destruct (aptr_eq_dec m g) as [->|NE]; [exact (hosts_inj _ _ _ IM _ _ _ Hm g_hosts)|]. exfalso.
  destruct (Z.eq_dec (m_maplen (MR st m)) 0) as [Hml'|Hml'].
  - destruct (@top_chain _ _ _ _ IM IG IS m b Hm Hml') as (t & j & c & bt & Ha & Ht & Htop & Hft).
    assert (t = g) by (apply (@top_unique _ _ _ IG t g bt p Ht g_hosts Htop Hml); congruence). subst t.
    destruct (@anc_hostslot _ _ _ _ IM IG IS m g j c Ha) as (bp & Hp & Hsl).
    pose proof (hosts_inj _ _ _ IM _ _ _ Hp g_hosts). subst bp.
    destruct (@anc_facts _ _ _ _ IM IG IS m g j c Ha) as (bm' & bp' & _ & _ & _ & Hj & _).
    destruct (g_slot_free j Hj) as (_ & N & _). exact (Hsl N).
  - apply NE. apply (@top_unique _ _ _ IG m g b p Hm g_hosts Hml' Hml Hf).
Qed.

Lemma gcnt_K sc' : gcnt st sc' = (if sc =? sc' then cnt else 0) + gcnt st' sc'.
Proof.
  rewrite (gcnt_delete st st' p _ sc' Hg K_groups K_metas). unfold gterm. cbn. fold sc. fold cnt. reflexivity.
Qed.

Theorem INVL_kill : INVL X' st' L BL LS.
Proof.
  pose proof GO as GOg. pose proof g_hosts as Hgh.
  assert (NGm : forall b m, hosts st b m -> m <> g -> b <> p).
  { intros b m Hm NE ->. exact (NE (hosts_fun _ _ _ _ Hm g_hosts)). }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* [comment removed for export] *) destruct IR; constructor; rewrite ?K_regions, ?K_next_rid, ?K_reserved, ?K_atop; try assumption.
    + eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite K_frontier. reflexivity.
    + intros rid r H1 H2. rewrite K_frontier. exact (ir_metalen rid r H1 H2).
    + intros rid r H1 H2. rewrite K_frontier. exact (ir_brkfront rid r H1 H2).
    + apply (K_c (fun c => 0 <= c_meta_alloc_shift c /\ (c_meta_alloc_shift c = 0 \/ exists rid r, s_regions st !! rid = Some r /\ r_kind r = RKMeta /\ r_len r = 2 ^ c_meta_alloc_shift c * PGSZ))); [intros c U H; exact H| exact ir_shift].
    + apply (K_c (fun c => match c_brk c with
                           | BrkUntried => ld_brk L = BPUntried /\ forall rid r, s_regions st !! rid = Some r -> r_kind r <> RKBrk
                           | BrkDead => ld_brk L = BPDead
                           | BrkLive rid off => ld_brk L = BPLive /\ exists r, s_regions st !! rid = Some r /\ r_kind r = RKBrk /\ r_len r = off end));
        [intros c U H; exact H| exact ir_brk].
    + apply (K_c (fun c => 0 <= c_avail_meta_area_count c /\
        (0 < c_avail_meta_area_count c -> c_avail_meta_areas c <> None) /\
        (forall rid off, c_avail_meta_areas c = Some (rid, off) -> exists r, s_regions st !! rid = Some r /\ is_metakind r /\ PGSZ <= off /\ off mod PGSZ = 0
           /\ off + c_avail_meta_area_count c * PGSZ = r_len r /\ (0 < c_avail_meta_area_count c -> r_kind r = RKMeta))));
        [intros c U H; exact H| exact ir_cursor].
    + intros rid Ho. unfold X' in Ho. cbn in Ho. unfold nested in Ho. destruct (Z.eqb_spec (m_maplen (MR st g)) 0) as [E|NE]; [discriminate|].
      inversion Ho. subst rid. destruct (g_top _ _ _ _ _ _ GOg NE) as (H0 & r & Hr & Hk & _). exists r. split; [exact Hr|]. split; [exact Hk|].
      intros b Hb. rewrite K_groups. destruct (aptr_eq_dec b p) as [->|NEb]; [apply lookup_delete_eq|]. rewrite lookup_delete_ne by congruence.
      destruct (s_groups st !! b) eqn:Eb; [| reflexivity]. exfalso. exact (NEb (top_region_empty b _ NE Eb Hb)).
  - (* [comment removed for export] *) destruct K_cf as (cf1 & cf2 & cf3 & cf4 & cf5 & cf6 & cf7 & cf8 & cf9 & cf10 & cf11 & cf12 & cf13 & cf14 & cf15 & cf16 & cf17).
    destruct IA; constructor; rewrite ?K_regions, ?K_areas, ?K_secret, ?K_metas, ?cf1, ?cf2, ?cf3, ?cf4, ?cf5, ?cf6, ?cf7, ?cf8, ?cf9, ?cf10, ?cf11, ?cf12, ?cf13, ?cf14, ?cf15, ?cf16, ?cf17; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite K_frontier. auto.
    + intros sc' Hsc'. rewrite K_usage, (U1 sc' Hsc').
      pose proof (gcnt_K sc') as GK. rewrite <- (ia_usage sc' Hsc') in GK. rewrite Z.eqb_sym in GK.
      destruct (Z.eqb_spec sc' sc) as [E|NE]; [rewrite <- E; lia| lia].
  - (* [comment removed for export] *) destruct IM as [M1 M2 M3 M4 M5] eqn:EIM; constructor; rewrite ?K_MR.
    + intros m Hm. rewrite !K_MR. apply M1. rewrite <- (K_MR m). exact Hm.
    + intros m b Hm. rewrite K_MR in Hm. destruct (aptr_eq_dec m g) as [->|NE]; [right; left; reflexivity|].
      destruct (M2 m b Hm) as [H|H]; [left| right; right; exact H]. apply hosts_K. split; [exact H|]. exact (NGm b m H NE).
    + intros b h Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [NE Hb]. destruct (M3 b h Hb) as (m & ? & ? & ?). exists m. rewrite !K_MR. auto.
    + intros m Hm. rewrite K_metas. exact (M4 m Hm).
    + intros z Hz. rewrite !K_MR, K_groups. cbn in Hz. destruct Hz as [<-|Hz].
      * split; [intros [h Hh]; exact (g_unlisted_K h Hh)|]. split; [exact NL|].
        split; [exact (proj2 (il_link _ _ IL g) NL)|].
        exists p. split; [exact (hosts_mem _ _ _ IM _ _ g_hosts)| apply lookup_delete_eq].
      * destruct (M5 z Hz) as (A1 & A2 & A3 & b & A4 & A5). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
        exists b. split; [exact A4|]. destruct (aptr_eq_dec b p) as [->|NE]; [apply lookup_delete_eq| rewrite lookup_delete_ne by congruence; exact A5].
  - (* [comment removed for export] *) destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9] eqn:EIL; constructor; try assumption.
    + intros h. rewrite K_get_head. apply L1.
    + intros h. apply (dll_ext_metas st st' K_metas). apply L2.
    + intros m. rewrite !K_MR. apply L5.
    + intros m Hm. rewrite !K_MR. apply L6. exact Hm.
    + intros sc0 m Hm. destruct (L7 sc0 m Hm) as (A1 & A2 & A3). rewrite K_MR. split; [exact A1|]. split; [| exact A3].
      apply live_K; [exact A2|]. intros ->. exact (g_unlisted_K _ Hm).
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5] eqn:EIG. constructor.
    + intros m b aim Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [NEb Hb]. pose proof (G1 m b aim Hb) as GOm.
      assert (NEm : m <> g) by (intros ->; apply NEb; symmetry; exact (hosts_inj _ _ _ IM _ _ _ (ex_intro _ aim Hb) g_hosts)).
      assert (NF : x_fresh X <> Some m) by (rewrite HF; congruence).
      destruct GOm; constructor; rewrite ?K_MR, ?K_metas, ?K_regions; try assumption.
      * intros _. exact (g_partial NF).
      * intros _. exact (g_unlisted NF).
      * intros _. exact (g_rest NF).
      * intros _. exact (g_under NF).
      * intros Hml. destruct (g_nest Hml) as (pm & i' & Hs & REST). exists pm, i'. rewrite !K_MR. split; [| exact REST].
        rewrite K_slots_other; [exact Hs|]. apply (entry_not_g _ _ _ Hs). intros ->.
        destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & Hi' & Eb).
        destruct (g_slot_free' i' Hi') as [_ N]. rewrite <- Eb, Hb in N. discriminate.
    + intros b aim Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [_ Hb]. exact (G2 b aim Hb).
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite K_groups in H1, H2. apply lookup_delete_Some in H1 as [_ H1]. apply lookup_delete_Some in H2 as [_ H2].
      rewrite !K_MR. eapply G3; eassumption.
    + intros rid r Hr Hk Ho. rewrite K_regions in Hr. destruct (G4 rid r Hr Hk ltac:(rewrite HO; discriminate)) as (m & Hm & Hml). exists m. rewrite K_MR. split; [| exact Hml].
      apply hosts_K. split; [exact Hm|]. intros E.
      assert (Em : m = g) by (apply (hosts_fun st p); [rewrite <- E; exact Hm| exact g_hosts]). subst m.
      unfold X' in Ho. cbn in Ho. unfold nested in Ho. rewrite (proj2 (Z.eqb_neq _ _) Hml) in Ho. apply Ho. rewrite <- E. reflexivity.
    + intros b h Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [_ Hb]. rewrite K_regions. exact (G5 b h Hb).
  - (* [comment removed for export] *) destruct IS as [S1' S2 S3 S4 S5 S6] eqn:EIS. constructor.
    + intros s m j Hs. destruct (K_slots_some _ _ Hs) as [Hs0 NG]. destruct (S1' s m j Hs0) as (Hl & Hj & Es). rewrite !K_MR.
      assert (NEm : m <> g) by (intros ->; exact (NG (entry_g_gslot _ _ Hs0))).
      split; [exact (live_K m Hl NEm)|]. auto.
    + intros b m j Hb Hj. rewrite K_MR in Hj |- *. apply hosts_K in Hb as [Hb NEb].
      assert (NEm : m <> g) by (intros ->; exact (NEb (hosts_inj _ _ _ IM _ _ _ Hb g_hosts))).
      rewrite K_slots_other; [exact (S2 b m j Hb Hj)|]. exact (other_slot_not_g m b j Hb NEm Hj).
    + intros b m aim j Hb Hj. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [NEb Hb]. rewrite K_MR in Hj. rewrite !K_MR, K_groups. unfold X'. cbn [x_pend].
      assert (Hbm : hosts st b m) by (exists aim; exact Hb).
      assert (NEm : m <> g) by (intros ->; apply NEb; symmetry; exact (hosts_inj _ _ _ IM _ _ _ Hbm g_hosts)).
      pose proof (S3 b m aim j Hb Hj) as P. cbn zeta in P |- *.
      set (s := slot_start' (MR st m) j) in *.
      assert (OP : ~ (x_pend X = Some s)).
      { rewrite HP. intros E. apply (other_slot_not_g m b j Hbm NEm Hj). exists i. split; [unfold cnt; lia|].
        rewrite (slot_start'_eq _ _ _ IM _ _ _ g_hosts). apply (inj Some) in E. rewrite E. reflexivity. }
      unfold one5 in P |- *.
      destruct P as (P0 & nAB & nAC & nAD & nAE & nBC & nBD & nBE & nCD & nCE & nDE).
      destruct (aptr_eq_dec s p) as [Esp|NEsp].
      * assert (Hn : nested = true).
        { unfold nested. apply Z.eqb_eq. destruct (Z.eq_dec (m_maplen (MR st g)) 0) as [E|NE]; [exact E|]. exfalso.
          destruct (g_top _ _ _ _ _ _ GOg NE) as [H0 _]. pose proof (slots_pos s m j (S2 b m j Hbm Hj)) as SP. rewrite Esp in SP. lia. }
        rewrite Hn. rewrite Esp in *. rewrite lookup_delete_eq.
        assert (D : s_groups st !! p <> None) by (rewrite Hg; discriminate).
        assert (nA : ~ tbit (m_avail (MR st m)) j = true) by (intros A; exact (nAD (conj A D))).
        assert (nB : ~ tbit (m_freed (MR st m)) j = true) by (intros B; exact (nBD (conj B D))).
        assert (nC : ~ In p (map bslot BL)) by (intros C; exact (nCD (conj C D))).
        clear - nA nB nC. assert (NN : ~ (@None ghdr <> None)) by (intros H; apply H; reflexivity). tauto.
      * rewrite lookup_delete_ne by congruence.
        assert (NP' : ~ ((if nested then Some p else None) = Some s)) by (destruct nested; [intros E; inversion E; congruence| discriminate]).
        revert P0 nAB nAC nAD nAE nBC nBD nBE nCD nCE nDE OP NP'. clear.
        generalize (tbit (m_avail (MR st m)) j = true) (tbit (m_freed (MR st m)) j = true) (In s (map bslot BL)) (s_groups st !! s <> None).
        generalize ((if nested then Some p else None) = Some s) (x_pend X = Some s). intros. tauto.
    + intros s Hs. unfold X' in Hs. cbn [x_pend] in Hs. unfold nested in Hs. destruct (Z.eqb_spec (m_maplen (MR st g)) 0) as [Hml|Hml]; [| discriminate]. inversion Hs. subst s.
      destruct (g_nest _ _ _ _ _ _ GOg Hml) as (pm & ip & Hs0 & _). rewrite K_slots_other; [rewrite Hs0; discriminate| exact p_not_gslot].
    + exact S5.
    + intros k Hk. destruct (S6 k Hk) as (m & j & Hs & REST). exists m, j. rewrite K_MR. split; [| exact REST].
      rewrite K_slots_other; [exact Hs|]. intros G. destruct (gslot_range _ G) as (j' & Hj' & E).
      destruct (g_slot_free' j' Hj') as [NB _]. apply NB. rewrite <- E. apply in_map_iff. exists k. auto.
  - (* [comment removed for export] *) destruct ISH as [D1 D2 D3 D4 D5 D6] eqn:EISH.
    assert (KN : forall q v, known st q v -> known st' q v).
    { intros q v. unfold known, SHd, get_shadow. rewrite K_shadow. exact (fun H => H). }
    assert (UN : forall q, unknown st q -> unknown st' q).
    { intros q. unfold unknown, SHd, get_shadow. rewrite K_shadow. exact (fun H => H). }
    constructor.
    + intros rid sh Hsh. rewrite K_shadow in Hsh. rewrite K_regions. exact (D1 rid sh Hsh).
    + intros rid sh Hsh. rewrite K_shadow in Hsh. rewrite K_tick. exact (D2 rid sh Hsh).
    + intros b m j Hb Hj. apply hosts_K in Hb as [Hb _]. rewrite K_MR in Hj |- *. apply KN. exact (D3 b m j Hb Hj).
    + intros b m o Hb Ho. apply hosts_K in Hb as [Hb _]. apply UN. exact (D4 b m o Hb Ho).
    + intros b m pm j Hb Hml Hs. apply hosts_K in Hb as [Hb _]. rewrite K_MR in Hml. destruct (K_slots_some _ _ Hs) as [Hs0 _]. rewrite !K_MR.
      destruct (D5 b m pm j Hb Hml Hs0) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q). cbn zeta.
      split; [exists v3; auto|]. auto.
    + intros k m j Hk Hs. destruct (K_slots_some _ _ Hs) as [Hs0 _]. rewrite !K_MR. pose proof (D6 k m j Hk Hs0) as B. cbn zeta in B |- *.
      destruct B as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [exact A5|]. split.
      * intros Hres. destruct (A6 Hres) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; auto.
      * split; [intros Hres; apply KN; apply A7; exact Hres|]. intros a Ha. apply UN. apply A8. exact Ha.
Qed.

Lemma kill_top : m_maplen (MR st g) <> 0 ->
  exists r, snd p = 0 /\ s_regions st' !! (fst p) = Some r /\ r_kind r = RKGroup
    /\ m_maplen (MR st g) * 4096 = round_up_pg (r_len r) /\ 0 < m_maplen (MR st g) * 4096.
Proof.
  intros Hml. destruct (g_top _ _ _ _ _ _ GO Hml) as (H0 & r & Hr & Hk & E & _). exists r. rewrite K_regions.
  pose proof (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & L0 & _). pose proof (round_up_ge_k (r_len r)). repeat split; auto. lia.
Qed.

Lemma kill_nested : m_maplen (MR st g) = 0 ->
  exists pm ip bpm, s_slots st' !! p = Some (pm, ip) /\ hosts st' bpm pm /\ fst bpm = fst p
    /\ 0 <= ip <= m_last_idx (MR st pm) /\ p = (fst bpm, sstart (MR st pm) ip)
    /\ m_sizeclass (MR st g) < m_sizeclass (MR st pm) < 48
    /\ get_stride (MR st pm) = UNIT * size_class (m_sizeclass (MR st pm))
    /\ gend (MR st g) <= sstart (MR st pm) ip + get_stride (MR st pm).
Proof.
  intros Hml. destruct (g_nest _ _ _ _ _ _ GO Hml) as (pm & ip & Hs & Hf & He & Hsc & Hstr).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bpm Hpm] & Hip & Ep).
  exists pm, ip, bpm.
  assert (NE : pm <> g) by (intros ->; lia).
  split; [rewrite K_slots_other; [exact Hs| exact p_not_gslot]|].
  split; [apply hosts_K; split; [exact Hpm|]; intros ->; exact (NE (hosts_fun _ _ _ _ Hpm g_hosts))|].
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hpm) in Ep.
  split; [rewrite Ep; reflexivity|]. repeat split; auto; lia.
Qed.

(* [comment removed for export] *)
Lemma dec_hdr_eq {T} (k : aptr -> Z -> M T) bail :
  m_maplen (MR st g) = 0 ->
  exists pm ip bpm, dec_hdr st' p k bail = k pm ip
    /\ s_slots st' !! p = Some (pm, ip) /\ hosts st' bpm pm /\ fst bpm = fst p
    /\ 0 <= ip <= m_last_idx (MR st pm) /\ p = (fst bpm, sstart (MR st pm) ip)
    /\ m_sizeclass (MR st g) < m_sizeclass (MR st pm) < 48.
Proof.
  intros Hml. destruct (kill_nested Hml) as (pm & ip & bpm & Hs' & Hpm' & Hf & Hip & Ep & Hsc & Hstr & Hend).
  exists pm, ip, bpm. split; [| repeat split; auto; lia].
  pose proof Hpm' as Hpm. apply hosts_K in Hpm as [Hpm NEb].
  destruct (hosts_ok _ _ _ IG _ _ Hpm) as (aipm & Hgpm & GOpm).
  assert (Hs : s_slots st !! p = Some (pm, ip)) by (destruct (K_slots_some _ _ Hs') as [H _]; exact H).
  (* [comment removed for export] *)
  pose proof (ish_nest _ _ ISH p g pm ip g_hosts Hml Hs) as NS. cbn zeta in NS. rewrite (hosts_gbase _ _ _ IM _ _ Hpm) in NS.
  set (q := (snd p - snd bpm - UNIT) / UNIT) in NS.
  destruct NS as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
  pose proof (ish_hdr0 _ _ ISH bpm pm ip Hpm ltac:(unfold cnt_of; lia)) as K4.
  assert (KN : forall a v, known st a v -> known st' a v).
  { intros a v. unfold known, SHd, get_shadow. rewrite K_shadow. exact (fun H => H). }
  assert (Hq : UNIT * q = get_stride (MR st pm) * ip).
  { subst q. rewrite Ep. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hpm).
    replace (snd bpm + UNIT + get_stride (MR st pm) * ip - snd bpm - UNIT) with (size_class (m_sizeclass (MR st pm)) * ip * UNIT) by (rewrite Hstr; lia).
    rewrite Hstr. unfold UNIT. rewrite Z.div_mul by lia. lia. }
  clearbody q.
  pose proof (g_align _ _ _ _ _ _ GOpm) as [A0 A16].
  unfold dec_hdr, get_meta.
  rewrite (guard_true 10).
  2:{ apply Z.eqb_eq. rewrite Ep. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hpm), Hstr. unfold UNIT in *.
      replace (snd bpm + 16 + 16 * size_class (m_sizeclass (MR st pm)) * ip) with (snd bpm + (1 + size_class (m_sizeclass (MR st pm)) * ip) * 16) by lia.
      rewrite Z_mod_plus_full. exact A16. }
  unfold rd16.
  rewrite (rd8_known st' (aadd p (-2)) (byte_of q 0)) by (eapply known_at; [apply KN; exact K2| cbn; lia| reflexivity]).
  rewrite (rd8_known st' (aadd (aadd p (-2)) 1) (byte_of q 1)) by (eapply known_at; [apply KN; exact K1| cbn; lia| reflexivity]).
  rewrite (rd8_known st' (aadd p (-3)) v3) by (eapply known_at; [apply KN; exact K3| cbn; lia| reflexivity]).
  rewrite (rd8_known st' (aadd p (-4)) 0).
  2:{ eapply known_at; [apply KN; exact K4| rewrite Ep; cbn; unfold IB; lia| rewrite Ep; reflexivity]. }
  cbn [Z.eqb negb].
  rewrite (u16_bytes q Q).
  assert (Ebase : aadd p (- (UNIT * q) - UNIT) = bpm).
  { rewrite Ep. unfold aadd, sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hpm). destruct bpm as [br bo]. cbn [fst snd] in *. f_equal. lia. }
  rewrite Ebase. unfold get_group. destruct Hpm' as [ai' Hg']. rewrite Hg'. cbn [g_meta]. rewrite E3. fold (MR st' pm). rewrite !K_MR.
  rewrite (guard_true 11) by (rewrite (hosts_mem _ _ _ IM _ _ Hpm); apply optr_eqb_refl).
  rewrite (guard_true 12) by (apply Z.leb_le; lia).
  pose proof (is_part _ _ _ IS _ _ _ ip Hgpm Hip) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hpm), <- Ep in P. unfold one5 in P.
  assert (D : s_groups st !! p <> None) by (rewrite Hg; discriminate).
  rewrite (guard_true 13) by (unfold testbit; destruct (Z.testbit (m_avail (MR st pm)) ip) eqn:E; [exfalso; unfold tbit in P; tauto| reflexivity]).
  rewrite (guard_true 14) by (unfold testbit; destruct (Z.testbit (m_freed (MR st pm)) ip) eqn:E; [exfalso; unfold tbit in P; tauto| reflexivity]).
  pose proof (g_present _ _ _ _ _ _ GOpm) as Pr. destruct (s_metas st !! pm) as [mr|] eqn:Em; [| congruence].
  destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk).
  destruct (ia_areas _ IA _ _ Ha) as ((r & Hr & Hmk & Hal & Hpg & Hfr) & Hck & Hns & _).
  destruct K_cf as (cf1 & _).
  rewrite (guard_true 15) by (rewrite K_areas, Emk, (area_of_mslot a ka Hal Hka), Ha; apply Z.eqb_eq; unfold ctx; rewrite cf1; exact Hck).
  pose proof (size_class_bound (m_sizeclass (MR st pm))) as SB.
  rewrite (guard_true 16).
  2:{ clear KN K2 K1 K3 K4 P D Ebase. destruct (Z.ltb_spec (m_sizeclass (MR st pm)) 48); [| lia]. rewrite Hstr in Hq.
      assert (Eq : q = size_class (m_sizeclass (MR st pm)) * ip) by (unfold UNIT in Hq; lia).
      assert (G0 : 0 <= m_sizeclass (MR st g)) by (destruct (g_sc _ _ _ _ _ _ GO) as [[[G0 _] _]|(G63 & _)]; lia).
      rewrite Eq. specialize (SB ltac:(lia)). apply Bool.andb_true_iff. split; [apply Z.leb_le; lia| apply Z.ltb_lt]. rewrite Z.mul_add_distr_l. lia. }
  rewrite (guard_true 17).
  2:{ destruct (Z.eqb_spec (m_maplen (MR st pm)) 0) as [|NM]; cbn [negb]; [reflexivity|].
      destruct (g_top _ _ _ _ _ _ GOpm NM) as (B0 & _ & _ & _ & _ & GE). apply Z.leb_le.
      unfold gend, cnt_of, sstart in GE. rewrite (hosts_gbase _ _ _ IM _ _ Hpm), B0 in GE.
      pose proof (stride_ge _ _ _ IG _ _ Hpm) as [S16 _]. unfold UNIT in S16, Hq, GE.
      clear KN K2 K1 K3 K4 P D Ebase SB.
      eapply (guard17_arith (get_stride (MR st pm)) ip 0 0 q (m_last_idx (MR st pm)) (m_maplen (MR st pm))); try lia. }
  reflexivity.
Qed.
End KILL.

(* [comment removed for export] *)
Lemma fg_st1 X st L BL LS g p ai (INV : INVL X st L BL LS) (Hg : s_groups st !! p = Some (mkGhdr (Some g) ai)) :
  let sc := m_sizeclass (MR st g) in
  let cnt := m_last_idx (MR st g) + 1 in
  let st1 := if sc <? 48 then set_usage sc (usage st sc - cnt) st else st in
  (exists U, st1 = upd_ctx (fun c => set_usage_map U c) st)
  /\ (forall sc', 0 <= sc' < 48 -> usage st1 sc' = if sc' =? sc then usage st sc - cnt else usage st sc')
  /\ (forall sc0 v, c_usage (s_ctx st1) !! sc0 = Some v -> 0 <= sc0 < 48).
Proof.
  cbn zeta. pose proof (ia_usage_keys _ (proj1 (proj2 INV))) as UK.
  pose proof (g_sc _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hg)) as SC.
  destruct (Z.ltb_spec (m_sizeclass (MR st g)) 48) as [LT|GE].
  - split; [eexists; reflexivity|]. split.
    + intros sc' Hsc'. apply usage_set_usage.
    + intros sc0 v. cbn. destruct (Z.eq_dec sc0 (m_sizeclass (MR st g))) as [->|NE].
      * intros _. destruct SC as [[A _]|(A & _)]; lia.
      * rewrite lookup_insert_ne by congruence. apply UK.
  - split; [| split; [| exact UK]].
    + exists (c_usage (s_ctx st)). destruct st as [c ? ? ? ? ? ? ? ? ? ?]; destruct c; reflexivity.
    + intros sc' Hsc'. destruct (Z.eqb_spec sc' (m_sizeclass (MR st g))); [lia| reflexivity].
Qed.
