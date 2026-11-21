(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (58 recorded proofs replaced by written proofs (data0_shape, data0_mem, de_fields and 55 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2 MI_Pres3.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Pres4 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC47Corelib4Init9Datatypes3appC45stdpp>list_relations4list9NoDup_nilC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC59OSSVerify5KrLib4Spec7MI_List>NoDup_In_splitC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4base6ElemOfC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapI35stdpp4base<list_elem_of00C35stdpp4base?list_elem_of_InC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC35stdpp6option;from_optionC47Corelib4Init9Datatypes2IDC35stdpp4base5EmptyC35stdpp8fin_maps@lookup_insert_neC59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_extC35stdpp4gmapBgmap_partial_alterC59OSSVerify5KrLib4Spec7MI_List7data_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3iffK59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List:data_of_eqC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres49de_fieldsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List?get_stride_dataC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes2idK47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib4Spec8MI_Pres46de_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1N01C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulc59OSSVerify5KrLib4Spec8MI_Pres49de_strideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres48de_gbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02c59OSSVerify5KrLib4Spec8MI_Pres47de_lastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib4Spec8MI_Pres46de_cntC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres49de_sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib4Spec8MI_Pres4=ctx_but_heads01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib4Spec8MI_Pres4=ctx_but_heads00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_headC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec7MI_List8lists_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7head_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3dllC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K59OSSVerify5KrLib4Spec7MI_List8lists_ok01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic9False_indI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6MI_Ext9hosts_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext>live_group_extC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres47cb_amasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8frontierC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00c59OSSVerify5KrLib4Spec8MI_Pres48cb_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres3?gcnt_ext_groupsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_zombC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv;is_metakindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec4KInv7ld_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps;map_to_listC46Stdlib5Lists4List6filterI46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec4KInv9ld_brkregC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation@Permutation_reflc59OSSVerify5KrLib4Spec8MI_Pres4;rl_frontierC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationAPermutation_transK59OSSVerify5KrLib4Spec6MI_Inv5inv_R01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5mslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gcntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib4Spec8MI_Pres47rl_gcntC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres48rl_usageC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_A01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4;data0_shapeC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsBsubrelation_properc59OSSVerify5KrLib4Spec8MI_Pres48rl_hostsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_M01C1?~~~~~~~~~~~~~~~C47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismc59OSSVerify5KrLib4Spec8MI_Pres47rl_liveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_L01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7x_freshC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K59OSSVerify5KrLib4Spec6MI_Inv8group_ok01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_G01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Inv5inv_S01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext;inv_SH_viewC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsFreflexive_proper_proxyK59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7atop_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv9brk_phase04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes?RelationClasses=iff_ReflexiveC35stdpp4base:decide_relC35stdpp4base6decideI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic7and_indC47Corelib4Init5Logic6or_indC59OSSVerify5KrLib4Spec7MI_List4fupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List<lhead_eq_decC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1c59OSSVerify5KrLib4Spec8MI_Pres4;inv_L_listsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7il_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9il_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7il_keysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv>ia_active_keysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7im_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7im_zombC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres49old_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_scC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec7MI_ListBlists_in_next_someC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres49old_listsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_Pres3?present_of_nextC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4;listed_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7il_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List=lists_prev_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List=lists_next_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres48old_idleC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres48old_zombC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9hosts_memC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres48old_freeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres49data0_memC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres46xfreshC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres48cbh_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4:old_activeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres48old_keysC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4;old_actkeysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9g_partialC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:g_unlistedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6g_restC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres46old_63C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7g_underC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4;INVL_relinkC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc>set_active_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBset_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List8queue_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Kit@s_metas_upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List>set_head_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyc59OSSVerify5KrLib4Spec8MI_Pres47fupd_inC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_app_iffC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes?RelationClasses>iff_Transitivec59OSSVerify5KrLib4Spec8MI_Pres44q_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List;lists_notinC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4=idle_not_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4=zomb_not_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4;head_listedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4;prev_listedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4Aqueue_metas_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4;queue_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List:queue_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List:queue_keysC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4>listed_presentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List?queue_keys_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List;lists_queueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List7fupd_neC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4?get_head_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List:queue_headC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4:g_not_idleC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4=idle_unlistedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres49untouchedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres49q_in_listC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4:g_not_zombC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4=zomb_unlistedC1?~~~~~~~~~~~~~~~C47Corelib7Classes>Morphisms_Prop@not_iff_morphismC59OSSVerify5KrLib4Spec7MI_List7fupd_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4;head_of_appC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses5mkrelC47Corelib7Classes9MorphismsDiff_impl_subrelationC59OSSVerify5KrLib4Spec8MI_Pres35xidleC1?~~~~~~~~~~~~~~~C47Corelib7Classes>Morphisms_PropIiff_iff_iff_impl_morphismc59OSSVerify5KrLib4Spec8MI_Pres44d_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8il_nodupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7il_disjC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres48m_listedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4;next_listedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4Cdequeue_metas_otherC1?~~~~~~~~~~~~~~~C45stdpp>list_relations4list:NoDup_consC35stdpp4base7elem_ofC59OSSVerify5KrLib4Spec7MI_List<dequeue_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitEget_meta_rec_upd_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4=dequeue_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List<dequeue_keysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_ListAdequeue_keys_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List=lists_dequeueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List<dequeue_headC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4;untouched_dC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres49d_in_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List=dequeue_key_mC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4:present_MRC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natc59OSSVerify5KrLib4Spec8MI_Pres4=free_not_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres48d_in_revC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4;nonhead_oldC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres45MR'_mC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres45m_outC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib4Spec8MI_Pres44r_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres4<cbh_set_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_List<lists_rotateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitGget_head_set_head_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_Pres49r_in_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_KitEget_meta_rec_set_headC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition xfresh (X : extras) (f : option aptr) : extras := mkX (x_idle X) (x_zomb X) (x_pend X) (x_orph X) f.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma data0_shape r : data_of r = data_of meta0 <-> r = mkMeta (m_prev r) (m_next r) None 0 0 0 0 0 0.
Proof.
  destruct r; unfold data_of, m_set_prev, m_set_next, meta0; cbn. split; intros H; [injection H; intros; subst; reflexivity| injection H; intros; subst; reflexivity].
Qed.

Lemma data0_mem r : data_of r = data_of meta0 -> m_mem r = None.
Proof. intros H. apply data_of_eq in H. destruct H as (H & _). exact H. Qed.

Section DEXT.
Variables (st st' : mstate).
Hypothesis DE : forall x, data_of (MR st' x) = data_of (MR st x).
Lemma de_fields x :
  m_mem (MR st' x) = m_mem (MR st x) /\ m_avail (MR st' x) = m_avail (MR st x) /\ m_freed (MR st' x) = m_freed (MR st x)
  /\ m_last_idx (MR st' x) = m_last_idx (MR st x) /\ m_freeable (MR st' x) = m_freeable (MR st x)
  /\ m_sizeclass (MR st' x) = m_sizeclass (MR st x) /\ m_maplen (MR st' x) = m_maplen (MR st x).
Proof. apply data_of_eq. apply DE. Qed.
Lemma de_mem x : m_mem (MR st' x) = m_mem (MR st x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) ["DEXT"] "h01xh11Hp;2p;1p;3g00V@j22Tg00Koj13Tg003Yj34Tg00Lej15Tg00M]j1:Tg00NUj19Tg00OPj18Tg00PKj17Tg00QGj16Tg00UeR0j21Tg00W3j1;Tg00SUf1R1f0R234p=0g002dR3P0g00=ZR0p,3st'R4/22R5#3p,2stR6/22R7#334R8%55%57'0%:5%:7'0%95%97'0%85%87'0%75%77'0%65%67'0'1'1'1'1'11241#31261#3540%;2P1n2001000000120000000X03P8^03P2P1O1b1X03P2O1W0o"). Qed.
Lemma de_avail x : m_avail (MR st' x) = m_avail (MR st x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) ["DEXT"] "h01xh11Hh22H0p;2p;1p;3g00V@j24Tg00Koj1;Tg003Yj3:Tg00Lej17Tg00M]j12Tg00NUj13Tg00OPj11Tg00PKj15Tg00QGj16Tg00UeR0j29Tg00W3j1<Tg00SUR1f1R2f0R33:p=8f2R4=:12/93p=0g002dR1P0g00=Zp,3st'R5/43R6#;p,2stR7/43R8#;3:%76%78'8R9%26%28%36%38%16%18%56%58%66%68'830303030R8'9R61452R5#71472R7#7'8R:%25%27%35%37%15%17%55%57%65%67'830303030'9%<3P3n2001000000120000000X01P6^01P0P9P8P:P2P3O1P2n2001000000120000000X01P9^01P3P4O1b2b1X01P3O1W0o"). Qed.
Lemma de_freed x : m_freed (MR st' x) = m_freed (MR st x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) ["DEXT"] "h01xh11Hh22H0h32H1p;2p;1p;3g00V@j22Tg00Koj1:Tg003Yj39Tg00Lej17Tg00M]j18Tg00NUj14Tg00OPj13Tg00PKj15Tg00QGj16Tg00UeR0j21Tg00W3j1;Tg00SUf1R1f0R239p=0g002dR3P0g00=Zp,3st'R4/22R5#:p,2stR6/22R7#:39%75%77'0R8%85%87'0R9%45%47'0%35%37'0%55%57'0%65%67'0'1'1'1R7'1R5'1R:1241R4#71261R6#7'0%84%86'0R;%44%46'0%34%36'0%54%56'0%64%66'0'1'1'1'1R6'1%;2P2n2001000000120000000X03P:^03P0P8P5P6P1P2O1R6P2n2001000000120000000X03P5^03P0P9P7P;P6P1n2001000000120000000X03P9^03P2f3O1b3b2b1X03P2O1W0o"). Qed.
Lemma de_last x : m_last_idx (MR st' x) = m_last_idx (MR st x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) ["DEXT"] "h01xh11Hh22H0h32H1h42H2p;2p;1p;3g00V@j22Tg00Koj1:Tg003Yj39Tg00Lej17Tg00M]j18Tg00NUj14Tg00OPj13Tg00PKj15Tg00QGj16Tg00UeR0j21Tg00W3j1;Tg00SUf1R1f0R239p=0g002dR3P0g00=Zp,3st'R4/22R5#:p,2stR6/22R7#:39%75%77'0R8%85%87'0R9%45%47'0R:%35%37'0%55%57'0%65%67'0'1'1R7'1R5'1R;'1R<1241R4#71261R6#7'0%84%86'0%44%46'0R=%34%36'0%54%56'0%64%66'0'1'1'1R6'1R4'1%;2P2n2001000000120000000X03P<^03P0P8P;P4P1P2O1R4P2n2001000000120000000X03P;^03P0P9P5P6P4P2n2001000000120000000X03P5^03P0P:P7P=P4P1n2001000000120000000X03P:^03P2f4O1b4b3b2b1X03P2O1W0o"). Qed.
Lemma de_freeable x : m_freeable (MR st' x) = m_freeable (MR st x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) ["DEXT"] "h01xh11Hh22H0h32H1h42H2h52H3p;2p;1p;3g00V@j22Tg00Koj1:Tg003Yj39Tg00Lej17Tg00M]j18Tg00NUj14Tg00OPj13Tg00PKj15Tg00QGj16Tg00UeR0j21Tg00W3j1;Tg00SUf1R1f0R239p=0g002dR3P0g00=Zp,3st'R4/22R5#:p,2stR6/22R7#:39%75%77'0R8%85%87'0R9%45%47'0R:%35%37'0R;%55%57'0%65%67'0'1R7'1R5'1R<'1R='1R>1241R4#71261R6#7'0%84%86'0%44%46'0%34%36'0R?%54%56'0%64%66'0'1'1R6'1R4'1R@'1%;2P2n2001000000120000000X03P>^03P0P8P=P@P1P2O1R@P2n2001000000120000000X03P=^03P0P9P<P4P@P2n2001000000120000000X03P<^03P0P:P5P6P@P2n2001000000120000000X03P5^03P0P;P7P?P@P1n2001000000120000000X03P;^03P2f5O1b5b4b3b2b1X03P2O1W0o"). Qed.
Lemma de_sc x : m_sizeclass (MR st' x) = m_sizeclass (MR st x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) ["DEXT"] "h01xh11Hh22H0h32H1h42H2h52H3h62H4p;2p;1p;3g00V@j22Tg00Koj1:Tg003Yj39Tg00Lej17Tg00M]j18Tg00NUj14Tg00OPj13Tg00PKj15Tg00QGj16Tg00UeR0j21Tg00W3j1;Tg00SUf1R1f0R239p=0g002dR3P0g00=Zp,3st'R4/22R5#:p,2stR6/22R7#:39%75%77'0R8%85%87'0R9%45%47'0R:%35%37'0R;%55%57'0R<%65%67'0R7'1R5'1R='1R>'1R?'1R@1241R4#71261R6#7'0%84%86'0%44%46'0%34%36'0%54%56'0RA%64%66'0'1R6'1R4'1RB'1RC'1%;2P2n2001000000120000000X03P@^03P0P8P?PCP1P2O1RCP2n2001000000120000000X03P?^03P0P9P>PBPCP2n2001000000120000000X03P>^03P0P:P=P4PCP2n2001000000120000000X03P=^03P0P;P5P6PCP2n2001000000120000000X03P5^03P0P<P7PAPCP1n2001000000120000000X03P<^03P2f6O1b6b5b4b3b2b1X03P2O1W0o"). Qed.
Lemma de_maplen x : m_maplen (MR st' x) = m_maplen (MR st x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) ["DEXT"] "h01xh11Hh22H0h32H1h42H2h52H3h62H4p;2p;1p;3g00V@j22Tg00Koj1:Tg003Yj39Tg00Lej17Tg00M]j18Tg00NUj14Tg00OPj13Tg00PKj15Tg00QGj16Tg00UeR0j21Tg00W3j1;Tg00SUf1R1f0R239p=0g002dR3P0g00=Zp,3st'R4/22R5#:p,2stR6/22R7#:39%75%77'0R8%85%87'0R9%45%47'0R:%35%37'0R;%55%57'0R<%65%67'0R7'1R5'1R='1R>'1R?'1R@1241R4#71261R6#7'0%84%86'0%44%46'0%34%36'0%54%56'0%64%66'0R6'1R4'1RA'1RB'1RC'1%;2P2n2001000000120000000X03P@^03P0P8P?PCP1P2O1R1P2n2001000000120000000X03P?^03P0P9P>PBP1P2n2001000000120000000X03P>^03P0P:P=PAP1P2n2001000000120000000X03P=^03P0P;P5P4P1P2n2001000000120000000X03P5^03P0P<P7P6P1P2n2001000000120000000X03P7^03P2f6O1b6b5b4b3b2b1X03P2O1W0o"). Qed.
Lemma de_stride x : get_stride (MR st' x) = get_stride (MR st x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) ["DEXT"] "h01xp;2p;3g00V@j20Tg00Woj31Tg002dR0p,3st'f0R1'0p,2st/01p,2DEP1O131X00P1O1W0o"). Qed.
Lemma de_gbase x : gbase (MR st' x) = gbase (MR st x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) ["DEXT"] "h01xh11op;2p;1p;4p;5p;3p;6g00V@j21Tg00Koj12Tg00Y0j29Tg00YPj15Tg00Ylj4:Tg00>lj50Tg003Yj34Tg00K:j28Tg00ZLj17Tg006>j66Tg00[Ej13Tg002dR0g00=ZR1p,2stR2f0R3'1R4#2R5g00\;R6g00SUR7'9R8P8%58R9P6P7g00\Yg00S7C:R7P3D0P8P8P9P7f1,12#2D0540X11P8P8P9P7P5D0,80p,3st'/13R5#2%73E6%35%34540eX00P3O1W0o"). Qed.
Lemma de_sstart x i : sstart (MR st' x) i = sstart (MR st x) i.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) ["DEXT"] "h01ih11xh21ah31zp;2p;1p;3p;6g00V@j22Tg00[Ej16Tg00]7j20Tg00]Tj13Tg00^Oj21Tg003Yj35Tg00K:j2<Tg00^lj1;Tg006>j68Tg00_hj19Tg00`cj27Tg00aZj3:Tg00\;g00SUR0f0R13:p=4g002dR2P2p,2stR3f1R4'2R5#6R6%41g00b7R7'0p,3st'R8f2R9'2#3/14'01239R9#6#4/07R3%39/14'0R9550X22P0%35R:1114,03=509X30%46/0711:1'0,<01284R8#3%;4E8%68%94E817811751550eX00X12P4P1O2X00W1o"). Qed.
Lemma de_slot_start' x i : slot_start' (MR st' x) i = slot_start' (MR st x) i.
Proof. unfold slot_start'. rewrite de_mem, de_stride. reflexivity. Qed.
Lemma de_cnt x : cnt_of (MR st' x) = cnt_of (MR st x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) ["DEXT"] "h01xh11zp;2p;1p;3p;6g00V@j20Tg00NUj12Tg00d]j16Tg00]7j21Tg003Yj34Tg00K:j28Tg00e;j17Tg006>j65Tg00f5j13Tg002dR0g00SUR1p,2stR2f0R3'0R4#2R5g00fl#6R6,13f1,02#2/16541X111156,81p,3st'/03R6#2%73E5%36%34541eX00P3O1W0o"). Qed.
Lemma de_gend x : gend (MR st' x) = gend (MR st x).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) ["DEXT"] "h01xh11zp;2p;1p;3p;6g00V@j22Tg00f5j13Tg00`cj20Tg003Yj31Tg00K:j28Tg00gQj17Tg006>j65Tg00hJj26Tg00iFj14Tg002dR0g00SUR1p,2stR2f0R3'2R4p,3st'/23R5#3R6'0f1,22R2%32'0R79113X11P1%34R81023=117X111048,81P6%73E510561636E5%45%44511eX00P3O1W0o"). Qed.
End DEXT.

(* [comment removed for export] *)
Record ctx_but_heads (c c' : mctx) : Prop := mkCBH {
  cb_secret : c_secret c' = c_secret c;
  cb_init : c_init_done c' = c_init_done c;
  cb_mc : c_mmap_counter c' = c_mmap_counter c;
  cb_am : c_avail_meta c' = c_avail_meta c;
  cb_amc : c_avail_meta_count c' = c_avail_meta_count c;
  cb_amac : c_avail_meta_area_count c' = c_avail_meta_area_count c;
  cb_shift : c_meta_alloc_shift c' = c_meta_alloc_shift c;
  cb_mah : c_meta_area_head c' = c_meta_area_head c;
  cb_mat : c_meta_area_tail c' = c_meta_area_tail c;
  cb_amas : c_avail_meta_areas c' = c_avail_meta_areas c;
  cb_usage : c_usage c' = c_usage c;
  cb_unmap : c_unmap_seq c' = c_unmap_seq c;
  cb_bounces : c_bounces c' = c_bounces c;
  cb_seq : c_seq c' = c_seq c;
  cb_brk : c_brk c' = c_brk c
}.
Lemma cbh_refl c : ctx_but_heads c c.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) [] "h01cp;1p;2p;4p;Ag00j;j1BTg00k4j13Tg00l0j12Tg00loj1ATg00K:j20Tg00mlj1:Tg00noj14Tg0107j15Tg011:j16Tg012;j17Tg013<j18Tg00D\j49Tg014?j1@Tg0157j1?Tg0163j1<Tg016mj1;Tg017cj1=Tg018YlA>Tg00SUR0f0R1'0p=1g019[R2P1P1%B1#1%31#1%21#1g00=ZR3%A1'0%:1#1%41#1%51#1%61,03%71,03%81,03P0g01:Rg01:kP0C9R0%@1'0%?1,00%<1,00%;1#1g01;I%=1'0MA>X02P1O1W0o"). Qed.
Lemma cbh_trans a b c : ctx_but_heads a b -> ctx_but_heads b c -> ctx_but_heads a c.
Proof. intros [] []; constructor; congruence. Qed.
Lemma cbh_set_head st h v : ctx_but_heads (s_ctx st) (s_ctx (set_head h v st)).
Proof. destruct h; constructor; reflexivity. Qed.
Lemma cbh_upd_meta st m f : ctx_but_heads (s_ctx st) (s_ctx (upd_meta m f st)).
Proof. constructor; reflexivity. Qed.

Lemma inv_L_lists st LS : inv_L st LS -> lists_ok st LS.
Proof. intros [L1 L2 L3 L4 L5 L6 L7 L9]. constructor; auto. Qed.

Lemma head_of_app (l : list aptr) g : l <> [] -> head_of (l ++ [g]) = head_of l.
Proof. destruct l; cbn; congruence. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RELINK.
Variables (X X' : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS LS' : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis DE : forall x, data_of (MR st' x) = data_of (MR st x).
Hypothesis KEYS : forall x, s_metas st' !! x <> None <-> s_metas st !! x <> None.
Hypotheses (HR : s_regions st' = s_regions st) (HSh : s_shadow st' = s_shadow st) (HN : s_next_rid st' = s_next_rid st)
           (HA : s_areas st' = s_areas st) (HG : s_groups st' = s_groups st) (HS : s_slots st' = s_slots st)
           (HT : s_tick st' = s_tick st) (HX : s_secret st' = s_secret st) (HV : s_reserved st' = s_reserved st) (HAT : s_atop st' = s_atop st).
Hypothesis HC : ctx_but_heads (s_ctx st) (s_ctx st').
Hypothesis XE : x_pend X' = x_pend X /\ x_orph X' = x_orph X /\ x_zomb X' = x_zomb X.
Hypothesis LO' : lists_ok st' LS'.
Hypothesis H_free : forall m, In m (LS' LFree) -> data_of (MR st m) = data_of meta0.
Hypothesis H_active : forall sc m, In m (LS' (LActive sc)) -> 0 <= sc < 48 /\ live_group st m /\ m_sizeclass (MR st m) = sc.
Hypothesis H_keys : forall sc, LS' (LActive sc) <> [] -> 0 <= sc < 48.
Hypothesis H_actkeys : forall sc g, c_active (s_ctx st') !! sc = Some g -> 0 <= sc < 48.
Hypothesis H_idle : forall m, In m (x_idle X') -> s_metas st' !! m = Some meta0 /\ ~ in_list LS' m.
Hypothesis H_zomb : forall z, In z (x_zomb X) -> m_next (MR st' z) = None /\ m_prev (MR st' z) = None /\ ~ in_list LS' z.
Hypothesis H_groups : forall m b ai, s_groups st !! b = Some (mkGhdr (Some m) ai) ->
   (x_fresh X' <> Some m -> ai < m_last_idx (MR st m) -> In m (LS' (LActive (m_sizeclass (MR st m)))))
   /\ (x_fresh X' <> Some m -> m_sizeclass (MR st m) < 48 -> ~ in_list LS' m -> m_avail (MR st m) = 0 /\ m_freed (MR st m) = 0)
   /\ (x_fresh X' <> Some m -> forall sc, In m (LS' (LActive sc)) -> Some m <> head_of (LS' (LActive sc)) ->
         m_avail (MR st m) = 0 /\ m_freed (MR st m) <> 0)
   /\ (m_sizeclass (MR st m) = 63 -> ~ in_list LS' m)
   /\ (x_fresh X' <> Some m -> m_sizeclass (MR st m) < 48 -> get_stride (MR st m) < UNIT * size_class (m_sizeclass (MR st m)) ->
         m_avail (MR st m) = 0 /\ m_freed (MR st m) = 0).

Let dmem := de_mem st st' DE. Let davail := de_avail st st' DE. Let dfreed := de_freed st st' DE.
Let dlast := de_last st st' DE. Let dfreeable := de_freeable st st' DE. Let dsc := de_sc st st' DE.
Let dmaplen := de_maplen st st' DE. Let dstride := de_stride st st' DE. Let dgbase := de_gbase st st' DE.
Let dsstart := de_sstart st st' DE. Let dslot := de_slot_start' st st' DE. Let dcnt := de_cnt st st' DE. Let dgend := de_gend st st' DE.

Lemma rl_hosts b m : hosts st' b m <-> hosts st b m.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) ["RELINK"] "h01bh11mp;5g01Q[j50Tg002dR0p,2stp,3st'p,2HGf1R1f0R2D0X10X00P1P2O2X10W0o"). Qed.
Lemma rl_live m : live_group st' m <-> live_group st m.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) ["RELINK"] "h01mp;4g01RUj40Tg002dR0p,2stp,3st'p,2HGf0R1C0X00P1O1W0o"). Qed.
Lemma rl_frontier rid r : frontier st' rid r = frontier st rid r.
Proof. unfold frontier. rewrite (cb_amas _ _ HC). reflexivity. Qed.
Lemma rl_usage sc : usage st' sc = usage st sc.
Proof. unfold usage, ctx. rewrite (cb_usage _ _ HC). reflexivity. Qed.
Lemma rl_gcnt sc : gcnt st' sc = gcnt st sc.
Proof.
  apply gcnt_ext_groups; [exact HG|]. intros b h m Hb Hm. rewrite dsc, dcnt. auto.
Qed.

Theorem INVL_relink : INVL X' st' L BL LS'.
Proof.
  destruct XE as (XP & XO & XZ).
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof HC as [cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 cs12 cs13 cs14 cs15].
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* [comment removed for export] *) destruct IR; constructor; rewrite ?HR, ?HN, ?HV, ?HAT, ?HG, ?XO, ?cs6, ?cs7, ?cs10, ?cs15; try assumption.
    + eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite rl_frontier. reflexivity.
    + intros rid r H1 H2. rewrite rl_frontier. exact (ir_metalen rid r H1 H2).
    + intros rid r H1 H2. rewrite rl_frontier. exact (ir_brkfront rid r H1 H2).
  - (* [comment removed for export] *) destruct IA; constructor; rewrite ?HR, ?HA, ?HX, ?cs1, ?cs2, ?cs3, ?cs4, ?cs5, ?cs6, ?cs8, ?cs9, ?cs10, ?cs11, ?cs12, ?cs13, ?cs14; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite rl_frontier. auto.
    + intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply KEYS in K.
      destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply KEYS in K. apply K. apply Hk. exact Hk2.
    + intros sc Hsc. rewrite rl_usage, rl_gcnt. exact (ia_usage sc Hsc).
  - (* [comment removed for export] *) destruct IM as [M1 M2 M3 M4 M5]; constructor.
    + intros m Hm. apply data0_shape. rewrite DE. apply data0_shape. apply M1. rewrite <- dmem. exact Hm.
    + intros m b Hm. rewrite dmem in Hm. rewrite rl_hosts, XZ. apply M2. exact Hm.
    + intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & ? & ? & ?). exists m. rewrite dmem, dlast. auto.
    + exact H_idle.
    + intros z Hz. rewrite XZ in Hz. destruct (H_zomb z Hz) as (A1 & A2 & A3). destruct (M5 z Hz) as (_ & _ & _ & b & B1 & B2).
      split; [exact A3|]. split; [exact A1|]. split; [exact A2|]. exists b. rewrite dmem, HG. auto.
  - (* [comment removed for export] *) destruct LO' as [Q1 Q2 Q3 Q4 Q5]. constructor; try assumption.
    + intros m Hm. apply data0_shape. rewrite DE. apply H_free. exact Hm.
    + intros sc m Hm. destruct (H_active sc m Hm) as (A1 & A2 & A3). rewrite rl_live, dsc. auto.
    + intros [sc|] Hne; [| exact I]. apply H_keys. exact Hne.
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5]; constructor.
    + intros m b ai Hb. rewrite HG in Hb. pose proof (G1 m b ai Hb) as GO. destruct (H_groups m b ai Hb) as (P1 & P2 & P3 & P4 & P5).
      destruct GO; constructor; rewrite ?dmem, ?davail, ?dfreed, ?dlast, ?dfreeable, ?dsc, ?dmaplen, ?dstride, ?dcnt, ?dgend, ?HR, ?HS; try assumption.
      * apply KEYS. exact g_present.
      * destruct g_sc as [A|(A1 & A2 & A3 & A4)]; [left; exact A| right]. auto.
      * intros Hml. destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite dgbase, dsstart, dstride, dsc. auto 10.
    + intros b ai Hb. rewrite HG in Hb. exact (G2 b ai Hb).
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite HG in H1, H2. rewrite !dlast, !dsc. eapply G3; eassumption.
    + intros rid r Hr Hk Ho. rewrite HR in Hr. rewrite XO in Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite rl_hosts, dmaplen. auto.
    + intros b h Hb. rewrite HG in Hb. rewrite HR. exact (G5 b h Hb).
  - (* [comment removed for export] *) destruct IS as [S1 S2 S3 S4 S5 S6]; constructor.
    + intros s m i Hs. rewrite HS in Hs. destruct (S1 s m i Hs) as (? & ? & ?). rewrite rl_live, dlast, dslot. auto.
    + intros b m i Hb Hi. rewrite HS, dslot. apply (S2 b); [apply rl_hosts; exact Hb| rewrite <- dlast; exact Hi].
    + intros b m ai i Hb Hi. rewrite HG in Hb. rewrite dlast in Hi. rewrite dslot, HG, davail, dfreed, XP. exact (S3 b m ai i Hb Hi).
    + intros s Hs. rewrite HS. apply S4. rewrite <- XP. exact Hs.
    + exact S5.
    + intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, dstride. auto.
  - (* [comment removed for export] *) apply (inv_SH_view st st'); auto.
Qed.
End RELINK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma present_MR st x : s_metas st !! x <> None -> s_metas st !! x = Some (MR st x).
Proof. unfold MR, get_meta_rec. destruct (s_metas st !! x); [reflexivity| congruence]. Qed.

Lemma fupd_in LS h l h' m : In m (fupd LS h l h') <-> (h' = h /\ In m l) \/ (h' <> h /\ In m (LS h')).
Proof.
  unfold fupd. destruct (decide (h' = h)) as [E|NE]; split; intros H; try tauto.
  all: destruct H as [[H1 H2]|[H1 H2]]; first [exact H2| congruence].
Qed.

Section OLD.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.

Lemma old_lists : lists_ok st LS.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) ["OLD"] "p;2p;3p;1g01DMj2:Tg01eYj39Tg01fQj33Tg01gIj22Tg00Uej20Tg01daj38Tg01cij15Tg01c1j34Tg039oj31Tg03:Jj36Tg03:ej37Tp,2stR0p,2LSR11:01R2p,1XR3?901p,2BLR493301204'0'0R4A8301R11024R4%50R21014R4p,1L94301024p,3INV3131313637o"). Qed.
Lemma old_free m : In m (LS LFree) -> data_of (MR st m) = data_of meta0.
Proof. intros H. apply data0_shape. exact (il_free _ _ (proj1 (proj2 (proj2 (proj2 INV)))) m H). Qed.
Lemma old_active sc m : In m (LS (LActive sc)) -> 0 <= sc < 48 /\ live_group st m /\ m_sizeclass (MR st m) = sc.
Proof. exact (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m). Qed.
Lemma old_keys sc : LS (LActive sc) <> [] -> 0 <= sc < 48.
Proof. intros H. exact (il_keys _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc) H). Qed.
Lemma old_actkeys sc g : c_active (s_ctx st) !! sc = Some g -> 0 <= sc < 48.
Proof. exact (ia_active_keys _ (proj1 (proj2 INV)) sc g). Qed.
Lemma old_idle m : In m (x_idle X) -> s_metas st !! m = Some meta0 /\ ~ in_list LS m.
Proof. exact (im_idle _ _ _ (proj1 (proj2 (proj2 INV))) m). Qed.
Lemma old_zomb z : In z (x_zomb X) -> m_next (MR st z) = None /\ m_prev (MR st z) = None /\ ~ in_list LS z /\
  exists b, m_mem (MR st z) = Some b /\ s_groups st !! b = None.
Proof. intros H. destruct (im_zomb _ _ _ (proj1 (proj2 (proj2 INV))) z H) as (A & B & C & D). auto. Qed.
Lemma old_group m b ai : s_groups st !! b = Some (mkGhdr (Some m) ai) -> group_ok X st LS m b ai.
Proof. intros H. exact (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) m b ai H). Qed.
Lemma old_63 m b ai : s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (MR st m) = 63 -> ~ in_list LS m.
Proof. intros H E. destruct (g_sc _ _ _ _ _ _ (old_group m b ai H)) as [[[_ Hlt] _]|(_ & _ & _ & NI)]; [lia| exact NI]. Qed.
(* [comment removed for export] *)
Lemma listed_next m h : In m (LS h) -> m_next (MR st m) <> None.
Proof. intros H. apply (lists_in_next_some st LS old_lists h m H). Qed.
Lemma listed_present m h : In m (LS h) -> s_metas st !! m <> None.
Proof. intros H. destruct (m_next (MR st m)) as [x|] eqn:E; [exact (present_of_next st m x E)|]. exfalso. exact (listed_next m h H E). Qed.
Lemma head_listed h a : get_head st h = Some a -> In a (LS h).
Proof. intros H. rewrite (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) in H. destruct (LS h); cbn in H; [discriminate|]. inversion H. left. reflexivity. Qed.
Lemma prev_listed h a x : In a (LS h) -> m_prev (MR st a) = Some x -> In x (LS h).
Proof. intros Ha Hp. destruct (lists_prev_in st LS old_lists h a Ha) as (y & Hy & E & _). rewrite Hp in E. inversion E. subst. exact Hy. Qed.
Lemma next_listed h a x : In a (LS h) -> m_next (MR st a) = Some x -> In x (LS h).
Proof. intros Ha Hn. destruct (lists_next_in st LS old_lists h a Ha) as (y & Hy & E & _). rewrite Hn in E. inversion E. subst. exact Hy. Qed.
Lemma idle_unlisted m h : In m (x_idle X) -> ~ In m (LS h).
Proof. intros Hi H. apply (proj2 (old_idle m Hi)). exists h. exact H. Qed.
Lemma zomb_unlisted z h : In z (x_zomb X) -> ~ In z (LS h).
Proof. intros Hz H. apply (proj1 (proj2 (proj2 (old_zomb z Hz)))). exists h. exact H. Qed.
Lemma idle_not_live m : In m (x_idle X) -> ~ live_group st m.
Proof.
  intros Hi [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
  destruct (old_idle m Hi) as [E _]. unfold MR, get_meta_rec in M. rewrite E in M. cbn in M. discriminate.
Qed.
Lemma zomb_not_live z : In z (x_zomb X) -> ~ live_group st z.
Proof.
  intros Hz [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
  destruct (old_zomb z Hz) as (_ & _ & _ & b' & M' & G'). rewrite M in M'. inversion M'. subst. destruct Hb as [ai Hb]. rewrite Hb in G'. discriminate.
Qed.
Lemma free_not_live m : In m (LS LFree) -> ~ live_group st m.
Proof.
  intros Hf [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
  pose proof (data0_mem _ (old_free m Hf)) as D. rewrite D in M. discriminate.
Qed.
End OLD.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma INVL_set_fresh X st L BL LS f :
  INVL X st L BL LS -> x_fresh X = None -> INVL (xfresh X f) st L BL LS.
Proof.
  intros INV HF.
  refine (INVL_relink X (xfresh X f) st st L BL LS LS INV (fun x => eq_refl) (fun x => iff_refl _)
            eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_refl _) _
            (old_lists _ _ _ _ _ INV) (old_free _ _ _ _ _ INV) (old_active _ _ _ _ _ INV) (old_keys _ _ _ _ _ INV)
            (old_actkeys _ _ _ _ _ INV) _ _ _).
  - cbn. auto.
  - cbn. apply (old_idle _ _ _ _ _ INV).
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _). auto.
  - intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO.
    assert (NF : x_fresh X <> Some m) by (rewrite HF; discriminate).
    split; [| split; [| split; [| split]]].
    + intros _. exact (g_partial _ _ _ _ _ _ GO NF).
    + intros _. exact (g_unlisted _ _ _ _ _ _ GO NF).
    + intros _. exact (g_rest _ _ _ _ _ _ GO NF).
    + exact (old_63 _ _ _ _ _ INV m b ai Hb).
    + intros _. exact (g_under _ _ _ _ _ _ GO NF).
Qed.

Lemma INVL_clear_fresh X st L BL LS g :
  INVL X st L BL LS -> x_fresh X = Some g ->
  (forall b ai, s_groups st !! b = Some (mkGhdr (Some g) ai) ->
     (ai < m_last_idx (MR st g) -> In g (LS (LActive (m_sizeclass (MR st g)))))
     /\ (m_sizeclass (MR st g) < 48 -> ~ in_list LS g -> m_avail (MR st g) = 0 /\ m_freed (MR st g) = 0)
     /\ (forall sc, In g (LS (LActive sc)) -> Some g <> head_of (LS (LActive sc)) -> m_avail (MR st g) = 0 /\ m_freed (MR st g) <> 0)
     /\ (m_sizeclass (MR st g) < 48 -> get_stride (MR st g) < UNIT * size_class (m_sizeclass (MR st g)) -> m_avail (MR st g) = 0 /\ m_freed (MR st g) = 0)) ->
  INVL (xfresh X None) st L BL LS.
Proof.
  intros INV HF OB.
  refine (INVL_relink X (xfresh X None) st st L BL LS LS INV (fun x => eq_refl) (fun x => iff_refl _)
            eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_refl _) _
            (old_lists _ _ _ _ _ INV) (old_free _ _ _ _ _ INV) (old_active _ _ _ _ _ INV) (old_keys _ _ _ _ _ INV)
            (old_actkeys _ _ _ _ _ INV) _ _ _).
  - cbn. auto.
  - cbn. apply (old_idle _ _ _ _ _ INV).
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _). auto.
  - intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO.
    destruct (aptr_eq_dec m g) as [->|NE].
    + destruct (OB b ai Hb) as (O1 & O2 & O3 & O4). split; [| split; [| split; [| split]]]; auto. exact (old_63 _ _ _ _ _ INV g b ai Hb).
    + assert (NF : x_fresh X <> Some m) by (rewrite HF; congruence).
      split; [| split; [| split; [| split]]].
      * intros _. exact (g_partial _ _ _ _ _ _ GO NF).
      * intros _. exact (g_unlisted _ _ _ _ _ _ GO NF).
      * intros _. exact (g_rest _ _ _ _ _ _ GO NF).
      * exact (old_63 _ _ _ _ _ INV m b ai Hb).
      * intros _. exact (g_under _ _ _ _ _ _ GO NF).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma queue_frame h g st : let st' := queue_st h g st in
  s_regions st' = s_regions st /\ s_shadow st' = s_shadow st /\ s_next_rid st' = s_next_rid st
  /\ s_areas st' = s_areas st /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st
  /\ s_tick st' = s_tick st /\ s_secret st' = s_secret st /\ s_reserved st' = s_reserved st /\ s_atop st' = s_atop st
  /\ ctx_but_heads (s_ctx st) (s_ctx st').
Proof.
  unfold queue_st, q_link, q_single. destruct (get_head st h) as [a|]; [destruct (m_prev (get_meta_rec st a))| destruct h]; cbn;
    repeat split; try reflexivity; constructor; reflexivity.
Qed.

Lemma queue_metas_other h g st x :
  x <> g -> (forall a, get_head st h = Some a -> x <> a /\ m_prev (MR st a) <> Some x) ->
  s_metas (queue_st h g st) !! x = s_metas st !! x.
Proof.
  intros NE H. unfold queue_st, q_link, q_single. destruct (get_head st h) as [a|] eqn:E.
  - destruct (H a eq_refl) as [NA NP]. unfold MR in NP.
    destruct (m_prev (get_meta_rec st a)) as [pv|] eqn:Ep; rewrite !s_metas_upd_meta, !lookup_insert_ne by congruence; reflexivity.
  - rewrite set_head_metas, s_metas_upd_meta, lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma dequeue_frame h m st : let st' := dequeue h m st in
  s_regions st' = s_regions st /\ s_shadow st' = s_shadow st /\ s_next_rid st' = s_next_rid st
  /\ s_areas st' = s_areas st /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st
  /\ s_tick st' = s_tick st /\ s_secret st' = s_secret st /\ s_reserved st' = s_reserved st /\ s_atop st' = s_atop st
  /\ ctx_but_heads (s_ctx st) (s_ctx st').
Proof.
  unfold dequeue.
  destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|]; cbn -[get_head optr_eqb aptr_eqb];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; try destruct h; cbn;
  repeat split; try reflexivity; constructor; reflexivity.
Qed.

Lemma dequeue_metas_other h m st x :
  x <> m -> m_prev (MR st m) <> Some x -> m_next (MR st m) <> Some x ->
  s_metas (dequeue h m st) !! x = s_metas st !! x.
Proof.
  intros NE NP NN. unfold dequeue, MR in *.
  rewrite s_metas_upd_meta, lookup_insert_ne by congruence.
  destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|]; cbn -[get_head optr_eqb aptr_eqb upd_meta set_head];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
  rewrite ?set_head_metas, ?s_metas_upd_meta, ?lookup_insert_ne by congruence; try reflexivity;
  rewrite ?set_head_metas, ?s_metas_upd_meta, ?lookup_insert_ne by congruence; try reflexivity.
Qed.

Lemma get_head_active st sc : get_head st (LActive sc) = c_active (s_ctx st) !! sc.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section QUEUE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g : aptr) (h : lhead).
Hypothesis INV : INVL X st L BL LS.
Hypothesis NL : m_next (MR st g) = None.
Hypothesis PRES : s_metas st !! g <> None.
Hypothesis HQ : match h with
  | LActive sc => 0 <= sc < 48 /\ live_group st g /\ m_sizeclass (MR st g) = sc /\ x_fresh X = Some g
  | LFree => data_of (MR st g) = data_of meta0 /\ ~ In g (x_idle X) /\ ~ In g (x_zomb X)
  end.
Let st' := queue_st h g st.
Let LS' := fupd LS h (LS h ++ [g]).

Lemma q_in m h' : In m (LS' h') <-> In m (LS h') \/ (h' = h /\ m = g).
Proof.
  unfold LS'. rewrite fupd_in, in_app_iff. cbn. destruct (decide (h' = h)) as [->|NE]; intuition congruence.
Qed.
Lemma q_in_list m : in_list LS' m <-> in_list LS m \/ m = g.
Proof.
  unfold in_list. split.
  - intros [h' H]. apply q_in in H. destruct H as [H|[_ ->]]; [left; exists h'; exact H| right; reflexivity].
  - intros [[h' H]| ->]; [exists h'; apply q_in; left; exact H| exists h; apply q_in; right; auto].
Qed.
Lemma g_unlisted_old h' : ~ In g (LS h').
Proof. exact (lists_notin st LS (old_lists _ _ _ _ _ INV) g NL h'). Qed.
Lemma g_not_idle : ~ In g (x_idle X).
Proof.
  destruct h as [sc|]; [| exact (proj1 (proj2 HQ))]. destruct HQ as (_ & Hl & _). intros Hi. exact (idle_not_live _ _ _ _ _ INV g Hi Hl).
Qed.
Lemma g_not_zomb : ~ In g (x_zomb X).
Proof.
  destruct h as [sc|]; [| exact (proj2 (proj2 HQ))]. destruct HQ as (_ & Hl & _). intros Hz. exact (zomb_not_live _ _ _ _ _ INV g Hz Hl).
Qed.
Lemma untouched x : (forall h', ~ In x (LS h')) -> x <> g -> s_metas st' !! x = s_metas st !! x.
Proof.
  intros NI NE. apply queue_metas_other; [exact NE|]. intros a Ha. split.
  - intros ->. exact (NI h (head_listed _ _ _ _ _ INV h a Ha)).
  - intros Hp. exact (NI h (prev_listed _ _ _ _ _ INV h a x (head_listed _ _ _ _ _ INV h a Ha) Hp)).
Qed.

Theorem INVL_queue : INVL X st' L BL LS'.
Proof.
  destruct (queue_frame h g st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC).
  refine (INVL_relink X X st st' L BL LS LS' INV (queue_data h g st) _ F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 FC _ _ _ _ _ _ _ _ _).
  - (* [comment removed for export] *) intros x. split; [| apply queue_keys_mono]. intros K. apply queue_keys in K.
    destruct K as [K|[->|[Hh|(a & Ha & Hp)]]]; [exact K| exact PRES| |].
    + exact (listed_present _ _ _ _ _ INV x h (head_listed _ _ _ _ _ INV h x Hh)).
    + exact (listed_present _ _ _ _ _ INV x h (prev_listed _ _ _ _ _ INV h a x (head_listed _ _ _ _ _ INV h a Ha) Hp)).
  - auto.
  - apply lists_queue; [apply (old_lists _ _ _ _ _ INV)| exact NL].
  - intros m Hm. apply q_in in Hm. destruct Hm as [Hm|[E ->]]; [exact (old_free _ _ _ _ _ INV m Hm)|]. subst h. exact (proj1 HQ).
  - intros sc m Hm. apply q_in in Hm. destruct Hm as [Hm|[E ->]]; [exact (old_active _ _ _ _ _ INV sc m Hm)|]. subst h. destruct HQ as (A & B & C & _). auto.
  - intros sc Hne. destruct (decide (LActive sc = h)) as [E|NE].
    + subst h. exact (proj1 HQ).
    + unfold LS' in Hne. rewrite fupd_ne in Hne by exact NE. exact (old_keys _ _ _ _ _ INV sc Hne).
  - intros sc x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx. rewrite queue_head in Hx.
    destruct (decide (LActive sc = h)) as [E|NE]; [subst h; exact (proj1 HQ)|]. exact (old_actkeys _ _ _ _ _ INV sc x Hx).
  - intros m Hm. cbn in Hm. destruct (old_idle _ _ _ _ _ INV m Hm) as [E NI].
    assert (NE : m <> g) by (intros ->; exact (g_not_idle Hm)).
    split; [rewrite untouched; [exact E| intros h'; apply (idle_unlisted _ _ _ _ _ INV); exact Hm| exact NE]|].
    rewrite q_in_list. tauto.
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
    assert (NE : z <> g) by (intros ->; exact (g_not_zomb Hz)).
    assert (E : MR st' z = MR st z).
    { unfold MR, get_meta_rec. rewrite untouched; [reflexivity| intros h'; apply (zomb_unlisted _ _ _ _ _ INV); exact Hz| exact NE]. }
    rewrite E, q_in_list. repeat split; auto. tauto.
  - intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO. split; [| split; [| split; [| split]]].
    5:{ exact (g_under _ _ _ _ _ _ GO). }
    + intros NF Hai. apply q_in. left. exact (g_partial _ _ _ _ _ _ GO NF Hai).
    + intros NF Hsc NI. apply (g_unlisted _ _ _ _ _ _ GO NF Hsc). rewrite q_in_list in NI. tauto.
    + intros NF sc Hm Hh. apply q_in in Hm. destruct Hm as [Hm|[E ->]].
      * apply (g_rest _ _ _ _ _ _ GO NF sc Hm). unfold LS' in Hh. destruct (decide (LActive sc = h)) as [E|NE].
        -- subst h. rewrite fupd_eq in Hh. rewrite head_of_app in Hh; [exact Hh|]. intros E0. rewrite E0 in Hm. exact Hm.
        -- rewrite fupd_ne in Hh by exact NE. exact Hh.
      * exfalso. subst h. apply NF. exact (proj2 (proj2 (proj2 HQ))).
    + intros H63. rewrite q_in_list. intros [NI| ->]; [exact (old_63 _ _ _ _ _ INV m b ai Hb H63 NI)|].
      destruct h as [sc|].
      * destruct HQ as (A & _ & C & _). lia.
      * pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ (ex_intro _ ai Hb)) as M.
        rewrite (data0_mem _ (proj1 HQ)) in M. discriminate.
Qed.
End QUEUE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DEQUEUE.
Variables (X X' : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (m : aptr) (h : lhead) (l1 l2 : list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HL : LS h = l1 ++ m :: l2.
Hypothesis HX : (exists sc, h = LActive sc /\ x_fresh X = None /\ X' = xfresh X (Some m)) \/ (h = LFree /\ X' = xidle X (m :: x_idle X)).
Let st' := dequeue h m st.
Let LS' := fupd LS h (l1 ++ l2).

Lemma m_listed : In m (LS h).
Proof.
ltac2:(KReplay.run1 (kr_t_MI_Pres4 ()) ["DEQUEUE"] "h01lh11Ah21ah32l'h41Hp;1p;3p;2p;4p;6g01Cmj12Tg01OXj3:Tg0075j31Tg01I;j30Tg01o;j23Tg04;lj49Tg003Yj38Tg00K:j25Tg02Wbj36Tg02X<j37Tg006>j64Tg002dR0#2R1p,2l1R2p,1mR3p,2l2R45:0R5510f0R69003X01g004fp4p710R1%26R7f1R8#2R9f2R:g00Uef3R;A1;:8706f4R<?08;A0<8:'3R=[A0;6:A0;68'3A1<;:90<8[R>f5R?A1?<;70:\=P;P:P8P6C9P6n2001000000120000000W2W3W0W1P>^2:^39^07^11P6P0P2P5P3A0032A0035A8033A003415033637O5b4p,2LSp,1hO1p,2HLE4o"). Qed.
Lemma d_in x h' : In x (LS' h') -> In x (LS h').
Proof.
  unfold LS'. rewrite fupd_in. intros [[-> H]|[_ H]]; [| exact H]. rewrite HL. apply in_app_iff in H. apply in_app_iff. cbn. tauto.
Qed.
Lemma d_in_rev x h' : In x (LS h') -> x <> m -> In x (LS' h').
Proof.
  intros H NE. unfold LS'. apply fupd_in. destruct (decide (h' = h)) as [->|NE'].
  - left. split; [reflexivity|]. rewrite HL in H. apply in_app_iff in H. apply in_app_iff. cbn in H. destruct H as [H|[H|H]]; [tauto| congruence| tauto].
  - right. auto.
Qed.
Lemma d_in_list x : in_list LS' x -> in_list LS x.
Proof. intros [h' H]. exists h'. apply (d_in x h' H). Qed.
Lemma m_out : ~ in_list LS' m.
Proof.
  intros [h' H]. unfold LS' in H. apply fupd_in in H. destruct H as [[-> H]|[NE H]].
  - pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) as ND. rewrite HL in ND.
    destruct (NoDup_In_split l1 l2 m ND) as [N1 N2]. apply in_app_iff in H. tauto.
  - apply NE. exact (il_disj _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h' h m H m_listed).
Qed.
Lemma untouched_d x : (forall h', ~ In x (LS h')) -> s_metas st' !! x = s_metas st !! x.
Proof.
  intros NI. apply dequeue_metas_other.
  - intros ->. exact (NI h m_listed).
  - intros Hp. exact (NI h (prev_listed _ _ _ _ _ INV h m x m_listed Hp)).
  - intros Hn. exact (NI h (next_listed _ _ _ _ _ INV h m x m_listed Hn)).
Qed.
Lemma nonhead_old x : In x (LS' h) -> Some x <> head_of (LS' h) -> Some x <> head_of (LS h).
Proof.
  intros Hx Hh. unfold LS' in Hx, Hh. rewrite fupd_eq in Hx, Hh. rewrite HL. destruct l1 as [|a l1']; cbn in *.
  - intros E. inversion E. subst x.
    pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) as ND. rewrite HL in ND. cbn in ND.
    apply NoDup_cons in ND as [N _]. apply N. apply list_elem_of_In. exact Hx.
  - exact Hh.
Qed.
Lemma MR'_m : MR st' m = data_of (MR st m).
Proof.
  pose proof (dequeue_data h m st m) as D. fold st' in D. rewrite <- D.
  unfold st', dequeue, MR. rewrite get_meta_rec_upd_same. reflexivity.
Qed.

Theorem INVL_dequeue : INVL X' st' L BL LS'.
Proof.
  destruct (dequeue_frame h m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC).
  refine (INVL_relink X X' st st' L BL LS LS' INV (dequeue_data h m st) _ F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 FC _ _ _ _ _ _ _ _ _).
  - (* [comment removed for export] *) intros x. split; [| apply dequeue_keys_mono]. intros K. apply dequeue_keys in K.
    destruct K as [K|[->|[Hp|Hn]]]; [exact K| exact (listed_present _ _ _ _ _ INV m h m_listed)| |].
    + exact (listed_present _ _ _ _ _ INV x h (prev_listed _ _ _ _ _ INV h m x m_listed Hp)).
    + exact (listed_present _ _ _ _ _ INV x h (next_listed _ _ _ _ _ INV h m x m_listed Hn)).
  - destruct HX as [(sc & Eh & HD & ->)|(Eh & ->)]; cbn; auto.
  - apply lists_dequeue; [apply (old_lists _ _ _ _ _ INV)| exact HL].
  - intros x Hx. exact (old_free _ _ _ _ _ INV x (d_in x LFree Hx)).
  - intros sc x Hx. exact (old_active _ _ _ _ _ INV sc x (d_in x _ Hx)).
  - intros sc Hne. apply (old_keys _ _ _ _ _ INV sc). intros E. apply Hne. unfold LS'. unfold fupd.
    destruct (decide (LActive sc = h)) as [E2|NE2]; [| exact E]. exfalso. rewrite E2, HL in E. destruct l1; discriminate.
  - intros sc x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx. rewrite dequeue_head in Hx.
    destruct (decide (LActive sc = h)) as [E|NE]; [| exact (old_actkeys _ _ _ _ _ INV sc x Hx)].
    apply (old_keys _ _ _ _ _ INV sc). rewrite E, HL. destruct l1; discriminate.
  - intros x Hx.
    assert (OLD : In x (x_idle X) -> s_metas st' !! x = Some meta0 /\ ~ in_list LS' x).
    { intros Hi. destruct (old_idle _ _ _ _ _ INV x Hi) as [E NI]. split.
      - rewrite untouched_d; [exact E|]. intros h'. apply (idle_unlisted _ _ _ _ _ INV). exact Hi.
      - intros IL'. exact (NI (d_in_list x IL')). }
    destruct HX as [(sc & Eh & HD & EX)|(Eh & EX)]; rewrite EX in Hx; cbn in Hx; [exact (OLD Hx)|].
    destruct Hx as [<-|Hx]; [| exact (OLD Hx)].
    split; [| exact m_out].
    rewrite (present_MR st' m (dequeue_key_m h m st)). f_equal. rewrite MR'_m.
    apply (old_free _ _ _ _ _ INV). rewrite <- Eh. exact m_listed.
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
    assert (E : MR st' z = MR st z).
    { unfold MR, get_meta_rec. rewrite untouched_d; [reflexivity|]. intros h'. apply (zomb_unlisted _ _ _ _ _ INV). exact Hz. }
    rewrite E. repeat split; auto. intros IL'. exact (C (d_in_list z IL')).
  - intros x b ai Hb. pose proof (old_group _ _ _ _ _ INV x b ai Hb) as GO.
    destruct (aptr_eq_dec x m) as [->|NEm].
    + destruct HX as [(sc & Eh & HD & EX)|(Eh & EX)].
      * pose proof m_listed as ML. rewrite Eh in ML. destruct (old_active _ _ _ _ _ INV sc m ML) as (A1 & A2 & A3).
        rewrite EX. cbn. split; [| split; [| split; [| split]]]; [intros NF; exfalso; apply NF; reflexivity..| | intros NF; exfalso; apply NF; reflexivity]. intros H63. lia.
      * exfalso. pose proof m_listed as ML. rewrite Eh in ML. exact (free_not_live _ _ _ _ _ INV m ML (ex_intro _ b (ex_intro _ ai Hb))).
    + assert (HNF : x_fresh X' <> Some x -> x_fresh X <> Some x).
      { destruct HX as [(sc & Eh & HD & ->)|(Eh & ->)]; cbn; [rewrite HD; intros _; discriminate| exact (fun H => H)]. }
      split; [| split; [| split; [| split]]].
      5:{ intros NF. exact (g_under _ _ _ _ _ _ GO (HNF NF)). }
      * intros NF Hai. apply d_in_rev; [| exact NEm]. exact (g_partial _ _ _ _ _ _ GO (HNF NF) Hai).
      * intros NF Hsc NI. apply (g_unlisted _ _ _ _ _ _ GO (HNF NF) Hsc). intros [h' H]. apply NI. exists h'. apply d_in_rev; [exact H| exact NEm].
      * intros NF sc Hx Hh. apply (g_rest _ _ _ _ _ _ GO (HNF NF) sc (d_in x _ Hx)).
        destruct (decide (LActive sc = h)) as [E|NE].
        -- rewrite E in Hx, Hh |- *. exact (nonhead_old x Hx Hh).
        -- unfold LS' in Hh. rewrite fupd_ne in Hh by exact NE. exact Hh.
      * intros H63 IL'. exact (old_63 _ _ _ _ _ INV x b ai Hb H63 (d_in_list x IL')).
Qed.
End DEQUEUE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ROTATE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (a a' : aptr) (rest : list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HL : LS (LActive sc) = a :: rest.
Hypothesis Hn : m_next (MR st a) = Some a'.
Hypothesis OB : x_fresh X <> Some a -> rest <> [] -> m_avail (MR st a) = 0 /\ m_freed (MR st a) <> 0.
Let h := LActive sc.
Let st' := set_head h (Some a') st.
Let LS' := fupd LS h (rest ++ [a]).

Lemma r_in x h' : In x (LS' h') <-> In x (LS h').
Proof.
  unfold LS'. rewrite fupd_in. destruct (decide (h' = h)) as [->|NE].
  - unfold h. rewrite HL, in_app_iff. cbn. tauto.
  - tauto.
Qed.
Lemma r_in_list x : in_list LS' x <-> in_list LS x.
Proof. unfold in_list. split; intros [h' H]; exists h'; apply r_in; exact H. Qed.

Theorem INVL_rotate : INVL X st' L BL LS'.
Proof.
  refine (INVL_relink X X st st' L BL LS LS' INV (fun x => eq_refl) (fun x => iff_refl _)
            eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_set_head st h (Some a')) _
            _ _ _ _ _ _ _ _).
  - auto.
  - apply lists_rotate; [apply (old_lists _ _ _ _ _ INV)| exact HL| exact Hn].
  - intros m Hm. apply r_in in Hm. exact (old_free _ _ _ _ _ INV m Hm).
  - intros sc0 m Hm. apply r_in in Hm. exact (old_active _ _ _ _ _ INV sc0 m Hm).
  - intros sc0 Hne. apply (old_keys _ _ _ _ _ INV sc0). intros E. apply Hne. unfold LS', fupd.
    destruct (decide (LActive sc0 = h)) as [E2|NE2]; [| exact E]. exfalso. unfold h in E2. inversion E2. subst. rewrite HL in E. discriminate.
  - intros sc0 x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx.
    destruct (decide (LActive sc0 = h)) as [E|NE].
    + apply (old_keys _ _ _ _ _ INV sc0). unfold h in E. inversion E. subst. rewrite HL. discriminate.
    + rewrite get_head_set_head_other in Hx by exact NE. exact (old_actkeys _ _ _ _ _ INV sc0 x Hx).
  - intros m Hm. cbn in Hm. destruct (old_idle _ _ _ _ _ INV m Hm) as [E NI]. split; [| rewrite r_in_list; exact NI].
    unfold st'. rewrite set_head_metas. exact E.
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
    unfold st', MR. rewrite get_meta_rec_set_head. fold (MR st z). rewrite r_in_list. auto.
  - intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO. split; [| split; [| split; [| split]]].
    5:{ exact (g_under _ _ _ _ _ _ GO). }
    + intros NF Hai. apply r_in. exact (g_partial _ _ _ _ _ _ GO NF Hai).
    + intros NF Hsc NI. rewrite r_in_list in NI. exact (g_unlisted _ _ _ _ _ _ GO NF Hsc NI).
    + intros NF sc0 Hm Hh. destruct (decide (LActive sc0 = h)) as [E|NE].
      * unfold h in E. inversion E. subst sc0. unfold LS' in Hm, Hh. fold h in Hm, Hh. rewrite fupd_eq in Hm, Hh.
        apply in_app_iff in Hm. destruct Hm as [Hm|[<-|[]]].
        -- apply (g_rest _ _ _ _ _ _ GO NF sc). { unfold h in HL. rewrite HL. right. exact Hm. }
           unfold h in HL. rewrite HL. cbn. intros E2. inversion E2. subst m.
           pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND.
           apply NoDup_cons in ND as [N _]. apply N. apply list_elem_of_In. exact Hm.
        -- apply OB; [exact NF|]. intros ->. cbn in Hh. apply Hh. reflexivity.
      * unfold LS' in Hm, Hh. rewrite fupd_ne in Hm, Hh by exact NE. exact (g_rest _ _ _ _ _ _ GO NF sc0 Hm Hh).
    + intros H63. rewrite r_in_list. exact (old_63 _ _ _ _ _ INV m b ai Hb H63).
Qed.
End ROTATE.
